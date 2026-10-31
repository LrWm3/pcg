#![feature(rustc_private)]

use pcg::{
    action::PcgAction,
    borrow_pcg::{
        action::BorrowPcgActionKind, edge::kind::BorrowPcgEdgeKind,
        region_projection::PcgRegion,
    },
    pcg::{EvalStmtPhase, PcgNode},
};
use pcg_tests::{BodySelector, run_pcg_on_str};

#[test]
fn iterator_loop_restores_storage_and_referents_together() {
    run_pcg_on_str(
        r#"
        fn visit(values: &mut [&mut u32]) {
            let mut it = values.iter_mut();
            loop {
                match it.next() {
                    Some(value) => **value = 7,
                    None => break,
                }
            }
            drop(it);
            if !values.is_empty() { let _ = *values[0]; }
        }
        "#,
        BodySelector::FirstFunction,
        true,
        |mut analysis| {
            let ctxt = analysis.ctxt();
            let mut found = false;
            let mut entry_obligation = false;
            for block in ctxt.body().basic_blocks.indices() {
                let Some(data) = analysis.get_all_for_bb(block).unwrap() else {
                    continue;
                };
                for statement in &data.statements {
                    let graph = statement.states[EvalStmtPhase::PreOperands]
                        .borrow_pcg()
                        .graph();
                    for edge in graph.edges() {
                        let BorrowPcgEdgeKind::Coupled(edge) = edge.kind() else {
                            continue;
                        };
                        if edge.loop_head().is_none() {
                            continue;
                        }
                        let inputs = edge.inputs(ctxt);
                        let storage = inputs
                            .iter()
                            .any(|input| matches!(**input, PcgNode::Place(_)));
                        let referents = inputs
                            .iter()
                            .any(|input| matches!(**input, PcgNode::LifetimeProjection(_)));
                        found |= storage && referents && edge.outputs().len() == 2;
                    }
                }
                for successor in &data.terminator.succs {
                    for action in successor.actions().iter() {
                        if let PcgAction::Borrow(action) = action
                            && let BorrowPcgActionKind::AddEdge { edge } = action.kind()
                            && let BorrowPcgEdgeKind::Coupled(edge) = edge.kind()
                            && edge.loop_head().is_some()
                        {
                            entry_obligation = true;
                        }
                    }
                }
            }
            assert!(
                found,
                "the iterator must jointly restore its slice storage and element referents"
            );
            assert!(
                entry_obligation,
                "entering the loop must establish the joint obligation"
            );
        },
    );
}

#[test]
fn owned_iterator_loop_restores_one_opaque_input_once() {
    fn restores_opaque_input<'a, 'tcx: 'a>(
        edge: &pcg::coupling::PcgCoupledEdgeKind<'tcx>,
        ctxt: impl pcg::utils::HasCompilerCtxt<'a, 'tcx>,
    ) -> bool {
        if edge.loop_head().is_none() || edge.outputs().len() < 2 {
            return false;
        }
        let inputs = edge.inputs(ctxt);
        inputs.len() == 1
            && matches!(**inputs.first().unwrap(), PcgNode::LifetimeProjection(projection)
                if matches!(projection.region(ctxt), PcgRegion::RegionsIn(_)))
    }
    for nll in [false, true] {
        pcg_tests::run_pcg_on_str_with_borrow_checker(
            r#"
            fn count<T>(values: Vec<T>) -> usize {
                let mut other = Vec::<T>::new().into_iter();
                let mut count = 0;
                for _value in values {
                    let _ = other.next();
                    count += 1;
                }
                count
            }
            "#,
            BodySelector::FirstFunction,
            true,
            nll,
            move |mut analysis| {
                let ctxt = analysis.ctxt();
                let mut joint_input = false;
                let mut entry_obligation = false;
                for block in ctxt.body().basic_blocks.indices() {
                    let Some(data) = analysis.get_all_for_bb(block).unwrap() else {
                        continue;
                    };
                    for statement in &data.statements {
                        for edge in statement.states[EvalStmtPhase::PreOperands]
                            .borrow_pcg()
                            .graph()
                            .edges()
                        {
                            if let BorrowPcgEdgeKind::Coupled(edge) = edge.kind() {
                                joint_input |= restores_opaque_input(edge, ctxt);
                            }
                        }
                    }
                    for successor in &data.terminator.succs {
                        for action in successor.actions().iter() {
                            if let PcgAction::Borrow(action) = action
                                && let BorrowPcgActionKind::AddEdge { edge } = action.kind()
                                && let BorrowPcgEdgeKind::Coupled(edge) = edge.kind()
                            {
                                entry_obligation |= restores_opaque_input(edge, ctxt);
                            }
                        }
                    }
                }
                assert!(joint_input, "one opaque input must not become independent loop obligations");
                assert!(entry_obligation, "loop entry must establish the joint input obligation");
            },
        );
    }
}
