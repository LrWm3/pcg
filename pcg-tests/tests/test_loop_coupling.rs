#![feature(rustc_private)]

use pcg::{
    action::PcgAction,
    borrow_pcg::{action::BorrowPcgActionKind, edge::kind::BorrowPcgEdgeKind},
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
