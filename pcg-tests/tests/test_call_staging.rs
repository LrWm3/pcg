#![feature(rustc_private)]

use pcg::{
    borrow_pcg::{
        edge::{abstraction::FunctionCallOrLoop, kind::BorrowPcgEdgeKind},
        edge_data::EdgeData,
    },
    coupling::PcgCoupledEdgeKind,
    pcg::{EvalStmtPhase, PcgNode},
    rustc_interface::{
        index::Idx,
        middle::{mir, ty},
    },
};
use pcg_tests::BodySelector;

#[test]
fn slice_output_storage_expires_before_a_replaced_reference() {
    for nll in [false, true] {
        pcg_tests::run_pcg_on_str_with_borrow_checker(
            r#"
            fn target<'a>(values: &mut Vec<&'a mut usize>, replacement: &'a mut usize) -> &'a mut usize {
                let selected = &mut values[..];
                let previous = core::mem::replace(&mut selected[0], replacement);
                *values[0] = 11;
                *previous = 7;
                previous
            }
            "#,
            BodySelector::FirstFunction,
            true,
            nll,
            move |mut analysis| {
                let ctxt = analysis.ctxt();
                let slice_call = ctxt
                    .body()
                    .basic_blocks
                    .iter_enumerated()
                    .find_map(|(block, data)| {
                        let mir::TerminatorKind::Call { destination, .. } = data.terminator().kind
                        else {
                            return None;
                        };
                        let ty::TyKind::Ref(_, referent, ty::Mutability::Mut) =
                            destination.ty(ctxt.body(), ctxt.tcx()).ty.kind()
                        else {
                            return None;
                        };
                        matches!(referent.kind(), ty::TyKind::Slice(_)).then_some(block)
                    })
                    .expect("slice IndexMut call");
                let mut separate_storage = false;
                let mut delayed_referents = false;
                let mut storage_expired_first = false;
                for block in ctxt.body().basic_blocks.indices() {
                    let Some(data) = analysis.get_all_for_bb(block).unwrap() else {
                        continue;
                    };
                    for statement in &data.statements {
                        for phase in [EvalStmtPhase::PreOperands, EvalStmtPhase::PostMain] {
                            let mut storage_live = false;
                            let mut referents_live = false;
                            for edge in statement.states[phase].borrow_pcg().graph().edges() {
                                let BorrowPcgEdgeKind::Coupled(PcgCoupledEdgeKind(
                                    FunctionCallOrLoop::FunctionCall(call),
                                )) = edge.kind()
                                else {
                                    continue;
                                };
                                if call.metadata().location().block != slice_call {
                                    continue;
                                }
                                let inputs = edge.blocked_nodes(ctxt).collect::<Vec<_>>();
                                let outputs = edge.blocked_by_nodes(ctxt).collect::<Vec<_>>();
                                storage_live |= inputs.iter().any(|input| matches!(input, PcgNode::LifetimeProjection(p) if p.region_idx().index()==0));
                                referents_live |= inputs.iter().any(|input| matches!(input, PcgNode::LifetimeProjection(p) if p.region_idx().index()>0));
                                separate_storage |= inputs.iter().all(|input| matches!(input, PcgNode::LifetimeProjection(p) if p.region_idx().index()==0))
                                    && outputs.iter().all(|output| matches!(*output, PcgNode::LifetimeProjection(p) if p.region_idx().index()==0));
                                delayed_referents |= inputs.iter().all(|input| matches!(input, PcgNode::LifetimeProjection(p) if p.region_idx().index()>0))
                                    && outputs.iter().any(|output| matches!(*output, PcgNode::LifetimeProjection(p) if p.region_idx().index()>0));
                            }
                            storage_expired_first |= !storage_live && referents_live;
                        }
                    }
                }
                assert!(
                    separate_storage,
                    "outer storage needs its own expiry stage (nll={nll})"
                );
                assert!(
                    delayed_referents,
                    "escaped referents must keep their restoration dependency (nll={nll})"
                );
                assert!(
                    storage_expired_first,
                    "the storage obligation must expire while the removed reference remains live (nll={nll})"
                );
            },
        );
    }
}
