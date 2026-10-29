#![feature(rustc_private)]

use pcg::{
    borrow_pcg::{
        edge_data::EdgeData,
        region_projection::{ExtractRegionsCtxt, PcgRegion},
    },
    pcg::{EvalStmtPhase, PcgNode},
    rustc_interface::{index::Idx, middle::mir},
};
use pcg_tests::{BodySelector, run_pcg_on_str};

#[test]
fn opaque_resources_are_retained_in_generic_body_edges() {
    run_pcg_on_str(
        "fn target<T>(x: T) -> T { x }",
        BodySelector::FirstFunction,
        true,
        |mut analysis| {
            let ctxt = analysis.ctxt();
            let input = ctxt.body().local_decls[mir::Local::from_usize(1)].ty;
            let regions: Vec<PcgRegion<'_>> = ctxt.extract_regions(input).into_iter().collect();
            assert!(matches!(regions.as_slice(), [PcgRegion::RegionsIn(_)]));
            let mut found = false;
            for block in ctxt.body().basic_blocks.indices() {
                if let Some(data) = analysis.get_all_for_bb(block).unwrap() {
                    for statement in &data.statements {
                        let state = &statement.states[EvalStmtPhase::PostMain];
                        found |= state.borrow_pcg().graph().edges().any(|edge| {
                            edge.blocked_by_nodes(ctxt).any(|node| {
                                matches!(node,
                            PcgNode::LifetimeProjection(projection)
                                if matches!(projection.region(ctxt), PcgRegion::RegionsIn(_)))
                            })
                        });
                    }
                }
            }
            assert!(found, "generic body edges must carry the opaque group");
        },
    );
}

#[test]
fn implied_slice_bound_does_not_relate_unrelated_regions() {
    run_pcg_on_str(
        "fn target<T>(values: &[T], unrelated: &u32, callback: fn(T)) {}",
        BodySelector::FirstFunction,
        true,
        |analysis| {
            let ctxt = analysis.ctxt();
            let values = ctxt.body().local_decls[mir::Local::from_usize(1)].ty;
            let unrelated = ctxt.body().local_decls[mir::Local::from_usize(2)].ty;
            let callback = ctxt.body().local_decls[mir::Local::from_usize(3)].ty;
            let values: Vec<PcgRegion<'_>> = ctxt.extract_regions(values).into_iter().collect();
            let unrelated: Vec<PcgRegion<'_>> =
                ctxt.extract_regions(unrelated).into_iter().collect();
            let callback: Vec<PcgRegion<'_>> = ctxt.extract_regions(callback).into_iter().collect();
            let [outer, group] = values.as_slice() else {
                panic!("missing slice group: {values:?}")
            };
            assert!(matches!(group, PcgRegion::RegionsIn(_)));
            assert!(
                callback.is_empty(),
                "fn argument types do not own their parameters"
            );
            let at = mir::Location {
                block: mir::START_BLOCK,
                statement_index: 0,
            };
            assert!(ctxt.borrow_checker().outlives(*group, *outer, at));
            assert!(!ctxt.borrow_checker().outlives(*group, unrelated[0], at));
            assert!(!ctxt.borrow_checker().outlives(*outer, *group, at));
        },
    );
}

#[test]
fn generic_explicit_tail_body_is_analyzed_with_groups() {
    run_pcg_on_str(
        r#"
        fn advance<'a, T>(remaining: &mut &'a mut [T]) -> Option<&'a mut T> {
            let slice = std::mem::replace(remaining, &mut []);
            if let Some((head, tail)) = slice.split_first_mut() {
                *remaining = tail;
                Some(head)
            } else { None }
        }
    "#,
        BodySelector::FirstFunction,
        true,
        |mut analysis| {
            let ctxt = analysis.ctxt();
            for block in ctxt.body().basic_blocks.indices() {
                analysis.get_all_for_bb(block).unwrap();
            }
            let result: Vec<PcgRegion<'_>> = ctxt
                .extract_regions(ctxt.body().return_ty())
                .into_iter()
                .collect();
            assert!(
                result
                    .iter()
                    .any(|region| matches!(region, PcgRegion::RegionsIn(_)))
            );
        },
    );
}

#[test]
fn generic_function_item_constant_has_no_resource_group() {
    run_pcg_on_str(
        r#"
        fn target<T>() { consume(item::<T>); }
        fn item<T>() {}
        fn consume<F>(callback: F) {}
    "#,
        BodySelector::FirstFunction,
        true,
        |mut analysis| {
            for block in analysis.ctxt().body().basic_blocks.indices() {
                analysis.get_all_for_bb(block).unwrap();
            }
        },
    );
}

#[test]
fn raw_pointer_does_not_own_pointee_resources() {
    run_pcg_on_str(
        "fn target<T>(x: *mut T) -> *mut T { x }",
        BodySelector::FirstFunction,
        true,
        |mut analysis| {
            let ctxt = analysis.ctxt();
            let regions: Vec<PcgRegion<'_>> = ctxt
                .extract_regions(ctxt.body().return_ty())
                .into_iter()
                .collect();
            assert!(regions.is_empty());
            for block in ctxt.body().basic_blocks.indices() {
                analysis.get_all_for_bb(block).unwrap();
            }
        },
    );
}

#[test]
fn generic_result_does_not_borrow_short_container_region() {
    use pcg::borrow_pcg::{
        ArgIdxOrResult, FunctionShape, edge::abstraction::function::DefinedFnCallWithCallTys,
    };
    use pcg::utils::HasCompilerCtxt;
    run_pcg_on_str(
        r#"
        fn target<T>(values: &mut Vec<T>) -> T { take(values) }
        fn take<T>(values: &mut Vec<T>) -> T { unimplemented!() }
    "#,
        BodySelector::FirstFunction,
        true,
        |analysis| {
            let ctxt = analysis.ctxt();
            let call = ctxt
                .body()
                .basic_blocks
                .iter()
                .find_map(|bb| {
                    DefinedFnCallWithCallTys::from_terminator(
                        bb.terminator(),
                        ctxt.ctxt().def_id(),
                        ctxt,
                    )
                })
                .unwrap();
            let shape = FunctionShape::for_fn_call(call, ctxt).unwrap();
            let result_edges = shape
                .edges()
                .filter(|edge| edge.output().base() == ArgIdxOrResult::Result)
                .collect::<Vec<_>>();
            assert!(
                !result_edges.is_empty(),
                "the result must retain its opaque resource input"
            );
            assert!(
                result_edges
                    .iter()
                    .all(|edge| edge.input().region_idx().index() != 0),
                "a generic result cannot borrow the container merely because its type is opaque: {shape}"
            );
        },
    );
}
