#![feature(rustc_private)]

use pcg::{
    borrow_pcg::{ArgIdxOrResult, FunctionData, region_projection::LifetimeProjection},
    rustc_interface::middle::ty::Ty,
};
use pcg_tests::{BodySelector, run_pcg_on_str};

// These tests supply deliberately chosen call types, independent of rustc's
// inference choices, so collapse and expansion of lifetime indices are explicit.
#[test]
fn one_signature_lifetime_can_have_multiple_call_incarnations() {
    run_pcg_on_str(
        "fn target<'a>(x: (&'a u32, &'a u32)) -> (&'a u32, &'a u32) { x }",
        BodySelector::FirstFunction,
        true,
        |analysis| {
            let ctxt = analysis.ctxt();
            let tcx = ctxt.tcx();
            let a = Ty::new_imm_ref(tcx, tcx.lifetimes.re_static, tcx.types.u32);
            let b = Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, tcx.types.u32);
            let tuple = Ty::new_tup(tcx, &[a, b]);
            let map = FunctionData::new(ctxt.def_id().to_def_id())
                .call_projection_map(&[tuple], tuple, ctxt)
                .unwrap();
            for base in [ArgIdxOrResult::Argument(0.into()), ArgIdxOrResult::Result] {
                assert_eq!(
                    map.call_nodes(LifetimeProjection::from_index(base, 0.into())),
                    Some(
                        [
                            LifetimeProjection::from_index(base, 0.into()),
                            LifetimeProjection::from_index(base, 1.into()),
                        ]
                        .as_slice()
                    )
                );
            }
        },
    );
}

#[test]
fn collapsed_lifetimes_keep_both_signature_origins() {
    run_pcg_on_str(
        "fn target<'a, 'b>(x: (&'a u32, &'b u32)) -> (&'a u32, &'b u32) { x }",
        BodySelector::FirstFunction,
        true,
        |analysis| {
            let ctxt = analysis.ctxt();
            let tcx = ctxt.tcx();
            let reference = Ty::new_imm_ref(tcx, tcx.lifetimes.re_static, tcx.types.u32);
            let tuple = Ty::new_tup(tcx, &[reference, reference]);
            let map = FunctionData::new(ctxt.def_id().to_def_id())
                .call_projection_map(&[tuple], tuple, ctxt)
                .unwrap();
            for base in [ArgIdxOrResult::Argument(0.into()), ArgIdxOrResult::Result] {
                for index in [0, 1] {
                    assert_eq!(
                        map.call_nodes(LifetimeProjection::from_index(base, index.into())),
                        Some([LifetimeProjection::from_index(base, 0.into())].as_slice())
                    );
                }
            }
        },
    );
}

#[test]
fn generic_projection_preserves_opaque_body_groups() {
    run_pcg_on_str(
        "fn target<T>(x: T) -> T { x }",
        BodySelector::FirstFunction,
        true,
        |analysis| {
            let ctxt = analysis.ctxt();
            let tcx = ctxt.tcx();
            let data = FunctionData::new(ctxt.def_id().to_def_id());
            let signature = data.identity_fn_sig(tcx);
            let a = Ty::new_imm_ref(tcx, tcx.lifetimes.re_static, tcx.types.u32);
            let b = Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, tcx.types.u32);
            let tuple = Ty::new_tup(tcx, &[a, b]);
            for base in [ArgIdxOrResult::Argument(0.into()), ArgIdxOrResult::Result] {
                let node = LifetimeProjection::from_index(base, 0.into());
                let concrete = data.call_projection_map(&[tuple], tuple, ctxt).unwrap();
                assert_eq!(
                    concrete.call_nodes(node),
                    Some(
                        [
                            LifetimeProjection::from_index(base, 0.into()),
                            LifetimeProjection::from_index(base, 1.into()),
                        ]
                        .as_slice()
                    )
                );
                let empty = data
                    .call_projection_map(&[tcx.types.u32], tcx.types.u32, ctxt)
                    .unwrap();
                assert_eq!(empty.call_nodes(node), Some([].as_slice()));
                let opaque = data
                    .call_projection_map(signature.inputs(), signature.output(), ctxt)
                    .unwrap();
                assert_eq!(
                    opaque.call_nodes(node),
                    Some([LifetimeProjection::from_index(base, 0.into())].as_slice())
                );
            }
            assert!(data.call_projection_map(&[], tcx.types.u32, ctxt).is_err());
        },
    );
}

#[test]
fn unmatched_shapes_are_unknown_and_argument_origins_remain_distinct() {
    run_pcg_on_str(
        "fn target<'a, 'b>(x: &'a u32, y: &'b u32) -> &'a u32 { x }",
        BodySelector::FirstFunction,
        true,
        |analysis| {
            let ctxt = analysis.ctxt();
            let tcx = ctxt.tcx();
            let reference = Ty::new_imm_ref(tcx, tcx.lifetimes.re_static, tcx.types.u32);
            let data = FunctionData::new(ctxt.def_id().to_def_id());
            let map = data
                .call_projection_map(&[reference, reference], reference, ctxt)
                .unwrap();
            for index in [0, 1] {
                let base = ArgIdxOrResult::Argument(index.into());
                assert_eq!(
                    map.call_nodes(LifetimeProjection::from_index(base, 0.into())),
                    Some([LifetimeProjection::from_index(base, 0.into())].as_slice())
                );
            }
            let map = data
                .call_projection_map(&[tcx.types.u32, reference], reference, ctxt)
                .unwrap();
            assert_eq!(
                map.call_nodes(LifetimeProjection::from_index(
                    ArgIdxOrResult::Argument(0.into()),
                    0.into()
                )),
                None
            );
        },
    );
}
