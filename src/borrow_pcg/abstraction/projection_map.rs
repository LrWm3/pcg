//! Checked correspondence between signature and call-site lifetime projections.
//!
//! This relation is per argument/result, and may be many-to-many: substituting
//! one region for two signature lifetimes must not overwrite either origin.
use std::collections::HashMap;

use super::{
    ArgIdxOrResult, FunctionData, FunctionShapeDataSource, FunctionShapeNode,
    MakeFunctionShapeError,
};
use crate::{
    borrow_pcg::{
        edge::abstraction::function::DefinedFnSigShapeDataSource,
        region_projection::{Generalized, LifetimeProjection, PcgRegion},
        visitor::{GeneralizedLifetime, OpaqueTy, extract_generalized_lifetimes, extract_regions},
    },
    rustc_interface::middle::ty,
    utils::HasTyCtxt,
};

#[derive(Clone, Debug)]
pub struct FunctionCallProjectionMap {
    targets: HashMap<FunctionShapeNode<Generalized>, Option<Vec<FunctionShapeNode>>>,
}

impl FunctionCallProjectionMap {
    /// `None` means the correspondence is unknown. An empty slice means the
    /// projection has no call-site incarnations (e.g. `RegionsIn(T)` for u32).
    pub fn call_nodes(&self, node: FunctionShapeNode<Generalized>) -> Option<&[FunctionShapeNode]> {
        self.targets.get(&node)?.as_deref()
    }
}

type Origins<'tcx> = HashMap<GeneralizedLifetime<'tcx>, Option<Vec<PcgRegion<'tcx>>>>;

fn record<'tcx>(
    origins: &mut Origins<'tcx>,
    origin: GeneralizedLifetime<'tcx>,
    regions: Option<Vec<PcgRegion<'tcx>>>,
) {
    match origins.entry(origin) {
        std::collections::hash_map::Entry::Vacant(entry) => {
            entry.insert(regions);
        }
        std::collections::hash_map::Entry::Occupied(mut entry) => {
            match (entry.get_mut(), regions) {
                (Some(existing), Some(regions)) => {
                    for region in regions {
                        if !existing.contains(&region) {
                            existing.push(region);
                        }
                    }
                }
                (existing, _) => *existing = None,
            }
        }
    }
}

fn align<'tcx>(identity: ty::Ty<'tcx>, actual: ty::Ty<'tcx>, origins: &mut Origins<'tcx>) {
    let mut region = |identity: ty::Region<'tcx>, actual: ty::Region<'tcx>| {
        record(
            origins,
            GeneralizedLifetime::Region(identity.into()),
            Some(vec![actual.into()]),
        );
    };
    match (identity.kind(), actual.kind()) {
        (ty::TyKind::Param(_) | ty::TyKind::Alias(..), _) => {
            let opaque = OpaqueTy::try_from(identity).unwrap();
            // Hidden resources have an explicit body projection now. Mapping
            // the complete group must retain those projections, even when no
            // concrete lifetime is visible in the substituted type.
            record(
                origins,
                GeneralizedLifetime::RegionsIn(opaque),
                Some(extract_regions(actual).into_iter().collect()),
            );
        }
        (ty::TyKind::Ref(a, x, ma), ty::TyKind::Ref(b, y, mb)) if ma == mb => {
            region(*a, *b);
            align(*x, *y, origins);
        }
        (ty::TyKind::Adt(a, xs), ty::TyKind::Adt(b, ys))
            if a.did() == b.did() && xs.len() == ys.len() =>
        {
            for (x, y) in xs.iter().zip(ys.iter()) {
                if let (Some(a), Some(b)) = (x.as_region(), y.as_region()) {
                    record(
                        origins,
                        GeneralizedLifetime::Region(a.into()),
                        Some(vec![b.into()]),
                    );
                } else if let (Some(a), Some(b)) = (x.as_type(), y.as_type()) {
                    align(a, b, origins);
                }
            }
        }
        (ty::TyKind::Tuple(xs), ty::TyKind::Tuple(ys)) if xs.len() == ys.len() => {
            for (x, y) in xs.iter().zip(ys.iter()) {
                align(x, y, origins);
            }
        }
        (ty::TyKind::Slice(x), ty::TyKind::Slice(y))
        | (ty::TyKind::Array(x, _), ty::TyKind::Array(y, _)) => align(*x, *y, origins),
        (ty::TyKind::RawPtr(x, a), ty::TyKind::RawPtr(y, b)) if a == b => align(*x, *y, origins),
        (ty::TyKind::Dynamic(_, a, ..), ty::TyKind::Dynamic(_, b, ..)) => region(*a, *b),
        _ => {
            // Do not guess corresponding indices across unmatched type shapes.
            for origin in extract_generalized_lifetimes(identity, None) {
                record(origins, origin, None);
            }
        }
    }
}

impl<'tcx> FunctionData<'tcx> {
    /// Build a partial, structurally checked mapping using the same generalized
    /// projection lists as the signature shape. Opaque substitutions retain their
    /// body groups; unmatched structural shapes remain explicitly unknown.
    pub fn call_projection_map(
        self,
        arguments: &[ty::Ty<'tcx>],
        result: ty::Ty<'tcx>,
        ctxt: impl HasTyCtxt<'tcx> + Copy,
    ) -> Result<FunctionCallProjectionMap, MakeFunctionShapeError> {
        let source = DefinedFnSigShapeDataSource::new(self.def_id(), ctxt.tcx())?;
        let identity = self.identity_fn_sig(ctxt.tcx());
        if arguments.len() != identity.inputs().len() {
            return Err(MakeFunctionShapeError::ArgumentCountMismatch);
        }
        let mut targets = HashMap::new();
        let nodes = source
            .input_arg_projections(ctxt.tcx())
            .into_iter()
            .map(|p| (ArgIdxOrResult::Argument(p.base), p.region_idx, p.region))
            .chain(
                source
                    .result_projections(ctxt.tcx())
                    .into_iter()
                    .map(|p| (p.base, p.region_idx, p.region)),
            )
            .collect::<Vec<_>>();
        for (base, actual) in arguments
            .iter()
            .enumerate()
            .map(|(i, ty)| (ArgIdxOrResult::Argument(i.into()), *ty))
            .chain(std::iter::once((ArgIdxOrResult::Result, result)))
        {
            let identity_ty = match base {
                ArgIdxOrResult::Argument(i) => identity.inputs()[*i],
                ArgIdxOrResult::Result => identity.output(),
            };
            let mut origins = HashMap::new();
            align(identity_ty, actual, &mut origins);
            let actual_regions = extract_regions(actual);
            for &(node_base, index, origin) in &nodes {
                if node_base != base {
                    continue;
                }
                let mapped = origins
                    .get(&origin)
                    .and_then(|regions| regions.as_ref())
                    .and_then(|regions| {
                        regions
                            .iter()
                            .map(|r| {
                                actual_regions
                                    .iter_enumerated()
                                    .find(|(_, actual)| *actual == r)
                                    .map(|(index, _)| LifetimeProjection::from_index(base, index))
                            })
                            .collect::<Option<Vec<_>>>()
                    });
                targets.insert(LifetimeProjection::from_index(base, index), mapped);
            }
        }
        Ok(FunctionCallProjectionMap { targets })
    }
}
