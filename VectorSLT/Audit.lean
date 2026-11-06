import VectorSLT

/-! Axiom audit for headline declarations. Every line should print only
`propext`, `Classical.choice`, `Quot.sound` (or a subset). -/

-- Milestone A
#print axioms VectorSLT.prefixNet_apply_sum_cubes
#print axioms VectorSLT.prefixNet_apply_sum_cubes_Icc
#print axioms VectorSLT.prefixNet_eq_foldl
#print axioms VectorSLT.network_eq_foldl
#print axioms VectorSLT.network_apply_sum_cubes
#print axioms VectorSLT.prefixNet_congr
#print axioms VectorSLT.layer_A0
#print axioms VectorSLT.active_row_coords
#print axioms VectorSLT.inactive_row_coords
#print axioms VectorSLT.M2_error
-- Milestone B
#print axioms VectorSLT.volume_abs_sq_sub_le
#print axioms VectorSLT.volume_abs_quad_le
#print axioms VectorSLT.lintegral_min_div_abs_le
#print axioms VectorSLT.quad_ge_dist_roots
#print axioms VectorSLT.lemmaM2_explicit
#print axioms VectorSLT.lemmaM2
-- Milestone C
#print axioms VectorSLT.scaled_bound
#print axioms VectorSLT.volume_bFibre
#print axioms VectorSLT.volume_lowerRegion
#print axioms VectorSLT.lowerRegion_sub
#print axioms VectorSLT.rowSublevel_lower_explicit
#print axioms VectorSLT.rowSublevel_lower
#print axioms VectorSLT.rowLaplace_lower
#print axioms VectorSLT.leadingModel_lower
-- Milestone D
#print axioms VectorSLT.err_bound
#print axioms VectorSLT.net_recursion
#print axioms VectorSLT.measurePreserving_toM2
#print axioms VectorSLT.volume_OmegaM
#print axioms VectorSLT.omega_err
#print axioms VectorSLT.omega_near
#print axioms VectorSLT.propLprime
#print axioms VectorSLT.propLprime_population
-- Brief 02, checkpoint 1
-- L3
#print axioms VectorSLT.bordered_det
#print axioms VectorSLT.null_direction
-- L2
#print axioms VectorSLT.layer_conj
#print axioms VectorSLT.prefixNet_conj
#print axioms VectorSLT.shear_normalize
#print axioms VectorSLT.net_Tfun
#print axioms VectorSLT.lintegral_linearEquiv
#print axioms VectorSLT.propLprime_shear
-- L1
#print axioms VectorSLT.net_basePos
#print axioms VectorSLT.Zpos_one_lower
#print axioms VectorSLT.separation
#print axioms VectorSLT.separation_tendsto
-- Brief 02, checkpoint 2
-- L4 (namespace SLT, Mathlib only)
#print axioms SLT.Z_ge_V
#print axioms SLT.laplaceLower_of_volume
#print axioms SLT.Z_eq_layercake
#print axioms SLT.gammaLog_lt_top
#print axioms SLT.Z_le_of_volume
#print axioms SLT.laplaceUpper_of_volume
#print axioms SLT.Z_comparable
#print axioms SLT.LaplaceLower.of_le_mul
#print axioms SLT.LaplaceUpper.of_mul_le
#print axioms SLT.HasLaplacePair.of_comparable
#print axioms SLT.Z_prior_comparable
#print axioms SLT.HasLaplacePair.of_prior
#print axioms SLT.Z_prod
#print axioms SLT.HasLaplacePair.prod
#print axioms SLT.monomial_hasLaplacePair
#print axioms VectorSLT.leadingModel_laplaceLower
#print axioms VectorSLT.row_laplaceLower
#print axioms VectorSLT.position_one_laplaceLower
#print axioms VectorSLT.ThmK.hasLaplacePair
-- L5
#print axioms VectorSLT.error_isPoly
#print axioms VectorSLT.evalBox_injective
#print axioms VectorSLT.l2_le_sup
#print axioms VectorSLT.popLossA_le_moments
#print axioms VectorSLT.propLprime_moments
#print axioms VectorSLT.separation_moments
-- Plan (a): d-variable normal crossing (namespace SLT, Mathlib only)
#print axioms SLT.NCBound.step_lt
#print axioms SLT.NCBound.step_eq
#print axioms SLT.NCBound.step_gt
#print axioms SLT.NCBound.base
#print axioms SLT.ncZ_succ
#print axioms SLT.ncZ_bound
#print axioms SLT.normalCrossing
#print axioms SLT.normalCrossing_Z
-- Plan (b): Gaussian inputs
#print axioms VectorSLT.stdGauss2_moments
#print axioms VectorSLT.propLprime_gaussian
#print axioms VectorSLT.separation_gaussian
-- L6 stage 1
#print axioms SLT.lintegral_comp_affine
#print axioms SLT.setLIntegral_comp_affine_le
#print axioms SLT.lintegral_exp_neg_le_tsum
#print axioms SLT.lintegral_exp_neg_le_of_sublevel
#print axioms SLT.lintegral_min_rsq_inv
#print axioms SLT.radial_split
#print axioms SLT.lintegral_Icc_isqrt
#print axioms SLT.expand_of_deriv
#print axioms SLT.lintegral_isqrt_comp_le
#print axioms VectorSLT.lemmaM3
