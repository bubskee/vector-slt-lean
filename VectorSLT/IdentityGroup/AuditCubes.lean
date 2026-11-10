import VectorSLT.IdentityGroup.Cubes

/-! Axiom audit for `VectorSLT.IdentityGroup.Cubes`: one line per declaration of the
files `Cubes.lean` and `Cubes/*.lean`. Every line should print a subset of
`propext`, `Classical.choice`, `Quot.sound`. -/

-- Headline theorems (Cubes.lean)
#print axioms VectorSLT.IdentityGroup.cubeSumUpper_one
#print axioms VectorSLT.IdentityGroup.cubeSumUpper_two
#print axioms VectorSLT.IdentityGroup.cubeSumUpper_three
#print axioms VectorSLT.IdentityGroup.cubeSumLower

-- Cubes/Scaling.lean
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSum_smul
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSumSq_smul
#print axioms VectorSLT.IdentityGroup.Cubes.measurable_cubeSumSq
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSumSq_nonneg
#print axioms VectorSLT.IdentityGroup.Cubes.lintegral_comp_smul_eq
#print axioms VectorSLT.IdentityGroup.Cubes.finrank_forms
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSumUpper_of_lintegral_lt_top

-- Cubes/One.lean
#print axioms VectorSLT.IdentityGroup.Cubes.outer_le_cubeSumSq
#print axioms VectorSLT.IdentityGroup.Cubes.lintegral_gauss_lt_top
#print axioms VectorSLT.IdentityGroup.Cubes.lintegral_gauss_shift
#print axioms VectorSLT.IdentityGroup.Cubes.lintegral_exp_neg_cubeSumSq_one_lt_top
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSumUpper_one

-- Cubes/Two.lean
#print axioms VectorSLT.IdentityGroup.Cubes.two_cube_lower
#print axioms VectorSLT.IdentityGroup.Cubes.one_add_abs_pow_four_le
#print axioms VectorSLT.IdentityGroup.Cubes.lintegral_two_cube_lt_top
#print axioms VectorSLT.IdentityGroup.Cubes.lintegral_exp_neg_cubeSumSq_two_lt_top
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSumUpper_two

-- Cubes/Chart.lean
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSumSq_comp_perm
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSumSq_swap
#print axioms VectorSLT.IdentityGroup.Cubes.symForms
#print axioms VectorSLT.IdentityGroup.Cubes.symForms_false
#print axioms VectorSLT.IdentityGroup.Cubes.symForms_true
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSumSq_symForms
#print axioms VectorSLT.IdentityGroup.Cubes.measurePreserving_comp_perm
#print axioms VectorSLT.IdentityGroup.Cubes.measurePreserving_swapForms
#print axioms VectorSLT.IdentityGroup.Cubes.measurePreserving_symForms
#print axioms VectorSLT.IdentityGroup.Cubes.chartRegion
#print axioms VectorSLT.IdentityGroup.Cubes.measurableSet_chartRegion
#print axioms VectorSLT.IdentityGroup.Cubes.norm_prod_swap
#print axioms VectorSLT.IdentityGroup.Cubes.exists_symForms_mem_chartRegion
#print axioms VectorSLT.IdentityGroup.Cubes.expG
#print axioms VectorSLT.IdentityGroup.Cubes.measurable_expG
#print axioms VectorSLT.IdentityGroup.Cubes.lintegral_le_mul_setLIntegral_chartRegion
#print axioms VectorSLT.IdentityGroup.Cubes.lintegral_comp_abs
#print axioms VectorSLT.IdentityGroup.Cubes.ofReal_rpow_neg_eq
#print axioms VectorSLT.IdentityGroup.Cubes.lintegral_radial_le
#print axioms VectorSLT.IdentityGroup.Cubes.instIsAddHaarMeasureChart
#print axioms VectorSLT.IdentityGroup.Cubes.instNullSingletonClassChart
#print axioms VectorSLT.IdentityGroup.Cubes.splitForms
#print axioms VectorSLT.IdentityGroup.Cubes.splitForms_symm_apply
#print axioms VectorSLT.IdentityGroup.Cubes.measurePreserving_splitForms
#print axioms VectorSLT.IdentityGroup.Cubes.finrank_chart
#print axioms VectorSLT.IdentityGroup.Cubes.cons_mem_chartRegion_iff
#print axioms VectorSLT.IdentityGroup.Cubes.chartG
#print axioms VectorSLT.IdentityGroup.Cubes.cons_smul_eq
#print axioms VectorSLT.IdentityGroup.Cubes.measurable_chartG
#print axioms VectorSLT.IdentityGroup.Cubes.lintegral_slice_le
#print axioms VectorSLT.IdentityGroup.Cubes.indicator_eq_indicator_one_mul
#print axioms VectorSLT.IdentityGroup.Cubes.chartG_nonneg
#print axioms VectorSLT.IdentityGroup.Cubes.setLIntegral_chartRegion_le
#print axioms VectorSLT.IdentityGroup.Cubes.shear
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSum_shear_zero
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSum_shear_one
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSum_shear_two
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSum_shear_three
#print axioms VectorSLT.IdentityGroup.Cubes.sq_add_le_two
#print axioms VectorSLT.IdentityGroup.Cubes.sq_add_le_three
#print axioms VectorSLT.IdentityGroup.Cubes.sq_add_le_four
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSumSq_shear_le
#print axioms VectorSLT.IdentityGroup.Cubes.shear_cons
#print axioms VectorSLT.IdentityGroup.Cubes.measurePreserving_shear_pair
#print axioms VectorSLT.IdentityGroup.Cubes.measurePreserving_shear
#print axioms VectorSLT.IdentityGroup.Cubes.norm_shear_le
#print axioms VectorSLT.IdentityGroup.Cubes.chartN
#print axioms VectorSLT.IdentityGroup.Cubes.measurable_chartN
#print axioms VectorSLT.IdentityGroup.Cubes.chartG_ge
#print axioms VectorSLT.IdentityGroup.Cubes.setLIntegral_chartG_le
#print axioms VectorSLT.IdentityGroup.Cubes.lintegral_exp_lt_top_of_chart
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSumUpper_of_chart

-- Cubes/Three.lean
#print axioms VectorSLT.IdentityGroup.Cubes.H3
#print axioms VectorSLT.IdentityGroup.Cubes.chartN_two
#print axioms VectorSLT.IdentityGroup.Cubes.H3_symm
#print axioms VectorSLT.IdentityGroup.Cubes.sigma_sq_le_H3
#print axioms VectorSLT.IdentityGroup.Cubes.tau_sq_le_H3
#print axioms VectorSLT.IdentityGroup.Cubes.sq_le_of_abs_le
#print axioms VectorSLT.IdentityGroup.Cubes.residual_identity
#print axioms VectorSLT.IdentityGroup.Cubes.ab_sq_le
#print axioms VectorSLT.IdentityGroup.Cubes.le_neg_half_of_sigma_small
#print axioms VectorSLT.IdentityGroup.Cubes.abs_sigma_le
#print axioms VectorSLT.IdentityGroup.Cubes.abs_tau_le
#print axioms VectorSLT.IdentityGroup.Cubes.ψ
#print axioms VectorSLT.IdentityGroup.Cubes.ψL
#print axioms VectorSLT.IdentityGroup.Cubes.measurable_ψ
#print axioms VectorSLT.IdentityGroup.Cubes.measurable_ψL
#print axioms VectorSLT.IdentityGroup.Cubes.ψL_eq_ψ
#print axioms VectorSLT.IdentityGroup.Cubes.lintegral_ψL_lt_top
#print axioms VectorSLT.IdentityGroup.Cubes.lintegral_ψL_affine_le
#print axioms VectorSLT.IdentityGroup.Cubes.lintegral_ψL_cube_le
#print axioms VectorSLT.IdentityGroup.Cubes.inv_le_of_sq_le
#print axioms VectorSLT.IdentityGroup.Cubes.inv_le_of_prod_le
#print axioms VectorSLT.IdentityGroup.Cubes.inv_le_weights
#print axioms VectorSLT.IdentityGroup.Cubes.Ψ
#print axioms VectorSLT.IdentityGroup.Cubes.measurable_Ψ
#print axioms VectorSLT.IdentityGroup.Cubes.inv_H3_le
#print axioms VectorSLT.IdentityGroup.Cubes.lintegral_Ψ_lt_top
#print axioms VectorSLT.IdentityGroup.Cubes.mem_closedBall_two_iff
#print axioms VectorSLT.IdentityGroup.Cubes.chart_three
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSumUpper_three

-- Cubes/Lower.lean
#print axioms VectorSLT.IdentityGroup.Cubes.CubeSumLower
#print axioms VectorSLT.IdentityGroup.Cubes.abs_moment_le
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSumSq_le
#print axioms VectorSLT.IdentityGroup.Cubes.cubeSumLower_all
