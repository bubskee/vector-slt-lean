import VectorSLT

/-! Brief 05, R2: focused paper audit for vector-slt-lean.
Prints the definitions the statements rest on, the type of every principal declaration and
paper-facing alias, and `#print axioms` for each. Run from the repository root with
`lake env lean -DwarningAsError=true -DautoImplicit=false checks/PaperAudit.lean`. -/

-- Definitions
#print VectorSLT.SLT.Z
#print VectorSLT.SLT.LaplaceLower
#print VectorSLT.SLT.LaplaceUpper
#print VectorSLT.SLT.HasLaplacePair
#print VectorSLT.layer
#print VectorSLT.net
#print VectorSLT.popLossA
#print VectorSLT.Zpos
#print VectorSLT.basePos
#print VectorSLT.ShearTarget
#print VectorSLT.ThmK
#print VectorSLT.ThmKUpper
#print VectorSLT.ThmN
#print VectorSLT.Aeta
#print VectorSLT.Meta
#print VectorSLT.Leta

-- Principal declarations
#check @VectorSLT.mainTheorem_shear
#check @VectorSLT.mainTheorem_shear_ratio
#check @VectorSLT.mainTheorem_shear_gaussian
#check @VectorSLT.propLprime_shear
#check @VectorSLT.propLprime_moments
#check @VectorSLT.propLprime_gaussian
#check @VectorSLT.shear_normalize
#check @VectorSLT.theoremM
#check @VectorSLT.theoremM_shear
#check @VectorSLT.ZN1_two_sided
#check @VectorSLT.ZN1_two_sided_shear
#check @VectorSLT.ZN1_two_sided_moments
#check @VectorSLT.ZN1_two_sided_gaussian
#check @VectorSLT.Gdown
#check @VectorSLT.Zpos_lower_N4
#check @VectorSLT.middle_position_pair
#check @VectorSLT.position_four_pair
#check @VectorSLT.separation
#check @VectorSLT.separation_moments
#check @VectorSLT.separation_gaussian
#check @VectorSLT.inverse_criterion
#check @VectorSLT.rank_one_criterion
#check @VectorSLT.shear_inverse
#check @VectorSLT.deriv_criterion
#check @VectorSLT.sepMap_injective
#check @VectorSLT.sepLin_lower
#check @VectorSLT.sep_absorb
#check @VectorSLT.bordered_det
#check @VectorSLT.null_direction
#check @VectorSLT.normalize_Aeta
#check @VectorSLT.errPη_coeff_ne3
#check @VectorSLT.errPη_s5
#check @VectorSLT.errPη_c3
#check @VectorSLT.errPη_c2
#check @VectorSLT.errPη_c1
#check @VectorSLT.errPη_c0
#check @VectorSLT.X4_lower
#check @VectorSLT.X4_lower_segment
#check @VectorSLT.X4_at_zero
#check @VectorSLT.X4_lower_population
#check @VectorSLT.X4_lower_gaussian
#check @VectorSLT.X4_lower_compact
#check @VectorSLT.SLT.Z_eq_layercake
#check @VectorSLT.SLT.laplaceLower_of_volume
#check @VectorSLT.SLT.laplaceUpper_of_volume
#check @VectorSLT.SLT.HasLaplacePair.of_comparable
#check @VectorSLT.SLT.HasLaplacePair.of_prior
#check @VectorSLT.SLT.HasLaplacePair.prod
#check @VectorSLT.SLT.monomial_hasLaplacePair
#check @VectorSLT.SLT.normalCrossing_Z

-- Paper-facing aliases (R3)
#check @VectorSLT.vector_shear_main_theorem
#check @VectorSLT.vector_shear_main_theorem_ratio
#check @VectorSLT.vector_shear_main_theorem_gaussian
#check @VectorSLT.vector_shear_position_one_lower
#check @VectorSLT.vector_shear_position_one_upper
#check @VectorSLT.vector_shear_position_one_exact
#check @VectorSLT.vector_shear_position_one_exact_gaussian
#check @VectorSLT.vector_any_position_lower
#check @VectorSLT.vector_near_shear_lower
#check @VectorSLT.vector_near_shear_lower_gaussian
#check @VectorSLT.vector_near_shear_normal_form
#check @VectorSLT.vector_shear_normal_form
#check @VectorSLT.vector_E0_bordered_det

-- Axioms
#print axioms VectorSLT.mainTheorem_shear
#print axioms VectorSLT.mainTheorem_shear_ratio
#print axioms VectorSLT.mainTheorem_shear_gaussian
#print axioms VectorSLT.propLprime_shear
#print axioms VectorSLT.propLprime_moments
#print axioms VectorSLT.propLprime_gaussian
#print axioms VectorSLT.shear_normalize
#print axioms VectorSLT.theoremM
#print axioms VectorSLT.theoremM_shear
#print axioms VectorSLT.ZN1_two_sided
#print axioms VectorSLT.ZN1_two_sided_shear
#print axioms VectorSLT.ZN1_two_sided_moments
#print axioms VectorSLT.ZN1_two_sided_gaussian
#print axioms VectorSLT.Gdown
#print axioms VectorSLT.Zpos_lower_N4
#print axioms VectorSLT.middle_position_pair
#print axioms VectorSLT.position_four_pair
#print axioms VectorSLT.separation
#print axioms VectorSLT.separation_moments
#print axioms VectorSLT.separation_gaussian
#print axioms VectorSLT.inverse_criterion
#print axioms VectorSLT.rank_one_criterion
#print axioms VectorSLT.shear_inverse
#print axioms VectorSLT.deriv_criterion
#print axioms VectorSLT.sepMap_injective
#print axioms VectorSLT.sepLin_lower
#print axioms VectorSLT.sep_absorb
#print axioms VectorSLT.bordered_det
#print axioms VectorSLT.null_direction
#print axioms VectorSLT.normalize_Aeta
#print axioms VectorSLT.errPη_coeff_ne3
#print axioms VectorSLT.errPη_s5
#print axioms VectorSLT.errPη_c3
#print axioms VectorSLT.errPη_c2
#print axioms VectorSLT.errPη_c1
#print axioms VectorSLT.errPη_c0
#print axioms VectorSLT.X4_lower
#print axioms VectorSLT.X4_lower_segment
#print axioms VectorSLT.X4_at_zero
#print axioms VectorSLT.X4_lower_population
#print axioms VectorSLT.X4_lower_gaussian
#print axioms VectorSLT.X4_lower_compact
#print axioms VectorSLT.SLT.Z_eq_layercake
#print axioms VectorSLT.SLT.laplaceLower_of_volume
#print axioms VectorSLT.SLT.laplaceUpper_of_volume
#print axioms VectorSLT.SLT.HasLaplacePair.of_comparable
#print axioms VectorSLT.SLT.HasLaplacePair.of_prior
#print axioms VectorSLT.SLT.HasLaplacePair.prod
#print axioms VectorSLT.SLT.monomial_hasLaplacePair
#print axioms VectorSLT.SLT.normalCrossing_Z
#print axioms VectorSLT.vector_shear_main_theorem
#print axioms VectorSLT.vector_shear_main_theorem_ratio
#print axioms VectorSLT.vector_shear_main_theorem_gaussian
#print axioms VectorSLT.vector_shear_position_one_lower
#print axioms VectorSLT.vector_shear_position_one_upper
#print axioms VectorSLT.vector_shear_position_one_exact
#print axioms VectorSLT.vector_shear_position_one_exact_gaussian
#print axioms VectorSLT.vector_any_position_lower
#print axioms VectorSLT.vector_near_shear_lower
#print axioms VectorSLT.vector_near_shear_lower_gaussian
#print axioms VectorSLT.vector_near_shear_normal_form
#print axioms VectorSLT.vector_shear_normal_form
#print axioms VectorSLT.vector_E0_bordered_det
