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
#print VectorSLT.IdentityGroup.cubeSum
#print VectorSLT.IdentityGroup.cubeSumSq
#print VectorSLT.IdentityGroup.CubeSumUpper
#print VectorSLT.IdentityGroup.Cubes.CubeSumLower
#print VectorSLT.IdentityGroup.Pairs.NonShearTarget
#print VectorSLT.IdentityGroup.Pairs.grpPoly
#print VectorSLT.IdentityGroup.Pairs.grpErr
#print VectorSLT.IdentityGroup.Pairs.grpBlocks
#print VectorSLT.IdentityGroup.Pairs.grpJ
#print VectorSLT.LeadingMap.thetaEps
#print VectorSLT.LeadingMap.scaledBlocks
#print VectorSLT.LeadingMap.lead
#print VectorSLT.LeadingMap.dLayer
#print VectorSLT.LeadingMap.Spre
#print VectorSLT.LeadingMap.Ssuf
#print VectorSLT.LeadingMap.pre
#print VectorSLT.LeadingMap.suf
#print VectorSLT.LeadingMap.rowForm
#print VectorSLT.LeadingMap.mom
#print VectorSLT.LeadingMap.momD
#print VectorSLT.LeadingMap.poly11
#print VectorSLT.LeadingMap.n1Coeff
#print VectorSLT.LeadingMap.cube
#print VectorSLT.LeadingMap.twoCube
#print VectorSLT.LeadingMap.rowCubic
#print VectorSLT.LeadingMap.leadingMap
#print VectorSLT.LeadingMap.generators
#print VectorSLT.LeadingMap.R2
#print VectorSLT.LeadingMap.R3
#print VectorSLT.LeadingMap.w2
#print VectorSLT.LeadingMap.w3
#print VectorSLT.LeadingMap.w4
#print VectorSLT.LeadingMap.activeLin
#print VectorSLT.LeadingMap.activeCoords
#print VectorSLT.LeadingMap.coeffMid
#print VectorSLT.LeadingMap.LamMid
#print VectorSLT.LeadingMap.coeffFour
#print VectorSLT.LeadingMap.LamFour
#print VectorSLT.LossCompare.Ψ
#print VectorSLT.LossCompare.cvec
#print VectorSLT.LossCompare.wOf
#print VectorSLT.LossCompare.flat
#print VectorSLT.LossCompare.unflat
#print VectorSLT.LossCompare.inact
#print VectorSLT.LossCompare.MarginData
#print VectorSLT.LossCompare.G4
#print VectorSLT.LossCompare.H4
#print VectorSLT.LossCompare.h4
#print VectorSLT.LossCompare.hS5
#print VectorSLT.LossCompare.hS4
#print VectorSLT.LossCompare.hST
#print VectorSLT.LossCompare.hT3
#print VectorSLT.LossCompare.Pm
#print VectorSLT.LossCompare.Dm
#print VectorSLT.LossCompare.W5
#print VectorSLT.LossCompare.W4
#print VectorSLT.LossCompare.ext4
#print VectorSLT.LossCompare.Gmid
#print VectorSLT.LossCompare.Hmid
#print VectorSLT.LossCompare.hvec
#print VectorSLT.LossCompare.hS
#print VectorSLT.LossCompare.Nmid
#print VectorSLT.LossCompare.cubeTab

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
#check @VectorSLT.X5_upper
#check @VectorSLT.X5_upper_two
#check @VectorSLT.X5_upper_gaussian
#check @VectorSLT.X5_upper_explicit
#check @VectorSLT.X5_upper_explicit_two
#check @VectorSLT.IdentityGroup.cubeSumUpper_one
#check @VectorSLT.IdentityGroup.cubeSumUpper_two
#check @VectorSLT.IdentityGroup.cubeSumUpper_three
#check @VectorSLT.IdentityGroup.cubeSumLower
#check @VectorSLT.IdentityGroup.prop_nonshear_upper
#check @VectorSLT.IdentityGroup.prop_nonshear_pair
#check @VectorSLT.IdentityGroup.thm_invertible_upper
#check @VectorSLT.IdentityGroup.thm_invertible_pair
#check @VectorSLT.IdentityGroup.lem_Abox_upper
#check @VectorSLT.LeadingMap.leading_expansion
#check @VectorSLT.LeadingMap.leading_term_unique
#check @VectorSLT.LeadingMap.prop_N1_table
#check @VectorSLT.LeadingMap.lemma_N3_position_two
#check @VectorSLT.LeadingMap.lemma_N3_position_three
#check @VectorSLT.LeadingMap.eq_KR_position_four
#check @VectorSLT.LeadingMap.lead_A0_eq_zero_iff
#check @VectorSLT.LeadingMap.net_expansion_four
#check @VectorSLT.LeadingMap.activeCoords_eq
#check @VectorSLT.LossCompare.change_of_variables
#check @VectorSLT.LossCompare.position_four_comparison
#check @VectorSLT.LossCompare.position_four_homogeneity
#check @VectorSLT.LossCompare.position_four_marginData
#check @VectorSLT.LossCompare.middle_comparison
#check @VectorSLT.LossCompare.position_two_homogeneity
#check @VectorSLT.LossCompare.position_three_homogeneity
#check @VectorSLT.LossCompare.middle_marginData

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
#check @VectorSLT.vector_near_shear_upper
#check @VectorSLT.vector_near_shear_upper_gaussian
#check @VectorSLT.vector_nonshear_pair
#check @VectorSLT.vector_invertible_pair
#check @VectorSLT.vector_identity_group_upper

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
#print axioms VectorSLT.X5_upper
#print axioms VectorSLT.X5_upper_two
#print axioms VectorSLT.X5_upper_gaussian
#print axioms VectorSLT.X5_upper_explicit
#print axioms VectorSLT.X5_upper_explicit_two
#print axioms VectorSLT.IdentityGroup.cubeSumUpper_one
#print axioms VectorSLT.IdentityGroup.cubeSumUpper_two
#print axioms VectorSLT.IdentityGroup.cubeSumUpper_three
#print axioms VectorSLT.IdentityGroup.cubeSumLower
#print axioms VectorSLT.IdentityGroup.prop_nonshear_upper
#print axioms VectorSLT.IdentityGroup.prop_nonshear_pair
#print axioms VectorSLT.IdentityGroup.thm_invertible_upper
#print axioms VectorSLT.IdentityGroup.thm_invertible_pair
#print axioms VectorSLT.IdentityGroup.lem_Abox_upper
#print axioms VectorSLT.LeadingMap.leading_expansion
#print axioms VectorSLT.LeadingMap.leading_term_unique
#print axioms VectorSLT.LeadingMap.prop_N1_table
#print axioms VectorSLT.LeadingMap.lemma_N3_position_two
#print axioms VectorSLT.LeadingMap.lemma_N3_position_three
#print axioms VectorSLT.LeadingMap.eq_KR_position_four
#print axioms VectorSLT.LeadingMap.lead_A0_eq_zero_iff
#print axioms VectorSLT.LeadingMap.net_expansion_four
#print axioms VectorSLT.LeadingMap.activeCoords_eq
#print axioms VectorSLT.LossCompare.change_of_variables
#print axioms VectorSLT.LossCompare.position_four_comparison
#print axioms VectorSLT.LossCompare.position_four_homogeneity
#print axioms VectorSLT.LossCompare.position_four_marginData
#print axioms VectorSLT.LossCompare.middle_comparison
#print axioms VectorSLT.LossCompare.position_two_homogeneity
#print axioms VectorSLT.LossCompare.position_three_homogeneity
#print axioms VectorSLT.LossCompare.middle_marginData
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
#print axioms VectorSLT.vector_near_shear_upper
#print axioms VectorSLT.vector_near_shear_upper_gaussian
#print axioms VectorSLT.vector_nonshear_pair
#print axioms VectorSLT.vector_invertible_pair
#print axioms VectorSLT.vector_identity_group_upper
