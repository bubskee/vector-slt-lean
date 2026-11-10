/-
Audit of every declaration of `VectorSLT/IdentityGroup/Pairs/*.lean` and `VectorSLT/IdentityGroup/Pairs.lean`,
one line each. Every line must report `[propext, Classical.choice, Quot.sound]` or a subset.
Run: `lake env lean -DwarningAsError=true -DautoImplicit=false VectorSLT/IdentityGroup/AuditPairs.lean`.
-/
import VectorSLT.IdentityGroup.Pairs

-- VectorSLT/IdentityGroup/Pairs/Absorb.lean
#print axioms VectorSLT.IdentityGroup.Pairs.uniform_lower_of_continuousAt
#print axioms VectorSLT.IdentityGroup.Pairs.uniform_lower_of_linear

-- VectorSLT/IdentityGroup/Pairs/GramDown.lean
#print axioms VectorSLT.IdentityGroup.Pairs.errPoly
#print axioms VectorSLT.IdentityGroup.Pairs.eval_errPoly
#print axioms VectorSLT.IdentityGroup.Pairs.errBox
#print axioms VectorSLT.IdentityGroup.Pairs.errBox_apply
#print axioms VectorSLT.IdentityGroup.Pairs.abs_eval_le_norm
#print axioms VectorSLT.IdentityGroup.Pairs.norm_errBox_sq_le
#print axioms VectorSLT.IdentityGroup.Pairs.norm_sq_le_L2
#print axioms VectorSLT.IdentityGroup.Pairs.gram_down

-- VectorSLT/IdentityGroup/Pairs/GroupCubic.lean
#print axioms VectorSLT.IdentityGroup.Pairs.rayHom
#print axioms VectorSLT.IdentityGroup.Pairs.eval_rayHom
#print axioms VectorSLT.IdentityGroup.Pairs.rayCub
#print axioms VectorSLT.IdentityGroup.Pairs.rayCub_bound
#print axioms VectorSLT.IdentityGroup.Pairs.grpPoly
#print axioms VectorSLT.IdentityGroup.Pairs.totalDegree_grpPoly
#print axioms VectorSLT.IdentityGroup.Pairs.grpErr
#print axioms VectorSLT.IdentityGroup.Pairs.eval_grpErr
#print axioms VectorSLT.IdentityGroup.Pairs.ray_polyNet
#print axioms VectorSLT.IdentityGroup.Pairs.rayCub_grpErr
#print axioms VectorSLT.IdentityGroup.Pairs.cubeSumSq_le_rays
#print axioms VectorSLT.IdentityGroup.Pairs.grpRow
#print axioms VectorSLT.IdentityGroup.Pairs.cubeSumSq_le_of_rayCub
#print axioms VectorSLT.IdentityGroup.Pairs.cubeSumSq_le_grpErr

-- VectorSLT/IdentityGroup/Pairs/Integrate.lean
#print axioms VectorSLT.IdentityGroup.Pairs.rowU
#print axioms VectorSLT.IdentityGroup.Pairs.triE
#print axioms VectorSLT.IdentityGroup.Pairs.triE_apply
#print axioms VectorSLT.IdentityGroup.Pairs.measurePreserving_triE
#print axioms VectorSLT.IdentityGroup.Pairs.rowE
#print axioms VectorSLT.IdentityGroup.Pairs.rowE_apply
#print axioms VectorSLT.IdentityGroup.Pairs.measurePreserving_rowE
#print axioms VectorSLT.IdentityGroup.Pairs.lintegral_rowU
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_cubeSumSq
#print axioms VectorSLT.IdentityGroup.Pairs.cubeSumSq_nonneg
#print axioms VectorSLT.IdentityGroup.Pairs.RowBound
#print axioms VectorSLT.IdentityGroup.Pairs.rowBound_three
#print axioms VectorSLT.IdentityGroup.Pairs.ofReal_mul_le_max
#print axioms VectorSLT.IdentityGroup.Pairs.rowBound_split
#print axioms VectorSLT.IdentityGroup.Pairs.actSq
#print axioms VectorSLT.IdentityGroup.Pairs.lintegral_act
#print axioms VectorSLT.IdentityGroup.Pairs.rowF
#print axioms VectorSLT.IdentityGroup.Pairs.layoutF
#print axioms VectorSLT.IdentityGroup.Pairs.layout_bound
#print axioms VectorSLT.IdentityGroup.Pairs.swapE
#print axioms VectorSLT.IdentityGroup.Pairs.swapE_swapE
#print axioms VectorSLT.IdentityGroup.Pairs.Sfun
#print axioms VectorSLT.IdentityGroup.Pairs.Sfun_Sfun
#print axioms VectorSLT.IdentityGroup.Pairs.Slin
#print axioms VectorSLT.IdentityGroup.Pairs.lintegral_Sfun
#print axioms VectorSLT.IdentityGroup.Pairs.inact
#print axioms VectorSLT.IdentityGroup.Pairs.inact_ne
#print axioms VectorSLT.IdentityGroup.Pairs.Sfun_act
#print axioms VectorSLT.IdentityGroup.Pairs.rowU_Sfun
#print axioms VectorSLT.IdentityGroup.Pairs.actSq_Sfun
#print axioms VectorSLT.IdentityGroup.Pairs.abs_tri_le
#print axioms VectorSLT.IdentityGroup.Pairs.abs_weights_le
#print axioms VectorSLT.IdentityGroup.Pairs.weights_sub
#print axioms VectorSLT.IdentityGroup.Pairs.weights_eq_sub_base
#print axioms VectorSLT.IdentityGroup.Pairs.inact_lt
#print axioms VectorSLT.IdentityGroup.Pairs.rowU_Sfun_norm
#print axioms VectorSLT.IdentityGroup.Pairs.position_bound

-- VectorSLT/IdentityGroup/Pairs/Endpoint.lean
#print axioms VectorSLT.IdentityGroup.Pairs.layer_apply'
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_layer_joint
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_weights
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_prefixNet_joint
#print axioms VectorSLT.IdentityGroup.Pairs.prefixNet_shift
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_eval_joint
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_polyBox_of
#print axioms VectorSLT.IdentityGroup.Pairs.upper_of_absorb
#print axioms VectorSLT.IdentityGroup.Pairs.pair_of_upper

-- VectorSLT/IdentityGroup/Pairs/FirstPosition.lean
#print axioms VectorSLT.IdentityGroup.Pairs.EndDom
#print axioms VectorSLT.IdentityGroup.Pairs.mulVec_two
#print axioms VectorSLT.IdentityGroup.Pairs.dot_two
#print axioms VectorSLT.IdentityGroup.Pairs.M0fun
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_M0fun
#print axioms VectorSLT.IdentityGroup.Pairs.M0
#print axioms VectorSLT.IdentityGroup.Pairs.M0_apply
#print axioms VectorSLT.IdentityGroup.Pairs.vFirst
#print axioms VectorSLT.IdentityGroup.Pairs.A_add_vFirst
#print axioms VectorSLT.IdentityGroup.Pairs.errBox_eq_M0
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_vFirst_fst
#print axioms VectorSLT.IdentityGroup.Pairs.vFirst_base
#print axioms VectorSLT.IdentityGroup.Pairs.first_absorb
#print axioms VectorSLT.IdentityGroup.Pairs.sum_sq_le_norm
#print axioms VectorSLT.IdentityGroup.Pairs.rowU_Sfun0
#print axioms VectorSLT.IdentityGroup.Pairs.first_compare
#print axioms VectorSLT.IdentityGroup.Pairs.eval_bind₁_eq
#print axioms VectorSLT.IdentityGroup.Pairs.eval_eq_zero_of_box
#print axioms VectorSLT.IdentityGroup.Pairs.layerPoly
#print axioms VectorSLT.IdentityGroup.Pairs.eval_layerPoly
#print axioms VectorSLT.IdentityGroup.Pairs.M0_kernel
#print axioms VectorSLT.IdentityGroup.Pairs.first_upper

-- VectorSLT/IdentityGroup/Pairs/NonShear.lean
#print axioms VectorSLT.IdentityGroup.Pairs.NonShearTarget
#print axioms VectorSLT.IdentityGroup.Pairs.lineHom
#print axioms VectorSLT.IdentityGroup.Pairs.eval_lineHom
#print axioms VectorSLT.IdentityGroup.Pairs.comp_cubic_eq
#print axioms VectorSLT.IdentityGroup.Pairs.decomp2
#print axioms VectorSLT.IdentityGroup.Pairs.nonshear_kernel
#print axioms VectorSLT.IdentityGroup.Pairs.polyBox_ext
#print axioms VectorSLT.IdentityGroup.Pairs.nonshear_injective
#print axioms VectorSLT.IdentityGroup.Pairs.nonshear_upper
#print axioms VectorSLT.IdentityGroup.Pairs.nonshear_pair

-- VectorSLT/IdentityGroup/Pairs/LemmaABox.lean
#print axioms VectorSLT.IdentityGroup.Pairs.grpBlocks
#print axioms VectorSLT.IdentityGroup.Pairs.grpJ
#print axioms VectorSLT.IdentityGroup.Pairs.grpRows
#print axioms VectorSLT.IdentityGroup.Pairs.grpRow_grpBlocks
#print axioms VectorSLT.IdentityGroup.Pairs.measurePreserving_grpRows
#print axioms VectorSLT.IdentityGroup.Pairs.norm_grpRows_le
#print axioms VectorSLT.IdentityGroup.Pairs.lemAbox_upper

-- VectorSLT/IdentityGroup/Pairs/PolyAlgebra.lean
#print axioms VectorSLT.IdentityGroup.Pairs.odd_poly_zero
#print axioms VectorSLT.IdentityGroup.Pairs.coeff_pow_mul_pow_cubic
#print axioms VectorSLT.IdentityGroup.Pairs.cubicHom
#print axioms VectorSLT.IdentityGroup.Pairs.eval_cubicHom
#print axioms VectorSLT.IdentityGroup.Pairs.coeff_aeval_cubic
#print axioms VectorSLT.IdentityGroup.Pairs.homogeneousComponent_totalDegree_ne_zero
#print axioms VectorSLT.IdentityGroup.Pairs.layer_smul
#print axioms VectorSLT.IdentityGroup.Pairs.totalDegree_le_one_of_odd
#print axioms VectorSLT.IdentityGroup.Pairs.eval_affine
#print axioms VectorSLT.IdentityGroup.Pairs.eq_zero_of_layer_odd
#print axioms VectorSLT.IdentityGroup.Pairs.lin_mul_sq_zero
#print axioms VectorSLT.IdentityGroup.Pairs.row_ne_zero

-- VectorSLT/IdentityGroup/Pairs/LastPosition.lean
#print axioms VectorSLT.IdentityGroup.Pairs.evalV
#print axioms VectorSLT.IdentityGroup.Pairs.M3fun
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_evalV_joint
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_M3fun
#print axioms VectorSLT.IdentityGroup.Pairs.M3
#print axioms VectorSLT.IdentityGroup.Pairs.M3_apply
#print axioms VectorSLT.IdentityGroup.Pairs.vLast
#print axioms VectorSLT.IdentityGroup.Pairs.errBox_eq_M3
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_vLast
#print axioms VectorSLT.IdentityGroup.Pairs.prefixNet_zero_blocks
#print axioms VectorSLT.IdentityGroup.Pairs.vLast_base
#print axioms VectorSLT.IdentityGroup.Pairs.last_absorb
#print axioms VectorSLT.IdentityGroup.Pairs.cubeSumSq_comp_equiv
#print axioms VectorSLT.IdentityGroup.Pairs.rowU_Sfun3
#print axioms VectorSLT.IdentityGroup.Pairs.last_compare
#print axioms VectorSLT.IdentityGroup.Pairs.last_upper

-- VectorSLT/IdentityGroup/Pairs/Invertible.lean
#print axioms VectorSLT.IdentityGroup.Pairs.mulVec_smul_apply
#print axioms VectorSLT.IdentityGroup.Pairs.invertible_first_injective
#print axioms VectorSLT.IdentityGroup.Pairs.M3_kernel
#print axioms VectorSLT.IdentityGroup.Pairs.last_kernel
#print axioms VectorSLT.IdentityGroup.Pairs.invertible_last_injective
#print axioms VectorSLT.IdentityGroup.Pairs.invertible_first_upper
#print axioms VectorSLT.IdentityGroup.Pairs.invertible_last_upper
#print axioms VectorSLT.IdentityGroup.Pairs.invertible_first_pair
#print axioms VectorSLT.IdentityGroup.Pairs.invertible_last_pair

-- VectorSLT/IdentityGroup/Pairs/OnePrefix.lean
#print axioms VectorSLT.IdentityGroup.Pairs.prefixNet_add
#print axioms VectorSLT.IdentityGroup.Pairs.cub
#print axioms VectorSLT.IdentityGroup.Pairs.cubV
#print axioms VectorSLT.IdentityGroup.Pairs.cubeCoeffs
#print axioms VectorSLT.IdentityGroup.Pairs.cub_cubeCoeffs
#print axioms VectorSLT.IdentityGroup.Pairs.cub_smul
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_cub_joint
#print axioms VectorSLT.IdentityGroup.Pairs.cubPoly
#print axioms VectorSLT.IdentityGroup.Pairs.eval_cubPoly
#print axioms VectorSLT.IdentityGroup.Pairs.cub_eq_zero
#print axioms VectorSLT.IdentityGroup.Pairs.OneDom
#print axioms VectorSLT.IdentityGroup.Pairs.OnePar
#print axioms VectorSLT.IdentityGroup.Pairs.M1fun
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_M1fun
#print axioms VectorSLT.IdentityGroup.Pairs.M1
#print axioms VectorSLT.IdentityGroup.Pairs.M1_apply
#print axioms VectorSLT.IdentityGroup.Pairs.vOne
#print axioms VectorSLT.IdentityGroup.Pairs.ηOne
#print axioms VectorSLT.IdentityGroup.Pairs.errBox_eq_M1
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_ηOne
#print axioms VectorSLT.IdentityGroup.Pairs.ηOne_base
#print axioms VectorSLT.IdentityGroup.Pairs.one_absorb
#print axioms VectorSLT.IdentityGroup.Pairs.M1_kernel
#print axioms VectorSLT.IdentityGroup.Pairs.onePrefix_injective
#print axioms VectorSLT.IdentityGroup.Pairs.gOne
#print axioms VectorSLT.IdentityGroup.Pairs.cubeSumSq_one_le
#print axioms VectorSLT.IdentityGroup.Pairs.one_compare
#print axioms VectorSLT.IdentityGroup.Pairs.measurable_gOne
#print axioms VectorSLT.IdentityGroup.Pairs.invertible_two_upper
#print axioms VectorSLT.IdentityGroup.Pairs.invertible_two_pair

-- VectorSLT/IdentityGroup/Pairs/Quintic.lean
#print axioms VectorSLT.IdentityGroup.Pairs.quin
#print axioms VectorSLT.IdentityGroup.Pairs.quinV
#print axioms VectorSLT.IdentityGroup.Pairs.quin_smul
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_quin_joint
#print axioms VectorSLT.IdentityGroup.Pairs.quinPoly
#print axioms VectorSLT.IdentityGroup.Pairs.eval_quinPoly
#print axioms VectorSLT.IdentityGroup.Pairs.quin_eq_zero
#print axioms VectorSLT.IdentityGroup.Pairs.mulQuint
#print axioms VectorSLT.IdentityGroup.Pairs.quin_mulQuint
#print axioms VectorSLT.IdentityGroup.Pairs.mulQuint_smul
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_mulQuint
#print axioms VectorSLT.IdentityGroup.Pairs.mulQuint_eq_zero
#print axioms VectorSLT.IdentityGroup.Pairs.mulQuint_lower

-- VectorSLT/IdentityGroup/Pairs/TwoPrefix.lean
#print axioms VectorSLT.IdentityGroup.Pairs.cub_add
#print axioms VectorSLT.IdentityGroup.Pairs.cub_smul_coeff
#print axioms VectorSLT.IdentityGroup.Pairs.quin_smul_coeff
#print axioms VectorSLT.IdentityGroup.Pairs.abs_coord_le_one
#print axioms VectorSLT.IdentityGroup.Pairs.abs_dot_le
#print axioms VectorSLT.IdentityGroup.Pairs.abs_cub_le
#print axioms VectorSLT.IdentityGroup.Pairs.norm_cubeCoeffs_le
#print axioms VectorSLT.IdentityGroup.Pairs.TwoDom
#print axioms VectorSLT.IdentityGroup.Pairs.TwoPar
#print axioms VectorSLT.IdentityGroup.Pairs.gV
#print axioms VectorSLT.IdentityGroup.Pairs.M2fun
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_M2fun
#print axioms VectorSLT.IdentityGroup.Pairs.M2
#print axioms VectorSLT.IdentityGroup.Pairs.M2_apply
#print axioms VectorSLT.IdentityGroup.Pairs.psiTwo
#print axioms VectorSLT.IdentityGroup.Pairs.vTwo
#print axioms VectorSLT.IdentityGroup.Pairs.ηTwo
#print axioms VectorSLT.IdentityGroup.Pairs.Rtwo
#print axioms VectorSLT.IdentityGroup.Pairs.cub_psiTwo
#print axioms VectorSLT.IdentityGroup.Pairs.Rtwo_eq
#print axioms VectorSLT.IdentityGroup.Pairs.err_split
#print axioms VectorSLT.IdentityGroup.Pairs.norm_psiTwo_le
#print axioms VectorSLT.IdentityGroup.Pairs.abs_R_le
#print axioms VectorSLT.IdentityGroup.Pairs.amax
#print axioms VectorSLT.IdentityGroup.Pairs.amax_nonneg
#print axioms VectorSLT.IdentityGroup.Pairs.abs_mulVec_le
#print axioms VectorSLT.IdentityGroup.Pairs.norm_E_le
#print axioms VectorSLT.IdentityGroup.Pairs.continuous_ηTwo
#print axioms VectorSLT.IdentityGroup.Pairs.ηTwo_base
#print axioms VectorSLT.IdentityGroup.Pairs.two_absorb
#print axioms VectorSLT.IdentityGroup.Pairs.homDeg_cubV
#print axioms VectorSLT.IdentityGroup.Pairs.homDeg_quinV
#print axioms VectorSLT.IdentityGroup.Pairs.homDeg_zero5
#print axioms VectorSLT.IdentityGroup.Pairs.M2_kernel
#print axioms VectorSLT.IdentityGroup.Pairs.twoPrefix_injective
#print axioms VectorSLT.IdentityGroup.Pairs.gTwo
#print axioms VectorSLT.IdentityGroup.Pairs.measurable_gTwo
#print axioms VectorSLT.IdentityGroup.Pairs.cubeSumSq_two_le
#print axioms VectorSLT.IdentityGroup.Pairs.two_compare
#print axioms VectorSLT.IdentityGroup.Pairs.invertible_three_upper
#print axioms VectorSLT.IdentityGroup.Pairs.invertible_three_pair

-- VectorSLT/IdentityGroup/Pairs.lean
#print axioms VectorSLT.IdentityGroup.Pairs.paper_lemAbox_upper
#print axioms VectorSLT.IdentityGroup.Pairs.paper_nonshear_upper
#print axioms VectorSLT.IdentityGroup.Pairs.paper_nonshear_pair
#print axioms VectorSLT.IdentityGroup.Pairs.paper_invertible_upper
#print axioms VectorSLT.IdentityGroup.Pairs.paper_invertible_pair

