import VectorSLT.EtaUpper

/-! Axiom audit for Proposition X5 (`VectorSLT.EtaUpper`). One line per public declaration;
each should print only `propext`, `Classical.choice`, `Quot.sound` (or a subset). -/

-- EtaUpper/GdownEta.lean
#print axioms VectorSLT.errXη_mem
#print axioms VectorSLT.errXη
#print axioms VectorSLT.coeffST_errXη
#print axioms VectorSLT.eval_errXη
#print axioms VectorSLT.c2Mη
#print axioms VectorSLT.c1Mη
#print axioms VectorSLT.coeffs_errθη
#print axioms VectorSLT.Gdown_eta

-- EtaUpper/SliceEta.lean
#print axioms VectorSLT.quadForm_add_affine
#print axioms VectorSLT.slice_exists_eta
#print axioms VectorSLT.lemmaM4_eta

-- EtaUpper/RowBoundEta.lean
#print axioms VectorSLT.rowIntη
#print axioms VectorSLT.pivotRow_eta
#print axioms VectorSLT.rowActη
#print axioms VectorSLT.rowActη_piv
#print axioms VectorSLT.rowBound_eta
#print axioms VectorSLT.rowBound_M6_eta

-- EtaUpper/TheoremMEta.lean
#print axioms VectorSLT.TMxη
#print axioms VectorSLT.SMxη
#print axioms VectorSLT.sum_coeffs_eq_eta
#print axioms VectorSLT.A1_core'
#print axioms VectorSLT.P1t_sub_le
#print axioms VectorSLT.TMxη_le_SMxη
#print axioms VectorSLT.Hwη
#print axioms VectorSLT.split_exp_eta
#print axioms VectorSLT.F0rη
#print axioms VectorSLT.F1rη
#print axioms VectorSLT.Hwη_split
#print axioms VectorSLT.measurable_F0rη
#print axioms VectorSLT.measurable_F1rη
#print axioms VectorSLT.J_bound_eta
#print axioms VectorSLT.UM_inner_eta
#print axioms VectorSLT.UM_c_eta
#print axioms VectorSLT.UM_bound_eta
#print axioms VectorSLT.SMxη_nonneg
#print axioms VectorSLT.theoremM_eta

-- EtaUpper/X5.lean
#print axioms VectorSLT.toM2_mem_UM_eta
#print axioms VectorSLT.prior_le_indicator_eta
#print axioms VectorSLT.X5_upper_explicit
#print axioms VectorSLT.isCompact_UM
#print axioms VectorSLT.volume_UM_ne_top
#print axioms VectorSLT.Zpos_le_volume_UM
#print axioms VectorSLT.X5_upper_explicit_two

-- EtaUpper.lean
#print axioms VectorSLT.X5_upper
#print axioms VectorSLT.X5_upper_two
#print axioms VectorSLT.X5_upper_gaussian
