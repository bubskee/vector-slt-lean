import VectorSLT.IdentityGroup.Unconditional
import VectorSLT.EtaUpper

/-! Axiom audit for the joined, unconditional paper-2 statements: Proposition `prop:nonshear`,
Theorem `thm:invertible`, Lemma `lem:A-box` (upper half, groups of at most three blocks), and
Proposition X5. Run: `lake env lean VectorSLT/IdentityGroup/AuditUnconditional.lean`. The
component audits are `AuditCubes.lean`, `AuditPairs.lean` and `EtaUpper/AuditX5.lean`. -/

#print axioms VectorSLT.IdentityGroup.prop_nonshear_upper
#print axioms VectorSLT.IdentityGroup.prop_nonshear_pair
#print axioms VectorSLT.IdentityGroup.thm_invertible_upper
#print axioms VectorSLT.IdentityGroup.thm_invertible_pair
#print axioms VectorSLT.IdentityGroup.lem_Abox_upper
#print axioms VectorSLT.X5_upper
#print axioms VectorSLT.X5_upper_two
