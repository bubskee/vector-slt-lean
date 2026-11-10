/-
The leading maps of the shear target at positions two, three and four (paper 2, Proposition N1
and Lemma N3 of Appendix E.1, equation (K-R) of Appendix D.1).

* `VectorSLT/LeadingMap/Expansion.lean`: `net θ_ε = F_A + ε³ lead + O(ε⁶)` for every target and
  position (`net_expansion`), by first-order perturbation through the four layers.
* `VectorSLT/LeadingMap/Table.lean`: for `A₀`, `lead` is the Proposition N1 table in `(s, t)`
  (`lead_A0_eq_table`), derived, at every position.
* `VectorSLT/LeadingMap/Generators.lean`: real mirrors of slt-bridge's `generators`, `R2`, `R3`,
  `leadingMap`, and the generator vectors `gens2`, `gens3`, `gens4` of the inactive blocks.
* `VectorSLT/LeadingMap/Tie.lean`: `lead A₀ p Δ V = Λ_p (c(Δ, V), gens_p V)` with `Λ_p` linear and
  injective and `Δ ↦ c(Δ, V)` a bijection (Lemma N3; (K-R) at position four).

This file restates the headline theorems. Notes: `VectorSLT/LeadingMap/NOTES_leading.md`.
-/
import VectorSLT.LeadingMap.Tie

namespace VectorSLT.LeadingMap

open Asymptotics Filter Topology

/-- **The expansion.** For every target `A`, Lean position `p`, perturbation `Δ` of the active
block and inactive blocks `V` (parameter `θ_ε`: active `A + ε³ Δ`, inactive `ε V_l`), every input
`x` and output `k`: `net θ_ε x k - F_A(x)_k - ε³ lead A p Δ V x k = O(ε⁶)` as `ε → 0`. -/
theorem leading_expansion (A Δ : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) (k : Fin 2) :
    (fun ε => net (thetaEps A Δ p V ε) x k - layer A x k - ε ^ 3 * lead A p Δ V x k)
      =O[𝓝 0] fun ε : ℝ => ε ^ 6 :=
  net_expansion A Δ p V x k

/-- **Proposition N1** (derived): for `A₀`, row `k` of the leading term is the N1 table
polynomial in `s = x₀ - x₁`, `t = x₁`. -/
theorem prop_N1_table (p : Fin 4) (Δ : Matrix (Fin 2) (Fin 2) ℝ)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) (k : Fin 2) :
    lead A0 p Δ V x k = poly11 (n1Coeff p Δ V k) (x 0 - x 1) (x 1) :=
  lead_A0_eq_table p Δ V x k

/-- **Lemma N3 at position two** (Lean `p = 1`): the leading term is `Λ_mid` of the active
coordinates and slt-bridge's `R2`; `Λ_mid` is injective; the active coordinates are a bijection
of `Δ` for every `V`. -/
theorem lemma_N3_position_two :
    (∀ Δ V, lead A0 1 Δ V = LamMid (activeCoords Δ V, R2 (w2 V))) ∧
      Function.Injective LamMid ∧ ∀ V, Function.Bijective fun Δ => activeCoords Δ V :=
  ⟨lead_A0_pos2, LamMid_injective, activeCoords_bijective⟩

/-- **Lemma N3 at position three** (Lean `p = 2`), with slt-bridge's `R3`. -/
theorem lemma_N3_position_three :
    (∀ Δ V, lead A0 2 Δ V = LamMid (activeCoords Δ V, R3 (w3 V))) ∧
      Function.Injective LamMid ∧ ∀ V, Function.Bijective fun Δ => activeCoords Δ V :=
  ⟨lead_A0_pos3, LamMid_injective, activeCoords_bijective⟩

/-- **Equation (K-R) at position four** (Lean `p = 3`), with slt-bridge's `leadingMap`. -/
theorem eq_KR_position_four :
    (∀ Δ V, lead A0 3 Δ V = LamFour (activeCoords Δ V, leadingMap (w4 V))) ∧
      Function.Injective LamFour ∧ ∀ V, Function.Bijective fun Δ => activeCoords Δ V :=
  ⟨lead_A0_pos4, LamFour_injective, activeCoords_bijective⟩

/-- **The `ε³` term vanishes exactly on the zero set of the active coordinates and the
slt-bridge leading map**, at positions two, three and four. -/
theorem lead_A0_eq_zero_iff (Δ : Matrix (Fin 2) (Fin 2) ℝ)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) :
    (lead A0 1 Δ V = 0 ↔ activeCoords Δ V = 0 ∧ R2 (w2 V) = 0) ∧
      (lead A0 2 Δ V = 0 ↔ activeCoords Δ V = 0 ∧ R3 (w3 V) = 0) ∧
      (lead A0 3 Δ V = 0 ↔ activeCoords Δ V = 0 ∧ leadingMap (w4 V) = 0) :=
  ⟨lead_A0_pos2_eq_zero_iff Δ V, lead_A0_pos3_eq_zero_iff Δ V, lead_A0_pos4_eq_zero_iff Δ V⟩

end VectorSLT.LeadingMap
