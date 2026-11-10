/-
The Proposition N1 table (item 2 of the leading-map brief; paper 2, Appendix E.1).

For the shear target `A₀ = [[1,-1],[1,-1]]`, in the coordinates `s = x₀ - x₁`, `t = x₁`, row `k` of
the leading term `lead A₀ p Δ V x` is an explicit polynomial in `(s, t)` with eleven monomials
`s³, s²t, st², t³, s⁵, s⁴t, s³t², s²t³, s⁷, s⁶t, s⁹` (`poly11`). Its coefficients (`n1Coeff`) are
moments `P_i[X] = ∑_{l ∈ X} a_l^{3-i} b_l^i` of the row forms `a s + b t` of the inactive blocks
(`a = V_l k 0`, `b = V_l k 0 + V_l k 1`) over the prefix, the suffix or all inactive blocks, plus
the active terms `3 Δ_{k0}` and `3 (Δ_{k0} + Δ_{k1})`. The table is derived in Lean
(`lead_A0_eq_table`), at every position (at Lean `p = 0` the prefix is empty).
-/
import VectorSLT.LeadingMap.Expansion

namespace VectorSLT.LeadingMap

open Matrix Finset

/-! ### Row forms and moments -/

/-- Row `k` of a block `B`, as the form `a s + b t` of the state in the coordinates
`(s, t) = (z₀ - z₁, z₁)`: `(a, b) = (B k 0, B k 0 + B k 1)`. -/
def rowForm (B : Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) : ℝ × ℝ := (B k 0, B k 0 + B k 1)

theorem dot_rowForm (B : Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) (z : Fin 2 → ℝ) :
    (B *ᵥ z) k = (rowForm B k).1 * (z 0 - z 1) + (rowForm B k).2 * z 1 := by
  simp [rowForm, mulVec, dotProduct, Fin.sum_univ_two]; ring

/-- The moment `P_i^{(k)}[X] = ∑_{l ∈ X} a_l^{3-i} b_l^i` of row `k` over a set `X` of inactive
blocks (paper: `P_i^{(k)}[X]`, Appendix E.1). -/
def mom (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (X : Finset (Fin 3)) (k : Fin 2) (i : ℕ) : ℝ :=
  ∑ l ∈ X, (rowForm (V l) k).1 ^ (3 - i) * (rowForm (V l) k).2 ^ i

/-- `D_i = P_i^{(1)}[prefix] - P_i^{(2)}[prefix]` (Lean rows `0` and `1`; the paper's table writes
`Δ_i` for this). -/
def momD (p : Fin 4) (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (i : ℕ) : ℝ :=
  mom V (pre p) 0 i - mom V (pre p) 1 i

/-! ### The eleven monomials -/

/-- `κ₀ s³ + κ₁ s²t + κ₂ st² + κ₃ t³ + κ₄ s⁵ + κ₅ s⁴t + κ₆ s³t² + κ₇ s²t³ + κ₈ s⁷ + κ₉ s⁶t + κ₁₀ s⁹`. -/
def poly11 (κ : Fin 11 → ℝ) (s t : ℝ) : ℝ :=
  κ 0 * s ^ 3 + κ 1 * s ^ 2 * t + κ 2 * s * t ^ 2 + κ 3 * t ^ 3 + κ 4 * s ^ 5 +
    κ 5 * s ^ 4 * t + κ 6 * s ^ 3 * t ^ 2 + κ 7 * s ^ 2 * t ^ 3 + κ 8 * s ^ 7 +
    κ 9 * s ^ 6 * t + κ 10 * s ^ 9

/-- A cubic in `t` that vanishes identically has zero coefficients. -/
theorem cubic_coeffs_zero {c₀ c₁ c₂ c₃ : ℝ} (h : ∀ t : ℝ, c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3 = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h (-1); have h3 := h 2
  norm_num at h0 h1 h2 h3
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **The eleven monomials are linearly independent as functions.** -/
theorem poly11_eq_zero {κ : Fin 11 → ℝ} (h : ∀ s t, poly11 κ s t = 0) : κ = 0 := by
  have hc : ∀ s : ℝ, (κ 0 * s ^ 3 + κ 4 * s ^ 5 + κ 8 * s ^ 7 + κ 10 * s ^ 9 = 0) ∧
      (κ 1 * s ^ 2 + κ 5 * s ^ 4 + κ 9 * s ^ 6 = 0) ∧ (κ 2 * s + κ 6 * s ^ 3 = 0) ∧
      (κ 3 + κ 7 * s ^ 2 = 0) := by
    intro s
    exact cubic_coeffs_zero fun t => by rw [← h s t, poly11]; ring
  obtain ⟨a1, b1, c1, d1⟩ := hc 1
  obtain ⟨a2, b2, c2, d2⟩ := hc 2
  obtain ⟨a3, b3, -, -⟩ := hc 3
  obtain ⟨a4, -, -, -⟩ := hc 4
  norm_num at a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 a4
  funext i
  fin_cases i <;> simp <;> linarith

/-! ### The table -/

/-- **The Proposition N1 table**, row `k`, as the coefficient vector of `poly11`:

| monomial | coefficient |
|---|---|
| `s³` | `3 Δ_{k0} + P₀[all]` |
| `s²t` | `3 (Δ_{k0} + Δ_{k1}) + 3 P₁[all]` |
| `st²` | `3 P₂[all]` |
| `t³` | `P₃[all]` |
| `s⁵` | `3 (D₀ + P₁[suf])` |
| `s⁴t` | `3 (3 D₁ + 2 P₂[suf])` |
| `s³t²` | `3 (3 D₂ + P₃[suf])` |
| `s²t³` | `3 D₃` |
| `s⁷` | `3 P₂[suf]` |
| `s⁶t` | `3 P₃[suf]` |
| `s⁹` | `P₃[suf]` |

with all moments those of row `k` except `D_i = P_i^{(0)}[pre] - P_i^{(1)}[pre]`. -/
def n1Coeff (p : Fin 4) (Δ : Matrix (Fin 2) (Fin 2) ℝ) (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ)
    (k : Fin 2) : Fin 11 → ℝ :=
  ![3 * Δ k 0 + mom V univ k 0, 3 * (Δ k 0 + Δ k 1) + 3 * mom V univ k 1,
    3 * mom V univ k 2, mom V univ k 3,
    3 * (momD p V 0 + mom V (suf p) k 1), 3 * (3 * momD p V 1 + 2 * mom V (suf p) k 2),
    3 * (3 * momD p V 2 + mom V (suf p) k 3), 3 * momD p V 3,
    3 * mom V (suf p) k 2, 3 * mom V (suf p) k 3, mom V (suf p) k 3]

/-- **Proposition N1, derived.** For the shear target `A₀`, at every position `p`, row `k` of
the leading term is the table polynomial in `s = x₀ - x₁`, `t = x₁`. -/
theorem lead_A0_eq_table (p : Fin 4) (Δ : Matrix (Fin 2) (Fin 2) ℝ)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) (k : Fin 2) :
    lead A0 p Δ V x k = poly11 (n1Coeff p Δ V k) (x 0 - x 1) (x 1) := by
  have hF : layer A0 x = ![x 0 + (x 0 - x 1) ^ 3, x 1 + (x 0 - x 1) ^ 3] := layer_A0 x
  have hA : ∀ z : Fin 2 → ℝ, A0 *ᵥ z = fun _ => z 0 - z 1 := by
    intro z; funext j; fin_cases j <;> simp [A0, mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  simp only [lead, dLayer, Spre, Ssuf, hA, hF, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
    Finset.sum_apply, Pi.ofNat_apply, dot_rowForm]
  simp only [poly11, n1Coeff, momD, mom]
  fin_cases p <;> fin_cases k <;>
    simp [pre, suf, Finset.sum_filter, Fin.sum_univ_three, rowForm] <;> ring

end VectorSLT.LeadingMap
