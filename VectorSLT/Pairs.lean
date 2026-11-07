/-
L4 follow-up: restating milestones C and D through `VectorSLT.SLT.LaplaceLower`.
-/
import VectorSLT.SLT.Laplace
import VectorSLT.Separation

namespace VectorSLT

open MeasureTheory Set Filter Topology

theorem rpow_neg_natCast_eq {N : ℝ} (hN : 0 < N) (n : ℕ) : N ^ (-(n : ℝ)) = N⁻¹ ^ n := by
  rw [Real.rpow_neg hN.le, Real.rpow_natCast, inv_pow]

/-- Turn a bound `c N⁻ⁿ (log N)^{m-1} ≤ Z(N)` (for `N ≥ N₀`) into `LaplaceLower Z n m`. -/
theorem laplaceLower_of_bound {Zf : ℝ → ENNReal} {n m : ℕ} {c N₀ : ℝ} (hc : 0 < c)
    (h : ∀ N, N₀ ≤ N → ENNReal.ofReal (c * N⁻¹ ^ n * Real.log N ^ (m - 1)) ≤ Zf N) :
    VectorSLT.SLT.LaplaceLower Zf n m := by
  refine ⟨c, hc, max N₀ 1, fun N hN => ?_⟩
  have hN0 : 0 < N := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hN)
  rw [rpow_neg_natCast_eq hN0]
  exact h N ((le_max_left _ _).trans hN)

/-- Milestone C (leading model, `λ = 4`, `m = 5`) as a Laplace lower half. -/
theorem leadingModel_laplaceLower {ε : ℝ} (hε : 0 < ε) :
    VectorSLT.SLT.LaplaceLower (VectorSLT.SLT.Z (volume.restrict (box16 ε)) K0) 4 5 := by
  have hcC : 0 < cC := by unfold cC; norm_num
  refine laplaceLower_of_bound (c := Real.exp (-3) * (cC ^ 2 / 16))
    (N₀ := max (max 1 ((4 / ε) ^ 10)) (1 / ε ^ 2)) (by positivity) fun N hN => ?_
  exact leadingModel_lower hε hN

/-- Milestone C (one row, `λ = 1`, `m = 3`) as a Laplace lower half. -/
theorem row_laplaceLower {ε : ℝ} (hε : 0 < ε) :
    VectorSLT.SLT.LaplaceLower (VectorSLT.SLT.Z (volume.restrict {x : (Fin 3 → ℝ) × (Fin 3 → ℝ) |
      (∀ i, x.1 i ∈ Icc (-ε) ε) ∧ (∀ i, x.2 i ∈ Icc (-ε) ε)}) (fun x => rowPsq x.1 x.2)) 1 3 := by
  have hcC : 0 < cC := by unfold cC; norm_num
  have := laplaceLower_of_bound (Zf := VectorSLT.SLT.Z (volume.restrict {x : (Fin 3 → ℝ) × (Fin 3 → ℝ) |
      (∀ i, x.1 i ∈ Icc (-ε) ε) ∧ (∀ i, x.2 i ∈ Icc (-ε) ε)}) (fun x => rowPsq x.1 x.2))
    (n := 1) (m := 3) (c := Real.exp (-1) * cC)
    (N₀ := max 1 ((4 / ε) ^ 10)) (by positivity) (fun N hN => by
      have h := rowLaplace_lower hε hN
      simp only [pow_one, show 3 - 1 = 2 from rfl] at h ⊢
      exact h)
  simpa only [Nat.cast_one] using this

/-- Milestone D / L2 (Proposition L′, every two-nonzero-row shear target) as a Laplace lower
half with `(λ, m) = (4, 5)`. -/
theorem position_one_laplaceLower {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) {R : ℝ}
    (μ : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, ∀ i, |x i| ≤ R)
    (φ χ : Raw16 → ENNReal) {φ₀ χ₀ : ℝ} (hφ₀ : 0 < φ₀) (hχ₀ : 0 < χ₀)
    (hφ : ∀ᶠ θ in 𝓝 (basePos A 0), ENNReal.ofReal φ₀ ≤ φ θ)
    (hχ : ∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) :
    VectorSLT.SLT.LaplaceLower (Zpos μ A φ χ 0) 4 5 := by
  obtain ⟨c, hc, N₀, h⟩ := Zpos_one_lower hA μ hμ φ χ hφ₀ hχ₀ hφ hχ
  have := laplaceLower_of_bound (n := 4) (m := 5) hc h
  simpa only [Nat.cast_ofNat] using this

/-- Theorem K's (K1) in pair language, `(λ, m) = (4, 1)`. -/
theorem ThmK.hasLaplacePair {μ : Measure (Fin 2 → ℝ)} {A : Matrix (Fin 2) (Fin 2) ℝ}
    {φ χ : Raw16 → ENNReal} (h : ThmK μ A φ χ) : VectorSLT.SLT.HasLaplacePair (Zpos μ A φ χ 3) 4 1 := by
  obtain ⟨c, C, N₀, hc, hK⟩ := h
  refine ⟨⟨c, hc, max N₀ 1, fun N hN => ?_⟩, ⟨C, max N₀ 1, fun N hN => ?_⟩⟩ <;>
  · have hN0 : 0 < N := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hN)
    have := hK N ((le_max_left _ _).trans hN)
    simp only [Nat.sub_self, pow_zero, mul_one]
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, rpow_neg_natCast_eq hN0]
    first | exact this.1 | exact this.2

end VectorSLT
