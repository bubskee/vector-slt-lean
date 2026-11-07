/-
Brief 04, X4 for the population loss: `Z_{N}(A_η) ≥ c N⁻⁴ (1 + 𝓛_η(N))⁴` uniformly in
`|η| ≤ 1/10`, for every input law with finite 162nd moments (standard Gaussian included) and
for every compactly supported law, on the common footing of `Zpos`.

The only new ingredient beyond `X4_lower` is that the moment form of (G↑) has a constant `Λ`
independent of the target (it comes from `l2_le_sup`, which never sees `A`).
-/
import VectorSLT.EtaLower
import VectorSLT.TwoSidedLaws

namespace VectorSLT

open MeasureTheory Set Filter Topology MvPolynomial

/-- **(G↑) for moment laws, uniform in the target**: one `Λ` serves every `A`. -/
theorem popLossA_le_moments_unif (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) :
    ∃ Λ : ℝ, ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) θ M, 0 ≤ M → (∀ x : Fin 2 → ℝ, (∀ i, |x i| ≤ 1) →
      ∀ k, |net θ x k - layer A x k| ≤ M) → popLossA μ A θ ≤ Λ * M ^ 2 := by
  obtain ⟨C, hC, hL2⟩ := l2_le_sup 81 μ hmom
  refine ⟨2 * C, fun A θ M hM hbd => ?_⟩
  choose p hpdeg hpeval using fun k => error_isPoly (weights θ) A k
  set q : Fin 2 → PolyBox 81 := fun k => PolyBox.mk (p k) (hpdeg k)
  have hq : ∀ k, ‖q k‖ ≤ M := fun k => PolyBox.norm_le hM fun x hx => by
    simp only [q, PolyBox.poly_mk, hpeval]; exact hbd x hx k
  have hfun : (fun x => ∑ k, (net θ x k - layer A x k) ^ 2) =
      fun x => ∑ k, eval x (q k).poly ^ 2 := by
    funext x; congr 1; funext k; simp only [q, PolyBox.poly_mk, hpeval]; rfl
  unfold popLossA
  rw [hfun, integral_finsetSum _ fun k _ => (hL2 (q k)).1, Fin.sum_univ_two]
  have h0 := (hL2 (q 0)).2
  have h1 := (hL2 (q 1)).2
  have e0 : ‖q 0‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hq 0) 2
  have e1 : ‖q 1‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hq 1) 2
  nlinarith [mul_le_mul_of_nonneg_left e0 hC, mul_le_mul_of_nonneg_left e1 hC]

/-- The common-footing prior `φ(θ) χ(θ - θ₀(η))` is `≥ φ₀ χ₀` within `r₀` of the base point,
once `φ ≥ φ₀` on the `r₀`-neighbourhood of the segment and `χ ≥ χ₀` on the `r₀`-ball. -/
theorem prior_floor {φ χ : Raw16 → ENNReal} {φ₀ χ₀ r₀ η : ℝ} (hφ₀ : 0 < φ₀)
    (hφ : ∀ θ, dist θ (basePos (Aeta η) 0) < r₀ → ENNReal.ofReal φ₀ ≤ φ θ)
    (hχ : ∀ θ, ‖θ‖ < r₀ → ENNReal.ofReal χ₀ ≤ χ θ) :
    ∀ θ, dist θ (basePos (Aeta η) 0) < r₀ →
      ENNReal.ofReal (φ₀ * χ₀) ≤ φ θ * χ (θ - basePos (Aeta η) 0) := by
  intro θ hθ
  rw [ENNReal.ofReal_mul hφ₀.le]
  exact mul_le_mul' (hφ θ hθ) (hχ _ (by rwa [← dist_eq_norm]))

/-- **X4 for moment laws** (`X4_lower_population`). For a finite input law with finite 162nd
moments, a prior factor `φ ≥ φ₀` on the `r₀`-neighbourhood of the whole segment of base points
`{(A_η, 0, 0, 0) : |η| ≤ 1/10}`, and a cutoff `χ ≥ χ₀` on the `r₀`-ball, there are `c > 0` and
`N₀` such that for **all** `|η| ≤ 1/10` and `N ≥ N₀`,
`Z_{N,1}(A_η) ≥ c N⁻⁴ (1 + 𝓛_η(N))⁴`. -/
theorem X4_lower_population (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    (φ χ : Raw16 → ENNReal) {φ₀ χ₀ r₀ : ℝ} (hφ₀ : 0 < φ₀) (hχ₀ : 0 < χ₀) (hr₀ : 0 < r₀)
    (hφ : ∀ η', |η'| ≤ 1 / 10 → ∀ θ, dist θ (basePos (Aeta η') 0) < r₀ → ENNReal.ofReal φ₀ ≤ φ θ)
    (hχ : ∀ θ, ‖θ‖ < r₀ → ENNReal.ofReal χ₀ ≤ χ θ) :
    ∃ c N₀ : ℝ, 0 < c ∧ ∀ η : ℝ, |η| ≤ 1 / 10 → ∀ N : ℝ, N₀ ≤ N →
      ENNReal.ofReal (c * N⁻¹ ^ 4 * (1 + Leta η N) ^ 4) ≤ Zpos μ (Aeta η) φ χ 0 N := by
  obtain ⟨Λ, hΛ⟩ := popLossA_le_moments_unif μ hmom
  obtain ⟨c, N₀, hc, h⟩ := X4_lower (Λ := Λ) (le_refl (1 : ℝ)) (mul_pos hφ₀ hχ₀) hr₀
  exact ⟨c, N₀, hc, fun η hη N hN =>
    h η hη (popLossA μ (Aeta η)) (hΛ (Aeta η)) _ (prior_floor hφ₀ (hφ η hη) hχ) N hN⟩

/-- **X4 for the standard Gaussian input law.** -/
theorem X4_lower_gaussian (φ χ : Raw16 → ENNReal) {φ₀ χ₀ r₀ : ℝ} (hφ₀ : 0 < φ₀) (hχ₀ : 0 < χ₀)
    (hr₀ : 0 < r₀)
    (hφ : ∀ η', |η'| ≤ 1 / 10 → ∀ θ, dist θ (basePos (Aeta η') 0) < r₀ → ENNReal.ofReal φ₀ ≤ φ θ)
    (hχ : ∀ θ, ‖θ‖ < r₀ → ENNReal.ofReal χ₀ ≤ χ θ) :
    ∃ c N₀ : ℝ, 0 < c ∧ ∀ η : ℝ, |η| ≤ 1 / 10 → ∀ N : ℝ, N₀ ≤ N →
      ENNReal.ofReal (c * N⁻¹ ^ 4 * (1 + Leta η N) ^ 4) ≤ Zpos stdGauss2 (Aeta η) φ χ 0 N :=
  X4_lower_population stdGauss2 (fun i => stdGauss2_moments _ i) φ χ hφ₀ hχ₀ hr₀ hφ hχ

/-- **X4 for compactly supported laws** (`|xᵢ| ≤ R` a.s., `Λ = 2`). -/
theorem X4_lower_compact {R : ℝ} (hR : 1 ≤ R) (μ : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ∀ i, |x i| ≤ R)
    (φ χ : Raw16 → ENNReal) {φ₀ χ₀ r₀ : ℝ} (hφ₀ : 0 < φ₀) (hχ₀ : 0 < χ₀) (hr₀ : 0 < r₀)
    (hφ : ∀ η', |η'| ≤ 1 / 10 → ∀ θ, dist θ (basePos (Aeta η') 0) < r₀ → ENNReal.ofReal φ₀ ≤ φ θ)
    (hχ : ∀ θ, ‖θ‖ < r₀ → ENNReal.ofReal χ₀ ≤ χ θ) :
    ∃ c N₀ : ℝ, 0 < c ∧ ∀ η : ℝ, |η| ≤ 1 / 10 → ∀ N : ℝ, N₀ ≤ N →
      ENNReal.ofReal (c * N⁻¹ ^ 4 * (1 + Leta η N) ^ 4) ≤ Zpos μ (Aeta η) φ χ 0 N := by
  obtain ⟨c, N₀, hc, h⟩ := X4_lower (Λ := 2) hR (mul_pos hφ₀ hχ₀) hr₀
  exact ⟨c, N₀, hc, fun η hη N hN =>
    h η hη (popLossA μ (Aeta η)) (fun θ M hM hbd => popLossA_le hμ (Aeta η) θ M hM hbd) _
      (prior_floor hφ₀ (hφ η hη) hχ) N hN⟩

end VectorSLT
