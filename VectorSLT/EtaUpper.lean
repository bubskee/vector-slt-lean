/-
Proposition X5 of paper 2 (uniform upper bound near a shear), formalized.

`Z_N(A_η) ≤ C N⁻⁴ (log N)⁴` at position one, with `C` (and `N₀`) independent of `η` for
`|η| ≤ η₀`. Constants are chosen in the order `ε₁ = 1/100`, `η₀ = 1/200`, `r = 1/400`, then `C`
and `N₀` from the input law and the prior bound only. See `EtaUpper/NOTES_x5.md`.

Files:
* `EtaUpper/GdownEta.lean`    (G↓) for `A_η`, `κ` uniform in `η`;
* `EtaUpper/SliceEta.lean`    Lemma M4 for `G_η` (the slice quadratic changes only in `L, k`);
* `EtaUpper/RowBoundEta.lean` Lemma M5 / one-row bound for `G_η`;
* `EtaUpper/TheoremMEta.lean` Theorem M for `A_η` on the fixed box `UM`;
* `EtaUpper/X5.lean`          raw coordinates, `N ≥ N₀` and `N ≥ 2` forms.
-/
import VectorSLT.EtaUpper.X5
import VectorSLT.TwoSidedLaws

namespace VectorSLT

open MeasureTheory Set

/-- **Proposition X5 (uniform upper bound).** There are `η₀ > 0` and `r > 0` such that for every
input law `μ` with finite 162nd moments that dominates a uniform density on a box, every prior
`φ ≤ π₁` and every cutoff `χ ≤ 1` vanishing outside the sup-norm `r`-ball, there are `C` and
`N₀` with `Z_{N,1}(A_η) ≤ C N⁻⁴ (log N)⁴` for **all** `|η| ≤ η₀` and `N ≥ N₀`. The cutoff is
centred at `basePos (Aeta η) 0`, which moves with `η`. (`η₀ = 1/200`, `r = 1/400`.) -/
theorem X5_upper :
    ∃ η₀ r : ℝ, 0 < η₀ ∧ 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C N₀ : ℝ, ∀ η : ℝ, |η| ≤ η₀ → ∀ N : ℝ, N₀ ≤ N →
        Zpos μ (Aeta η) φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4 * Real.log N ^ 4) := by
  refine ⟨1 / 200, 1 / 400, by norm_num, by norm_num, ?_⟩
  intro μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ π₁ hπ₁ hφ hχ hχs
  obtain ⟨C, N₀, h⟩ := X5_upper_explicit μ hmom hlh hμ₀ hμ hπ₁
  exact ⟨C, N₀, fun η hη N hN => h η hη φ χ hφ hχ hχs N hN⟩

/-- **Proposition X5 in the paper's range `N ≥ 2`.** Same hypotheses; one `C` for all
`|η| ≤ η₀` and all `N ≥ 2`. -/
theorem X5_upper_two :
    ∃ η₀ r : ℝ, 0 < η₀ ∧ 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C : ℝ, ∀ η : ℝ, |η| ≤ η₀ → ∀ N : ℝ, 2 ≤ N →
        Zpos μ (Aeta η) φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4 * Real.log N ^ 4) := by
  refine ⟨1 / 200, 1 / 400, by norm_num, by norm_num, ?_⟩
  intro μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ π₁ hπ₁ hφ hχ hχs
  obtain ⟨C, h⟩ := X5_upper_explicit_two μ hmom hlh hμ₀ hμ hπ₁
  exact ⟨C, fun η hη N hN => h η hη φ χ hφ hχ hχs N hN⟩

/-- **Proposition X5 for the standard Gaussian input law**, `N ≥ 2`. -/
theorem X5_upper_gaussian (φ χ : Raw16 → ENNReal) {π₁ : ℝ} (hπ₁ : 0 ≤ π₁)
    (hφ : ∀ θ, φ θ ≤ ENNReal.ofReal π₁) (hχ : ∀ θ, χ θ ≤ 1)
    (hχs : ∀ θ, 1 / 400 < ‖θ‖ → χ θ = 0) :
    ∃ C : ℝ, ∀ η : ℝ, |η| ≤ 1 / 200 → ∀ N : ℝ, 2 ≤ N →
      Zpos stdGauss2 (Aeta η) φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4 * Real.log N ^ 4) := by
  obtain ⟨C, h⟩ := X5_upper_explicit_two stdGauss2 (fun i => stdGauss2_moments _ i)
    (fun _ => by norm_num) (pow_pos cG_pos 2) stdGauss2_density hπ₁
  exact ⟨C, fun η hη N hN => h η hη φ χ hφ hχ hχs N hN⟩

end VectorSLT
