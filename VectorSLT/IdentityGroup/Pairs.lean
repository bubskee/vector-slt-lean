/-
Paper 2 ("Rank, Shears, and Logarithmic Multiplicity"): the pairs `(4, 1)` of Proposition
`prop:nonshear` and Theorem `thm:invertible`, from the identity-group interface
`CubeSumUpper k` of `VectorSLT/IdentityGroup/Defs.lean` (the upper half of Lemma `lem:A-cubes`).

Every statement here is conditional only on `CubeSumUpper k` for the listed `k`, beyond the
shared hypotheses of `theoremM_shear` (input law with finite 162nd moments and a density bounded
below on a box; prior bounded above; cutoff bounded by one and vanishing outside the sup-norm
ball of radius `r(A)`, with `r(A)` produced by the theorem). The lower halves are the certified
`Zpos_lower_N4`. Lean positions `p = 0, 1, 2, 3` are the paper's positions one to four.

See `VectorSLT/IdentityGroup/NOTES_pairs.md` for the correspondence with the paper.
-/
import VectorSLT.IdentityGroup.Pairs.Absorb
import VectorSLT.IdentityGroup.Pairs.GramDown
import VectorSLT.IdentityGroup.Pairs.GroupCubic
import VectorSLT.IdentityGroup.Pairs.Integrate
import VectorSLT.IdentityGroup.Pairs.Endpoint
import VectorSLT.IdentityGroup.Pairs.FirstPosition
import VectorSLT.IdentityGroup.Pairs.NonShear
import VectorSLT.IdentityGroup.Pairs.LemmaABox
import VectorSLT.IdentityGroup.Pairs.PolyAlgebra
import VectorSLT.IdentityGroup.Pairs.LastPosition
import VectorSLT.IdentityGroup.Pairs.Invertible
import VectorSLT.IdentityGroup.Pairs.OnePrefix
import VectorSLT.IdentityGroup.Pairs.Quintic
import VectorSLT.IdentityGroup.Pairs.TwoPrefix

namespace VectorSLT.IdentityGroup.Pairs

open MeasureTheory Filter Topology VectorSLT

/-- **Lemma `lem:A-box`, upper half.** For a group of `n` blocks, `CubeSumUpper n` gives
`∫_{‖W‖ ≤ r} e^{-c N J_n(W)} dW ≤ C N^{-2n/3}` for `N ≥ 1`, where `J_n` is the squared sup norm
on `[-1,1]²` of the group error `F_{W_{n-1}} ∘ ⋯ ∘ F_{W_0} - I`, summed over both output rows. -/
theorem paper_lemAbox_upper {n : ℕ} (hn : CubeSumUpper n) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∃ C : ℝ, ∀ N : ℝ, 1 ≤ N →
      ∫⁻ W in Metric.closedBall (0 : Fin n → Fin 2 → Fin 2 → ℝ) r,
        ENNReal.ofReal (Real.exp (-(c * N * grpJ W))) ≤
          ENNReal.ofReal (C * N ^ (-(2 * (n : ℝ)) / 3)) :=
  lemAbox_upper hn hr hc

/-- **Proposition `prop:nonshear`, upper half.** For `A = a vᵀ` with `a₀ a₁ ≠ 0` and
`v · a^{⊙3} ≠ 0`, at position one, from `CubeSumUpper 3`: `Z_N ≤ C N⁻⁴` for large `N`. -/
theorem paper_nonshear_upper {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : NonShearTarget A)
    (h3 : CubeSumUpper 3) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → Zpos μ A φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4) :=
  nonshear_upper hA h3

/-- **Proposition `prop:nonshear`: the pair `(4, 1)` at position one**, from `CubeSumUpper 3`. -/
theorem paper_nonshear_pair {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : NonShearTarget A)
    (h3 : CubeSumUpper 3) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ᶠ θ in 𝓝 (basePos A 0), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      VectorSLT.SLT.HasLaplacePair (Zpos μ A φ χ 0) 4 1 :=
  nonshear_pair hA h3

/-- **Theorem `thm:invertible`, upper half, every position.** For `det A ≠ 0`, from
`CubeSumUpper 1`, `CubeSumUpper 2` and `CubeSumUpper 3`: at every Lean position `p`,
`Z_{N,p} ≤ C N⁻⁴` for large `N`. Positions `p = 0, 3` use only `CubeSumUpper 3`; positions
`p = 1, 2` use only `CubeSumUpper 1` and `CubeSumUpper 2`. -/
theorem paper_invertible_upper {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0)
    (h1 : CubeSumUpper 1) (h2 : CubeSumUpper 2) (h3 : CubeSumUpper 3) (p : Fin 4) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → Zpos μ A φ χ p N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4) := by
  fin_cases p
  · exact invertible_first_upper hA h3
  · exact invertible_two_upper hA h1 h2
  · exact invertible_three_upper hA h1 h2
  · exact invertible_last_upper hA h3

/-- **Theorem `thm:invertible`: the pair `(4, 1)` at every position**, for `det A ≠ 0`, from
`CubeSumUpper 1`, `CubeSumUpper 2` and `CubeSumUpper 3`. -/
theorem paper_invertible_pair {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0)
    (h1 : CubeSumUpper 1) (h2 : CubeSumUpper 2) (h3 : CubeSumUpper 3) (p : Fin 4) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ᶠ θ in 𝓝 (basePos A p), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      VectorSLT.SLT.HasLaplacePair (Zpos μ A φ χ p) 4 1 :=
  pair_of_upper A p (paper_invertible_upper hA h1 h2 h3 p)

end VectorSLT.IdentityGroup.Pairs
