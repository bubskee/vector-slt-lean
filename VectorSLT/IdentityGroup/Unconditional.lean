/-
Paper 2 ("Rank, Shears, and Logarithmic Multiplicity"): Proposition `prop:nonshear` and Theorem
`thm:invertible`, with no hypothesis beyond the shared ones on the input law, the prior and the
cutoff.

This is the join of two branches. `VectorSLT.IdentityGroup.Cubes` proves the interface
`CubeSumUpper k` for `k = 1, 2, 3` (the upper half of Lemma `lem:A-cubes`).
`VectorSLT.IdentityGroup.Pairs` derives the pairs from that interface. Here the two are composed.

Lean positions `p = 0, 1, 2, 3` are the paper's positions one to four. The shared hypotheses are
those of `theoremM_shear`: an input law with finite 162nd moments that dominates a uniform
density on a box, a prior bounded above, and a cutoff bounded by one that vanishes outside the
sup-norm ball of radius `r(A)`, with `r(A)` produced by the theorem. The pair statements also
take the local lower bounds on the prior and the cutoff that `Zpos_lower_N4` needs.
-/
import VectorSLT.IdentityGroup.Cubes
import VectorSLT.IdentityGroup.Pairs

namespace VectorSLT.IdentityGroup

open MeasureTheory Filter Topology VectorSLT Pairs

/-- **Proposition `prop:nonshear`, upper half.** For `A = a vᵀ` with `a₀ a₁ ≠ 0` and
`v · a^{⊙3} ≠ 0`, at position one: `Z_N ≤ C N⁻⁴` for large `N`. -/
theorem prop_nonshear_upper {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : NonShearTarget A) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → Zpos μ A φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4) :=
  paper_nonshear_upper hA cubeSumUpper_three

/-- **Proposition `prop:nonshear`.** For a rank-one target that is not a shear, with both rows
nonzero, the pair at position one is `(4, 1)`. -/
theorem prop_nonshear_pair {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : NonShearTarget A) :
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
  paper_nonshear_pair hA cubeSumUpper_three

/-- **Theorem `thm:invertible`, upper half.** For `det A ≠ 0`, at every position `p`:
`Z_{N,p} ≤ C N⁻⁴` for large `N`. -/
theorem thm_invertible_upper {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) (p : Fin 4) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → Zpos μ A φ χ p N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4) :=
  paper_invertible_upper hA cubeSumUpper_one cubeSumUpper_two cubeSumUpper_three p

/-- **Theorem `thm:invertible`.** For an invertible active block, the pair is `(4, 1)` at every
position. -/
theorem thm_invertible_pair {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) (p : Fin 4) :
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
  paper_invertible_pair hA cubeSumUpper_one cubeSumUpper_two cubeSumUpper_three p

/-- **Lemma `lem:A-box`, upper half, for groups of one, two or three blocks.**
`∫_{‖W‖ ≤ r} e^{-c N J_n(W)} dW ≤ C N^{-2n/3}` for `N ≥ 1`. -/
theorem lem_Abox_upper {n : ℕ} (hn1 : 1 ≤ n) (hn3 : n ≤ 3) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∃ C : ℝ, ∀ N : ℝ, 1 ≤ N →
      ∫⁻ W in Metric.closedBall (0 : Fin n → Fin 2 → Fin 2 → ℝ) r,
        ENNReal.ofReal (Real.exp (-(c * N * grpJ W))) ≤
          ENNReal.ofReal (C * N ^ (-(2 * (n : ℝ)) / 3)) := by
  have hn : CubeSumUpper n := by
    interval_cases n
    · exact cubeSumUpper_one
    · exact cubeSumUpper_two
    · exact cubeSumUpper_three
  exact paper_lemAbox_upper hn hr hc

end VectorSLT.IdentityGroup
