/-
The elementary loss comparison at positions two to four (paper 2, Proposition N2, first
paragraph, and the coordinates; Appendix C, "Active change of variables"), at positions two,
three and four (Lean `p = 1, 2, 3`).

* `VectorSLT/LossCompare/Coeffs.lean`: the exact `s³, s²t, st², t³, s⁵, s⁴t` coefficients of the
  error for every parameter, read off the four raw blocks (`errθ_coeffs`), and (G↓) for any finite
  family of coefficients (`gdown_family`).
* `VectorSLT/LossCompare/ChangeVar.lean`: the coordinates `Ψ_p θ = (𝐜(θ), w(θ))` and the
  change-of-variables bound on a ball around `basePos A₀ p` (`cov_bound`), at every position.
* `VectorSLT/LossCompare/PositionFour.lean`: the inactive function `G₄ = ∑ ĝᵢ²`, its weighted
  homogeneity `G₄(r ξ) = r⁶ H₄(r, ξ)` with `H₄(0, ξ) = ‖gens4 ξ‖²`, and the comparison
  `κ (‖𝐜‖² + G₄(w)) ≤ K` (`loss_compare_four`).
* `VectorSLT/LossCompare/Package.lean`: `MarginData`, i.e. slt-bridge's `PositionMargin` without
  the angular margin, at `A₀` and for every two-nonzero-row shear target (`marginData_shear`).
* `VectorSLT/LossCompare/Coeffs7.lean`, `Tables.lean`: the exact `s³t²` and `s⁷` coefficients, and
  all coefficients used as polynomials in the cube moments of the blocks.
* `VectorSLT/LossCompare/Elim.lean`: the elimination bound at every position (Lipschitz).
* `VectorSLT/LossCompare/Middle.lean`, `MiddleCompare.lean`: positions two and three: eleven
  eliminated coefficients, `G_p`, `H_p` with `H_p(0, ·) = ‖R2‖²`, `‖R3‖²`, and the comparison.

This file restates the headline theorems. Notes: `VectorSLT/LossCompare/NOTES_loss.md`.
-/
import VectorSLT.LossCompare.MiddleCompare

namespace VectorSLT.LossCompare

open MeasureTheory Set Filter Metric Topology VectorSLT VectorSLT.LeadingMap
open scoped ENNReal

/-- **Item 1 (every position).** For `ρ ≤ 1/2` there is `J` with
`∫ f(Ψ_p θ) 𝟙_{‖θ - basePos A₀ p‖ ≤ ρ} dθ ≤ J ∫ f` for every measurable `f ≥ 0`. -/
theorem change_of_variables (p : Fin 4) {ρ : ℝ} (hρ : ρ ≤ 1 / 2) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ f : (Fin 4 → ℝ) × (Fin 12 → ℝ) → ℝ≥0∞, Measurable f →
      ∫⁻ θ, f (Ψ p θ) * (closedBall (basePos A0 p) ρ).indicator 1 θ ≤
        ENNReal.ofReal J * ∫⁻ y, f y :=
  cov_bound p hρ

/-- **Item 2 at position four.** Under the moment and box hypotheses of `Gdown`, for every `ρ`
there is `κ > 0` with `κ (‖𝐜(θ)‖² + G₄(w(θ))) ≤ K(θ)` on the closed `ρ`-ball around
`basePos A₀ 3`. -/
theorem position_four_comparison (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ) (ρ : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ θ ∈ closedBall (basePos A0 3) ρ,
      κ * (∑ i, (Ψ 3 θ).1 i ^ 2 + G4 (Ψ 3 θ).2) ≤ popLossA μ A0 θ :=
  loss_compare_four μ hmom hlh hμ₀ hμ ρ

/-- **Item 3 at position four.** `G₄(r ξ) = r⁶ H₄(r, ξ)` for every real `r`, `H₄ ≥ 0` is jointly
continuous, and `H₄(0, ξ) = ∑ᵢ (leadingMap (w4 (unflat ξ)))ᵢ²`. -/
theorem position_four_homogeneity :
    (∀ (r : ℝ) (ξ : Fin 12 → ℝ), G4 (r • ξ) = r ^ 6 * H4 r ξ) ∧
    (∀ (r : ℝ) (ξ : Fin 12 → ℝ), 0 ≤ H4 r ξ) ∧
    Continuous (fun q : ℝ × (Fin 12 → ℝ) => H4 q.1 q.2) ∧
    (∀ ξ : Fin 12 → ℝ, H4 0 ξ = ∑ i, leadingMap (w4 (unflat ξ)) i ^ 2) :=
  ⟨G4_smul, H4_nonneg, continuous_H4, H4_zero⟩

/-- **Position four, every shear target**: `PositionMargin` without the angular margin. -/
theorem position_four_marginData {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε r : ℝ, 0 ≤ r → r ≤ c * min (1 / 2) (ε / 2) →
      ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ℝ≥0∞) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      MarginData μ A φ χ 3 G4 ε :=
  marginData_shear hA compareA0_four

/-- **Item 2 at positions two and three** (Lean `p = 1, 2`). -/
theorem middle_comparison {p : Fin 4} (hp : p = 1 ∨ p = 2) (μ : Measure (Fin 2 → ℝ))
    [IsFiniteMeasure μ] (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ) (ρ : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ θ ∈ closedBall (basePos A0 p) ρ,
      κ * (∑ i, (Ψ p θ).1 i ^ 2 + Gmid p (Ψ p θ).2) ≤ popLossA μ A0 θ :=
  loss_compare_mid hp μ hmom hlh hμ₀ hμ ρ

/-- **Item 3 at position two** (Lean `p = 1`): `G(r ξ) = r⁶ H(r, ξ)`, `H ≥ 0` jointly continuous,
`H(0, ξ) = ∑ᵢ (R2 (w2 (unflat ξ)))ᵢ²`. -/
theorem position_two_homogeneity :
    (∀ (r : ℝ) (ξ : Fin 12 → ℝ), Gmid 1 (r • ξ) = r ^ 6 * Hmid 1 r ξ) ∧
    (∀ (r : ℝ) (ξ : Fin 12 → ℝ), 0 ≤ Hmid 1 r ξ) ∧
    Continuous (fun q : ℝ × (Fin 12 → ℝ) => Hmid 1 q.1 q.2) ∧
    (∀ ξ : Fin 12 → ℝ, Hmid 1 0 ξ = ∑ i, R2 (w2 (unflat ξ)) i ^ 2) :=
  ⟨Gmid_smul (Or.inl rfl), Hmid_nonneg 1, continuous_Hmid 1, Hmid_zero_one⟩

/-- **Item 3 at position three** (Lean `p = 2`): `H(0, ξ) = ∑ᵢ (R3 (w3 (unflat ξ)))ᵢ²`. -/
theorem position_three_homogeneity :
    (∀ (r : ℝ) (ξ : Fin 12 → ℝ), Gmid 2 (r • ξ) = r ^ 6 * Hmid 2 r ξ) ∧
    (∀ (r : ℝ) (ξ : Fin 12 → ℝ), 0 ≤ Hmid 2 r ξ) ∧
    Continuous (fun q : ℝ × (Fin 12 → ℝ) => Hmid 2 q.1 q.2) ∧
    (∀ ξ : Fin 12 → ℝ, Hmid 2 0 ξ = ∑ i, R3 (w3 (unflat ξ)) i ^ 2) :=
  ⟨Gmid_smul (Or.inr rfl), Hmid_nonneg 2, continuous_Hmid 2, Hmid_zero_two⟩

/-- **Positions two and three, every shear target**: `PositionMargin` without the angular
margin, with inactive function `G_p = Gmid p`. -/
theorem middle_marginData {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) {p : Fin 4}
    (hp : p = 1 ∨ p = 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε r : ℝ, 0 ≤ r → r ≤ c * min (1 / 2) (ε / 2) →
      ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ℝ≥0∞) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      MarginData μ A φ χ p (Gmid p) ε :=
  marginData_shear hA (compareA0_mid hp)

end VectorSLT.LossCompare
