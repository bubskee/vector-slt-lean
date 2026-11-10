/-
Loss comparison, packaging: everything slt-bridge's `PositionMargin` asks for at a position,
except the angular margin itself (`MarginData`), first at `A₀` and then, through
`shear_normalize`, for every two-nonzero-row shear target.

`MarginData μ A φ χ p G ε` is `PositionMargin μ A φ χ p` (slt-bridge `zoo/Zoo/TemplateMargin.lean`)
with the clauses `2 < s`, `0 ≤ M`, `AngularMargin G 3 s ε M` and `Measurable G` removed; it uses
Mathlib vocabulary only.
-/
import VectorSLT.LossCompare.PositionFour
import VectorSLT.ShearUpper

namespace VectorSLT.LossCompare

open MeasureTheory Set Filter Metric Topology VectorSLT
open scoped ENNReal

/-- **The margin data at position `p`**: coordinates `Ψ' = (𝐜, w)` with a bounded change of
variables against prior × cutoff, the comparison `κ (‖𝐜‖² + G(w)) ≤ K` on the support, and
`w` in the ball of radius `ε/2`. -/
def MarginData (μ : Measure (Fin 2 → ℝ)) (A : Matrix (Fin 2) (Fin 2) ℝ) (φ χ : Raw16 → ℝ≥0∞)
    (p : Fin 4) (G : (Fin 12 → ℝ) → ℝ) (ε : ℝ) : Prop :=
  ∃ (Ψ' : Raw16 → (Fin 4 → ℝ) × (Fin 12 → ℝ)) (J κ : ℝ), Measurable Ψ' ∧ 0 < κ ∧
    (∀ f : (Fin 4 → ℝ) × (Fin 12 → ℝ) → ℝ≥0∞, Measurable f →
      ∫⁻ θ, f (Ψ' θ) * (φ θ * χ (θ - basePos A p)) ≤ ENNReal.ofReal J * ∫⁻ y, f y) ∧
    ∀ θ, φ θ * χ (θ - basePos A p) ≠ 0 →
      κ * (∑ i, (Ψ' θ).1 i ^ 2 + G (Ψ' θ).2) ≤ popLossA μ A θ ∧
        (Ψ' θ).2 ∈ closedBall (0 : Fin 12 → ℝ) (ε / 2)

/-- The comparison hypothesis at `A₀` and position `p`, for every admissible input law and every
radius (what `loss_compare_four` proves at `p = 3`). -/
def CompareA0 (p : Fin 4) (G : (Fin 12 → ℝ) → ℝ) : Prop :=
  ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
    (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
    ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
    ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ → ∀ ρ : ℝ,
    ∃ κ : ℝ, 0 < κ ∧ ∀ θ ∈ closedBall (basePos A0 p) ρ,
      κ * (∑ i, (Ψ p θ).1 i ^ 2 + G (Ψ p θ).2) ≤ popLossA μ A0 θ

theorem compareA0_four : CompareA0 3 G4 := fun μ _ hmom _ _ hlh _ hμ₀ hμ ρ =>
  loss_compare_four μ hmom hlh hμ₀ hμ ρ

theorem continuous_Ψ (p : Fin 4) : Continuous (Ψ p) := by
  have : Ψ p = Φmap P0w P1w ∘ Lequiv p := funext (Ψ_eq p)
  rw [this]
  exact (continuous_Φmap continuous_P0w continuous_P1w).comp (Lequiv p).continuous

/-- Prior × cutoff is at most `π₁` times the indicator of the `r`-ball. -/
theorem prior_cutoff_le {φ χ : Raw16 → ℝ≥0∞} {π₁ r : ℝ} (hφ : ∀ θ, φ θ ≤ ENNReal.ofReal π₁)
    (hχ : ∀ θ, χ θ ≤ 1) (hχs : ∀ θ, r < ‖θ‖ → χ θ = 0) (c θ : Raw16) :
    φ θ * χ (θ - c) ≤ ENNReal.ofReal π₁ * (closedBall c r).indicator 1 θ := by
  by_cases hθ : θ ∈ closedBall c r
  · rw [indicator_of_mem hθ, Pi.one_apply, mul_one]
    exact (mul_le_mul' (hφ θ) (hχ _)).trans (by rw [mul_one])
  · have : r < ‖θ - c‖ := by rw [mem_closedBall, dist_eq_norm, not_le] at hθ; exact hθ
    rw [hχs _ this, mul_zero]; exact bot_le

/-- **The margin data at `A₀`**, from the comparison at position `p`, for a cutoff supported in
the `r`-ball with `r ≤ 1/2` and `r ≤ ε/2`. -/
theorem marginData_A0 {p : Fin 4} {G : (Fin 12 → ℝ) → ℝ} (hcmp : CompareA0 p G)
    (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ)
    {φ χ : Raw16 → ℝ≥0∞} {π₁ r ε : ℝ} (hπ₁ : 0 ≤ π₁) (hr2 : r ≤ 1 / 2) (hrε : r ≤ ε / 2)
    (hφ : ∀ θ, φ θ ≤ ENNReal.ofReal π₁) (hχ : ∀ θ, χ θ ≤ 1) (hχs : ∀ θ, r < ‖θ‖ → χ θ = 0) :
    MarginData μ A0 φ χ p G ε := by
  obtain ⟨J, hJ0, hJ⟩ := cov_bound p hr2
  obtain ⟨κ, hκ, hK⟩ := hcmp μ hmom hlh hμ₀ hμ r
  refine ⟨Ψ p, π₁ * J, κ, (continuous_Ψ p).measurable, hκ, fun f hf => ?_, fun θ hθ => ?_⟩
  · calc ∫⁻ θ, f (Ψ p θ) * (φ θ * χ (θ - basePos A0 p))
        ≤ ∫⁻ θ, ENNReal.ofReal π₁ * (f (Ψ p θ) * (closedBall (basePos A0 p) r).indicator 1 θ) :=
          lintegral_mono fun θ =>
            (mul_le_mul' le_rfl (prior_cutoff_le hφ hχ hχs _ θ)).trans
              (le_of_eq (mul_left_comm _ _ _))
      _ = ENNReal.ofReal π₁ * ∫⁻ θ, f (Ψ p θ) * (closedBall (basePos A0 p) r).indicator 1 θ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal π₁ * (ENNReal.ofReal J * ∫⁻ y, f y) := mul_le_mul' le_rfl (hJ f hf)
      _ = ENNReal.ofReal (π₁ * J) * ∫⁻ y, f y := by rw [ENNReal.ofReal_mul hπ₁, mul_assoc]
  · have hball : θ ∈ closedBall (basePos A0 p) r := by
      by_contra hc
      have : r < ‖θ - basePos A0 p‖ := by
        rw [mem_closedBall, dist_eq_norm, not_le] at hc; exact hc
      exact hθ (by rw [hχs _ this, mul_zero])
    refine ⟨hK θ hball, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    have := norm_wOf_sub_le p θ A0
    rw [mem_closedBall, dist_eq_norm] at hball
    exact this.trans (hball.trans hrε)

/-! ### Every two-nonzero-row shear target -/

theorem Tfun_basePos {d : Fin 2 → ℝ} {b : Bool} {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hact : actW d b A = A0) (p : Fin 4) : Tfun d b (basePos A p) = basePos A0 p := by
  apply rawEquiv.injective
  change rawW _ = rawW _
  funext q
  rw [rawW, weights_Tfun b _ q q.isLt, ← rawW, rawW_basePos, rawW_basePos]
  by_cases hq : q = p
  · subst hq; rw [Pi.single_eq_same, Pi.single_eq_same, hact]
  · rw [Pi.single_eq_of_ne hq, Pi.single_eq_of_ne hq]
    ext i j; simp [actW]

/-- **The margin data for every two-nonzero-row shear target.** Given the comparison at `A₀`
and position `p`, there is `c > 0` (depending only on `A`) such that for every `ε` and every
cutoff radius `0 < r ≤ c · min(1/2, ε/2)`, every admissible input law, prior and cutoff,
`MarginData μ A φ χ p G ε` holds, with the same inactive function `G`. -/
theorem marginData_shear {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) {p : Fin 4}
    {G : (Fin 12 → ℝ) → ℝ} (hcmp : CompareA0 p G) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε r : ℝ, 0 ≤ r → r ≤ c * min (1 / 2) (ε / 2) →
      ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ℝ≥0∞) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      MarginData μ A φ χ p G ε := by
  obtain ⟨d, b, hd, hact⟩ := shear_normalize hA
  set T := Tlin hd b
  set Tc : Raw16 →L[ℝ] Raw16 := (T.toContinuousLinearEquiv : Raw16 →L[ℝ] Raw16)
  have hT : ∀ θ, T θ = Tfun d b θ := fun _ => rfl
  have hTb : T (basePos A p) = basePos A0 p := Tfun_basePos hact p
  refine ⟨1 / (‖Tc‖ + 1), by positivity, ?_⟩
  intro ε r hr0 hr μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ π₁ hπ₁ hφ hχ hχs
  -- the radius after the change of coordinates
  set ρ := ‖Tc‖ * r
  have hmin : min (1 / 2 : ℝ) (ε / 2) ≤ 1 / 2 := min_le_left _ _
  have hρ : ρ ≤ min (1 / 2) (ε / 2) := by
    have hc0 : 0 < 1 / (‖Tc‖ + 1) := by positivity
    have hm0 : 0 ≤ min (1 / 2 : ℝ) (ε / 2) := by
      by_contra hc; push Not at hc
      have : 1 / (‖Tc‖ + 1) * min (1 / 2 : ℝ) (ε / 2) < 0 := mul_neg_of_pos_of_neg hc0 hc
      linarith
    calc ρ ≤ ‖Tc‖ * (1 / (‖Tc‖ + 1) * min (1 / 2) (ε / 2)) :=
          mul_le_mul_of_nonneg_left hr (norm_nonneg _)
      _ = ‖Tc‖ / (‖Tc‖ + 1) * min (1 / 2) (ε / 2) := by ring
      _ ≤ 1 * min (1 / 2) (ε / 2) := by
          apply mul_le_mul_of_nonneg_right _ hm0
          rw [div_le_one (by positivity)]; linarith
      _ = _ := one_mul _
  have hρ2 : ρ ≤ 1 / 2 := hρ.trans hmin
  have hρε : ρ ≤ ε / 2 := hρ.trans (min_le_right _ _)
  have hnorm : ∀ η, ‖T η‖ ≤ ‖Tc‖ * ‖η‖ := fun η => Tc.le_opNorm η
  -- the input law and the loss after the change of coordinates
  set μ' := μ.map (Φs d b)
  have hmom' := moments_map hmom d b
  obtain ⟨lo', hi', hlh', μ₁, hμ₁, hμ'⟩ := density_map hlh hμ₀ hμ hd b
  obtain ⟨J, hJ0, hJ⟩ := cov_bound p hρ2
  obtain ⟨κ, hκ, hK⟩ := hcmp μ' hmom' hlh' hμ₁ hμ' ρ
  set m := min ((d 0)⁻¹ ^ 2) ((d 1)⁻¹ ^ 2)
  have hm : 0 < m := lt_min (by have := hd 0; positivity) (by have := hd 1; positivity)
  set Jd := |(LinearMap.det (T : Raw16 →ₗ[ℝ] Raw16))⁻¹|
  refine ⟨fun θ => Ψ p (T θ), Jd * (π₁ * J), m * κ,
    (continuous_Ψ p).measurable.comp T.toContinuousLinearEquiv.continuous.measurable,
    mul_pos hm hκ, fun f hf => ?_, fun θ hθ => ?_⟩
  · -- the change of variables, through `T`
    have hsupp : ∀ θ', φ (T.symm θ') * χ (T.symm θ' - basePos A p) ≤
        ENNReal.ofReal π₁ * (closedBall (basePos A0 p) ρ).indicator 1 θ' := by
      intro θ'
      have e : T.symm θ' - basePos A p = T.symm (θ' - basePos A0 p) := by
        rw [map_sub, ← hTb, T.symm_apply_apply]
      by_cases hθ' : θ' ∈ closedBall (basePos A0 p) ρ
      · rw [indicator_of_mem hθ', Pi.one_apply, mul_one]
        exact (mul_le_mul' (hφ _) (hχ _)).trans (by rw [mul_one])
      · rw [e]
        have hfar : r < ‖T.symm (θ' - basePos A0 p)‖ := by
          rw [mem_closedBall, dist_eq_norm, not_le] at hθ'
          by_contra hc; push Not at hc
          have := hnorm (T.symm (θ' - basePos A0 p))
          rw [T.apply_symm_apply] at this
          have : ‖θ' - basePos A0 p‖ ≤ ρ := this.trans (mul_le_mul_of_nonneg_left hc (norm_nonneg _))
          linarith
        rw [hχs _ hfar, mul_zero]; exact bot_le
    calc ∫⁻ θ, f (Ψ p (T θ)) * (φ θ * χ (θ - basePos A p))
        = ENNReal.ofReal Jd * ∫⁻ θ', f (Ψ p (T (T.symm θ'))) *
            (φ (T.symm θ') * χ (T.symm θ' - basePos A p)) := lintegral_linearEquiv T _
      _ ≤ ENNReal.ofReal Jd * ∫⁻ θ', ENNReal.ofReal π₁ *
            (f (Ψ p θ') * (closedBall (basePos A0 p) ρ).indicator 1 θ') := by
          refine mul_le_mul' le_rfl (lintegral_mono fun θ' => ?_)
          rw [T.apply_symm_apply]
          exact (mul_le_mul' le_rfl (hsupp θ')).trans (le_of_eq (mul_left_comm _ _ _))
      _ = ENNReal.ofReal Jd * (ENNReal.ofReal π₁ *
            ∫⁻ θ', f (Ψ p θ') * (closedBall (basePos A0 p) ρ).indicator 1 θ') := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal Jd * (ENNReal.ofReal π₁ * (ENNReal.ofReal J * ∫⁻ y, f y)) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl (hJ f hf))
      _ = ENNReal.ofReal (Jd * (π₁ * J)) * ∫⁻ y, f y := by
          rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_mul hπ₁, mul_assoc, mul_assoc]
  · -- the comparison, through `T`
    have hball : ‖θ - basePos A p‖ ≤ r := by
      by_contra hc; push Not at hc
      exact hθ (by rw [hχs _ hc, mul_zero])
    have hball' : T θ ∈ closedBall (basePos A0 p) ρ := by
      rw [mem_closedBall, dist_eq_norm, ← hTb, ← map_sub]
      exact (hnorm _).trans (mul_le_mul_of_nonneg_left hball (norm_nonneg _))
    have h1 := hK (T θ) hball'
    have h2 : m * popLossA μ' A0 (T θ) ≤ popLossA μ A θ := by
      have := loss_compare hd b hact μ hmom (T θ)
      rwa [show Tinv d b (T θ) = θ from T.symm_apply_apply θ] at this
    refine ⟨?_, ?_⟩
    · calc m * κ * (∑ i, (Ψ p (T θ)).1 i ^ 2 + G (Ψ p (T θ)).2)
          = m * (κ * (∑ i, (Ψ p (T θ)).1 i ^ 2 + G (Ψ p (T θ)).2)) := by ring
        _ ≤ m * popLossA μ' A0 (T θ) := mul_le_mul_of_nonneg_left h1 hm.le
        _ ≤ _ := h2
    · rw [mem_closedBall, dist_zero_right]
      have := norm_wOf_sub_le p (T θ) A0
      rw [mem_closedBall, dist_eq_norm] at hball'
      exact this.trans (hball'.trans hρε)

end VectorSLT.LossCompare
