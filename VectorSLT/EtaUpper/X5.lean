/-
X5, step 5: Proposition X5 in raw coordinates.

**Order of constants.** `ε₁ = 1/100` (the active half-width `Jν`, fixed by `UM`), then
`η₀ = 1/200 ≤ ε₁` (the base points `(αₖ, νₖ) = (1, η)` lie in `UM`, and `|P₁ - η| ≤ 1/100` for
(A1)), then `r = 1/400` (so that `|ν - η| ≤ 2r` keeps `|ν| ≤ η₀ + 2r = ε₁`, and
`|b| ≤ 2r ≤ 1/20`), then `C, N₀` (from `μ` and `π₁` only, through `κ` of `Gdown_eta`).
-/
import VectorSLT.EtaUpper.TheoremMEta

namespace VectorSLT

open MeasureTheory Set

/-- The sup-norm ball of radius `1/400` around the moving base point `basePos (A_η) 0` lies in
the fixed box `UM` whenever `|η| ≤ 1/200`. -/
theorem toM2_mem_UM_eta {η : ℝ} (hη : |η| ≤ 1 / 200) {θ : Raw16}
    (h : ‖θ - basePos (Aeta η) 0‖ ≤ 1 / 400) : toM2 θ ∈ UM := by
  obtain ⟨⟨⟨m00, m01⟩, ⟨m10, m11⟩⟩, ⟨⟨⟨p0, p1, p2⟩, ⟨q0, q1, q2⟩⟩, ⟨⟨r0, r1, r2⟩, ⟨s0, s1, s2⟩⟩⟩⟩ := θ
  rw [basePos_zero] at h
  rw [abs_le] at hη
  simp only [baseA, Aeta, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Prod.norm_def, max_le_iff,
    Real.norm_eq_abs, sub_zero, abs_le, Prod.mk_sub_mk] at h
  simp only [toM2, UM, mem_prod, Iα, Jν, box3, mem_Icc, mem_ofPred_eq, abs_le, Prod.mk_add_mk]
  repeat' constructor
  all_goals linarith

/-- The prior × cutoff, bounded by `π₁` and supported in the `1/400`-ball, is dominated by
`π₁ · 1_{UM}` in (M2) coordinates. -/
theorem prior_le_indicator_eta {η : ℝ} (hη : |η| ≤ 1 / 200) {φ χ : Raw16 → ENNReal} {π₁ : ℝ}
    (hφ : ∀ θ, φ θ ≤ ENNReal.ofReal π₁) (hχ : ∀ θ, χ θ ≤ 1)
    (hχs : ∀ θ, 1 / 400 < ‖θ‖ → χ θ = 0) (θ : Raw16) :
    φ θ * χ (θ - basePos (Aeta η) 0) ≤ (toM2 ⁻¹' UM).indicator (fun _ => ENNReal.ofReal π₁) θ := by
  by_cases hθ : toM2 θ ∈ UM
  · rw [indicator_of_mem (show θ ∈ toM2 ⁻¹' UM from hθ)]
    calc φ θ * χ (θ - basePos (Aeta η) 0) ≤ ENNReal.ofReal π₁ * 1 := mul_le_mul' (hφ θ) (hχ _)
      _ = _ := mul_one _
  · have : 1 / 400 < ‖θ - basePos (Aeta η) 0‖ := by
      by_contra hc; exact hθ (toM2_mem_UM_eta hη (not_lt.mp hc))
    rw [hχs _ this, mul_zero]; exact bot_le

/-- **Proposition X5, explicit form, `N ≥ N₀`.** `η₀ = 1/200`, `r = 1/400`; `C` and `N₀`
depend only on the input law and on `π₁`, and are chosen before `η`, `φ` and `χ`. -/
theorem X5_upper_explicit (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ) {π₁ : ℝ} (hπ₁ : 0 ≤ π₁) :
    ∃ C N₀ : ℝ, ∀ η : ℝ, |η| ≤ 1 / 200 → ∀ φ χ : Raw16 → ENNReal,
      (∀ θ, φ θ ≤ ENNReal.ofReal π₁) → (∀ θ, χ θ ≤ 1) → (∀ θ, 1 / 400 < ‖θ‖ → χ θ = 0) →
      ∀ N : ℝ, N₀ ≤ N →
        Zpos μ (Aeta η) φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4 * Real.log N ^ 4) := by
  obtain ⟨C, N₀, h⟩ := theoremM_eta μ hmom hlh hμ₀ hμ hπ₁
  refine ⟨C, N₀, fun η hη φ χ hφ hχ hχs N hN => ?_⟩
  have hη' : |η| ≤ 9 / 1000 := hη.trans (by norm_num)
  exact h η hη' φ χ (prior_le_indicator_eta hη hφ hχ hχs) N hN

/-! ### From `N ≥ N₀` to the paper's `N ≥ 2` -/

theorem isCompact_UM : IsCompact UM := by
  have hb : IsCompact (box3 (1 / 20)) := by
    rw [box3_eq]; exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have ha : IsCompact (Iα ×ˢ Jν) := isCompact_Icc.prod isCompact_Icc
  exact (ha.prod ha).prod ((hb.prod hb).prod (hb.prod hb))

theorem volume_UM_ne_top : volume UM ≠ ⊤ := isCompact_UM.measure_lt_top.ne

/-- The trivial bound `Z_N ≤ π₁ vol(UM)` for `N ≥ 0`. -/
theorem Zpos_le_volume_UM (μ : Measure (Fin 2 → ℝ)) {η : ℝ} (hη : |η| ≤ 1 / 200)
    {φ χ : Raw16 → ENNReal} {π₁ : ℝ}
    (hφ : ∀ θ, φ θ ≤ ENNReal.ofReal π₁) (hχ : ∀ θ, χ θ ≤ 1)
    (hχs : ∀ θ, 1 / 400 < ‖θ‖ → χ θ = 0) {N : ℝ} (hN : 0 ≤ N) :
    Zpos μ (Aeta η) φ χ 0 N ≤ ENNReal.ofReal π₁ * volume UM := by
  have hset : MeasurableSet (toM2 ⁻¹' UM) := measurableSet_UM.preimage measurable_toM2
  calc Zpos μ (Aeta η) φ χ 0 N
      = ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * popLossA μ (Aeta η) θ))) *
          (φ θ * χ (θ - basePos (Aeta η) 0)) := rfl
    _ ≤ ∫⁻ θ, (toM2 ⁻¹' UM).indicator (fun _ => ENNReal.ofReal π₁) θ := by
        refine lintegral_mono fun θ => ?_
        have h1 : ENNReal.ofReal (Real.exp (-(N * popLossA μ (Aeta η) θ))) ≤ 1 := by
          rw [← ENNReal.ofReal_one]; apply ENNReal.ofReal_le_ofReal
          rw [Real.exp_le_one_iff]
          have : 0 ≤ popLossA μ (Aeta η) θ := integral_nonneg fun x => by positivity
          nlinarith
        calc _ ≤ 1 * (φ θ * χ (θ - basePos (Aeta η) 0)) := mul_le_mul' h1 le_rfl
          _ = _ := one_mul _
          _ ≤ _ := prior_le_indicator_eta hη hφ hχ hχs θ
    _ = ENNReal.ofReal π₁ * volume (toM2 ⁻¹' UM) := by
        rw [lintegral_indicator hset, setLIntegral_const]
    _ = ENNReal.ofReal π₁ * volume UM := by
        rw [measurePreserving_toM2.measure_preimage measurableSet_UM.nullMeasurableSet]

/-- **Proposition X5, explicit form, for all `N ≥ 2`** (the paper's range). -/
theorem X5_upper_explicit_two (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ) {π₁ : ℝ} (hπ₁ : 0 ≤ π₁) :
    ∃ C : ℝ, ∀ η : ℝ, |η| ≤ 1 / 200 → ∀ φ χ : Raw16 → ENNReal,
      (∀ θ, φ θ ≤ ENNReal.ofReal π₁) → (∀ θ, χ θ ≤ 1) → (∀ θ, 1 / 400 < ‖θ‖ → χ θ = 0) →
      ∀ N : ℝ, 2 ≤ N →
        Zpos μ (Aeta η) φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4 * Real.log N ^ 4) := by
  obtain ⟨C, N₀, h⟩ := X5_upper_explicit μ hmom hlh hμ₀ hμ hπ₁
  set V := (volume UM).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  set N₁ := max N₀ 2
  have hN₁ : 2 ≤ N₁ := le_max_right _ _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C₂ := π₁ * V * N₁ ^ 4 / Real.log 2 ^ 4
  have hC₂ : 0 ≤ C₂ := by positivity
  refine ⟨max C 0 + C₂, fun η hη φ χ hφ hχ hχs N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hlN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  have hX : 0 ≤ N⁻¹ ^ 4 * Real.log N ^ 4 := by
    have : 0 ≤ Real.log N := hl2.le.trans hlN
    positivity
  rcases le_or_gt N₀ N with hN₀ | hN₀
  · refine (h η hη φ χ hφ hχ hχs N hN₀).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right ((le_max_left C 0).trans (by linarith)) hX
  · refine (Zpos_le_volume_UM μ hη hφ hχ hχs hN0.le).trans ?_
    rw [← ENNReal.ofReal_toReal volume_UM_ne_top, ← ENNReal.ofReal_mul hπ₁]
    apply ENNReal.ofReal_le_ofReal
    have hNN₁ : N ≤ N₁ := (le_of_lt hN₀).trans (le_max_left _ _)
    -- `π₁ V ≤ C₂ N⁻⁴ (log N)⁴` on `[2, N₁]`
    have hinv : N₁⁻¹ ^ 4 ≤ N⁻¹ ^ 4 :=
      pow_le_pow_left₀ (by positivity) (inv_anti₀ hN0 hNN₁) 4
    have hlog4 : Real.log 2 ^ 4 ≤ Real.log N ^ 4 := pow_le_pow_left₀ hl2.le hlN 4
    have hN₁0 : 0 < N₁ := by linarith
    have key : π₁ * V = C₂ * N₁⁻¹ ^ 4 * Real.log 2 ^ 4 := by
      simp only [C₂]; field_simp
    have h2 : C₂ * N₁⁻¹ ^ 4 * Real.log 2 ^ 4 ≤ C₂ * (N⁻¹ ^ 4 * Real.log N ^ 4) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hinv hlog4 (by positivity) (by positivity)) hC₂
    have h3 : C₂ * (N⁻¹ ^ 4 * Real.log N ^ 4) ≤ (max C 0 + C₂) * (N⁻¹ ^ 4 * Real.log N ^ 4) :=
      mul_le_mul_of_nonneg_right (by linarith [le_max_right C 0]) hX
    rw [mul_assoc (max C 0 + C₂)]
    linarith

end VectorSLT
