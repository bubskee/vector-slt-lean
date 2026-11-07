/-
L6 stage 1: general one-dimensional tools (namespace `VectorSLT.SLT`, Mathlib only).

* `lintegral_comp_affine`: `∫ f(a x + b) dx = |a|⁻¹ ∫ f` (mathlib has this only for Bochner
  integrals);
* `lintegral_exp_neg_le_tsum`: Laplace from sublevel sets (decomposition M4.3, handoff 8),
  `∫ e^{-g} ≤ ∑ₙ e^{-n} μ{g ≤ n+1}` for `g ≥ 0`;
* `lintegral_min_rsq_inv`: the radial split (M5.3, handoff 9),
  `∫₀^ε min(A r², B/r) dr ≤ B (1/3 + log⁺(ε (A/B)^{1/3}))`.
-/
import Mathlib

namespace VectorSLT.SLT

open MeasureTheory Set Filter Real

/-! ### Affine substitution -/

/-- **Affine substitution in lintegrals**: `∫⁻ f(a x + b) dx = |a|⁻¹ ∫⁻ f`. -/
theorem lintegral_comp_affine {f : ℝ → ENNReal} (hf : Measurable f) {a : ℝ} (ha : a ≠ 0)
    (b : ℝ) : ∫⁻ x, f (a * x + b) = ENNReal.ofReal |a⁻¹| * ∫⁻ y, f y := by
  have hg : Measurable fun y => f (y + b) := hf.comp (measurable_add_const b)
  calc ∫⁻ x, f (a * x + b) = ∫⁻ y, f (y + b) ∂(Measure.map (fun x => a * x) volume) :=
        (lintegral_map hg (measurable_const_mul a)).symm
    _ = ENNReal.ofReal |a⁻¹| * ∫⁻ y, f (y + b) := by
        rw [Real.map_volume_mul_left ha, lintegral_smul_measure, smul_eq_mul]
    _ = _ := by rw [lintegral_add_right_eq_self (fun y => f y) b]

/-- On a set: the integral over any `s` is at most the integral over the whole line. -/
theorem setLIntegral_comp_affine_le {f : ℝ → ENNReal} (hf : Measurable f) {a : ℝ} (ha : a ≠ 0)
    (b : ℝ) (s : Set ℝ) :
    ∫⁻ x in s, f (a * x + b) ≤ ENNReal.ofReal |a⁻¹| * ∫⁻ y, f y :=
  (setLIntegral_le_lintegral s _).trans (lintegral_comp_affine hf ha b).le

/-! ### Laplace from sublevel sets -/

/-- **(M4.3)** `∫ e^{-g} dμ ≤ ∑ₙ e^{-n} μ{g ≤ n+1}` for `g ≥ 0` measurable. -/
theorem lintegral_exp_neg_le_tsum {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-g x)) ∂μ ≤
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (-n)) * μ {x | g x ≤ n + 1} := by
  have hpt : ∀ x, ENNReal.ofReal (Real.exp (-g x)) ≤ ∑' n : ℕ,
      {x | g x ≤ n + 1}.indicator (fun _ => ENNReal.ofReal (Real.exp (-n))) x := by
    intro x
    set n := ⌊g x⌋₊
    refine le_trans ?_ (ENNReal.le_tsum n)
    have hn : (n : ℝ) ≤ g x := Nat.floor_le (hg0 x)
    have hn1 : g x ≤ n + 1 := (Nat.lt_floor_add_one (g x)).le
    rw [indicator_of_mem (show x ∈ {x | g x ≤ n + 1} from hn1)]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  rw [lintegral_tsum fun n => (Measurable.indicator measurable_const
    (measurableSet_le hg measurable_const)).aemeasurable]
  congr 1; funext n
  rw [lintegral_indicator_const (measurableSet_le hg measurable_const)]

/-- `∑ₙ e^{-n} (n+1)^k < ∞`, as a real sum. -/
theorem summable_exp_neg_mul_pow (k : ℕ) :
    Summable fun n : ℕ => Real.exp (-n) * ((n : ℝ) + 1) ^ k := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul k (r := 1) one_pos
  have h' := (summable_nat_add_iff 1).mpr h
  refine (h'.mul_left (Real.exp 1)).congr fun n => ?_
  push_cast
  rw [show -1 * ((n : ℝ) + 1) = -(n : ℝ) + -1 by ring, Real.exp_add]
  rw [show Real.exp 1 * (((n : ℝ) + 1) ^ k * (Real.exp (-(n : ℝ)) * Real.exp (-1))) =
    Real.exp (-(n : ℝ)) * ((n : ℝ) + 1) ^ k * (Real.exp 1 * Real.exp (-1)) by ring,
    ← Real.exp_add]
  simp

/-- **(M4.3), polynomial sublevel growth.** If `μ{g ≤ n+1} ≤ K (n+1)^k` for every `n`, then
`∫ e^{-g} ≤ K ∑ₙ e^{-n}(n+1)^k`. -/
theorem lintegral_exp_neg_le_of_sublevel {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) {K : ℝ} (hK : 0 ≤ K) (k : ℕ)
    (hsub : ∀ n : ℕ, μ {x | g x ≤ n + 1} ≤ ENNReal.ofReal (K * ((n : ℝ) + 1) ^ k)) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-g x)) ∂μ ≤
      ENNReal.ofReal (K * ∑' n : ℕ, Real.exp (-n) * ((n : ℝ) + 1) ^ k) := by
  refine (lintegral_exp_neg_le_tsum hg hg0).trans ?_
  rw [← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    ((summable_exp_neg_mul_pow k).mul_left K)]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [show K * (Real.exp (-n) * ((n : ℝ) + 1) ^ k) = Real.exp (-n) * (K * ((n : ℝ) + 1) ^ k) by
    ring, ENNReal.ofReal_mul (Real.exp_pos _).le]
  gcongr; exact hsub n

/-! ### The radial split -/

/-- **(M5.3), general form.** For `A, B, ε > 0`,
`∫_{(0,ε]} min(A r², B/r) dr ≤ B (1/3 + log⁺(ε (A/B)^{1/3}))`. -/
theorem lintegral_min_rsq_inv {A B ε : ℝ} (hA : 0 < A) (hB : 0 < B) (hε : 0 < ε) :
    ∫⁻ r in Ioc 0 ε, min (ENNReal.ofReal (A * r ^ 2)) (ENNReal.ofReal (B / r)) ≤
      ENNReal.ofReal (B * (1 / 3 + Real.posLog (ε * (A / B) ^ ((1 : ℝ) / 3)))) := by
  set r₀ := (B / A) ^ ((1 : ℝ) / 3)
  have hr₀ : 0 < r₀ := Real.rpow_pos_of_pos (div_pos hB hA) _
  have hr₀3 : A * r₀ ^ 3 = B := by
    simp only [r₀]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hB hA).le]
    norm_num; field_simp
  have hint2 : ∀ c : ℝ, 0 ≤ c → ∫⁻ r in Ioc 0 c, ENNReal.ofReal (A * r ^ 2) =
      ENNReal.ofReal (A * c ^ 3 / 3) := by
    intro c hc
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [← intervalIntegral.integral_of_le hc, intervalIntegral.integral_const_mul,
        integral_pow]; congr 1; ring
    · exact (continuous_const.mul (continuous_pow 2)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · exact Eventually.of_forall fun r => by positivity
  have hB3 : 0 ≤ B / 3 := by positivity
  have hP : 0 ≤ Real.posLog (ε * (A / B) ^ ((1 : ℝ) / 3)) := Real.posLog_nonneg
  rcases le_or_gt ε r₀ with hle | hlt
  · -- the whole interval is in the `A r²` regime
    calc ∫⁻ r in Ioc 0 ε, min (ENNReal.ofReal (A * r ^ 2)) (ENNReal.ofReal (B / r))
        ≤ ∫⁻ r in Ioc 0 ε, ENNReal.ofReal (A * r ^ 2) :=
          lintegral_mono fun r => min_le_left _ _
      _ = ENNReal.ofReal (A * ε ^ 3 / 3) := hint2 ε hε.le
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have : A * ε ^ 3 ≤ A * r₀ ^ 3 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le hle 3) hA.le
          nlinarith
  · -- split at r₀
    have hsub : Ioc 0 ε ⊆ Ioc 0 r₀ ∪ Ioc r₀ ε := by
      intro r hr
      rcases le_or_gt r r₀ with h | h
      · exact Or.inl ⟨hr.1, h⟩
      · exact Or.inr ⟨h, hr.2⟩
    have hlog : Real.log (ε / r₀) = Real.log (ε * (A / B) ^ ((1 : ℝ) / 3)) := by
      congr 1; simp only [r₀]
      rw [Real.div_rpow hB.le hA.le, Real.div_rpow hA.le hB.le]
      field_simp
    have hout : ∫⁻ r in Ioc r₀ ε, ENNReal.ofReal (B / r) = ENNReal.ofReal (B * Real.log (ε / r₀)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · rw [← intervalIntegral.integral_of_le hlt.le]
        simp_rw [div_eq_mul_inv]
        rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hr₀ hε, div_eq_mul_inv]
      · exact (ContinuousOn.div continuousOn_const continuousOn_id
          (fun r hr => (lt_of_lt_of_le hr₀ hr.1).ne')).integrableOn_Icc.mono_set Ioc_subset_Icc_self
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact div_nonneg hB.le (lt_trans hr₀ hr.1).le
    calc ∫⁻ r in Ioc 0 ε, min (ENNReal.ofReal (A * r ^ 2)) (ENNReal.ofReal (B / r))
        ≤ (∫⁻ r in Ioc 0 r₀, min (ENNReal.ofReal (A * r ^ 2)) (ENNReal.ofReal (B / r))) +
          ∫⁻ r in Ioc r₀ ε, min (ENNReal.ofReal (A * r ^ 2)) (ENNReal.ofReal (B / r)) :=
          (lintegral_mono_set hsub).trans (lintegral_union_le _ _ _)
      _ ≤ ENNReal.ofReal (A * r₀ ^ 3 / 3) + ENNReal.ofReal (B * Real.log (ε / r₀)) := by
          gcongr
          · exact (lintegral_mono fun r => min_le_left _ _).trans (hint2 r₀ hr₀.le).le
          · exact (lintegral_mono fun r => min_le_right _ _).trans hout.le
      _ ≤ _ := by
          rw [hr₀3, hlog]
          have hl : Real.log (ε * (A / B) ^ ((1 : ℝ) / 3)) ≤
              Real.posLog (ε * (A / B) ^ ((1 : ℝ) / 3)) := by
            rw [Real.posLog_apply]; exact le_max_right _ _
          have hl0 : 0 ≤ Real.log (ε * (A / B) ^ ((1 : ℝ) / 3)) := by
            rw [← hlog]; exact Real.log_nonneg (by rw [le_div_iff₀ hr₀]; linarith)
          rw [← ENNReal.ofReal_add hB3 (mul_nonneg hB.le hl0)]
          apply ENNReal.ofReal_le_ofReal
          nlinarith

/-- **(M5.3)** as used in Theorem M: for `N ≥ e`,
`∫₀^ε min(r² ε³, N⁻¹(1+log N)/r) dr ≤ C_ε N⁻¹ (log N)²`. -/
theorem radial_split {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ N : ℝ, Real.exp 1 ≤ N →
      ∫⁻ r in Ioc 0 ε, min (ENNReal.ofReal (ε ^ 3 * r ^ 2))
        (ENNReal.ofReal (N⁻¹ * (1 + Real.log N) / r)) ≤
      ENNReal.ofReal (C * N⁻¹ * Real.log N ^ 2) := by
  refine ⟨2 * (1 / 3 + Real.posLog (ε ^ 2) + 1 / 3), fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hN
  have hN0 : 0 < N := by linarith
  have hl : 1 ≤ Real.log N := by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hN
  set B := N⁻¹ * (1 + Real.log N)
  have hB : 0 < B := by positivity
  refine (lintegral_min_rsq_inv (pow_pos hε 3) hB hε).trans (ENNReal.ofReal_le_ofReal ?_)
  -- log⁺(ε (ε³/B)^{1/3}) ≤ log⁺(ε²) + (1/3) log N
  have hA : ε * (ε ^ 3 / B) ^ ((1 : ℝ) / 3) = ε ^ 2 * (N / (1 + Real.log N)) ^ ((1 : ℝ) / 3) := by
    rw [Real.div_rpow (by positivity) hB.le, show (ε ^ 3) ^ ((1 : ℝ) / 3) = ε by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num]
    rw [Real.div_rpow hN0.le (by positivity)]
    simp only [B]
    rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hN0.le]
    field_simp
  have hpl : Real.posLog (ε * (ε ^ 3 / B) ^ ((1 : ℝ) / 3)) ≤
      Real.posLog (ε ^ 2) + 1 / 3 * Real.log N := by
    rw [hA]
    refine (Real.posLog_mul).trans (add_le_add le_rfl ?_)
    have hle : (N / (1 + Real.log N)) ^ ((1 : ℝ) / 3) ≤ N ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow (by positivity) (div_le_self hN0.le (by linarith)) (by norm_num)
    have hge : 0 ≤ (N / (1 + Real.log N)) ^ ((1 : ℝ) / 3) := by positivity
    calc Real.posLog ((N / (1 + Real.log N)) ^ ((1 : ℝ) / 3))
        ≤ Real.posLog (N ^ ((1 : ℝ) / 3)) := Real.posLog_le_posLog (by linarith) hle
      _ = 1 / 3 * Real.log N := by
          rw [Real.posLog_eq_log (by
            rw [abs_of_nonneg (by positivity)]; exact Real.one_le_rpow hN1 (by norm_num)),
            Real.log_rpow hN0]
  have hP0 : 0 ≤ Real.posLog (ε ^ 2) := Real.posLog_nonneg
  have hBle : B ≤ 2 * N⁻¹ * Real.log N := by
    simp only [B]; have : 0 < N⁻¹ := inv_pos.mpr hN0; nlinarith
  calc B * (1 / 3 + Real.posLog (ε * (ε ^ 3 / B) ^ ((1 : ℝ) / 3)))
      ≤ (2 * N⁻¹ * Real.log N) * (1 / 3 + (Real.posLog (ε ^ 2) + 1 / 3 * Real.log N)) := by
        have hl0 := Real.log_nonneg hN1
        have hNi : 0 ≤ N⁻¹ := inv_nonneg.mpr hN0.le
        have hpp := Real.posLog_nonneg (x := ε * (ε ^ 3 / B) ^ ((1 : ℝ) / 3))
        apply mul_le_mul hBle (by linarith) (by linarith)
          (mul_nonneg (mul_nonneg (by norm_num) hNi) hl0)
    _ ≤ (2 * N⁻¹ * Real.log N) * ((1 / 3 + Real.posLog (ε ^ 2) + 1 / 3) * Real.log N) := by
        have hl0 := Real.log_nonneg hN1
        have hNi : 0 ≤ N⁻¹ := inv_nonneg.mpr hN0.le
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (by norm_num) hNi) hl0)
        nlinarith
    _ = _ := by ring

end VectorSLT.SLT
