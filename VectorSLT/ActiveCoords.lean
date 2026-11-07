/-
L6 stage 3, F1–F3: the active coordinates.

* F1: `∫ e^{-M(3α²ν + t)²} dν ≤ √(π/M)` (an affine Gaussian, `α ≥ 3/5`).
* F2: `∫_{[0.99, 1.01]} h(α³) dα ≤ ½ ∫_{[0.99³, 1.01³]} h(u) du` (`3α² ≥ 2`).
* F3: `u ↦ c = u - 1 + A` is a translation, and `[0.99³, 1.01³] - 1 + A ⊆ [-1/32, 1/32]`.
Combined: `active_bound`.
-/
import VectorSLT.LemmaM4

namespace VectorSLT

open MeasureTheory Set SLT

/-- The active `α`-interval `[1 - ε₁, 1 + ε₁]`, `ε₁ = 1/100`. -/
def Iα : Set ℝ := Icc (99 / 100) (101 / 100)
/-- The active `ν`-interval `[-ε₁, ε₁]`. -/
def Jν : Set ℝ := Icc (-(1 / 100)) (1 / 100)
/-- The `c₃`-interval `[-c₀, c₀]`, `c₀ = 1/32`. -/
def Ic : Set ℝ := Icc (-(1 / 32)) (1 / 32)

/-- **F1.** -/
theorem nu_int {M : ℝ} (hM : 0 < M) {α : ℝ} (hα : 3 / 5 ≤ α) (t : ℝ) :
    ∫⁻ ν, ENNReal.ofReal (Real.exp (-(M * (3 * α ^ 2 * ν + t) ^ 2))) ≤
      ENNReal.ofReal (√(Real.pi / M)) := by
  have ha : (3 * α ^ 2) ≠ 0 := by positivity
  have hf : Measurable fun ζ : ℝ => ENNReal.ofReal (Real.exp (-(M * ζ ^ 2))) := by fun_prop
  rw [lintegral_comp_affine (f := fun ζ => ENNReal.ofReal (Real.exp (-(M * ζ ^ 2)))) hf ha t,
    lintegral_gaussian hM]
  have h1 : |(3 * α ^ 2)⁻¹| ≤ 1 := by
    rw [abs_inv, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith)
  calc ENNReal.ofReal |(3 * α ^ 2)⁻¹| * ENNReal.ofReal (√(Real.pi / M))
      ≤ 1 * ENNReal.ofReal (√(Real.pi / M)) := by
        gcongr; rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1
    _ = _ := one_mul _

/-- **F2.** -/
theorem cube_subst (g : ℝ → ENNReal) :
    ∫⁻ α in Iα, g (α ^ 3) ≤ 2⁻¹ * ∫⁻ u in Icc ((99 / 100 : ℝ) ^ 3) ((101 / 100) ^ 3), g u := by
  have hpos : ∀ x ∈ Iα, 0 < x := fun x hx => by linarith [hx.1]
  have himg := lintegral_image_eq_lintegral_abs_deriv_mul (s := Iα) (f := fun x => x ^ 3)
    (f' := fun x => 3 * x ^ 2) measurableSet_Icc
    (fun x _ => by simpa using (hasDerivAt_pow 3 x).hasDerivWithinAt)
    ((Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)).injective.injOn) g
  have hsub : (fun x : ℝ => x ^ 3) '' Iα ⊆ Icc ((99 / 100 : ℝ) ^ 3) ((101 / 100) ^ 3) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨pow_le_pow_left₀ (by norm_num) hx.1 3, pow_le_pow_left₀ (by linarith [hx.1]) hx.2 3⟩
  calc ∫⁻ α in Iα, g (α ^ 3)
      ≤ ∫⁻ α in Iα, 2⁻¹ * (ENNReal.ofReal |3 * α ^ 2| * g (α ^ 3)) := by
        refine setLIntegral_mono' measurableSet_Icc fun α hα => ?_
        have h1 : (1 : ENNReal) ≤ 2⁻¹ * ENNReal.ofReal |3 * α ^ 2| := by
          rw [abs_of_nonneg (by positivity), ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          all_goals nlinarith [hα.1]
        calc g (α ^ 3) = 1 * g (α ^ 3) := (one_mul _).symm
          _ ≤ (2⁻¹ * ENNReal.ofReal |3 * α ^ 2|) * g (α ^ 3) := by gcongr
          _ = _ := mul_assoc _ _ _
    _ = 2⁻¹ * ∫⁻ α in Iα, ENNReal.ofReal |3 * α ^ 2| * g (α ^ 3) :=
        lintegral_const_mul' _ _ (by simp)
    _ = 2⁻¹ * ∫⁻ u in (fun x : ℝ => x ^ 3) '' Iα, g u := by rw [himg]
    _ ≤ _ := by gcongr

/-- **F3.** -/
theorem transl_bound (h : ℝ → ENNReal) {A : ℝ} (hA : |A| ≤ 1 / 2000) :
    ∫⁻ u in Icc ((99 / 100 : ℝ) ^ 3) ((101 / 100) ^ 3), h u ≤
      ∫⁻ c in Ic, h (c + 1 - A) := by
  rw [← lintegral_indicator measurableSet_Icc,
    show (∫⁻ c in Ic, h (c + 1 - A)) = ∫⁻ c, Ic.indicator (fun c => h (c + 1 - A)) c from
      (lintegral_indicator measurableSet_Icc _).symm,
    ← lintegral_add_right_eq_self _ (1 - A)]
  refine lintegral_mono fun c => ?_
  by_cases hc : c + (1 - A) ∈ Icc ((99 / 100 : ℝ) ^ 3) ((101 / 100) ^ 3)
  · rw [indicator_of_mem hc]
    have hc' : c ∈ Ic := by
      rw [abs_le] at hA
      exact ⟨by norm_num at hc; linarith [hc.1], by norm_num at hc; linarith [hc.2]⟩
    rw [indicator_of_mem hc', show c + 1 - A = c + (1 - A) by ring]
  · rw [indicator_of_notMem hc]; exact bot_le

/-- One active row: `∫_{Iα × Jν} e^{-M c₂²} h(α³) ≤ √(π/M) ∫_{Iα} h(α³)`. -/
theorem pair_bound {M : ℝ} (hM : 0 < M) (t : ℝ → ℝ) (h : ℝ → ENNReal) (hh : Measurable h)
    (ht : Measurable t) :
    ∫⁻ z in Iα ×ˢ Jν, ENNReal.ofReal (Real.exp (-(M * (3 * z.1 ^ 2 * z.2 + t z.1) ^ 2))) *
        h z.1 ≤ ENNReal.ofReal (√(Real.pi / M)) * ∫⁻ α in Iα, h α := by
  have hF : Measurable fun z : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (-(M * (3 * z.1 ^ 2 * z.2 + t z.1) ^ 2))) * h z.1 := by
    have h1 : Measurable fun z : ℝ × ℝ => t z.1 := ht.comp measurable_fst
    have h2 : Measurable fun z : ℝ × ℝ => h z.1 := hh.comp measurable_fst
    fun_prop
  rw [Measure.volume_eq_prod, setLIntegral_prod _ hF.aemeasurable, ← lintegral_const_mul' _ _
    ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun α hα => ?_
  simp only
  have hmν : Measurable fun ν : ℝ => ENNReal.ofReal (Real.exp (-(M * (3 * α ^ 2 * ν + t α) ^ 2))) := by
    fun_prop
  rw [lintegral_mul_const _ hmν]
  exact mul_le_mul' ((setLIntegral_le_lintegral _ _).trans
    (nu_int (α := α) hM (by linarith [hα.1]) (t α))) le_rfl

/-- **F1–F3 combined**, for fixed inactive coordinates. -/
theorem active_bound {M : ℝ} (hM : 0 < M) (t0 t1 : ℝ → ℝ) (ht0 : Measurable t0)
    (ht1 : Measurable t1) (H : ℝ × ℝ → ENNReal) (hH : Measurable H) {A0 A1 : ℝ}
    (hA0 : |A0| ≤ 1 / 2000) (hA1 : |A1| ≤ 1 / 2000) :
    ∫⁻ z in (Iα ×ˢ Jν) ×ˢ (Iα ×ˢ Jν),
        ENNReal.ofReal (Real.exp (-(M * (3 * z.1.1 ^ 2 * z.1.2 + t0 z.1.1) ^ 2))) *
        ENNReal.ofReal (Real.exp (-(M * (3 * z.2.1 ^ 2 * z.2.2 + t1 z.2.1) ^ 2))) *
          H (z.1.1 ^ 3, z.2.1 ^ 3) ≤
      ENNReal.ofReal (Real.pi / M) * 4⁻¹ *
        ∫⁻ c in Ic ×ˢ Ic, H (c.1 + 1 - A0, c.2 + 1 - A1) := by
  have hs : MeasurableSet (Iα ×ˢ Jν) := measurableSet_Icc.prod measurableSet_Icc
  set g0 : ℝ × ℝ → ENNReal := fun z =>
    ENNReal.ofReal (Real.exp (-(M * (3 * z.1 ^ 2 * z.2 + t0 z.1) ^ 2))) with hg0
  set g1 : ℝ × ℝ → ENNReal := fun z =>
    ENNReal.ofReal (Real.exp (-(M * (3 * z.1 ^ 2 * z.2 + t1 z.1) ^ 2))) with hg1
  have hg0m : Measurable g0 := by
    have : Measurable fun z : ℝ × ℝ => t0 z.1 := ht0.comp measurable_fst
    fun_prop
  have hg1m : Measurable g1 := by
    have : Measurable fun z : ℝ × ℝ => t1 z.1 := ht1.comp measurable_fst
    fun_prop
  have hHc : ∀ x : ℝ, Measurable fun y : ℝ => H (x, y) := fun x => hH.comp measurable_prodMk_left
  have hF : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => g0 z.1 * g1 z.2 * H (z.1.1 ^ 3, z.2.1 ^ 3) := by
    have : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => H (z.1.1 ^ 3, z.2.1 ^ 3) :=
      hH.comp ((measurable_fst.comp measurable_fst).pow_const 3 |>.prodMk
        ((measurable_fst.comp measurable_snd).pow_const 3))
    exact ((hg0m.comp measurable_fst).mul (hg1m.comp measurable_snd)).mul this
  -- inner active row
  have hin : ∀ z1 : ℝ × ℝ, ∫⁻ z2 in Iα ×ˢ Jν, g0 z1 * g1 z2 * H (z1.1 ^ 3, z2.1 ^ 3) ≤
      g0 z1 * (ENNReal.ofReal (√(Real.pi / M)) * ∫⁻ α in Iα, H (z1.1 ^ 3, α ^ 3)) := by
    intro z1
    have hm : Measurable fun z2 : ℝ × ℝ => g1 z2 * H (z1.1 ^ 3, z2.1 ^ 3) :=
      hg1m.mul ((hHc _).comp (measurable_fst.pow_const 3))
    simp_rw [mul_assoc]
    rw [lintegral_const_mul _ hm]
    gcongr
    exact pair_bound hM t1 (fun α => H (z1.1 ^ 3, α ^ 3)) ((hHc _).comp (measurable_id.pow_const 3))
      ht1
  have hK : Measurable fun x : ℝ => ∫⁻ α in Iα, H (x ^ 3, α ^ 3) := by
    have : Measurable fun p : ℝ × ℝ => H (p.1 ^ 3, p.2 ^ 3) :=
      hH.comp ((measurable_fst.pow_const 3).prodMk (measurable_snd.pow_const 3))
    exact this.lintegral_prod_right'
  have step1 : ∫⁻ z in (Iα ×ˢ Jν) ×ˢ (Iα ×ˢ Jν), g0 z.1 * g1 z.2 * H (z.1.1 ^ 3, z.2.1 ^ 3) ≤
      ENNReal.ofReal (√(Real.pi / M)) * ENNReal.ofReal (√(Real.pi / M)) *
        ∫⁻ α in Iα, ∫⁻ β in Iα, H (α ^ 3, β ^ 3) := by
    rw [Measure.volume_eq_prod, setLIntegral_prod _ hF.aemeasurable]
    calc ∫⁻ z1 in Iα ×ˢ Jν, ∫⁻ z2 in Iα ×ˢ Jν, g0 z1 * g1 z2 * H (z1.1 ^ 3, z2.1 ^ 3)
        ≤ ∫⁻ z1 in Iα ×ˢ Jν, g0 z1 * (ENNReal.ofReal (√(Real.pi / M)) *
            ∫⁻ α in Iα, H (z1.1 ^ 3, α ^ 3)) := lintegral_mono fun z1 => hin z1
      _ = ENNReal.ofReal (√(Real.pi / M)) * ∫⁻ z1 in Iα ×ˢ Jν, g0 z1 *
            ∫⁻ α in Iα, H (z1.1 ^ 3, α ^ 3) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1; funext z1; ring
      _ ≤ ENNReal.ofReal (√(Real.pi / M)) * (ENNReal.ofReal (√(Real.pi / M)) *
            ∫⁻ α in Iα, ∫⁻ β in Iα, H (α ^ 3, β ^ 3)) := by
          gcongr
          exact pair_bound hM t0 (fun x => ∫⁻ α in Iα, H (x ^ 3, α ^ 3)) hK ht0
      _ = _ := (mul_assoc _ _ _).symm
  have hpi : ENNReal.ofReal (√(Real.pi / M)) * ENNReal.ofReal (√(Real.pi / M)) =
      ENNReal.ofReal (Real.pi / M) := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.mul_self_sqrt (by positivity)]
  -- substitutions and translations
  have hHc' : ∀ y : ℝ, Measurable fun x : ℝ => H (x, y) := fun y => hH.comp measurable_prodMk_right
  have step2 : ∫⁻ α in Iα, ∫⁻ β in Iα, H (α ^ 3, β ^ 3) ≤
      4⁻¹ * ∫⁻ c in Ic ×ˢ Ic, H (c.1 + 1 - A0, c.2 + 1 - A1) := by
    have hT : Measurable fun c : ℝ × ℝ => H (c.1 + 1 - A0, c.2 + 1 - A1) := by
      have := hH.comp (((measurable_fst.add_const 1).sub_const A0).prodMk
        ((measurable_snd.add_const 1).sub_const A1))
      simpa only [Function.comp_def] using this
    rw [Measure.volume_eq_prod, setLIntegral_prod _ hT.aemeasurable]
    calc ∫⁻ α in Iα, ∫⁻ β in Iα, H (α ^ 3, β ^ 3)
        ≤ ∫⁻ α in Iα, 2⁻¹ * ∫⁻ c2 in Ic, H (α ^ 3, c2 + 1 - A1) := by
          refine lintegral_mono fun α => ?_
          exact (cube_subst (fun u => H (α ^ 3, u))).trans
            (mul_le_mul' le_rfl (transl_bound (fun u => H (α ^ 3, u)) hA1))
      _ = 2⁻¹ * ∫⁻ α in Iα, (fun u => ∫⁻ c2 in Ic, H (u, c2 + 1 - A1)) (α ^ 3) :=
          lintegral_const_mul' _ _ (by simp)
      _ ≤ 2⁻¹ * (2⁻¹ * ∫⁻ c1 in Ic, ∫⁻ c2 in Ic, H (c1 + 1 - A0, c2 + 1 - A1)) := by
          exact mul_le_mul' le_rfl ((cube_subst (fun u => ∫⁻ c2 in Ic, H (u, c2 + 1 - A1))).trans
            (mul_le_mul' le_rfl (transl_bound (fun u => ∫⁻ c2 in Ic, H (u, c2 + 1 - A1)) hA0)))
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.mul_inv (by simp) (by simp)]; norm_num
  calc _ = ∫⁻ z in (Iα ×ˢ Jν) ×ˢ (Iα ×ˢ Jν), g0 z.1 * g1 z.2 * H (z.1.1 ^ 3, z.2.1 ^ 3) := rfl
    _ ≤ _ := step1
    _ ≤ ENNReal.ofReal (Real.pi / M) * (4⁻¹ * ∫⁻ c in Ic ×ˢ Ic, H (c.1 + 1 - A0, c.2 + 1 - A1)) := by
        rw [hpi]; gcongr
    _ = _ := (mul_assoc _ _ _).symm

end VectorSLT
