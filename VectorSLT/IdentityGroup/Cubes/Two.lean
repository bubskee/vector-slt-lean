import VectorSLT.IdentityGroup.Cubes.One

/-!
# `CubeSumUpper 2`

`G_2 ≥ (a₀³ + a₁³)² + (b₀³ + b₁³)²` separates the `a`-entries from the `b`-entries, so
`∫ e^{-G_2}` over `ℝ⁴` is at most the square of `∫_{ℝ²} e^{-(x³ + y³)²}`. With `w = x + y`,
`x³ + y³ = w (x² - xy + y²)`, and `x² - xy + y² ≥ x²/2` and `≥ w²/4`. Hence
`(x³ + y³)² ≥ (x⁴/8 + 1/32) w² - 1/32` (`two_cube_lower`). The `y`-integral is then a Gaussian
of width `(x⁴/8 + 1/32)^{-1/2} ≤ 16 (1 + |x|)^{-2}`, integrable in `x`.

This is not the paper's route (local charts at collinear zeros and a radial integration); see
`NOTES_cubes.md`.
-/

namespace VectorSLT.IdentityGroup.Cubes

open MeasureTheory Real
open scoped ENNReal

/-- The pointwise lower bound behind `k = 2`. -/
lemma two_cube_lower (x y : ℝ) : (x ^ 4 / 8 + 1 / 32) * (x + y) ^ 2 - 1 / 32 ≤ (x ^ 3 + y ^ 3) ^ 2 := by
  set w := x + y with hw
  set Q := x ^ 2 - x * y + y ^ 2 with hQ
  have hfac : x ^ 3 + y ^ 3 = w * Q := by rw [hw, hQ]; ring
  have hQ1 : x ^ 2 / 2 ≤ Q := by rw [hQ]; nlinarith [sq_nonneg (y - x / 2)]
  have hQ2 : w ^ 2 / 4 ≤ Q := by rw [hQ, hw]; nlinarith [sq_nonneg (x - y)]
  have hQ1' : (x ^ 2 / 2) ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ (by positivity) hQ1 2
  have hQ2' : (w ^ 2 / 4) ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ (by positivity) hQ2 2
  have hw2 : 0 ≤ w ^ 2 := sq_nonneg w
  have h6 : w ^ 2 - 1 ≤ w ^ 6 := by
    nlinarith [mul_nonneg hw2 (sq_nonneg (w ^ 2 - 1)), sq_nonneg (w ^ 2 - 1 / 2)]
  rw [hfac, mul_pow]
  nlinarith [mul_le_mul_of_nonneg_left hQ1' hw2, mul_le_mul_of_nonneg_left hQ2' hw2]

lemma one_add_abs_pow_four_le (x : ℝ) : (1 + |x|) ^ 4 ≤ 8 * (1 + x ^ 4) := by
  have ht : 0 ≤ |x| := abs_nonneg x
  have hx4 : |x| ^ 4 = x ^ 4 := by rw [pow_abs]; exact abs_of_nonneg (by positivity)
  rw [← hx4]
  nlinarith [sq_nonneg (|x| - 1), sq_nonneg (|x| ^ 2 - 1), mul_nonneg ht (sq_nonneg (|x| - 1)),
    sq_nonneg (|x| ^ 2 + |x|), mul_nonneg (mul_nonneg ht ht) (sq_nonneg (|x| - 1))]

/-- `∫_{ℝ²} e^{-(x³ + y³)²} < ∞`. -/
lemma lintegral_two_cube_lt_top :
    ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.exp (-(p.1 ^ 3 + p.2 ^ 3) ^ 2)) < ⊤ := by
  set β : ℝ → ℝ := fun x => x ^ 4 / 8 + 1 / 32 with hβdef
  have hβ : ∀ x, 0 < β x := fun x => by simp only [hβdef]; positivity
  have hint : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (by simp)
  calc ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.exp (-(p.1 ^ 3 + p.2 ^ 3) ^ 2))
      ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (Real.exp (-(x ^ 3 + y ^ 3) ^ 2)) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_le (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(p.1 ^ 3 + p.2 ^ 3) ^ 2)))
    _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (Real.exp (1 / 32)) *
          ENNReal.ofReal (Real.exp (-β x * (x + y) ^ 2)) := by
        refine lintegral_mono fun x => lintegral_mono fun y => ?_
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        simp only [hβdef]
        nlinarith [two_cube_lower x y]
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp (1 / 32)) * ENNReal.ofReal (√(π / β x)) := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_gauss_shift (hβ x)]
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (1 / 32) * (√π * 16) * (1 + ‖x‖) ^ (-(2 : ℝ))) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
        have h1 : 0 < 1 + ‖x‖ := by positivity
        rw [Real.rpow_neg h1.le, Real.rpow_two, Real.sqrt_div' _ (hβ x).le, mul_assoc,
          ← div_eq_mul_inv]
        rw [div_le_iff₀ (Real.sqrt_pos.mpr (hβ x)), mul_assoc]
        refine le_mul_of_one_le_right (Real.sqrt_nonneg _) ?_
        rw [div_mul_eq_mul_div, one_le_div (by positivity)]
        have hsq : (1 + ‖x‖) ^ 2 / 16 ≤ √(β x) := by
          rw [Real.le_sqrt (by positivity) (hβ x).le]
          have := one_add_abs_pow_four_le x
          have h2 : ((1 + |x|) ^ 2 / 16) ^ 2 = (1 + |x|) ^ 4 / 256 := by ring
          simp only [hβdef, Real.norm_eq_abs]
          rw [h2]
          nlinarith [pow_nonneg (sq_nonneg x) 2]
        linarith
    _ < ⊤ := (hint.const_mul _).lintegral_lt_top

theorem lintegral_exp_neg_cubeSumSq_two_lt_top :
    ∫⁻ u : Fin 2 → ℝ × ℝ, ENNReal.ofReal (Real.exp (-cubeSumSq u)) < ⊤ := by
  set Φ : (Fin 2 → ℝ) → ℝ≥0∞ := fun v => ENNReal.ofReal (Real.exp (-(v 0 ^ 3 + v 1 ^ 3) ^ 2))
    with hΦ
  set e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 2)
  have hbound : ∀ u : Fin 2 → ℝ × ℝ,
      ENNReal.ofReal (Real.exp (-cubeSumSq u)) ≤ (fun z => Φ z.1 * Φ z.2) (e u) := by
    intro u
    have h := outer_le_cubeSumSq u
    simp only [Fin.sum_univ_two] at h
    simp only [hΦ, e]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    change -cubeSumSq u ≤ -((u 0).1 ^ 3 + (u 1).1 ^ 3) ^ 2 + -((u 0).2 ^ 3 + (u 1).2 ^ 3) ^ 2
    linarith
  have hΦint : ∫⁻ v : Fin 2 → ℝ, Φ v < ⊤ := by
    have := (volume_preserving_finTwoArrow ℝ).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _)
      (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(p.1 ^ 3 + p.2 ^ 3) ^ 2)))
    simp only [MeasurableEquiv.finTwoArrow_apply] at this
    rw [hΦ, this]
    exact lintegral_two_cube_lt_top
  calc ∫⁻ u : Fin 2 → ℝ × ℝ, ENNReal.ofReal (Real.exp (-cubeSumSq u))
      ≤ ∫⁻ u : Fin 2 → ℝ × ℝ, (fun z => Φ z.1 * Φ z.2) (e u) := lintegral_mono hbound
    _ = ∫⁻ z : (Fin 2 → ℝ) × (Fin 2 → ℝ), Φ z.1 * Φ z.2 :=
        (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 2)).lintegral_comp_emb
          e.measurableEmbedding (fun z => Φ z.1 * Φ z.2)
    _ < ⊤ := by
        rw [Measure.volume_eq_prod, lintegral_prod_mul (by fun_prop) (by fun_prop)]
        exact ENNReal.mul_lt_top hΦint hΦint

/-- **Lemma A-cubes, upper half, `k = 2`.** -/
theorem cubeSumUpper_two : CubeSumUpper 2 :=
  cubeSumUpper_of_lintegral_lt_top lintegral_exp_neg_cubeSumSq_two_lt_top

end VectorSLT.IdentityGroup.Cubes
