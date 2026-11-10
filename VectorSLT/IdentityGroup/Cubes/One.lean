import VectorSLT.IdentityGroup.Cubes.Scaling

/-!
# `CubeSumUpper 1`, and the outer-moment bound used for `k = 2`

By `cubeSumUpper_of_lintegral_lt_top` it suffices that `∫ e^{-G_k} < ∞` over all of
`Fin k → ℝ × ℝ`. Both cases use only the two outer moment coordinates:
`G_k ≥ (∑ aᵢ³)² + (∑ bᵢ³)²`, which separates the `a`-entries from the `b`-entries.

* `k = 1`: `a⁶ + b⁶ ≥ a² + b² - 2`, a Gaussian bound.
* `k = 2`: with `w = x + y`, `x³ + y³ = w (x² - xy + y²)` and `x² - xy + y² ≥ x²/2, w²/4`, so
  `(x³ + y³)² ≥ (x⁴/8 + 1/32) w² - 1/32`. The `y`-integral is a Gaussian of width
  `(x⁴/8 + 1/32)^{-1/2} ≲ (1 + |x|)^{-2}`, which is integrable in `x`.
-/

namespace VectorSLT.IdentityGroup.Cubes

open MeasureTheory Real
open scoped ENNReal

/-- The two outer moment coordinates bound `cubeSumSq` from below. -/
lemma outer_le_cubeSumSq {k : ℕ} (u : Fin k → ℝ × ℝ) :
    (∑ i, (u i).1 ^ 3) ^ 2 + (∑ i, (u i).2 ^ 3) ^ 2 ≤ cubeSumSq u := by
  simp only [cubeSumSq, Fin.sum_univ_four, cubeSum]
  simp only [Matrix.cons_val, Fin.isValue]
  nlinarith [sq_nonneg (∑ i, (u i).1 ^ 2 * (u i).2), sq_nonneg (∑ i, (u i).1 * (u i).2 ^ 2)]

/-- Finiteness of a one-dimensional Gaussian lower integral. -/
lemma lintegral_gauss_lt_top {b : ℝ} (hb : 0 < b) :
    ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-b * x ^ 2)) < ⊤ :=
  (integrable_exp_neg_mul_sq hb).lintegral_lt_top

/-- A shifted one-dimensional Gaussian lower integral. -/
lemma lintegral_gauss_shift {b : ℝ} (hb : 0 < b) (c : ℝ) :
    ∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-b * (c + y) ^ 2)) = ENNReal.ofReal (√(π / b)) := by
  rw [lintegral_add_left_eq_self (fun y => ENNReal.ofReal (Real.exp (-b * y ^ 2))) c,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq hb)
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le), integral_gaussian]

/-! ### `k = 1` -/

theorem lintegral_exp_neg_cubeSumSq_one_lt_top :
    ∫⁻ u : Fin 1 → ℝ × ℝ, ENNReal.ofReal (Real.exp (-cubeSumSq u)) < ⊤ := by
  set g : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp 2) * (ENNReal.ofReal (Real.exp (-1 * p.1 ^ 2)) *
      ENNReal.ofReal (Real.exp (-1 * p.2 ^ 2))) with hg
  have hbound : ∀ u : Fin 1 → ℝ × ℝ,
      ENNReal.ofReal (Real.exp (-cubeSumSq u)) ≤ g (MeasurableEquiv.funUnique (Fin 1) (ℝ × ℝ) u) := by
    intro u
    have h := outer_le_cubeSumSq u
    simp only [Fin.sum_univ_one] at h
    simp only [hg, MeasurableEquiv.funUnique_apply, Fin.default_eq_zero]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add, ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ((u 0).1 ^ 2 - 1), sq_nonneg ((u 0).2 ^ 2 - 1), sq_nonneg (u 0).1,
      sq_nonneg (u 0).2, mul_nonneg (sq_nonneg (u 0).1) (sq_nonneg ((u 0).1 ^ 2 - 1)),
      mul_nonneg (sq_nonneg (u 0).2) (sq_nonneg ((u 0).2 ^ 2 - 1))]
  calc ∫⁻ u : Fin 1 → ℝ × ℝ, ENNReal.ofReal (Real.exp (-cubeSumSq u))
      ≤ ∫⁻ u : Fin 1 → ℝ × ℝ, g (MeasurableEquiv.funUnique (Fin 1) (ℝ × ℝ) u) :=
        lintegral_mono hbound
    _ = ∫⁻ p : ℝ × ℝ, g p :=
        (volume_preserving_funUnique (Fin 1) (ℝ × ℝ)).lintegral_comp_emb
          (MeasurableEquiv.measurableEmbedding _) g
    _ < ⊤ := by
        simp only [hg]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Measure.volume_eq_prod,
          lintegral_prod_mul (f := fun x : ℝ => ENNReal.ofReal (Real.exp (-1 * x ^ 2)))
            (g := fun x : ℝ => ENNReal.ofReal (Real.exp (-1 * x ^ 2))) (by fun_prop) (by fun_prop)]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top (lintegral_gauss_lt_top one_pos) (lintegral_gauss_lt_top one_pos))

/-- **Lemma A-cubes, upper half, `k = 1`.** -/
theorem cubeSumUpper_one : CubeSumUpper 1 :=
  cubeSumUpper_of_lintegral_lt_top lintegral_exp_neg_cubeSumSq_one_lt_top

end VectorSLT.IdentityGroup.Cubes
