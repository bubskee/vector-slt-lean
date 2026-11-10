import VectorSLT.IdentityGroup.Cubes.Scaling

/-!
# The lower half of Lemma A-cubes, for every `k`

`G_k(u) ≤ 4k² ‖u‖⁶` in the sup norm, so on the ball of radius `ρ = min(r, 1) N^{-1/6}` the
integrand `e^{-cN G_k}` is at least `e^{-4ck²}`. That ball has volume
`min(r, 1)^{2k} N^{-k/3} · vol(B₁)`. Nothing in the paper needs this direction from the library;
it is recorded as the paper's "the ball of radius `N^{-1/6}` gives the lower bound".
-/

namespace VectorSLT.IdentityGroup.Cubes

open MeasureTheory Real Module
open scoped ENNReal

/-- The lower half of Lemma A-cubes (stated here; not part of the shared interface). -/
def CubeSumLower (k : ℕ) : Prop :=
  ∀ r c : ℝ, 0 < r → 0 < c → ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N →
    ENNReal.ofReal (C * N ^ (-(k : ℝ) / 3)) ≤
      ∫⁻ u in Metric.closedBall (0 : Fin k → ℝ × ℝ) r,
        ENNReal.ofReal (Real.exp (-(c * N * cubeSumSq u)))

lemma abs_moment_le {k : ℕ} (u : Fin k → ℝ × ℝ) (f : ℝ × ℝ → ℝ)
    (hf : ∀ z : ℝ × ℝ, |f z| ≤ ‖z‖ ^ 3) : |∑ i, f (u i)| ≤ k * ‖u‖ ^ 3 := by
  calc |∑ i, f (u i)| ≤ ∑ i, |f (u i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin k, ‖u‖ ^ 3 := Finset.sum_le_sum fun i _ =>
        (hf (u i)).trans (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm u i) 3)
    _ = k * ‖u‖ ^ 3 := by simp

lemma cubeSumSq_le {k : ℕ} (u : Fin k → ℝ × ℝ) : cubeSumSq u ≤ 4 * k ^ 2 * ‖u‖ ^ 6 := by
  have h1 : ∀ z : ℝ × ℝ, |z.1| ≤ ‖z‖ := fun z => by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_left _ _
  have h2 : ∀ z : ℝ × ℝ, |z.2| ≤ ‖z‖ := fun z => by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_right _ _
  have hm : ∀ (f : ℝ × ℝ → ℝ), (∀ z : ℝ × ℝ, |f z| ≤ ‖z‖ ^ 3) →
      (∑ i, f (u i)) ^ 2 ≤ k ^ 2 * ‖u‖ ^ 6 := by
    intro f hf
    have := abs_moment_le u f hf
    calc (∑ i, f (u i)) ^ 2 = |∑ i, f (u i)| ^ 2 := (sq_abs _).symm
      _ ≤ (k * ‖u‖ ^ 3) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = k ^ 2 * ‖u‖ ^ 6 := by ring
  have e0 := hm (fun z => z.1 ^ 3) fun z => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (h1 z) 3
  have e1 := hm (fun z => z.1 ^ 2 * z.2) fun z => by
    rw [abs_mul, abs_pow]
    calc |z.1| ^ 2 * |z.2| ≤ ‖z‖ ^ 2 * ‖z‖ :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (h1 z) 2) (h2 z) (abs_nonneg _)
            (pow_nonneg (norm_nonneg _) 2)
      _ = ‖z‖ ^ 3 := by ring
  have e2 := hm (fun z => z.1 * z.2 ^ 2) fun z => by
    rw [abs_mul, abs_pow]
    calc |z.1| * |z.2| ^ 2 ≤ ‖z‖ * ‖z‖ ^ 2 :=
          mul_le_mul (h1 z) (pow_le_pow_left₀ (abs_nonneg _) (h2 z) 2)
            (pow_nonneg (abs_nonneg _) 2) (norm_nonneg _)
      _ = ‖z‖ ^ 3 := by ring
  have e3 := hm (fun z => z.2 ^ 3) fun z => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (h2 z) 3
  simp only [cubeSumSq, Fin.sum_univ_four, cubeSum, Matrix.cons_val, Fin.isValue]
  linarith

/-- **Lemma A-cubes, lower half, for every `k`.** -/
theorem cubeSumLower_all (k : ℕ) : CubeSumLower k := by
  intro r c hr hc
  set m := min r 1 with hm
  have hm0 : 0 < m := lt_min hr one_pos
  have hm1 : m ≤ 1 := min_le_right _ _
  set V := volume (Metric.ball (0 : Fin k → ℝ × ℝ) 1) with hV
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos volume 0 one_pos).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  set E := Real.exp (-(4 * c * k ^ 2)) with hE
  refine ⟨E * m ^ (2 * k) * V.toReal, by
    have := ENNReal.toReal_pos hV0 hVt; positivity, fun N hN => ?_⟩
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  set t := N ^ (-(1 : ℝ) / 6) with ht
  have ht0 : 0 < t := rpow_pos_of_pos hN0 _
  have ht1 : t ≤ 1 := rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
  have ht6 : t ^ 6 = N⁻¹ := by
    rw [ht, ← rpow_natCast, ← rpow_mul hN0.le,
      show (-(1 : ℝ) / 6) * ((6 : ℕ) : ℝ) = -1 by norm_num, rpow_neg_one]
  have htk : t ^ (2 * k) = N ^ (-(k : ℝ) / 3) := by
    rw [ht, ← rpow_natCast, ← rpow_mul hN0.le]; congr 1; push_cast; ring
  set ρ := m * t with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρr : ρ ≤ r := by
    calc ρ = m * t := rfl
      _ ≤ m * 1 := by gcongr
      _ ≤ r := by rw [mul_one]; exact min_le_left _ _
  have hpt : ∀ u ∈ Metric.closedBall (0 : Fin k → ℝ × ℝ) ρ,
      ENNReal.ofReal E ≤ ENNReal.ofReal (Real.exp (-(c * N * cubeSumSq u))) := by
    intro u hu
    rw [mem_closedBall_zero_iff] at hu
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have hu6 : ‖u‖ ^ 6 ≤ N⁻¹ := by
      calc ‖u‖ ^ 6 ≤ ρ ^ 6 := pow_le_pow_left₀ (norm_nonneg _) hu 6
        _ = m ^ 6 * t ^ 6 := by rw [hρ]; ring
        _ ≤ 1 * N⁻¹ := by
            rw [ht6]; gcongr; exact pow_le_one₀ hm0.le hm1
        _ = N⁻¹ := one_mul _
    have hG := cubeSumSq_le u
    have : c * N * cubeSumSq u ≤ 4 * c * k ^ 2 := by
      calc c * N * cubeSumSq u ≤ c * N * (4 * k ^ 2 * ‖u‖ ^ 6) := by gcongr
        _ ≤ c * N * (4 * k ^ 2 * N⁻¹) := by gcongr
        _ = 4 * c * k ^ 2 := by field_simp
    linarith
  calc ENNReal.ofReal (E * m ^ (2 * k) * V.toReal * N ^ (-(k : ℝ) / 3))
      = ENNReal.ofReal E * volume (Metric.closedBall (0 : Fin k → ℝ × ℝ) ρ) := by
        rw [Measure.addHaar_closedBall volume 0 hρ0, finrank_forms, ← hV, hρ, mul_pow, htk,
          ← ENNReal.ofReal_toReal hVt, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
        ring_nf
    _ = ∫⁻ _u in Metric.closedBall (0 : Fin k → ℝ × ℝ) ρ, ENNReal.ofReal E :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ u in Metric.closedBall (0 : Fin k → ℝ × ℝ) ρ,
          ENNReal.ofReal (Real.exp (-(c * N * cubeSumSq u))) :=
        setLIntegral_mono (by fun_prop) hpt
    _ ≤ ∫⁻ u in Metric.closedBall (0 : Fin k → ℝ × ℝ) r,
          ENNReal.ofReal (Real.exp (-(c * N * cubeSumSq u))) :=
        lintegral_mono_set (Metric.closedBall_subset_closedBall hρr)

end VectorSLT.IdentityGroup.Cubes
