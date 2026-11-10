import VectorSLT.IdentityGroup.Defs

/-!
# Homogeneity reduction for `CubeSumUpper`

`cubeSumSq` is homogeneous of degree six on `Fin k → ℝ × ℝ`, a space of real dimension `2k`.
The substitution `u ↦ (cN)^{1/6} u` turns `∫ e^{-cN G}` over the whole space into
`(cN)^{-k/3} ∫ e^{-G}`. So `CubeSumUpper k` follows from the single finiteness statement
`∫ e^{-G} < ∞` over all of `Fin k → ℝ × ℝ` (`cubeSumUpper_of_lintegral_lt_top`).
-/

namespace VectorSLT.IdentityGroup.Cubes

open MeasureTheory Real Module
open scoped ENNReal

/-- Each moment coordinate of `cubeSum` is homogeneous of degree three. -/
lemma cubeSum_smul {k : ℕ} (t : ℝ) (u : Fin k → ℝ × ℝ) (j : Fin 4) :
    cubeSum (t • u) j = t ^ 3 * cubeSum u j := by
  fin_cases j <;>
    simp only [cubeSum, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Finset.mul_sum, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
    exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- `cubeSumSq` is homogeneous of degree six. -/
lemma cubeSumSq_smul {k : ℕ} (t : ℝ) (u : Fin k → ℝ × ℝ) :
    cubeSumSq (t • u) = t ^ 6 * cubeSumSq u := by
  simp only [cubeSumSq, cubeSum_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

@[fun_prop]
lemma measurable_cubeSumSq {n : ℕ} : Measurable (cubeSumSq (k := n)) := by
  unfold cubeSumSq cubeSum
  fun_prop

lemma cubeSumSq_nonneg {k : ℕ} (u : Fin k → ℝ × ℝ) : 0 ≤ cubeSumSq u :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Scaling of a lower Lebesgue integral under a Haar measure. -/
lemma lintegral_comp_smul_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (f : E → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    ∫⁻ x, f (r • x) ∂μ = ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| * ∫⁻ x, f x ∂μ := by
  let e := (Homeomorph.smulOfNeZero (α := E) r hr).toMeasurableEquiv
  have he : (e : E → E) = (r • ·) := rfl
  have h1 : ∫⁻ x, f (r • x) ∂μ = ∫⁻ x, f (e x) ∂μ := by rw [he]
  rw [h1, ← lintegral_map_equiv f e, he, Measure.map_addHaar_smul μ hr, lintegral_smul_measure,
    smul_eq_mul]

lemma finrank_forms (k : ℕ) : finrank ℝ (Fin k → ℝ × ℝ) = 2 * k := by
  simp [Module.finrank_pi_fintype, Module.finrank_prod, mul_comm]

/-- **Homogeneity reduction.** If `∫ e^{-G_k} < ∞` over the whole space, then
`CubeSumUpper k` holds. -/
theorem cubeSumUpper_of_lintegral_lt_top {k : ℕ}
    (h : ∫⁻ u : Fin k → ℝ × ℝ, ENNReal.ofReal (Real.exp (-cubeSumSq u)) < ⊤) :
    CubeSumUpper k := by
  intro r c _ hc
  set I := ∫⁻ u : Fin k → ℝ × ℝ, ENNReal.ofReal (Real.exp (-cubeSumSq u)) with hI
  refine ⟨c ^ (-(k : ℝ) / 3) * I.toReal, fun N hN => ?_⟩
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  have hcN : 0 < c * N := mul_pos hc hN0
  set t := (c * N) ^ ((1 : ℝ) / 6) with ht_def
  have ht : 0 < t := rpow_pos_of_pos hcN _
  have ht6 : t ^ 6 = c * N := by
    rw [ht_def, ← rpow_natCast, ← rpow_mul hcN.le]; norm_num
  have key : ∀ u : Fin k → ℝ × ℝ, c * N * cubeSumSq u = cubeSumSq (t • u) := by
    intro u; rw [cubeSumSq_smul, ht6]
  have htk : (t ^ finrank ℝ (Fin k → ℝ × ℝ))⁻¹ = c ^ (-(k : ℝ) / 3) * N ^ (-(k : ℝ) / 3) := by
    rw [finrank_forms, ht_def, ← rpow_natCast, ← rpow_mul hcN.le, ← rpow_neg hcN.le,
      mul_rpow hc.le hN0.le]
    congr 2 <;> push_cast <;> ring
  calc ∫⁻ u in Metric.closedBall (0 : Fin k → ℝ × ℝ) r,
        ENNReal.ofReal (Real.exp (-(c * N * cubeSumSq u)))
      ≤ ∫⁻ u, ENNReal.ofReal (Real.exp (-(c * N * cubeSumSq u))) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ u, ENNReal.ofReal (Real.exp (-cubeSumSq (t • u))) := by simp_rw [key]
    _ = ENNReal.ofReal |(t ^ finrank ℝ (Fin k → ℝ × ℝ))⁻¹| * I :=
        lintegral_comp_smul_eq volume (fun u => ENNReal.ofReal (Real.exp (-cubeSumSq u))) ht.ne'
    _ = ENNReal.ofReal (c ^ (-(k : ℝ) / 3) * I.toReal * N ^ (-(k : ℝ) / 3)) := by
        rw [htk, abs_of_nonneg (by positivity)]
        rw [show c ^ (-(k : ℝ) / 3) * I.toReal * N ^ (-(k : ℝ) / 3)
            = c ^ (-(k : ℝ) / 3) * N ^ (-(k : ℝ) / 3) * I.toReal by ring,
          ENNReal.ofReal_mul (p := c ^ (-(k : ℝ) / 3) * N ^ (-(k : ℝ) / 3)) (q := I.toReal)
            (by positivity), ENNReal.ofReal_toReal h.ne]

end VectorSLT.IdentityGroup.Cubes
