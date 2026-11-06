/-
Milestone C, leading-model assembly: two rows and four Gaussian (regular active)
coordinates give `Z ≥ c N⁻⁴ (log N)⁴` for the leading loss `K₀ = |u|² + ‖R(w)‖²`
of Theorem L (L2), where `R(w) = (P(a⁽¹⁾,b⁽¹⁾), P(a⁽²⁾,b⁽²⁾))`.
-/
import VectorSLT.LeadingRow

namespace VectorSLT

open MeasureTheory Set

/-- Parameters of the leading model: four active coordinates and two rows `(a⁽ʲ⁾, b⁽ʲ⁾)`. -/
abbrev LMParam := (Fin 4 → ℝ) × (((Fin 3 → ℝ) × (Fin 3 → ℝ)) × ((Fin 3 → ℝ) × (Fin 3 → ℝ)))

/-- The leading loss `K₀ = |u|² + ‖P(a⁽¹⁾,b⁽¹⁾)‖² + ‖P(a⁽²⁾,b⁽²⁾)‖²`. -/
def K0 (z : LMParam) : ℝ :=
  ∑ i, z.1 i ^ 2 + rowPsq z.2.1.1 z.2.1.2 + rowPsq z.2.2.1 z.2.2.2

/-- The box `[-ε, ε]¹⁶`. -/
def box16 (ε : ℝ) : Set LMParam :=
  {z | (∀ i, z.1 i ∈ Icc (-ε) ε) ∧
    ((∀ i, z.2.1.1 i ∈ Icc (-ε) ε) ∧ (∀ i, z.2.1.2 i ∈ Icc (-ε) ε)) ∧
    ((∀ i, z.2.2.1 i ∈ Icc (-ε) ε) ∧ (∀ i, z.2.2.2 i ∈ Icc (-ε) ε))}

/-- **Leading-model four-log lower bound.** For `N ≥ max (max 1 ((4/ε)¹⁰)) (1/ε²)`,
`∫_{[-ε,ε]¹⁶} e^{-N K₀} ≥ e^{-3} (cC²/16) N⁻⁴ (log N)⁴`. -/
theorem leadingModel_lower {ε N : ℝ} (hε : 0 < ε)
    (hN : max (max 1 ((4 / ε) ^ 10)) (1 / ε ^ 2) ≤ N) :
    ENNReal.ofReal (Real.exp (-3) * (cC ^ 2 / 16) * N⁻¹ ^ 4 * Real.log N ^ 4) ≤
      ∫⁻ z in box16 ε, ENNReal.ofReal (Real.exp (-(N * K0 z))) := by
  have hN1 : 1 ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN0 : 0 < N := by linarith
  have ht0 : 0 < N⁻¹ := inv_pos.mpr hN0
  have ht : N⁻¹ ≤ min 1 ((ε / 4) ^ 10) := by
    refine le_min (inv_le_one_of_one_le₀ hN1) ?_
    rw [inv_le_comm₀ hN0 (by positivity), ← inv_pow, inv_div]
    exact (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hrow := rowSublevel_lower_explicit hε ht0 ht
  rw [one_div, inv_inv] at hrow
  -- the active cube of side s = 1/(2√N)
  set s := 1 / (2 * √N)
  have hs : 0 < s := by positivity
  have hs2 : s ^ 2 = N⁻¹ / 4 := by
    simp only [s]; rw [div_pow, mul_pow, Real.sq_sqrt hN0.le]; field_simp; ring
  have hsε : s ≤ ε := by
    have h1 : 1 / ε ^ 2 ≤ N := (le_max_right _ _).trans hN
    have : s ^ 2 ≤ ε ^ 2 := by
      rw [hs2]
      have : N⁻¹ ≤ ε ^ 2 := by
        rw [inv_le_comm₀ hN0 (by positivity)]; simpa [one_div] using h1
      linarith
    exact (pow_le_pow_iff_left₀ hs.le hε.le (by norm_num)).mp this
  set U : Set (Fin 4 → ℝ) := Set.pi univ fun _ => Icc 0 s
  have hU : volume U = ENNReal.ofReal (s ^ 4) := by
    rw [volume_pi_pi]
    simp only [Real.volume_Icc, sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [ENNReal.ofReal_pow hs.le]
  set S := rowSublevel ε N⁻¹
  have hcC : 0 < cC := by unfold cC; norm_num
  -- lower region inside the box, where e^{-N K₀} ≥ e^{-3}
  have hsub : U ×ˢ (S ×ˢ S) ⊆ box16 ε := by
    rintro ⟨u, x, y⟩ ⟨hu, hx, hy⟩
    refine ⟨fun i => ⟨?_, ?_⟩, ⟨hx.1, hx.2.1⟩, ⟨hy.1, hy.2.1⟩⟩
    · have := (hu i (mem_univ _)).1; linarith
    · exact (hu i (mem_univ _)).2.trans hsε
  have hK : ∀ z ∈ U ×ˢ (S ×ˢ S), N * K0 z ≤ 3 := by
    rintro ⟨u, x, y⟩ ⟨hu, hx, hy⟩
    have hu2 : ∑ i, u i ^ 2 ≤ N⁻¹ := by
      have : ∀ i, u i ^ 2 ≤ s ^ 2 := fun i =>
        pow_le_pow_left₀ (hu i (mem_univ _)).1 (hu i (mem_univ _)).2 2
      calc ∑ i, u i ^ 2 ≤ ∑ _i : Fin 4, s ^ 2 := Finset.sum_le_sum fun i _ => this i
        _ = N⁻¹ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hs2]; simp; ring
    have h1 := hx.2.2
    have h2 := hy.2.2
    simp only [K0]
    have : N * N⁻¹ = 1 := mul_inv_cancel₀ hN0.ne'
    nlinarith
  calc ENNReal.ofReal (Real.exp (-3) * (cC ^ 2 / 16) * N⁻¹ ^ 4 * Real.log N ^ 4)
      = ENNReal.ofReal (Real.exp (-3)) * (ENNReal.ofReal (s ^ 4) *
          (ENNReal.ofReal (cC * N⁻¹ * Real.log N ^ 2) *
            ENNReal.ofReal (cC * N⁻¹ * Real.log N ^ 2))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]; ring
    _ ≤ ENNReal.ofReal (Real.exp (-3)) * (volume U * (volume S * volume S)) := by
        rw [hU]; gcongr
    _ = ∫⁻ _ in U ×ˢ (S ×ˢ S), ENNReal.ofReal (Real.exp (-3)) := by
        have hSS : volume (S ×ˢ S) = volume S * volume S := by
          rw [Measure.volume_eq_prod (α := (Fin 3 → ℝ) × (Fin 3 → ℝ))
            (β := (Fin 3 → ℝ) × (Fin 3 → ℝ)), Measure.prod_prod]
        rw [setLIntegral_const, Measure.volume_eq_prod (α := Fin 4 → ℝ), Measure.prod_prod,
          hSS, mul_comm]
    _ ≤ ∫⁻ z in U ×ˢ (S ×ˢ S), ENNReal.ofReal (Real.exp (-(N * K0 z))) := by
        refine setLIntegral_mono ?_ fun z hz => ?_
        · unfold K0 rowPsq rowP; fun_prop
        · exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hK z hz]))
    _ ≤ _ := lintegral_mono_set hsub

end VectorSLT
