/-
Milestone B, one-dimensional ingredients.
-/
import Mathlib

namespace VectorSLT

open MeasureTheory Set

/-- Sublevel set of `|w² - e|` on the line: measure at most `4 τ / √|e|`. -/
theorem volume_abs_sq_sub_le (e τ : ℝ) (he : e ≠ 0) (hτ : 0 ≤ τ) :
    volume {w : ℝ | |w ^ 2 - e| ≤ τ} ≤ ENNReal.ofReal (4 * τ / √|e|) := by
  rcases lt_or_gt_of_ne he with he' | he'
  · -- e < 0
    have hae : |e| = -e := abs_of_neg he'
    by_cases hτe : τ < -e
    · have : {w : ℝ | |w ^ 2 - e| ≤ τ} = ∅ := by
        ext w; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
        rw [abs_of_pos (by nlinarith [sq_nonneg w])]; nlinarith [sq_nonneg w]
      rw [this, measure_empty]; exact bot_le
    · push Not at hτe
      have hsub : {w : ℝ | |w ^ 2 - e| ≤ τ} ⊆ Icc (-√τ) (√τ) := by
        intro w hw
        simp only [mem_ofPred_eq] at hw
        have h1 : w ^ 2 ≤ τ := by have := (abs_le.mp hw).2; linarith
        exact abs_le.mp (Real.abs_le_sqrt h1)
      refine (measure_mono hsub).trans ?_
      rw [Real.volume_Icc]
      apply ENNReal.ofReal_le_ofReal
      rw [hae]
      have hs : 0 < √(-e) := Real.sqrt_pos.mpr (by linarith)
      rw [le_div_iff₀ hs]
      have h1 : √(-e) ≤ √τ := Real.sqrt_le_sqrt hτe
      have h2 : √τ * √τ = τ := Real.mul_self_sqrt hτ
      nlinarith [Real.sqrt_nonneg τ]
  · -- e > 0
    have hae : |e| = e := abs_of_pos he'
    rw [hae]
    have hse : 0 < √e := Real.sqrt_pos.mpr he'
    by_cases hτe : τ < e
    · set p := √(e - τ)
      set q := √(e + τ)
      have hp2 : p ^ 2 = e - τ := Real.sq_sqrt (by linarith)
      have hq2 : q ^ 2 = e + τ := Real.sq_sqrt (by linarith)
      have hp0 : 0 ≤ p := Real.sqrt_nonneg _
      have hq0 : 0 ≤ q := Real.sqrt_nonneg _
      have hsub : {w : ℝ | |w ^ 2 - e| ≤ τ} ⊆ Icc p q ∪ Icc (-q) (-p) := by
        intro w hw
        simp only [mem_ofPred_eq] at hw
        obtain ⟨h1, h2⟩ := abs_le.mp hw
        have hw1 : p ^ 2 ≤ w ^ 2 := by linarith
        have hw2 : w ^ 2 ≤ q ^ 2 := by linarith
        have ha1 : p ≤ |w| := by
          have := Real.sqrt_le_sqrt hw1
          rwa [Real.sqrt_sq hp0, Real.sqrt_sq_eq_abs] at this
        have ha2 : |w| ≤ q := by
          have := Real.sqrt_le_sqrt hw2
          rwa [Real.sqrt_sq hq0, Real.sqrt_sq_eq_abs] at this
        rcases le_total 0 w with hw0 | hw0
        · rw [abs_of_nonneg hw0] at ha1 ha2; exact Or.inl ⟨ha1, ha2⟩
        · rw [abs_of_nonpos hw0] at ha1 ha2; exact Or.inr ⟨by linarith, by linarith⟩
      refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
      rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by linarith [Real.sqrt_le_sqrt (show e - τ ≤ e + τ by linarith)]) (by linarith [Real.sqrt_le_sqrt (show e - τ ≤ e + τ by linarith)])]
      apply ENNReal.ofReal_le_ofReal
      -- (q - p) (q + p) = 2τ and q ≥ √e
      have hqe : √e ≤ q := Real.sqrt_le_sqrt (by linarith)
      have hprod : (q - p) * (q + p) = 2 * τ := by nlinarith
      rw [le_div_iff₀ hse]
      nlinarith [mul_le_mul_of_nonneg_left hqe (show 0 ≤ q - p by nlinarith)]
    · push Not at hτe
      have hsub : {w : ℝ | |w ^ 2 - e| ≤ τ} ⊆ Icc (-√(e + τ)) (√(e + τ)) := by
        intro w hw
        simp only [mem_ofPred_eq] at hw
        have h1 : w ^ 2 ≤ e + τ := by have := (abs_le.mp hw).2; linarith
        exact abs_le.mp (Real.abs_le_sqrt h1)
      refine (measure_mono hsub).trans ?_
      rw [Real.volume_Icc]
      apply ENNReal.ofReal_le_ofReal
      rw [le_div_iff₀ hse]
      -- √(e+τ) √e ≤ √(2τ) √τ = √2 τ ≤ 2τ
      have h1 : √(e + τ) ≤ √(2 * τ) := Real.sqrt_le_sqrt (by linarith)
      have h2 : √e ≤ √τ := Real.sqrt_le_sqrt hτe
      have h3 : √(2 * τ) = √2 * √τ := Real.sqrt_mul (by norm_num) τ
      have h4 : √τ * √τ = τ := Real.mul_self_sqrt hτ
      have h5 : √2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have h6 : √(e + τ) * √e ≤ √2 * τ := by
        calc √(e + τ) * √e ≤ (√2 * √τ) * √τ := by
              rw [← h3]; exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          _ = √2 * τ := by rw [mul_assoc, h4]
      nlinarith [Real.sqrt_nonneg (e + τ)]

/-- Sublevel set of a real quadratic `a x² + b x + c` (with `a` possibly zero) on the line:
measure at most `8 σ / √|Δ|`, `Δ = b² - 4ac`, provided `Δ ≠ 0`. -/
theorem volume_abs_quad_le_of_ne (a b c σ : ℝ) (hσ : 0 ≤ σ) (hΔ : b ^ 2 - 4 * a * c ≠ 0) :
    volume {x : ℝ | |a * x ^ 2 + b * x + c| ≤ σ} ≤
      ENNReal.ofReal (8 * σ / √|b ^ 2 - 4 * a * c|) := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b ≠ 0 := by intro hb; apply hΔ; simp [hb]
    have hb' : 0 < |b| := abs_pos.mpr hb
    have hsub : {x : ℝ | |0 * x ^ 2 + b * x + c| ≤ σ} ⊆
        Icc (-c / b - σ / |b|) (-c / b + σ / |b|) := by
      intro x hx
      simp only [mem_ofPred_eq, zero_mul, zero_add] at hx
      have : b * x + c = b * (x - (-c / b)) := by field_simp; ring
      rw [this, abs_mul] at hx
      have h2 : |x - -c / b| ≤ σ / |b| := by rw [le_div_iff₀ hb']; linarith
      have := abs_le.mp h2
      exact ⟨by linarith, by linarith⟩
    refine (measure_mono hsub).trans ?_
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    have : √|b ^ 2 - 4 * 0 * c| = |b| := by simp [Real.sqrt_sq_eq_abs]
    rw [this]
    rw [show -c / b + σ / |b| - (-c / b - σ / |b|) = 2 * σ / |b| by ring]
    exact div_le_div_of_nonneg_right (by linarith) hb'.le
  · set Δ := b ^ 2 - 4 * a * c
    set e := Δ / (4 * a ^ 2)
    have ha2 : 0 < a ^ 2 := by positivity
    have haa : 0 < |a| := abs_pos.mpr ha
    have he : e ≠ 0 := div_ne_zero hΔ (by positivity)
    have hset : {x : ℝ | |a * x ^ 2 + b * x + c| ≤ σ} =
        (fun x => x + b / (2 * a)) ⁻¹' {w : ℝ | |w ^ 2 - e| ≤ σ / |a|} := by
      ext x
      simp only [mem_ofPred_eq, mem_preimage]
      have : a * x ^ 2 + b * x + c = a * ((x + b / (2 * a)) ^ 2 - e) := by
        simp only [e, Δ]; field_simp; ring
      rw [this, abs_mul, le_div_iff₀ haa, mul_comm]
    rw [hset, measure_preimage_add_right]
    refine (volume_abs_sq_sub_le e (σ / |a|) he (by positivity)).trans ?_
    apply le_of_eq; congr 1
    have h1 : |e| = |Δ| / (4 * a ^ 2) := by
      simp only [e]; rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 4 * a ^ 2)]
    have h2 : √(4 * a ^ 2) = 2 * |a| := by
      rw [show 4 * a ^ 2 = (2 * |a|) ^ 2 by rw [mul_pow, sq_abs]; norm_num]
      exact Real.sqrt_sq (by positivity)
    have hD : 0 < √|Δ| := Real.sqrt_pos.mpr (abs_pos.mpr hΔ)
    rw [h1, Real.sqrt_div' _ (by positivity), h2]
    field_simp; ring

/-- ENNReal form, valid with no hypothesis on the discriminant (`x / 0 = ⊤`). -/
theorem volume_abs_quad_le (a b c σ : ℝ) (hσ : 0 < σ) :
    volume {x : ℝ | |a * x ^ 2 + b * x + c| ≤ σ} ≤
      ENNReal.ofReal (8 * σ) / ENNReal.ofReal (√|b ^ 2 - 4 * a * c|) := by
  rcases eq_or_ne (b ^ 2 - 4 * a * c) 0 with h | h
  · rw [h, abs_zero, Real.sqrt_zero, ENNReal.ofReal_zero,
      ENNReal.div_zero (by simp [hσ])]
    exact le_top
  · rw [← ENNReal.ofReal_div_of_pos (Real.sqrt_pos.mpr (abs_pos.mpr h))]
    exact volume_abs_quad_le_of_ne a b c σ hσ.le h

/-- `∫⁻_{[β,γ]} K/(y-r) = K log((γ-r)/(β-r))` for `r < β ≤ γ`. -/
theorem lintegral_Icc_div_sub (K r β γ : ℝ) (hK : 0 ≤ K) (hβ : r < β) (hβγ : β ≤ γ) :
    ∫⁻ y in Icc β γ, ENNReal.ofReal (K / (y - r)) =
      ENNReal.ofReal (K * Real.log ((γ - r) / (β - r))) := by
  have hcont : ContinuousOn (fun y => K / (y - r)) (Icc β γ) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
    intro y hy; have := hy.1; simp only [Pi.sub_apply, id]; linarith
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hβγ,
      intervalIntegral.integral_comp_sub_right (fun x => K / x)]
    simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul]
    rw [integral_inv_of_pos (by linarith) (by linarith), div_eq_mul_inv]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact div_nonneg hK (by linarith [hy.1])

/-- Reflected version: `∫⁻_{[β,γ]} K/(r-y) = K log((r-β)/(r-γ))` for `β ≤ γ < r`. -/
theorem lintegral_Icc_div_sub' (K r β γ : ℝ) (hK : 0 ≤ K) (hγ : γ < r) (hβγ : β ≤ γ) :
    ∫⁻ y in Icc β γ, ENNReal.ofReal (K / (r - y)) =
      ENNReal.ofReal (K * Real.log ((r - β) / (r - γ))) := by
  have hcont : ContinuousOn (fun y => K / (r - y)) (Icc β γ) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_const.sub continuousOn_id)
    intro y hy; have := hy.2; simp only [Pi.sub_apply, id]; linarith
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hβγ,
      intervalIntegral.integral_comp_sub_left (fun x => K / x)]
    simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul]
    rw [integral_inv_of_pos (by linarith) (by linarith), div_eq_mul_inv]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact div_nonneg hK (by linarith [hy.2])


/-- **The hyperbola log.** On any interval of length `ℓ`,
`∫ min(A, K/|y - r|) dy ≤ 2K(1 + log(1 + ℓA/K))`, uniformly in the position of the
interval and of the singularity `r`. -/
theorem lintegral_min_div_abs_le (A K ℓ p r : ℝ) (hA : 0 < A) (hK : 0 < K) (hℓ : 0 ≤ ℓ) :
    ∫⁻ y in Icc p (p + ℓ), min (ENNReal.ofReal A) (ENNReal.ofReal K / ENNReal.ofReal |y - r|) ≤
      ENNReal.ofReal (2 * K * (1 + Real.log (1 + ℓ * A / K))) := by
  set f : ℝ → ENNReal := fun y => min (ENNReal.ofReal A) (ENNReal.ofReal K / ENNReal.ofReal |y - r|)
  set T := K / A with hTdef
  have hT : 0 < T := div_pos hK hA
  have hTA : T * A = K := by simp only [T]; field_simp
  have hlog0 : 0 ≤ Real.log (1 + ℓ * A / K) :=
    Real.log_nonneg (by have : 0 ≤ ℓ * A / K := by positivity
                        linarith)
  have hratio : ∀ u v : ℝ, T ≤ u → v ≤ u + ℓ → 0 < v →
      Real.log (v / u) ≤ Real.log (1 + ℓ * A / K) := by
    intro u v hu hv hv0
    have hu0 : 0 < u := lt_of_lt_of_le hT hu
    apply Real.log_le_log (div_pos hv0 hu0)
    rw [div_le_iff₀ hu0]
    have : ℓ * A / K * u ≥ ℓ := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hK]
      calc ℓ * K = ℓ * (T * A) := by rw [hTA]
        _ ≤ ℓ * A * u := by nlinarith [mul_le_mul_of_nonneg_left hu (mul_nonneg hℓ hA.le)]
    nlinarith
  -- the three pieces
  set β := max p (r + T)
  set γ := min (p + ℓ) (r - T)
  have hcover : Icc p (p + ℓ) ⊆ Icc (r - T) (r + T) ∪ (Icc β (p + ℓ) ∪ Icc p γ) := by
    intro y hy
    by_cases h1 : r + T < y
    · exact Or.inr (Or.inl ⟨max_le hy.1 h1.le, hy.2⟩)
    · by_cases h2 : y < r - T
      · exact Or.inr (Or.inr ⟨hy.1, le_min hy.2 h2.le⟩)
      · exact Or.inl ⟨by linarith, by linarith⟩
  have hp1 : ∫⁻ y in Icc (r - T) (r + T), f y ≤ ENNReal.ofReal (2 * K) := by
    calc ∫⁻ y in Icc (r - T) (r + T), f y ≤ ∫⁻ _ in Icc (r - T) (r + T), ENNReal.ofReal A :=
          setLIntegral_mono measurable_const (fun _ _ => min_le_left _ _)
      _ = ENNReal.ofReal (2 * K) := by
          rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul hA.le, ← hTA]
          congr 1; ring
  have hp2 : ∫⁻ y in Icc β (p + ℓ), f y ≤ ENNReal.ofReal (K * Real.log (1 + ℓ * A / K)) := by
    by_cases hβ : β ≤ p + ℓ
    · have hβr : r < β := by have := le_max_right p (r + T); linarith
      calc ∫⁻ y in Icc β (p + ℓ), f y ≤ ∫⁻ y in Icc β (p + ℓ), ENNReal.ofReal (K / (y - r)) := by
            refine setLIntegral_mono (by fun_prop) (fun y hy => (min_le_right _ _).trans ?_)
            have hy : 0 < y - r := by linarith [hy.1]
            rw [abs_of_pos hy, ENNReal.ofReal_div_of_pos hy]
        _ = ENNReal.ofReal (K * Real.log ((p + ℓ - r) / (β - r))) :=
            lintegral_Icc_div_sub K r β (p + ℓ) hK.le hβr hβ
        _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            apply mul_le_mul_of_nonneg_left _ hK.le
            apply hratio _ _ (by have := le_max_right p (r + T); linarith)
              (by have := le_max_left p (r + T); linarith) (by linarith)
    · rw [Icc_eq_empty hβ, Measure.restrict_empty, lintegral_zero_measure]; exact bot_le
  have hp3 : ∫⁻ y in Icc p γ, f y ≤ ENNReal.ofReal (K * Real.log (1 + ℓ * A / K)) := by
    by_cases hγ : p ≤ γ
    · have hγr : γ < r := by have := min_le_right (p + ℓ) (r - T); linarith
      calc ∫⁻ y in Icc p γ, f y ≤ ∫⁻ y in Icc p γ, ENNReal.ofReal (K / (r - y)) := by
            refine setLIntegral_mono (by fun_prop) (fun y hy => (min_le_right _ _).trans ?_)
            have hy : 0 < r - y := by linarith [hy.2]
            rw [abs_sub_comm, abs_of_pos hy, ENNReal.ofReal_div_of_pos hy]
        _ = ENNReal.ofReal (K * Real.log ((r - p) / (r - γ))) :=
            lintegral_Icc_div_sub' K r p γ hK.le hγr hγ
        _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            apply mul_le_mul_of_nonneg_left _ hK.le
            apply hratio _ _ (by have := min_le_right (p + ℓ) (r - T); linarith)
              (by have := min_le_left (p + ℓ) (r - T); linarith) (by linarith)
    · rw [Icc_eq_empty hγ, Measure.restrict_empty, lintegral_zero_measure]; exact bot_le
  calc ∫⁻ y in Icc p (p + ℓ), f y
      ≤ ∫⁻ y in Icc (r - T) (r + T) ∪ (Icc β (p + ℓ) ∪ Icc p γ), f y :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ y in Icc (r - T) (r + T), f y) +
          ((∫⁻ y in Icc β (p + ℓ), f y) + ∫⁻ y in Icc p γ, f y) :=
        (lintegral_union_le _ _ _).trans (add_le_add le_rfl (lintegral_union_le _ _ _))
    _ ≤ ENNReal.ofReal (2 * K) + (ENNReal.ofReal (K * Real.log (1 + ℓ * A / K)) +
          ENNReal.ofReal (K * Real.log (1 + ℓ * A / K))) :=
        add_le_add hp1 (add_le_add hp2 hp3)
    _ = _ := by
        have h0 : 0 ≤ K * Real.log (1 + ℓ * A / K) := mul_nonneg hK.le hlog0
        rw [← ENNReal.ofReal_add h0 h0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end VectorSLT
