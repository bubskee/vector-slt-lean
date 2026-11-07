/-
L6 stage 1: integrals of `|f|^{-1/2}` (namespace `SLT`, Mathlib only).

`|·|^{-1/2}` is taken in `ℝ≥0∞`, so it is `∞` at zeros. The key 1-D fact (replacing the
paper's monotone substitution, decomposition M3.2): if `|f'| ≥ 1` on an interval, then `f`
expands distances, so `|f(x)| ≥ |x - m|` at a minimizer `m` of `|f|`, and
`∫_I |f|^{-1/2} ≤ 4 √|I|`.
-/
import VectorSLT.SLT.Toolkit
import VectorSLT.SLT.NormalCrossing

namespace SLT

open MeasureTheory Set Filter Real

/-- `x ↦ (ofReal |x|)^{-1/2}` in `ℝ≥0∞`. -/
noncomputable def isqrt (x : ℝ) : ENNReal := (ENNReal.ofReal |x|) ^ (-(1 / 2 : ℝ))

theorem measurable_isqrt : Measurable isqrt := by unfold isqrt; fun_prop

theorem isqrt_anti {x y : ℝ} (h : |x| ≤ |y|) : isqrt y ≤ isqrt x := by
  unfold isqrt
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h) (by norm_num))

theorem isqrt_le_of_le {x c : ℝ} (hc : 0 < c) (h : c ≤ |x|) :
    isqrt x ≤ ENNReal.ofReal (c ^ (-(1 / 2 : ℝ))) := by
  have := isqrt_anti (x := c) (y := x) (by rwa [abs_of_pos hc])
  unfold isqrt at this ⊢
  rwa [abs_of_pos hc, ENNReal.ofReal_rpow_of_pos hc] at this

theorem lintegral_Ioc_isqrt {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ∫⁻ u in Ioc 0 ℓ, isqrt u = ENNReal.ofReal (2 * √ℓ) := by
  rw [setLIntegral_congr_fun measurableSet_Ioc (fun u hu => by
      unfold isqrt; rw [abs_of_pos hu.1, ENNReal.ofReal_rpow_of_pos hu.1]),
    lintegral_Ioc_zero_rpow hℓ (by norm_num), Real.sqrt_eq_rpow]
  congr 1; norm_num; ring

/-- `∫_{[-ℓ,ℓ]} |u|^{-1/2} du = 4 √ℓ`. -/
theorem lintegral_Icc_isqrt {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ∫⁻ u in Icc (-ℓ) ℓ, isqrt u ≤ ENNReal.ofReal (4 * √ℓ) := by
  have hsub : Icc (-ℓ) ℓ ⊆ Icc (-ℓ) 0 ∪ Ioc 0 ℓ := by
    intro u hu
    rcases le_or_gt u 0 with h | h
    · exact Or.inl ⟨hu.1, h⟩
    · exact Or.inr ⟨h, hu.2⟩
  have hneg : ∫⁻ u in Icc (-ℓ) 0, isqrt u = ∫⁻ u in Icc 0 ℓ, isqrt u := by
    have hpt : ∀ u : ℝ, (Icc (-ℓ) 0).indicator isqrt u =
        (Icc 0 ℓ).indicator isqrt (-1 * u + 0) := by
      intro u
      have hi : isqrt (-1 * u + 0) = isqrt u := by
        unfold isqrt; rw [show -1 * u + 0 = -u by ring, abs_neg]
      have hiff : u ∈ Icc (-ℓ) 0 ↔ (-1 * u + 0) ∈ Icc 0 ℓ := by
        simp only [mem_Icc]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
      by_cases hu : u ∈ Icc (-ℓ) 0
      · rw [indicator_of_mem hu, indicator_of_mem (hiff.mp hu), hi]
      · rw [indicator_of_notMem hu, indicator_of_notMem (fun h => hu (hiff.mpr h))]
    rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Icc]
    simp_rw [hpt]
    rw [lintegral_comp_affine (measurable_isqrt.indicator measurableSet_Icc) (by norm_num)]
    simp
  have hIcc : ∫⁻ u in Icc 0 ℓ, isqrt u = ∫⁻ u in Ioc 0 ℓ, isqrt u :=
    setLIntegral_congr Ioc_ae_eq_Icc.symm
  calc ∫⁻ u in Icc (-ℓ) ℓ, isqrt u
      ≤ (∫⁻ u in Icc (-ℓ) 0, isqrt u) + ∫⁻ u in Ioc 0 ℓ, isqrt u :=
        (lintegral_mono_set hsub).trans (lintegral_union_le _ _ _)
    _ = ENNReal.ofReal (2 * √ℓ) + ENNReal.ofReal (2 * √ℓ) := by
        rw [hneg, hIcc, lintegral_Ioc_isqrt hℓ]
    _ = ENNReal.ofReal (4 * √ℓ) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

/-- `∫_{[p,q]} |x - m|^{-1/2} dx ≤ 4 √(q-p)` for `m ∈ [p,q]`. -/
theorem lintegral_isqrt_sub {p q m : ℝ} (hm : m ∈ Icc p q) :
    ∫⁻ x in Icc p q, isqrt (x - m) ≤ ENNReal.ofReal (4 * √(q - p)) := by
  set ℓ := q - p
  have hℓ : 0 ≤ ℓ := by simp only [ℓ]; linarith [hm.1, hm.2]
  have hsub : Icc p q ⊆ Icc (m - ℓ) (m + ℓ) := by
    intro x hx; constructor <;> simp only [ℓ] <;> linarith [hx.1, hx.2, hm.1, hm.2]
  have htr : ∫⁻ x in Icc (m - ℓ) (m + ℓ), isqrt (x - m) = ∫⁻ u in Icc (-ℓ) ℓ, isqrt u := by
    have h := lintegral_comp_affine (f := (Icc (-ℓ) ℓ).indicator isqrt)
      (measurable_isqrt.indicator measurableSet_Icc) (a := 1) one_ne_zero (-m)
    simp only [one_mul, inv_one, abs_one, ENNReal.ofReal_one] at h
    rw [lintegral_indicator measurableSet_Icc] at h
    rw [← h, ← lintegral_indicator measurableSet_Icc]
    congr 1; funext x
    simp only [Set.indicator, mem_Icc, ← sub_eq_add_neg]
    congr 1; apply propext; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  calc ∫⁻ x in Icc p q, isqrt (x - m) ≤ ∫⁻ x in Icc (m - ℓ) (m + ℓ), isqrt (x - m) :=
        lintegral_mono_set hsub
    _ = _ := htr
    _ ≤ _ := lintegral_Icc_isqrt hℓ

/-- **Expansion from `|f'| ≥ 1`**: `|f y - f x| ≥ |y - x|` on the interval. -/
theorem expand_of_deriv {f : ℝ → ℝ} {p q : ℝ} (hc : ContinuousOn f (Icc p q))
    (hd : ∀ x ∈ Ioo p q, ∃ d, HasDerivAt f d x ∧ 1 ≤ |d|) {x y : ℝ} (hx : x ∈ Icc p q)
    (hy : y ∈ Icc p q) : |y - x| ≤ |f y - f x| := by
  wlog hxy : x < y generalizing x y
  · rcases eq_or_lt_of_le (not_lt.mp hxy) with h | h
    · rw [h]; simp
    · rw [abs_sub_comm, abs_sub_comm (f y)]; exact this hy hx h
  choose! f' hf' hf'1 using hd
  obtain ⟨c, hc', hslope⟩ := exists_hasDerivAt_eq_slope f f' hxy
    (hc.mono (Icc_subset_Icc hx.1 hy.2))
    (fun z hz => hf' z ⟨lt_of_le_of_lt hx.1 hz.1, lt_of_lt_of_le hz.2 hy.2⟩)
  have hcI : c ∈ Ioo p q := ⟨lt_of_le_of_lt hx.1 hc'.1, lt_of_lt_of_le hc'.2 hy.2⟩
  have h1 := hf'1 c hcI
  have hyx : 0 < y - x := by linarith
  rw [hslope, abs_div, abs_of_pos hyx, le_div_iff₀ hyx] at h1
  rw [abs_of_pos hyx]; linarith

/-- **1-D bound, expansion form**: if `f` is continuous on `[p,q]` and expanding
(`|f y - f x| ≥ |y - x|`), then `∫_{[p,q]} |f|^{-1/2} ≤ 4 √(q-p)`, uniformly in `f`. -/
theorem lintegral_isqrt_of_expand {f : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hc : ContinuousOn f (Icc p q))
    (hexp' : ∀ x ∈ Icc p q, ∀ y ∈ Icc p q, |y - x| ≤ |f y - f x|) :
    ∫⁻ x in Icc p q, isqrt (f x) ≤ ENNReal.ofReal (4 * √(q - p)) := by
  obtain ⟨m, hm, hmin⟩ := (isCompact_Icc (a := p) (b := q)).exists_isMinOn
    (nonempty_Icc.mpr hpq) hc.abs
  have hkey : ∀ x ∈ Icc p q, |x - m| ≤ |f x| := by
    intro x hx
    have hexp := hexp' m hm x hx
    have hfm : |f m| ≤ |f x| := isMinOn_iff.mp hmin x hx
    -- `f x` and `f m` have the same sign (else a zero lies between, forcing `f m = 0`)
    by_cases hs : 0 ≤ f x * f m
    · refine hexp.trans ?_
      rcases le_total 0 (f x) with h1 | h1
      · rcases le_total 0 (f m) with h2 | h2
        · rw [abs_of_nonneg h1] at hfm ⊢; rw [abs_of_nonneg h2] at hfm
          rw [abs_le]; constructor <;> linarith
        · have : f x = 0 ∨ f m = 0 := by
            rcases eq_or_lt_of_le h1 with h | h
            · exact Or.inl h.symm
            · right; nlinarith
          rcases this with h | h
          · rw [h] at hfm ⊢; simp at hfm; rw [hfm]; simp
          · rw [h]; simp
      · rcases le_total 0 (f m) with h2 | h2
        · have : f x = 0 ∨ f m = 0 := by
            rcases eq_or_lt_of_le h2 with h | h
            · exact Or.inr h.symm
            · left; nlinarith
          rcases this with h | h
          · rw [h] at hfm ⊢; simp at hfm; rw [hfm]; simp
          · rw [h]; simp
        · rw [abs_of_nonpos h1] at hfm ⊢; rw [abs_of_nonpos h2] at hfm
          rw [abs_le]; constructor <;> linarith
    · exfalso
      push Not at hs
      have hsub : uIcc m x ⊆ Icc p q := uIcc_subset_Icc hm hx
      have h0 : (0 : ℝ) ∈ uIcc (f m) (f x) := by
        rcases lt_or_gt_of_ne (show f m ≠ 0 by intro h; rw [h] at hs; simp at hs) with h | h
        · have : 0 < f x := by nlinarith
          exact ⟨by simp [min_le_iff]; left; linarith, by simp [le_max_iff]; right; linarith⟩
        · have : f x < 0 := by nlinarith
          exact ⟨by simp [min_le_iff]; right; linarith, by simp [le_max_iff]; left; linarith⟩
      obtain ⟨z, hz, hfz⟩ := intermediate_value_uIcc (hc.mono hsub) h0
      have := isMinOn_iff.mp hmin z (hsub hz)
      simp only [hfz, abs_zero] at this
      have hm0 : f m = 0 := abs_nonpos_iff.mp this
      rw [hm0] at hs; simp at hs
  calc ∫⁻ x in Icc p q, isqrt (f x) ≤ ∫⁻ x in Icc p q, isqrt (x - m) :=
        setLIntegral_mono' measurableSet_Icc fun x hx => isqrt_anti (hkey x hx)
    _ ≤ _ := lintegral_isqrt_sub hm

/-- **1-D bound (M3.2)**: if `|f'| ≥ 1` on `(p,q)` and `f` is continuous on `[p,q]`, then
`∫_{[p,q]} |f|^{-1/2} ≤ 4 √(q-p)`, uniformly in `f`. -/
theorem lintegral_isqrt_comp_le {f : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hc : ContinuousOn f (Icc p q)) (hd : ∀ x ∈ Ioo p q, ∃ d, HasDerivAt f d x ∧ 1 ≤ |d|) :
    ∫⁻ x in Icc p q, isqrt (f x) ≤ ENNReal.ofReal (4 * √(q - p)) :=
  lintegral_isqrt_of_expand hpq hc fun _ hx _ hy => expand_of_deriv hc hd hx hy

end SLT
