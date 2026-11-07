/-
L6 stage 1: Lemma M3 (uniform integrability), decomposition §4.

With `E₀ = 1 + q³ + a³`: if `E` is continuous, `|E - E₀| ≤ 1/10` on `[-1,1]²`, and the
partial derivative in the named variable has `|·| ≥ 1` on each region below, then
`∫_{[-1,1]²} |q|^{-1/2} |a|^{-1/2} |E|^{-1/2} ≤ C` with an absolute constant `C`.
-/
import VectorSLT.SLT.InvSqrt

namespace VectorSLT

open MeasureTheory Set Filter VectorSLT.SLT

/-- The constant of Lemma M3. -/
noncomputable def M3const : ℝ := 16 * √5 + 64 * (7 / 10 : ℝ) ^ (-(1 / 2 : ℝ)) * √(3 / 10)

theorem lintegral_Icc_one_isqrt : ∫⁻ u in Icc (-1 : ℝ) 1, isqrt u ≤ ENNReal.ofReal 4 := by
  have := lintegral_Icc_isqrt (ℓ := 1) zero_le_one
  simpa using this

/-- The two outer intervals `[0.7,1] ∪ [-1,-0.7]`. -/
def outer7 : Set ℝ := Icc (7 / 10) 1 ∪ Icc (-1) (-(7 / 10))

theorem measurableSet_outer7 : MeasurableSet outer7 := measurableSet_Icc.union measurableSet_Icc

theorem abs_ge_of_outer7 {x : ℝ} (hx : x ∈ outer7) : 7 / 10 ≤ |x| := by
  rcases hx with h | h
  · rw [abs_of_pos (by linarith [h.1])]; exact h.1
  · rw [abs_of_neg (by linarith [h.2])]; linarith [h.2]

/-- Expansion `|f y - f x| ≥ |y - x|` on each of the two outer intervals. -/
def OuterExp (f : ℝ → ℝ) : Prop :=
  (∀ x ∈ Icc (7 / 10 : ℝ) 1, ∀ y ∈ Icc (7 / 10 : ℝ) 1, |y - x| ≤ |f y - f x|) ∧
  (∀ x ∈ Icc (-1 : ℝ) (-(7 / 10)), ∀ y ∈ Icc (-1 : ℝ) (-(7 / 10)), |y - x| ≤ |f y - f x|)

/-- `∫_{outer7} |f|^{-1/2} ≤ 8 √0.3` for `f` continuous on `[-1,1]` and expanding on the
outer intervals. -/
theorem lintegral_outer7_isqrt' {f : ℝ → ℝ} (hc : ContinuousOn f (Icc (-1) 1))
    (hx : OuterExp f) :
    ∫⁻ x in outer7, isqrt (f x) ≤ ENNReal.ofReal (8 * √(3 / 10)) := by
  have h1 := lintegral_isqrt_of_expand (f := f) (p := 7 / 10) (q := 1) (by norm_num)
    (hc.mono (Icc_subset_Icc (by norm_num) le_rfl)) hx.1
  have h2 := lintegral_isqrt_of_expand (f := f) (p := -1) (q := -(7 / 10)) (by norm_num)
    (hc.mono (Icc_subset_Icc le_rfl (by norm_num))) hx.2
  norm_num at h1 h2
  calc ∫⁻ x in outer7, isqrt (f x)
      ≤ (∫⁻ x in Icc (7 / 10) 1, isqrt (f x)) + ∫⁻ x in Icc (-1) (-(7 / 10)), isqrt (f x) :=
        lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (4 * √(3 / 10)) + ENNReal.ofReal (4 * √(3 / 10)) := by
        gcongr
        · convert h1 using 3; norm_num
        · convert h2 using 3; norm_num
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

theorem outerExp_of_deriv {f : ℝ → ℝ} (hc : ContinuousOn f (Icc (-1) 1))
    (hd : ∀ x, 7 / 10 < |x| → |x| < 1 → ∃ d, HasDerivAt f d x ∧ 1 ≤ |d|) : OuterExp f := by
  constructor
  · intro x hx y hy
    exact expand_of_deriv (hc.mono (Icc_subset_Icc (by norm_num) le_rfl))
      (fun z hz => hd z (by rw [abs_of_pos (by linarith [hz.1])]; exact hz.1)
        (by rw [abs_of_pos (by linarith [hz.1])]; exact hz.2)) hx hy
  · intro x hx y hy
    exact expand_of_deriv (hc.mono (Icc_subset_Icc le_rfl (by norm_num)))
      (fun z hz => hd z (by rw [abs_of_neg (by linarith [hz.2])]; linarith [hz.2])
        (by rw [abs_of_neg (by linarith [hz.2])]; linarith [hz.1])) hx hy

/-- **Lemma M3, core form.** The hypotheses are exactly what the proof consumes:
measurability, continuity on the relevant slices, closeness to `E₀`, and expansion
`|E(y) - E(x)| ≥ |y - x|` along the named variable on the outer intervals. -/
theorem lemmaM3_core (E : ℝ × ℝ → ℝ) (hEm : Measurable E)
    (hca : ∀ q, |q| ≤ 1 → ContinuousOn (fun a => E (q, a)) (Icc (-1) 1))
    (hcq : ∀ a, |a| < 7 / 10 → ContinuousOn (fun q => E (q, a)) (Icc (-1) 1))
    (hclose : ∀ q a : ℝ, |q| ≤ 1 → |a| ≤ 1 → |E (q, a) - (1 + q ^ 3 + a ^ 3)| ≤ 1 / 10)
    (hxa : ∀ q, |q| ≤ 1 → OuterExp fun a => E (q, a))
    (hxq : ∀ a, |a| < 7 / 10 → OuterExp fun q => E (q, a)) :
    ∫⁻ p in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, isqrt p.1 * isqrt p.2 * isqrt (E p) ≤
      ENNReal.ofReal M3const := by
  set H : ℝ × ℝ → ENNReal := fun p => isqrt p.1 * isqrt p.2 * isqrt (E p)
  have hHm : Measurable H := by
    have := measurable_isqrt
    exact ((this.comp measurable_fst).mul (this.comp measurable_snd)).mul
      (this.comp hEm)
  set c7 := (7 / 10 : ℝ) ^ (-(1 / 2 : ℝ))
  have hc7 : ∀ x : ℝ, 7 / 10 ≤ |x| → isqrt x ≤ ENNReal.ofReal c7 :=
    fun x hx => isqrt_le_of_le (by norm_num) hx
  set I1 := Ioo (-(7 / 10) : ℝ) (7 / 10)
  have hcover : Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ⊆
      (I1 ×ˢ I1) ∪ ((Icc (-1 : ℝ) 1 ×ˢ outer7) ∪ (outer7 ×ˢ I1)) := by
    rintro ⟨q, a⟩ ⟨hq, ha⟩
    by_cases hA : |a| < 7 / 10
    · have ha' : a ∈ I1 := ⟨by linarith [neg_abs_le a], by linarith [le_abs_self a]⟩
      by_cases hQ : |q| < 7 / 10
      · exact Or.inl ⟨⟨by linarith [neg_abs_le q], by linarith [le_abs_self q]⟩, ha'⟩
      · push Not at hQ
        refine Or.inr (Or.inr ⟨?_, ha'⟩)
        rcases le_total 0 q with h | h
        · left; rw [abs_of_nonneg h] at hQ; exact ⟨hQ, hq.2⟩
        · right; rw [abs_of_nonpos h] at hQ; exact ⟨hq.1, by linarith⟩
    · push Not at hA
      refine Or.inr (Or.inl ⟨hq, ?_⟩)
      rcases le_total 0 a with h | h
      · left; rw [abs_of_nonneg h] at hA; exact ⟨hA, ha.2⟩
      · right; rw [abs_of_nonpos h] at hA; exact ⟨ha.1, by linarith⟩
  -- region 1: |E| ≥ 1/5
  have hR1 : ∫⁻ p in I1 ×ˢ I1, H p ≤ ENNReal.ofReal (16 * √5) := by
    have hE5 : ∀ p ∈ I1 ×ˢ I1, isqrt (E p) ≤ ENNReal.ofReal √5 := by
      rintro ⟨q, a⟩ ⟨hq, ha⟩
      have hq3 : |q ^ 3| ≤ 343 / 1000 := by
        rw [abs_pow]
        have : |q| ≤ 7 / 10 := (abs_lt.mpr ⟨hq.1, hq.2⟩).le
        calc |q| ^ 3 ≤ (7 / 10) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) this 3
          _ = 343 / 1000 := by norm_num
      have ha3 : |a ^ 3| ≤ 343 / 1000 := by
        rw [abs_pow]
        have : |a| ≤ 7 / 10 := (abs_lt.mpr ⟨ha.1, ha.2⟩).le
        calc |a| ^ 3 ≤ (7 / 10) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) this 3
          _ = 343 / 1000 := by norm_num
      have hcl := hclose q a (by rw [abs_le]; constructor <;> linarith [hq.1, hq.2])
        (by rw [abs_le]; constructor <;> linarith [ha.1, ha.2])
      have hlow : 1 / 5 ≤ |E (q, a)| := by
        rw [abs_le] at hcl hq3 ha3
        rw [le_abs]; left; linarith [hcl.1, hq3.1, ha3.1]
      have := isqrt_le_of_le (x := E (q, a)) (by norm_num) hlow
      refine this.trans (le_of_eq ?_)
      congr 1
      rw [show (1 / 5 : ℝ) = 5⁻¹ by norm_num, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
        neg_neg, Real.sqrt_eq_rpow]
    calc ∫⁻ p in I1 ×ˢ I1, H p
        ≤ ∫⁻ p in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, isqrt p.1 * isqrt p.2 * ENNReal.ofReal √5 := by
          refine (setLIntegral_mono' (measurableSet_Ioo.prod measurableSet_Ioo) fun p hp => ?_).trans
            (lintegral_mono_set (prod_mono
              (Ioo_subset_Icc_self.trans (Icc_subset_Icc (by norm_num) (by norm_num)))
              (Ioo_subset_Icc_self.trans (Icc_subset_Icc (by norm_num) (by norm_num)))))
          show isqrt p.1 * isqrt p.2 * isqrt (E p) ≤ _
          gcongr; exact hE5 p hp
      _ = (∫⁻ q in Icc (-1 : ℝ) 1, isqrt q) * (∫⁻ a in Icc (-1 : ℝ) 1, isqrt a) *
            ENNReal.ofReal √5 := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, Measure.volume_eq_prod,
            ← Measure.prod_restrict, lintegral_prod_mul measurable_isqrt.aemeasurable
              measurable_isqrt.aemeasurable]
      _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal 4 * ENNReal.ofReal √5 := by
          gcongr <;> exact lintegral_Icc_one_isqrt
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]; ring_nf
  -- region 2: |a| ≥ 0.7, derivative in a
  have hR2 : ∫⁻ p in Icc (-1 : ℝ) 1 ×ˢ outer7, H p ≤
      ENNReal.ofReal (4 * (c7 * (8 * √(3 / 10)))) := by
    rw [Measure.volume_eq_prod, setLIntegral_prod H hHm.aemeasurable]
    calc ∫⁻ q in Icc (-1 : ℝ) 1, ∫⁻ a in outer7, H (q, a)
        ≤ ∫⁻ q in Icc (-1 : ℝ) 1, isqrt q * ENNReal.ofReal (c7 * (8 * √(3 / 10))) := by
          refine setLIntegral_mono' measurableSet_Icc fun q hq => ?_
          have hq1 : |q| ≤ 1 := abs_le.mpr hq
          calc ∫⁻ a in outer7, H (q, a)
              ≤ ∫⁻ a in outer7, isqrt q * ENNReal.ofReal c7 * isqrt (E (q, a)) :=
                setLIntegral_mono' measurableSet_outer7 fun a ha => by
                  show isqrt q * isqrt a * isqrt (E (q, a)) ≤ _
                  gcongr; exact hc7 a (abs_ge_of_outer7 ha)
            _ = isqrt q * ENNReal.ofReal c7 * ∫⁻ a in outer7, isqrt (E (q, a)) :=
                lintegral_const_mul _ (measurable_isqrt.comp
                  (hEm.comp (measurable_const.prodMk measurable_id)))
            _ ≤ _ := by
                rw [mul_assoc, ENNReal.ofReal_mul (by positivity)]
                gcongr
                exact lintegral_outer7_isqrt' (hca q hq1) (hxa q hq1)
      _ = (∫⁻ q in Icc (-1 : ℝ) 1, isqrt q) * ENNReal.ofReal (c7 * (8 * √(3 / 10))) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal (c7 * (8 * √(3 / 10))) := by
          gcongr; exact lintegral_Icc_one_isqrt
      _ = _ := (ENNReal.ofReal_mul (by norm_num)).symm
  -- region 3: |q| ≥ 0.7, |a| < 0.7, derivative in q (integrate q first)
  have hR3 : ∫⁻ p in outer7 ×ˢ I1, H p ≤ ENNReal.ofReal (4 * (c7 * (8 * √(3 / 10)))) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm H hHm.aemeasurable]
    calc ∫⁻ a in I1, ∫⁻ q in outer7, H (q, a)
        ≤ ∫⁻ a in I1, isqrt a * ENNReal.ofReal (c7 * (8 * √(3 / 10))) := by
          refine setLIntegral_mono' measurableSet_Ioo fun a ha => ?_
          have ha7 : |a| < 7 / 10 := abs_lt.mpr ⟨ha.1, ha.2⟩
          calc ∫⁻ q in outer7, H (q, a)
              ≤ ∫⁻ q in outer7, isqrt a * ENNReal.ofReal c7 * isqrt (E (q, a)) :=
                setLIntegral_mono' measurableSet_outer7 fun q hq => by
                  show isqrt q * isqrt a * isqrt (E (q, a)) ≤ _
                  rw [mul_comm (isqrt q)]
                  gcongr; exact hc7 q (abs_ge_of_outer7 hq)
            _ = isqrt a * ENNReal.ofReal c7 * ∫⁻ q in outer7, isqrt (E (q, a)) :=
                lintegral_const_mul _ (measurable_isqrt.comp
                  (hEm.comp (measurable_id.prodMk measurable_const)))
            _ ≤ _ := by
                rw [mul_assoc, ENNReal.ofReal_mul (by positivity)]
                gcongr
                exact lintegral_outer7_isqrt' (hcq a ha7) (hxq a ha7)
      _ = (∫⁻ a in I1, isqrt a) * ENNReal.ofReal (c7 * (8 * √(3 / 10))) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal (c7 * (8 * √(3 / 10))) := by
          gcongr
          exact (lintegral_mono_set (Ioo_subset_Icc_self.trans
            (Icc_subset_Icc (by norm_num) (by norm_num)))).trans lintegral_Icc_one_isqrt
      _ = _ := (ENNReal.ofReal_mul (by norm_num)).symm
  calc ∫⁻ p in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, H p
      ≤ (∫⁻ p in I1 ×ˢ I1, H p) + ((∫⁻ p in Icc (-1 : ℝ) 1 ×ˢ outer7, H p) +
          ∫⁻ p in outer7 ×ˢ I1, H p) :=
        (lintegral_mono_set hcover).trans
          ((lintegral_union_le _ _ _).trans (add_le_add le_rfl (lintegral_union_le _ _ _)))
    _ ≤ ENNReal.ofReal (16 * √5) + (ENNReal.ofReal (4 * (c7 * (8 * √(3 / 10)))) +
          ENNReal.ofReal (4 * (c7 * (8 * √(3 / 10))))) := add_le_add hR1 (add_le_add hR2 hR3)
    _ = ENNReal.ofReal M3const := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        unfold M3const; congr 1; ring

/-- **Lemma M3** (derivative form, as in stage 1). -/
theorem lemmaM3 (E : ℝ × ℝ → ℝ) (hE : Continuous E)
    (hclose : ∀ q a : ℝ, |q| ≤ 1 → |a| ≤ 1 → |E (q, a) - (1 + q ^ 3 + a ^ 3)| ≤ 1 / 10)
    (hda : ∀ q, |q| ≤ 1 → ∀ a, 7 / 10 < |a| → |a| < 1 →
      ∃ d, HasDerivAt (fun a' => E (q, a')) d a ∧ 1 ≤ |d|)
    (hdq : ∀ a, |a| < 7 / 10 → ∀ q, 7 / 10 < |q| → |q| < 1 →
      ∃ d, HasDerivAt (fun q' => E (q', a)) d q ∧ 1 ≤ |d|) :
    ∫⁻ p in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, isqrt p.1 * isqrt p.2 * isqrt (E p) ≤
      ENNReal.ofReal M3const :=
  lemmaM3_core E hE.measurable (fun q _ => (hE.comp (Continuous.prodMk_right q)).continuousOn)
    (fun a _ => (hE.comp (Continuous.prodMk_left a)).continuousOn) hclose
    (fun q hq => outerExp_of_deriv (hE.comp (Continuous.prodMk_right q)).continuousOn (hda q hq))
    (fun a ha => outerExp_of_deriv (hE.comp (Continuous.prodMk_left a)).continuousOn (hdq a ha))

end VectorSLT
