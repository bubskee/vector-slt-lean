/-
L6 stage 3, M5: the amplitude integral of one row (Lemma M5 of `shear_position_one_exact.md`
§5, decomposition §5). Source pinned at cubic-chaos `103cdc7`.

Pivot-first chart `a = (a_p, (a_i, a_j))` with `|a_i|, |a_j| ≤ |a_p| ≤ ε`. On the chart at
radius `r = |a_p|`, scale `(a_i, a_j) = a_p (q, a')` (two 1-D linear substitutions, factor
`r²`), apply Lemma M3 in `(q, a')`, and finish with the radial split.
-/
import VectorSLT.LemmaM3
import VectorSLT.LemmaM4

namespace VectorSLT

open MeasureTheory Set Filter VectorSLT.SLT

/-! ### Helpers -/

/-- `∫_{[-|c|,|c|]} f = |c| ∫_{[-1,1]} f(c s) ds` for `c ≠ 0`. -/
theorem setLIntegral_Icc_scale {f : ℝ → ENNReal} (hf : Measurable f) {c : ℝ} (hc : c ≠ 0) :
    ∫⁻ t in Icc (-|c|) |c|, f t = ENNReal.ofReal |c| * ∫⁻ s in Icc (-1 : ℝ) 1, f (c * s) := by
  have hc0 : 0 < |c| := abs_pos.mpr hc
  have hpt : ∀ s : ℝ, (Icc (-|c|) |c|).indicator f (c * s + 0) =
      (Icc (-1 : ℝ) 1).indicator (fun s => f (c * s)) s := by
    intro s
    have hiff : c * s + 0 ∈ Icc (-|c|) |c| ↔ s ∈ Icc (-1 : ℝ) 1 := by
      rw [add_zero, mem_Icc, mem_Icc, ← abs_le, ← abs_le, abs_mul]
      constructor
      · intro h; exact (mul_le_iff_le_one_right hc0).mp h
      · intro h; exact (mul_le_iff_le_one_right hc0).mpr h
    by_cases hs : s ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem (hiff.mpr hs), indicator_of_mem hs, add_zero]
    · rw [indicator_of_notMem (fun h => hs (hiff.mp h)), indicator_of_notMem hs]
  have h := lintegral_comp_affine (f := (Icc (-|c|) |c|).indicator f)
    (hf.indicator measurableSet_Icc) hc 0
  simp_rw [hpt] at h
  rw [lintegral_indicator measurableSet_Icc, lintegral_indicator measurableSet_Icc] at h
  rw [h, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, mul_inv_cancel₀ hc0.ne',
    ENNReal.ofReal_one, one_mul]

theorem isqrt_pos (x : ℝ) : 0 < isqrt x := by
  unfold isqrt
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ENNReal.zero_rpow_of_neg (by norm_num : -(1 / 2 : ℝ) < 0)]
  · exact ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (abs_pos.mpr hx)) ENNReal.ofReal_ne_top

/-- `|xy|^{-1/2} = |x|^{-1/2} |y|^{-1/2}` in `ℝ≥0∞` (with `0^{-1/2} = ∞`). -/
theorem isqrt_mul (x y : ℝ) : isqrt (x * y) = isqrt x * isqrt y := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_mul, isqrt_zero, ENNReal.top_mul (isqrt_pos y).ne']
  rcases eq_or_ne y 0 with rfl | hy
  · rw [mul_zero, isqrt_zero, ENNReal.mul_top (isqrt_pos x).ne']
  unfold isqrt
  rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _), ENNReal.mul_rpow_of_ne_zero
    (ENNReal.ofReal_pos.mpr (abs_pos.mpr hx)).ne' (ENNReal.ofReal_pos.mpr (abs_pos.mpr hy)).ne']

/-- The hypotheses of Lemma M3 on a function `E` of `(q, a')`. -/
def M3Hyp (E : ℝ × ℝ → ℝ) : Prop :=
  Continuous E ∧
  (∀ q a : ℝ, |q| ≤ 1 → |a| ≤ 1 → |E (q, a) - (1 + q ^ 3 + a ^ 3)| ≤ 1 / 10) ∧
  (∀ q, |q| ≤ 1 → ∀ a, 7 / 10 < |a| → |a| < 1 →
    ∃ d, HasDerivAt (fun a' => E (q, a')) d a ∧ 1 ≤ |d|) ∧
  (∀ a, |a| < 7 / 10 → ∀ q, 7 / 10 < |q| → |q| < 1 →
    ∃ d, HasDerivAt (fun q' => E (q', a)) d q ∧ 1 ≤ |d|)

/-- Lemma M3's conclusion as a predicate (any `E` it applies to). -/
def M3Int (E : ℝ × ℝ → ℝ) : Prop :=
  ∫⁻ p in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, isqrt p.1 * isqrt p.2 * isqrt (E p) ≤
    ENNReal.ofReal M3const

theorem M3Hyp.int {E : ℝ × ℝ → ℝ} (hE : M3Hyp E) : M3Int E := by
  obtain ⟨hEc, hcl, hda, hdq⟩ := hE
  exact lemmaM3 E hEc hcl hda hdq

/-- **Inner square bound (M5.1 + M5.2)**: on the chart at radius `r = |a_p|`, if
`D(a_p q, a_p a') = q a' E(q, a')` with `E` satisfying Lemma M3's conclusion (`M3Int`), then
`∫_{[-r,r]²} |D|^{-1/2} ≤ r² · C_{M3}`. -/
theorem inner_bound {ap : ℝ} (hap : ap ≠ 0) (Dfun : ℝ × ℝ → ℝ) (hDm : Measurable Dfun)
    (E : ℝ × ℝ → ℝ) (hM3 : M3Int E)
    (hDE : ∀ q a' : ℝ, |q| ≤ 1 → |a'| ≤ 1 → Dfun (ap * q, ap * a') = q * a' * E (q, a')) :
    ∫⁻ x in Icc (-|ap|) |ap| ×ˢ Icc (-|ap|) |ap|, isqrt (Dfun x) ≤
      ENNReal.ofReal (ap ^ 2 * M3const) := by
  have hm : Measurable fun x : ℝ × ℝ => isqrt (Dfun x) := measurable_isqrt.comp hDm
  rw [Measure.volume_eq_prod, setLIntegral_prod _ hm.aemeasurable]
  have hin : ∀ ai : ℝ, ∫⁻ aj in Icc (-|ap|) |ap|, isqrt (Dfun (ai, aj)) =
      ENNReal.ofReal |ap| * ∫⁻ a' in Icc (-1 : ℝ) 1, isqrt (Dfun (ai, ap * a')) :=
    fun ai => setLIntegral_Icc_scale (hm.comp (measurable_const.prodMk measurable_id)) hap
  simp_rw [hin]
  have hgm : Measurable fun ai : ℝ => ∫⁻ a' in Icc (-1 : ℝ) 1, isqrt (Dfun (ai, ap * a')) :=
    (hm.comp (measurable_fst.prodMk (measurable_const.mul measurable_snd))).lintegral_prod_right'
  rw [lintegral_const_mul _ hgm, setLIntegral_Icc_scale hgm hap, ← mul_assoc,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  -- back to a product integral over [-1,1]² and Lemma M3
  have hprod : ∫⁻ q in Icc (-1 : ℝ) 1, ∫⁻ a' in Icc (-1 : ℝ) 1, isqrt (Dfun (ap * q, ap * a')) =
      ∫⁻ p in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, isqrt (Dfun (ap * p.1, ap * p.2)) := by
    have hmm : Measurable fun p : ℝ × ℝ => isqrt (Dfun (ap * p.1, ap * p.2)) :=
      hm.comp ((measurable_const.mul measurable_fst).prodMk (measurable_const.mul measurable_snd))
    rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ),
      setLIntegral_prod (fun p : ℝ × ℝ => isqrt (Dfun (ap * p.1, ap * p.2))) hmm.aemeasurable]
  rw [hprod]
  have hcong : ∫⁻ p in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, isqrt (Dfun (ap * p.1, ap * p.2)) =
      ∫⁻ p in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, isqrt p.1 * isqrt p.2 * isqrt (E p) := by
    refine setLIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) fun p hp => ?_
    rw [hDE p.1 p.2 (abs_le.mpr hp.1) (abs_le.mpr hp.2), isqrt_mul, isqrt_mul]
  rw [hcong]
  calc ENNReal.ofReal (|ap| * |ap|) *
        ∫⁻ p in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, isqrt p.1 * isqrt p.2 * isqrt (E p)
      ≤ ENNReal.ofReal (|ap| * |ap|) * ENNReal.ofReal M3const := by gcongr; exact hM3
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← abs_mul, ← sq, abs_of_nonneg (sq_nonneg _)]

/-- An even function on `[-ε,ε]`: `∫ ≤ 2 ∫_{(0,ε]}`. -/
theorem setLIntegral_Icc_even_le {h : ℝ → ENNReal} (hm : Measurable h) (heven : ∀ t, h (-t) = h t)
    {ε : ℝ} (hε : 0 ≤ ε) : ∫⁻ t in Icc (-ε) ε, h t ≤ 2 * ∫⁻ t in Ioc 0 ε, h t := by
  have hsub : Icc (-ε) ε ⊆ Icc (-ε) 0 ∪ Ioc 0 ε := by
    intro u hu
    rcases le_or_gt u 0 with h' | h'
    · exact Or.inl ⟨hu.1, h'⟩
    · exact Or.inr ⟨h', hu.2⟩
  have hneg : ∫⁻ u in Icc (-ε) 0, h u = ∫⁻ u in Icc 0 ε, h u := by
    have hpt : ∀ u : ℝ, (Icc (-ε) 0).indicator h u = (Icc 0 ε).indicator h (-1 * u + 0) := by
      intro u
      have hi : h (-1 * u + 0) = h u := by rw [show -1 * u + 0 = -u by ring, heven]
      have hiff : u ∈ Icc (-ε) 0 ↔ (-1 * u + 0) ∈ Icc 0 ε := by
        simp only [mem_Icc]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
      by_cases hu : u ∈ Icc (-ε) 0
      · rw [indicator_of_mem hu, indicator_of_mem (hiff.mp hu), hi]
      · rw [indicator_of_notMem hu, indicator_of_notMem (fun h => hu (hiff.mpr h))]
    rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Icc]
    simp_rw [hpt]
    rw [lintegral_comp_affine (hm.indicator measurableSet_Icc) (by norm_num)]
    simp
  have hIcc : ∫⁻ u in Icc 0 ε, h u = ∫⁻ u in Ioc 0 ε, h u := setLIntegral_congr Ioc_ae_eq_Icc.symm
  calc ∫⁻ t in Icc (-ε) ε, h t ≤ (∫⁻ u in Icc (-ε) 0, h u) + ∫⁻ u in Ioc 0 ε, h u :=
        (lintegral_mono_set hsub).trans (lintegral_union_le _ _ _)
    _ = 2 * ∫⁻ t in Ioc 0 ε, h t := by rw [hneg, hIcc, two_mul]

/-- The pivot-first chart region `|a_i|, |a_j| ≤ |a_p| ≤ ε`. -/
def pivotRegion (ε : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  {a | |a.1| ≤ ε ∧ |a.2.1| ≤ |a.1| ∧ |a.2.2| ≤ |a.1|}

theorem measurableSet_pivotRegion (ε : ℝ) : MeasurableSet (pivotRegion ε) := by
  unfold pivotRegion; simp only [ofPred_and]
  refine (measurableSet_le (by fun_prop) measurable_const).inter
    ((measurableSet_le (by fun_prop) (by fun_prop)).inter (measurableSet_le (by fun_prop) (by fun_prop)))

/-- The M5 constant. -/
noncomputable def CM5 (ε B : ℝ) : ℝ :=
  4 * (B * M3const) * (2 / 3 + Real.posLog (ε * (32 * ε ^ 3 / (B * M3const)) ^ ((1 : ℝ) / 3)))

theorem M3const_pos : 0 < M3const := by unfold M3const; positivity

/-- **Lemma M5** (one row, pivot-first chart). Let `D` be measurable, and on each chart radius
`0 < |a_p| ≤ ε` write `D(a_p, a_p q, a_p a') = q a' E(q, a')` with `E` satisfying Lemma M3's
hypotheses. Then for `N ≥ e`
`∫_{chart} min{(2ε)³, B N⁻¹ |a_p|⁻³ (1+log N) |D|^{-1/2}} da ≤ C N⁻¹ (log N)²`. -/
theorem lemmaM5 {ε N B : ℝ} (hε : 0 < ε) (hN : Real.exp 1 ≤ N) (hB : 0 < B)
    (Dfun : ℝ × (ℝ × ℝ) → ℝ) (hDm : Measurable Dfun)
    (hD : ∀ ap : ℝ, ap ≠ 0 → |ap| ≤ ε → ∃ E : ℝ × ℝ → ℝ, M3Int E ∧
      ∀ q a' : ℝ, |q| ≤ 1 → |a'| ≤ 1 → Dfun (ap, (ap * q, ap * a')) = q * a' * E (q, a')) :
    ∫⁻ a in pivotRegion ε, min (ENNReal.ofReal ((2 * ε) ^ 3))
      (ENNReal.ofReal (B * N⁻¹ * |a.1|⁻¹ ^ 3 * (1 + Real.log N)) * isqrt (Dfun a)) ≤
      ENNReal.ofReal (CM5 ε B * N⁻¹ * Real.log N ^ 2) := by
  have hN1 : 1 ≤ N := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hN
  have hN0 : 0 < N := by linarith
  have hl1 : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hN
  have hM3 := M3const_pos
  set B' := B * M3const * N⁻¹ * (1 + Real.log N)
  have hB' : 0 < B' := by positivity
  set F : ℝ × (ℝ × ℝ) → ENNReal := fun a => min (ENNReal.ofReal ((2 * ε) ^ 3))
    (ENNReal.ofReal (B * N⁻¹ * |a.1|⁻¹ ^ 3 * (1 + Real.log N)) * isqrt (Dfun a))
  have hFm : Measurable F := by
    simp only [F]
    exact measurable_const.min ((ENNReal.measurable_ofReal.comp (by fun_prop)).mul
      (measurable_isqrt.comp hDm))
  set g : ℝ → ENNReal := fun t =>
    min (ENNReal.ofReal (32 * ε ^ 3 * t ^ 2)) (ENNReal.ofReal (B' / |t|))
  -- slice bound
  have hslice : ∀ ap : ℝ, ∫⁻ x, (pivotRegion ε).indicator F (ap, x) ≤
      (Icc (-ε) ε).indicator g ap := by
    intro ap
    by_cases hap : |ap| ≤ ε
    · rw [indicator_of_mem (show ap ∈ Icc (-ε) ε from abs_le.mp hap)]
      have hsl : (fun x => (pivotRegion ε).indicator F (ap, x)) =
          (Icc (-|ap|) |ap| ×ˢ Icc (-|ap|) |ap|).indicator (fun x => F (ap, x)) := by
        funext x
        by_cases hx : x ∈ Icc (-|ap|) |ap| ×ˢ Icc (-|ap|) |ap|
        · rw [indicator_of_mem hx, indicator_of_mem
            (show (ap, x) ∈ pivotRegion ε from ⟨hap, abs_le.mpr hx.1, abs_le.mpr hx.2⟩)]
        · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx
            ⟨abs_le.mp h.2.1, abs_le.mp h.2.2⟩)]
      rw [hsl, lintegral_indicator (measurableSet_Icc.prod measurableSet_Icc)]
      rcases eq_or_ne ap 0 with h0 | h0
      · subst h0
        have : volume (Icc (-|(0:ℝ)|) |0| ×ˢ Icc (-|(0:ℝ)|) |0|) = 0 := by
          rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
        rw [setLIntegral_measure_zero _ _ this]; exact bot_le
      · obtain ⟨E, hE, hDE⟩ := hD ap h0 hap
        have hap0 : 0 < |ap| := abs_pos.mpr h0
        have hin := inner_bound h0 (fun x => Dfun (ap, x)) (hDm.comp measurable_prodMk_left) E hE
          (fun q a' hq ha => hDE q a' hq ha)
        refine le_min ?_ ?_
        · calc ∫⁻ x in Icc (-|ap|) |ap| ×ˢ Icc (-|ap|) |ap|, F (ap, x)
              ≤ ∫⁻ x in Icc (-|ap|) |ap| ×ˢ Icc (-|ap|) |ap|, ENNReal.ofReal ((2 * ε) ^ 3) :=
                lintegral_mono fun x => min_le_left _ _
            _ = ENNReal.ofReal (32 * ε ^ 3 * ap ^ 2) := by
                rw [setLIntegral_const, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
                  ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by positivity)]
                congr 1; rw [← sq_abs ap]; ring
        · calc ∫⁻ x in Icc (-|ap|) |ap| ×ˢ Icc (-|ap|) |ap|, F (ap, x)
              ≤ ∫⁻ x in Icc (-|ap|) |ap| ×ˢ Icc (-|ap|) |ap|,
                  ENNReal.ofReal (B * N⁻¹ * |ap|⁻¹ ^ 3 * (1 + Real.log N)) * isqrt (Dfun (ap, x)) :=
                lintegral_mono fun x => min_le_right _ _
            _ = ENNReal.ofReal (B * N⁻¹ * |ap|⁻¹ ^ 3 * (1 + Real.log N)) *
                  ∫⁻ x in Icc (-|ap|) |ap| ×ˢ Icc (-|ap|) |ap|, isqrt (Dfun (ap, x)) :=
                lintegral_const_mul _ (measurable_isqrt.comp (hDm.comp measurable_prodMk_left))
            _ ≤ ENNReal.ofReal (B * N⁻¹ * |ap|⁻¹ ^ 3 * (1 + Real.log N)) *
                  ENNReal.ofReal (ap ^ 2 * M3const) := by gcongr
            _ = ENNReal.ofReal (B' / |ap|) := by
                rw [← ENNReal.ofReal_mul (by positivity)]
                congr 1; simp only [B']; rw [← sq_abs ap]; field_simp
    · rw [indicator_of_notMem (show ap ∉ Icc (-ε) ε from fun h => hap (abs_le.mpr h))]
      have : (fun x => (pivotRegion ε).indicator F (ap, x)) = 0 := by
        funext x; exact indicator_of_notMem (fun h => hap h.1) _
      rw [this]; exact (lintegral_zero_fun (μ := volume)).le
  -- integrate over `a_p`
  rw [← lintegral_indicator (measurableSet_pivotRegion ε), Measure.volume_eq_prod,
    lintegral_prod _ (hFm.indicator (measurableSet_pivotRegion ε)).aemeasurable]
  have hgm : Measurable g := by simp only [g]; fun_prop
  refine (lintegral_mono hslice).trans ?_
  rw [lintegral_indicator measurableSet_Icc]
  refine (setLIntegral_Icc_even_le hgm (fun t => by simp [g, abs_neg]) hε.le).trans ?_
  have hpos : ∀ t ∈ Ioc (0 : ℝ) ε, g t = min (ENNReal.ofReal (32 * ε ^ 3 * t ^ 2))
      (ENNReal.ofReal (B' / t)) := fun t ht => by simp only [g, abs_of_pos ht.1]
  rw [setLIntegral_congr_fun measurableSet_Ioc hpos]
  have hmin := lintegral_min_rsq_inv (A := 32 * ε ^ 3) (by positivity) hB' hε
  refine (mul_le_mul' (le_refl (2 : ENNReal)) hmin).trans ?_
  rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  set K0 := Real.posLog (ε * (32 * ε ^ 3 / (B * M3const)) ^ ((1 : ℝ) / 3))
  have hK0 : 0 ≤ K0 := Real.posLog_nonneg
  have hL0 : 0 < 1 + Real.log N := by linarith
  have hsplit : ε * (32 * ε ^ 3 / B') ^ ((1 : ℝ) / 3) =
      ε * (32 * ε ^ 3 / (B * M3const)) ^ ((1 : ℝ) / 3) * (N / (1 + Real.log N)) ^ ((1 : ℝ) / 3) := by
    rw [mul_assoc, ← Real.mul_rpow (by positivity) (by positivity)]
    congr 2; simp only [B']; field_simp
  have hNl : Real.posLog ((N / (1 + Real.log N)) ^ ((1 : ℝ) / 3)) ≤ 1 / 3 * Real.log N := by
    have hle : (N / (1 + Real.log N)) ^ ((1 : ℝ) / 3) ≤ N ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow (by positivity) (div_le_self hN0.le (by linarith)) (by norm_num)
    have hge : 0 ≤ (N / (1 + Real.log N)) ^ ((1 : ℝ) / 3) := by positivity
    calc Real.posLog ((N / (1 + Real.log N)) ^ ((1 : ℝ) / 3))
        ≤ Real.posLog (N ^ ((1 : ℝ) / 3)) := Real.posLog_le_posLog (by linarith) hle
      _ = 1 / 3 * Real.log N := by
          have h1 : 1 ≤ |N ^ ((1 : ℝ) / 3)| := by
            rw [abs_of_nonneg (by positivity)]; exact Real.one_le_rpow hN1 (by norm_num)
          rw [Real.posLog_eq_log h1, Real.log_rpow hN0]
  have hbr : 1 / 3 + Real.posLog (ε * (32 * ε ^ 3 / B') ^ ((1 : ℝ) / 3)) ≤
      (2 / 3 + K0) * Real.log N := by
    rw [hsplit]
    have := (Real.posLog_mul (x := ε * (32 * ε ^ 3 / (B * M3const)) ^ ((1 : ℝ) / 3))
      (y := (N / (1 + Real.log N)) ^ ((1 : ℝ) / 3)))
    nlinarith
  have hB'le : B' ≤ 2 * (B * M3const) * N⁻¹ * Real.log N := by
    simp only [B']
    have : 0 ≤ B * M3const * N⁻¹ := by positivity
    nlinarith
  have hbr0 : 0 ≤ 1 / 3 + Real.posLog (ε * (32 * ε ^ 3 / B') ^ ((1 : ℝ) / 3)) := by
    have := Real.posLog_nonneg (x := ε * (32 * ε ^ 3 / B') ^ ((1 : ℝ) / 3)); linarith
  calc 2 * (B' * (1 / 3 + Real.posLog (ε * (32 * ε ^ 3 / B') ^ ((1 : ℝ) / 3))))
      ≤ 2 * ((2 * (B * M3const) * N⁻¹ * Real.log N) * ((2 / 3 + K0) * Real.log N)) := by
        gcongr
    _ = CM5 ε B * N⁻¹ * Real.log N ^ 2 := by unfold CM5; ring

end VectorSLT
