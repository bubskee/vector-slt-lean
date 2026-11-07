/-
L6 stage 3, F4 + F5 (one row, pivot first): Lemma M4 at every amplitude point,
Lemma M3 for the (M9) `E` built from amplitude-dependent weights, and Lemma M5.

The weights `y_p, y_i, y_j, γ` are arbitrary measurable functions of the amplitude vector
that are `1/20`-close to `1` on the box and change by `O(ε³)` along every "cube-Lipschitz"
curve (`WOK`, `WDOK`). These are exactly the properties the explicit (M6) weights have
(`RowBound.lean`).
-/
import VectorSLT.ChartLip

namespace VectorSLT

open MeasureTheory Set VectorSLT.SLT

/-- Amplitude vectors, pivot first: `(a_p, (a_i, a_j))`. -/
abbrev T3 := ℝ × ℝ × ℝ

/-- A coordinate along a curve: bounded by `ε`, and its cube is `3ε³`-Lipschitz. -/
def coordOK (ε : ℝ) (f : ℝ → ℝ) : Prop :=
  (∀ x ∈ Icc (-1 : ℝ) 1, |f x| ≤ ε) ∧
    ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1, |f y ^ 3 - f x ^ 3| ≤ 3 * ε ^ 3 * |y - x|

theorem coordOK.cube {ε : ℝ} {f : ℝ → ℝ} (h : coordOK ε f) :
    LB (fun x => f x ^ 3) (Icc (-1) 1) (ε ^ 3) (3 * ε ^ 3) :=
  ⟨fun x hx => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (h.1 x hx) 3, h.2⟩

theorem coordOK_const {a ε : ℝ} (ha : |a| ≤ ε) : coordOK ε fun _ => a :=
  ⟨fun _ _ => ha, fun x _ y _ => by
    have : 0 ≤ ε := (abs_nonneg _).trans ha
    simp only [sub_self, abs_zero]; positivity⟩

theorem coordOK_scale {ap ε : ℝ} (hap : |ap| ≤ ε) : coordOK ε fun x => ap * x := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [abs_mul]
    calc |ap| * |x| ≤ ε * 1 := mul_le_mul hap (abs_le.mpr hx) (abs_nonneg _)
          ((abs_nonneg _).trans hap)
      _ = ε := mul_one ε
  · have hc := (LB.cube (S := Icc (-1 : ℝ) 1) subset_rfl).2 x hx y hy
    have hε0 : 0 ≤ ε := (abs_nonneg _).trans hap
    rw [show (ap * y) ^ 3 - (ap * x) ^ 3 = ap ^ 3 * (y ^ 3 - x ^ 3) by ring, abs_mul, abs_pow]
    calc |ap| ^ 3 * |y ^ 3 - x ^ 3| ≤ ε ^ 3 * (3 * |y - x|) :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hap 3) hc (abs_nonneg _) (by positivity)
      _ = 3 * ε ^ 3 * |y - x| := by ring

/-- A cube-Lipschitz curve in the amplitude box. -/
def CurveOK (ε : ℝ) (A : ℝ → T3) : Prop :=
  coordOK ε (fun x => (A x).1) ∧ coordOK ε (fun x => (A x).2.1) ∧ coordOK ε (fun x => (A x).2.2)

/-- The amplitude box `[-ε,ε]³`. -/
def box3 (ε : ℝ) : Set T3 := {a | |a.1| ≤ ε ∧ |a.2.1| ≤ ε ∧ |a.2.2| ≤ ε}

theorem CurveOK.mem {ε : ℝ} {A : ℝ → T3} (h : CurveOK ε A) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    A x ∈ box3 ε :=
  ⟨h.1.1 x hx, h.2.1.1 x hx, h.2.2.1 x hx⟩

/-- A weight: `1/20`-close to `1` on the box, `O(ε³)`-Lipschitz along curves. -/
def WOK (ε : ℝ) (w : T3 → ℝ) : Prop :=
  (∀ a ∈ box3 ε, |w a - 1| ≤ 1 / 20) ∧
    ∀ A, CurveOK ε A → LB (fun x => w (A x)) (Icc (-1) 1) (21 / 20) (18 * ε ^ 3)

/-- Two weights whose difference is `O(ε³)` (the constant `c` cancels). -/
def WDOK (ε : ℝ) (w w' : T3 → ℝ) : Prop :=
  ∀ A, CurveOK ε A → LB (fun x => w (A x) - w' (A x)) (Icc (-1) 1) (6 * ε ^ 3) (18 * ε ^ 3)

theorem WOK.ge {ε : ℝ} {w : T3 → ℝ} (h : WOK ε w) {a : T3} (ha : a ∈ box3 ε) :
    19 / 20 ≤ |w a| := by
  have := h.1 a ha
  rw [abs_le] at this
  rw [abs_of_pos (by linarith)]; linarith

theorem eps3_le {ε : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 1 / 20) : ε ^ 3 ≤ 1 / 8000 := by
  calc ε ^ 3 ≤ (1 / 20) ^ 3 := pow_le_pow_left₀ hε.le hε20 3
    _ = 1 / 8000 := by norm_num

/-- The chart ratio `u - 1 = (y_i - y_p)/y_p` is `1/100`-small and Lipschitz. -/
theorem ratio_LB {ε : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 1 / 20) {yP yI : T3 → ℝ} (hP : WOK ε yP)
    (hIP : WDOK ε yI yP) {A : ℝ → T3} (hA : CurveOK ε A) :
    LB (fun x => (yI (A x) - yP (A x)) / yP (A x)) (Icc (-1) 1) (1 / 100) (1 / 100) := by
  have h := (hIP A hA).div (hP.2 A hA) (by norm_num : (0 : ℝ) < 19 / 20)
    (fun x hx => hP.ge (hA.mem hx))
  have e3 := eps3_le hε hε20
  have e0 : 0 ≤ ε ^ 3 := by positivity
  refine h.mono ?_ ?_
  · rw [div_le_iff₀ (by norm_num)]; nlinarith
  · have : 6 * ε ^ 3 * (18 * ε ^ 3) ≤ 6 * (1 / 8000) * (18 * (1 / 8000)) := by gcongr
    rw [div_add_div _ _ (by norm_num) (by norm_num), div_le_iff₀ (by norm_num)]
    nlinarith

/-- The chart coefficient `c = a_p³/γ` is `1/100`-small and Lipschitz. -/
theorem coef_LB {ε : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 1 / 20) {γ : T3 → ℝ} (hγ : WOK ε γ)
    {ap : ℝ} (hap : |ap| ≤ ε) {A : ℝ → T3} (hA : CurveOK ε A) :
    LB (fun x => ap ^ 3 / γ (A x)) (Icc (-1) 1) (1 / 100) (1 / 100) := by
  have hap3 : |ap ^ 3| ≤ ε ^ 3 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hap 3
  have h := (LB.const' (S := Icc (-1 : ℝ) 1) hap3).div (hγ.2 A hA)
    (by norm_num : (0 : ℝ) < 19 / 20) (fun x hx => hγ.ge (hA.mem hx))
  have e3 := eps3_le hε hε20
  have e0 : 0 ≤ ε ^ 3 := by positivity
  refine h.mono ?_ ?_
  · rw [div_le_iff₀ (by norm_num)]; nlinarith
  · have : ε ^ 3 * (18 * ε ^ 3) ≤ (1 / 8000) * (18 * (1 / 8000)) := by gcongr
    rw [zero_div, zero_add, div_le_iff₀ (by norm_num)]
    nlinarith

/-- The (M9) `E` of the chart at radius `a_p`, as a function of `(q, a')`. -/
noncomputable def Echart (yP yI yJ γ : T3 → ℝ) (ap : ℝ) (p : ℝ × ℝ) : ℝ :=
  EM9 p.1 p.2 (yI (ap, (ap * p.1, ap * p.2)) / yP (ap, (ap * p.1, ap * p.2)))
    (yJ (ap, (ap * p.1, ap * p.2)) / yP (ap, (ap * p.1, ap * p.2)))
    (ap ^ 3 / γ (ap, (ap * p.1, ap * p.2)))

theorem ratio_eq {yP yI : ℝ} (h : yP ≠ 0) : yI / yP = 1 + (yI - yP) / yP := by
  field_simp; ring

/-- **F4: Lemma M3 holds for the chart `E` of (M9)**, uniformly in `a_p`. -/
theorem m3Int_Echart {ε : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 1 / 20) {yP yI yJ γ : T3 → ℝ}
    (hmP : Measurable yP) (hmI : Measurable yI) (hmJ : Measurable yJ) (hmγ : Measurable γ)
    (hP : WOK ε yP) (hγ : WOK ε γ) (hIP : WDOK ε yI yP) (hJP : WDOK ε yJ yP)
    {ap : ℝ} (hap : |ap| ≤ ε) : M3Int (Echart yP yI yJ γ ap) := by
  have hpt : Measurable fun p : ℝ × ℝ => ((ap, (ap * p.1, ap * p.2)) : T3) := by fun_prop
  have hEm : Measurable (Echart yP yI yJ γ ap) := by
    unfold Echart EM9
    have h1 := hmI.comp hpt
    have h2 := hmJ.comp hpt
    have h3 := hmP.comp hpt
    have h4 := hmγ.comp hpt
    simp only [Function.comp_def] at h1 h2 h3 h4
    fun_prop
  have hq1 : ∀ q : ℝ, |q| ≤ 1 → |ap * q| ≤ ε := fun q hq => by
    rw [abs_mul]; nlinarith [abs_nonneg ap, abs_nonneg q]
  refine m3Int_of_LB _ hEm (fun q hq => ?_) (fun a ha => ?_)
  · -- moving `a'`
    have hA : CurveOK ε fun x => ((ap, (ap * q, ap * x)) : T3) :=
      ⟨coordOK_const hap, coordOK_const (hq1 q hq), coordOK_scale hap⟩
    have key := EM9_pert (S := Icc (-1 : ℝ) 1) subset_rfl hq (ratio_LB hε hε20 hP hIP hA)
      (ratio_LB hε hε20 hP hJP hA) (coef_LB hε hε20 hγ hap hA)
    refine key.congr fun x hx => ?_
    have h0 : yP (ap, (ap * q, ap * x)) ≠ 0 := fun h => by
      have := hP.ge (hA.mem hx); rw [h, abs_zero] at this; linarith
    simp only [Echart]
    rw [← ratio_eq h0, ← ratio_eq h0]
  · -- moving `q`, by the `(q,u) ↔ (a',v)` symmetry of (M9)
    have hA : CurveOK ε fun x => ((ap, (ap * x, ap * a)) : T3) :=
      ⟨coordOK_const hap, coordOK_scale hap, coordOK_const (hq1 a ha)⟩
    have key := EM9_pert (S := Icc (-1 : ℝ) 1) subset_rfl ha (ratio_LB hε hε20 hP hJP hA)
      (ratio_LB hε hε20 hP hIP hA) (coef_LB hε hε20 hγ hap hA)
    refine key.congr fun x hx => ?_
    have h0 : yP (ap, (ap * x, ap * a)) ≠ 0 := fun h => by
      have := hP.ge (hA.mem hx); rw [h, abs_zero] at this; linarith
    simp only [Echart]
    rw [EM9_symm, ← ratio_eq h0, ← ratio_eq h0]

/-- Trivial bound: any `e^{-g}` with `g ≥ 0` integrates to at most the box volume. -/
theorem lintegral_exp_neg_le_vol {ε : ℝ} (hε : 0 < ε) (g : ℝ × (Fin 2 → ℝ) → ℝ)
    (hg : ∀ b, 0 ≤ g b) :
    ∫⁻ b in Icc (-ε) ε ×ˢ square 0 ε, ENNReal.ofReal (Real.exp (-g b)) ≤
      ENNReal.ofReal ((2 * ε) ^ 3) := by
  have := lemmaM4_trivial hε (fun b => √(g b))
  refine le_trans (le_of_eq ?_) this
  refine lintegral_congr fun b => ?_
  rw [Real.sq_sqrt (hg b)]

/-- The pivot-first row integrand. -/
noncomputable def rowInt (yP yI yJ γ : T3 → ℝ) (M κ : ℝ) (a : T3) (b : ℝ × (Fin 2 → ℝ)) : ℝ :=
  Real.exp (-(M * ((a.1 ^ 2 * yP a * b.1 + a.2.1 ^ 2 * yI a * b.2 0 + a.2.2 ^ 2 * yJ a * b.2 1 +
      κ) ^ 2 + (a.1 * b.1 ^ 2 + a.2.1 * b.2 0 ^ 2 + a.2.2 * b.2 1 ^ 2 +
      (a.1 ^ 2 * b.1 + a.2.1 ^ 2 * b.2 0 + a.2.2 ^ 2 * b.2 1) ^ 2 / γ a) ^ 2)))

theorem pivotRegion_sub_box3 {ε : ℝ} : pivotRegion ε ⊆ box3 ε := by
  intro a ha
  obtain ⟨h1, h2, h3⟩ := ha
  exact ⟨h1, h2.trans h1, h3.trans h1⟩

theorem ae_fst_ne_zero : ∀ᵐ a : T3 ∂volume, a.1 ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have : {a : T3 | a.1 = 0} = {0} ×ˢ univ := by ext a; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- **One row, pivot first (F5 per pivot):** the amplitude integral of the `κ`-uniform
`b`-integral is `≤ C N⁻¹ (log N)²`. -/
theorem pivotRow {ε M : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 1 / 20) (hM : Real.exp 1 ≤ M)
    {yP yI yJ γ : T3 → ℝ} (hmP : Measurable yP) (hmI : Measurable yI) (hmJ : Measurable yJ)
    (hmγ : Measurable γ) (hP : WOK ε yP) (hI : WOK ε yI) (hJ : WOK ε yJ) (hγ : WOK ε γ)
    (hIP : WDOK ε yI yP) (hJP : WDOK ε yJ yP) :
    ∫⁻ a in pivotRegion ε, ⨆ κ : ℝ, ∫⁻ b in Icc (-ε) ε ×ˢ square 0 ε,
        ENNReal.ofReal (rowInt yP yI yJ γ M κ a b) ≤
      ENNReal.ofReal (CM5 ε (CM4 ε) * M⁻¹ * Real.log M ^ 2) := by
  have hM1 : 1 ≤ M := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hM
  have hε1 : ε ≤ 1 := by linarith
  set Dfun : T3 → ℝ := fun a => a.2.1 / a.1 * (a.2.2 / a.1) *
    EM9 (a.2.1 / a.1) (a.2.2 / a.1) (yI a / yP a) (yJ a / yP a) (a.1 ^ 3 / γ a) with hDfun
  have hDm : Measurable Dfun := by
    simp only [hDfun, EM9]; fun_prop
  have hD : ∀ ap : ℝ, ap ≠ 0 → |ap| ≤ ε → ∃ E : ℝ × ℝ → ℝ, M3Int E ∧
      ∀ q a' : ℝ, |q| ≤ 1 → |a'| ≤ 1 → Dfun (ap, (ap * q, ap * a')) = q * a' * E (q, a') := by
    intro ap hap0 hap
    refine ⟨Echart yP yI yJ γ ap, m3Int_Echart hε hε20 hmP hmI hmJ hmγ hP hγ hIP hJP hap,
      fun q a' _ _ => ?_⟩
    simp only [hDfun, Echart]
    rw [mul_div_cancel_left₀ q hap0, mul_div_cancel_left₀ a' hap0]
  have hCM4 : 0 < CM4 ε := by unfold CM4; have := Kslice_pos hε; positivity
  refine le_trans ?_ (lemmaM5 hε hM hCM4 Dfun hDm hD)
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_pivotRegion ε),
    ae_restrict_of_ae ae_fst_ne_zero] with a ha ha0
  refine iSup_le fun κ => le_min ?_ ?_
  · exact lintegral_exp_neg_le_vol hε _ fun b => by positivity
  · obtain ⟨h1, h2, h3⟩ := ha
    have hb := pivotRegion_sub_box3 ⟨h1, h2, h3⟩
    exact lemmaM4 hε hε1 hM1 ha0 h1 h2 h3 (hP.1 a hb) (hI.1 a hb) (hJ.1 a hb) (hγ.1 a hb)

end VectorSLT
