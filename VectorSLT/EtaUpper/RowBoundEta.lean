/-
X5, step 3: one row (F4 + F5) for the near-shear target.

Copies of `pivotRow`, `rowBound` and `rowBound_M6` with `G` replaced by
`G_η = ∑ aᵢ bᵢ² - η² + (∑ aᵢ² bᵢ - η)²/γ`. The only change in the proofs is that the
amplitude-wise bound is `lemmaM4_eta` instead of `lemmaM4`; its right side is the same, so
Lemma M5 and the final constant `3 C_{M5} N⁻¹ (log N)²` are unchanged and independent of `η`.
-/
import VectorSLT.RowBound
import VectorSLT.EtaUpper.SliceEta

namespace VectorSLT

open MeasureTheory Set VectorSLT.SLT

/-- The pivot-first row integrand for `A_η`. -/
noncomputable def rowIntη (yP yI yJ γ : T3 → ℝ) (M κ η : ℝ) (a : T3) (b : ℝ × (Fin 2 → ℝ)) : ℝ :=
  Real.exp (-(M * ((a.1 ^ 2 * yP a * b.1 + a.2.1 ^ 2 * yI a * b.2 0 + a.2.2 ^ 2 * yJ a * b.2 1 +
      κ) ^ 2 + (a.1 * b.1 ^ 2 + a.2.1 * b.2 0 ^ 2 + a.2.2 * b.2 1 ^ 2 - η ^ 2 +
      (a.1 ^ 2 * b.1 + a.2.1 ^ 2 * b.2 0 + a.2.2 ^ 2 * b.2 1 - η) ^ 2 / γ a) ^ 2)))

/-- **One row, pivot first, for `A_η`** (`pivotRow` with `lemmaM4_eta`). -/
theorem pivotRow_eta {ε M : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 1 / 20) (hM : Real.exp 1 ≤ M) (η : ℝ)
    {yP yI yJ γ : T3 → ℝ} (hmP : Measurable yP) (hmI : Measurable yI) (hmJ : Measurable yJ)
    (hmγ : Measurable γ) (hP : WOK ε yP) (hI : WOK ε yI) (hJ : WOK ε yJ) (hγ : WOK ε γ)
    (hIP : WDOK ε yI yP) (hJP : WDOK ε yJ yP) :
    ∫⁻ a in pivotRegion ε, ⨆ κ : ℝ, ∫⁻ b in Icc (-ε) ε ×ˢ square 0 ε,
        ENNReal.ofReal (rowIntη yP yI yJ γ M κ η a b) ≤
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
    exact lemmaM4_eta hε hε1 hM1 η ha0 h1 h2 h3 (hP.1 a hb) (hI.1 a hb) (hJ.1 a hb) (hγ.1 a hb)

/-- `e^{-M(Z² + G_η²)}` for one row in its actual coordinates. -/
noncomputable def rowActη (y : ℕ → T3 → ℝ) (γ : T3 → ℝ) (M κ η : ℝ) (a b : T3) : ℝ :=
  Real.exp (-(M * ((a.1 ^ 2 * y 0 a * b.1 + a.2.1 ^ 2 * y 1 a * b.2.1 + a.2.2 ^ 2 * y 2 a * b.2.2 +
      κ) ^ 2 + (a.1 * b.1 ^ 2 + a.2.1 * b.2.1 ^ 2 + a.2.2 * b.2.2 ^ 2 - η ^ 2 +
      (a.1 ^ 2 * b.1 + a.2.1 ^ 2 * b.2.1 + a.2.2 ^ 2 * b.2.2 - η) ^ 2 / γ a) ^ 2)))

theorem rowActη_piv (p : Fin 3) (y : ℕ → T3 → ℝ) (γ : T3 → ℝ) (M κ η : ℝ) (a' b : T3) :
    rowActη y γ M κ η ((pivMap p).symm a') b =
      rowIntη (fun a => y (pP p) ((pivMap p).symm a)) (fun a => y (pI p) ((pivMap p).symm a))
        (fun a => y (pJ p) ((pivMap p).symm a)) (fun a => γ ((pivMap p).symm a)) M κ η a'
        (e2 (pivMap p b)) := by
  obtain ⟨x0, x1, x2⟩ := a'
  obtain ⟨b0, b1, b2⟩ := b
  fin_cases p
  · simp only [rowActη, rowIntη, pivMap, MeasurableEquiv.refl_apply, MeasurableEquiv.symm_refl,
      e2_apply, pP, pI, pJ, Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp only [rowActη, rowIntη, pivMap, perm1_apply, perm1_symm_apply, e2_apply, pP, pI, pJ,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 2; ring
  · simp only [rowActη, rowIntη, pivMap, perm2_apply, perm2_symm_apply, e2_apply, pP, pI, pJ,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 2; ring

/-- **One row (F5) for `A_η`**:
`∫_{[-ε,ε]³} sup_κ ∫_{[-ε,ε]³} e^{-M(Z² + G_η²)} db da ≤ 3 C N⁻¹(log N)²`, for every `η`. -/
theorem rowBound_eta {ε M : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 1 / 20) (hM : Real.exp 1 ≤ M) (η : ℝ)
    {y : ℕ → T3 → ℝ} {γ : T3 → ℝ} (hmy : ∀ i, Measurable (y i)) (hmγ : Measurable γ)
    (hy : ∀ i < 3, WOK ε (y i)) (hγ : WOK ε γ) (hyd : ∀ i < 3, ∀ l < 3, WDOK ε (y i) (y l)) :
    ∫⁻ a in box3 ε, ⨆ κ : ℝ, ∫⁻ b in box3 ε, ENNReal.ofReal (rowActη y γ M κ η a b) ≤
      3 * ENNReal.ofReal (CM5 ε (CM4 ε) * M⁻¹ * Real.log M ^ 2) := by
  set Φ : T3 → ENNReal := fun a => ⨆ κ : ℝ, ∫⁻ b in box3 ε, ENNReal.ofReal (rowActη y γ M κ η a b)
    with hΦ
  set B := ENNReal.ofReal (CM5 ε (CM4 ε) * M⁻¹ * Real.log M ^ 2)
  have hpart : ∀ p : Fin 3, ∫⁻ a in (pivMap p) ⁻¹' pivotRegion ε, Φ a ≤ B := by
    intro p
    have hπ := permOK_symm p
    obtain ⟨hP3, hI3, hJ3⟩ := pidx_lt p
    have hmeas : ∀ i, Measurable fun a => y i ((pivMap p).symm a) :=
      fun i => (hmy i).comp (pivMap p).symm.measurable
    have e1 : ∫⁻ a in (pivMap p) ⁻¹' pivotRegion ε, Φ a =
        ∫⁻ a' in pivotRegion ε, Φ ((pivMap p).symm a') := by
      have := (mp_pivMap p).setLIntegral_comp_preimage_emb (pivMap p).measurableEmbedding
        (fun a' => Φ ((pivMap p).symm a')) (pivotRegion ε)
      simpa only [MeasurableEquiv.symm_apply_apply] using this
    rw [e1]
    have hτ : MeasurePreserving (fun b => e2 (pivMap p b)) volume volume :=
      mp_e2.comp (mp_pivMap p)
    have hτe : MeasurableEmbedding fun b => e2 (pivMap p b) :=
      ((pivMap p).trans e2).measurableEmbedding
    have e3 : ∀ a' : T3, Φ ((pivMap p).symm a') = ⨆ κ : ℝ,
        ∫⁻ β in Icc (-ε) ε ×ˢ square 0 ε, ENNReal.ofReal (rowIntη
          (fun a => y (pP p) ((pivMap p).symm a)) (fun a => y (pI p) ((pivMap p).symm a))
          (fun a => y (pJ p) ((pivMap p).symm a)) (fun a => γ ((pivMap p).symm a)) M κ η a' β) := by
      intro a'
      simp only [hΦ]
      refine iSup_congr fun κ => ?_
      rw [box3_eq_preimage p ε]
      simp_rw [rowActη_piv p]
      exact hτ.setLIntegral_comp_preimage_emb hτe
        (fun β => ENNReal.ofReal (rowIntη (fun a => y (pP p) ((pivMap p).symm a))
          (fun a => y (pI p) ((pivMap p).symm a)) (fun a => y (pJ p) ((pivMap p).symm a))
          (fun a => γ ((pivMap p).symm a)) M κ η a' β)) _
    simp_rw [e3]
    exact pivotRow_eta hε hε20 hM η (hmeas _) (hmeas _) (hmeas _)
      (hmγ.comp (pivMap p).symm.measurable)
      ((hy _ hP3).comp hπ) ((hy _ hI3).comp hπ) ((hy _ hJ3).comp hπ) (hγ.comp hπ)
      ((hyd _ hI3 _ hP3).comp hπ) ((hyd _ hJ3 _ hP3).comp hπ)
  have hcover : box3 ε ⊆ (pivMap 0) ⁻¹' pivotRegion ε ∪
      ((pivMap 1) ⁻¹' pivotRegion ε ∪ (pivMap 2) ⁻¹' pivotRegion ε) := by
    rintro ⟨a0, a1, a2⟩ ⟨h0, h1, h2⟩
    simp only [mem_union, mem_preimage, pivMap, MeasurableEquiv.refl_apply, perm1_apply,
      perm2_apply, pivotRegion, mem_ofPred_eq]
    rcases le_total |a1| |a0| with c1 | c1 <;> rcases le_total |a2| |a0| with c2 | c2 <;>
      rcases le_total |a2| |a1| with c3 | c3
    all_goals first
      | exact Or.inl ⟨h0, c1, c2⟩
      | exact Or.inr (Or.inl ⟨h1, c1, c3⟩)
      | exact Or.inr (Or.inr ⟨h2, c2, c3⟩)
      | exact Or.inr (Or.inl ⟨h1, c1, by linarith⟩)
      | exact Or.inr (Or.inr ⟨h2, c2, by linarith⟩)
  calc ∫⁻ a in box3 ε, Φ a
      ≤ ∫⁻ a in (pivMap 0) ⁻¹' pivotRegion ε ∪
          ((pivMap 1) ⁻¹' pivotRegion ε ∪ (pivMap 2) ⁻¹' pivotRegion ε), Φ a :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ a in (pivMap 0) ⁻¹' pivotRegion ε, Φ a) +
          ((∫⁻ a in (pivMap 1) ⁻¹' pivotRegion ε, Φ a) +
            ∫⁻ a in (pivMap 2) ⁻¹' pivotRegion ε, Φ a) :=
        (lintegral_union_le _ _ _).trans (add_le_add le_rfl (lintegral_union_le _ _ _))
    _ ≤ B + (B + B) := add_le_add (hpart 0) (add_le_add (hpart 1) (hpart 2))
    _ = 3 * B := by ring

/-- **The row bound for the explicit (M6) weights, target `A_η`.** -/
theorem rowBound_M6_eta {ε M : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 1 / 20) (hM : Real.exp 1 ≤ M) (η : ℝ)
    {cy cg : ℝ} (hcy : |cy| ≤ 1 / 32) (hcg : |cg| ≤ 1 / 32) {g : T3 → T3} (hgm : Measurable g)
    (hg : GOK ε g) :
    ∫⁻ a in box3 ε, ⨆ κ : ℝ, ∫⁻ b in box3 ε,
        ENNReal.ofReal (rowActη (yRow cy g) (γRow cg) M κ η a b) ≤
      3 * ENNReal.ofReal (CM5 ε (CM4 ε) * M⁻¹ * Real.log M ^ 2) :=
  rowBound_eta hε hε20 hM η (measurable_yRow cy hgm) (measurable_γRow cg)
    (fun i _ => yRow_WOK hε hε20 hcy hg i) (γRow_WOK hε hε20 hcg)
    (fun i _ l _ => yRow_WDOK hε hg i l)

end VectorSLT
