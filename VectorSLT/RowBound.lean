/-
L6 stage 3, F4 + F5: one row in its actual coordinates.

The amplitude box `[-ε,ε]³` is covered by the three pivot regions. Each is mapped to the
pivot-first region by a coordinate permutation (measure preserving), and the `b`-box to
`[-ε,ε] × square` likewise, so `pivotRow` applies. The explicit (M6) weights
`y_i = 1 + c - A + ∑_{j<i} a_j³` and `γ = 1 + c - A` satisfy `WOK`/`WDOK`, whether `y`
depends on the row's own amplitudes (row 2) or is constant in them (row 1).
-/
import VectorSLT.PivotRow

namespace VectorSLT

open MeasureTheory Set SLT

/-! ### Coordinate permutations -/

/-- `(a₀, (a₁, a₂)) ↦ (a₁, (a₀, a₂))`. -/
def perm1 : T3 ≃ᵐ T3 :=
  MeasurableEquiv.prodAssoc.symm.trans
    (((MeasurableEquiv.prodComm).prodCongr (MeasurableEquiv.refl ℝ)).trans
      MeasurableEquiv.prodAssoc)

/-- `(a₀, (a₁, a₂)) ↦ (a₂, (a₀, a₁))`. -/
def perm2 : T3 ≃ᵐ T3 := MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm

theorem perm1_apply (x : T3) : perm1 x = (x.2.1, (x.1, x.2.2)) := rfl
theorem perm2_apply (x : T3) : perm2 x = (x.2.2, (x.1, x.2.1)) := rfl
theorem perm1_symm_apply (x : T3) : perm1.symm x = (x.2.1, (x.1, x.2.2)) := rfl
theorem perm2_symm_apply (x : T3) : perm2.symm x = (x.2.1, (x.2.2, x.1)) := rfl

theorem mp_perm1 : MeasurePreserving perm1 volume volume := by
  have h1 := (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
    (volume : Measure ℝ)).symm
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).prod (MeasurePreserving.id (volume : Measure ℝ))
  have h3 := measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
    (volume : Measure ℝ)
  exact h3.comp (h2.comp h1)

theorem mp_perm2 : MeasurePreserving perm2 volume volume := by
  have h1 := (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
    (volume : Measure ℝ)).symm
  have h2 := Measure.measurePreserving_swap (μ := (volume : Measure (ℝ × ℝ)))
    (ν := (volume : Measure ℝ))
  exact h2.comp h1

/-- `(b_p, (b_i, b_j)) ↦ (b_p, ![b_i, b_j])`. -/
def e2 : T3 ≃ᵐ ℝ × (Fin 2 → ℝ) :=
  (MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow.symm

theorem e2_apply (x : T3) : e2 x = (x.1, ![x.2.1, x.2.2]) :=
  Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)

theorem mp_e2 : MeasurePreserving e2 volume volume :=
  (MeasurePreserving.id (volume : Measure ℝ)).prod ((volume_preserving_finTwoArrow ℝ).symm _)

/-- The pivot maps `a ↦ (a_p, (a_i, a_j))`. -/
def pivMap : Fin 3 → (T3 ≃ᵐ T3)
  | 0 => MeasurableEquiv.refl T3
  | 1 => perm1
  | 2 => perm2

/-- Pivot index and the two others, matching `pivMap`. -/
def pP : Fin 3 → ℕ | 0 => 0 | 1 => 1 | 2 => 2
def pI : Fin 3 → ℕ | 0 => 1 | 1 => 0 | 2 => 0
def pJ : Fin 3 → ℕ | 0 => 2 | 1 => 2 | 2 => 1

theorem pidx_lt (p : Fin 3) : pP p < 3 ∧ pI p < 3 ∧ pJ p < 3 := by
  fin_cases p <;> simp [pP, pI, pJ]

theorem mp_pivMap (p : Fin 3) : MeasurePreserving (pivMap p) volume volume := by
  fin_cases p
  · exact MeasurePreserving.id _
  · exact mp_perm1
  · exact mp_perm2

/-- Coordinate permutations preserve the box and cube-Lipschitz curves. -/
def PermOK (π : T3 → T3) : Prop :=
  (∀ ε a, a ∈ box3 ε → π a ∈ box3 ε) ∧ ∀ ε A, CurveOK ε A → CurveOK ε fun x => π (A x)

theorem permOK_symm (p : Fin 3) : PermOK (pivMap p).symm := by
  fin_cases p
  · exact ⟨fun _ _ h => h, fun _ _ h => h⟩
  · refine ⟨fun ε a ⟨h1, h2, h3⟩ => ?_, fun ε A ⟨h1, h2, h3⟩ => ?_⟩
    · simp only [pivMap, perm1_symm_apply]; exact ⟨h2, h1, h3⟩
    · simp only [pivMap, perm1_symm_apply]; exact ⟨h2, h1, h3⟩
  · refine ⟨fun ε a ⟨h1, h2, h3⟩ => ?_, fun ε A ⟨h1, h2, h3⟩ => ?_⟩
    · simp only [pivMap, perm2_symm_apply]; exact ⟨h2, h3, h1⟩
    · simp only [pivMap, perm2_symm_apply]; exact ⟨h2, h3, h1⟩

theorem WOK.comp {ε : ℝ} {w : T3 → ℝ} {π : T3 → T3} (h : WOK ε w) (hπ : PermOK π) :
    WOK ε fun a => w (π a) :=
  ⟨fun a ha => h.1 _ (hπ.1 ε a ha), fun A hA => h.2 _ (hπ.2 ε A hA)⟩

theorem WDOK.comp {ε : ℝ} {w w' : T3 → ℝ} {π : T3 → T3} (h : WDOK ε w w') (hπ : PermOK π) :
    WDOK ε (fun a => w (π a)) fun a => w' (π a) :=
  fun A hA => h _ (hπ.2 ε A hA)

/-! ### The row integrand in actual coordinates -/

/-- `e^{-M(Z² + G²)}` for one row: `Z = ∑ aᵢ² yᵢ bᵢ + κ`, `G = ∑ aᵢ bᵢ² + (∑ aᵢ² bᵢ)²/γ`. -/
noncomputable def rowAct (y : ℕ → T3 → ℝ) (γ : T3 → ℝ) (M κ : ℝ) (a b : T3) : ℝ :=
  Real.exp (-(M * ((a.1 ^ 2 * y 0 a * b.1 + a.2.1 ^ 2 * y 1 a * b.2.1 + a.2.2 ^ 2 * y 2 a * b.2.2 +
      κ) ^ 2 + (a.1 * b.1 ^ 2 + a.2.1 * b.2.1 ^ 2 + a.2.2 * b.2.2 ^ 2 +
      (a.1 ^ 2 * b.1 + a.2.1 ^ 2 * b.2.1 + a.2.2 ^ 2 * b.2.2) ^ 2 / γ a) ^ 2)))

theorem rowAct_piv (p : Fin 3) (y : ℕ → T3 → ℝ) (γ : T3 → ℝ) (M κ : ℝ) (a' b : T3) :
    rowAct y γ M κ ((pivMap p).symm a') b =
      rowInt (fun a => y (pP p) ((pivMap p).symm a)) (fun a => y (pI p) ((pivMap p).symm a))
        (fun a => y (pJ p) ((pivMap p).symm a)) (fun a => γ ((pivMap p).symm a)) M κ a'
        (e2 (pivMap p b)) := by
  obtain ⟨x0, x1, x2⟩ := a'
  obtain ⟨b0, b1, b2⟩ := b
  fin_cases p
  · simp only [rowAct, rowInt, pivMap, MeasurableEquiv.refl_apply, MeasurableEquiv.symm_refl,
      e2_apply, pP, pI, pJ, Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp only [rowAct, rowInt, pivMap, perm1_apply, perm1_symm_apply, e2_apply, pP, pI, pJ,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 2; ring
  · simp only [rowAct, rowInt, pivMap, perm2_apply, perm2_symm_apply, e2_apply, pP, pI, pJ,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 2; ring

theorem box3_eq_preimage (p : Fin 3) (ε : ℝ) :
    box3 ε = (fun b => e2 (pivMap p b)) ⁻¹' (Icc (-ε) ε ×ˢ square 0 ε) := by
  ext ⟨b0, b1, b2⟩
  fin_cases p <;>
  simp only [box3, square, pivMap, MeasurableEquiv.refl_apply, perm1_apply, perm2_apply, e2_apply,
    mem_ofPred_eq, mem_preimage, mem_prod, mem_pi, mem_univ, forall_const, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, zero_sub, zero_add, abs_le, mem_Icc,
    true_implies] <;> tauto

theorem measurable_rowAct {y : ℕ → T3 → ℝ} {γ : T3 → ℝ} (hy : ∀ i, Measurable (y i))
    (hγ : Measurable γ) (M κ : ℝ) : Measurable fun z : T3 × T3 => rowAct y γ M κ z.1 z.2 := by
  have h0 : Measurable fun z : T3 × T3 => y 0 z.1 := (hy 0).comp measurable_fst
  have h1 : Measurable fun z : T3 × T3 => y 1 z.1 := (hy 1).comp measurable_fst
  have h2 : Measurable fun z : T3 × T3 => y 2 z.1 := (hy 2).comp measurable_fst
  have h3 : Measurable fun z : T3 × T3 => γ z.1 := hγ.comp measurable_fst
  unfold rowAct; fun_prop

/-- **One row (F5):** `∫_{[-ε,ε]³} sup_κ ∫_{[-ε,ε]³} e^{-M(Z² + G²)} db da ≤ 3 C N⁻¹(log N)²`. -/
theorem rowBound {ε M : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 1 / 20) (hM : Real.exp 1 ≤ M)
    {y : ℕ → T3 → ℝ} {γ : T3 → ℝ} (hmy : ∀ i, Measurable (y i)) (hmγ : Measurable γ)
    (hy : ∀ i < 3, WOK ε (y i)) (hγ : WOK ε γ) (hyd : ∀ i < 3, ∀ l < 3, WDOK ε (y i) (y l)) :
    ∫⁻ a in box3 ε, ⨆ κ : ℝ, ∫⁻ b in box3 ε, ENNReal.ofReal (rowAct y γ M κ a b) ≤
      3 * ENNReal.ofReal (CM5 ε (CM4 ε) * M⁻¹ * Real.log M ^ 2) := by
  set Φ : T3 → ENNReal := fun a => ⨆ κ : ℝ, ∫⁻ b in box3 ε, ENNReal.ofReal (rowAct y γ M κ a b)
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
        ∫⁻ β in Icc (-ε) ε ×ˢ square 0 ε, ENNReal.ofReal (rowInt
          (fun a => y (pP p) ((pivMap p).symm a)) (fun a => y (pI p) ((pivMap p).symm a))
          (fun a => y (pJ p) ((pivMap p).symm a)) (fun a => γ ((pivMap p).symm a)) M κ a' β) := by
      intro a'
      simp only [hΦ]
      refine iSup_congr fun κ => ?_
      rw [box3_eq_preimage p ε]
      simp_rw [rowAct_piv p]
      exact hτ.setLIntegral_comp_preimage_emb hτe
        (fun β => ENNReal.ofReal (rowInt (fun a => y (pP p) ((pivMap p).symm a))
          (fun a => y (pI p) ((pivMap p).symm a)) (fun a => y (pJ p) ((pivMap p).symm a))
          (fun a => γ ((pivMap p).symm a)) M κ a' β)) _
    simp_rw [e3]
    exact pivotRow hε hε20 hM (hmeas _) (hmeas _) (hmeas _) (hmγ.comp (pivMap p).symm.measurable)
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
      | exact Or.inr (Or.inr ⟨h2, by linarith, c3⟩)
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

/-! ### The explicit (M6) weights -/

def cub3 (a : T3) : ℝ := a.1 ^ 3 + a.2.1 ^ 3 + a.2.2 ^ 3

/-- `∑_{j<i} a_j³` for `i ≤ 2`. -/
def pcub : ℕ → T3 → ℝ
  | 0, _ => 0
  | 1, a => a.1 ^ 3
  | _, a => a.1 ^ 3 + a.2.1 ^ 3

/-- `yᵢ = 1 + c - A + ∑_{j<i} a_j³`, read off the amplitudes `g a`. -/
def yRow (cy : ℝ) (g : T3 → T3) (i : ℕ) (a : T3) : ℝ := 1 + cy - cub3 (g a) + pcub i (g a)

/-- `γ = 1 + c - A`. -/
def γRow (cg : ℝ) (a : T3) : ℝ := 1 + cg - cub3 a

theorem cub3_LB {ε : ℝ} {A : ℝ → T3} (hA : CurveOK ε A) :
    LB (fun x => cub3 (A x)) (Icc (-1) 1) (3 * ε ^ 3) (9 * ε ^ 3) :=
  ((hA.1.cube.add hA.2.1.cube).add hA.2.2.cube).mono (le_of_eq (by ring)) (le_of_eq (by ring))

theorem pcub_LB {ε : ℝ} (hε : 0 ≤ ε) {A : ℝ → T3} (hA : CurveOK ε A) (i : ℕ) :
    LB (fun x => pcub i (A x)) (Icc (-1) 1) (3 * ε ^ 3) (9 * ε ^ 3) := by
  have e0 : 0 ≤ ε ^ 3 := by positivity
  rcases i with _ | _ | i
  · exact (LB.const' (a := (0 : ℝ)) (b := 3 * ε ^ 3) (by rw [abs_zero]; positivity)).mono le_rfl
      (by positivity)
  · exact hA.1.cube.mono (by linarith) (by linarith)
  · exact (hA.1.cube.add hA.2.1.cube).mono (by linarith) (by linarith)

/-- Amplitude readers: the row's own amplitudes (`id`) or a fixed vector in the box. -/
def GOK (ε : ℝ) (g : T3 → T3) : Prop :=
  (∀ a ∈ box3 ε, g a ∈ box3 ε) ∧ ∀ A, CurveOK ε A → CurveOK ε fun x => g (A x)

theorem gok_id (ε : ℝ) : GOK ε id := ⟨fun _ h => h, fun _ h => h⟩

theorem gok_const {ε : ℝ} {a₂ : T3} (h : a₂ ∈ box3 ε) : GOK ε fun _ => a₂ :=
  ⟨fun _ _ => h, fun _ _ => ⟨coordOK_const h.1, coordOK_const h.2.1, coordOK_const h.2.2⟩⟩

theorem curveOK_const {ε : ℝ} {a : T3} (h : a ∈ box3 ε) : CurveOK ε fun _ => a :=
  ⟨coordOK_const h.1, coordOK_const h.2.1, coordOK_const h.2.2⟩

theorem yRow_LB {ε : ℝ} (hε : 0 < ε) {cy : ℝ} {g : T3 → T3} (hg : GOK ε g) (i : ℕ)
    {A : ℝ → T3} (hA : CurveOK ε A) :
    LB (fun x => yRow cy g i (A x) - 1) (Icc (-1) 1) (|cy| + 6 * ε ^ 3) (18 * ε ^ 3) := by
  have hgA := hg.2 A hA
  exact ((((LB.const cy).sub (cub3_LB hgA)).add (pcub_LB hε.le hgA i)).congr
    fun x _ => by simp only [yRow]; ring).mono (le_of_eq (by ring)) (le_of_eq (by ring))

theorem yRow_WOK {ε : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 1 / 20) {cy : ℝ} (hcy : |cy| ≤ 1 / 32)
    {g : T3 → T3} (hg : GOK ε g) (i : ℕ) : WOK ε (yRow cy g i) := by
  have e3 := eps3_le hε hε20
  refine ⟨fun a ha => ?_, fun A hA => ?_⟩
  · have := (yRow_LB (cy := cy) hε hg i (curveOK_const ha)).1 0 ⟨by norm_num, by norm_num⟩
    linarith
  · have h := (yRow_LB (cy := cy) hε hg i hA).add (LB.const' (S := Icc (-1 : ℝ) 1) (a := 1) (b := 1)
      (by norm_num))
    exact (h.congr fun x _ => by ring).mono (by linarith) (by linarith)

theorem yRow_WDOK {ε : ℝ} (hε : 0 < ε) {cy : ℝ} {g : T3 → T3} (hg : GOK ε g) (i l : ℕ) :
    WDOK ε (yRow cy g i) (yRow cy g l) := by
  intro A hA
  have hgA := hg.2 A hA
  exact (((pcub_LB hε.le hgA i).sub (pcub_LB hε.le hgA l)).congr
    fun x _ => by simp only [yRow]; ring).mono (le_of_eq (by ring)) (le_of_eq (by ring))

theorem γRow_WOK {ε : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 1 / 20) {cg : ℝ} (hcg : |cg| ≤ 1 / 32) :
    WOK ε (γRow cg) := by
  have e3 := eps3_le hε hε20
  have e0 : 0 ≤ ε ^ 3 := by positivity
  refine ⟨fun a ha => ?_, fun A hA => ?_⟩
  · have := (cub3_LB (curveOK_const ha)).1 0 ⟨by norm_num, by norm_num⟩
    simp only [γRow]
    rw [show 1 + cg - cub3 a - 1 = cg - cub3 a by ring]
    have := abs_sub cg (cub3 a)
    linarith
  · have h := (LB.const (S := Icc (-1 : ℝ) 1) (1 + cg)).sub (cub3_LB hA)
    have h1 : |1 + cg| ≤ 1 + 1 / 32 := (abs_add_le _ _).trans (by rw [abs_one]; linarith)
    exact (h.congr fun x _ => by simp only [γRow]).mono (by linarith) (by linarith)

theorem measurable_cub3 : Measurable cub3 := by unfold cub3; fun_prop

theorem measurable_pcub (i : ℕ) : Measurable (pcub i) := by
  rcases i with _ | _ | i
  · exact measurable_const
  · show Measurable fun a : T3 => a.1 ^ 3; fun_prop
  · show Measurable fun a : T3 => a.1 ^ 3 + a.2.1 ^ 3; fun_prop

theorem measurable_yRow (cy : ℝ) {g : T3 → T3} (hg : Measurable g) (i : ℕ) :
    Measurable (yRow cy g i) := by
  unfold yRow
  exact ((measurable_const.sub (measurable_cub3.comp hg)).add ((measurable_pcub i).comp hg))

theorem measurable_γRow (cg : ℝ) : Measurable (γRow cg) := by
  unfold γRow; exact measurable_const.sub measurable_cub3

/-- **The row bound for the explicit weights.** -/
theorem rowBound_M6 {ε M : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 1 / 20) (hM : Real.exp 1 ≤ M)
    {cy cg : ℝ} (hcy : |cy| ≤ 1 / 32) (hcg : |cg| ≤ 1 / 32) {g : T3 → T3} (hgm : Measurable g)
    (hg : GOK ε g) :
    ∫⁻ a in box3 ε, ⨆ κ : ℝ, ∫⁻ b in box3 ε,
        ENNReal.ofReal (rowAct (yRow cy g) (γRow cg) M κ a b) ≤
      3 * ENNReal.ofReal (CM5 ε (CM4 ε) * M⁻¹ * Real.log M ^ 2) :=
  rowBound hε hε20 hM (measurable_yRow cy hgm) (measurable_γRow cg)
    (fun i _ => yRow_WOK hε hε20 hcy hg i) (γRow_WOK hε hε20 hcg)
    (fun i _ l _ => yRow_WDOK hε hg i l)

end VectorSLT
