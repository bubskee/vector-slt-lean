import VectorSLT.IdentityGroup.Cubes.Scaling

/-!
# The chart reduction for `n = k + 1` forms

This file reduces `∫ e^{-G_n} < ∞` over `Fin n → ℝ × ℝ` to an angular integrability statement
in one affine chart, the analogue of the paper's "Radial integration" step for the sup norm.

1. *Symmetry* (`lintegral_le_mul_setLIntegral_chartRegion`). `G_n` is invariant under
   permutations of the forms and under `x ↔ y`. Every `u` is moved by one of these `2n` maps into
   the region `chartRegion` where `|a₀|` is the largest of all `2n` coordinates.
2. *Radial integration* (`setLIntegral_chartRegion_le`). On that region write
   `u = a • (Fin.cons (1, β) w)` with `‖(β, w)‖ ≤ 1`. Homogeneity of degree six gives
   `∫ |a|^{2n-1} e^{-a⁶ g} da = (Γ(n/3)/3) g^{-n/3}`.
3. *Shear* (`setLIntegral_chartG_le`). The substitution `y ↦ y - βx` makes form 0 equal to `x`.
   It changes the coefficient norm by a factor at most `80` (for `|β| ≤ 1`) and moves the ball of
   radius one into the ball of radius two, preserving volume.

The result (`lintegral_exp_lt_top_of_chart`): if `∫_{‖w‖ ≤ 2} G_n(x, w)^{-n/3} < ∞`, where
`G_n(x, w)` is the coefficient norm of `x³ + ∑ ℓ_{w_i}³`, then `∫ e^{-G_n} < ∞`.
-/

namespace VectorSLT.IdentityGroup.Cubes

open MeasureTheory Real Module Set
open scoped ENNReal

/-! ### Symmetries of `cubeSumSq` -/

lemma cubeSumSq_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (u : Fin n → ℝ × ℝ) :
    cubeSumSq (fun j => u (σ j)) = cubeSumSq u := by
  have h : cubeSum (fun j => u (σ j)) = cubeSum u := by
    funext j
    fin_cases j
    · exact Equiv.sum_comp σ (fun i => (u i).1 ^ 3)
    · exact Equiv.sum_comp σ (fun i => (u i).1 ^ 2 * (u i).2)
    · exact Equiv.sum_comp σ (fun i => (u i).1 * (u i).2 ^ 2)
    · exact Equiv.sum_comp σ (fun i => (u i).2 ^ 3)
  simp only [cubeSumSq, h]

lemma cubeSumSq_swap {n : ℕ} (u : Fin n → ℝ × ℝ) :
    cubeSumSq (fun j => (u j).swap) = cubeSumSq u := by
  simp only [cubeSumSq, Fin.sum_univ_four, cubeSum, Prod.fst_swap, Prod.snd_swap]
  simp only [Matrix.cons_val, Fin.isValue]
  have h1 : ∑ i, (u i).2 ^ 2 * (u i).1 = ∑ i, (u i).1 * (u i).2 ^ 2 :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have h2 : ∑ i, (u i).2 * (u i).1 ^ 2 = ∑ i, (u i).1 ^ 2 * (u i).2 :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [h1, h2]; ring

/-- Reorder the forms by `σ`, then optionally swap `x ↔ y`. -/
def symForms {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Bool) (u : Fin n → ℝ × ℝ) :
    Fin n → ℝ × ℝ :=
  fun j => if s then (u (σ j)).swap else u (σ j)

lemma symForms_false {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    symForms σ false = fun u j => u (σ j) := rfl

lemma symForms_true {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    symForms σ true = fun u j => (u (σ j)).swap := rfl

lemma cubeSumSq_symForms {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Bool) (u : Fin n → ℝ × ℝ) :
    cubeSumSq (symForms σ s u) = cubeSumSq u := by
  cases s
  · rw [symForms_false]; exact cubeSumSq_comp_perm σ u
  · rw [symForms_true]
    exact (cubeSumSq_swap (fun j => u (σ j))).trans (cubeSumSq_comp_perm σ u)

lemma measurePreserving_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun (u : Fin n → ℝ × ℝ) j => u (σ j)) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ × ℝ) σ.symm
  have he : (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ × ℝ) σ.symm :
      (Fin n → ℝ × ℝ) → (Fin n → ℝ × ℝ)) = fun u j => u (σ j) := by
    funext u j
    have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => ℝ × ℝ) σ.symm u (σ j)
    simpa using this
  rw [he] at h
  exact h

lemma measurePreserving_swapForms {n : ℕ} :
    MeasurePreserving (fun (u : Fin n → ℝ × ℝ) j => (u j).swap) volume volume :=
  measurePreserving_pi (fun _ => (volume : Measure (ℝ × ℝ))) (fun _ => volume)
    (fun _ => Measure.measurePreserving_swap)

lemma measurePreserving_symForms {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Bool) :
    MeasurePreserving (symForms σ s) volume volume := by
  cases s
  · rw [symForms_false]; exact measurePreserving_comp_perm σ
  · rw [symForms_true]
    exact (measurePreserving_swapForms (n := n)).comp (measurePreserving_comp_perm σ)

/-- The region where `|a₀|` is the largest of all coordinates. -/
def chartRegion (n : ℕ) : Set (Fin (n + 1) → ℝ × ℝ) := {u | ∀ j, ‖u j‖ ≤ |(u 0).1|}

lemma measurableSet_chartRegion (n : ℕ) : MeasurableSet (chartRegion n) := by
  have : chartRegion n = ⋂ j, {u : Fin (n + 1) → ℝ × ℝ | ‖u j‖ ≤ |(u 0).1|} := by
    ext u; simp [chartRegion]
  rw [this]
  exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) (by fun_prop)

lemma norm_prod_swap (z : ℝ × ℝ) : ‖z.swap‖ = ‖z‖ := by
  simp [Prod.norm_def, max_comm]

lemma exists_symForms_mem_chartRegion {n : ℕ} (u : Fin (n + 1) → ℝ × ℝ) :
    ∃ i : Fin (n + 1), ∃ s : Bool, symForms (Equiv.swap 0 i) s u ∈ chartRegion n := by
  obtain ⟨i, hi⟩ := Finite.exists_max fun j => ‖u j‖
  refine ⟨i, decide (|(u i).1| < |(u i).2|), fun j => ?_⟩
  have hσ0 : Equiv.swap (0 : Fin (n + 1)) i 0 = i := Equiv.swap_apply_left 0 i
  have hj := hi (Equiv.swap 0 i j)
  by_cases h : |(u i).1| < |(u i).2|
  · have hn : ‖u i‖ = |(u i).2| := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_eq_right h.le]
    have hs : decide (|(u i).1| < |(u i).2|) = true := decide_eq_true h
    rw [hs, symForms_true]
    simp only [hσ0, Prod.fst_swap, norm_prod_swap]
    linarith
  · have hn : ‖u i‖ = |(u i).1| := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_eq_left (not_lt.mp h)]
    have hs : decide (|(u i).1| < |(u i).2|) = false := decide_eq_false h
    rw [hs, symForms_false]
    simp only [hσ0]
    linarith

/-- The integrand of the whole-space integral. -/
noncomputable def expG {n : ℕ} (u : Fin n → ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-cubeSumSq u))

lemma measurable_expG {n : ℕ} : Measurable (expG (n := n)) := by
  unfold expG
  exact ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp measurable_cubeSumSq.neg)

/-- **Symmetry step.** -/
theorem lintegral_le_mul_setLIntegral_chartRegion (n : ℕ) :
    ∫⁻ u : Fin (n + 1) → ℝ × ℝ, expG u ≤
      (2 * (n + 1) : ℝ≥0∞) * ∫⁻ u in chartRegion n, expG u := by
  set T : Fin (n + 1) × Bool → (Fin (n + 1) → ℝ × ℝ) → (Fin (n + 1) → ℝ × ℝ) :=
    fun is => symForms (Equiv.swap 0 is.1) is.2 with hT
  have hpt : ∀ u, expG u ≤ ∑ is : Fin (n + 1) × Bool, (chartRegion n).indicator expG (T is u) := by
    intro u
    obtain ⟨i, s, hmem⟩ := exists_symForms_mem_chartRegion u
    calc expG u = (chartRegion n).indicator expG (T (i, s) u) := by
          rw [indicator_of_mem hmem]
          simp only [expG, cubeSumSq_symForms]
      _ ≤ _ := Finset.single_le_sum (f := fun is => (chartRegion n).indicator expG (T is u))
          (fun _ _ => bot_le) (Finset.mem_univ (i, s))
  have hmeas : ∀ is, Measurable fun u => (chartRegion n).indicator expG (T is u) := fun is =>
    (measurable_expG.indicator (measurableSet_chartRegion n)).comp
      (measurePreserving_symForms _ _).measurable
  have hcomp : ∀ is, ∫⁻ u, (chartRegion n).indicator expG (T is u) =
      ∫⁻ u in chartRegion n, expG u := by
    intro is
    rw [← lintegral_indicator (measurableSet_chartRegion n)]
    exact (measurePreserving_symForms _ _).lintegral_comp
      (measurable_expG.indicator (measurableSet_chartRegion n))
  calc ∫⁻ u, expG u
      ≤ ∫⁻ u, ∑ is : Fin (n + 1) × Bool, (chartRegion n).indicator expG (T is u) :=
        lintegral_mono hpt
    _ = ∑ is : Fin (n + 1) × Bool, ∫⁻ u, (chartRegion n).indicator expG (T is u) :=
        lintegral_finsetSum _ fun is _ => hmeas is
    _ = ∑ _is : Fin (n + 1) × Bool, ∫⁻ u in chartRegion n, expG u := by
        simp only [hcomp]
    _ = (2 * (n + 1) : ℝ≥0∞) * ∫⁻ u in chartRegion n, expG u := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_bool, nsmul_eq_mul]
        push_cast; ring

/-! ### One-dimensional radial integral -/

/-- An even integrand: `∫ F(|x|) dx = 2 ∫_{x > 0} F(x) dx`. -/
lemma lintegral_comp_abs (F : ℝ → ℝ≥0∞) :
    ∫⁻ x, F |x| = 2 * ∫⁻ x in Ioi 0, F x := by
  have hpos : ∫⁻ x in Ioi 0, F |x| = ∫⁻ x in Ioi 0, F x :=
    setLIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [abs_of_pos hx]
  have hneg : ∫⁻ x in (Ioi (0 : ℝ))ᶜ, F |x| = ∫⁻ x in Ioi 0, F x := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
      (Homeomorph.neg ℝ).measurableEmbedding (fun y => F |y|) (Ici 0)
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Ici 0 = (Ioi (0 : ℝ))ᶜ := by
      ext x; simp
    simp only [abs_neg] at h
    rw [hpre] at h
    rw [h, setLIntegral_congr Ioi_ae_eq_Ici.symm]
    exact setLIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [abs_of_pos hx]
  rw [← lintegral_add_compl (fun x => F |x|) measurableSet_Ioi, hpos, hneg, two_mul]

lemma ofReal_rpow_neg_eq {g r : ℝ} (hg : 0 < g) :
    ENNReal.ofReal (g ^ (-r)) = ((ENNReal.ofReal g)⁻¹) ^ r := by
  rw [← ENNReal.ofReal_rpow_of_pos hg, ENNReal.rpow_neg, ENNReal.inv_rpow]

/-- The radial integral `∫ |a|^d e^{-a⁶ g} da ≤ (Γ((d+1)/6)/3) g^{-(d+1)/6}`, with value `∞`
on the right when `g = 0`. -/
lemma lintegral_radial_le (d : ℕ) {g : ℝ} (hg : 0 ≤ g) :
    ∫⁻ a : ℝ, ENNReal.ofReal (|a| ^ d) * ENNReal.ofReal (Real.exp (-(a ^ 6 * g))) ≤
      ENNReal.ofReal (Real.Gamma (((d : ℝ) + 1) / 6) / 3) *
        ((ENNReal.ofReal g)⁻¹) ^ (((d : ℝ) + 1) / 6) := by
  have hΓ : 0 < Real.Gamma (((d : ℝ) + 1) / 6) / 3 :=
    div_pos (Real.Gamma_pos_of_pos (by positivity)) (by norm_num)
  rcases hg.eq_or_lt with rfl | hg
  · rw [ENNReal.ofReal_zero, ENNReal.inv_zero, ENNReal.top_rpow_of_pos (by positivity),
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr hΓ).ne']
    exact le_top
  · refine le_of_eq ?_
    have h1 : ∀ a : ℝ, ENNReal.ofReal (|a| ^ d) * ENNReal.ofReal (Real.exp (-(a ^ 6 * g))) =
        (fun t => ENNReal.ofReal (t ^ d * Real.exp (-(t ^ 6 * g)))) |a| := by
      intro a
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 3
      rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, pow_mul, sq_abs]
    simp_rw [h1]
    rw [lintegral_comp_abs (fun t => ENNReal.ofReal (t ^ d * Real.exp (-(t ^ 6 * g))))]
    have hcongr : ∀ t ∈ Ioi (0 : ℝ), t ^ d * Real.exp (-(t ^ 6 * g)) =
        t ^ (d : ℝ) * Real.exp (-g * t ^ (6 : ℝ)) := by
      intro t _
      rw [Real.rpow_natCast, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring_nf
    have hint : IntegrableOn (fun t : ℝ => t ^ (d : ℝ) * Real.exp (-g * t ^ (6 : ℝ))) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith [d.cast_nonneg (α := ℝ)])
        (by norm_num) hg
    rw [setLIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [hcongr t ht],
      ← ofReal_integral_eq_lintegral_ofReal hint
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht =>
          mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le)),
      integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by linarith [d.cast_nonneg (α := ℝ)]) hg]
    rw [← ofReal_rpow_neg_eq hg, ← ENNReal.ofReal_mul hΓ.le,
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [neg_div]
    ring

/-! ### Coordinates `u = Fin.cons (a, β) w` -/

/-- Lebesgue measure on the chart space is an additive Haar measure. -/
instance instIsAddHaarMeasureChart (n : ℕ) :
    (volume : Measure (ℝ × (Fin n → ℝ × ℝ))).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Lebesgue measure on the chart space has no atoms. -/
instance instNullSingletonClassChart (n : ℕ) :
    NullSingletonClass (volume : Measure (ℝ × (Fin n → ℝ × ℝ))) :=
  Measure.prod.instNullSingletonClass_fst (μ := volume) (ν := volume)

/-- Split off the first coordinate `a₀` and the first slope entry `b₀`. -/
noncomputable def splitForms (n : ℕ) :
    (Fin (n + 1) → ℝ × ℝ) ≃ᵐ ℝ × (ℝ × (Fin n → ℝ × ℝ)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ × ℝ) 0).trans
    MeasurableEquiv.prodAssoc

lemma splitForms_symm_apply (n : ℕ) (a b : ℝ) (w : Fin n → ℝ × ℝ) :
    (splitForms n).symm (a, (b, w)) = Fin.cons (a, b) w := by
  simp [splitForms, MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl

lemma measurePreserving_splitForms (n : ℕ) :
    MeasurePreserving (splitForms n) volume volume :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ × ℝ) 0).trans
    volume_preserving_prodAssoc

lemma finrank_chart (n : ℕ) : finrank ℝ (ℝ × (Fin n → ℝ × ℝ)) = 2 * n + 1 := by
  simp [Module.finrank_pi_fintype, Module.finrank_prod]; ring

lemma cons_mem_chartRegion_iff {n : ℕ} (a : ℝ) (v : ℝ × (Fin n → ℝ × ℝ)) :
    (Fin.cons (a, v.1) v.2 : Fin (n + 1) → ℝ × ℝ) ∈ chartRegion n ↔
      v ∈ Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) |a| := by
  rw [mem_closedBall_zero_iff, norm_prod_le_iff, pi_norm_le_iff_of_nonneg (abs_nonneg a)]
  simp only [chartRegion, mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Prod.norm_def, Real.norm_eq_abs, max_le_iff, le_refl, true_and]

/-- The chart function: the coefficient norm of `(x + βy)³ + ∑ ℓ_{w_i}³`. -/
noncomputable def chartG {n : ℕ} (v : ℝ × (Fin n → ℝ × ℝ)) : ℝ :=
  cubeSumSq (Fin.cons ((1 : ℝ), v.1) v.2 : Fin (n + 1) → ℝ × ℝ)

lemma cons_smul_eq {n : ℕ} (a : ℝ) (v : ℝ × (Fin n → ℝ × ℝ)) :
    (Fin.cons (a, (a • v).1) (a • v).2 : Fin (n + 1) → ℝ × ℝ) =
      a • (Fin.cons ((1 : ℝ), v.1) v.2 : Fin (n + 1) → ℝ × ℝ) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp

lemma measurable_chartG {n : ℕ} : Measurable (chartG (n := n)) := by
  have : Measurable fun v : ℝ × (Fin n → ℝ × ℝ) =>
      (Fin.cons ((1 : ℝ), v.1) v.2 : Fin (n + 1) → ℝ × ℝ) := by
    refine measurable_pi_iff.mpr fun j => ?_
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Fin.cons_zero]; fun_prop
    · simp only [Fin.cons_succ]; fun_prop
  exact measurable_cubeSumSq.comp this

/-- The inner integral over the slice `a₀ = a`, rescaled to the unit ball. -/
lemma lintegral_slice_le {n : ℕ} (a : ℝ) :
    ∫⁻ v, (Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) |a|).indicator
        (fun v => expG (Fin.cons (a, v.1) v.2 : Fin (n + 1) → ℝ × ℝ)) v ≤
      ENNReal.ofReal (|a| ^ (2 * n + 1)) *
        ∫⁻ v, (Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) 1).indicator
          (fun v => ENNReal.ofReal (Real.exp (-(a ^ 6 * chartG v)))) v := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [abs_zero, lintegral_indicator Metric.isClosed_closedBall.measurableSet,
      Metric.closedBall_zero, setLIntegral_measure_zero _ _ (measure_singleton _)]
    exact bot_le
  · set φ := (Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) |a|).indicator
        (fun v => expG (Fin.cons (a, v.1) v.2 : Fin (n + 1) → ℝ × ℝ)) with hφ
    have hscale := lintegral_comp_smul_eq volume φ ha
    rw [finrank_chart] at hscale
    have hcomp : ∀ v, φ (a • v) = (Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) 1).indicator
        (fun v => ENNReal.ofReal (Real.exp (-(a ^ 6 * chartG v)))) v := by
      intro v
      have hmem : a • v ∈ Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) |a| ↔
          v ∈ Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) 1 := by
        simp only [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs]
        constructor
        · intro h; exact (mul_le_iff_le_one_right (abs_pos.mpr ha)).mp h
        · intro h; exact (mul_le_iff_le_one_right (abs_pos.mpr ha)).mpr h
      by_cases hv : v ∈ Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) 1
      · rw [hφ, indicator_of_mem (hmem.mpr hv), indicator_of_mem hv]
        simp only [expG, cons_smul_eq, cubeSumSq_smul, chartG]
      · rw [hφ, indicator_of_notMem (fun h => hv (hmem.mp h)), indicator_of_notMem hv]
    simp only [hcomp] at hscale
    rw [hscale, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), abs_inv, abs_pow,
      mul_inv_cancel₀ (pow_ne_zero _ (abs_pos.mpr ha).ne'), ENNReal.ofReal_one, one_mul]

lemma indicator_eq_indicator_one_mul {α : Type*} (s : Set α) (f : α → ℝ≥0∞) (x : α) :
    s.indicator f x = s.indicator 1 x * f x := by
  by_cases hx : x ∈ s <;> simp [hx]

lemma chartG_nonneg {n : ℕ} (v : ℝ × (Fin n → ℝ × ℝ)) : 0 ≤ chartG v := cubeSumSq_nonneg _

/-- **Radial integration on the chart region.** -/
theorem setLIntegral_chartRegion_le (n : ℕ) :
    ∫⁻ u in chartRegion n, expG u ≤
      ENNReal.ofReal (Real.Gamma (((n : ℝ) + 1) / 3) / 3) *
        ∫⁻ v in Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) 1,
          ((ENNReal.ofReal (chartG v))⁻¹) ^ (((n : ℝ) + 1) / 3) := by
  set B1 := Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) 1 with hB1
  set d := 2 * n + 1 with hd
  have hexp : ((d : ℕ) : ℝ) + 1 = 2 * ((n : ℝ) + 1) := by rw [hd]; push_cast; ring
  have hexp' : (((d : ℕ) : ℝ) + 1) / 6 = ((n : ℝ) + 1) / 3 := by rw [hexp]; ring
  have hmeasF : Measurable fun p : ℝ × (ℝ × (Fin n → ℝ × ℝ)) =>
      ENNReal.ofReal (|p.1| ^ d) * (B1.indicator 1 p.2 *
        ENNReal.ofReal (Real.exp (-(p.1 ^ 6 * chartG p.2)))) := by
    refine Measurable.mul (by fun_prop) (Measurable.mul ?_ ?_)
    · exact (measurable_one.indicator Metric.isClosed_closedBall.measurableSet).comp measurable_snd
    · exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        ((measurable_fst.pow_const 6).mul (measurable_chartG.comp measurable_snd)).neg)
  calc ∫⁻ u in chartRegion n, expG u
      = ∫⁻ u, (chartRegion n).indicator expG u :=
        (lintegral_indicator (measurableSet_chartRegion n) _).symm
    _ = ∫⁻ x, (chartRegion n).indicator expG ((splitForms n).symm x) :=
        ((measurePreserving_splitForms n).symm.lintegral_comp_emb
          (splitForms n).symm.measurableEmbedding _).symm
    _ ≤ ∫⁻ a, ∫⁻ v, (chartRegion n).indicator expG ((splitForms n).symm (a, v)) := by
        rw [Measure.volume_eq_prod]; exact lintegral_prod_le _
    _ = ∫⁻ a, ∫⁻ v, (Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) |a|).indicator
          (fun v => expG (Fin.cons (a, v.1) v.2 : Fin (n + 1) → ℝ × ℝ)) v := by
        refine lintegral_congr fun a => lintegral_congr fun v => ?_
        rw [show v = (v.1, v.2) from rfl, splitForms_symm_apply]
        by_cases hv : v ∈ Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) |a|
        · rw [indicator_of_mem ((cons_mem_chartRegion_iff a v).mpr hv), indicator_of_mem hv]
        · rw [indicator_of_notMem (fun h => hv ((cons_mem_chartRegion_iff a v).mp h)),
            indicator_of_notMem hv]
    _ ≤ ∫⁻ a, ENNReal.ofReal (|a| ^ d) *
          ∫⁻ v, B1.indicator (fun v => ENNReal.ofReal (Real.exp (-(a ^ 6 * chartG v)))) v :=
        lintegral_mono fun a => lintegral_slice_le a
    _ = ∫⁻ a, ∫⁻ v, ENNReal.ofReal (|a| ^ d) * (B1.indicator 1 v *
          ENNReal.ofReal (Real.exp (-(a ^ 6 * chartG v)))) := by
        refine lintegral_congr fun a => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun v => ?_
        congr 1
        exact indicator_eq_indicator_one_mul B1 _ v
    _ = ∫⁻ v, ∫⁻ a, ENNReal.ofReal (|a| ^ d) * (B1.indicator 1 v *
          ENNReal.ofReal (Real.exp (-(a ^ 6 * chartG v)))) := by
        refine lintegral_lintegral_swap ?_
        have : Function.uncurry (fun (a : ℝ) (v : ℝ × (Fin n → ℝ × ℝ)) =>
            ENNReal.ofReal (|a| ^ d) * (B1.indicator 1 v *
              ENNReal.ofReal (Real.exp (-(a ^ 6 * chartG v))))) =
            fun p : ℝ × (ℝ × (Fin n → ℝ × ℝ)) => ENNReal.ofReal (|p.1| ^ d) *
              (B1.indicator 1 p.2 * ENNReal.ofReal (Real.exp (-(p.1 ^ 6 * chartG p.2)))) := rfl
        rw [this]
        exact hmeasF.aemeasurable
    _ = ∫⁻ v, B1.indicator 1 v * ∫⁻ a, ENNReal.ofReal (|a| ^ d) *
          ENNReal.ofReal (Real.exp (-(a ^ 6 * chartG v))) := by
        refine lintegral_congr fun v => ?_
        rw [← lintegral_const_mul' _ _ (by by_cases hv : v ∈ B1 <;> simp [hv])]
        refine lintegral_congr fun a => ?_
        ring
    _ ≤ ∫⁻ v, B1.indicator 1 v * (ENNReal.ofReal (Real.Gamma (((n : ℝ) + 1) / 3) / 3) *
          ((ENNReal.ofReal (chartG v))⁻¹) ^ (((n : ℝ) + 1) / 3)) := by
        refine lintegral_mono fun v => ?_
        have := lintegral_radial_le d (chartG_nonneg v)
        rw [hexp'] at this
        gcongr
    _ = ENNReal.ofReal (Real.Gamma (((n : ℝ) + 1) / 3) / 3) *
          ∫⁻ v in B1, ((ENNReal.ofReal (chartG v))⁻¹) ^ (((n : ℝ) + 1) / 3) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ← lintegral_indicator Metric.isClosed_closedBall.measurableSet]
        refine lintegral_congr fun v => ?_
        by_cases hv : v ∈ Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) 1 <;> simp [hv, hB1]

/-! ### The shear `y ↦ y - βx` -/

/-- Substitute `y ↦ y - βx` in every form: `(a, b) ↦ (a, b - β a)`. -/
def shear {m : ℕ} (β : ℝ) (u : Fin m → ℝ × ℝ) : Fin m → ℝ × ℝ :=
  fun i => ((u i).1, (u i).2 - β * (u i).1)

lemma cubeSum_shear_zero {m : ℕ} (β : ℝ) (u : Fin m → ℝ × ℝ) :
    cubeSum (shear β u) 0 = cubeSum u 0 := by
  simp [cubeSum, shear]

lemma cubeSum_shear_one {m : ℕ} (β : ℝ) (u : Fin m → ℝ × ℝ) :
    cubeSum (shear β u) 1 = cubeSum u 1 - β * cubeSum u 0 := by
  simp only [cubeSum, shear, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma cubeSum_shear_two {m : ℕ} (β : ℝ) (u : Fin m → ℝ × ℝ) :
    cubeSum (shear β u) 2 = cubeSum u 2 - 2 * β * cubeSum u 1 + β ^ 2 * cubeSum u 0 := by
  simp only [cubeSum, shear, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one,
    Matrix.cons_val_zero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma cubeSum_shear_three {m : ℕ} (β : ℝ) (u : Fin m → ℝ × ℝ) :
    cubeSum (shear β u) 3 = cubeSum u 3 - 3 * β * cubeSum u 2 + 3 * β ^ 2 * cubeSum u 1 -
      β ^ 3 * cubeSum u 0 := by
  simp only [cubeSum, shear, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one,
    Matrix.cons_val_zero]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma sq_add_le_two (p q : ℝ) : (p + q) ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) := by
  nlinarith [sq_nonneg (p - q)]

lemma sq_add_le_three (p q r : ℝ) : (p + q + r) ^ 2 ≤ 3 * (p ^ 2 + q ^ 2 + r ^ 2) := by
  nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (p - r)]

lemma sq_add_le_four (p q r t : ℝ) :
    (p + q + r + t) ^ 2 ≤ 4 * (p ^ 2 + q ^ 2 + r ^ 2 + t ^ 2) := by
  nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (p - r), sq_nonneg (p - t),
    sq_nonneg (q - t), sq_nonneg (r - t)]

/-- A shear with `|β| ≤ 1` changes the coefficient norm by a factor at most `80`. -/
lemma cubeSumSq_shear_le {m : ℕ} {β : ℝ} (hβ : |β| ≤ 1) (u : Fin m → ℝ × ℝ) :
    cubeSumSq (shear β u) ≤ 80 * cubeSumSq u := by
  have hβ2 : β ^ 2 ≤ 1 := by nlinarith [sq_abs β, abs_nonneg β]
  have hsc : ∀ (c x : ℝ), c ^ 2 ≤ 1 → (c * x) ^ 2 ≤ x ^ 2 := fun c x hc => by
    rw [mul_pow]; exact mul_le_of_le_one_left (sq_nonneg x) hc
  have hβ4 : (β ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg β]
  have hβ6 : (β ^ 3) ^ 2 ≤ 1 := by
    have : (β ^ 3) ^ 2 = (β ^ 2) ^ 3 := by ring
    rw [this]; exact pow_le_one₀ (sq_nonneg β) hβ2
  set x0 := cubeSum u 0
  set x1 := cubeSum u 1
  set x2 := cubeSum u 2
  set x3 := cubeSum u 3
  have hG : cubeSumSq u = x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 := by
    simp only [cubeSumSq, Fin.sum_univ_four]; rfl
  have hG' : cubeSumSq (shear β u) = x0 ^ 2 + (x1 - β * x0) ^ 2 +
      (x2 - 2 * β * x1 + β ^ 2 * x0) ^ 2 +
      (x3 - 3 * β * x2 + 3 * β ^ 2 * x1 - β ^ 3 * x0) ^ 2 := by
    simp only [cubeSumSq, Fin.sum_univ_four, Fin.isValue]
    rw [cubeSum_shear_zero, cubeSum_shear_one, cubeSum_shear_two, cubeSum_shear_three]
  have e1 := sq_add_le_two x1 (-(β * x0))
  have e2 := sq_add_le_three x2 (-(2 * (β * x1))) ((β ^ 2) * x0)
  have e3 := sq_add_le_four x3 (-(3 * (β * x2))) (3 * ((β ^ 2) * x1)) (-((β ^ 3) * x0))
  have b1 := hsc β x0 hβ2
  have b2 := hsc β x1 hβ2
  have b3 := hsc β x2 hβ2
  have b4 := hsc (β ^ 2) x0 hβ4
  have b5 := hsc (β ^ 2) x1 hβ4
  have b6 := hsc (β ^ 3) x0 hβ6
  rw [hG, hG']
  have r1 : (x1 - β * x0) = x1 + -(β * x0) := by ring
  have r2 : (x2 - 2 * β * x1 + β ^ 2 * x0) = x2 + -(2 * (β * x1)) + (β ^ 2) * x0 := by ring
  have r3 : (x3 - 3 * β * x2 + 3 * β ^ 2 * x1 - β ^ 3 * x0) =
      x3 + -(3 * (β * x2)) + 3 * ((β ^ 2) * x1) + -((β ^ 3) * x0) := by ring
  rw [r1, r2, r3]
  simp only [neg_sq, mul_pow] at e1 e2 e3 ⊢
  simp only [mul_pow] at b1 b2 b3 b4 b5 b6
  nlinarith [sq_nonneg x0, sq_nonneg x1, sq_nonneg x2, sq_nonneg x3]

lemma shear_cons {n : ℕ} (β : ℝ) (w : Fin n → ℝ × ℝ) :
    shear β (Fin.cons ((1 : ℝ), β) w : Fin (n + 1) → ℝ × ℝ) =
      Fin.cons ((1 : ℝ), (0 : ℝ)) (shear β w) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [shear]
  · simp [shear]

lemma measurePreserving_shear_pair (β : ℝ) :
    MeasurePreserving (fun z : ℝ × ℝ => (z.1, z.2 - β * z.1)) volume volume := by
  have := (MeasurePreserving.id (volume : Measure ℝ)).skew_product
    (g := fun (a y : ℝ) => y - β * a) (by fun_prop)
    (Filter.Eventually.of_forall fun a => (measurePreserving_sub_right volume (β * a)).map_eq)
  exact this

lemma measurePreserving_shear {m : ℕ} (β : ℝ) :
    MeasurePreserving (shear (m := m) β) volume volume :=
  measurePreserving_pi (fun _ => (volume : Measure (ℝ × ℝ))) (fun _ => volume)
    (fun _ => measurePreserving_shear_pair β)

lemma norm_shear_le {m : ℕ} {β : ℝ} (hβ : |β| ≤ 1) {w : Fin m → ℝ × ℝ} (hw : ‖w‖ ≤ 1) :
    ‖shear β w‖ ≤ 2 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  have hi := (norm_le_pi_norm w i).trans hw
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff] at hi
  rw [shear, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff]
  refine ⟨by linarith [hi.1], ?_⟩
  calc |(w i).2 - β * (w i).1| ≤ |(w i).2| + |β| * |(w i).1| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ ≤ 1 + 1 * 1 := by gcongr <;> linarith [hi.1, hi.2]
    _ = 2 := by norm_num

/-- The normalized chart function: the coefficient norm of `x³ + ∑ ℓ_{w_i}³`. -/
noncomputable def chartN {n : ℕ} (w : Fin n → ℝ × ℝ) : ℝ :=
  cubeSumSq (Fin.cons ((1 : ℝ), (0 : ℝ)) w : Fin (n + 1) → ℝ × ℝ)

lemma measurable_chartN {n : ℕ} : Measurable (chartN (n := n)) := by
  have : Measurable fun w : Fin n → ℝ × ℝ =>
      (Fin.cons ((1 : ℝ), (0 : ℝ)) w : Fin (n + 1) → ℝ × ℝ) := by
    refine measurable_pi_iff.mpr fun j => ?_
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Fin.cons_zero]; fun_prop
    · simp only [Fin.cons_succ]; fun_prop
  exact measurable_cubeSumSq.comp this

lemma chartG_ge {n : ℕ} {β : ℝ} (hβ : |β| ≤ 1) (w : Fin n → ℝ × ℝ) :
    chartN (shear β w) / 80 ≤ chartG (β, w) := by
  have := cubeSumSq_shear_le hβ (Fin.cons ((1 : ℝ), β) w : Fin (n + 1) → ℝ × ℝ)
  rw [shear_cons] at this
  simp only [chartN, chartG]
  linarith

/-- **Shear step.** -/
theorem setLIntegral_chartG_le (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ v in Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) 1,
        ((ENNReal.ofReal (chartG v))⁻¹) ^ s ≤
      2 * (80 : ℝ≥0∞) ^ s * ∫⁻ w in Metric.closedBall (0 : Fin n → ℝ × ℝ) 2,
        ((ENNReal.ofReal (chartN w))⁻¹) ^ s := by
  set Φ : (Fin n → ℝ × ℝ) → ℝ≥0∞ := fun w => ((ENNReal.ofReal (chartN w))⁻¹) ^ s with hΦ
  have hΦm : Measurable Φ :=
    ((ENNReal.measurable_ofReal.comp measurable_chartN).inv).pow_const s
  set B2 := Metric.closedBall (0 : Fin n → ℝ × ℝ) 2 with hB2
  have h80 : (80 : ℝ≥0∞) ^ s ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hs (by simp)
  have hpt : ∀ (b : ℝ) (w : Fin n → ℝ × ℝ),
      (Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) 1).indicator
        (fun v => ((ENNReal.ofReal (chartG v))⁻¹) ^ s) (b, w) ≤
      (Icc (-1 : ℝ) 1).indicator 1 b * ((80 : ℝ≥0∞) ^ s * B2.indicator Φ (shear b w)) := by
    intro b w
    by_cases hv : (b, w) ∈ Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) 1
    · rw [indicator_of_mem hv]
      rw [mem_closedBall_zero_iff, norm_prod_le_iff, Real.norm_eq_abs] at hv
      have hb : b ∈ Icc (-1 : ℝ) 1 := abs_le.mp hv.1
      have hsh : shear b w ∈ B2 := by
        rw [hB2, mem_closedBall_zero_iff]; exact norm_shear_le hv.1 hv.2
      rw [indicator_of_mem hb, indicator_of_mem hsh, Pi.one_apply, one_mul, hΦ]
      have hle : ENNReal.ofReal (chartN (shear b w) / 80) ≤ ENNReal.ofReal (chartG (b, w)) :=
        ENNReal.ofReal_le_ofReal (chartG_ge hv.1 w)
      calc ((ENNReal.ofReal (chartG (b, w)))⁻¹) ^ s
          ≤ ((ENNReal.ofReal (chartN (shear b w) / 80))⁻¹) ^ s :=
            ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.mpr hle) hs
        _ = (80 : ℝ≥0∞) ^ s * ((ENNReal.ofReal (chartN (shear b w)))⁻¹) ^ s := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.inv_div (by simp) (by simp),
              div_eq_mul_inv, ENNReal.mul_rpow_of_nonneg _ _ hs]
            simp
    · rw [indicator_of_notMem hv]; exact bot_le
  calc ∫⁻ v in Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) 1,
        ((ENNReal.ofReal (chartG v))⁻¹) ^ s
      = ∫⁻ v, (Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) 1).indicator
          (fun v => ((ENNReal.ofReal (chartG v))⁻¹) ^ s) v :=
        (lintegral_indicator Metric.isClosed_closedBall.measurableSet _).symm
    _ ≤ ∫⁻ b, ∫⁻ w, (Metric.closedBall (0 : ℝ × (Fin n → ℝ × ℝ)) 1).indicator
          (fun v => ((ENNReal.ofReal (chartG v))⁻¹) ^ s) (b, w) := by
        rw [Measure.volume_eq_prod]; exact lintegral_prod_le _
    _ ≤ ∫⁻ b, ∫⁻ w, (Icc (-1 : ℝ) 1).indicator 1 b *
          ((80 : ℝ≥0∞) ^ s * B2.indicator Φ (shear b w)) :=
        lintegral_mono fun b => lintegral_mono fun w => hpt b w
    _ = ∫⁻ b, (Icc (-1 : ℝ) 1).indicator 1 b * ((80 : ℝ≥0∞) ^ s * ∫⁻ w, B2.indicator Φ w) := by
        refine lintegral_congr fun b => ?_
        rw [lintegral_const_mul' _ _ (by
            by_cases hb : b ∈ Icc (-1 : ℝ) 1 <;> simp [hb]),
          lintegral_const_mul' _ _ h80,
          (measurePreserving_shear b).lintegral_comp (hΦm.indicator
            Metric.isClosed_closedBall.measurableSet)]
    _ = 2 * (80 : ℝ≥0∞) ^ s * ∫⁻ w in B2, Φ w := by
        rw [lintegral_mul_const _ (measurable_one.indicator measurableSet_Icc),
          lintegral_indicator_one measurableSet_Icc, Real.volume_Icc,
          lintegral_indicator Metric.isClosed_closedBall.measurableSet]
        norm_num
        ring

/-- **Chart reduction.** If `∫_{‖w‖ ≤ 2} G_{n+1}(x, w)^{-(n+1)/3} < ∞`, then
`∫ e^{-G_{n+1}} < ∞` over all of `Fin (n + 1) → ℝ × ℝ`. -/
theorem lintegral_exp_lt_top_of_chart (n : ℕ)
    (h : ∫⁻ w in Metric.closedBall (0 : Fin n → ℝ × ℝ) 2,
      ((ENNReal.ofReal (chartN w))⁻¹) ^ (((n : ℝ) + 1) / 3) < ⊤) :
    ∫⁻ u : Fin (n + 1) → ℝ × ℝ, ENNReal.ofReal (Real.exp (-cubeSumSq u)) < ⊤ := by
  have hs : (0 : ℝ) ≤ ((n : ℝ) + 1) / 3 := by positivity
  have h80 : (80 : ℝ≥0∞) ^ (((n : ℝ) + 1) / 3) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hs (by simp)
  calc ∫⁻ u : Fin (n + 1) → ℝ × ℝ, ENNReal.ofReal (Real.exp (-cubeSumSq u))
      = ∫⁻ u, expG u := rfl
    _ ≤ (2 * (n + 1) : ℝ≥0∞) * ∫⁻ u in chartRegion n, expG u :=
        lintegral_le_mul_setLIntegral_chartRegion n
    _ ≤ (2 * (n + 1) : ℝ≥0∞) * (ENNReal.ofReal (Real.Gamma (((n : ℝ) + 1) / 3) / 3) *
          (2 * (80 : ℝ≥0∞) ^ (((n : ℝ) + 1) / 3) *
            ∫⁻ w in Metric.closedBall (0 : Fin n → ℝ × ℝ) 2,
              ((ENNReal.ofReal (chartN w))⁻¹) ^ (((n : ℝ) + 1) / 3))) := by
        gcongr
        exact (setLIntegral_chartRegion_le n).trans
          (mul_le_mul_right (setLIntegral_chartG_le n hs) _)
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (by simp [ENNReal.mul_lt_top])
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) h80.lt_top) h))

/-- **Chart reduction for `CubeSumUpper`.** -/
theorem cubeSumUpper_of_chart (n : ℕ)
    (h : ∫⁻ w in Metric.closedBall (0 : Fin n → ℝ × ℝ) 2,
      ((ENNReal.ofReal (chartN w))⁻¹) ^ (((n : ℝ) + 1) / 3) < ⊤) :
    CubeSumUpper (n + 1) :=
  cubeSumUpper_of_lintegral_lt_top (lintegral_exp_lt_top_of_chart n h)

end VectorSLT.IdentityGroup.Cubes
