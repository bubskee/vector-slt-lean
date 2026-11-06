/-
Milestone B: Lemma M2 (planar quadratic sublevel sets).

Paper (cubic-chaos `shear_position_one_exact.md` §4, Lemma M2):
  Let Q(β) = βᵀMβ + L·β + k on ℝ², M real symmetric, ‖M‖ ≤ Λ, det M ≠ 0, L and k
  arbitrary. Then for every square S of side 2ε and every σ > 0,
    |{β ∈ S : |Q(β)| ≤ σ}| ≤ C_{Λ,ε} σ (1 + log⁺(1/σ)) / √|det M|.

The Lean proof differs from the paper's route. It does not diagonalize. It uses
Fubini in the original coordinates: each horizontal slice is a 1-D quadratic sublevel set,
of measure ≤ 8σ/√|Δ(y)| (`volume_abs_quad_le`). The slice discriminant Δ(y) is a quadratic
in y with leading coefficient −4 det M, so |Δ(y)| ≥ 4|det M| · dist(y, roots)². The
y-integral is then two copies of the hyperbola log `lintegral_min_div_abs_le`.
-/
import VectorSLT.Sublevel1D

namespace VectorSLT

open MeasureTheory Set Matrix

/-- The planar quadratic `Q(β) = βᵀ M β + L · β + k`. -/
def quadForm (M : Matrix (Fin 2) (Fin 2) ℝ) (L : Fin 2 → ℝ) (k : ℝ) (β : Fin 2 → ℝ) : ℝ :=
  β ⬝ᵥ (M *ᵥ β) + L ⬝ᵥ β + k

/-- The closed axis-parallel square of side `2ε` centred at `c`. -/
def square (c : Fin 2 → ℝ) (ε : ℝ) : Set (Fin 2 → ℝ) :=
  Set.pi univ fun i => Icc (c i - ε) (c i + ε)

/-- The constant of Lemma M2 (explicit): `16 (1 + log 2 + log (1 + √2 ε² Λ))`. -/
noncomputable def M2const (Λ ε : ℝ) : ℝ :=
  16 * (1 + Real.log 2 + Real.log (1 + √2 * ε ^ 2 * Λ))

theorem quadForm_expand (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.IsSymm) (L : Fin 2 → ℝ)
    (k : ℝ) (β : Fin 2 → ℝ) :
    quadForm M L k β = M 0 0 * β 0 ^ 2 + (2 * M 0 1 * β 1 + L 0) * β 0 +
      (M 1 1 * β 1 ^ 2 + L 1 * β 1 + k) := by
  have h10 : M 1 0 = M 0 1 := hM.apply 0 1
  simp only [quadForm, dotProduct, mulVec, Fin.sum_univ_two, h10]
  ring

/-- A real quadratic with nonzero leading coefficient dominates `|A| dist(y, roots)²`. -/
theorem quad_ge_dist_roots (A b c : ℝ) (hA : A ≠ 0) :
    ∃ r₁ r₂ : ℝ, ∀ y : ℝ,
      |A| * min |y - r₁| |y - r₂| ^ 2 ≤ |A * y ^ 2 + b * y + c| := by
  set y₀ := -b / (2 * A)
  set e := (b ^ 2 - 4 * A * c) / (4 * A ^ 2)
  have hfac : ∀ y, A * y ^ 2 + b * y + c = A * ((y - y₀) ^ 2 - e) := by
    intro y; simp only [y₀, e]; field_simp; ring
  rcases le_or_gt 0 e with he | he
  · refine ⟨y₀ + √e, y₀ - √e, fun y => ?_⟩
    rw [hfac, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg A)
    have : (y - y₀) ^ 2 - e = (y - (y₀ + √e)) * (y - (y₀ - √e)) := by
      have := Real.sq_sqrt he; nlinarith
    rw [this, abs_mul, sq]
    exact mul_le_mul (min_le_left _ _) (min_le_right _ _) (by positivity) (abs_nonneg _)
  · refine ⟨y₀, y₀, fun y => ?_⟩
    rw [hfac, abs_mul, min_self, sq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg A)
    rw [abs_of_pos (by nlinarith [sq_nonneg (y - y₀)])]
    linarith

/-- `|det M| ≤ 2Λ²` under the entrywise bound. -/
theorem abs_det_le (M : Matrix (Fin 2) (Fin 2) ℝ) {Λ : ℝ} (hMb : ∀ i j, |M i j| ≤ Λ) :
    |M.det| ≤ 2 * Λ ^ 2 := by
  rw [det_fin_two]
  have h := fun i j => hMb i j
  have h0 : 0 ≤ Λ := (abs_nonneg _).trans (hMb 0 0)
  calc |M 0 0 * M 1 1 - M 0 1 * M 1 0| ≤ |M 0 0| * |M 1 1| + |M 0 1| * |M 1 0| := by
        rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
    _ ≤ Λ * Λ + Λ * Λ := add_le_add (mul_le_mul (h 0 0) (h 1 1) (abs_nonneg _) h0)
        (mul_le_mul (h 0 1) (h 1 0) (abs_nonneg _) h0)
    _ = 2 * Λ ^ 2 := by ring

theorem log_one_add_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ Real.log (1 + x) :=
  Real.log_nonneg (by linarith)

/-- The closing real inequality of Lemma M2. -/
theorem M2_final_ineq {Λ ε σ D : ℝ} (hΛ : 0 ≤ Λ) (hε : 0 < ε) (hσ : 0 < σ) (hD : 0 < |D|)
    (hDΛ : |D| ≤ 2 * Λ ^ 2) :
    2 * (4 * σ / √|D|) * (1 + Real.log (1 + 2 * ε * (2 * ε) / (4 * σ / √|D|))) +
      2 * (4 * σ / √|D|) * (1 + Real.log (1 + 2 * ε * (2 * ε) / (4 * σ / √|D|))) ≤
      M2const Λ ε * (σ * (1 + Real.posLog (1 / σ))) / √|D| := by
  have hsD : 0 < √|D| := Real.sqrt_pos.mpr hD
  have hsDΛ : √|D| ≤ √2 * Λ := by
    rw [show √2 * Λ = √(2 * Λ ^ 2) by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hΛ]]
    exact Real.sqrt_le_sqrt hDΛ
  set a := √2 * ε ^ 2 * Λ
  set x := 1 / σ
  have ha : 0 ≤ a := by positivity
  have hx : 0 < x := by positivity
  have hratio : 2 * ε * (2 * ε) / (4 * σ / √|D|) ≤ a * x := by
    simp only [a, x]
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hsDΛ (show 0 ≤ ε ^ 2 by positivity)]
  have hlog : Real.log (1 + 2 * ε * (2 * ε) / (4 * σ / √|D|)) ≤
      Real.log (1 + a) + Real.posLog x + Real.log 2 := by
    calc Real.log (1 + 2 * ε * (2 * ε) / (4 * σ / √|D|)) ≤ Real.log ((1 + a) * (1 + x)) := by
          apply Real.log_le_log (by positivity)
          nlinarith [mul_nonneg ha hx.le]
      _ = Real.log (1 + a) + Real.log (1 + x) :=
          Real.log_mul (by positivity) (by positivity)
      _ ≤ _ := by have := Real.log_one_add_le_posLog (x := x); linarith
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hla : 0 ≤ Real.log (1 + a) := log_one_add_nonneg a ha
  have hP : 0 ≤ Real.posLog x := Real.posLog_nonneg
  -- reduce to the bracket inequality
  have hbr : 1 + Real.log (1 + 2 * ε * (2 * ε) / (4 * σ / √|D|)) ≤
      (1 + Real.log 2 + Real.log (1 + a)) * (1 + Real.posLog x) := by
    nlinarith [mul_nonneg (add_nonneg hl2 hla) hP]
  have hbr0 : 0 ≤ 1 + Real.log (1 + 2 * ε * (2 * ε) / (4 * σ / √|D|)) := by
    have := log_one_add_nonneg (2 * ε * (2 * ε) / (4 * σ / √|D|)) (by positivity); linarith
  simp only [M2const]
  rw [show 16 * (1 + Real.log 2 + Real.log (1 + √2 * ε ^ 2 * Λ)) * (σ * (1 + Real.posLog (1 / σ)))
      / √|D| = (16 * σ / √|D|) * ((1 + Real.log 2 + Real.log (1 + a)) * (1 + Real.posLog x)) by
      simp only [a, x]; ring]
  have h16 : 0 ≤ 16 * σ / √|D| := by positivity
  calc _ = (16 * σ / √|D|) * (1 + Real.log (1 + 2 * ε * (2 * ε) / (4 * σ / √|D|))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbr h16

/-- **Lemma M2, explicit-constant form.** -/
theorem lemmaM2_explicit {Λ ε : ℝ} (hΛ : 0 ≤ Λ) (hε : 0 < ε)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.IsSymm) (hMb : ∀ i j, |M i j| ≤ Λ)
    (hdet : M.det ≠ 0) (L : Fin 2 → ℝ) (k : ℝ) (c : Fin 2 → ℝ) {σ : ℝ} (hσ : 0 < σ) :
    volume {β | β ∈ square c ε ∧ |quadForm M L k β| ≤ σ} ≤
      ENNReal.ofReal (M2const Λ ε * (σ * (1 + Real.posLog (1 / σ))) / √|M.det|) := by
  -- notation
  set D := M.det with hD
  have hD' : D = M 0 0 * M 1 1 - M 0 1 ^ 2 := by
    rw [hD, det_fin_two, hM.apply 0 1]; ring
  have hDpos : 0 < |D| := abs_pos.mpr hdet
  have hsD : 0 < √|D| := Real.sqrt_pos.mpr hDpos
  set a := M 0 0
  set Bf : ℝ → ℝ := fun y => 2 * M 0 1 * y + L 0
  set Cf : ℝ → ℝ := fun y => M 1 1 * y ^ 2 + L 1 * y + k
  set q : ℝ → ℝ → ℝ := fun x y => a * x ^ 2 + Bf y * x + Cf y
  set Δ : ℝ → ℝ := fun y => Bf y ^ 2 - 4 * a * Cf y
  have hΔ : ∀ y, Δ y = (-4 * D) * y ^ 2 + (4 * M 0 1 * L 0 - 4 * a * L 1) * y +
      (L 0 ^ 2 - 4 * a * k) := by
    intro y; simp only [Δ, Bf, Cf, hD', a]; ring
  obtain ⟨r₁, r₂, hroots⟩ := quad_ge_dist_roots (-4 * D)
    (4 * M 0 1 * L 0 - 4 * a * L 1) (L 0 ^ 2 - 4 * a * k) (by simpa using hdet)
  set K := 4 * σ / √|D|
  have hK : 0 < K := by positivity
  -- transport to ℝ × ℝ
  set I₀ := Icc (c 0 - ε) (c 0 + ε)
  set I₁ := Icc (c 1 - ε) (c 1 + ε)
  set t : Set (ℝ × ℝ) := (I₀ ×ˢ I₁) ∩ {p | |q p.1 p.2| ≤ σ}
  have hst : {β | β ∈ square c ε ∧ |quadForm M L k β| ≤ σ} =
      MeasurableEquiv.finTwoArrow ⁻¹' t := by
    ext β
    simp only [square, mem_pi, mem_univ, forall_const, Fin.forall_fin_two, mem_ofPred_eq,
      MeasurableEquiv.finTwoArrow_apply, mem_preimage, t, mem_inter_iff, mem_prod, I₀, I₁,
      q, Bf, Cf, a, quadForm_expand M hM]
  have htm : MeasurableSet t :=
    (measurableSet_Icc.prod measurableSet_Icc).inter
      (measurableSet_le (by fun_prop) measurable_const)
  rw [hst, (volume_preserving_finTwoArrow ℝ).measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_apply_symm htm]
  -- slice bound
  set g : ℝ → ENNReal := fun y =>
    min (ENNReal.ofReal (2 * ε)) (ENNReal.ofReal K / ENNReal.ofReal |y - r₁|) +
    min (ENNReal.ofReal (2 * ε)) (ENNReal.ofReal K / ENNReal.ofReal |y - r₂|)
  have hslice : ∀ y, volume ((fun x => (x, y)) ⁻¹' t) ≤ I₁.indicator g y := by
    intro y
    by_cases hy : y ∈ I₁
    · rw [indicator_of_mem hy]
      have hsub1 : (fun x => (x, y)) ⁻¹' t ⊆ I₀ := fun x hx => hx.1.1
      have hsub2 : (fun x => (x, y)) ⁻¹' t ⊆ {x | |a * x ^ 2 + Bf y * x + Cf y| ≤ σ} :=
        fun x hx => hx.2
      have hv0 : volume ((fun x => (x, y)) ⁻¹' t) ≤ ENNReal.ofReal (2 * ε) :=
        (measure_mono hsub1).trans (by rw [Real.volume_Icc]; apply le_of_eq; congr 1; ring)
      -- which root is nearer
      have key : ∀ r : ℝ, min |y - r₁| |y - r₂| = |y - r| →
          volume ((fun x => (x, y)) ⁻¹' t) ≤
            min (ENNReal.ofReal (2 * ε)) (ENNReal.ofReal K / ENNReal.ofReal |y - r|) := by
        intro r hr
        refine le_min hv0 ?_
        rcases eq_or_lt_of_le (abs_nonneg (y - r)) with h0 | hpos
        · rw [← h0, ENNReal.ofReal_zero, ENNReal.div_zero (by simp [hK])]; exact le_top
        · have hm := hroots y
          rw [← hΔ y, hr] at hm
          have hΔpos : 0 < |Δ y| := lt_of_lt_of_le (by positivity) hm
          refine (measure_mono hsub2).trans ((volume_abs_quad_le_of_ne a (Bf y) (Cf y) σ hσ.le
            (abs_pos.mp hΔpos)).trans ?_)
          rw [← ENNReal.ofReal_div_of_pos hpos]
          apply ENNReal.ofReal_le_ofReal
          -- 8σ/√|Δ| ≤ K/|y - r|  ⟸  2√|D| |y - r| ≤ √|Δ|
          have hsq : 2 * √|D| * |y - r| ≤ √|Δ y| := by
            rw [show 2 * √|D| * |y - r| = √(|-4 * D| * |y - r| ^ 2) by
              rw [Real.sqrt_mul (abs_nonneg _), Real.sqrt_sq (abs_nonneg _), abs_mul,
                Real.sqrt_mul (abs_nonneg _)]
              norm_num]
            exact Real.sqrt_le_sqrt hm
          have hsΔ : 0 < √|Δ y| := Real.sqrt_pos.mpr hΔpos
          simp only [K]
          rw [div_div, div_le_div_iff₀ hsΔ (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hsq (show (0:ℝ) ≤ 4 * σ by positivity)]
      rcases min_choice |y - r₁| |y - r₂| with h | h
      · exact (key r₁ h).trans le_self_add
      · exact (key r₂ h).trans le_add_self
    · rw [indicator_of_notMem hy]
      have : (fun x => (x, y)) ⁻¹' t = ∅ := by
        ext x; simp only [mem_preimage, mem_empty_iff_false, iff_false]
        exact fun hx => hy hx.1.2
      rw [this, measure_empty]
  -- integrate
  have hint := lintegral_mono (μ := (volume : Measure ℝ)) hslice
  rw [lintegral_indicator measurableSet_Icc] at hint
  refine hint.trans ?_
  have hI₁ : Icc (c 1 - ε) (c 1 + ε) = Icc (c 1 - ε) (c 1 - ε + 2 * ε) := by ring_nf
  have h2e : 0 < 2 * ε := by positivity
  have hH := fun r => lintegral_min_div_abs_le (2 * ε) K (2 * ε) (c 1 - ε) r h2e hK h2e.le
  rw [hI₁]
  rw [lintegral_add_left (by fun_prop)]
  refine (add_le_add (hH r₁) (hH r₂)).trans ?_
  have hX : 0 ≤ 2 * K * (1 + Real.log (1 + 2 * ε * (2 * ε) / K)) := by
    have := log_one_add_nonneg (2 * ε * (2 * ε) / K) (by positivity)
    positivity
  rw [← ENNReal.ofReal_add hX hX]
  apply ENNReal.ofReal_le_ofReal
  exact M2_final_ineq hΛ hε hσ hDpos (abs_det_le M hMb)

theorem M2const_pos {Λ ε : ℝ} (hΛ : 0 ≤ Λ) (hε : 0 < ε) : 0 < M2const Λ ε := by
  have h1 := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
  have h2 := log_one_add_nonneg (√2 * ε ^ 2 * Λ) (by positivity)
  unfold M2const; positivity

/-- **Lemma M2** (paper statement shape). For every `Λ ≥ 0` and `ε > 0` there is a constant
`C > 0` such that, uniformly over all symmetric `M` with entries bounded by `Λ` and
`det M ≠ 0`, all `L`, `k`, all squares of side `2ε` and all `σ > 0`, the sublevel area is at
most `C σ (1 + log⁺(1/σ)) / √|det M|`. -/
theorem lemmaM2 {Λ ε : ℝ} (hΛ : 0 ≤ Λ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Matrix (Fin 2) (Fin 2) ℝ), M.IsSymm → (∀ i j, |M i j| ≤ Λ) →
      M.det ≠ 0 → ∀ (L : Fin 2 → ℝ) (k : ℝ) (c : Fin 2 → ℝ) (σ : ℝ), 0 < σ →
        volume {β | β ∈ square c ε ∧ |quadForm M L k β| ≤ σ} ≤
          ENNReal.ofReal (C * σ * (1 + Real.posLog (1 / σ)) / √|M.det|) := by
  refine ⟨M2const Λ ε, M2const_pos hΛ hε, fun M hM hMb hdet L k c σ hσ => ?_⟩
  rw [mul_assoc]
  exact lemmaM2_explicit hΛ hε M hM hMb hdet L k c hσ

end VectorSLT
