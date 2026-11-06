/-
Milestone D: full-network four-log lower bound at the first shear position
(Proposition L′ of `shear_position_one_lower_exact.md`, Theorem L (L3)).
-/
import VectorSLT.Network
import VectorSLT.ErrorBound
import VectorSLT.LeadingModel

namespace VectorSLT

open MeasureTheory Set Filter Topology

/-! ### Raw parameters -/

/-- One row of the three inactive blocks, two triples: `((ρ₁,ρ₂,ρ₃)_{col 0}, (ρ₁,ρ₂,ρ₃)_{col 1})`. -/
abbrev Row := (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)
/-- The sixteen raw weights at depth four, width two:
`(((M₀₀, M₀₁), (M₁₀, M₁₁)), (row 0 of B₁B₂B₃, row 1 of B₁B₂B₃))`, with Lebesgue measure. -/
abbrev Raw16 := ((ℝ × ℝ) × (ℝ × ℝ)) × (Row × Row)

/-- Component `i ∈ {0,1,2}` of a triple. -/
def tri (v : ℝ × ℝ × ℝ) : ℕ → ℝ
  | 0 => v.1
  | 1 => v.2.1
  | _ => v.2.2

/-- The four weight matrices of a raw parameter, in application order: `W 0 = M` (active,
position one), `W (i+1) = B_{i+1}`, whose row `k` is `(ρₖ.1 i, ρₖ.2 i)`. -/
def weights (θ : Raw16) : ℕ → Matrix (Fin 2) (Fin 2) ℝ
  | 0 => !![θ.1.1.1, θ.1.1.2; θ.1.2.1, θ.1.2.2]
  | i + 1 => !![tri θ.2.1.1 i, tri θ.2.1.2 i; tri θ.2.2.1 i, tri θ.2.2.2 i]

/-- The depth-four network `h_θ = F_{B₃} ∘ F_{B₂} ∘ F_{B₁} ∘ F_M`. -/
def net (θ : Raw16) : (Fin 2 → ℝ) → (Fin 2 → ℝ) := prefixNet (weights θ) 4

/-- The base point: active matrix `A₀`, inactive blocks zero. -/
def θ₀ : Raw16 := (((1, -1), (1, -1)), ((0, 0), (0, 0)))

theorem weights_θ₀_zero : weights θ₀ 0 = A0 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-! ### (M2) coordinates: a unimodular shear -/

/-- `(m₁, m₂) ↦ (α, ν) = (m₁, m₁ + m₂)` on each active row and `(a, a') ↦ (a, b) = (a, a + a')`
on each inactive row (the raw row is `(a, b - a)`). -/
def toM2 (θ : Raw16) : Raw16 :=
  (((θ.1.1.1, θ.1.1.1 + θ.1.1.2), (θ.1.2.1, θ.1.2.1 + θ.1.2.2)),
    ((θ.2.1.1, θ.2.1.1 + θ.2.1.2), (θ.2.2.1, θ.2.2.1 + θ.2.2.2)))

theorem measurePreserving_toM2 : MeasurePreserving toM2 volume volume := by
  have h2 : MeasurePreserving (fun z : ℝ × ℝ => (z.1, z.1 + z.2)) volume volume :=
    measurePreserving_prod_add volume volume
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have : (volume : Measure (ℝ × ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have h3 : MeasurePreserving (fun z : Row => (z.1, z.1 + z.2)) volume volume :=
    measurePreserving_prod_add volume volume
  exact (h2.prod h2).prod (h3.prod h3)

theorem measurable_toM2 : Measurable toM2 := measurePreserving_toM2.measurable

/-! ### Reading the (M2) coordinates -/

def actα (y : Raw16) (k : Fin 2) : ℝ := ![y.1.1.1, y.1.2.1] k
def actν (y : Raw16) (k : Fin 2) : ℝ := ![y.1.1.2, y.1.2.2] k
/-- Inactive amplitude `a_{i+1}^{(k)}`. -/
def inA (y : Raw16) (k : Fin 2) (i : ℕ) : ℝ := tri (![y.2.1, y.2.2] k).1 i
/-- Inactive coefficient `b_{i+1}^{(k)}`. -/
def inB (y : Raw16) (k : Fin 2) (i : ℕ) : ℝ := tri (![y.2.1, y.2.2] k).2 i

/-- **The network in (M2) coordinates.** Along the trajectory `zᵢ = G_{i}x` (Lean's
`prefixNet (weights θ) i x`), the row forms `λᵢ⁽ᵏ⁾ = W_i k · zᵢ` and the `(s,t)`-state
`(Sᵢ, Tᵢ) = (z_{i+1,0} - z_{i+1,1}, z_{i+1,1})` satisfy the recursion used by `err_bound`, and
the output error is `∑ᵢ λᵢ³ - s³`. -/
theorem net_recursion (θ : Raw16) (x : Fin 2 → ℝ) :
    let W := weights θ
    let y := toM2 θ
    let lam : ℕ → Fin 2 → ℝ := fun i k => W i k ⬝ᵥ prefixNet W i x
    let S : ℕ → ℝ := fun i => prefixNet W (i + 1) x 0 - prefixNet W (i + 1) x 1
    let T : ℕ → ℝ := fun i => prefixNet W (i + 1) x 1
    let s := x 0 - x 1
    let t := x 1
    (∀ k, lam 0 k = actα y k * s + actν y k * t) ∧
    S 0 = s + lam 0 0 ^ 3 - lam 0 1 ^ 3 ∧ T 0 = t + lam 0 1 ^ 3 ∧
    (∀ i < 3, ∀ k, lam (i + 1) k = inA y k i * S i + inB y k i * T i) ∧
    (∀ i < 3, S (i + 1) = S i + lam (i + 1) 0 ^ 3 - lam (i + 1) 1 ^ 3) ∧
    (∀ i < 3, T (i + 1) = T i + lam (i + 1) 1 ^ 3) ∧
    (∀ k, net θ x k - layer A0 x k = lam 0 k ^ 3 + lam 1 k ^ 3 + lam 2 k ^ 3 + lam 3 k ^ 3 - s ^ 3) := by
  intro W y lam S T s t
  have hstep : ∀ i, ∀ k, prefixNet W (i + 1) x k = prefixNet W i x k + lam i k ^ 3 := by
    intro i k; rw [prefixNet_succ, Function.comp_apply, layer_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    fin_cases k <;>
      simp [lam, W, y, s, t, actα, actν, weights, toM2, dotProduct, Fin.sum_univ_two] <;> ring
  · simp only [S, hstep 0]; simp [s]; ring
  · simp only [T, hstep 0]; simp [t]
  · intro i hi k
    have e : ∀ z : Fin 2 → ℝ, W (i + 1) k ⬝ᵥ z =
        inA y k i * (z 0 - z 1) + inB y k i * z 1 := by
      intro z
      fin_cases k <;>
        simp [W, y, inA, inB, weights, toM2, dotProduct, Fin.sum_univ_two] <;>
        interval_cases i <;> simp [tri] <;> ring
    exact e _
  · intro i hi
    simp only [S, hstep (i + 1)]; ring
  · intro i hi
    simp only [T, hstep (i + 1)]
  · intro k
    have h := M2_error W x k
    simp only [net, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h ⊢
    rw [h]

/-! ### The lower region `Ω_N` in (M2) coordinates -/

/-- Real cube root on `[0, ∞)`. -/
noncomputable def cbrt (x : ℝ) : ℝ := x ^ ((1 : ℝ) / 3)

/-- Active part (replacing L′'s image of the `c`-cube under the inverse triangular map by a
sub-box): `α ∈ (1 - A)^{1/3} ± e/10`, then `ν ∈ -P₁/α² ± e/10`. -/
def actBox (e : ℝ) (w : Row) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Icc (cbrt (1 - momA (tri w.1)) - e / 10) (cbrt (1 - momA (tri w.1)) + e / 10) ∧
    z.2 ∈ Icc (-momP1 (tri w.1) (tri w.2) / z.1 ^ 2 - e / 10)
      (-momP1 (tri w.1) (tri w.2) / z.1 ^ 2 + e / 10)}

/-- `Ω_N` in (M2) coordinates, `t = 1/N`: both rows in the inactive lower region of
milestone C (independent radii), each active row in its box with `e = √t = N^{-1/2}`. -/
def OmegaM (t : ℝ) : Set Raw16 :=
  {y | (y.2.1 ∈ lowerRegion t ∧ y.2.2 ∈ lowerRegion t) ∧
    (y.1.1 ∈ actBox (√t) y.2.1 ∧ y.1.2 ∈ actBox (√t) y.2.2)}

@[fun_prop] theorem measurable_momA_tri {α : Type*} [MeasurableSpace α] {f : α → ℝ × ℝ × ℝ}
    (hf : Measurable f) : Measurable fun x => momA (tri (f x)) := by
  unfold momA tri; fun_prop

@[fun_prop] theorem measurable_momP1_tri {α : Type*} [MeasurableSpace α]
    {f g : α → ℝ × ℝ × ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => momP1 (tri (f x)) (tri (g x)) := by
  unfold momP1 tri; fun_prop

@[fun_prop] theorem measurable_cbrt_comp {α : Type*} [MeasurableSpace α] {f : α → ℝ}
    (hf : Measurable f) : Measurable fun x => cbrt (f x) := by
  unfold cbrt; fun_prop

theorem measurableSet_OmegaM (t : ℝ) : MeasurableSet (OmegaM t) := by
  have hL := measurableSet_lowerRegion t
  unfold OmegaM actBox
  simp only [mem_Icc, ofPred_and, mem_ofPred_eq]
  refine ((measurable_snd.fst hL).inter (measurable_snd.snd hL)).inter ?_
  refine (((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)).inter
    ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_))).inter
    (((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)).inter
    ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_))) <;> fun_prop

theorem measurableSet_actBox (e : ℝ) (w : Row) : MeasurableSet (actBox e w) := by
  unfold actBox
  simp only [mem_Icc, ofPred_and]
  refine ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)).inter
    ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)) <;> fun_prop

theorem volume_actBox (e : ℝ) (w : Row) :
    volume (actBox e w) = ENNReal.ofReal (e / 5) * ENNReal.ofReal (e / 5) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_actBox e w)]
  set c := cbrt (1 - momA (tri w.1))
  have h : ∀ α : ℝ, volume (Prod.mk α ⁻¹' actBox e w) =
      (Icc (c - e / 10) (c + e / 10)).indicator (fun _ => ENNReal.ofReal (e / 5)) α := by
    intro α
    by_cases hα : α ∈ Icc (c - e / 10) (c + e / 10)
    · rw [indicator_of_mem hα]
      have : Prod.mk α ⁻¹' actBox e w = Icc (-momP1 (tri w.1) (tri w.2) / α ^ 2 - e / 10)
          (-momP1 (tri w.1) (tri w.2) / α ^ 2 + e / 10) := by
        ext ν; simp only [mem_preimage, actBox, mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨hα, h⟩⟩
      rw [this, Real.volume_Icc]; congr 1; ring
    · rw [indicator_of_notMem hα]
      have : Prod.mk α ⁻¹' actBox e w = ∅ := by
        ext ν; simp only [mem_preimage, actBox, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hα h.1
      rw [this, measure_empty]
  simp_rw [h]
  rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc, mul_comm]
  congr 2; ring

theorem volume_OmegaM (t : ℝ) :
    volume (OmegaM t) = ENNReal.ofReal (√t / 5) ^ 4 *
      (volume (lowerRegion t) * volume (lowerRegion t)) := by
  have hL := measurableSet_lowerRegion t
  rw [Measure.volume_eq_prod (α := (ℝ × ℝ) × (ℝ × ℝ)) (β := Row × Row),
    Measure.prod_apply_symm (measurableSet_OmegaM t)]
  have h : ∀ rr : Row × Row, volume ((fun a => (a, rr)) ⁻¹' OmegaM t) =
      (lowerRegion t ×ˢ lowerRegion t).indicator
        (fun _ => ENNReal.ofReal (√t / 5) ^ 4) rr := by
    intro rr
    by_cases hr : rr ∈ lowerRegion t ×ˢ lowerRegion t
    · rw [indicator_of_mem hr]
      have : (fun a => (a, rr)) ⁻¹' OmegaM t = actBox (√t) rr.1 ×ˢ actBox (√t) rr.2 := by
        ext a; simp only [mem_preimage, OmegaM, mem_ofPred_eq, mem_prod]
        exact ⟨fun h => h.2, fun h => ⟨hr, h⟩⟩
      rw [this, Measure.volume_eq_prod, Measure.prod_prod, volume_actBox, volume_actBox]
      ring
    · rw [indicator_of_notMem hr]
      have : (fun a => (a, rr)) ⁻¹' OmegaM t = ∅ := by
        ext a; simp only [mem_preimage, OmegaM, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hr h.1
      rw [this, measure_empty]
  simp_rw [h]
  rw [lintegral_indicator_const (hL.prod hL), Measure.volume_eq_prod (α := Row) (β := Row),
    Measure.prod_prod]

/-! ### Pointwise control on `Ω_N` -/

theorem cbrt_cube {x : ℝ} (hx : 0 ≤ x) : cbrt x ^ 3 = x := by
  unfold cbrt
  rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.rpow_inv_natCast_pow hx (by norm_num)

theorem cbrt_mem {x : ℝ} (h1 : 95 / 100 ≤ x) (h2 : x ≤ 105 / 100) :
    95 / 100 ≤ cbrt x ∧ cbrt x ≤ 105 / 100 := by
  unfold cbrt
  rcases le_total x 1 with hx | hx
  · constructor
    · calc (95 / 100 : ℝ) ≤ x := h1
        _ = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ x ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow_of_exponent_ge (by linarith) hx (by norm_num)
    · exact (Real.rpow_le_one (by linarith) hx (by norm_num)).trans (by norm_num)
  · constructor
    · exact le_trans (by norm_num) (Real.one_le_rpow hx (by norm_num))
    · calc x ^ ((1 : ℝ) / 3) ≤ x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
        _ = x := Real.rpow_one x
        _ ≤ 105 / 100 := h2

/-- The smallness conditions on `t = 1/N` (all hold for large `N`). -/
def TSmall (R t : ℝ) : Prop := 0 < t ∧ t ≤ 1 / 100 ∧ 4 * t ^ ((1 : ℝ) / 10) * R ^ 3 ≤ 1 / 1200

/-- Bounds on one inactive row in the lower region (Lemma L′2, rows 1–2). -/
theorem row_bounds {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) {w : Row} (hw : w ∈ lowerRegion t) :
    (∀ i < 3, |tri w.1 i| ≤ 4 * t ^ ((1 : ℝ) / 10) ∧ |tri w.2 i| ≤ 4 * t ^ ((1 : ℝ) / 10)) ∧
    |momP1 (tri w.1) (tri w.2)| ≤ √t ∧ |momP2 (tri w.1) (tri w.2)| ≤ √t ∧
    |momP3 (tri w.2)| ≤ √t := by
  set f : Fin 3 → ℝ := ![w.1.1, w.1.2.1, w.1.2.2]
  set g : Fin 3 → ℝ := ![w.2.1, w.2.2.1, w.2.2.2]
  have hε : 0 < 4 * t ^ ((1 : ℝ) / 10) := by positivity
  have htε : t ≤ (4 * t ^ ((1 : ℝ) / 10) / 4) ^ 10 := by
    rw [mul_div_cancel_left₀ _ (by norm_num : (4:ℝ) ≠ 0), ← Real.rpow_natCast,
      ← Real.rpow_mul ht0.le]; norm_num
  obtain ⟨hf, hg, hP⟩ := lowerRegion_sub hε ht0 ht1 htε f g hw
  have hsplit : rowPsq f g = momP1 (tri w.1) (tri w.2) ^ 2 + momP2 (tri w.1) (tri w.2) ^ 2 +
      momP3 (tri w.2) ^ 2 := by
    simp [rowPsq, rowP, Fin.sum_univ_three, momP1, momP2, momP3, tri, f, g]
  rw [hsplit] at hP
  refine ⟨fun i hi => ?_, ?_, ?_, ?_⟩
  · interval_cases i
    · exact ⟨hf 0, hg 0⟩
    · exact ⟨hf 1, hg 1⟩
    · exact ⟨hf 2, hg 2⟩
  · have := sq_nonneg (momP2 (tri w.1) (tri w.2))
    have := sq_nonneg (momP3 (tri w.2))
    exact Real.abs_le_sqrt (by linarith)
  · have := sq_nonneg (momP1 (tri w.1) (tri w.2))
    have := sq_nonneg (momP3 (tri w.2))
    exact Real.abs_le_sqrt (by linarith)
  · have := sq_nonneg (momP1 (tri w.1) (tri w.2))
    have := sq_nonneg (momP2 (tri w.1) (tri w.2))
    exact Real.abs_le_sqrt (by linarith)

/-- Active-row consequences of the active box (Lemma L′2, rows 4–5, and `|c₃|, |c₂| ≤ e`). -/
theorem act_bounds {e ρ : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 / 10) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 10)
    {w : Row} (hw : ∀ i < 3, |tri w.1 i| ≤ ρ)
    {z : ℝ × ℝ} (hz : z ∈ actBox e w) :
    (9 / 10 ≤ z.1 ∧ z.1 ≤ 11 / 10) ∧ |z.1 ^ 3 - 1 + momA (tri w.1)| ≤ e ∧
      |3 * z.1 ^ 2 * z.2 + 3 * momP1 (tri w.1) (tri w.2)| ≤ e := by
  have hA := momA_le hw
  have hρ3 : ρ ^ 3 ≤ 1 / 1000 := by
    have := pow_le_pow_left₀ hρ0 hρ 3; norm_num at this; linarith
  set A := momA (tri w.1)
  have hx1 : 95 / 100 ≤ 1 - A := by linarith [(abs_le.mp hA).2]
  have hx2 : 1 - A ≤ 105 / 100 := by linarith [(abs_le.mp hA).1]
  obtain ⟨c1, c2⟩ := cbrt_mem hx1 hx2
  obtain ⟨⟨hz1, hz2⟩, hz3, hz4⟩ := hz
  have hα : 9 / 10 ≤ z.1 ∧ z.1 ≤ 11 / 10 := ⟨by linarith, by linarith⟩
  refine ⟨hα, ?_, ?_⟩
  · have hc := cbrt_cube (show 0 ≤ 1 - A by linarith)
    have e1 : z.1 ^ 3 - 1 + A = z.1 ^ 3 - cbrt (1 - A) ^ 3 := by rw [hc]; ring
    rw [e1]
    have hm1 : |z.1| ≤ 11 / 10 := by rw [abs_of_pos (by linarith)]; exact hα.2
    have hm2 : |cbrt (1 - A)| ≤ 11 / 10 := by rw [abs_of_pos (by linarith)]; linarith
    refine (cube_diff_le hm1 hm2).trans ?_
    have : |z.1 - cbrt (1 - A)| ≤ e / 10 := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg (z.1 - cbrt (1 - A))]
  · have hα0 : z.1 ≠ 0 := by linarith
    have hα2 : 0 < z.1 ^ 2 := by positivity
    set P := momP1 (tri w.1) (tri w.2)
    have e1 : 3 * z.1 ^ 2 * z.2 + 3 * P = 3 * z.1 ^ 2 * (z.2 - (-P / z.1 ^ 2)) := by
      field_simp; ring
    rw [e1, abs_mul, abs_of_pos (by positivity)]
    have : |z.2 - (-P / z.1 ^ 2)| ≤ e / 10 := by rw [abs_le]; constructor <;> linarith
    have h121 : z.1 ^ 2 ≤ 121 / 100 := by nlinarith
    nlinarith [abs_nonneg (z.2 - (-P / z.1 ^ 2))]

/-- The constant in the sup-norm error bound on `Ω_N`. -/
noncomputable def Cerr (R : ℝ) : ℝ := 3 * 10 ^ 12 * 4097 * R ^ 15

theorem tsmall_facts {R t : ℝ} (hR : 1 ≤ R) (ht : TSmall R t) :
    0 < t ∧ t ≤ 1 ∧ √t ≤ 1 / 10 ∧ √t ≤ t ^ ((1 : ℝ) / 10) ∧
      4 * t ^ ((1 : ℝ) / 10) ≤ 1 / 1200 ∧
      (4 * t ^ ((1 : ℝ) / 10)) ^ 6 ≤ 4096 * √t := by
  obtain ⟨h0, h1, h2⟩ := ht
  have ht1 : t ≤ 1 := by linarith
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
  have hτ0 : 0 ≤ t ^ ((1 : ℝ) / 10) := by positivity
  refine ⟨h0, ht1, ?_, ?_, ?_, ?_⟩
  · rw [show (1 / 10 : ℝ) = √(1 / 100) by
      rw [show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h1
  · rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge h0 ht1 (by norm_num)
  · nlinarith
  · have e : (t ^ ((1 : ℝ) / 10)) ^ 6 = t ^ ((6 : ℝ) / 10) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le]; norm_num
    rw [mul_pow, e, Real.sqrt_eq_rpow]
    have : t ^ ((6 : ℝ) / 10) ≤ t ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_ge h0 ht1 (by norm_num)
    norm_num; linarith

/-- **Lemma L′3, sup-norm form.** On `Ω_N` (with `t = 1/N` small), for every input with
`|xᵢ| ≤ R`, each output of the network differs from the target by at most `C_R N^{-1/2}`. -/
theorem omega_err {R t : ℝ} (hR : 1 ≤ R) (ht : TSmall R t) {θ : Raw16}
    (hθ : toM2 θ ∈ OmegaM t) {x : Fin 2 → ℝ} (hx : ∀ i, |x i| ≤ R) (k : Fin 2) :
    |net θ x k - layer A0 x k| ≤ Cerr R * √t := by
  obtain ⟨ht0, ht1, hsq, -, hρs, hρ6⟩ := tsmall_facts hR ht
  have hρR := ht.2.2
  set ρ := 4 * t ^ ((1 : ℝ) / 10)
  have hρ0 : 0 ≤ ρ := by positivity
  set y := toM2 θ
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hθ
  obtain ⟨rb1, p11, p12, p13⟩ := row_bounds ht0 ht1 h1
  obtain ⟨rb2, p21, p22, p23⟩ := row_bounds ht0 ht1 h2
  obtain ⟨ab1, c31, c21⟩ := act_bounds (Real.sqrt_nonneg t) hsq hρ0 (by linarith)
    (fun i hi => (rb1 i hi).1) h3
  obtain ⟨ab2, c32, c22⟩ := act_bounds (Real.sqrt_nonneg t) hsq hρ0 (by linarith)
    (fun i hi => (rb2 i hi).1) h4
  obtain ⟨hl0, hS0, hT0, hl, hS, hT, herr⟩ := net_recursion θ x
  have hs : |x 0 - x 1| ≤ 2 * R := by
    have := abs_sub (x 0) (x 1); linarith [hx 0, hx 1]
  have hb := err_bound hR (Real.sqrt_nonneg t) hsq hρ0 hρR
    hs (hx 1) (actα y) (actν y) (inA y) (inB y)
    (fun i k => weights θ i k ⬝ᵥ prefixNet (weights θ) i x)
    (fun i => prefixNet (weights θ) (i + 1) x 0 - prefixNet (weights θ) (i + 1) x 1)
    (fun i => prefixNet (weights θ) (i + 1) x 1)
    (fun k => by fin_cases k; exacts [ab1, ab2])
    (fun k i hi => by fin_cases k; exacts [rb1 i hi, rb2 i hi])
    (fun k => by fin_cases k; exacts [p11, p21])
    (fun k => by fin_cases k; exacts [p12, p22])
    (fun k => by fin_cases k; exacts [p13, p23])
    (fun k => by fin_cases k; exacts [c31, c32])
    (fun k => by fin_cases k; exacts [c21, c22])
    hl0 hS0 hT0 hl hS hT k
  rw [herr k]
  refine hb.trans ?_
  have : 0 ≤ R ^ 15 := by positivity
  have : √t + ρ ^ 6 ≤ 4097 * √t := by linarith
  calc 3 * 10 ^ 12 * R ^ 15 * (√t + ρ ^ 6) ≤ 3 * 10 ^ 12 * R ^ 15 * (4097 * √t) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = Cerr R * √t := by unfold Cerr; ring

/-- `Ω_N` shrinks to the base point: every raw coordinate is within `15 t^{1/10}` of `θ₀`
(Lemma L′2, "`Ω_N ⊂ U` for large N"). -/
theorem omega_near {R t : ℝ} (hR : 1 ≤ R) (ht : TSmall R t) {θ : Raw16}
    (hθ : toM2 θ ∈ OmegaM t) : dist θ θ₀ ≤ 15 * t ^ ((1 : ℝ) / 10) := by
  obtain ⟨ht0, ht1, hsq, hsqτ, hρs, -⟩ := tsmall_facts hR ht
  set τ := t ^ ((1 : ℝ) / 10)
  have hτ0 : 0 ≤ τ := by positivity
  set ρ := 4 * τ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ3 : ρ ^ 3 ≤ ρ := pow_le_of_le_one hρ0 (by linarith) (by norm_num)
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hθ
  obtain ⟨rb1, p11, -, -⟩ := row_bounds ht0 ht1 h1
  obtain ⟨rb2, p21, -, -⟩ := row_bounds ht0 ht1 h2
  -- active rows
  have act : ∀ (w : Row) (z : ℝ × ℝ), (∀ i < 3, |tri w.1 i| ≤ ρ) →
      |momP1 (tri w.1) (tri w.2)| ≤ √t → z ∈ actBox (√t) w →
      |z.1 - 1| ≤ 13 * τ ∧ |z.2| ≤ 2 * τ := by
    intro w z hw hP hz
    obtain ⟨hα, hc3, hc2⟩ := act_bounds (Real.sqrt_nonneg t) hsq hρ0 (by linarith) hw hz
    have hA := momA_le hw
    have h1 := abs_sub_one_le_cube (show 0 ≤ z.1 by linarith [hα.1])
    have := abs_sub (z.1 ^ 3 - 1 + momA (tri w.1)) (momA (tri w.1))
    rw [show z.1 ^ 3 - 1 + momA (tri w.1) - momA (tri w.1) = z.1 ^ 3 - 1 by ring] at this
    have hν := nu_le hα.1 hc2 hP
    constructor <;> linarith
  obtain ⟨a1, n1⟩ := act _ _ (fun i hi => (rb1 i hi).1) p11 h3
  obtain ⟨a2, n2⟩ := act _ _ (fun i hi => (rb2 i hi).1) p21 h4
  have r1 := fun i hi => rb1 i hi
  have r2 := fun i hi => rb2 i hi
  obtain ⟨r10, r10'⟩ := r1 0 (by norm_num)
  obtain ⟨r11, r11'⟩ := r1 1 (by norm_num)
  obtain ⟨r12, r12'⟩ := r1 2 (by norm_num)
  obtain ⟨r20, r20'⟩ := r2 0 (by norm_num)
  obtain ⟨r21, r21'⟩ := r2 1 (by norm_num)
  obtain ⟨r22, r22'⟩ := r2 2 (by norm_num)
  simp only [toM2, tri] at a1 n1 a2 n2 r10 r10' r11 r11' r12 r12' r20 r20' r21 r21' r22 r22'
  rw [abs_le] at a1 n1 a2 n2 r10 r10' r11 r11' r12 r12' r20 r20' r21 r21' r22 r22'
  simp only [θ₀, Prod.dist_eq, Real.dist_eq, max_le_iff]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at *
  and_intros <;> rw [abs_le] <;> constructor <;> linarith

/-! ### Proposition L′ -/

theorem inv_rpow_tenth_le {N M : ℝ} (hM : 0 < M) (hN : M ^ 10 ≤ N) :
    N⁻¹ ^ ((1 : ℝ) / 10) ≤ M⁻¹ := by
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  rw [Real.inv_rpow hN0.le]
  apply inv_anti₀ hM
  calc M = (M ^ 10) ^ ((1 : ℝ) / 10) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]; norm_num
    _ ≤ N ^ ((1 : ℝ) / 10) := Real.rpow_le_rpow (by positivity) hN (by norm_num)

/-- **Proposition L′ (Theorem L's lower bound (L3)), Lean form.**

Setting: width two, depth four, all sixteen raw weights free (`Raw16`, Lebesgue measure),
active block at position one, target `F_{A₀}` with `A₀ = [[1,-1],[1,-1]]` (the normalized
rank-one shear with both rows nonzero; the reduction to `A₀` is Theorem H §2 and is not
formalized). Hypotheses, the two easy directions of results §0 in compact-input form:

* **(G↑)**: `K θ ≤ Λ M²` whenever every output error is at most `M` on the input box
  `|xᵢ| ≤ R` (e.g. the population loss of an input law supported in the box, `Λ = 2`);
* **(π↓)**: the prior (times cutoff) is at least `π₀ > 0` on a neighbourhood of `θ₀`.

Conclusion: `Z_N = ∫ e^{-N K} π ≥ c N⁻⁴ (log N)⁴` for all large `N`. -/
theorem propLprime {R Λ π₀ : ℝ} (hR : 1 ≤ R) (hπ₀ : 0 < π₀)
    (K : Raw16 → ℝ)
    (hK : ∀ θ M, 0 ≤ M → (∀ x : Fin 2 → ℝ, (∀ i, |x i| ≤ R) →
      ∀ k, |net θ x k - layer A0 x k| ≤ M) → K θ ≤ Λ * M ^ 2)
    (π : Raw16 → ENNReal) (hπ : ∀ᶠ θ in 𝓝 θ₀, ENNReal.ofReal π₀ ≤ π θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ENNReal.ofReal (c * N⁻¹ ^ 4 * Real.log N ^ 4) ≤
        ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * K θ))) * π θ := by
  obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff.mp hπ
  set E := Real.exp (-(Λ * Cerr R ^ 2))
  have hcC : 0 < cC := by unfold cC; norm_num
  refine ⟨E * π₀ * cC ^ 2 / 625, by positivity,
    max (max 100 ((4800 * R ^ 3) ^ 10)) ((30 / r₀) ^ 10), fun N hN => ?_⟩
  have hN100 : 100 ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN0 : 0 < N := by linarith
  set t := N⁻¹ with htdef
  have ht0 : 0 < t := inv_pos.mpr hN0
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
  have hτ1 : t ^ ((1 : ℝ) / 10) ≤ (4800 * R ^ 3)⁻¹ :=
    inv_rpow_tenth_le (by positivity) ((le_max_right _ _).trans ((le_max_left _ _).trans hN))
  have hτ2 : t ^ ((1 : ℝ) / 10) ≤ (30 / r₀)⁻¹ :=
    inv_rpow_tenth_le (by positivity) ((le_max_right _ _).trans hN)
  have hts : TSmall R t := by
    refine ⟨ht0, ?_, ?_⟩
    · rw [htdef, inv_le_comm₀ hN0 (by norm_num)]; norm_num; linarith
    · have := mul_le_mul_of_nonneg_right hτ1 (show 0 ≤ 4 * R ^ 3 by positivity)
      rw [show (4800 * R ^ 3)⁻¹ * (4 * R ^ 3) = 1 / 1200 by field_simp; norm_num] at this
      linarith
  have ht1 : t ≤ 1 := (tsmall_facts hR hts).2.1
  -- the region in raw coordinates
  set Ω := toM2 ⁻¹' OmegaM t
  have hΩm : MeasurableSet Ω := measurable_toM2 (measurableSet_OmegaM t)
  have hpt : ∀ θ ∈ Ω, ENNReal.ofReal E * ENNReal.ofReal π₀ ≤
      ENNReal.ofReal (Real.exp (-(N * K θ))) * π θ := by
    intro θ hθ
    apply mul_le_mul'
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hKθ := hK θ (Cerr R * √t) (by unfold Cerr; positivity)
        (fun x hx k => omega_err hR hts hθ hx k)
      have e : Λ * (Cerr R * √t) ^ 2 = Λ * Cerr R ^ 2 * t := by
        rw [mul_pow, Real.sq_sqrt ht0.le]; ring
      rw [e] at hKθ
      have hNt : N * t = 1 := mul_inv_cancel₀ hN0.ne'
      have : N * K θ ≤ Λ * Cerr R ^ 2 := by
        calc N * K θ ≤ N * (Λ * Cerr R ^ 2 * t) := mul_le_mul_of_nonneg_left hKθ hN0.le
          _ = Λ * Cerr R ^ 2 * (N * t) := by ring
          _ = Λ * Cerr R ^ 2 := by rw [hNt, mul_one]
      linarith
    · apply hball
      have := omega_near hR hts hθ
      have h30 : 15 * t ^ ((1 : ℝ) / 10) ≤ 15 * (30 / r₀)⁻¹ := by linarith
      rw [inv_div] at h30
      linarith
  have hvol : volume Ω = volume (OmegaM t) :=
    measurePreserving_toM2.measure_preimage (measurableSet_OmegaM t).nullMeasurableSet
  have hLR := volume_lowerRegion ht0 ht1
  rw [one_div, htdef, inv_inv] at hLR
  calc ENNReal.ofReal (E * π₀ * cC ^ 2 / 625 * N⁻¹ ^ 4 * Real.log N ^ 4)
      = ENNReal.ofReal E * ENNReal.ofReal π₀ * (ENNReal.ofReal (√t / 5) ^ 4 *
          (ENNReal.ofReal (cC * N⁻¹ * Real.log N ^ 2) *
            ENNReal.ofReal (cC * N⁻¹ * Real.log N ^ 2))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [div_pow, show √t ^ 4 = (√t ^ 2) ^ 2 by ring, Real.sq_sqrt ht0.le, htdef]; ring
    _ ≤ ENNReal.ofReal E * ENNReal.ofReal π₀ * volume (OmegaM t) := by
        rw [volume_OmegaM]; gcongr
    _ = ∫⁻ θ in Ω, ENNReal.ofReal E * ENNReal.ofReal π₀ := by
        rw [setLIntegral_const, hvol, mul_comm]
    _ ≤ ∫⁻ θ in Ω, ENNReal.ofReal (Real.exp (-(N * K θ))) * π θ := setLIntegral_mono' hΩm hpt
    _ ≤ _ := setLIntegral_le_lintegral _ _

/-- The population loss `K(θ) = E_μ ‖h_θ(x) - F_{A₀}(x)‖²`. -/
noncomputable def popLoss (μ : Measure (Fin 2 → ℝ)) (θ : Raw16) : ℝ :=
  ∫ x, ∑ k, (net θ x k - layer A0 x k) ^ 2 ∂μ

/-- **Proposition L′ for the population loss** of any input law supported in the box
`|xᵢ| ≤ R` (no Gram hypothesis needed: `(G↑)` holds with `Λ = 2`). -/
theorem propLprime_population {R π₀ : ℝ} (hR : 1 ≤ R) (hπ₀ : 0 < π₀)
    (μ : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ∀ i, |x i| ≤ R)
    (π : Raw16 → ENNReal) (hπ : ∀ᶠ θ in 𝓝 θ₀, ENNReal.ofReal π₀ ≤ π θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ENNReal.ofReal (c * N⁻¹ ^ 4 * Real.log N ^ 4) ≤
        ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * popLoss μ θ))) * π θ := by
  refine propLprime hR hπ₀ (popLoss μ) (Λ := 2) ?_ π hπ
  intro θ M hM hbd
  unfold popLoss
  have hle : ∀ᵐ x ∂μ, ∑ k, (net θ x k - layer A0 x k) ^ 2 ≤ 2 * M ^ 2 := by
    filter_upwards [hμ] with x hx
    rw [Fin.sum_univ_two]
    have h0 := sq_le_sq' (abs_le.mp (hbd x hx 0)).1 (abs_le.mp (hbd x hx 0)).2
    have h1 := sq_le_sq' (abs_le.mp (hbd x hx 1)).1 (abs_le.mp (hbd x hx 1)).2
    linarith
  calc ∫ x, ∑ k, (net θ x k - layer A0 x k) ^ 2 ∂μ ≤ ∫ _x, 2 * M ^ 2 ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
          (integrable_const _) hle
    _ = 2 * M ^ 2 := by simp

end VectorSLT
