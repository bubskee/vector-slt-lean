/-
L6 stage 3, F5 + F6 + assembly: **Theorem M**, the upper bound
`Z_{N,1} ≤ C N⁻⁴ (log N)⁴` (decomposition §0), from (G↓) (`Gdown`, proved in stage 2).

Coordinates are the (M2) coordinates `y = toM2 θ`:
`y = (((α₀, ν₀), (α₁, ν₁)), ((a⁽⁰⁾, b⁽⁰⁾), (a⁽¹⁾, b⁽¹⁾)))`. The box is
`|α_k - 1|, |ν_k| ≤ 1/100`, `|a|, |b| ≤ 1/20` (`UM`).
-/
import VectorSLT.RowBound
import VectorSLT.ActiveCoords
import VectorSLT.Gdown
import VectorSLT.Separation

namespace VectorSLT

open MeasureTheory Set VectorSLT.SLT

/-! ### Explicit coordinates -/

/-- `P₁ = ∑ aᵢ² bᵢ`. -/
def P1t (a b : T3) : ℝ := a.1 ^ 2 * b.1 + a.2.1 ^ 2 * b.2.1 + a.2.2 ^ 2 * b.2.2
/-- `P₂ = ∑ aᵢ bᵢ²`. -/
def P2t (a b : T3) : ℝ := a.1 * b.1 ^ 2 + a.2.1 * b.2.1 ^ 2 + a.2.2 * b.2.2 ^ 2

/-- The quintic moment `Z = ∑ aᵢ²(aᵢ ηᵢ + bᵢ yᵢ)` of the row with amplitudes `a`, coefficients
`b`, with `α₀³ = u₀`, `α₁³ = u₁` (M3)/(M6). -/
def Zr (u0 u1 : ℝ) (a0 a1 a b : T3) : ℝ :=
  a.1 ^ 2 * (a.1 * (u0 - u1) + b.1 * u1) +
  a.2.1 ^ 2 * (a.2.1 * (u0 - u1 + a0.1 ^ 3 - a1.1 ^ 3) + b.2.1 * (u1 + a1.1 ^ 3)) +
  a.2.2 ^ 2 * (a.2.2 * (u0 - u1 + (a0.1 ^ 3 + a0.2.1 ^ 3) - (a1.1 ^ 3 + a1.2.1 ^ 3)) +
    b.2.2 * (u1 + (a1.1 ^ 3 + a1.2.1 ^ 3)))

theorem tri0 (v : T3) : tri v 0 = v.1 := rfl
theorem tri1 (v : T3) : tri v 1 = v.2.1 := rfl
theorem tri2 (v : T3) : tri v 2 = v.2.2 := rfl
theorem pcub0 (v : T3) : pcub 0 v = 0 := rfl
theorem pcub1 (v : T3) : pcub 1 v = v.1 ^ 3 := rfl
theorem pcub2 (v : T3) : pcub 2 v = v.1 ^ 3 + v.2.1 ^ 3 := rfl

/-- The ten-generator form (M5) in explicit coordinates. -/
noncomputable def TMx (α0 ν0 α1 ν1 : ℝ) (a0 b0 a1 b1 : T3) : ℝ :=
  (α0 ^ 3 - 1 + cub3 a0) ^ 2 + (3 * α0 ^ 2 * ν0 + 3 * P1t a0 b0) ^ 2 +
    (P2t a0 b0 + P1t a0 b0 ^ 2 / α0 ^ 3) ^ 2 + Zr (α0 ^ 3) (α1 ^ 3) a0 a1 a0 b0 ^ 2 +
  ((α1 ^ 3 - 1 + cub3 a1) ^ 2 + (3 * α1 ^ 2 * ν1 + 3 * P1t a1 b1) ^ 2 +
    (P2t a1 b1 + P1t a1 b1 ^ 2 / α1 ^ 3) ^ 2 + Zr (α0 ^ 3) (α1 ^ 3) a0 a1 a1 b1 ^ 2)

/-- The four-coefficient form `∑ₖ (c₃² + c₂² + c₁² + Z²)` of (G↓), explicit. -/
noncomputable def SMx (α0 ν0 α1 ν1 : ℝ) (a0 b0 a1 b1 : T3) : ℝ :=
  (α0 ^ 3 - 1 + cub3 a0) ^ 2 + (3 * α0 ^ 2 * ν0 + 3 * P1t a0 b0) ^ 2 +
    (3 * α0 * ν0 ^ 2 + 3 * P2t a0 b0) ^ 2 + Zr (α0 ^ 3) (α1 ^ 3) a0 a1 a0 b0 ^ 2 +
  ((α1 ^ 3 - 1 + cub3 a1) ^ 2 + (3 * α1 ^ 2 * ν1 + 3 * P1t a1 b1) ^ 2 +
    (3 * α1 * ν1 ^ 2 + 3 * P2t a1 b1) ^ 2 + Zr (α0 ^ 3) (α1 ^ 3) a0 a1 a1 b1 ^ 2)

/-- (G↓)'s right side in explicit coordinates. -/
theorem sum_coeffs_eq (θ : Raw16) :
    ∑ k, (c3M θ k ^ 2 + c2M θ k ^ 2 + c1M θ k ^ 2 + ZM θ k ^ 2) =
      SMx (toM2 θ).1.1.1 (toM2 θ).1.1.2 (toM2 θ).1.2.1 (toM2 θ).1.2.2 (toM2 θ).2.1.1
        (toM2 θ).2.1.2 (toM2 θ).2.2.1 (toM2 θ).2.2.2 := by
  unfold c3M c2M c1M ZM
  generalize toM2 θ = y
  obtain ⟨⟨⟨α0, ν0⟩, ⟨α1, ν1⟩⟩, ⟨⟨a0, b0⟩, ⟨a1, b1⟩⟩⟩ := y
  simp only [Fin.sum_univ_two, c3M, c2M, c1M, ZM, SMx, Zmom, etaM, yM, Zr, actα, actν, inA, inB,
    momA, momP1, momP2, P1t, P2t, cub3, tri0, tri1, tri2, Finset.sum_range_succ,
    Finset.sum_range_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-! ### (A1): `c₁² + c₂² ≥ (G² + c₂²)/3` on the box -/

theorem A1_core {α ν P1 P2 : ℝ} (hα : α ∈ Iα) (hν : ν ∈ Jν) (hP1 : |P1| ≤ 1 / 1000) :
    (3 * α ^ 2 * ν + 3 * P1) ^ 2 + (P2 + P1 ^ 2 / α ^ 3) ^ 2 ≤
      3 * ((3 * α ^ 2 * ν + 3 * P1) ^ 2 + (3 * α * ν ^ 2 + 3 * P2) ^ 2) := by
  obtain ⟨hα1, hα2⟩ := hα
  have hα0 : 0 < α := by linarith
  have hα3 : 9 / 10 ≤ α ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hα1 3]
  set c2 := 3 * α ^ 2 * ν + 3 * P1
  set c1 := 3 * α * ν ^ 2 + 3 * P2
  set D := c2 * (6 * P1 - c2) / (9 * α ^ 3)
  have hG : P2 + P1 ^ 2 / α ^ 3 = c1 / 3 + D := by
    simp only [c1, c2, D]; field_simp; ring
  have hc2 : |c2| ≤ 1 / 10 := by
    have hν' : |ν| ≤ 1 / 100 := abs_le.mpr ⟨hν.1, hν.2⟩
    have : α ^ 2 ≤ 2 := by nlinarith
    have e1 : |3 * α ^ 2 * ν| = 3 * α ^ 2 * |ν| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 3 * α ^ 2)]
    have e2 : |3 * P1| = 3 * |P1| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have e3 : 3 * α ^ 2 * |ν| ≤ 3 * 2 * (1 / 100) := by
      have := mul_le_mul this hν' (abs_nonneg _) (by norm_num)
      linarith
    calc |c2| ≤ |3 * α ^ 2 * ν| + |3 * P1| := abs_add_le _ _
      _ ≤ 1 / 10 := by rw [e1, e2]; linarith
  have hD : |D| ≤ |c2| := by
    simp only [D]
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 9 * α ^ 3),
      div_le_iff₀ (by positivity)]
    have : |6 * P1 - c2| ≤ 9 * α ^ 3 := by
      calc |6 * P1 - c2| ≤ |6 * P1| + |c2| := abs_sub _ _
        _ = 6 * |P1| + |c2| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
        _ ≤ 9 * α ^ 3 := by linarith
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  rw [hG]
  have h1 : D ^ 2 ≤ c2 ^ 2 := by
    rw [← sq_abs D, ← sq_abs c2]; exact pow_le_pow_left₀ (abs_nonneg _) hD 2
  nlinarith [sq_nonneg (c1 / 3 - D)]

/-- The box `UM` in (M2) coordinates. -/
def UM : Set Raw16 :=
  ((Iα ×ˢ Jν) ×ˢ (Iα ×ˢ Jν)) ×ˢ ((box3 (1 / 20) ×ˢ box3 (1 / 20)) ×ˢ
    (box3 (1 / 20) ×ˢ box3 (1 / 20)))

theorem box3_eq (ε : ℝ) : box3 ε = Icc (-ε) ε ×ˢ (Icc (-ε) ε ×ˢ Icc (-ε) ε) := by
  ext a; simp only [box3, mem_ofPred_eq, mem_prod, mem_Icc, abs_le]

theorem measurableSet_box3 (ε : ℝ) : MeasurableSet (box3 ε) := by
  rw [box3_eq]; exact measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)

theorem measurableSet_UM : MeasurableSet UM := by
  have hb := measurableSet_box3 (1 / 20)
  have ha : MeasurableSet (Iα ×ˢ Jν) := measurableSet_Icc.prod measurableSet_Icc
  exact (ha.prod ha).prod ((hb.prod hb).prod (hb.prod hb))

theorem P1t_le {a b : T3} (ha : a ∈ box3 (1 / 20)) (hb : b ∈ box3 (1 / 20)) :
    |P1t a b| ≤ 1 / 1000 := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  have t : ∀ x y : ℝ, |x| ≤ 1 / 20 → |y| ≤ 1 / 20 → |x ^ 2 * y| ≤ 1 / 8000 := by
    intro x y hx hy
    rw [abs_mul, abs_pow]
    calc |x| ^ 2 * |y| ≤ (1 / 20) ^ 2 * (1 / 20) := by gcongr
      _ = 1 / 8000 := by norm_num
  unfold P1t
  have := t _ _ a1 b1; have := t _ _ a2 b2; have := t _ _ a3 b3
  calc _ ≤ |a.1 ^ 2 * b.1 + a.2.1 ^ 2 * b.2.1| + |a.2.2 ^ 2 * b.2.2| := abs_add_le _ _
    _ ≤ |a.1 ^ 2 * b.1| + |a.2.1 ^ 2 * b.2.1| + |a.2.2 ^ 2 * b.2.2| := by
        gcongr; exact abs_add_le _ _
    _ ≤ 1 / 1000 := by linarith

theorem cub3_le {a : T3} (ha : a ∈ box3 (1 / 20)) : |cub3 a| ≤ 1 / 2000 := by
  have := (cub3_LB (curveOK_const ha)).1 0 ⟨by norm_num, by norm_num⟩
  simp only at this
  linarith [show (3 : ℝ) * (1 / 20) ^ 3 ≤ 1 / 2000 by norm_num]

/-- **(A1)/(M5)**: on the box, `(G↓)`'s form dominates a third of the (M5) form. -/
theorem TMx_le_SMx {α0 ν0 α1 ν1 : ℝ} {a0 b0 a1 b1 : T3} (h0 : α0 ∈ Iα) (h1 : ν0 ∈ Jν)
    (h2 : α1 ∈ Iα) (h3 : ν1 ∈ Jν) (ha0 : a0 ∈ box3 (1 / 20)) (hb0 : b0 ∈ box3 (1 / 20))
    (ha1 : a1 ∈ box3 (1 / 20)) (hb1 : b1 ∈ box3 (1 / 20)) :
    TMx α0 ν0 α1 ν1 a0 b0 a1 b1 / 3 ≤ SMx α0 ν0 α1 ν1 a0 b0 a1 b1 := by
  have e0 := A1_core (P2 := P2t a0 b0) h0 h1 (P1t_le ha0 hb0)
  have e1 := A1_core (P2 := P2t a1 b1) h2 h3 (P1t_le ha1 hb1)
  unfold TMx SMx
  nlinarith [sq_nonneg (α0 ^ 3 - 1 + cub3 a0), sq_nonneg (α1 ^ 3 - 1 + cub3 a1),
    sq_nonneg (Zr (α0 ^ 3) (α1 ^ 3) a0 a1 a0 b0), sq_nonneg (Zr (α0 ^ 3) (α1 ^ 3) a0 a1 a1 b1)]

/-! ### Two rows: the triangular Fubini (F5) -/

theorem meas3 {X : Type*} [MeasurableSpace X] {f g h : X → T3} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) {F : T3 → T3 → T3 → ENNReal}
    (hF : Measurable fun p : T3 × T3 × T3 => F p.1 p.2.1 p.2.2) :
    Measurable fun z => F (f z) (g z) (h z) :=
  hF.comp (hf.prodMk (hg.prodMk hh))

theorem two_rows {S : Set T3} (hS : MeasurableSet S) (F0 F1 : T3 → T3 → T3 → ENNReal)
    (hF0 : Measurable fun p : T3 × T3 × T3 => F0 p.1 p.2.1 p.2.2)
    (hF1 : Measurable fun p : T3 × T3 × T3 => F1 p.1 p.2.1 p.2.2) {B0 B1 : ENNReal}
    (hB0 : B0 ≠ ⊤) (Ψ : T3 → ENNReal)
    (h0 : ∀ a1 ∈ S, ∫⁻ a0 in S, ∫⁻ b0 in S, F0 a0 b0 a1 ≤ B0)
    (h1 : ∀ a0 a1, ∫⁻ b1 in S, F1 a1 b1 a0 ≤ Ψ a1) (hΨ : ∫⁻ a1 in S, Ψ a1 ≤ B1) :
    ∫⁻ w in (S ×ˢ S) ×ˢ (S ×ˢ S), F0 w.1.1 w.1.2 w.2.1 * F1 w.2.1 w.2.2 w.1.1 ≤ B0 * B1 := by
  have hW : Measurable fun w : (T3 × T3) × (T3 × T3) => F0 w.1.1 w.1.2 w.2.1 * F1 w.2.1 w.2.2 w.1.1 :=
    (hF0.comp ((measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)))).mul
    (hF1.comp ((measurable_fst.comp measurable_snd).prodMk ((measurable_snd.comp measurable_snd).prodMk
      (measurable_fst.comp measurable_fst))))
  -- F̂₀(a₀, a₁) = ∫ F₀ db₀
  set G0 : T3 → T3 → ENNReal := fun a0 a1 => ∫⁻ b0 in S, F0 a0 b0 a1 with hG0
  have hG0m : Measurable fun p : T3 × T3 => G0 p.1 p.2 := by
    have : Measurable fun q : (T3 × T3) × T3 => F0 q.1.1 q.2 q.1.2 :=
      meas3 (f := fun q : (T3 × T3) × T3 => q.1.1) (g := fun q => q.2) (h := fun q => q.1.2)
        (measurable_fst.comp measurable_fst) measurable_snd (measurable_snd.comp measurable_fst) hF0
    exact this.lintegral_prod_right'
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm _ hW.aemeasurable]
  -- inner: fixed r₁ = (a₁, b₁)
  have hin : ∀ r1 : T3 × T3, ∫⁻ r0 in S ×ˢ S, F0 r0.1 r0.2 r1.1 * F1 r1.1 r1.2 r0.1 =
      ∫⁻ a0 in S, G0 a0 r1.1 * F1 r1.1 r1.2 a0 := by
    intro r1
    have hm : Measurable fun r0 : T3 × T3 => F0 r0.1 r0.2 r1.1 * F1 r1.1 r1.2 r0.1 :=
      (meas3 (f := fun r0 : T3 × T3 => r0.1) (g := fun r0 => r0.2) (h := fun _ => r1.1)
        measurable_fst measurable_snd measurable_const hF0).mul
      (meas3 (f := fun _ : T3 × T3 => r1.1) (g := fun _ => r1.2) (h := fun r0 => r0.1)
        measurable_const measurable_const measurable_fst hF1)
    rw [Measure.volume_eq_prod, setLIntegral_prod _ hm.aemeasurable]
    refine lintegral_congr fun a0 => ?_
    try simp only
    rw [lintegral_mul_const _ (meas3 (f := fun _ : T3 => a0) (g := fun y => y)
      (h := fun _ => r1.1) measurable_const measurable_id measurable_const hF0)]
  simp_rw [hin]
  -- outer: r₁ = (a₁, b₁), swap b₁ and a₀
  have hJ : Measurable fun q : T3 × T3 × T3 => G0 q.2.2 q.1 * F1 q.1 q.2.1 q.2.2 :=
    (hG0m.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)).mul hF1
  have hJ' : Measurable fun r1 : T3 × T3 => ∫⁻ a0 in S, G0 a0 r1.1 * F1 r1.1 r1.2 a0 := by
    have : Measurable fun q : (T3 × T3) × T3 => G0 q.2 q.1.1 * F1 q.1.1 q.1.2 q.2 :=
      (hG0m.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))).mul
        (meas3 (f := fun q : (T3 × T3) × T3 => q.1.1) (g := fun q => q.1.2) (h := fun q => q.2)
          (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst) measurable_snd
          hF1)
    exact this.lintegral_prod_right'
  rw [Measure.volume_eq_prod, setLIntegral_prod _ hJ'.aemeasurable]
  calc ∫⁻ a1 in S, ∫⁻ b1 in S, ∫⁻ a0 in S, G0 a0 (a1, b1).1 * F1 (a1, b1).1 (a1, b1).2 a0
      = ∫⁻ a1 in S, ∫⁻ a0 in S, G0 a0 a1 * ∫⁻ b1 in S, F1 a1 b1 a0 := by
        refine lintegral_congr fun a1 => ?_
        try simp only
        have hsw : Measurable (Function.uncurry fun b1 a0 => G0 a0 a1 * F1 a1 b1 a0) :=
          (hJ.comp ((measurable_const (a := a1)).prodMk (measurable_fst.prodMk measurable_snd)))
        rw [lintegral_lintegral_swap hsw.aemeasurable]
        refine lintegral_congr fun a0 => ?_
        try simp only
        rw [lintegral_const_mul _ (meas3 (f := fun _ : T3 => a1) (g := fun y => y)
          (h := fun _ => a0) measurable_const measurable_id measurable_const hF1)]
    _ ≤ ∫⁻ a1 in S, ∫⁻ a0 in S, G0 a0 a1 * Ψ a1 :=
        lintegral_mono fun a1 => lintegral_mono fun a0 => by gcongr; exact h1 a0 a1
    _ = ∫⁻ a1 in S, (∫⁻ a0 in S, G0 a0 a1) * Ψ a1 := by
        refine lintegral_congr fun a1 => ?_
        exact lintegral_mul_const _ (hG0m.comp (measurable_id.prodMk measurable_const))
    _ ≤ ∫⁻ a1 in S, B0 * Ψ a1 :=
        setLIntegral_mono' hS fun a1 ha1 => by gcongr; exact h0 a1 ha1
    _ = B0 * ∫⁻ a1 in S, Ψ a1 := lintegral_const_mul' _ _ hB0
    _ ≤ B0 * B1 := by gcongr

/-! ### The integrand in product form -/

/-- `H(u₀, u₁)`: the integrand without the two `c₂` factors, with `α_k³ = u_k`. -/
noncomputable def Hw (M : ℝ) (a0 b0 a1 b1 : T3) (u : ℝ × ℝ) : ENNReal :=
  ENNReal.ofReal (Real.exp (-(M * ((u.1 - 1 + cub3 a0) ^ 2 + (P2t a0 b0 + P1t a0 b0 ^ 2 / u.1) ^ 2 +
    Zr u.1 u.2 a0 a1 a0 b0 ^ 2 + ((u.2 - 1 + cub3 a1) ^ 2 +
      (P2t a1 b1 + P1t a1 b1 ^ 2 / u.2) ^ 2 + Zr u.1 u.2 a0 a1 a1 b1 ^ 2)))))

theorem measurable_Hw (M : ℝ) : Measurable fun p : (ℝ × ℝ) × ((T3 × T3) × (T3 × T3)) =>
    Hw M p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2 p.1 := by
  unfold Hw Zr P1t P2t cub3; fun_prop

theorem split_exp (M α0 ν0 α1 ν1 : ℝ) (a0 b0 a1 b1 : T3) :
    ENNReal.ofReal (Real.exp (-(M * TMx α0 ν0 α1 ν1 a0 b0 a1 b1))) =
      ENNReal.ofReal (Real.exp (-(M * (3 * α0 ^ 2 * ν0 + 3 * P1t a0 b0) ^ 2))) *
      ENNReal.ofReal (Real.exp (-(M * (3 * α1 ^ 2 * ν1 + 3 * P1t a1 b1) ^ 2))) *
        Hw M a0 b0 a1 b1 (α0 ^ 3, α1 ^ 3) := by
  rw [Hw, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
    ← Real.exp_add, ← Real.exp_add]
  congr 2; unfold TMx; ring

/-- The shift `κ = ∑ᵢ aᵢ³ ηᵢ` of a row with amplitudes `a`. -/
def κr (u0 u1 : ℝ) (a0 a1 a : T3) : ℝ :=
  a.1 ^ 3 * (u0 - u1) + a.2.1 ^ 3 * (u0 - u1 + a0.1 ^ 3 - a1.1 ^ 3) +
    a.2.2 ^ 3 * (u0 - u1 + (a0.1 ^ 3 + a0.2.1 ^ 3) - (a1.1 ^ 3 + a1.2.1 ^ 3))

/-- Row 1 (Lean `k = 0`): weights read off row 2's amplitudes, `γ = α₀³`. -/
noncomputable def F0r (M : ℝ) (c : ℝ × ℝ) (a0 b0 a1 : T3) : ENNReal :=
  ENNReal.ofReal (rowAct (yRow c.2 fun _ => a1) (γRow c.1) M
    (κr (γRow c.1 a0) (γRow c.2 a1) a0 a1 a0) a0 b0)

/-- Row 2 (Lean `k = 1`): weights from its own amplitudes, `γ = α₁³`. -/
noncomputable def F1r (M : ℝ) (c : ℝ × ℝ) (a1 b1 a0 : T3) : ENNReal :=
  ENNReal.ofReal (rowAct (yRow c.2 id) (γRow c.2) M
    (κr (γRow c.1 a0) (γRow c.2 a1) a0 a1 a1) a1 b1)

theorem Hw_split (M : ℝ) (c : ℝ × ℝ) (a0 b0 a1 b1 : T3) :
    Hw M a0 b0 a1 b1 (c.1 + 1 - cub3 a0, c.2 + 1 - cub3 a1) =
      ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) * F0r M c a0 b0 a1 * F1r M c a1 b1 a0 := by
  have e0 : c.1 + 1 - cub3 a0 = γRow c.1 a0 := by unfold γRow; ring
  have e1 : c.2 + 1 - cub3 a1 = γRow c.2 a1 := by unfold γRow; ring
  rw [e0, e1, Hw, F0r, F1r, rowAct, rowAct, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, ← Real.exp_add]
  congr 2
  simp only [yRow, γRow, pcub0, pcub1, pcub2, id, Zr, κr, P1t, P2t]
  ring

theorem measurable_F0r (M : ℝ) (c : ℝ × ℝ) :
    Measurable fun p : T3 × T3 × T3 => F0r M c p.1 p.2.1 p.2.2 := by
  unfold F0r rowAct yRow γRow κr cub3
  simp only [pcub0, pcub1, pcub2]
  fun_prop

theorem measurable_F1r (M : ℝ) (c : ℝ × ℝ) :
    Measurable fun p : T3 × T3 × T3 => F1r M c p.1 p.2.1 p.2.2 := by
  unfold F1r rowAct yRow γRow κr cub3
  simp only [pcub0, pcub1, pcub2, id]
  fun_prop

theorem measurable_Phi (M : ℝ) : Measurable fun p : (ℝ × ℝ) × ((T3 × T3) × (T3 × T3)) =>
    ENNReal.ofReal (Real.exp (-(M * (p.1.1 ^ 2 + p.1.2 ^ 2)))) *
      F0r M p.1 p.2.1.1 p.2.1.2 p.2.2.1 * F1r M p.1 p.2.2.1 p.2.2.2 p.2.1.1 := by
  unfold F0r F1r rowAct yRow γRow κr cub3
  simp only [pcub0, pcub1, pcub2, id]
  fun_prop

/-- One row's amplitude bound, `3 C N⁻¹ (log N)²`. -/
noncomputable def BrowM (M : ℝ) : ENNReal :=
  3 * ENNReal.ofReal (CM5 (1 / 20) (CM4 (1 / 20)) * M⁻¹ * Real.log M ^ 2)

theorem BrowM_ne_top (M : ℝ) : BrowM M ≠ ⊤ :=
  ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top

/-- The inactive box `W = ([-ε,ε]³)⁴`. -/
def Wbox : Set ((T3 × T3) × (T3 × T3)) :=
  (box3 (1 / 20) ×ˢ box3 (1 / 20)) ×ˢ (box3 (1 / 20) ×ˢ box3 (1 / 20))

theorem measurableSet_Wbox : MeasurableSet Wbox := by
  have := measurableSet_box3 (1 / 20); exact (this.prod this).prod (this.prod this)

/-- **J(N; c) ≤ (3 C N⁻¹ (log N)²)²** (F5, both rows), uniformly in `|c| ≤ c₀`. -/
theorem J_bound {M : ℝ} (hM : Real.exp 1 ≤ M) {c : ℝ × ℝ} (hc : c ∈ Ic ×ˢ Ic) :
    ∫⁻ w in Wbox, F0r M c w.1.1 w.1.2 w.2.1 * F1r M c w.2.1 w.2.2 w.1.1 ≤ BrowM M * BrowM M := by
  have hc1 : |c.1| ≤ 1 / 32 := abs_le.mpr hc.1
  have hc2 : |c.2| ≤ 1 / 32 := abs_le.mpr hc.2
  have hε : (0 : ℝ) < 1 / 20 := by norm_num
  refine two_rows (measurableSet_box3 _) (F0r M c) (F1r M c) (measurable_F0r M c)
    (measurable_F1r M c) (BrowM_ne_top M) (fun a1 => ⨆ κ : ℝ, ∫⁻ b in box3 (1 / 20),
      ENNReal.ofReal (rowAct (yRow c.2 id) (γRow c.2) M κ a1 b)) (fun a1 ha1 => ?_)
    (fun a0 a1 => le_iSup (fun κ : ℝ => ∫⁻ b in box3 (1 / 20),
      ENNReal.ofReal (rowAct (yRow c.2 id) (γRow c.2) M κ a1 b)) _)
    (rowBound_M6 hε le_rfl hM hc2 hc2 measurable_id (gok_id _))
  refine le_trans (lintegral_mono fun a0 => ?_) (rowBound_M6 hε le_rfl hM hc2 hc1
    (measurable_const (a := a1)) (gok_const ha1))
  exact le_iSup (fun κ : ℝ => ∫⁻ b in box3 (1 / 20),
    ENNReal.ofReal (rowAct (yRow c.2 fun _ => a1) (γRow c.1) M κ a0 b)) _

theorem lintegral_gauss2 {M : ℝ} (hM : 0 < M) :
    ∫⁻ c : ℝ × ℝ, ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) =
      ENNReal.ofReal (Real.pi / M) := by
  have e : ∀ c : ℝ × ℝ, ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) =
      ENNReal.ofReal (Real.exp (-(M * c.1 ^ 2))) * ENNReal.ofReal (Real.exp (-(M * c.2 ^ 2))) := by
    intro c
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; congr 2; ring
  simp_rw [e]
  rw [Measure.volume_eq_prod,
    lintegral_prod_mul (f := fun x : ℝ => ENNReal.ofReal (Real.exp (-(M * x ^ 2))))
      (g := fun x : ℝ => ENNReal.ofReal (Real.exp (-(M * x ^ 2)))) (by fun_prop) (by fun_prop),
    lintegral_gaussian hM, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    Real.mul_self_sqrt (by positivity)]

/-- F1–F3 at a fixed inactive point. -/
theorem UM_inner {M : ℝ} (hM0 : 0 < M) (a0 b0 a1 b1 : T3) (ha0 : a0 ∈ box3 (1 / 20))
    (ha1 : a1 ∈ box3 (1 / 20)) :
    ∫⁻ z in (Iα ×ˢ Jν) ×ˢ (Iα ×ˢ Jν),
        ENNReal.ofReal (Real.exp (-(M * TMx z.1.1 z.1.2 z.2.1 z.2.2 a0 b0 a1 b1))) ≤
      ENNReal.ofReal (Real.pi / M) * 4⁻¹ * ∫⁻ c in Ic ×ˢ Ic,
        ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) * F0r M c a0 b0 a1 *
          F1r M c a1 b1 a0 := by
  have hH : Measurable (Hw M a0 b0 a1 b1) := by unfold Hw Zr P1t P2t cub3; fun_prop
  have h := active_bound hM0 (fun _ => 3 * P1t a0 b0) (fun _ => 3 * P1t a1 b1) measurable_const
    measurable_const (Hw M a0 b0 a1 b1) hH (cub3_le ha0) (cub3_le ha1)
  have e1 : ∫⁻ z in (Iα ×ˢ Jν) ×ˢ (Iα ×ˢ Jν),
      ENNReal.ofReal (Real.exp (-(M * TMx z.1.1 z.1.2 z.2.1 z.2.2 a0 b0 a1 b1))) =
      ∫⁻ z in (Iα ×ˢ Jν) ×ˢ (Iα ×ˢ Jν),
        ENNReal.ofReal (Real.exp (-(M * (3 * z.1.1 ^ 2 * z.1.2 + 3 * P1t a0 b0) ^ 2))) *
        ENNReal.ofReal (Real.exp (-(M * (3 * z.2.1 ^ 2 * z.2.2 + 3 * P1t a1 b1) ^ 2))) *
          Hw M a0 b0 a1 b1 (z.1.1 ^ 3, z.2.1 ^ 3) :=
    lintegral_congr fun z => split_exp M z.1.1 z.1.2 z.2.1 z.2.2 a0 b0 a1 b1
  have e2 : ∫⁻ c in Ic ×ˢ Ic, Hw M a0 b0 a1 b1 (c.1 + 1 - cub3 a0, c.2 + 1 - cub3 a1) =
      ∫⁻ c in Ic ×ˢ Ic, ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) *
        F0r M c a0 b0 a1 * F1r M c a1 b1 a0 :=
    lintegral_congr fun c => Hw_split M c a0 b0 a1 b1
  rw [e1, ← e2]
  exact h

/-- F5 + F6 at fixed `c`. -/
theorem UM_c {M : ℝ} (hM : Real.exp 1 ≤ M) {c : ℝ × ℝ} (hc : c ∈ Ic ×ˢ Ic) :
    ∫⁻ w in Wbox, ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) *
        F0r M c w.1.1 w.1.2 w.2.1 * F1r M c w.2.1 w.2.2 w.1.1 ≤
      ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) * (BrowM M * BrowM M) := by
  have hm : Measurable fun w : (T3 × T3) × (T3 × T3) =>
      F0r M c w.1.1 w.1.2 w.2.1 * F1r M c w.2.1 w.2.2 w.1.1 :=
    (meas3 (f := fun w : (T3 × T3) × (T3 × T3) => w.1.1) (g := fun w => w.1.2)
      (h := fun w => w.2.1) (measurable_fst.comp measurable_fst)
      (measurable_snd.comp measurable_fst) (measurable_fst.comp measurable_snd)
      (measurable_F0r M c)).mul
    (meas3 (f := fun w : (T3 × T3) × (T3 × T3) => w.2.1) (g := fun w => w.2.2)
      (h := fun w => w.1.1) (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd) (measurable_fst.comp measurable_fst)
      (measurable_F1r M c))
  have e : ∫⁻ w in Wbox, ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) *
        F0r M c w.1.1 w.1.2 w.2.1 * F1r M c w.2.1 w.2.2 w.1.1 =
      ∫⁻ w in Wbox, ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) *
        (F0r M c w.1.1 w.1.2 w.2.1 * F1r M c w.2.1 w.2.2 w.1.1) :=
    lintegral_congr fun w => mul_assoc _ _ _
  rw [e, lintegral_const_mul _ hm]
  exact mul_le_mul' le_rfl (J_bound hM hc)

/-- The full box integral of the (M5) form: `≤ (π/M)·¼·(π/M)·(3 C M⁻¹ (log M)²)²`. -/
theorem UM_bound {M : ℝ} (hM : Real.exp 1 ≤ M) :
    ∫⁻ y in UM, ENNReal.ofReal (Real.exp (-(M * TMx y.1.1.1 y.1.1.2 y.1.2.1 y.1.2.2 y.2.1.1
      y.2.1.2 y.2.2.1 y.2.2.2))) ≤
      ENNReal.ofReal (Real.pi / M) * 4⁻¹ * (ENNReal.ofReal (Real.pi / M) * (BrowM M * BrowM M)) := by
  have hM0 : 0 < M := lt_of_lt_of_le (Real.exp_pos 1) hM
  have hfm : Measurable fun y : Raw16 => ENNReal.ofReal (Real.exp (-(M * TMx y.1.1.1 y.1.1.2
      y.1.2.1 y.1.2.2 y.2.1.1 y.2.1.2 y.2.2.1 y.2.2.2))) := by
    unfold TMx Zr P1t P2t cub3; fun_prop
  have hU : UM = ((Iα ×ˢ Jν) ×ˢ (Iα ×ˢ Jν)) ×ˢ Wbox := rfl
  rw [hU, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm _ hfm.aemeasurable]
  refine (setLIntegral_mono' measurableSet_Wbox fun w hw =>
    UM_inner hM0 w.1.1 w.1.2 w.2.1 w.2.2 hw.1.1 hw.2.1).trans ?_
  have hsw : Measurable (Function.uncurry fun (a : (T3 × T3) × (T3 × T3)) (c : ℝ × ℝ) =>
      ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) * F0r M c a.1.1 a.1.2 a.2.1 *
        F1r M c a.2.1 a.2.2 a.1.1) := by
    unfold Function.uncurry F0r F1r rowAct yRow γRow κr cub3
    simp only [pcub0, pcub1, pcub2, id]
    fun_prop
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)),
    lintegral_lintegral_swap hsw.aemeasurable]
  gcongr
  refine (setLIntegral_mono' (measurableSet_Icc.prod measurableSet_Icc) fun c hc =>
    UM_c hM hc).trans ?_
  rw [lintegral_mul_const _ (by fun_prop)]
  exact mul_le_mul' ((setLIntegral_le_lintegral _ _).trans (le_of_eq (lintegral_gauss2 hM0))) le_rfl

theorem SMx_nonneg (α0 ν0 α1 ν1 : ℝ) (a0 b0 a1 b1 : T3) : 0 ≤ SMx α0 ν0 α1 ν1 a0 b0 a1 b1 := by
  unfold SMx; positivity

theorem UM_bound_real {M : ℝ} (hM : Real.exp 1 ≤ M) :
    ENNReal.ofReal (Real.pi / M) * 4⁻¹ * (ENNReal.ofReal (Real.pi / M) * (BrowM M * BrowM M)) =
      ENNReal.ofReal (Real.pi ^ 2 * 9 * CM5 (1 / 20) (CM4 (1 / 20)) ^ 2 / 4 * M⁻¹ ^ 4 *
        Real.log M ^ 4) := by
  have hM0 : 0 < M := lt_of_lt_of_le (Real.exp_pos 1) hM
  have hl : 0 ≤ Real.log M := Real.log_nonneg (le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hM)
  have hc5 : 0 ≤ CM5 (1 / 20) (CM4 (1 / 20)) := by
    have h1 := M3const_pos
    have h2 : 0 < CM4 (1 / 20) := by
      unfold CM4; have := Kslice_pos (by norm_num : (0 : ℝ) < 1 / 20); positivity
    have h3 := Real.posLog_nonneg (x := (1 / 20 : ℝ) * (32 * (1 / 20) ^ 3 /
      (CM4 (1 / 20) * M3const)) ^ ((1 : ℝ) / 3))
    unfold CM5; positivity
  have hx : 0 ≤ CM5 (1 / 20) (CM4 (1 / 20)) * M⁻¹ * Real.log M ^ 2 := by positivity
  have h3 : BrowM M = ENNReal.ofReal (3 * (CM5 (1 / 20) (CM4 (1 / 20)) * M⁻¹ * Real.log M ^ 2)) := by
    rw [BrowM, ENNReal.ofReal_mul (p := 3) (by norm_num), ENNReal.ofReal_ofNat]
  have h4 : (4 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 4) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  rw [h3, h4, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

/-- **Theorem M (upper bound), decomposition §0.** For any input law with finite 162nd
moments and a density bounded below on some box, and any prior × cutoff at position one
bounded by `π₁` and supported (in (M2) coordinates) in the box `UM`
(`|α_k - 1|, |ν_k| ≤ 1/100`, `|a|, |b| ≤ 1/20`):
`Z_{N,1} ≤ C N⁻⁴ (log N)⁴` for all large `N`. -/
theorem theoremM (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ)
    (φ χ : Raw16 → ENNReal) {π₁ : ℝ} (hπ₁ : 0 ≤ π₁)
    (hπ : ∀ θ, φ θ * χ (θ - basePos A0 0) ≤
      (toM2 ⁻¹' UM).indicator (fun _ => ENNReal.ofReal π₁) θ) :
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      Zpos μ A0 φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4 * Real.log N ^ 4) := by
  obtain ⟨κ, hκ, hG⟩ := Gdown μ hmom hlh hμ₀ hμ
  obtain ⟨κ', hκ'⟩ : ∃ κ', κ' = min κ 1 / 3 := ⟨_, rfl⟩
  have hκ'0 : 0 < κ' := by rw [hκ']; exact div_pos (lt_min hκ one_pos) (by norm_num)
  have hκ'1 : κ' ≤ 1 := by rw [hκ']; linarith [min_le_right κ 1]
  obtain ⟨Kc, hKc⟩ : ∃ Kc, Kc = Real.pi ^ 2 * 9 * CM5 (1 / 20) (CM4 (1 / 20)) ^ 2 / 4 :=
    ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  refine ⟨π₁ * Kc * κ'⁻¹ ^ 4, Real.exp 1 / κ', fun N hN => ?_⟩
  have hM : Real.exp 1 ≤ κ' * N := by
    rw [div_le_iff₀ hκ'0] at hN; linarith
  have hN0 : 0 < N := by
    have := Real.exp_pos 1
    have : 0 < κ' * N := by linarith
    exact pos_of_mul_pos_right this hκ'0.le
  have hset : MeasurableSet (toM2 ⁻¹' UM) := measurableSet_UM.preimage measurable_toM2
  set g : Raw16 → ENNReal := fun y => ENNReal.ofReal (Real.exp (-((κ' * N) * TMx y.1.1.1 y.1.1.2
    y.1.2.1 y.1.2.2 y.2.1.1 y.2.1.2 y.2.2.1 y.2.2.2))) with hg
  have hgm : Measurable g := by simp only [hg]; unfold TMx Zr P1t P2t cub3; fun_prop
  -- pointwise: (G↓) and (A1)
  have hpt : ∀ θ ∈ toM2 ⁻¹' UM,
      ENNReal.ofReal (Real.exp (-(N * popLossA μ A0 θ))) ≤ g (toM2 θ) := by
    intro θ hθ
    obtain ⟨⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩, ⟨⟨ha0, hb0⟩, ⟨ha1, hb1⟩⟩⟩ := hθ
    have hT := TMx_le_SMx h0 h1 h2 h3 ha0 hb0 ha1 hb1
    have hS0 := SMx_nonneg (toM2 θ).1.1.1 (toM2 θ).1.1.2 (toM2 θ).1.2.1 (toM2 θ).1.2.2
      (toM2 θ).2.1.1 (toM2 θ).2.1.2 (toM2 θ).2.2.1 (toM2 θ).2.2.2
    have hGθ := hG θ
    rw [sum_coeffs_eq] at hGθ
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hmin : min κ 1 * SMx (toM2 θ).1.1.1 (toM2 θ).1.1.2 (toM2 θ).1.2.1 (toM2 θ).1.2.2
        (toM2 θ).2.1.1 (toM2 θ).2.1.2 (toM2 θ).2.2.1 (toM2 θ).2.2.2 ≤ popLossA μ A0 θ :=
      le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hS0) hGθ
    have hT0 : 0 ≤ TMx (toM2 θ).1.1.1 (toM2 θ).1.1.2 (toM2 θ).1.2.1 (toM2 θ).1.2.2
        (toM2 θ).2.1.1 (toM2 θ).2.1.2 (toM2 θ).2.2.1 (toM2 θ).2.2.2 := by unfold TMx; positivity
    have hm0 : 0 ≤ min κ 1 := le_min hκ.le zero_le_one
    rw [hκ']
    nlinarith [mul_le_mul_of_nonneg_left hT hm0, mul_le_mul_of_nonneg_left hmin hN0.le]
  calc Zpos μ A0 φ χ 0 N
      = ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * popLossA μ A0 θ))) *
          (φ θ * χ (θ - basePos A0 0)) := rfl
    _ ≤ ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * popLossA μ A0 θ))) *
          (toM2 ⁻¹' UM).indicator (fun _ => ENNReal.ofReal π₁) θ :=
        lintegral_mono fun θ => mul_le_mul' le_rfl (hπ θ)
    _ = ∫⁻ θ in toM2 ⁻¹' UM, ENNReal.ofReal (Real.exp (-(N * popLossA μ A0 θ))) *
          ENNReal.ofReal π₁ := by
        rw [← lintegral_indicator hset]
        refine lintegral_congr fun θ => ?_
        exact (indicator_mul_right (toM2 ⁻¹' UM)
          (fun θ => ENNReal.ofReal (Real.exp (-(N * popLossA μ A0 θ))))
          (fun _ => ENNReal.ofReal π₁)).symm
    _ ≤ ∫⁻ θ in toM2 ⁻¹' UM, g (toM2 θ) * ENNReal.ofReal π₁ :=
        setLIntegral_mono' hset fun θ hθ => mul_le_mul' (hpt θ hθ) le_rfl
    _ = (∫⁻ y in UM, g y) * ENNReal.ofReal π₁ := by
        have hgc : Measurable fun θ => g (toM2 θ) := hgm.comp measurable_toM2
        rw [lintegral_mul_const _ hgc,
          measurePreserving_toM2.setLIntegral_comp_preimage measurableSet_UM hgm]
    _ ≤ ENNReal.ofReal (Kc * (κ' * N)⁻¹ ^ 4 * Real.log (κ' * N) ^ 4) * ENNReal.ofReal π₁ := by
        gcongr
        rw [hKc, ← UM_bound_real hM]
        exact UM_bound hM
    _ ≤ ENNReal.ofReal (π₁ * Kc * κ'⁻¹ ^ 4 * N⁻¹ ^ 4 * Real.log N ^ 4) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hl0 : 0 ≤ Real.log (κ' * N) :=
          Real.log_nonneg (le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hM)
        have hl1 : Real.log (κ' * N) ≤ Real.log N := by
          rw [Real.log_mul hκ'0.ne' hN0.ne']
          linarith [Real.log_nonpos hκ'0.le hκ'1]
        have hl4 : Real.log (κ' * N) ^ 4 ≤ Real.log N ^ 4 := pow_le_pow_left₀ hl0 hl1 4
        rw [mul_inv, mul_pow]
        have : 0 ≤ Kc * (κ'⁻¹ ^ 4 * N⁻¹ ^ 4) * π₁ := by positivity
        calc Kc * (κ'⁻¹ ^ 4 * N⁻¹ ^ 4) * Real.log (κ' * N) ^ 4 * π₁
            = Kc * (κ'⁻¹ ^ 4 * N⁻¹ ^ 4) * π₁ * Real.log (κ' * N) ^ 4 := by ring
          _ ≤ Kc * (κ'⁻¹ ^ 4 * N⁻¹ ^ 4) * π₁ * Real.log N ^ 4 :=
              mul_le_mul_of_nonneg_left hl4 this
          _ = _ := by ring

/-! ### Corollaries: raw-coordinate support, and the two-sided estimate -/

/-- The raw ball `‖θ - θ₀‖ ≤ 1/200` (sup norm) lies in the (M2) box. -/
theorem toM2_mem_UM {θ : Raw16} (h : ‖θ - basePos A0 0‖ ≤ 1 / 200) : toM2 θ ∈ UM := by
  obtain ⟨⟨⟨m00, m01⟩, ⟨m10, m11⟩⟩, ⟨⟨⟨p0, p1, p2⟩, ⟨q0, q1, q2⟩⟩, ⟨⟨r0, r1, r2⟩, ⟨s0, s1, s2⟩⟩⟩⟩ := θ
  rw [basePos_zero] at h
  simp only [baseA, A0, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Prod.norm_def, max_le_iff,
    Real.norm_eq_abs, sub_zero, abs_le, Prod.mk_sub_mk] at h
  simp only [toM2, UM, mem_prod, Iα, Jν, box3, mem_Icc, mem_ofPred_eq, abs_le, Prod.mk_add_mk]
  repeat' constructor
  all_goals linarith

/-- **Theorem M, raw form.** Prior bounded by `π₁`, cutoff bounded by `1` and supported in
the sup-norm ball of radius `1/200`. -/
theorem theoremM_raw (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ)
    (φ χ : Raw16 → ENNReal) {π₁ : ℝ} (hπ₁ : 0 ≤ π₁) (hφ : ∀ θ, φ θ ≤ ENNReal.ofReal π₁)
    (hχ : ∀ θ, χ θ ≤ 1) (hχs : ∀ θ, 1 / 200 < ‖θ‖ → χ θ = 0) :
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      Zpos μ A0 φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4 * Real.log N ^ 4) := by
  refine theoremM μ hmom hlh hμ₀ hμ φ χ hπ₁ fun θ => ?_
  by_cases hθ : toM2 θ ∈ UM
  · rw [indicator_of_mem (show θ ∈ toM2 ⁻¹' UM from hθ)]
    calc φ θ * χ (θ - basePos A0 0) ≤ ENNReal.ofReal π₁ * 1 := mul_le_mul' (hφ θ) (hχ _)
      _ = _ := mul_one _
  · have : 1 / 200 < ‖θ - basePos A0 0‖ := by
      by_contra hc; exact hθ (toM2_mem_UM (not_lt.mp hc))
    rw [hχs _ this, mul_zero]; exact bot_le

theorem shearTarget_A0 : ShearTarget A0 :=
  ⟨![1, 1], ![1, -1], fun i j => by fin_cases i <;> fin_cases j <;> simp [A0],
    by simp, by simp, fun h => by simpa using congrFun h 0, by simp⟩

/-- **`Z_{N,1} ≍ N⁻⁴ (log N)⁴`**: Proposition L′'s lower bound and Theorem M's upper bound,
for a compactly supported input law with a density bounded below on some box. -/
theorem ZN1_two_sided (μ : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure μ] {R : ℝ}
    (hμR : ∀ᵐ x ∂μ, ∀ i, |x i| ≤ R) {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ}
    (hμ₀ : 0 < μ₀) (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ)
    (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ} (hφ₀ : 0 < φ₀) (hχ₀ : 0 < χ₀)
    (hφl : ∀ᶠ θ in nhds (basePos A0 0), ENNReal.ofReal φ₀ ≤ φ θ)
    (hχl : ∀ᶠ θ in nhds 0, ENNReal.ofReal χ₀ ≤ χ θ)
    (hπ₁ : 0 ≤ π₁) (hφ : ∀ θ, φ θ ≤ ENNReal.ofReal π₁)
    (hχ : ∀ θ, χ θ ≤ 1) (hχs : ∀ θ, 1 / 200 < ‖θ‖ → χ θ = 0) :
    ∃ c C N₀ : ℝ, 0 < c ∧ ∀ N : ℝ, N₀ ≤ N →
      ENNReal.ofReal (c * N⁻¹ ^ 4 * Real.log N ^ 4) ≤ Zpos μ A0 φ χ 0 N ∧
        Zpos μ A0 φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4 * Real.log N ^ 4) := by
  have hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ := by
    intro i
    have hm : Measurable fun x : Fin 2 → ℝ => |x i| ^ (2 * 81) := by fun_prop
    refine Integrable.of_mem_Icc 0 (R ^ (2 * 81)) hm.aemeasurable ?_
    filter_upwards [hμR] with x hx
    exact ⟨by positivity, pow_le_pow_left₀ (abs_nonneg _) (hx i) _⟩
  obtain ⟨c, hc, N₁, hlow⟩ := Zpos_one_lower shearTarget_A0 μ hμR φ χ hφ₀ hχ₀ hφl hχl
  obtain ⟨C, N₂, hup⟩ := theoremM_raw μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs
  exact ⟨c, C, max N₁ N₂, hc, fun N hN =>
    ⟨hlow N ((le_max_left _ _).trans hN), hup N ((le_max_right _ _).trans hN)⟩⟩

end VectorSLT
