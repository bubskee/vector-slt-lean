/-
X5, step 4: Theorem M for the near-shear target `A_η`, with constants independent of `η`.

The assembly of `theoremM` with three changes:
* (G↓) is `Gdown_eta`: `c₂, c₁` become `c₂ - 3η = 3α²ν + 3(P₁ - η)` and
  `c₁ - 3η² = 3αν² + 3(P₂ - η²)`; `c₃` and `Z` are unchanged (Lemma X2); `κ` is uniform in `η`.
* (A1) is `A1_core` with `(P₁, P₂)` replaced by `(P₁ - η, P₂ - η²)`. Its hypothesis `|P₁| ≤ 1/1000`
  becomes `|P₁ - η| ≤ 1/100` (`A1_core'`), which holds on the box for `|η| ≤ 9/1000`.
  So `G` becomes `G_η = (P₂ - η²) + (P₁ - η)²/α³`.
* The row bound is `rowBound_M6_eta` (Lemma M4 for `G_η`, same constant).
The box `UM` (`|α_k - 1|, |ν_k| ≤ 1/100`, `|a|, |b| ≤ 1/20`) is unchanged: nothing uses
`ν_k ≈ 0` beyond `|ν_k| ≤ 1/100`.
-/
import VectorSLT.TheoremM
import VectorSLT.EtaUpper.GdownEta
import VectorSLT.EtaUpper.RowBoundEta

namespace VectorSLT

open MeasureTheory Set VectorSLT.SLT

/-! ### Explicit coordinates -/

/-- The ten-generator form (M5) for `A_η`, explicit. -/
noncomputable def TMxη (η α0 ν0 α1 ν1 : ℝ) (a0 b0 a1 b1 : T3) : ℝ :=
  (α0 ^ 3 - 1 + cub3 a0) ^ 2 + (3 * α0 ^ 2 * ν0 + 3 * (P1t a0 b0 - η)) ^ 2 +
    ((P2t a0 b0 - η ^ 2) + (P1t a0 b0 - η) ^ 2 / α0 ^ 3) ^ 2 + Zr (α0 ^ 3) (α1 ^ 3) a0 a1 a0 b0 ^ 2 +
  ((α1 ^ 3 - 1 + cub3 a1) ^ 2 + (3 * α1 ^ 2 * ν1 + 3 * (P1t a1 b1 - η)) ^ 2 +
    ((P2t a1 b1 - η ^ 2) + (P1t a1 b1 - η) ^ 2 / α1 ^ 3) ^ 2 + Zr (α0 ^ 3) (α1 ^ 3) a0 a1 a1 b1 ^ 2)

/-- The four-coefficient form of `Gdown_eta`, explicit. -/
noncomputable def SMxη (η α0 ν0 α1 ν1 : ℝ) (a0 b0 a1 b1 : T3) : ℝ :=
  (α0 ^ 3 - 1 + cub3 a0) ^ 2 + (3 * α0 ^ 2 * ν0 + 3 * (P1t a0 b0 - η)) ^ 2 +
    (3 * α0 * ν0 ^ 2 + 3 * (P2t a0 b0 - η ^ 2)) ^ 2 + Zr (α0 ^ 3) (α1 ^ 3) a0 a1 a0 b0 ^ 2 +
  ((α1 ^ 3 - 1 + cub3 a1) ^ 2 + (3 * α1 ^ 2 * ν1 + 3 * (P1t a1 b1 - η)) ^ 2 +
    (3 * α1 * ν1 ^ 2 + 3 * (P2t a1 b1 - η ^ 2)) ^ 2 + Zr (α0 ^ 3) (α1 ^ 3) a0 a1 a1 b1 ^ 2)

theorem sum_coeffs_eq_eta (η : ℝ) (θ : Raw16) :
    ∑ k, (c3M θ k ^ 2 + c2Mη η θ k ^ 2 + c1Mη η θ k ^ 2 + ZM θ k ^ 2) =
      SMxη η (toM2 θ).1.1.1 (toM2 θ).1.1.2 (toM2 θ).1.2.1 (toM2 θ).1.2.2 (toM2 θ).2.1.1
        (toM2 θ).2.1.2 (toM2 θ).2.2.1 (toM2 θ).2.2.2 := by
  unfold c3M c2Mη c1Mη ZM
  generalize toM2 θ = y
  obtain ⟨⟨⟨α0, ν0⟩, ⟨α1, ν1⟩⟩, ⟨⟨a0, b0⟩, ⟨a1, b1⟩⟩⟩ := y
  simp only [Fin.sum_univ_two, SMxη, Zmom, etaM, yM, Zr, actα, actν, inA, inB,
    momA, momP1, momP2, P1t, P2t, cub3, tri0, tri1, tri2, Finset.sum_range_succ,
    Finset.sum_range_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-! ### (A1) with the shifted moments -/

/-- `A1_core` under the weaker hypothesis `|P₁| ≤ 1/100` (used at `P₁ - η`). -/
theorem A1_core' {α ν P1 P2 : ℝ} (hα : α ∈ Iα) (hν : ν ∈ Jν) (hP1 : |P1| ≤ 1 / 100) :
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

theorem P1t_sub_le {a b : T3} (ha : a ∈ box3 (1 / 20)) (hb : b ∈ box3 (1 / 20)) {η : ℝ}
    (hη : |η| ≤ 9 / 1000) : |P1t a b - η| ≤ 1 / 100 := by
  have := P1t_le ha hb
  have := abs_sub (P1t a b) η
  linarith

/-- **(A1)/(M5) for `A_η`**: on the box, `Gdown_eta`'s form dominates a third of `TMxη`. -/
theorem TMxη_le_SMxη {η α0 ν0 α1 ν1 : ℝ} {a0 b0 a1 b1 : T3} (hη : |η| ≤ 9 / 1000)
    (h0 : α0 ∈ Iα) (h1 : ν0 ∈ Jν)
    (h2 : α1 ∈ Iα) (h3 : ν1 ∈ Jν) (ha0 : a0 ∈ box3 (1 / 20)) (hb0 : b0 ∈ box3 (1 / 20))
    (ha1 : a1 ∈ box3 (1 / 20)) (hb1 : b1 ∈ box3 (1 / 20)) :
    TMxη η α0 ν0 α1 ν1 a0 b0 a1 b1 / 3 ≤ SMxη η α0 ν0 α1 ν1 a0 b0 a1 b1 := by
  have e0 := A1_core' (P2 := P2t a0 b0 - η ^ 2) h0 h1 (P1t_sub_le ha0 hb0 hη)
  have e1 := A1_core' (P2 := P2t a1 b1 - η ^ 2) h2 h3 (P1t_sub_le ha1 hb1 hη)
  unfold TMxη SMxη
  nlinarith [sq_nonneg (α0 ^ 3 - 1 + cub3 a0), sq_nonneg (α1 ^ 3 - 1 + cub3 a1),
    sq_nonneg (Zr (α0 ^ 3) (α1 ^ 3) a0 a1 a0 b0), sq_nonneg (Zr (α0 ^ 3) (α1 ^ 3) a0 a1 a1 b1)]

/-! ### The integrand in product form -/

/-- `H_η(u₀, u₁)`: the integrand without the two `c₂ - 3η` factors, with `α_k³ = u_k`. -/
noncomputable def Hwη (M η : ℝ) (a0 b0 a1 b1 : T3) (u : ℝ × ℝ) : ENNReal :=
  ENNReal.ofReal (Real.exp (-(M * ((u.1 - 1 + cub3 a0) ^ 2 +
    ((P2t a0 b0 - η ^ 2) + (P1t a0 b0 - η) ^ 2 / u.1) ^ 2 +
    Zr u.1 u.2 a0 a1 a0 b0 ^ 2 + ((u.2 - 1 + cub3 a1) ^ 2 +
      ((P2t a1 b1 - η ^ 2) + (P1t a1 b1 - η) ^ 2 / u.2) ^ 2 + Zr u.1 u.2 a0 a1 a1 b1 ^ 2)))))

theorem split_exp_eta (M η α0 ν0 α1 ν1 : ℝ) (a0 b0 a1 b1 : T3) :
    ENNReal.ofReal (Real.exp (-(M * TMxη η α0 ν0 α1 ν1 a0 b0 a1 b1))) =
      ENNReal.ofReal (Real.exp (-(M * (3 * α0 ^ 2 * ν0 + 3 * (P1t a0 b0 - η)) ^ 2))) *
      ENNReal.ofReal (Real.exp (-(M * (3 * α1 ^ 2 * ν1 + 3 * (P1t a1 b1 - η)) ^ 2))) *
        Hwη M η a0 b0 a1 b1 (α0 ^ 3, α1 ^ 3) := by
  rw [Hwη, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
    ← Real.exp_add, ← Real.exp_add]
  congr 2; unfold TMxη; ring

/-- Row 1 (Lean `k = 0`) for `A_η`. -/
noncomputable def F0rη (M η : ℝ) (c : ℝ × ℝ) (a0 b0 a1 : T3) : ENNReal :=
  ENNReal.ofReal (rowActη (yRow c.2 fun _ => a1) (γRow c.1) M
    (κr (γRow c.1 a0) (γRow c.2 a1) a0 a1 a0) η a0 b0)

/-- Row 2 (Lean `k = 1`) for `A_η`. -/
noncomputable def F1rη (M η : ℝ) (c : ℝ × ℝ) (a1 b1 a0 : T3) : ENNReal :=
  ENNReal.ofReal (rowActη (yRow c.2 id) (γRow c.2) M
    (κr (γRow c.1 a0) (γRow c.2 a1) a0 a1 a1) η a1 b1)

theorem Hwη_split (M η : ℝ) (c : ℝ × ℝ) (a0 b0 a1 b1 : T3) :
    Hwη M η a0 b0 a1 b1 (c.1 + 1 - cub3 a0, c.2 + 1 - cub3 a1) =
      ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) * F0rη M η c a0 b0 a1 *
        F1rη M η c a1 b1 a0 := by
  have e0 : c.1 + 1 - cub3 a0 = γRow c.1 a0 := by unfold γRow; ring
  have e1 : c.2 + 1 - cub3 a1 = γRow c.2 a1 := by unfold γRow; ring
  rw [e0, e1, Hwη, F0rη, F1rη, rowActη, rowActη, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, ← Real.exp_add]
  congr 2
  simp only [yRow, γRow, pcub0, pcub1, pcub2, id, Zr, κr, P1t, P2t]
  ring

theorem measurable_F0rη (M η : ℝ) (c : ℝ × ℝ) :
    Measurable fun p : T3 × T3 × T3 => F0rη M η c p.1 p.2.1 p.2.2 := by
  unfold F0rη rowActη yRow γRow κr cub3
  simp only [pcub0, pcub1, pcub2]
  fun_prop

theorem measurable_F1rη (M η : ℝ) (c : ℝ × ℝ) :
    Measurable fun p : T3 × T3 × T3 => F1rη M η c p.1 p.2.1 p.2.2 := by
  unfold F1rη rowActη yRow γRow κr cub3
  simp only [pcub0, pcub1, pcub2, id]
  fun_prop

/-- **J(N; c) ≤ (3 C N⁻¹ (log N)²)²** for `A_η`, uniformly in `|c| ≤ c₀` and in `η`. -/
theorem J_bound_eta {M : ℝ} (hM : Real.exp 1 ≤ M) (η : ℝ) {c : ℝ × ℝ} (hc : c ∈ Ic ×ˢ Ic) :
    ∫⁻ w in Wbox, F0rη M η c w.1.1 w.1.2 w.2.1 * F1rη M η c w.2.1 w.2.2 w.1.1 ≤
      BrowM M * BrowM M := by
  have hc1 : |c.1| ≤ 1 / 32 := abs_le.mpr hc.1
  have hc2 : |c.2| ≤ 1 / 32 := abs_le.mpr hc.2
  have hε : (0 : ℝ) < 1 / 20 := by norm_num
  refine two_rows (measurableSet_box3 _) (F0rη M η c) (F1rη M η c) (measurable_F0rη M η c)
    (measurable_F1rη M η c) (BrowM_ne_top M) (fun a1 => ⨆ κ : ℝ, ∫⁻ b in box3 (1 / 20),
      ENNReal.ofReal (rowActη (yRow c.2 id) (γRow c.2) M κ η a1 b)) (fun a1 ha1 => ?_)
    (fun a0 a1 => le_iSup (fun κ : ℝ => ∫⁻ b in box3 (1 / 20),
      ENNReal.ofReal (rowActη (yRow c.2 id) (γRow c.2) M κ η a1 b)) _)
    (rowBound_M6_eta hε le_rfl hM η hc2 hc2 measurable_id (gok_id _))
  refine le_trans (lintegral_mono fun a0 => ?_) (rowBound_M6_eta hε le_rfl hM η hc2 hc1
    (measurable_const (a := a1)) (gok_const ha1))
  exact le_iSup (fun κ : ℝ => ∫⁻ b in box3 (1 / 20),
    ENNReal.ofReal (rowActη (yRow c.2 fun _ => a1) (γRow c.1) M κ η a0 b)) _

/-- F1–F3 at a fixed inactive point, `A_η`. -/
theorem UM_inner_eta {M : ℝ} (hM0 : 0 < M) (η : ℝ) (a0 b0 a1 b1 : T3) (ha0 : a0 ∈ box3 (1 / 20))
    (ha1 : a1 ∈ box3 (1 / 20)) :
    ∫⁻ z in (Iα ×ˢ Jν) ×ˢ (Iα ×ˢ Jν),
        ENNReal.ofReal (Real.exp (-(M * TMxη η z.1.1 z.1.2 z.2.1 z.2.2 a0 b0 a1 b1))) ≤
      ENNReal.ofReal (Real.pi / M) * 4⁻¹ * ∫⁻ c in Ic ×ˢ Ic,
        ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) * F0rη M η c a0 b0 a1 *
          F1rη M η c a1 b1 a0 := by
  have hH : Measurable (Hwη M η a0 b0 a1 b1) := by unfold Hwη Zr P1t P2t cub3; fun_prop
  have h := active_bound hM0 (fun _ => 3 * (P1t a0 b0 - η)) (fun _ => 3 * (P1t a1 b1 - η))
    measurable_const measurable_const (Hwη M η a0 b0 a1 b1) hH (cub3_le ha0) (cub3_le ha1)
  have e1 : ∫⁻ z in (Iα ×ˢ Jν) ×ˢ (Iα ×ˢ Jν),
      ENNReal.ofReal (Real.exp (-(M * TMxη η z.1.1 z.1.2 z.2.1 z.2.2 a0 b0 a1 b1))) =
      ∫⁻ z in (Iα ×ˢ Jν) ×ˢ (Iα ×ˢ Jν),
        ENNReal.ofReal (Real.exp (-(M * (3 * z.1.1 ^ 2 * z.1.2 + 3 * (P1t a0 b0 - η)) ^ 2))) *
        ENNReal.ofReal (Real.exp (-(M * (3 * z.2.1 ^ 2 * z.2.2 + 3 * (P1t a1 b1 - η)) ^ 2))) *
          Hwη M η a0 b0 a1 b1 (z.1.1 ^ 3, z.2.1 ^ 3) :=
    lintegral_congr fun z => split_exp_eta M η z.1.1 z.1.2 z.2.1 z.2.2 a0 b0 a1 b1
  have e2 : ∫⁻ c in Ic ×ˢ Ic, Hwη M η a0 b0 a1 b1 (c.1 + 1 - cub3 a0, c.2 + 1 - cub3 a1) =
      ∫⁻ c in Ic ×ˢ Ic, ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) *
        F0rη M η c a0 b0 a1 * F1rη M η c a1 b1 a0 :=
    lintegral_congr fun c => Hwη_split M η c a0 b0 a1 b1
  rw [e1, ← e2]
  exact h

/-- F5 + F6 at fixed `c`, `A_η`. -/
theorem UM_c_eta {M : ℝ} (hM : Real.exp 1 ≤ M) (η : ℝ) {c : ℝ × ℝ} (hc : c ∈ Ic ×ˢ Ic) :
    ∫⁻ w in Wbox, ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) *
        F0rη M η c w.1.1 w.1.2 w.2.1 * F1rη M η c w.2.1 w.2.2 w.1.1 ≤
      ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) * (BrowM M * BrowM M) := by
  have hm : Measurable fun w : (T3 × T3) × (T3 × T3) =>
      F0rη M η c w.1.1 w.1.2 w.2.1 * F1rη M η c w.2.1 w.2.2 w.1.1 :=
    (meas3 (f := fun w : (T3 × T3) × (T3 × T3) => w.1.1) (g := fun w => w.1.2)
      (h := fun w => w.2.1) (measurable_fst.comp measurable_fst)
      (measurable_snd.comp measurable_fst) (measurable_fst.comp measurable_snd)
      (measurable_F0rη M η c)).mul
    (meas3 (f := fun w : (T3 × T3) × (T3 × T3) => w.2.1) (g := fun w => w.2.2)
      (h := fun w => w.1.1) (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd) (measurable_fst.comp measurable_fst)
      (measurable_F1rη M η c))
  have e : ∫⁻ w in Wbox, ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) *
        F0rη M η c w.1.1 w.1.2 w.2.1 * F1rη M η c w.2.1 w.2.2 w.1.1 =
      ∫⁻ w in Wbox, ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) *
        (F0rη M η c w.1.1 w.1.2 w.2.1 * F1rη M η c w.2.1 w.2.2 w.1.1) :=
    lintegral_congr fun w => mul_assoc _ _ _
  rw [e, lintegral_const_mul _ hm]
  exact mul_le_mul' le_rfl (J_bound_eta hM η hc)

/-- The full box integral of the (M5) form for `A_η`, with the same bound as for `A₀`. -/
theorem UM_bound_eta {M : ℝ} (hM : Real.exp 1 ≤ M) (η : ℝ) :
    ∫⁻ y in UM, ENNReal.ofReal (Real.exp (-(M * TMxη η y.1.1.1 y.1.1.2 y.1.2.1 y.1.2.2 y.2.1.1
      y.2.1.2 y.2.2.1 y.2.2.2))) ≤
      ENNReal.ofReal (Real.pi / M) * 4⁻¹ * (ENNReal.ofReal (Real.pi / M) * (BrowM M * BrowM M)) := by
  have hM0 : 0 < M := lt_of_lt_of_le (Real.exp_pos 1) hM
  have hfm : Measurable fun y : Raw16 => ENNReal.ofReal (Real.exp (-(M * TMxη η y.1.1.1 y.1.1.2
      y.1.2.1 y.1.2.2 y.2.1.1 y.2.1.2 y.2.2.1 y.2.2.2))) := by
    unfold TMxη Zr P1t P2t cub3; fun_prop
  have hU : UM = ((Iα ×ˢ Jν) ×ˢ (Iα ×ˢ Jν)) ×ˢ Wbox := rfl
  rw [hU, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm _ hfm.aemeasurable]
  refine (setLIntegral_mono' measurableSet_Wbox fun w hw =>
    UM_inner_eta hM0 η w.1.1 w.1.2 w.2.1 w.2.2 hw.1.1 hw.2.1).trans ?_
  have hsw : Measurable (Function.uncurry fun (a : (T3 × T3) × (T3 × T3)) (c : ℝ × ℝ) =>
      ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) * F0rη M η c a.1.1 a.1.2 a.2.1 *
        F1rη M η c a.2.1 a.2.2 a.1.1) := by
    unfold Function.uncurry F0rη F1rη rowActη yRow γRow κr cub3
    simp only [pcub0, pcub1, pcub2, id]
    fun_prop
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)),
    lintegral_lintegral_swap hsw.aemeasurable]
  gcongr
  refine (setLIntegral_mono' (measurableSet_Icc.prod measurableSet_Icc) fun c hc =>
    UM_c_eta hM η hc).trans ?_
  rw [lintegral_mul_const _ (by fun_prop)]
  exact mul_le_mul' ((setLIntegral_le_lintegral _ _).trans (le_of_eq (lintegral_gauss2 hM0))) le_rfl

theorem SMxη_nonneg (η α0 ν0 α1 ν1 : ℝ) (a0 b0 a1 b1 : T3) :
    0 ≤ SMxη η α0 ν0 α1 ν1 a0 b0 a1 b1 := by
  unfold SMxη; positivity

/-- **Theorem M for `A_η`, uniform in `η`.** For an input law with finite 162nd moments and a
density bounded below on some box, and `π₁ ≥ 0`, there are `C` and `N₀` (depending only on `μ`
and `π₁`) such that for **every** `|η| ≤ 9/1000` and every prior × cutoff at position one bounded
by `π₁` and supported (in (M2) coordinates) in the fixed box `UM`,
`Z_{N,1}(A_η) ≤ C N⁻⁴ (log N)⁴` for all `N ≥ N₀`. -/
theorem theoremM_eta (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ) {π₁ : ℝ} (hπ₁ : 0 ≤ π₁) :
    ∃ C N₀ : ℝ, ∀ η : ℝ, |η| ≤ 9 / 1000 → ∀ φ χ : Raw16 → ENNReal,
      (∀ θ, φ θ * χ (θ - basePos (Aeta η) 0) ≤
        (toM2 ⁻¹' UM).indicator (fun _ => ENNReal.ofReal π₁) θ) →
      ∀ N : ℝ, N₀ ≤ N →
        Zpos μ (Aeta η) φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4 * Real.log N ^ 4) := by
  obtain ⟨κ, hκ, hG⟩ := Gdown_eta μ hmom hlh hμ₀ hμ
  obtain ⟨κ', hκ'⟩ : ∃ κ', κ' = min κ 1 / 3 := ⟨_, rfl⟩
  have hκ'0 : 0 < κ' := by rw [hκ']; exact div_pos (lt_min hκ one_pos) (by norm_num)
  have hκ'1 : κ' ≤ 1 := by rw [hκ']; linarith [min_le_right κ 1]
  obtain ⟨Kc, hKc⟩ : ∃ Kc, Kc = Real.pi ^ 2 * 9 * CM5 (1 / 20) (CM4 (1 / 20)) ^ 2 / 4 :=
    ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  refine ⟨π₁ * Kc * κ'⁻¹ ^ 4, Real.exp 1 / κ', fun η hη φ χ hπ N hN => ?_⟩
  have hM : Real.exp 1 ≤ κ' * N := by
    rw [div_le_iff₀ hκ'0] at hN; linarith
  have hN0 : 0 < N := by
    have := Real.exp_pos 1
    have : 0 < κ' * N := by linarith
    exact pos_of_mul_pos_right this hκ'0.le
  have hset : MeasurableSet (toM2 ⁻¹' UM) := measurableSet_UM.preimage measurable_toM2
  set g : Raw16 → ENNReal := fun y => ENNReal.ofReal (Real.exp (-((κ' * N) * TMxη η y.1.1.1
    y.1.1.2 y.1.2.1 y.1.2.2 y.2.1.1 y.2.1.2 y.2.2.1 y.2.2.2))) with hg
  have hgm : Measurable g := by simp only [hg]; unfold TMxη Zr P1t P2t cub3; fun_prop
  have hpt : ∀ θ ∈ toM2 ⁻¹' UM,
      ENNReal.ofReal (Real.exp (-(N * popLossA μ (Aeta η) θ))) ≤ g (toM2 θ) := by
    intro θ hθ
    obtain ⟨⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩, ⟨⟨ha0, hb0⟩, ⟨ha1, hb1⟩⟩⟩ := hθ
    have hT := TMxη_le_SMxη hη h0 h1 h2 h3 ha0 hb0 ha1 hb1
    have hS0 := SMxη_nonneg η (toM2 θ).1.1.1 (toM2 θ).1.1.2 (toM2 θ).1.2.1 (toM2 θ).1.2.2
      (toM2 θ).2.1.1 (toM2 θ).2.1.2 (toM2 θ).2.2.1 (toM2 θ).2.2.2
    have hGθ := hG η θ
    rw [sum_coeffs_eq_eta] at hGθ
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hmin : min κ 1 * SMxη η (toM2 θ).1.1.1 (toM2 θ).1.1.2 (toM2 θ).1.2.1 (toM2 θ).1.2.2
        (toM2 θ).2.1.1 (toM2 θ).2.1.2 (toM2 θ).2.2.1 (toM2 θ).2.2.2 ≤ popLossA μ (Aeta η) θ :=
      le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hS0) hGθ
    have hT0 : 0 ≤ TMxη η (toM2 θ).1.1.1 (toM2 θ).1.1.2 (toM2 θ).1.2.1 (toM2 θ).1.2.2
        (toM2 θ).2.1.1 (toM2 θ).2.1.2 (toM2 θ).2.2.1 (toM2 θ).2.2.2 := by unfold TMxη; positivity
    have hm0 : 0 ≤ min κ 1 := le_min hκ.le zero_le_one
    rw [hκ']
    nlinarith [mul_le_mul_of_nonneg_left hT hm0, mul_le_mul_of_nonneg_left hmin hN0.le]
  calc Zpos μ (Aeta η) φ χ 0 N
      = ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * popLossA μ (Aeta η) θ))) *
          (φ θ * χ (θ - basePos (Aeta η) 0)) := rfl
    _ ≤ ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * popLossA μ (Aeta η) θ))) *
          (toM2 ⁻¹' UM).indicator (fun _ => ENNReal.ofReal π₁) θ :=
        lintegral_mono fun θ => mul_le_mul' le_rfl (hπ θ)
    _ = ∫⁻ θ in toM2 ⁻¹' UM, ENNReal.ofReal (Real.exp (-(N * popLossA μ (Aeta η) θ))) *
          ENNReal.ofReal π₁ := by
        rw [← lintegral_indicator hset]
        refine lintegral_congr fun θ => ?_
        exact (indicator_mul_right (toM2 ⁻¹' UM)
          (fun θ => ENNReal.ofReal (Real.exp (-(N * popLossA μ (Aeta η) θ))))
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
        exact UM_bound_eta hM η
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

end VectorSLT
