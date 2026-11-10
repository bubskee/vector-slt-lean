/-
Loss comparison, part 1: exact low-degree error coefficients for every parameter, and (G↓) for
any finite family of them.

The polynomial model `errθ θ k` (`Gdown.lean`) is the error of output `k` in the coordinates
`(s, t) = (x₀ - x₁, x₁)` for **every** `θ`; it reads block `0` as `(α, ν)` and blocks `1, 2, 3`
as `(a i, b i)`, but nothing in it is specific to position one. `LemmaM1.lean` computes its
`s³, s²t, st², s⁵` coefficients. This file adds `t³` and `s⁴t`, and the family version of (G↓):
the population loss dominates the sum of squares of any finite family of error coefficients.
-/
import VectorSLT.Gdown
import VectorSLT.LeadingMap

namespace VectorSLT.LossCompare

open MeasureTheory Set Filter MvPolynomial Finset VectorSLT

/-! ### Two more coefficients of the polynomial model -/

/-- Additivity of a coefficient (the non-deprecated form of `MvPolynomial.coeff_add`). -/
theorem cAdd (m : Fin 2 →₀ ℕ) (p q : Pst) : (p + q).coeff m = p.coeff m + q.coeff m := by simp

theorem lin_cube_coeff03 (a b : ℝ) : (lin a b ^ 3).coeff (stMono 0 3) = b ^ 3 := by
  rw [lin_cube, coeff_sum4]; simp only [coeff_mono_monomial]; norm_num

theorem X0_cube_coeff03 : (X 0 ^ 3 : Pst).coeff (stMono 0 3) = 0 := by
  rw [X0_cube_eq, coeff_mono_monomial]; norm_num

/-- `[err]_{t³} = ν³ + P₃`: the `t³` coefficient of the error, every block contributing `b³`. -/
theorem errP_c0 (α ν : Fin 2 → ℝ) (a b : Fin 2 → ℕ → ℝ) (k : Fin 2) :
    (errP α ν a b k).coeff (stMono 0 3) = ν k ^ 3 + b k 0 ^ 3 + b k 1 ^ 3 + b k 2 ^ 3 := by
  rw [errP_coeff_low α ν a b k _ (by simp [stMono]), lin_cube_coeff03, lin_cube_coeff03,
    lin_cube_coeff03, lin_cube_coeff03, X0_cube_coeff03]; ring

theorem mono41_sub20 : stMono 4 1 - Finsupp.single 0 2 = stMono 2 1 := by
  ext i; fin_cases i <;> simp [stMono]

theorem mono41_sub01 : stMono 4 1 - Finsupp.single 1 1 = stMono 4 0 := by
  ext i; fin_cases i <;> simp [stMono]

theorem mono40_sub10 : stMono 4 0 - Finsupp.single 0 1 = stMono 3 0 := by
  ext i; fin_cases i <;> simp [stMono]

/-- `[ (a s + b t)² Q ]_{s⁴t} = a² [Q]_{s²t} + 2ab [Q]_{s³}`. -/
theorem lin_sq_mul_coeff41 (a b : ℝ) (Q : Pst) :
    (lin a b ^ 2 * Q).coeff (stMono 4 1) =
      a ^ 2 * Q.coeff (stMono 2 1) + 2 * a * b * Q.coeff (stMono 3 0) := by
  have e : lin a b ^ 2 * Q = C (a ^ 2) * (X 0 ^ 2 * Q) + C (2 * a * b) * (X 1 * (X 0 * Q)) +
      C (b ^ 2) * (X 1 ^ 2 * Q) := by
    simp only [lin, map_mul, map_pow, map_ofNat]; ring
  rw [e, cAdd, cAdd, coeff_C_mul, coeff_C_mul, coeff_C_mul,
    X_pow_eq_monomial, X_pow_eq_monomial, coeff_monomial_mul', coeff_monomial_mul', coeff_X_mul',
    coeff_X_mul']
  have hle : Finsupp.single (0 : Fin 2) 2 ≤ stMono 4 1 := by
    intro i; fin_cases i <;> simp [stMono]
  have hnle : ¬ Finsupp.single (1 : Fin 2) 2 ≤ stMono 4 1 := by
    intro h; have := h 1; simp [stMono] at this
  have h1 : (1 : Fin 2) ∈ (stMono 4 1).support := by simp [stMono]
  have h0 : (0 : Fin 2) ∈ (stMono 4 0).support := by simp [stMono]
  rw [ite_eq_left hle, mono41_sub20, ite_eq_right hnle, ite_eq_left h1, mono41_sub01, ite_eq_left h0, mono40_sub10]
  ring

theorem lin_cube_coeff41 (a b : ℝ) : (lin a b ^ 3).coeff (stMono 4 1) = 0 :=
  coeff_eq_zero_of_deg (totalDegree_lin_cube a b) (by simp [stMono])

/-- The `s⁴t` coefficient of a row cube: if `S = s + C_S + R_S`, `T = t + C_T + R_T` with `C` of
degree `≥ 3` and `R` of degree `≥ 5`, then `[(aS + bT)³]_{s⁴t} =
3a² (a [C_S]_{s²t} + b [C_T]_{s²t}) + 6ab (a [C_S]_{s³} + b [C_T]_{s³})`. -/
theorem row_cube41 {S T CS CT RS RT : Pst} (a b : ℝ) (hS : S = X 0 + CS + RS)
    (hT : T = X 1 + CT + RT) (hCS : HD 3 CS) (hCT : HD 3 CT) (hRS : HD 5 RS) (hRT : HD 5 RT) :
    ((C a * S + C b * T) ^ 3).coeff (stMono 4 1) =
      3 * a ^ 2 * (a * CS.coeff (stMono 2 1) + b * CT.coeff (stMono 2 1)) +
        6 * a * b * (a * CS.coeff (stMono 3 0) + b * CT.coeff (stMono 3 0)) := by
  set Cl := C a * CS + C b * CT
  set Rl := C a * RS + C b * RT
  have hlam : C a * S + C b * T = lin a b + Cl + Rl := by
    rw [hS, hT]; simp only [lin, Cl, Rl]; ring
  have hCl : HD 3 Cl := (hCS.C_mul a).add (hCT.C_mul b)
  have hRl : HD 5 Rl := (hRS.C_mul a).add (hRT.C_mul b)
  have hE := cube_decomp (hd_lin a b) hCl hRl
  have hdiff : (C a * S + C b * T) ^ 3 =
      ((lin a b + Cl + Rl) ^ 3 - lin a b ^ 3 - 3 * lin a b ^ 2 * Cl) + lin a b ^ 3 +
        3 * lin a b ^ 2 * Cl := by
    rw [hlam]; ring
  rw [hdiff, cAdd, cAdd, hE _ (by simp [stMono]),
    lin_cube_coeff41, show (3 : Pst) = C 3 from (map_ofNat C 3).symm, mul_assoc, coeff_C_mul,
    lin_sq_mul_coeff41]
  simp only [Cl, cAdd, coeff_C_mul]
  ring

section Recursion

variable (α ν : Fin 2 → ℝ) (a b : Fin 2 → ℕ → ℝ)

theorem cubS_coeff21 (i : ℕ) : (cubS α ν a b i).coeff (stMono 2 1) =
    3 * α 0 ^ 2 * ν 0 - 3 * α 1 ^ 2 * ν 1 +
      ∑ j ∈ range i, (3 * a 0 j ^ 2 * b 0 j - 3 * a 1 j ^ 2 * b 1 j) := by
  simp only [cubS, cAdd, coeff_sub, coeff_sum, lin_cube_coeff21]

theorem cubT_coeff21 (i : ℕ) : (cubT α ν a b i).coeff (stMono 2 1) =
    3 * α 1 ^ 2 * ν 1 + ∑ j ∈ range i, 3 * a 1 j ^ 2 * b 1 j := by
  simp only [cubT, cAdd, coeff_sum, lin_cube_coeff21]

theorem rowPoly_cube41 (i : ℕ) (k : Fin 2) :
    (rowPoly α ν a b i k ^ 3).coeff (stMono 4 1) =
      3 * a k i ^ 2 * (a k i * (cubS α ν a b i).coeff (stMono 2 1) +
          b k i * (cubT α ν a b i).coeff (stMono 2 1)) +
        6 * a k i * b k i * (a k i * (cubS α ν a b i).coeff (stMono 3 0) +
          b k i * (cubT α ν a b i).coeff (stMono 3 0)) := by
  obtain ⟨RS, RT, hRS, hRT, hS, hT⟩ := stP_decomp α ν a b i
  exact row_cube41 (a k i) (b k i) hS hT (hd_cubS α ν a b i) (hd_cubT α ν a b i) hRS hRT

/-- The quintic weights of block `i + 1` in the `s⁴t` coefficient:
`η'ᵢ = [cubS i]_{s²t}`, `y'ᵢ = [cubT i]_{s²t}`. -/
def etaM' (i : ℕ) : ℝ := 3 * α 0 ^ 2 * ν 0 - 3 * α 1 ^ 2 * ν 1 +
  ∑ j ∈ range i, (3 * a 0 j ^ 2 * b 0 j - 3 * a 1 j ^ 2 * b 1 j)
def yM' (i : ℕ) : ℝ := 3 * α 1 ^ 2 * ν 1 + ∑ j ∈ range i, 3 * a 1 j ^ 2 * b 1 j

/-- **The `s⁴t` coefficient**: `[err]_{s⁴t} = ∑ᵢ (3aᵢ²(aᵢη'ᵢ + bᵢy'ᵢ) + 6aᵢbᵢ(aᵢηᵢ + bᵢyᵢ))`. -/
theorem errP_s41 (k : Fin 2) : (errP α ν a b k).coeff (stMono 4 1) =
    ∑ i ∈ range 3, (3 * a k i ^ 2 * (a k i * etaM' α ν a b i + b k i * yM' α ν a b i) +
      6 * a k i * b k i * (a k i * etaM α a i + b k i * yM α a i)) := by
  unfold errP
  simp only [coeff_sub, cAdd]
  rw [lin_cube_coeff41,
    coeff_eq_zero_of_deg (p := (X 0 ^ 3 : Pst)) (n := 3) ((totalDegree_pow _ _).trans
      (by rw [totalDegree_X])) (by simp [stMono]),
    rowPoly_cube41, rowPoly_cube41, rowPoly_cube41, cubS_coeff21, cubS_coeff21, cubS_coeff21,
    cubT_coeff21, cubT_coeff21, cubT_coeff21, cubS_coeff, cubS_coeff, cubS_coeff, cubT_coeff,
    cubT_coeff, cubT_coeff]
  simp only [etaM', yM', etaM, yM, sum_range_succ, sum_range_zero]; ring

end Recursion


/-! ### The coefficients in terms of the four raw blocks -/

section Blocks

open VectorSLT.LeadingMap

variable (W : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ)

/-- Row `k` of block `l` as the form `a s + b t`: the amplitude `a = W l k 0`. -/
def rA (l : Fin 4) (k : Fin 2) : ℝ := (rowForm (W l) k).1
/-- Row `k` of block `l` as the form `a s + b t`: the coefficient `b = W l k 0 + W l k 1`. -/
def rB (l : Fin 4) (k : Fin 2) : ℝ := (rowForm (W l) k).2

/-- The `s³` coefficient of the cubic state increment before block `l`, row `0` minus row `1`. -/
def etaW (l : Fin 4) : ℝ := ∑ j ∈ univ.filter (· < l), (rA W j 0 ^ 3 - rA W j 1 ^ 3)
/-- The `s³` coefficient of the cubic state increment before block `l`, row `1`. -/
def yW (l : Fin 4) : ℝ := ∑ j ∈ univ.filter (· < l), rA W j 1 ^ 3
/-- The `s²t` coefficient of the cubic state increment before block `l`, row `0` minus row `1`. -/
def etaW' (l : Fin 4) : ℝ :=
  ∑ j ∈ univ.filter (· < l), (3 * rA W j 0 ^ 2 * rB W j 0 - 3 * rA W j 1 ^ 2 * rB W j 1)
/-- The `s²t` coefficient of the cubic state increment before block `l`, row `1`. -/
def yW' (l : Fin 4) : ℝ := ∑ j ∈ univ.filter (· < l), 3 * rA W j 1 ^ 2 * rB W j 1

/-- `[err_k]_{s³} = ∑_l a_l³ - 1`. -/
def e30 (k : Fin 2) : ℝ := ∑ l, rA W l k ^ 3 - 1
/-- `[err_k]_{s²t} = ∑_l 3 a_l² b_l`. -/
def e21 (k : Fin 2) : ℝ := ∑ l, 3 * rA W l k ^ 2 * rB W l k
/-- `[err_k]_{st²} = ∑_l 3 a_l b_l²`. -/
def e12 (k : Fin 2) : ℝ := ∑ l, 3 * rA W l k * rB W l k ^ 2
/-- `[err_k]_{t³} = ∑_l b_l³`. -/
def e03 (k : Fin 2) : ℝ := ∑ l, rB W l k ^ 3
/-- `[err_k]_{s⁵} = ∑_l 3 a_l² (a_l η_l + b_l y_l)`. -/
def e50 (k : Fin 2) : ℝ := ∑ l, 3 * rA W l k ^ 2 * (rA W l k * etaW W l + rB W l k * yW W l)
/-- `[err_k]_{s⁴t} = ∑_l (3 a_l² (a_l η'_l + b_l y'_l) + 6 a_l b_l (a_l η_l + b_l y_l))`. -/
def e41 (k : Fin 2) : ℝ :=
  ∑ l, (3 * rA W l k ^ 2 * (rA W l k * etaW' W l + rB W l k * yW' W l) +
    6 * rA W l k * rB W l k * (rA W l k * etaW W l + rB W l k * yW W l))

end Blocks

theorem toM2_rows (θ : Raw16) (k : Fin 2) :
    actα (toM2 θ) k = rA (rawW θ) 0 k ∧ actν (toM2 θ) k = rB (rawW θ) 0 k ∧
      inA (toM2 θ) k 0 = rA (rawW θ) 1 k ∧ inA (toM2 θ) k 1 = rA (rawW θ) 2 k ∧
      inA (toM2 θ) k 2 = rA (rawW θ) 3 k ∧ inB (toM2 θ) k 0 = rB (rawW θ) 1 k ∧
      inB (toM2 θ) k 1 = rB (rawW θ) 2 k ∧ inB (toM2 θ) k 2 = rB (rawW θ) 3 k := by
  fin_cases k <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The six coefficients, read off the raw blocks** (every `θ`, every row). -/
theorem errθ_coeffs (θ : Raw16) (k : Fin 2) :
    (errθ θ k).coeff (stMono 3 0) = e30 (rawW θ) k ∧
    (errθ θ k).coeff (stMono 2 1) = e21 (rawW θ) k ∧
    (errθ θ k).coeff (stMono 1 2) = e12 (rawW θ) k ∧
    (errθ θ k).coeff (stMono 0 3) = e03 (rawW θ) k ∧
    (errθ θ k).coeff (stMono 5 0) = e50 (rawW θ) k ∧
    (errθ θ k).coeff (stMono 4 1) = e41 (rawW θ) k := by
  have hα : ∀ k', actα (toM2 θ) k' = rA (rawW θ) 0 k' := fun k' => (toM2_rows θ k').1
  have hν : ∀ k', actν (toM2 θ) k' = rB (rawW θ) 0 k' := fun k' => (toM2_rows θ k').2.1
  have ha0 : ∀ k', inA (toM2 θ) k' 0 = rA (rawW θ) 1 k' := fun k' => (toM2_rows θ k').2.2.1
  have ha1 : ∀ k', inA (toM2 θ) k' 1 = rA (rawW θ) 2 k' := fun k' => (toM2_rows θ k').2.2.2.1
  have ha2 : ∀ k', inA (toM2 θ) k' 2 = rA (rawW θ) 3 k' := fun k' => (toM2_rows θ k').2.2.2.2.1
  have hb0 : ∀ k', inB (toM2 θ) k' 0 = rB (rawW θ) 1 k' :=
    fun k' => (toM2_rows θ k').2.2.2.2.2.1
  have hb1 : ∀ k', inB (toM2 θ) k' 1 = rB (rawW θ) 2 k' :=
    fun k' => (toM2_rows θ k').2.2.2.2.2.2.1
  have hb2 : ∀ k', inB (toM2 θ) k' 2 = rB (rawW θ) 3 k' :=
    fun k' => (toM2_rows θ k').2.2.2.2.2.2.2
  unfold errθ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [errP_c3]
    simp only [momA, e30, Fin.sum_univ_four, hα, ha0, ha1, ha2]
    ring
  · rw [errP_c2]
    simp only [momP1, e21, Fin.sum_univ_four, hα, hν, ha0, ha1, ha2, hb0, hb1, hb2]
    ring
  · rw [errP_c1]
    simp only [momP2, e12, Fin.sum_univ_four, hα, hν, ha0, ha1, ha2, hb0, hb1, hb2]
    ring
  · rw [errP_c0]
    simp only [e03, Fin.sum_univ_four, hν, hb0, hb1, hb2]
  · rw [errP_s5]
    simp only [Zmom, etaM, yM, e50, etaW, yW, Fin.sum_univ_four, sum_range_succ, sum_range_zero,
      Finset.sum_filter, hα, ha0, ha1, ha2, hb0, hb1, hb2]
    simp only [Fin.isValue, Fin.reduceLT, ite_true, ite_false, Fin.lt_irrefl]
    ring
  · rw [errP_s41]
    simp only [etaM', yM', etaM, yM, e41, etaW, yW, etaW', yW', Fin.sum_univ_four, sum_range_succ,
      sum_range_zero, Finset.sum_filter, hα, hν, ha0, ha1, ha2, hb0, hb1, hb2]
    simp only [Fin.isValue, Fin.reduceLT, ite_true, ite_false, Fin.lt_irrefl]
    ring

/-! ### (G↓) for a finite family of coefficients -/

/-- **(G↓), family version.** For any finite family `(kⱼ, mⱼ)` of an output row and an `(s,t)`
monomial, and an input law with the hypotheses of `Gdown`, the population loss for `A₀`
dominates `κ ∑ⱼ ([err_{kⱼ}]_{mⱼ})²`, with `κ > 0` independent of `θ`. -/
theorem gdown_family (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ)
    {n : ℕ} (fam : Fin n → Fin 2 × (Fin 2 →₀ ℕ)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ θ : Raw16,
      κ * ∑ j, ((errθ θ (fam j).1).coeff (fam j).2) ^ 2 ≤ popLossA μ A0 θ := by
  choose C hC0 hC using fun j => linear_le_L2 hlh ((coeffST (fam j).2 : PolyBox 81 →ₗ[ℝ] ℝ))
  obtain ⟨Cm, -, hL2⟩ := l2_le_sup 81 μ hmom
  set Cs := ∑ j, C j + 1
  have hCs : 0 < Cs := by
    have : 0 ≤ ∑ j, C j := Finset.sum_nonneg fun j _ => hC0 j
    positivity
  refine ⟨μ₀ / Cs, by positivity, fun θ => ?_⟩
  set B := cbox lo hi
  set f : Fin 2 → (Fin 2 → ℝ) → ℝ := fun k x => eval x (errX θ k).poly ^ 2
  set S := ∑ k, ∫ x in B, f k x
  have hI : ∀ k, 0 ≤ ∫ x in B, f k x := fun k => integral_nonneg fun x => sq_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => hI k
  have hj : ∀ j, ((errθ θ (fam j).1).coeff (fam j).2) ^ 2 ≤ C j * S := by
    intro j
    have g := hC j (errX θ (fam j).1)
    rw [coeffST_errX] at g
    refine g.trans (mul_le_mul_of_nonneg_left ?_ (hC0 j))
    exact Finset.single_le_sum (f := fun k => ∫ x in B, f k x) (fun k _ => hI k)
      (Finset.mem_univ _)
  have hsum : ∑ j, ((errθ θ (fam j).1).coeff (fam j).2) ^ 2 ≤ Cs * S := by
    calc ∑ j, ((errθ θ (fam j).1).coeff (fam j).2) ^ 2 ≤ ∑ j, C j * S :=
          Finset.sum_le_sum fun j _ => hj j
      _ = (∑ j, C j) * S := by rw [Finset.sum_mul]
      _ ≤ Cs * S := mul_le_mul_of_nonneg_right (by simp [Cs]) hS0
  have hint : ∀ k, Integrable (f k) μ := fun k => (hL2 (errX θ k)).1
  have hintB : ∀ k, Integrable (f k) (volume.restrict B) := fun k =>
    (memLp_eval_cbox lo hi (errX θ k).poly).integrable_sq
  have hpop : popLossA μ A0 θ = ∫ x, ∑ k, f k x ∂μ := by
    unfold popLossA; congr 1; funext x; congr 1; funext k; simp only [f, eval_errX]
  have hlow : μ₀ * ∫ x in B, ∑ k, f k x ≤ ∫ x, ∑ k, f k x ∂μ := by
    have := integral_mono_measure (f := fun x => ∑ k, f k x) hμ
      (Eventually.of_forall fun x => Finset.sum_nonneg fun k _ =>
        sq_nonneg (eval x (errX θ k).poly))
      (integrable_finsetSum _ fun k _ => hint k)
    rwa [integral_smul_measure, ENNReal.toReal_ofReal hμ₀.le, smul_eq_mul] at this
  have hsplit : ∫ x in B, ∑ k, f k x = S := integral_finsetSum _ fun k _ => hintB k
  calc μ₀ / Cs * ∑ j, ((errθ θ (fam j).1).coeff (fam j).2) ^ 2 ≤ μ₀ / Cs * (Cs * S) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = μ₀ * S := by field_simp
    _ ≤ _ := by rw [hpop, ← hsplit]; exact hlow

end VectorSLT.LossCompare
