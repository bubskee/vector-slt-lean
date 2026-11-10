/-
Loss comparison, part 1b: the exact `s³t²` and `s⁷` coefficients of the error for every
parameter (needed at the middle positions, where the coefficients of degree at most five have
rank ten on the eleven generators).

The `s⁷` coefficient needs one more truncation level than `LemmaM1`: the states are
`S = s + C₃ + C₅ + R`, `T = t + C₃' + C₅' + R'` with `C₃` of degree three, `C₅` of degree five
(`quinS`, `quinT`) and `R` of degree at least seven (`stP_decomp7`). For a row form
`λ = L + C + Q + R` the degree-seven part of `λ³` is `3L²Q + 3LC²` (`cube_decomp9`).
-/
import VectorSLT.LossCompare.Coeffs

namespace VectorSLT.LossCompare

open MeasureTheory Set Filter MvPolynomial Finset VectorSLT

/-! ### Coefficient extraction -/

theorem mono32_sub20 : stMono 3 2 - Finsupp.single 0 2 = stMono 1 2 := by
  ext i; fin_cases i <;> simp [stMono]
theorem mono32_sub01 : stMono 3 2 - Finsupp.single 1 1 = stMono 3 1 := by
  ext i; fin_cases i <;> simp [stMono]
theorem mono31_sub10 : stMono 3 1 - Finsupp.single 0 1 = stMono 2 1 := by
  ext i; fin_cases i <;> simp [stMono]
theorem mono32_sub02 : stMono 3 2 - Finsupp.single 1 2 = stMono 3 0 := by
  ext i; fin_cases i <;> simp [stMono]

/-- `[ (a s + b t)² Q ]_{s³t²} = a² [Q]_{st²} + 2ab [Q]_{s²t} + b² [Q]_{s³}`. -/
theorem lin_sq_mul_coeff32 (a b : ℝ) (Q : Pst) :
    (lin a b ^ 2 * Q).coeff (stMono 3 2) = a ^ 2 * Q.coeff (stMono 1 2) +
      2 * a * b * Q.coeff (stMono 2 1) + b ^ 2 * Q.coeff (stMono 3 0) := by
  have e : lin a b ^ 2 * Q = C (a ^ 2) * (X 0 ^ 2 * Q) + C (2 * a * b) * (X 1 * (X 0 * Q)) +
      C (b ^ 2) * (X 1 ^ 2 * Q) := by
    simp only [lin, map_mul, map_pow, map_ofNat]; ring
  rw [e, cAdd, cAdd, coeff_C_mul, coeff_C_mul, coeff_C_mul,
    X_pow_eq_monomial, X_pow_eq_monomial, coeff_monomial_mul', coeff_monomial_mul', coeff_X_mul',
    coeff_X_mul']
  have h1 : Finsupp.single (0 : Fin 2) 2 ≤ stMono 3 2 := by
    intro i; fin_cases i <;> simp [stMono]
  have h2 : Finsupp.single (1 : Fin 2) 2 ≤ stMono 3 2 := by
    intro i; fin_cases i <;> simp [stMono]
  have h3 : (1 : Fin 2) ∈ (stMono 3 2).support := by simp [stMono]
  have h4 : (0 : Fin 2) ∈ (stMono 3 1).support := by simp [stMono]
  rw [ite_eq_left h1, mono32_sub20, ite_eq_left h2, mono32_sub02, ite_eq_left h3, mono32_sub01,
    ite_eq_left h4, mono31_sub10]
  ring

theorem mono70_sub20 : stMono 7 0 - Finsupp.single 0 2 = stMono 5 0 := by
  ext i; fin_cases i <;> simp [stMono]
theorem mono70_sub10 : stMono 7 0 - Finsupp.single 0 1 = stMono 6 0 := by
  ext i; fin_cases i <;> simp [stMono]

/-- `[ (a s + b t)² Q ]_{s⁷} = a² [Q]_{s⁵}`. -/
theorem lin_sq_mul_coeff70 (a b : ℝ) (Q : Pst) :
    (lin a b ^ 2 * Q).coeff (stMono 7 0) = a ^ 2 * Q.coeff (stMono 5 0) := by
  have e : lin a b ^ 2 * Q = C (a ^ 2) * (X 0 ^ 2 * Q) + C (2 * a * b) * (X 1 * (X 0 * Q)) +
      C (b ^ 2) * (X 1 ^ 2 * Q) := by
    simp only [lin, map_mul, map_pow, map_ofNat]; ring
  rw [e, cAdd, cAdd, coeff_C_mul, coeff_C_mul, coeff_C_mul,
    X_pow_eq_monomial, X_pow_eq_monomial, coeff_monomial_mul', coeff_monomial_mul', coeff_X_mul']
  have h1 : Finsupp.single (0 : Fin 2) 2 ≤ stMono 7 0 := by
    intro i; fin_cases i <;> simp [stMono]
  have h2 : ¬ Finsupp.single (1 : Fin 2) 2 ≤ stMono 7 0 := by
    intro h; have := h 1; simp [stMono] at this
  have h3 : (1 : Fin 2) ∉ (stMono 7 0).support := by simp [stMono]
  rw [ite_eq_left h1, mono70_sub20, ite_eq_right h2, ite_eq_right h3]
  ring

/-- `[ (a s + b t) Q ]_{s⁷} = a [Q]_{s⁶}`. -/
theorem lin_mul_coeff70 (a b : ℝ) (Q : Pst) :
    (lin a b * Q).coeff (stMono 7 0) = a * Q.coeff (stMono 6 0) := by
  have e : lin a b * Q = C a * (X 0 * Q) + C b * (X 1 * Q) := by simp only [lin]; ring
  rw [e, cAdd, coeff_C_mul, coeff_C_mul, coeff_X_mul', coeff_X_mul']
  have h0 : (0 : Fin 2) ∈ (stMono 7 0).support := by simp [stMono]
  have h1 : (1 : Fin 2) ∉ (stMono 7 0).support := by simp [stMono]
  rw [ite_eq_left h0, mono70_sub10, ite_eq_right h1]
  ring

/-- Exactly cubic polynomials: `[P P']_{s⁶} = [P]_{s³} [P']_{s³}`. -/
theorem coeff60_mul {P P' : Pst} (hP : HD 3 P) (dP : P.totalDegree ≤ 3) :
    (P * P').coeff (stMono 6 0) = P.coeff (stMono 3 0) * P'.coeff (stMono 3 0) := by
  rw [coeff_mul, Finset.sum_eq_single (stMono 3 0, stMono 3 0)]
  · rintro ⟨m₁, m₂⟩ hm hne
    have hx : m₁ + m₂ = stMono 6 0 := by simpa using hm
    have e0 : m₁ 0 + m₂ 0 = 6 := by
      have := congrArg (· 0) hx; simpa [stMono] using this
    have e1 : m₁ 1 + m₂ 1 = 0 := by
      have := congrArg (· 1) hx; simpa [stMono] using this
    by_cases h1 : m₁ 0 + m₁ 1 < 3
    · rw [hP m₁ h1, zero_mul]
    by_cases h2 : 3 < m₁ 0 + m₁ 1
    · rw [coeff_eq_zero_of_deg dP h2, zero_mul]
    have : m₁ = stMono 3 0 ∧ m₂ = stMono 3 0 := by
      constructor <;> ext i <;> fin_cases i <;> simp [stMono] <;> omega
    exact absurd (Prod.ext this.1 this.2) hne
  · intro h
    exact absurd (HasAntidiagonal.mem_antidiagonal.mpr (by ext i; fin_cases i <;> simp [stMono])) h

/-! ### The degree-seven truncation -/

/-- **Cube decomposition to degree seven**: `(L + C + Q + R)³ - L³ - 3L²C - 3L²Q - 3LC² ∈ HD 9`. -/
theorem cube_decomp9 {L Cc Q R : Pst} (hL : HD 1 L) (hC : HD 3 Cc) (hQ : HD 5 Q) (hR : HD 7 R) :
    HD 9 ((L + Cc + Q + R) ^ 3 - L ^ 3 - 3 * L ^ 2 * Cc - 3 * L ^ 2 * Q - 3 * L * Cc ^ 2) := by
  set U := Q + R
  have hU : HD 5 U := hQ.add (hR.mono (by norm_num))
  have e : (L + Cc + Q + R) ^ 3 - L ^ 3 - 3 * L ^ 2 * Cc - 3 * L ^ 2 * Q - 3 * L * Cc ^ 2 =
      C 3 * (L * (L * R)) + C 6 * (L * (Cc * U)) + C 3 * (L * (U * U)) + Cc * (Cc * Cc) +
        C 3 * (Cc * (Cc * U)) + C 3 * (Cc * (U * U)) + U * (U * U) := by
    simp only [U, map_ofNat]; ring
  rw [e]
  refine ((((((((hL.mul (hL.mul hR)).C_mul 3)).add
    (((hL.mul (hC.mul hU)).C_mul 6))).add
    ((((hL.mul (hU.mul hU)).C_mul 3)).mono (by norm_num))).add
    (hC.mul (hC.mul hC))).add
    ((((hC.mul (hC.mul hU)).C_mul 3)).mono (by norm_num))).add
    ((((hC.mul (hU.mul hU)).C_mul 3)).mono (by norm_num))).add
    ((hU.mul (hU.mul hU)).mono (by norm_num))

theorem totalDegree_cubS_le (α ν : Fin 2 → ℝ) (a b : Fin 2 → ℕ → ℝ) (i : ℕ) :
    (cubS α ν a b i).totalDegree ≤ 3 := by
  unfold VectorSLT.cubS
  refine (totalDegree_add _ _).trans (max_le ((totalDegree_sub _ _).trans
    (max_le (totalDegree_lin_cube _ _) (totalDegree_lin_cube _ _))) ?_)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  exact (totalDegree_sub _ _).trans (max_le (totalDegree_lin_cube _ _) (totalDegree_lin_cube _ _))

theorem totalDegree_cubT_le (α ν : Fin 2 → ℝ) (a b : Fin 2 → ℕ → ℝ) (i : ℕ) :
    (cubT α ν a b i).totalDegree ≤ 3 := by
  unfold VectorSLT.cubT
  refine (totalDegree_add _ _).trans (max_le (totalDegree_lin_cube _ _) ?_)
  exact (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => totalDegree_lin_cube _ _)

section Recursion

variable (α ν : Fin 2 → ℝ) (a b : Fin 2 → ℕ → ℝ)

/-- The cubic part of row form `k` of block `i + 1`. -/
noncomputable def cubRow (i : ℕ) (k : Fin 2) : Pst :=
  C (a k i) * cubS α ν a b i + C (b k i) * cubT α ν a b i

/-- The degree-five increment of row `k` at block `i + 1`: `3 L² C`. -/
noncomputable def quinRow (i : ℕ) (k : Fin 2) : Pst :=
  3 * lin (a k i) (b k i) ^ 2 * cubRow α ν a b i k

/-- The degree-five parts of the states. -/
noncomputable def quinS (i : ℕ) : Pst := ∑ j ∈ range i, (quinRow α ν a b j 0 - quinRow α ν a b j 1)
noncomputable def quinT (i : ℕ) : Pst := ∑ j ∈ range i, quinRow α ν a b j 1

theorem hd_cubRow (i : ℕ) (k : Fin 2) : HD 3 (cubRow α ν a b i k) :=
  ((hd_cubS α ν a b i).C_mul _).add ((hd_cubT α ν a b i).C_mul _)

theorem totalDegree_cubRow (i : ℕ) (k : Fin 2) : (cubRow α ν a b i k).totalDegree ≤ 3 := by
  unfold cubRow
  refine (totalDegree_add _ _).trans (max_le ?_ ?_) <;>
  · refine (totalDegree_mul _ _).trans ?_
    simp only [totalDegree_C, zero_add]
    first | exact totalDegree_cubS_le α ν a b i | exact totalDegree_cubT_le α ν a b i

theorem hd_quinRow (i : ℕ) (k : Fin 2) : HD 5 (quinRow α ν a b i k) := by
  unfold quinRow
  have := ((((hd_lin (a k i) (b k i)).pow 2).mul (hd_cubRow α ν a b i k)).C_mul 3)
  simp only [map_ofNat] at this
  rw [mul_assoc]; simpa using this

theorem hd_quinS (i : ℕ) : HD 5 (quinS α ν a b i) := by
  unfold quinS
  induction i with
  | zero => simpa using HD.zero 5
  | succ i ih =>
    rw [sum_range_succ]; exact ih.add ((hd_quinRow α ν a b i 0).sub (hd_quinRow α ν a b i 1))

theorem hd_quinT (i : ℕ) : HD 5 (quinT α ν a b i) := by
  unfold quinT
  induction i with
  | zero => simpa using HD.zero 5
  | succ i ih => rw [sum_range_succ]; exact ih.add (hd_quinRow α ν a b i 1)

theorem rowPoly_split (i : ℕ) (k : Fin 2) (RS RT : Pst)
    (hS : (stP α ν a b i).1 = X 0 + cubS α ν a b i + quinS α ν a b i + RS)
    (hT : (stP α ν a b i).2 = X 1 + cubT α ν a b i + quinT α ν a b i + RT) :
    rowPoly α ν a b i k = lin (a k i) (b k i) + cubRow α ν a b i k +
      (C (a k i) * quinS α ν a b i + C (b k i) * quinT α ν a b i) +
      (C (a k i) * RS + C (b k i) * RT) := by
  simp only [rowPoly, hS, hT, cubRow, lin]; ring

/-- **The truncation invariant to degree seven.** -/
theorem stP_decomp7 (i : ℕ) : ∃ RS RT : Pst, HD 7 RS ∧ HD 7 RT ∧
    (stP α ν a b i).1 = X 0 + cubS α ν a b i + quinS α ν a b i + RS ∧
    (stP α ν a b i).2 = X 1 + cubT α ν a b i + quinT α ν a b i + RT := by
  induction i with
  | zero =>
    refine ⟨0, 0, HD.zero 7, HD.zero 7, ?_, ?_⟩
    · simp [stP, cubS, quinS]; ring
    · simp [stP, cubT, quinT]
  | succ i ih =>
    obtain ⟨RS, RT, hRS, hRT, hS, hT⟩ := ih
    have hlam := fun k => rowPoly_split α ν a b i k RS RT hS hT
    have hQ : ∀ k, HD 5 (C (a k i) * quinS α ν a b i + C (b k i) * quinT α ν a b i) := fun k =>
      ((hd_quinS α ν a b i).C_mul _).add ((hd_quinT α ν a b i).C_mul _)
    have hR : ∀ k, HD 7 (C (a k i) * RS + C (b k i) * RT) := fun k =>
      (hRS.C_mul _).add (hRT.C_mul _)
    have hE : ∀ k, HD 7 (rowPoly α ν a b i k ^ 3 - lin (a k i) (b k i) ^ 3 -
        quinRow α ν a b i k) := by
      intro k
      have h := cube_decomp (hd_lin (a k i) (b k i)) (hd_cubRow α ν a b i k)
        ((hQ k).add ((hR k).mono (by norm_num)))
      have e : rowPoly α ν a b i k ^ 3 - lin (a k i) (b k i) ^ 3 - quinRow α ν a b i k =
          (lin (a k i) (b k i) + cubRow α ν a b i k +
            ((C (a k i) * quinS α ν a b i + C (b k i) * quinT α ν a b i) +
              (C (a k i) * RS + C (b k i) * RT))) ^ 3 - lin (a k i) (b k i) ^ 3 -
            3 * lin (a k i) (b k i) ^ 2 * cubRow α ν a b i k := by
        rw [hlam k]; simp only [quinRow]; ring
      rw [e]; exact h
    refine ⟨RS + (rowPoly α ν a b i 0 ^ 3 - lin (a 0 i) (b 0 i) ^ 3 - quinRow α ν a b i 0) -
        (rowPoly α ν a b i 1 ^ 3 - lin (a 1 i) (b 1 i) ^ 3 - quinRow α ν a b i 1),
      RT + (rowPoly α ν a b i 1 ^ 3 - lin (a 1 i) (b 1 i) ^ 3 - quinRow α ν a b i 1),
      (hRS.add (hE 0)).sub (hE 1), hRT.add (hE 1), ?_, ?_⟩
    · show (stP α ν a b i).1 + (C (a 0 i) * (stP α ν a b i).1 + C (b 0 i) * (stP α ν a b i).2) ^ 3 -
          (C (a 1 i) * (stP α ν a b i).1 + C (b 1 i) * (stP α ν a b i).2) ^ 3 = _
      have e0 : (C (a 0 i) * (stP α ν a b i).1 + C (b 0 i) * (stP α ν a b i).2) =
          rowPoly α ν a b i 0 := rfl
      have e1 : (C (a 1 i) * (stP α ν a b i).1 + C (b 1 i) * (stP α ν a b i).2) =
          rowPoly α ν a b i 1 := rfl
      rw [e0, e1, hS]
      simp only [cubS, quinS, sum_range_succ]; ring
    · show (stP α ν a b i).2 + (C (a 1 i) * (stP α ν a b i).1 + C (b 1 i) * (stP α ν a b i).2) ^ 3 = _
      have e1 : (C (a 1 i) * (stP α ν a b i).1 + C (b 1 i) * (stP α ν a b i).2) =
          rowPoly α ν a b i 1 := rfl
      rw [e1, hT]
      simp only [cubT, quinT, sum_range_succ]; ring

end Recursion

theorem totalDegree_L2C (a b : ℝ) {P : Pst} (hP : P.totalDegree ≤ 3) :
    (3 * lin a b ^ 2 * P).totalDegree ≤ 5 := by
  rw [show (3 : Pst) = C 3 from (map_ofNat C 3).symm]
  have h1 : (C 3 : Pst).totalDegree = 0 := totalDegree_C 3
  have h2 : (lin a b ^ 2).totalDegree ≤ 2 :=
    (totalDegree_pow _ _).trans (by have := totalDegree_lin a b; omega)
  have h3 := totalDegree_mul (C 3 * lin a b ^ 2) P
  have h4 := totalDegree_mul (C 3 : Pst) (lin a b ^ 2)
  omega

section Coefficients

variable (α ν : Fin 2 → ℝ) (a b : Fin 2 → ℕ → ℝ)

theorem cubS_coeff12 (i : ℕ) : (cubS α ν a b i).coeff (stMono 1 2) =
    3 * α 0 * ν 0 ^ 2 - 3 * α 1 * ν 1 ^ 2 +
      ∑ j ∈ range i, (3 * a 0 j * b 0 j ^ 2 - 3 * a 1 j * b 1 j ^ 2) := by
  simp only [cubS, cAdd, coeff_sub, coeff_sum, lin_cube_coeff12]

theorem cubT_coeff12 (i : ℕ) : (cubT α ν a b i).coeff (stMono 1 2) =
    3 * α 1 * ν 1 ^ 2 + ∑ j ∈ range i, 3 * a 1 j * b 1 j ^ 2 := by
  simp only [cubT, cAdd, coeff_sum, lin_cube_coeff12]

theorem cubRow_coeff (i : ℕ) (k : Fin 2) (m : Fin 2 →₀ ℕ) :
    (cubRow α ν a b i k).coeff m =
      a k i * (cubS α ν a b i).coeff m + b k i * (cubT α ν a b i).coeff m := by
  simp only [cubRow, cAdd, coeff_C_mul]

/-- `[λ³]_{s³t²} = 3 (a² [C]_{st²} + 2ab [C]_{s²t} + b² [C]_{s³})` for the row form `λ` of block
`i + 1`. -/
theorem rowPoly_cube32 (i : ℕ) (k : Fin 2) :
    (rowPoly α ν a b i k ^ 3).coeff (stMono 3 2) =
      3 * (a k i ^ 2 * (cubRow α ν a b i k).coeff (stMono 1 2) +
        2 * a k i * b k i * (cubRow α ν a b i k).coeff (stMono 2 1) +
        b k i ^ 2 * (cubRow α ν a b i k).coeff (stMono 3 0)) := by
  obtain ⟨RS, RT, hRS, hRT, hS, hT⟩ := stP_decomp α ν a b i
  have hR : HD 5 (C (a k i) * RS + C (b k i) * RT) := (hRS.C_mul _).add (hRT.C_mul _)
  have h := cube_decomp (hd_lin (a k i) (b k i)) (hd_cubRow α ν a b i k) hR
  have e : rowPoly α ν a b i k = lin (a k i) (b k i) + cubRow α ν a b i k +
      (C (a k i) * RS + C (b k i) * RT) := by
    simp only [rowPoly, hS, hT, cubRow, lin]; ring
  have hsplit : rowPoly α ν a b i k ^ 3 =
      ((lin (a k i) (b k i) + cubRow α ν a b i k + (C (a k i) * RS + C (b k i) * RT)) ^ 3 -
        lin (a k i) (b k i) ^ 3 - 3 * lin (a k i) (b k i) ^ 2 * cubRow α ν a b i k) +
      lin (a k i) (b k i) ^ 3 + 3 * lin (a k i) (b k i) ^ 2 * cubRow α ν a b i k := by
    rw [e]; ring
  rw [hsplit, cAdd, cAdd, h _ (by simp [stMono]),
    coeff_eq_zero_of_deg (totalDegree_lin_cube _ _) (by simp [stMono]),
    show (3 : Pst) = C 3 from (map_ofNat C 3).symm, mul_assoc, coeff_C_mul, lin_sq_mul_coeff32]
  ring

/-- `[λ³]_{s⁷} = 3a² [Q]_{s⁵} + 3a ([C]_{s³})²` for the row form `λ = L + C + Q + R` of block
`i + 1`. -/
theorem rowPoly_cube70 (i : ℕ) (k : Fin 2) :
    (rowPoly α ν a b i k ^ 3).coeff (stMono 7 0) =
      3 * a k i ^ 2 * (a k i * (quinS α ν a b i).coeff (stMono 5 0) +
        b k i * (quinT α ν a b i).coeff (stMono 5 0)) +
      3 * a k i * (cubRow α ν a b i k).coeff (stMono 3 0) ^ 2 := by
  obtain ⟨RS, RT, hRS, hRT, hS, hT⟩ := stP_decomp7 α ν a b i
  set L := lin (a k i) (b k i)
  set Cc := cubRow α ν a b i k
  set Q := C (a k i) * quinS α ν a b i + C (b k i) * quinT α ν a b i
  set R := C (a k i) * RS + C (b k i) * RT
  have hQ : HD 5 Q := ((hd_quinS α ν a b i).C_mul _).add ((hd_quinT α ν a b i).C_mul _)
  have hR : HD 7 R := (hRS.C_mul _).add (hRT.C_mul _)
  have h := cube_decomp9 (hd_lin (a k i) (b k i)) (hd_cubRow α ν a b i k) hQ hR
  have e : rowPoly α ν a b i k = L + Cc + Q + R := rowPoly_split α ν a b i k RS RT hS hT
  have hsplit : rowPoly α ν a b i k ^ 3 =
      ((L + Cc + Q + R) ^ 3 - L ^ 3 - 3 * L ^ 2 * Cc - 3 * L ^ 2 * Q - 3 * L * Cc ^ 2) +
        L ^ 3 + 3 * L ^ 2 * Cc + 3 * L ^ 2 * Q + 3 * L * (Cc * Cc) := by
    rw [e]; ring
  rw [hsplit, cAdd, cAdd, cAdd, cAdd, h _ (by simp [stMono]),
    coeff_eq_zero_of_deg (totalDegree_lin_cube _ _) (by simp [stMono]),
    coeff_eq_zero_of_deg (totalDegree_L2C _ _ (totalDegree_cubRow α ν a b i k)) (by simp [stMono]),
    show (3 : Pst) = C 3 from (map_ofNat C 3).symm, mul_assoc, mul_assoc, coeff_C_mul, coeff_C_mul,
    lin_sq_mul_coeff70, lin_mul_coeff70,
    coeff60_mul (hd_cubRow α ν a b i k) (totalDegree_cubRow α ν a b i k)]
  simp only [Q, cAdd, coeff_C_mul]
  ring

theorem quinRow_coeff50 (i : ℕ) (k : Fin 2) : (quinRow α ν a b i k).coeff (stMono 5 0) =
    3 * a k i ^ 2 * (cubRow α ν a b i k).coeff (stMono 3 0) := by
  rw [quinRow, show (3 : Pst) = C 3 from (map_ofNat C 3).symm, mul_assoc, coeff_C_mul,
    lin_sq_mul_coeff50]
  ring

theorem errP_s32 (k : Fin 2) : (errP α ν a b k).coeff (stMono 3 2) =
    ∑ i ∈ range 3, (rowPoly α ν a b i k ^ 3).coeff (stMono 3 2) := by
  unfold errP
  simp only [coeff_sub, cAdd, sum_range_succ, sum_range_zero, zero_add]
  rw [coeff_eq_zero_of_deg (totalDegree_lin_cube _ _) (by simp [stMono]),
    coeff_eq_zero_of_deg (p := (X 0 ^ 3 : Pst)) (n := 3) ((totalDegree_pow _ _).trans
      (by rw [totalDegree_X])) (by simp [stMono])]
  ring

theorem errP_s70 (k : Fin 2) : (errP α ν a b k).coeff (stMono 7 0) =
    ∑ i ∈ range 3, (rowPoly α ν a b i k ^ 3).coeff (stMono 7 0) := by
  unfold errP
  simp only [coeff_sub, cAdd, sum_range_succ, sum_range_zero, zero_add]
  rw [coeff_eq_zero_of_deg (totalDegree_lin_cube _ _) (by simp [stMono]),
    coeff_eq_zero_of_deg (p := (X 0 ^ 3 : Pst)) (n := 3) ((totalDegree_pow _ _).trans
      (by rw [totalDegree_X])) (by simp [stMono])]
  ring

end Coefficients

end VectorSLT.LossCompare
