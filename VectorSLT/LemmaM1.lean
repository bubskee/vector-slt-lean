/-
L6 stage 2, part 2: Lemma M1 (the exact low-degree coefficients) from the polynomial model.

Polynomials in `(s, t) = (X 0, X 1)`. `HD n p` says every monomial of `p` has degree `≥ n`.
Along the (M2) recursion each row form is `λ = L + C + R` with `L` linear, `C` of degree
exactly 3 and `R ∈ HD 5`. Hence the degree-3 part of `λ³` is `L³` and the degree-5 part is
`3 L² C`. These two facts give the four cubic coefficients and the `s⁵` coefficient,
without expanding the degree-81 error.
-/
import VectorSLT.FullNetwork

namespace VectorSLT

open MvPolynomial Finset

abbrev Pst := MvPolynomial (Fin 2) ℝ

/-- The exponent of `s^i t^j`. -/
noncomputable def stMono (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

theorem mono_apply0 (i j : ℕ) : stMono i j 0 = i := by simp [stMono]
theorem mono_apply1 (i j : ℕ) : stMono i j 1 = j := by simp [stMono]

theorem mono_eq_iff {i j i' j' : ℕ} : stMono i j = stMono i' j' ↔ i = i' ∧ j = j' := by
  constructor
  · intro h
    exact ⟨by simpa [mono_apply0] using congrArg (· 0) h,
      by simpa [mono_apply1] using congrArg (· 1) h⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem X_pow_mul_X_pow (i j : ℕ) : (X 0 ^ i * X 1 ^ j : Pst) = monomial (stMono i j) 1 := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul, stMono]

theorem coeff_mono_monomial (i j i' j' : ℕ) (c : ℝ) :
    (C c * (X 0 ^ i' * X 1 ^ j') : Pst).coeff (stMono i j) = if i' = i ∧ j' = j then c else 0 := by
  rw [coeff_C_mul, X_pow_mul_X_pow, coeff_monomial]
  by_cases h : i' = i ∧ j' = j
  · rw [if_pos (mono_eq_iff.mpr h), if_pos h, mul_one]
  · rw [if_neg (fun h' => h (mono_eq_iff.mp h')), if_neg h, mul_zero]

/-! ### High degree -/

/-- Every monomial of `p` has total degree `≥ n`. -/
def HD (n : ℕ) (p : Pst) : Prop := ∀ m : Fin 2 →₀ ℕ, m 0 + m 1 < n → p.coeff m = 0

theorem HD.zero (n : ℕ) : HD n 0 := fun m _ => by simp
theorem HD.add {n : ℕ} {p q : Pst} (hp : HD n p) (hq : HD n q) : HD n (p + q) :=
  fun m hm => by rw [MvPolynomial.coeff_add, hp m hm, hq m hm, add_zero]
theorem HD.sub {n : ℕ} {p q : Pst} (hp : HD n p) (hq : HD n q) : HD n (p - q) :=
  fun m hm => by rw [coeff_sub, hp m hm, hq m hm, sub_zero]
theorem HD.C_mul {n : ℕ} {p : Pst} (c : ℝ) (hp : HD n p) : HD n (C c * p) :=
  fun m hm => by rw [coeff_C_mul, hp m hm, mul_zero]
theorem HD.mono {n n' : ℕ} {p : Pst} (hp : HD n p) (h : n' ≤ n) : HD n' p :=
  fun m hm => hp m (lt_of_lt_of_le hm h)

theorem HD.mul {a b : ℕ} {p q : Pst} (hp : HD a p) (hq : HD b q) : HD (a + b) (p * q) := by
  intro m hm
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' : x.1 + x.2 = m := by simpa using hx
  have h0 : x.1 0 + x.2 0 = m 0 := by rw [← hx']; rfl
  have h1 : x.1 1 + x.2 1 = m 1 := by rw [← hx']; rfl
  by_cases ha : x.1 0 + x.1 1 < a
  · rw [hp _ ha, zero_mul]
  · rw [hq _ (by omega), mul_zero]

theorem HD.X (i : Fin 2) : HD 1 (X i : Pst) := by
  intro m hm
  rw [coeff_X, if_neg]
  intro h
  rw [← h] at hm
  fin_cases i <;> simp at hm

theorem HD.pow {a : ℕ} {p : Pst} (hp : HD a p) (n : ℕ) : HD (a * n) (p ^ n) := by
  induction n with
  | zero => intro m hm; simp at hm
  | succ n ih => rw [pow_succ, mul_add, mul_one]; exact ih.mul hp

/-- Bounded total degree kills coefficients of higher-degree monomials. -/
theorem coeff_eq_zero_of_deg {p : Pst} {n : ℕ} (hp : p.totalDegree ≤ n) {m : Fin 2 →₀ ℕ}
    (hm : n < m 0 + m 1) : p.coeff m = 0 := by
  apply coeff_eq_zero_of_totalDegree_lt
  rw [Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi), Fin.sum_univ_two]
  omega

/-! ### Linear forms and their cubes -/

/-- The linear form `a s + b t`. -/
noncomputable def lin (a b : ℝ) : Pst := C a * X 0 + C b * X 1

theorem hd_lin (a b : ℝ) : HD 1 (lin a b) := ((HD.X 0).C_mul a).add ((HD.X 1).C_mul b)

theorem totalDegree_lin (a b : ℝ) : (lin a b).totalDegree ≤ 1 := by
  unfold lin
  refine (totalDegree_add _ _).trans (max_le ?_ ?_) <;>
  · refine (totalDegree_mul _ _).trans ?_; simp [totalDegree_C, totalDegree_X]

theorem lin_cube (a b : ℝ) : lin a b ^ 3 = C (a ^ 3) * (X 0 ^ 3 * X 1 ^ 0) +
    C (3 * a ^ 2 * b) * (X 0 ^ 2 * X 1 ^ 1) + C (3 * a * b ^ 2) * (X 0 ^ 1 * X 1 ^ 2) +
    C (b ^ 3) * (X 0 ^ 0 * X 1 ^ 3) := by
  simp only [lin, map_mul, map_pow, map_ofNat]; ring

theorem coeff_sum4 (m : Fin 2 →₀ ℕ) (p q r u : Pst) :
    (p + q + r + u).coeff m = p.coeff m + q.coeff m + r.coeff m + u.coeff m := by
  simp only [MvPolynomial.coeff_add]

theorem lin_cube_coeff30 (a b : ℝ) : (lin a b ^ 3).coeff (stMono 3 0) = a ^ 3 := by
  rw [lin_cube, coeff_sum4]; simp only [coeff_mono_monomial]; norm_num
theorem lin_cube_coeff21 (a b : ℝ) : (lin a b ^ 3).coeff (stMono 2 1) = 3 * a ^ 2 * b := by
  rw [lin_cube, coeff_sum4]; simp only [coeff_mono_monomial]; norm_num
theorem lin_cube_coeff12 (a b : ℝ) : (lin a b ^ 3).coeff (stMono 1 2) = 3 * a * b ^ 2 := by
  rw [lin_cube, coeff_sum4]; simp only [coeff_mono_monomial]; norm_num

theorem X0_cube_eq : (X 0 ^ 3 : Pst) = C 1 * (X 0 ^ 3 * X 1 ^ 0) := by simp
theorem X0_cube_coeff30 : (X 0 ^ 3 : Pst).coeff (stMono 3 0) = 1 := by
  rw [X0_cube_eq, coeff_mono_monomial]; norm_num
theorem X0_cube_coeff21 : (X 0 ^ 3 : Pst).coeff (stMono 2 1) = 0 := by
  rw [X0_cube_eq, coeff_mono_monomial]; norm_num
theorem X0_cube_coeff12 : (X 0 ^ 3 : Pst).coeff (stMono 1 2) = 0 := by
  rw [X0_cube_eq, coeff_mono_monomial]; norm_num

theorem mono50_sub : stMono 5 0 - Finsupp.single 0 2 = stMono 3 0 := by
  ext i; fin_cases i <;> simp [stMono]

/-- `[ (a s + b t)² Q ]_{s⁵} = a² [Q]_{s³}`. -/
theorem lin_sq_mul_coeff50 (a b : ℝ) (Q : Pst) :
    (lin a b ^ 2 * Q).coeff (stMono 5 0) = a ^ 2 * Q.coeff (stMono 3 0) := by
  have e : lin a b ^ 2 * Q = C (a ^ 2) * (X 0 ^ 2 * Q) + C (2 * a * b) * (X 0 * (X 1 * Q)) +
      C (b ^ 2) * (X 1 ^ 2 * Q) := by
    simp only [lin, map_mul, map_pow, map_ofNat]; ring
  rw [e, MvPolynomial.coeff_add, MvPolynomial.coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul,
    X_pow_eq_monomial, X_pow_eq_monomial, coeff_monomial_mul', coeff_monomial_mul', coeff_X_mul']
  have h0 : (0 : Fin 2) ∈ (stMono 5 0).support := by simp [stMono]
  have hle : Finsupp.single (0 : Fin 2) 2 ≤ stMono 5 0 := by
    intro i; fin_cases i <;> simp [stMono]
  have hnle : ¬ Finsupp.single (1 : Fin 2) 2 ≤ stMono 5 0 := by
    intro h; have := h 1; simp [stMono] at this
  rw [if_pos hle, mono50_sub, if_pos h0, if_neg hnle, coeff_X_mul', if_neg]
  · ring
  · intro h; simp [stMono] at h

/-! ### The cube of `L + C + R` -/

/-- **Cube decomposition**: `(L + C + R)³ = L³ + 3L²C + E` with `E ∈ HD 7`. -/
theorem cube_decomp {L Cc R : Pst} (hL : HD 1 L) (hC : HD 3 Cc) (hR : HD 5 R) :
    HD 7 ((L + Cc + R) ^ 3 - L ^ 3 - 3 * L ^ 2 * Cc) := by
  have e : (L + Cc + R) ^ 3 - L ^ 3 - 3 * L ^ 2 * Cc =
      C 3 * (L * (Cc * Cc)) + Cc * (Cc * Cc) +
      R * (C 3 * ((L + Cc) * (L + Cc)) + C 3 * ((L + Cc) * R) + R * R) := by
    simp only [map_ofNat]; ring
  rw [e]
  have hLC : HD 1 (L + Cc) := hL.add (hC.mono (by norm_num))
  refine ((((hL.mul (hC.mul hC)).C_mul 3).mono (by norm_num)).add
    ((hC.mul (hC.mul hC)).mono (by norm_num))).add ?_
  have h2 : HD 2 (C 3 * ((L + Cc) * (L + Cc)) + C 3 * ((L + Cc) * R) + R * R) :=
    (((hLC.mul hLC).C_mul 3).add (((hLC.mul hR).C_mul 3).mono (by norm_num))).add
      ((hR.mul hR).mono (by norm_num))
  exact hR.mul h2

/-! ### One row form `λ = a S + b T` -/

theorem totalDegree_lin_cube (a b : ℝ) : (lin a b ^ 3).totalDegree ≤ 3 :=
  (totalDegree_pow _ _).trans (by have := totalDegree_lin a b; omega)

theorem hd_lin_cube (a b : ℝ) : HD 3 (lin a b ^ 3) := by
  have := (hd_lin a b).pow 3; simpa using this

/-- If `S = s + C_S + R_S`, `T = t + C_T + R_T` (`C` of degree ≥ 3, `R` of degree ≥ 5), then
`λ = aS + bT` has `λ³ - (as+bt)³ ∈ HD 5`, the same low coefficients as `(as+bt)³` in degrees
`< 5`, and `[λ³]_{s⁵} = 3a²(a[C_S]_{s³} + b[C_T]_{s³})`. -/
theorem row_cube {S T CS CT RS RT : Pst} (a b : ℝ) (hS : S = X 0 + CS + RS)
    (hT : T = X 1 + CT + RT) (hCS : HD 3 CS) (hCT : HD 3 CT) (hRS : HD 5 RS) (hRT : HD 5 RT) :
    HD 5 ((C a * S + C b * T) ^ 3 - lin a b ^ 3) ∧
    (∀ m : Fin 2 →₀ ℕ, m 0 + m 1 < 5 →
      ((C a * S + C b * T) ^ 3).coeff m = (lin a b ^ 3).coeff m) ∧
    ((C a * S + C b * T) ^ 3).coeff (stMono 5 0) =
      3 * a ^ 2 * (a * CS.coeff (stMono 3 0) + b * CT.coeff (stMono 3 0)) := by
  set Cl := C a * CS + C b * CT
  set Rl := C a * RS + C b * RT
  have hlam : C a * S + C b * T = lin a b + Cl + Rl := by
    rw [hS, hT]; simp only [lin, Cl, Rl]; ring
  have hCl : HD 3 Cl := (hCS.C_mul a).add (hCT.C_mul b)
  have hRl : HD 5 Rl := (hRS.C_mul a).add (hRT.C_mul b)
  have hE := cube_decomp (hd_lin a b) hCl hRl
  have hmid : HD 5 (3 * lin a b ^ 2 * Cl) := by
    have := (((hd_lin a b).pow 2).mul hCl).C_mul 3
    simp only [map_ofNat] at this
    rw [mul_assoc]; simpa using this
  have hdiff : (C a * S + C b * T) ^ 3 - lin a b ^ 3 =
      ((lin a b + Cl + Rl) ^ 3 - lin a b ^ 3 - 3 * lin a b ^ 2 * Cl) + 3 * lin a b ^ 2 * Cl := by
    rw [hlam]; ring
  refine ⟨?_, fun m hm => ?_, ?_⟩
  · rw [hdiff]; exact (hE.mono (by norm_num)).add hmid
  · have h := congrArg (fun p : Pst => p.coeff m) hdiff
    rw [MvPolynomial.coeff_add, hE m (by omega), hmid m hm, add_zero, coeff_sub] at h
    linarith
  · have h := congrArg (fun p : Pst => p.coeff (stMono 5 0)) hdiff
    rw [MvPolynomial.coeff_add, hE _ (by simp [stMono]), zero_add, coeff_sub,
      coeff_eq_zero_of_deg (totalDegree_lin_cube a b) (by simp [stMono]), sub_zero] at h
    have h3 : (3 * lin a b ^ 2 * Cl).coeff (stMono 5 0) = 3 * (a ^ 2 * Cl.coeff (stMono 3 0)) := by
      rw [show (3 : Pst) = C 3 from (map_ofNat C 3).symm, mul_assoc, coeff_C_mul, lin_sq_mul_coeff50]
    rw [h3] at h
    have hCl3 : Cl.coeff (stMono 3 0) = a * CS.coeff (stMono 3 0) + b * CT.coeff (stMono 3 0) := by
      simp only [Cl, MvPolynomial.coeff_add, coeff_C_mul]
    rw [hCl3] at h
    linarith

/-! ### The (M2) recursion as polynomials in `(s, t)` -/

section Recursion

variable (α ν : Fin 2 → ℝ) (a b : Fin 2 → ℕ → ℝ)

/-- States `(S_i, T_i)` after the active block (`i = 0`) and after inactive blocks `1..i`. -/
noncomputable def stP : ℕ → Pst × Pst
  | 0 => (X 0 + lin (α 0) (ν 0) ^ 3 - lin (α 1) (ν 1) ^ 3, X 1 + lin (α 1) (ν 1) ^ 3)
  | i + 1 => ((stP i).1 + (C (a 0 i) * (stP i).1 + C (b 0 i) * (stP i).2) ^ 3 -
      (C (a 1 i) * (stP i).1 + C (b 1 i) * (stP i).2) ^ 3,
    (stP i).2 + (C (a 1 i) * (stP i).1 + C (b 1 i) * (stP i).2) ^ 3)

/-- Row `k` of inactive block `i+1`, applied to the state after block `i`. -/
noncomputable def rowPoly (i : ℕ) (k : Fin 2) : Pst :=
  C (a k i) * (stP α ν a b i).1 + C (b k i) * (stP α ν a b i).2

/-- The error of output `k`: `λ₀³ + λ₁³ + λ₂³ + λ₃³ - s³`. -/
noncomputable def errP (k : Fin 2) : Pst :=
  lin (α k) (ν k) ^ 3 + rowPoly α ν a b 0 k ^ 3 + rowPoly α ν a b 1 k ^ 3 + rowPoly α ν a b 2 k ^ 3 -
    X 0 ^ 3

/-- The cubic parts of the states. -/
noncomputable def cubS (i : ℕ) : Pst :=
  lin (α 0) (ν 0) ^ 3 - lin (α 1) (ν 1) ^ 3 +
    ∑ j ∈ range i, (lin (a 0 j) (b 0 j) ^ 3 - lin (a 1 j) (b 1 j) ^ 3)
noncomputable def cubT (i : ℕ) : Pst :=
  lin (α 1) (ν 1) ^ 3 + ∑ j ∈ range i, lin (a 1 j) (b 1 j) ^ 3

theorem hd_cubS (i : ℕ) : HD 3 (cubS α ν a b i) := by
  unfold VectorSLT.cubS
  refine ((hd_lin_cube _ _).sub (hd_lin_cube _ _)).add ?_
  induction i with
  | zero => simpa using HD.zero 3
  | succ i ih => rw [sum_range_succ]; exact ih.add ((hd_lin_cube _ _).sub (hd_lin_cube _ _))

theorem hd_cubT (i : ℕ) : HD 3 (cubT α ν a b i) := by
  unfold VectorSLT.cubT
  refine (hd_lin_cube _ _).add ?_
  induction i with
  | zero => simpa using HD.zero 3
  | succ i ih => rw [sum_range_succ]; exact ih.add (hd_lin_cube _ _)

/-- **The truncation invariant**: `S_i = s + cubS i + (deg ≥ 5)`, `T_i = t + cubT i + (deg ≥ 5)`. -/
theorem stP_decomp (i : ℕ) : ∃ RS RT : Pst, HD 5 RS ∧ HD 5 RT ∧
    (stP α ν a b i).1 = X 0 + cubS α ν a b i + RS ∧
    (stP α ν a b i).2 = X 1 + cubT α ν a b i + RT := by
  induction i with
  | zero =>
    refine ⟨0, 0, HD.zero 5, HD.zero 5, ?_, ?_⟩ <;> simp [stP, cubS, cubT] <;> ring
  | succ i ih =>
    obtain ⟨RS, RT, hRS, hRT, hS, hT⟩ := ih
    obtain ⟨h0, -, -⟩ := row_cube (a 0 i) (b 0 i) hS hT (hd_cubS α ν a b i)
      (hd_cubT α ν a b i) hRS hRT
    obtain ⟨h1, -, -⟩ := row_cube (a 1 i) (b 1 i) hS hT (hd_cubS α ν a b i)
      (hd_cubT α ν a b i) hRS hRT
    refine ⟨RS + ((C (a 0 i) * (stP α ν a b i).1 + C (b 0 i) * (stP α ν a b i).2) ^ 3 -
        lin (a 0 i) (b 0 i) ^ 3) - ((C (a 1 i) * (stP α ν a b i).1 +
        C (b 1 i) * (stP α ν a b i).2) ^ 3 - lin (a 1 i) (b 1 i) ^ 3),
      RT + ((C (a 1 i) * (stP α ν a b i).1 + C (b 1 i) * (stP α ν a b i).2) ^ 3 -
        lin (a 1 i) (b 1 i) ^ 3),
      (hRS.add h0).sub h1, hRT.add h1, ?_, ?_⟩
    · show (stP α ν a b i).1 + _ - _ = _
      rw [hS]; simp only [cubS, sum_range_succ]; ring
    · show (stP α ν a b i).2 + _ = _
      rw [hT]; simp only [cubT, sum_range_succ]; ring

/-- `η_{i+1} = [cubS i]_{s³}`, `y_{i+1} = [cubT i]_{s³}` (paper's (M3)). -/
theorem cubS_coeff (i : ℕ) : (cubS α ν a b i).coeff (stMono 3 0) =
    α 0 ^ 3 - α 1 ^ 3 + ∑ j ∈ range i, (a 0 j ^ 3 - a 1 j ^ 3) := by
  simp only [cubS, MvPolynomial.coeff_add, coeff_sub, coeff_sum, lin_cube_coeff30]

theorem cubT_coeff (i : ℕ) : (cubT α ν a b i).coeff (stMono 3 0) =
    α 1 ^ 3 + ∑ j ∈ range i, a 1 j ^ 3 := by
  simp only [cubT, MvPolynomial.coeff_add, coeff_sum, lin_cube_coeff30]

theorem rowPoly_cube (i : ℕ) (k : Fin 2) :
    (∀ m : Fin 2 →₀ ℕ, m 0 + m 1 < 5 →
      (rowPoly α ν a b i k ^ 3).coeff m = (lin (a k i) (b k i) ^ 3).coeff m) ∧
    (rowPoly α ν a b i k ^ 3).coeff (stMono 5 0) = 3 * a k i ^ 2 *
      (a k i * (cubS α ν a b i).coeff (stMono 3 0) + b k i * (cubT α ν a b i).coeff (stMono 3 0)) := by
  obtain ⟨RS, RT, hRS, hRT, hS, hT⟩ := stP_decomp α ν a b i
  obtain ⟨-, h1, h2⟩ := row_cube (a k i) (b k i) hS hT (hd_cubS α ν a b i)
    (hd_cubT α ν a b i) hRS hRT
  exact ⟨h1, h2⟩

theorem errP_coeff_low (k : Fin 2) (m : Fin 2 →₀ ℕ) (hm : m 0 + m 1 < 5) :
    (errP α ν a b k).coeff m = (lin (α k) (ν k) ^ 3).coeff m +
      (lin (a k 0) (b k 0) ^ 3).coeff m + (lin (a k 1) (b k 1) ^ 3).coeff m +
      (lin (a k 2) (b k 2) ^ 3).coeff m - (X 0 ^ 3 : Pst).coeff m := by
  unfold errP
  simp only [coeff_sub, MvPolynomial.coeff_add]
  rw [(rowPoly_cube α ν a b 0 k).1 m hm, (rowPoly_cube α ν a b 1 k).1 m hm,
    (rowPoly_cube α ν a b 2 k).1 m hm]

/-- **Lemma M1, `c₃`**: `[err]_{s³} = α³ - 1 + A`. -/
theorem errP_c3 (k : Fin 2) :
    (errP α ν a b k).coeff (stMono 3 0) = α k ^ 3 - 1 + momA (a k) := by
  rw [errP_coeff_low α ν a b k _ (by simp [stMono]), lin_cube_coeff30, lin_cube_coeff30,
    lin_cube_coeff30, lin_cube_coeff30, X0_cube_coeff30, momA]; ring

/-- **Lemma M1, `c₂`**: `[err]_{s²t} = 3α²ν + 3P₁`. -/
theorem errP_c2 (k : Fin 2) :
    (errP α ν a b k).coeff (stMono 2 1) = 3 * α k ^ 2 * ν k + 3 * momP1 (a k) (b k) := by
  rw [errP_coeff_low α ν a b k _ (by simp [stMono]), lin_cube_coeff21, lin_cube_coeff21,
    lin_cube_coeff21, lin_cube_coeff21, X0_cube_coeff21, momP1]; ring

/-- **Lemma M1, `c₁`**: `[err]_{st²} = 3αν² + 3P₂`. -/
theorem errP_c1 (k : Fin 2) :
    (errP α ν a b k).coeff (stMono 1 2) = 3 * α k * ν k ^ 2 + 3 * momP2 (a k) (b k) := by
  rw [errP_coeff_low α ν a b k _ (by simp [stMono]), lin_cube_coeff12, lin_cube_coeff12,
    lin_cube_coeff12, lin_cube_coeff12, X0_cube_coeff12, momP2]; ring

/-- The weights `ηᵢ` and `yᵢ` of (M3), for Lean's block index `i ∈ {0,1,2}`. -/
def etaM (i : ℕ) : ℝ := α 0 ^ 3 - α 1 ^ 3 + ∑ j ∈ range i, (a 0 j ^ 3 - a 1 j ^ 3)
def yM (i : ℕ) : ℝ := α 1 ^ 3 + ∑ j ∈ range i, a 1 j ^ 3

/-- The quintic moment `Z_k = ∑ᵢ aᵢ² (aᵢ ηᵢ + bᵢ yᵢ)` of (M3). -/
def Zmom (k : Fin 2) : ℝ :=
  ∑ i ∈ range 3, a k i ^ 2 * (a k i * etaM α a i + b k i * yM α a i)

/-- **Lemma M1, (M3)**: `[err]_{s⁵} = 3 Z_k`. -/
theorem errP_s5 (k : Fin 2) : (errP α ν a b k).coeff (stMono 5 0) = 3 * Zmom α a b k := by
  unfold errP
  simp only [coeff_sub, MvPolynomial.coeff_add]
  rw [coeff_eq_zero_of_deg (totalDegree_lin_cube _ _) (by simp [stMono]),
    coeff_eq_zero_of_deg (p := (X 0 ^ 3 : Pst)) (n := 3) ((totalDegree_pow _ _).trans
      (by rw [totalDegree_X])) (by simp [stMono]),
    (rowPoly_cube α ν a b 0 k).2, (rowPoly_cube α ν a b 1 k).2, (rowPoly_cube α ν a b 2 k).2,
    cubS_coeff, cubS_coeff, cubS_coeff, cubT_coeff, cubT_coeff, cubT_coeff]
  simp only [Zmom, etaM, yM, sum_range_succ, sum_range_zero]; ring

end Recursion

end VectorSLT
