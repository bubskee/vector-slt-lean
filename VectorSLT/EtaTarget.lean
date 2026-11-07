/-
Brief 04, X1: the near-shear target family `A_η` and Lemma X2 (exact coefficients).

Source: cubic-chaos `approx_shear_crossover.md` §§1–2 (pinned at `caccd6a`; the file is
unchanged since `935beb6`).

* `Aeta η = [[1, -1+η], [1, -1+η]]`, so `F_{A_η}(x)_k = x_k + ℓ³` with `ℓ = s + η t`
  (`s = x₀ - x₁`, `t = x₁`). At `η = 0` this is `A₀`.
* The base point `basePos (Aeta η) 0` has (M2) coordinates `(αₖ, νₖ) = (1, η)`.
* **Lemma X2.** The polynomial model of the error for target `A_η` is the `A₀` model plus
  `s³ - ℓ³`, so `c₃` is unchanged, `c₂, c₁, c₀` gain `-3η, -3η², -η³`, and **every
  coefficient of degree ≠ 3** (in particular of degree five, hence `Z_k`) is unchanged.
* **Proposition X1** (normal form, `b = false` branch): a rank-one `A = a vᵀ` with
  `a₀a₁ ≠ 0` and `β₀ = v₀a₀³ > 0` is conjugate by (H2) to `A_η`, `η = (v · a^{⊙3}) / β₀`.
-/
import VectorSLT.Gdown

namespace VectorSLT

open MvPolynomial Finset

/-! ### The target family -/

/-- `A_η = [[1, -1+η], [1, -1+η]]`. -/
def Aeta (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1 + η; 1, -1 + η]

theorem Aeta_zero : Aeta 0 = A0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Aeta, A0]

/-- Fidelity check: `F_{A_η}(x)_k = x_k + (s + η t)³`. -/
theorem layer_Aeta (η : ℝ) (x : Fin 2 → ℝ) (k : Fin 2) :
    layer (Aeta η) x k = x k + ((x 0 - x 1) + η * x 1) ^ 3 := by
  rw [layer_apply]
  fin_cases k <;> simp [Aeta, dotProduct, Fin.sum_univ_two] <;> ring

/-- The base point `basePos (Aeta η) 0` in (M2) coordinates: `α = 1`, `ν = η`, inactive zero. -/
theorem toM2_basePos_Aeta (η : ℝ) :
    toM2 (basePos (Aeta η) 0) = (((1, η), (1, η)), ((0, 0), (0, 0))) := by
  simp [toM2, basePos, ofEnt, Aeta]

theorem act_basePos_Aeta (η : ℝ) (k : Fin 2) :
    actα (toM2 (basePos (Aeta η) 0)) k = 1 ∧ actν (toM2 (basePos (Aeta η) 0)) k = η := by
  rw [toM2_basePos_Aeta]; fin_cases k <;> simp [actα, actν]

/-! ### Lemma X2 -/

section X2

variable (α ν : Fin 2 → ℝ) (a b : Fin 2 → ℕ → ℝ) (η : ℝ)

/-- The error polynomial for target `A_η`: the `A₀` model with `s³` replaced by `ℓ³`. -/
noncomputable def errPη (k : Fin 2) : Pst := errP α ν a b k + X 0 ^ 3 - lin 1 η ^ 3

theorem errPη_sub (k : Fin 2) : errPη α ν a b η k - errP α ν a b k = X 0 ^ 3 - lin 1 η ^ 3 := by
  unfold errPη; ring

theorem totalDegree_X0_cube : (X 0 ^ 3 : Pst).totalDegree ≤ 3 :=
  (totalDegree_pow _ _).trans (by rw [totalDegree_X])

theorem hd_X0_cube : HD 3 (X 0 ^ 3 : Pst) := by
  have := (HD.X (0 : Fin 2)).pow 3; simpa using this

/-- **Lemma X2, the degree-five part**: every coefficient of degree `≠ 3` agrees with `A₀`'s. -/
theorem errPη_coeff_ne3 (k : Fin 2) (m : Fin 2 →₀ ℕ) (hm : m 0 + m 1 ≠ 3) :
    (errPη α ν a b η k).coeff m = (errP α ν a b k).coeff m := by
  have h := congrArg (fun p : Pst => p.coeff m) (errPη_sub α ν a b η k)
  simp only [coeff_sub] at h
  have hz : (X 0 ^ 3 : Pst).coeff m = 0 ∧ (lin 1 η ^ 3).coeff m = 0 := by
    rcases Nat.lt_or_gt_of_ne hm with hlt | hgt
    · exact ⟨hd_X0_cube m hlt, hd_lin_cube 1 η m hlt⟩
    · exact ⟨coeff_eq_zero_of_deg totalDegree_X0_cube hgt,
        coeff_eq_zero_of_deg (totalDegree_lin_cube 1 η) hgt⟩
  rw [hz.1, hz.2] at h
  linarith

/-- **Lemma X2, `Z_k` unchanged**: `[err_η]_{s⁵} = 3 Z_k`. -/
theorem errPη_s5 (k : Fin 2) : (errPη α ν a b η k).coeff (stMono 5 0) = 3 * Zmom α a b k := by
  rw [errPη_coeff_ne3 α ν a b η k _ (by simp [stMono]), errP_s5]

theorem lin_cube_coeff03 (p q : ℝ) : (lin p q ^ 3).coeff (stMono 0 3) = q ^ 3 := by
  rw [lin_cube, coeff_sum4]; simp only [coeff_mono_monomial]; norm_num
theorem X0_cube_coeff03 : (X 0 ^ 3 : Pst).coeff (stMono 0 3) = 0 := by
  rw [X0_cube_eq, coeff_mono_monomial]; norm_num

/-- Lemma M1's missing `c₀` (target `A₀`): `[err]_{t³} = ν³ + P₃`. -/
theorem errP_c0 (k : Fin 2) :
    (errP α ν a b k).coeff (stMono 0 3) = ν k ^ 3 + momP3 (b k) := by
  rw [errP_coeff_low α ν a b k _ (by simp [stMono]), lin_cube_coeff03, lin_cube_coeff03,
    lin_cube_coeff03, lin_cube_coeff03, X0_cube_coeff03, momP3]; ring

theorem errPη_coeff3 (k : Fin 2) (m : Fin 2 →₀ ℕ) :
    (errPη α ν a b η k).coeff m =
      (errP α ν a b k).coeff m + (X 0 ^ 3 : Pst).coeff m - (lin 1 η ^ 3).coeff m := by
  rw [errPη, coeff_sub, AddMonoidAlgebra.coeff_add]; rfl

/-- **Lemma X2, `c₃`**: `α³ - 1 + A` (unchanged). -/
theorem errPη_c3 (k : Fin 2) :
    (errPη α ν a b η k).coeff (stMono 3 0) = α k ^ 3 - 1 + momA (a k) := by
  rw [errPη_coeff3, errP_c3, X0_cube_coeff30, lin_cube_coeff30]; ring

/-- **Lemma X2, `c₂`**: `3(α²ν + P₁ - η)`. -/
theorem errPη_c2 (k : Fin 2) :
    (errPη α ν a b η k).coeff (stMono 2 1) = 3 * (α k ^ 2 * ν k + momP1 (a k) (b k) - η) := by
  rw [errPη_coeff3, errP_c2, X0_cube_coeff21, lin_cube_coeff21]; ring

/-- **Lemma X2, `c₁`**: `3(αν² + P₂ - η²)`. -/
theorem errPη_c1 (k : Fin 2) :
    (errPη α ν a b η k).coeff (stMono 1 2) = 3 * (α k * ν k ^ 2 + momP2 (a k) (b k) - η ^ 2) := by
  rw [errPη_coeff3, errP_c1, X0_cube_coeff12, lin_cube_coeff12]; ring

/-- **Lemma X2, `c₀`**: `ν³ + P₃ - η³`. -/
theorem errPη_c0 (k : Fin 2) :
    (errPη α ν a b η k).coeff (stMono 0 3) = ν k ^ 3 + momP3 (b k) - η ^ 3 := by
  rw [errPη_coeff3, errP_c0, X0_cube_coeff03, lin_cube_coeff03]; ring

end X2

/-- The polynomial model at the (M2) coordinates of `θ`, target `A_η`. -/
noncomputable def errθη (η : ℝ) (θ : Raw16) (k : Fin 2) : Pst :=
  errPη (actα (toM2 θ)) (actν (toM2 θ)) (inA (toM2 θ)) (inB (toM2 θ)) η k

/-- **The polynomial model is the network** for target `A_η`. -/
theorem eval_errθη (η : ℝ) (θ : Raw16) (x : Fin 2 → ℝ) (k : Fin 2) :
    eval (stPt x) (errθη η θ k) = net θ x k - layer (Aeta η) x k := by
  have h := eval_errθ θ x k
  unfold errθη errPη
  rw [map_sub, map_add, ← errθ, h, map_pow, map_pow, eval_lin, layer_Aeta]
  have hA : layer A0 x k = x k + (x 0 - x 1) ^ 3 := by
    rw [← Aeta_zero, layer_Aeta]; ring
  rw [hA]; simp [stPt]; ring

/-! ### Proposition X1 (normal form) -/

/-- **Proposition X1** (`β₀ > 0` branch; the other sign is the coordinate swap). For
`A = a vᵀ` with `a₀, a₁ ≠ 0` and `β₀ = v₀ a₀³ > 0`, the (H2) conjugation with
`D = diag(k/a₀³, k/a₁³)`, `k = β₀^{3/2}`, sends `A` to `A_η` with `η = (v · a^{⊙3}) / β₀`. -/
theorem normalize_Aeta {A : Matrix (Fin 2) (Fin 2) ℝ} {a v : Fin 2 → ℝ}
    (hAav : ∀ i j, A i j = a i * v j) (ha0 : a 0 ≠ 0) (ha1 : a 1 ≠ 0)
    (hβ : 0 < v 0 * a 0 ^ 3) :
    ∃ d : Fin 2 → ℝ, (∀ i, d i ≠ 0) ∧
      actW d false A = Aeta ((v 0 * a 0 ^ 3 + v 1 * a 1 ^ 3) / (v 0 * a 0 ^ 3)) := by
  set β := v 0 * a 0 ^ 3
  set g := √β
  have hg : 0 < g := Real.sqrt_pos.mpr hβ
  have hg2 : g ^ 2 = β := Real.sq_sqrt hβ.le
  set d : Fin 2 → ℝ := fun i => g ^ 3 / a i ^ 3
  have hd : ∀ i, d i ≠ 0 := by
    intro i; fin_cases i <;> simp [d, hg.ne', ha0, ha1]
  have hr : ∀ i, rcbrt (d i) = g / a i := by
    intro i; apply rcbrt_eq_of_cube; simp only [d]; rw [div_pow]
  refine ⟨d, hd, ?_⟩
  have e : ∀ m n : Fin 2, rcbrt (d m) / d n * A m n = v n * a n ^ 3 / β := by
    intro m n
    rw [hr, hAav]
    simp only [d]
    have := (show a m ≠ 0 by fin_cases m <;> assumption)
    have := (show a n ≠ 0 by fin_cases n <;> assumption)
    rw [← hg2]; field_simp
  have hβ0 : β ≠ 0 := hβ.ne'
  ext i j
  simp only [actW, Matrix.of_apply, tau, Bool.false_eq_true, ite_false, e]
  have h0 : v 0 * a 0 ^ 3 / β = 1 := div_self hβ0
  have h1 : v 1 * a 1 ^ 3 / β = -1 + (β + v 1 * a 1 ^ 3) / β := by
    rw [add_div, div_self hβ0]; ring
  fin_cases i <;> fin_cases j <;> simp only [Aeta, Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, h0, h1]

end VectorSLT
