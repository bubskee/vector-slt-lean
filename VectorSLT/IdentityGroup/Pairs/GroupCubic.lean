/-
Paper 2, Lemma `lem:A-box` (Appendix A.1), upper half, algebraic part.

For a group of `n` blocks `B 0, …, B (n-1)` (application order), the group error is the
polynomial map `F_{B_{n-1}} ∘ ⋯ ∘ F_{B_0} - I`, of degree `≤ 3ⁿ` (`grpErr`). The paper's proof:
"the degree-three part of the group error is exactly `∑ᵢ V_{Bᵢ}`, so `J_n ≥ ‖∑ᵢ V_{Bᵢ}‖²`, and each
output row of `∑ᵢ V_{Bᵢ}` is a sum of `n` binary cubes in that row's own entries".

Lean form (`cubeSumSq_le_grpErr`): `G_n(row k) ≤ C ‖grpErr B n k‖²`, where `G_n = cubeSumSq` is
the squared moment norm of `∑ᵢ (Bᵢ k · x)³` (Defs.lean) and `‖·‖` is the sup norm on `[-1,1]²`.
The degree-three part is read off along rays: for fixed `y`, the cubic coefficient of the
univariate polynomial `s ↦ P(s y)` is the linear functional `rayCub y`, and on the group error it
equals `∑ᵢ (Bᵢ k · y)³` (`rayCub_grpErr`). Four rays recover the four moments.
-/
import VectorSLT.IdentityGroup.Defs
import VectorSLT.GeneralInput

namespace VectorSLT.IdentityGroup.Pairs

open MvPolynomial VectorSLT Finset

/-! ### Restriction to a ray -/

/-- `p ↦ (s ↦ p(s y))`, as an algebra map into univariate polynomials. -/
noncomputable def rayHom (y : Fin 2 → ℝ) : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] Polynomial ℝ :=
  aeval fun j => Polynomial.C (y j) * Polynomial.X

theorem eval_rayHom (y : Fin 2 → ℝ) (p : MvPolynomial (Fin 2) ℝ) (s : ℝ) :
    (rayHom y p).eval s = eval (s • y) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [rayHom]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, Polynomial.eval_mul, hp, map_mul, eval_X]
    simp only [rayHom, aeval_X, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Pi.smul_apply, smul_eq_mul]
    ring

/-- The cubic coefficient along the ray through `y`, as a linear functional on `PolyBox d`. -/
noncomputable def rayCub (d : ℕ) (y : Fin 2 → ℝ) : PolyBox d →ₗ[ℝ] ℝ where
  toFun p := (rayHom y p.poly).coeff 3
  map_add' p q := by simp [PolyBox.poly_add]
  map_smul' c p := by simp [PolyBox.poly_smul]

theorem rayCub_bound (d : ℕ) (y : Fin 2 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : PolyBox d, |rayCub d y p| ≤ C * ‖p‖ := by
  set L := LinearMap.toContinuousLinearMap (rayCub d y)
  refine ⟨‖L‖, norm_nonneg _, fun p => ?_⟩
  have := L.le_opNorm p
  simpa [L, Real.norm_eq_abs] using this

/-! ### The group error -/

/-- The error of a group of `n` blocks `B 0, …, B (n-1)`, output `k`, as a polynomial. -/
noncomputable def grpPoly (B : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) (k : Fin 2) :
    MvPolynomial (Fin 2) ℝ :=
  polyNet B n k - X k

theorem totalDegree_grpPoly (B : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) (k : Fin 2) :
    (grpPoly B n k).totalDegree ≤ 3 ^ n := by
  refine (totalDegree_sub _ _).trans (max_le (totalDegree_polyNet B n k) ?_)
  rw [totalDegree_X]; exact Nat.one_le_pow _ _ (by norm_num)

/-- The group error as an element of `PolyBox (3ⁿ)` (sup norm on `[-1,1]²`). -/
noncomputable def grpErr (B : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) (k : Fin 2) :
    PolyBox (3 ^ n) :=
  PolyBox.mk _ (totalDegree_grpPoly B n k)

theorem eval_grpErr (B : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) (k : Fin 2) (x : Fin 2 → ℝ) :
    eval x (grpErr B n k).poly = prefixNet B n x k - x k := by
  simp [grpErr, grpPoly, eval_polyNet]

/-- Along a ray, the group prefix is `s y + O(s³)`, with cubic term `∑ᵢ (Bᵢ k · y)³`. -/
theorem ray_polyNet (B : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (y : Fin 2 → ℝ) (n : ℕ) :
    ∀ j : Fin 2, ∃ e r : Polynomial ℝ,
      rayHom y (polyNet B n j) - Polynomial.C (y j) * Polynomial.X = Polynomial.X ^ 3 * e ∧
      rayHom y (polyNet B n j) - Polynomial.C (y j) * Polynomial.X -
        Polynomial.C (∑ i ∈ range n, (B i j ⬝ᵥ y) ^ 3) * Polynomial.X ^ 3 =
          Polynomial.X ^ 5 * r := by
  induction n with
  | zero =>
    intro j
    refine ⟨0, 0, ?_, ?_⟩ <;> simp [polyNet, rayHom]
  | succ n ih =>
    intro k
    choose e r he hr using ih
    set g : Fin 2 → Polynomial ℝ := fun j => rayHom y (polyNet B n j)
    set b : ℝ := B n k ⬝ᵥ y
    set E : Polynomial ℝ := ∑ j, Polynomial.C (B n k j) * e j
    have hL : rayHom y (∑ j, C (B n k j) * polyNet B n j) =
        Polynomial.C b * Polynomial.X + Polynomial.X ^ 3 * E := by
      simp only [map_sum, map_mul, rayHom, aeval_C, Polynomial.algebraMap_eq]
      have : ∀ j, aeval (fun j => Polynomial.C (y j) * Polynomial.X) (polyNet B n j) =
          Polynomial.C (y j) * Polynomial.X + Polynomial.X ^ 3 * e j := by
        intro j; have := he j; simp only [rayHom] at this; linear_combination this
      simp only [this, E, b, dotProduct, Fin.sum_univ_two, Polynomial.C_add, Polynomial.C_mul]
      ring
    have hstep : rayHom y (polyNet B (n + 1) k) =
        g k + (Polynomial.C b * Polynomial.X + Polynomial.X ^ 3 * E) ^ 3 := by
      simp only [polyNet, map_add, map_pow, hL, g]
    refine ⟨e k + (Polynomial.C b + Polynomial.X ^ 2 * E) ^ 3,
      r k + (3 * Polynomial.C b ^ 2 * E + 3 * Polynomial.C b * Polynomial.X ^ 2 * E ^ 2 +
        Polynomial.X ^ 4 * E ^ 3), ?_, ?_⟩
    · rw [hstep]
      have hek := he k
      simp only [g] at hek ⊢
      linear_combination hek
    · rw [hstep, sum_range_succ, Polynomial.C_add]
      have hrk := hr k
      simp only [g] at hrk ⊢
      have hb : Polynomial.C ((B n k ⬝ᵥ y) ^ 3) = Polynomial.C b ^ 3 := by
        rw [Polynomial.C_pow]
      rw [hb]
      linear_combination hrk

/-- **The degree-three part of the group error.** Along the ray through `y`, the cubic
coefficient of the group error of output `k` is `∑ᵢ (Bᵢ k · y)³`. -/
theorem rayCub_grpErr (B : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) (k : Fin 2) (y : Fin 2 → ℝ) :
    rayCub (3 ^ n) y (grpErr B n k) = ∑ i ∈ range n, (B i k ⬝ᵥ y) ^ 3 := by
  obtain ⟨e, r, -, hr⟩ := ray_polyNet B y n k
  have h : rayHom y (grpErr B n k).poly =
      Polynomial.C (∑ i ∈ range n, (B i k ⬝ᵥ y) ^ 3) * Polynomial.X ^ 3 +
        Polynomial.X ^ 5 * r := by
    simp only [grpErr, PolyBox.poly_mk, grpPoly, map_sub]
    have hX : rayHom y (X k) = Polynomial.C (y k) * Polynomial.X := by simp [rayHom]
    rw [hX]; linear_combination hr
  simp only [rayCub, LinearMap.coe_mk, AddHom.coe_mk, h, Polynomial.coeff_add,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_X_pow_mul']
  norm_num

/-- Four rays recover the four moments: `G(u) ≤ 2 (S(e₀)² + S(e₁)² + S(1,1)² + S(1,-1)²)`, where
`S(y) = ∑ᵢ ((uᵢ)₁ y₀ + (uᵢ)₂ y₁)³`. -/
theorem cubeSumSq_le_rays {n : ℕ} (u : Fin n → ℝ × ℝ) :
    cubeSumSq u ≤ 2 * ((∑ i, (u i).1 ^ 3) ^ 2 + (∑ i, (u i).2 ^ 3) ^ 2 +
      (∑ i, ((u i).1 + (u i).2) ^ 3) ^ 2 + (∑ i, ((u i).1 - (u i).2) ^ 3) ^ 2) := by
  set m0 := ∑ i, (u i).1 ^ 3
  set m1 := ∑ i, (u i).1 ^ 2 * (u i).2
  set m2 := ∑ i, (u i).1 * (u i).2 ^ 2
  set m3 := ∑ i, (u i).2 ^ 3
  have hp : ∑ i, ((u i).1 + (u i).2) ^ 3 = m0 + 3 * m1 + 3 * m2 + m3 := by
    have : ∀ i, ((u i).1 + (u i).2) ^ 3 = (u i).1 ^ 3 + 3 * ((u i).1 ^ 2 * (u i).2) +
        3 * ((u i).1 * (u i).2 ^ 2) + (u i).2 ^ 3 := fun i => by ring
    simp only [this, sum_add_distrib, ← mul_sum, m0, m1, m2, m3]
  have hm : ∑ i, ((u i).1 - (u i).2) ^ 3 = m0 - 3 * m1 + 3 * m2 - m3 := by
    have : ∀ i, ((u i).1 - (u i).2) ^ 3 = (u i).1 ^ 3 - 3 * ((u i).1 ^ 2 * (u i).2) +
        3 * ((u i).1 * (u i).2 ^ 2) - (u i).2 ^ 3 := fun i => by ring
    simp only [this, sum_add_distrib, sum_sub_distrib, ← mul_sum, m0, m1, m2, m3]
  have hG : cubeSumSq u = m0 ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2 := by
    simp [cubeSumSq, cubeSum, Fin.sum_univ_four, m0, m1, m2, m3]
  rw [hG, hp, hm]
  nlinarith [sq_nonneg (m0 + 3 * m2), sq_nonneg (3 * m1 + m3), sq_nonneg (m0 - 6 * m2),
    sq_nonneg (m3 - 6 * m1), sq_nonneg (2 * m0 + 3 * m2), sq_nonneg (2 * m3 + 3 * m1)]

/-- The row of `n` blocks seen by output `k`: `uᵢ = (Bᵢ k 0, Bᵢ k 1)`. -/
def grpRow (B : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) (k : Fin 2) : Fin n → ℝ × ℝ :=
  fun i => (B i k 0, B i k 1)

/-- **Moments from ray cubics.** If the cubic coefficient of `p ∈ PolyBox d` along every ray `y`
is `∑ᵢ ((uᵢ)₁ y₀ + (uᵢ)₂ y₁)³`, then `G(u) ≤ C ‖p‖²`, with `C` depending only on `d`. -/
theorem cubeSumSq_le_of_rayCub (d n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Fin n → ℝ × ℝ) (p : PolyBox d),
      (∀ y : Fin 2 → ℝ, rayCub d y p = ∑ i, ((u i).1 * y 0 + (u i).2 * y 1) ^ 3) →
      cubeSumSq u ≤ C * ‖p‖ ^ 2 := by
  obtain ⟨C1, hC1, h1⟩ := rayCub_bound d ![1, 0]
  obtain ⟨C2, hC2, h2⟩ := rayCub_bound d ![0, 1]
  obtain ⟨C3, hC3, h3⟩ := rayCub_bound d ![1, 1]
  obtain ⟨C4, hC4, h4⟩ := rayCub_bound d ![1, -1]
  refine ⟨2 * (C1 ^ 2 + C2 ^ 2 + C3 ^ 2 + C4 ^ 2), by positivity, fun u p hS => ?_⟩
  have sq_le : ∀ (a C : ℝ), |a| ≤ C * ‖p‖ → 0 ≤ C → a ^ 2 ≤ C ^ 2 * ‖p‖ ^ 2 := by
    intro a C h hC
    have := pow_le_pow_left₀ (abs_nonneg a) h 2
    rw [sq_abs, mul_pow] at this; exact this
  have e1 := sq_le _ _ (h1 p) hC1
  have e2 := sq_le _ _ (h2 p) hC2
  have e3 := sq_le _ _ (h3 p) hC3
  have e4 := sq_le _ _ (h4 p) hC4
  rw [hS] at e1 e2 e3 e4
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    mul_one, mul_zero, add_zero, zero_add, mul_neg] at e1 e2 e3 e4
  refine (cubeSumSq_le_rays _).trans ?_
  simp only [← sub_eq_add_neg] at e4
  nlinarith [e1, e2, e3, e4]

/-- **Lemma A-box, upper half, algebraic part.** The squared sup norm of the group error of
output `k` dominates the squared moment norm `G_n` of that row's sum of binary cubes:
`G_n(B₀ k, …, B_{n-1} k) ≤ C ‖F_{B_{n-1}} ∘ ⋯ ∘ F_{B₀} - I‖²_k`, with `C` depending only on `n`. -/
theorem cubeSumSq_le_grpErr (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2),
      cubeSumSq (grpRow B n k) ≤ C * ‖grpErr B n k‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := cubeSumSq_le_of_rayCub (3 ^ n) n
  refine ⟨C, hC, fun B k => h _ _ fun y => ?_⟩
  rw [rayCub_grpErr, ← Fin.sum_univ_eq_sum_range (fun i => (B i k ⬝ᵥ y) ^ 3)]
  simp [grpRow, dotProduct, Fin.sum_univ_two]

end VectorSLT.IdentityGroup.Pairs
