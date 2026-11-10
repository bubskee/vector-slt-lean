/-
Paper 2, Appendix A.3: the polynomial algebra behind the injectivity of the endpoint and
one-block-prefix maps for invertible `A`.

* `coeff_aeval_cubic`: along `s ↦ s y + s³ w`, the coefficient of `s^{3D}` in `Q(s y + s³ w)` is
  `Q_D(w)`, where `D = totalDegree Q` and `Q_D` is the top homogeneous part. This is the paper's
  "substitution argument": the top part of `Q ∘ F_A` has degree `3D` and equals `Q_D ∘ V_A`.
* `totalDegree_le_one_of_odd`: if `Q(F_A(s y))` only has the powers `s, s³, s⁵` for every `y`,
  then `Q` has degree `≤ 1` (since `V_A` is onto for invertible `A`).
* `eq_zero_of_layer_odd`: under the same hypothesis with no `s` term, `Q = 0`.
* `lin_mul_sq_zero`: `(δ · x)(a · x)² ≡ 0` with `a ≠ 0` forces `δ = 0` (injectivity of `L_A`).
-/
import VectorSLT.IdentityGroup.Pairs.FirstPosition
import VectorSLT.InvertibleSeparation

namespace VectorSLT.IdentityGroup.Pairs

open VectorSLT MvPolynomial
open scoped Matrix

/-! ### One-variable facts -/

/-- `a s + b s³ + c s⁵ ≡ 0` forces `a = b = c = 0`. -/
theorem odd_poly_zero {a b c : ℝ} (h : ∀ s : ℝ, a * s + b * s ^ 3 + c * s ^ 5 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hp : (Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X ^ 3 +
      Polynomial.C c * Polynomial.X ^ 5 : Polynomial ℝ) = 0 := by
    apply Polynomial.funext; intro s; simpa using h s
  have e1 := congrArg (fun p : Polynomial ℝ => p.coeff 1) hp
  have e3 := congrArg (fun p : Polynomial ℝ => p.coeff 3) hp
  have e5 := congrArg (fun p : Polynomial ℝ => p.coeff 5) hp
  simp [Polynomial.coeff_X_pow] at e1 e3 e5
  exact ⟨e1, e3, e5⟩

/-! ### The top coefficient under a cubic substitution -/

theorem coeff_pow_mul_pow_cubic {p0 p1 : Polynomial ℝ} (h0 : p0.natDegree ≤ 3)
    (h1 : p1.natDegree ≤ 3) {a b D : ℕ} (hab : a + b ≤ D) :
    (p0 ^ a * p1 ^ b).coeff (3 * D) =
      if a + b = D then p0.coeff 3 ^ a * p1.coeff 3 ^ b else 0 := by
  split_ifs with h
  · subst h
    rw [show 3 * (a + b) = a * 3 + b * 3 by ring]
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (Polynomial.natDegree_pow_le_of_le a h0)
      (Polynomial.natDegree_pow_le_of_le b h1)]
    rw [Polynomial.coeff_pow_of_natDegree_le h0, Polynomial.coeff_pow_of_natDegree_le h1]
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    calc (p0 ^ a * p1 ^ b).natDegree ≤ (p0 ^ a).natDegree + (p1 ^ b).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ a * 3 + b * 3 := add_le_add (Polynomial.natDegree_pow_le_of_le a h0)
          (Polynomial.natDegree_pow_le_of_le b h1)
      _ < 3 * D := by omega

/-- `p ↦ (s ↦ p(s y + s³ w))`, as a univariate polynomial. -/
noncomputable def cubicHom (y w : Fin 2 → ℝ) : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] Polynomial ℝ :=
  aeval fun i => Polynomial.C (y i) * Polynomial.X + Polynomial.C (w i) * Polynomial.X ^ 3

theorem eval_cubicHom (y w : Fin 2 → ℝ) (p : MvPolynomial (Fin 2) ℝ) (s : ℝ) :
    (cubicHom y w p).eval s = eval (s • y + s ^ 3 • w) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [cubicHom]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, Polynomial.eval_mul, hp, map_mul, eval_X]
    simp only [cubicHom, aeval_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- **The top coefficient.** The coefficient of `s^{3D}` in `Q(s y + s³ w)` is `Q_D(w)`. -/
theorem coeff_aeval_cubic (Q : MvPolynomial (Fin 2) ℝ) (y w : Fin 2 → ℝ) :
    (cubicHom y w Q).coeff (3 * Q.totalDegree) = eval w (homogeneousComponent Q.totalDegree Q) := by
  set f : Fin 2 → Polynomial ℝ :=
    fun i => Polynomial.C (y i) * Polynomial.X + Polynomial.C (w i) * Polynomial.X ^ 3
  have hf : ∀ i, (f i).natDegree ≤ 3 := by
    intro i
    refine (Polynomial.natDegree_add_le _ _).trans
      (max_le ?_ (Polynomial.natDegree_C_mul_X_pow_le _ _))
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  have hf3 : ∀ i, (f i).coeff 3 = w i := by intro i; simp [f]
  set D := Q.totalDegree with hD
  have hQ : cubicHom y w Q = aeval f (∑ v ∈ Q.support, monomial v (Q.coeff v)) := by
    rw [← Q.as_sum]; rfl
  rw [hQ]
  rw [homogeneousComponent_apply, map_sum, map_sum, Polynomial.finsetSum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [aeval_monomial, eval_monomial, Polynomial.algebraMap_eq, Polynomial.coeff_C_mul,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    Fin.prod_univ_two, Fin.prod_univ_two]
  have hdeg : d 0 + d 1 ≤ D := by
    have := le_totalDegree hd
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two, ← hD] at this
    exact this
  have hdd : d.degree = d 0 + d 1 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  rw [coeff_pow_mul_pow_cubic (hf 0) (hf 1) hdeg, hf3, hf3, hdd]
  split_ifs <;> ring

/-- A nonzero polynomial has a nonzero top homogeneous part. -/
theorem homogeneousComponent_totalDegree_ne_zero {Q : MvPolynomial (Fin 2) ℝ} (hQ : Q ≠ 0) :
    homogeneousComponent Q.totalDegree Q ≠ 0 := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup Q.support (support_nonempty.mpr hQ)
    (fun s => s.sum fun _ e => e)
  intro h0
  have hc := congrArg (fun p : MvPolynomial (Fin 2) ℝ => p.coeff m) h0
  simp only [coeff_homogeneousComponent] at hc
  have hdeg : m.degree = Q.totalDegree := by
    rw [totalDegree, hmax, Finsupp.degree_eq_sum, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp only [hdeg, ↓reduceIte] at hc
  exact (mem_support_iff.mp hm) (by simpa using hc)

/-- `F_A(s y) = s y + s³ V_A(y)`. -/
theorem layer_smul (A : Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ) (y : Fin 2 → ℝ) :
    layer A (s • y) = s • y + s ^ 3 • Vmap A y := by
  funext i
  simp only [layer_apply', Vmap, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.pow_apply,
    mulVec_two]
  ring

/-- **Degree count.** For invertible `A`, if every `s ↦ Q(F_A(s y))` has only the powers
`s, s³, s⁵`, then `Q` has total degree `≤ 1`. -/
theorem totalDegree_le_one_of_odd {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0)
    {Q : MvPolynomial (Fin 2) ℝ}
    (h : ∀ y : Fin 2 → ℝ, ∃ c₁ c₃ c₅ : ℝ, ∀ s : ℝ,
      eval (layer A (s • y)) Q = c₁ * s + c₃ * s ^ 3 + c₅ * s ^ 5) :
    Q.totalDegree ≤ 1 := by
  by_contra hD
  push Not at hD
  have hQ : Q ≠ 0 := by rintro rfl; simp at hD
  apply homogeneousComponent_totalDegree_ne_zero hQ
  apply MvPolynomial.funext; intro z
  obtain ⟨y, rfl⟩ := Vmap_surj hA z
  obtain ⟨c₁, c₃, c₅, hc⟩ := h y
  have hpoly : cubicHom y (Vmap A y) Q = Polynomial.C c₁ * Polynomial.X +
      Polynomial.C c₃ * Polynomial.X ^ 3 + Polynomial.C c₅ * Polynomial.X ^ 5 := by
    apply Polynomial.funext; intro s
    rw [eval_cubicHom, ← layer_smul, hc s]; simp
  have hco := coeff_aeval_cubic Q y (Vmap A y)
  rw [hpoly] at hco
  have h1 : 3 * Q.totalDegree ≠ 1 := by omega
  have h3 : 3 * Q.totalDegree ≠ 3 := by omega
  have h5 : 3 * Q.totalDegree ≠ 5 := by omega
  have hD1 : Q.totalDegree ≠ 1 := by omega
  simp [Polynomial.coeff_X, Polynomial.coeff_X_pow, h1.symm, hD1, h5] at hco
  rw [map_zero, ← hco]

/-- A polynomial of total degree `≤ 1` is affine. -/
theorem eval_affine {Q : MvPolynomial (Fin 2) ℝ} (hQ : Q.totalDegree ≤ 1) (z : Fin 2 → ℝ) :
    eval z Q = eval 0 Q + (eval ![1, 0] Q - eval 0 Q) * z 0 + (eval ![0, 1] Q - eval 0 Q) * z 1 := by
  have key : ∀ x : Fin 2 → ℝ, eval x Q = ∑ d ∈ Q.support, Q.coeff d * (x 0 ^ d 0 * x 1 ^ d 1) := by
    intro x
    conv_lhs => rw [Q.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
  rw [key z, key 0, key ![1, 0], key ![0, 1], ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d 0 + d 1 ≤ 1 := by
    have := le_totalDegree hd
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at this
    omega
  have h0 : d 0 ≤ 1 := by omega
  have h1 : d 1 ≤ 1 := by omega
  interval_cases hd0 : d 0 <;> interval_cases hd1 : d 1 <;> simp_all

/-- **`Q ∘ F_A` with no terms in `s`, `s⁰`.** For invertible `A`, if every `s ↦ Q(F_A(s y))` is
`c₃ s³ + c₅ s⁵`, then `Q = 0`. -/
theorem eq_zero_of_layer_odd {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0)
    {Q : MvPolynomial (Fin 2) ℝ}
    (h : ∀ y : Fin 2 → ℝ, ∃ c₃ c₅ : ℝ, ∀ s : ℝ,
      eval (layer A (s • y)) Q = c₃ * s ^ 3 + c₅ * s ^ 5) : Q = 0 := by
  have hdeg : Q.totalDegree ≤ 1 := totalDegree_le_one_of_odd hA fun y => by
    obtain ⟨c₃, c₅, hc⟩ := h y
    exact ⟨0, c₃, c₅, fun s => by rw [hc s]; ring⟩
  have hq0 : eval 0 Q = 0 := by
    obtain ⟨c₃, c₅, hc⟩ := h 0
    have := hc 0
    simp only [smul_zero] at this
    rw [show layer A 0 = 0 by funext i; simp [layer_apply']] at this
    rw [this]; ring
  have hl : ∀ y : Fin 2 → ℝ, eval ![1, 0] Q * y 0 + eval ![0, 1] Q * y 1 = 0 := by
    intro y
    obtain ⟨c₃, c₅, hc⟩ := h y
    have hs : ∀ s : ℝ, (eval ![1, 0] Q * y 0 + eval ![0, 1] Q * y 1) * s +
        (eval ![1, 0] Q * Vmap A y 0 + eval ![0, 1] Q * Vmap A y 1 - c₃) * s ^ 3 +
          (-c₅) * s ^ 5 = 0 := by
      intro s
      have := hc s
      rw [eval_affine hdeg, layer_smul, hq0] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      linear_combination this
    exact (odd_poly_zero hs).1
  have hl0 : eval ![1, 0] Q = 0 := by simpa using hl ![1, 0]
  have hl1 : eval ![0, 1] Q = 0 := by simpa using hl ![0, 1]
  apply MvPolynomial.funext; intro z
  rw [eval_affine hdeg, map_zero, hq0, hl0, hl1]; ring

/-- **Injectivity of `Δ ↦ (δ · x)(a · x)²`.** -/
theorem lin_mul_sq_zero {δ a : Fin 2 → ℝ} (ha : a ≠ 0)
    (h : ∀ x : Fin 2 → ℝ, (δ ⬝ᵥ x) * (a ⬝ᵥ x) ^ 2 = 0) : δ = 0 := by
  set pδ : MvPolynomial (Fin 2) ℝ := C (δ 0) * X 0 + C (δ 1) * X 1
  set pa : MvPolynomial (Fin 2) ℝ := C (a 0) * X 0 + C (a 1) * X 1
  have ev : ∀ (u : Fin 2 → ℝ) (x : Fin 2 → ℝ),
      eval x (C (u 0) * X 0 + C (u 1) * X 1) = u ⬝ᵥ x := by
    intro u x; simp only [map_add, map_mul, eval_C, eval_X, dot_two]
  have hprod : pδ * pa ^ 2 = 0 := by
    apply MvPolynomial.funext; intro x
    simp only [map_mul, map_pow, pδ, pa, ev, map_zero]; exact h x
  have hpa : pa ≠ 0 := by
    intro h0
    apply ha
    funext i
    have := congrArg (eval (Pi.single i 1)) h0
    simp only [pa, ev, map_zero] at this
    simpa [dotProduct_single] using this
  have hpδ : pδ = 0 := by
    rcases mul_eq_zero.mp hprod with h1 | h1
    · exact h1
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h1) hpa
  funext i
  have := congrArg (eval (Pi.single i 1)) hpδ
  simp only [pδ, ev, map_zero] at this
  simpa [dotProduct_single] using this

/-- Rows of an invertible matrix are nonzero. -/
theorem row_ne_zero {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) (k : Fin 2) : A k ≠ 0 := by
  intro h
  apply hA
  rw [Matrix.det_fin_two]
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.zero_apply] at h0 h1
  fin_cases k <;> simp_all

end VectorSLT.IdentityGroup.Pairs
