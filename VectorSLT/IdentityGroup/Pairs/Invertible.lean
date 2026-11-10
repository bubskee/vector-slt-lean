/-
Paper 2, Theorem `thm:invertible` (Appendix A.3) at the endpoints: `det A ≠ 0`, active block
first or last (Lean `p = 0` and `p = 3`), the other three blocks kept as one group.

* `invertible_first_injective`: `(Δ, P) ↦ L_A Δ + P ∘ F_A` is injective. If `P_k` had degree
  `D ≥ 2`, the coefficient of `s^{3D}` in `P_k(F_A(s y))` would be `(P_k)_D(V_A y)`, which is not
  identically zero since `V_A` is onto (`totalDegree_le_one_of_odd`); the affine case is direct
  (`eq_zero_of_layer_odd`), and then `L_A Δ = 0` forces `Δ = 0`.
* `invertible_last_injective`: `(Δ, P) ↦ L_A Δ + DF_A P` is injective, by the multiplication
  argument along rays.

With FirstPosition.lean and LastPosition.lean these give `Z_N ≤ C N⁻⁴` from `CubeSumUpper 3`,
and the pair `(4, 1)` with the certified lower bound.
-/
import VectorSLT.IdentityGroup.Pairs.LastPosition

namespace VectorSLT.IdentityGroup.Pairs

open MeasureTheory Set Filter Topology VectorSLT MvPolynomial
open scoped Matrix

theorem mulVec_smul_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ) (y : Fin 2 → ℝ) (k : Fin 2) :
    (A *ᵥ (s • y)) k = s * (A *ᵥ y) k := by
  rw [Matrix.mulVec_smul]; rfl

/-! ### Active block first -/

/-- **Injectivity of `𝒟` at the first position for invertible `A`.** -/
theorem invertible_first_injective {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) :
    Function.Injective (M0 A 0 (3 ^ 3)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  have hrow : ∀ k, (w.2 k).poly = 0 ∧ w.1 k = 0 := by
    intro k
    have hk := M0_kernel A hw k
    have hQ : (w.2 k).poly = 0 := by
      refine eq_zero_of_layer_odd hA fun y => ⟨-(3 * (w.1 k ⬝ᵥ y) * (A *ᵥ y) k ^ 2), 0,
        fun s => ?_⟩
      have := hk (s • y)
      rw [mulVec_smul_apply, dotProduct_smul, smul_eq_mul] at this
      linear_combination this
    refine ⟨hQ, lin_mul_sq_zero (row_ne_zero hA k) fun x => ?_⟩
    have := hk x
    rw [hQ, map_zero, add_zero] at this
    have e : (A *ᵥ x) k = A k ⬝ᵥ x := rfl
    rw [e] at this
    linear_combination this / 3
  refine Prod.ext (funext fun k => (hrow k).2) (funext fun k => Subtype.ext ?_)
  exact (hrow k).1

/-! ### Active block last -/

/-- The kernel of `M_0` at the last position, as an identity on the whole plane. -/
theorem M3_kernel (A : Matrix (Fin 2) (Fin 2) ℝ) {d : ℕ} {v : EndDom d}
    (hv : M3 A (0 : EndDom d) v = 0) (k : Fin 2) (x : Fin 2 → ℝ) :
    (v.1 k ⬝ᵥ x) * (3 * (A *ᵥ x) k ^ 2) + eval x (v.2 k).poly +
      3 * (A *ᵥ x) k ^ 2 * (A k 0 * eval x (v.2 0).poly + A k 1 * eval x (v.2 1).poly) = 0 := by
  set q : MvPolynomial (Fin 2) ℝ :=
    (C (v.1 k 0) * X 0 + C (v.1 k 1) * X 1) * (3 * (C (A k 0) * X 0 + C (A k 1) * X 1) ^ 2) +
      (v.2 k).poly + 3 * (C (A k 0) * X 0 + C (A k 1) * X 1) ^ 2 *
        (C (A k 0) * (v.2 0).poly + C (A k 1) * (v.2 1).poly)
  have hq : ∀ y : Fin 2 → ℝ, eval y q = (v.1 k ⬝ᵥ y) * (3 * (A *ᵥ y) k ^ 2) + eval y (v.2 k).poly +
      3 * (A *ᵥ y) k ^ 2 * (A k 0 * eval y (v.2 0).poly + A k 1 * eval y (v.2 1).poly) := by
    intro y
    simp only [q, map_add, map_mul, map_pow, eval_C, eval_X, dot_two, mulVec_two]
    norm_num
  rw [← hq]
  refine eval_eq_zero_of_box (fun y => ?_) x
  have h := congrArg (fun f : C(ubox, Fin 2 → ℝ) => f y k) hv
  simp only [M3_apply, M3fun, ContinuousMap.zero_apply, Pi.zero_apply, Prod.fst_zero,
    Prod.snd_zero] at h
  have h0 : evalV (0 : Fin 2 → PolyBox d) y.1 = 0 := by
    funext i; simp only [evalV, Pi.zero_apply]; rfl
  rw [h0, add_zero, show A + Matrix.of (0 : Fin 2 → Fin 2 → ℝ) = A by ext; simp] at h
  rw [hq, ← h]
  simp only [evalV, mulVec_two]
  ring

/-- **The multiplication argument along rays.** -/
theorem last_kernel {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) {δ : Fin 2 → Fin 2 → ℝ}
    {P : Fin 2 → MvPolynomial (Fin 2) ℝ}
    (h : ∀ k x, (δ k ⬝ᵥ x) * (3 * (A *ᵥ x) k ^ 2) + eval x (P k) +
      3 * (A *ᵥ x) k ^ 2 * (A k 0 * eval x (P 0) + A k 1 * eval x (P 1)) = 0) :
    δ = 0 ∧ P = 0 := by
  -- step 1: on rays through `y` with `(Ay)₀ (Ay)₁ ≠ 0`, every `P k` vanishes
  have hray : ∀ y : Fin 2 → ℝ, (A *ᵥ y) 0 ≠ 0 → (A *ᵥ y) 1 ≠ 0 → ∀ k, rayHom y (P k) = 0 := by
    intro y hy0 hy1
    set g : Fin 2 → Polynomial ℝ := fun k => rayHom y (P k)
    set a : Fin 2 → ℝ := fun k => (A *ᵥ y) k
    have ha : ∀ k, a k ≠ 0 := by intro k; fin_cases k; exacts [hy0, hy1]
    have hpoly : ∀ k, g k + Polynomial.C (3 * a k ^ 2) * ((Polynomial.C (A k 0) * g 0 +
        Polynomial.C (A k 1) * g 1) * Polynomial.X ^ 2) +
        Polynomial.C (3 * a k ^ 2 * (δ k ⬝ᵥ y)) * Polynomial.X ^ 3 = 0 := by
      intro k
      apply Polynomial.funext; intro s
      have := h k (s • y)
      simp only [g, a, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, eval_rayHom, Polynomial.eval_zero]
      rw [mulVec_smul_apply, dotProduct_smul, smul_eq_mul] at this
      linear_combination this
    set n := max (g 0).natDegree (g 1).natDegree
    have hgn : ∀ k, (g k).natDegree ≤ n := by
      intro k; fin_cases k; exacts [le_max_left _ _, le_max_right _ _]
    have hn : n ≤ 1 := by
      by_contra hn
      push Not at hn
      have htop : ∀ k, A k 0 * (g 0).coeff n + A k 1 * (g 1).coeff n = 0 := by
        intro k
        have e := congrArg (fun p : Polynomial ℝ => p.coeff (n + 2)) (hpoly k)
        simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow,
          Polynomial.coeff_zero] at e
        have hn3 : n + 2 ≠ 3 := by omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hgn k; omega),
          Polynomial.coeff_X_pow] at e
        simp only [hn3, ↓reduceIte, mul_zero, add_zero, zero_add] at e
        have hak : 3 * a k ^ 2 ≠ 0 := by have := ha k; positivity
        have : 3 * a k ^ 2 * (A k 0 * (g 0).coeff n + A k 1 * (g 1).coeff n) = 0 := by
          linarith
        exact (mul_eq_zero.mp this).resolve_left hak
      have hc : (fun j => (g j).coeff n) = 0 := by
        apply mulVec_inj_of_det hA
        funext k; rw [mulVec_two]; exact htop k
      have hlead : ∃ j, (g j).natDegree = n := by
        rcases max_choice (g 0).natDegree (g 1).natDegree with h' | h'
        · exact ⟨0, h'.symm⟩
        · exact ⟨1, h'.symm⟩
      obtain ⟨j, hj⟩ := hlead
      have hgj : g j ≠ 0 := by intro h0; rw [h0, Polynomial.natDegree_zero] at hj; omega
      have := congrFun hc j
      simp only [Pi.zero_apply] at this
      rw [← hj] at this
      exact (Polynomial.leadingCoeff_ne_zero.mpr hgj) this
    intro k
    have e0 := congrArg (fun p : Polynomial ℝ => p.coeff 0) (hpoly k)
    have e1 := congrArg (fun p : Polynomial ℝ => p.coeff 1) (hpoly k)
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow',
      Polynomial.coeff_zero] at e0 e1
    norm_num at e0 e1
    apply Polynomial.ext; intro m
    rw [Polynomial.coeff_zero]
    rcases m with _ | _ | m
    · exact e0
    · exact e1
    · have h' : (rayHom y (P k)).natDegree ≤ n := hgn k
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  -- step 2: `P = 0`, by density
  have hP : P = 0 := by
    have hf : Continuous fun y : Fin 2 → ℝ => fun k => eval y (P k) :=
      continuous_pi fun k => continuous_eval _
    have h0 := vanish_of_dense hA hf fun y hy0 hy1 => by
      funext k
      have := congrArg (Polynomial.eval 1) (hray y hy0 hy1 k)
      rw [eval_rayHom, one_smul, Polynomial.eval_zero] at this
      exact this
    funext k
    apply MvPolynomial.funext; intro y
    have := congrFun (congrFun h0 y) k
    simpa using this
  -- step 3: `Δ = 0`
  refine ⟨funext fun k => lin_mul_sq_zero (row_ne_zero hA k) fun x => ?_, hP⟩
  have := h k x
  rw [hP] at this
  simp only [Pi.zero_apply, map_zero, add_zero, mul_zero] at this
  have e : (A *ᵥ x) k = A k ⬝ᵥ x := rfl
  rw [e] at this
  linear_combination this / 3

/-- **Injectivity of the linear part at the last position for invertible `A`.** -/
theorem invertible_last_injective {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) :
    Function.Injective (M3 A (0 : EndDom (3 ^ 3))) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  obtain ⟨hδ, hP⟩ := last_kernel hA (P := fun k => (w.2 k).poly) (fun k x => M3_kernel A hw k x)
  refine Prod.ext hδ (funext fun k => Subtype.ext ?_)
  exact congrFun hP k

/-! ### Headline statements -/

/-- **Theorem "invertible active blocks", active block first (Lean `p = 0`), upper half**, from
`CubeSumUpper 3`. -/
theorem invertible_first_upper {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0)
    (h3 : CubeSumUpper 3) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → Zpos μ A φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4) :=
  first_upper (invertible_first_injective hA) h3

/-- **Theorem "invertible active blocks", active block last (Lean `p = 3`), upper half**, from
`CubeSumUpper 3`. -/
theorem invertible_last_upper {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0)
    (h3 : CubeSumUpper 3) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → Zpos μ A φ χ 3 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4) :=
  last_upper (invertible_last_injective hA) h3

/-- **Theorem "invertible active blocks", position one: the pair `(4, 1)`**, from
`CubeSumUpper 3`, with the certified lower bound `Zpos_lower_N4`. -/
theorem invertible_first_pair {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0)
    (h3 : CubeSumUpper 3) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ᶠ θ in 𝓝 (basePos A 0), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      VectorSLT.SLT.HasLaplacePair (Zpos μ A φ χ 0) 4 1 :=
  pair_of_upper A 0 (invertible_first_upper hA h3)

/-- **Theorem "invertible active blocks", position four: the pair `(4, 1)`**, from
`CubeSumUpper 3`, with the certified lower bound `Zpos_lower_N4`. -/
theorem invertible_last_pair {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0)
    (h3 : CubeSumUpper 3) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ᶠ θ in 𝓝 (basePos A 3), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      VectorSLT.SLT.HasLaplacePair (Zpos μ A φ χ 3) 4 1 :=
  pair_of_upper A 3 (invertible_last_upper hA h3)

end VectorSLT.IdentityGroup.Pairs
