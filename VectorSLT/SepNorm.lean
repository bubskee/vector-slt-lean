/-
Brief 03 filler F1: the norm form of Candidate 2 (`results.md` §4.2, the step after (11)–(12)).

* `Hom d ⊆ PolyBox d`: homogeneous polynomials of degree `d` in two variables, with the sup
  norm on `[-1,1]²` (the `PolyBox` template). `H_d² = Fin 2 → Hom d`.
* `SepDom = Mat₂ ⊕ H₃² ⊕ H₅² ⊕ H₃² ⊕ H₅²` (the paper's 44-dimensional space).
* `sepLin A : SepDom →ₗ C([-1,1]², ℝ²)`, the separation map (11) restricted to the input box,
  with the sup norm.
* `sepLin_injective`: injective for invertible `A` (from `sepMap_kernel` and the polynomial
  identity theorem on the box).
* `sepLin_lower`: a positive smallest singular value, `σ ‖v‖ ≤ ‖Φ_A v‖`.
* `sep_absorb`: the absorption step of (12): if `h - F = Φ_A v + E` with
  `‖E‖ ≤ C η ‖v‖` and `C η ≤ σ/2`, then `‖h - F‖ ≥ (σ/2) ‖v‖`.
Deriving the expansion (11) with remainder bound (12) for the actual network (Theorem B's
group estimates (8)–(10)) is not part of this file.
-/
import VectorSLT.InvertibleSeparation
import VectorSLT.GeneralInput

namespace VectorSLT

open MvPolynomial Matrix Set

/-! ### Homogeneous polynomial evaluation -/

theorem eval_smul_hom {p : MvPolynomial (Fin 2) ℝ} {d : ℕ} (hp : p.IsHomogeneous d) (r : ℝ)
    (z : Fin 2 → ℝ) : eval (r • z) p = r ^ d * eval z p := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : m.degree = d := by
    by_contra h; exact (mem_support_iff.mp hm) (hp.coeff_eq_zero h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  have : (∑ i ∈ m.support, m i) = d := by rw [← hdeg]; rfl
  rw [this]; ring

/-! ### The spaces `H_d` -/

theorem PolyBox.ext {d : ℕ} {p q : PolyBox d} (h : p.poly = q.poly) : p = q := Subtype.ext h

/-- Homogeneous polynomials of degree `d`, as a subspace of `PolyBox d` (box sup norm). -/
def Hom (d : ℕ) : Submodule ℝ (PolyBox d) where
  carrier := {p | p.poly.IsHomogeneous d}
  add_mem' {p q} hp hq := by
    simp only [mem_ofPred_eq, PolyBox.poly_add] at *; exact hp.add hq
  zero_mem' := by simp only [mem_ofPred_eq]; exact isHomogeneous_zero _ _ d
  smul_mem' c p hp := by
    simp only [mem_ofPred_eq, PolyBox.poly_smul, smul_eq_C_mul] at *; exact hp.C_mul c

/-- The paper's `Mat₂ ⊕ H₃² ⊕ H₅² ⊕ H₃² ⊕ H₅²`. -/
abbrev SepDom : Type :=
  (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Hom 3) × (Fin 2 → Hom 5) × (Fin 2 → Hom 3) × (Fin 2 → Hom 5)

/-- A vector polynomial map as a function. -/
noncomputable def fn {d : ℕ} (S : Fin 2 → Hom d) : (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
  fun z i => eval z (S i).1.poly

theorem homDeg_fn {d : ℕ} (S : Fin 2 → Hom d) : HomDeg d (fn S) :=
  ⟨continuous_pi fun i => continuous_eval _, fun r z => by
    funext i; simp only [fn, Pi.smul_apply, smul_eq_mul]; exact eval_smul_hom (S i).2 r z⟩

theorem fn_eq_zero {d : ℕ} {S : Fin 2 → Hom d} (h : fn S = 0) : S = 0 := by
  funext i
  apply Subtype.ext; apply PolyBox.ext
  apply MvPolynomial.funext; intro z
  have := congrFun (congrFun h z) i
  have h0 : ((0 : Fin 2 → Hom d) i).1.poly = 0 := rfl
  rw [h0, map_zero]
  simpa [fn] using this

/-- The separation map at `v`, as a function of the input. -/
noncomputable def sepFun (A : Matrix (Fin 2) (Fin 2) ℝ) (v : SepDom) (x : Fin 2 → ℝ) :
    Fin 2 → ℝ :=
  sepMap A (Matrix.of v.1) (fn v.2.1) (fn v.2.2.1) (fn v.2.2.2.1) (fn v.2.2.2.2) x

/-! ### Polynomial representation -/

noncomputable def linP (M : Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) : MvPolynomial (Fin 2) ℝ :=
  ∑ j, C (M k j) * X j

noncomputable def layerP (A : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → MvPolynomial (Fin 2) ℝ :=
  fun k => X k + linP A k ^ 3

noncomputable def sepPoly (A : Matrix (Fin 2) (Fin 2) ℝ) (v : SepDom) (k : Fin 2) :
    MvPolynomial (Fin 2) ℝ :=
  3 * linP A k ^ 2 * linP (Matrix.of v.1) k + ((v.2.1 k).1.poly + (v.2.2.1 k).1.poly) +
    3 * linP A k ^ 2 * (∑ j, C (A k j) * ((v.2.1 j).1.poly + (v.2.2.1 j).1.poly)) +
    bind₁ (layerP A) (v.2.2.2.1 k).1.poly + bind₁ (layerP A) (v.2.2.2.2 k).1.poly

theorem eval_linP (M : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) (k : Fin 2) :
    eval x (linP M k) = (M *ᵥ x) k := by
  simp [linP, Matrix.mulVec, dotProduct]

theorem eval_layerP (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    (fun i => eval x (layerP A i)) = layer A x := by
  funext k; simp only [layerP, map_add, map_pow, eval_X, eval_linP, layer_apply]; rfl

theorem eval_sepPoly (A : Matrix (Fin 2) (Fin 2) ℝ) (v : SepDom) (x : Fin 2 → ℝ) (k : Fin 2) :
    eval x (sepPoly A v k) = sepFun A v x k := by
  have hb : ∀ p : MvPolynomial (Fin 2) ℝ, eval x (bind₁ (layerP A) p) = eval (layer A x) p := by
    intro p
    rw [show eval x = eval₂Hom (RingHom.id ℝ) x from rfl, eval₂Hom_bind₁]
    exact congrArg (fun y => eval y p) (eval_layerP A x)
  simp only [sepPoly, map_add, map_mul, map_pow, map_sum, eval_C, eval_linP, hb, sepFun, sepMap,
    Lmap, DVmap, fn, Pi.add_apply, Matrix.mulVec, dotProduct]
  norm_num

theorem continuous_sepFun (A : Matrix (Fin 2) (Fin 2) ℝ) (v : SepDom) :
    Continuous (sepFun A v) := by
  refine continuous_pi fun k => ?_
  have : (fun x => sepFun A v x k) = fun x => eval x (sepPoly A v k) := by
    funext x; rw [eval_sepPoly]
  rw [this]; exact continuous_eval _

/-! ### The linear map into `C([-1,1]², ℝ²)` -/

theorem sepFun_add (A : Matrix (Fin 2) (Fin 2) ℝ) (v w : SepDom) (x : Fin 2 → ℝ) :
    sepFun A (v + w) x = sepFun A v x + sepFun A w x := by
  funext k
  simp only [sepFun, sepMap, Lmap, DVmap, fn, Pi.add_apply, Prod.fst_add, Prod.snd_add,
    Submodule.coe_add, PolyBox.poly_add, map_add, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.of_apply]
  ring

theorem sepFun_smul (A : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) (v : SepDom) (x : Fin 2 → ℝ) :
    sepFun A (c • v) x = c • sepFun A v x := by
  funext k
  simp only [sepFun, sepMap, Lmap, DVmap, fn, Pi.add_apply, Pi.smul_apply, Prod.smul_fst,
    Prod.smul_snd, Submodule.coe_smul, PolyBox.poly_smul, smul_eval, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.of_apply, smul_eq_mul]
  ring

/-- **The separation map (11), restricted to the input box.** -/
noncomputable def sepLin (A : Matrix (Fin 2) (Fin 2) ℝ) : SepDom →ₗ[ℝ] C(ubox, Fin 2 → ℝ) where
  toFun v := ⟨fun x => sepFun A v x.1, (continuous_sepFun A v).comp continuous_subtype_val⟩
  map_add' v w := by ext x k; simp [sepFun_add]
  map_smul' c v := by ext x k; simp [sepFun_smul]

/-- **Injectivity for invertible `A`.** -/
theorem sepLin_injective {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) :
    Function.Injective (sepLin A) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  -- vanishing on the box ⇒ vanishing everywhere
  have hall : ∀ x, sepFun A v x = 0 := by
    have hp : ∀ k, sepPoly A v k = 0 := by
      intro k
      refine funext_set (s := fun _ => Icc (-1 : ℝ) 1) (fun _ => Icc_infinite (by norm_num))
        fun x hx => ?_
      have hx' : x ∈ ubox := by simp only [ubox, ← pi_univ_Icc]; exact hx
      have := congrArg (fun f : C(ubox, Fin 2 → ℝ) => f ⟨x, hx'⟩ k) hv
      simp only [sepLin, LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.coe_mk,
        ContinuousMap.zero_apply, Pi.zero_apply] at this
      rw [eval_sepPoly, map_zero, this]
    intro x; funext k
    rw [← eval_sepPoly, hp k, map_zero]; rfl
  obtain ⟨hΔ, h1, h2, h3, h4⟩ := sepMap_kernel hA (homDeg_fn v.2.1) (homDeg_fn v.2.2.1)
    (homDeg_fn v.2.2.2.1) (homDeg_fn v.2.2.2.2) hall
  obtain ⟨Δ, Sm, Tm, Sp, Tp⟩ := v
  simp only at hΔ h1 h2 h3 h4
  have hΔ' : Δ = 0 := by funext i j; exact congrFun (congrFun hΔ i) j
  rw [hΔ', fn_eq_zero h1, fn_eq_zero h2, fn_eq_zero h3, fn_eq_zero h4]; rfl

/-- **A positive smallest singular value** on the 44-dimensional space, sup norm on the box. -/
theorem sepLin_lower {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ v : SepDom, σ * ‖v‖ ≤ ‖sepLin A v‖ := by
  have hiff := LinearMap.injective_iff_antilipschitz (𝕜 := ℝ) (E := SepDom)
    (F := C(ubox, Fin 2 → ℝ)) (sepLin A)
  obtain ⟨K, hK, hanti⟩ := hiff.mp (sepLin_injective hA)
  refine ⟨(K : ℝ)⁻¹, inv_pos.mpr (by exact_mod_cast hK), fun v => ?_⟩
  have h := hanti.le_mul_dist v 0
  rw [dist_zero_right, map_zero, dist_zero_right] at h
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [inv_mul_le_iff₀ hK']; exact h

/-- **The absorption step of (12).** If the network error on the box splits as
`h - F = Φ_A v + E` with `‖E‖ ≤ C η ‖v‖` and `C η ≤ σ/2`, then `‖h - F‖ ≥ (σ/2) ‖v‖`. -/
theorem sep_absorb {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ (C η : ℝ), C * η ≤ σ / 2 → ∀ (v : SepDom) (E : C(ubox, Fin 2 → ℝ)),
      ‖E‖ ≤ C * η * ‖v‖ → σ / 2 * ‖v‖ ≤ ‖sepLin A v + E‖ := by
  obtain ⟨σ, hσ, hlow⟩ := sepLin_lower hA
  refine ⟨σ, hσ, fun C η hCη v E hE => ?_⟩
  have h1 := hlow v
  have h2 : ‖sepLin A v‖ - ‖E‖ ≤ ‖sepLin A v + E‖ := by
    have := norm_sub_le (sepLin A v + E) E
    simp only [add_sub_cancel_right] at this
    linarith
  have h3 : C * η * ‖v‖ ≤ σ / 2 * ‖v‖ := mul_le_mul_of_nonneg_right hCη (norm_nonneg _)
  linarith

end VectorSLT
