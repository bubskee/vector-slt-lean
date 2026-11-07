/-
Brief 03, O5, Candidate 1 (`formalization_candidates.md`): the exact inverse criterion.

`V_B(x) = (Bx)^{⊙3}`, `F_B = id + V_B` (`layer B`).
* `inverse_criterion` (any width `n`): `(∀ x, B V_B(x) = 0) ↔ (∀ x, F_{-B}(F_B x) = x)`.
* `rank_one_criterion` (width two): `B V_B ≡ 0 ↔ B = u vᵀ` with `vᵀ u^{⊙3} = 0`
  (`B = 0` is the case `u = 0` or `v = 0`).
* `shear_inverse`: every `ShearTarget A` has `F_A⁻¹ = F_{-A}`.
* `deriv_criterion` (width two): `DV_B(x) V_B(x) ≡ 0 ↔ B V_B ≡ 0`, with
  `DV_B(x) h = 3 (Bx)^{⊙2} ⊙ Bh` (`hasDerivAt_Vmap_line` identifies it as the derivative of
  `V_B` along lines).
-/
import VectorSLT.Normalization

namespace VectorSLT

open Matrix

variable {n : ℕ}

/-- `V_B(x) = (Bx)^{⊙3}`. -/
def Vmap (B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Fin n → ℝ := (B *ᵥ x) ^ 3

theorem layer_eq_add_Vmap (B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    layer B x = x + Vmap B x := rfl

/-- **Candidate 1, exact inverse criterion**: `B V_B ≡ 0` iff `F_{-B} ∘ F_B = id`. -/
theorem inverse_criterion (B : Matrix (Fin n) (Fin n) ℝ) :
    (∀ x, B *ᵥ Vmap B x = 0) ↔ ∀ x, layer (-B) (layer B x) = x := by
  constructor
  · intro h x
    have hy : B *ᵥ layer B x = B *ᵥ x := by
      rw [layer_eq_add_Vmap, Matrix.mulVec_add, h x, add_zero]
    rw [layer, Matrix.neg_mulVec, hy, layer]
    funext k
    simp only [Pi.add_apply, Pi.pow_apply, Pi.neg_apply]
    ring
  · intro h x
    funext k
    have e := congrFun (h x) k
    rw [layer, Matrix.neg_mulVec] at e
    simp only [Pi.add_apply, Pi.pow_apply, Pi.neg_apply] at e
    have hc : (B *ᵥ layer B x) k ^ 3 = (B *ᵥ x) k ^ 3 := by
      have e2 : layer B x k = x k + (B *ᵥ x) k ^ 3 := rfl
      rw [e2] at e
      linear_combination -e
    have h1 := cube_injective hc
    rw [layer_eq_add_Vmap, Matrix.mulVec_add, Pi.add_apply] at h1
    simp only [Pi.zero_apply]
    linarith

/-! ### Width two: the rank-one characterization -/

/-- A singular `2×2` matrix is an outer product. -/
theorem outer_of_det_zero (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hdet : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 0) :
    ∃ u v : Fin 2 → ℝ, ∀ i j, B i j = u i * v j := by
  by_cases ha : B 0 0 = 0
  · by_cases hb : B 0 1 = 0
    · refine ⟨![0, 1], ![B 1 0, B 1 1], fun i j => ?_⟩
      fin_cases i <;> fin_cases j <;> simp [ha, hb]
    · have hc : B 1 0 = 0 := by
        rw [ha, zero_mul, zero_sub, neg_eq_zero] at hdet
        exact (mul_eq_zero.mp hdet).resolve_left hb
      refine ⟨![1, B 1 1 / B 0 1], ![0, B 0 1], fun i j => ?_⟩
      fin_cases i <;> fin_cases j <;> simp [ha, hc]
      field_simp
  · refine ⟨![1, B 1 0 / B 0 0], ![B 0 0, B 0 1], fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;> simp
    · field_simp
    · field_simp; linarith

/-- **Candidate 1, rank-one form.** For a `2×2` matrix, `B V_B ≡ 0` iff `B = u vᵀ` with
`vᵀ u^{⊙3} = 0`. -/
theorem rank_one_criterion (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ x, B *ᵥ Vmap B x = 0) ↔
      ∃ u v : Fin 2 → ℝ, (∀ i j, B i j = u i * v j) ∧ v 0 * u 0 ^ 3 + v 1 * u 1 ^ 3 = 0 := by
  constructor
  · intro h
    -- `B` is singular
    have hdet : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 0 := by
      by_contra hd
      have hinj : ∀ y : Fin 2 → ℝ, B *ᵥ y = 0 → y = 0 := by
        intro y hy
        have h0 := congrFun hy 0
        have h1 := congrFun hy 1
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.zero_apply] at h0 h1
        have hy0 : (B 0 0 * B 1 1 - B 0 1 * B 1 0) * y 0 = 0 := by
          linear_combination B 1 1 * h0 - B 0 1 * h1
        have hy1 : (B 0 0 * B 1 1 - B 0 1 * B 1 0) * y 1 = 0 := by
          linear_combination B 0 0 * h1 - B 1 0 * h0
        funext i
        fin_cases i
        · exact (mul_eq_zero.mp hy0).resolve_left hd
        · exact (mul_eq_zero.mp hy1).resolve_left hd
      have hcol : ∀ x : Fin 2 → ℝ, ∀ k, (B *ᵥ x) k = 0 := by
        intro x k
        have hV := congrFun (hinj _ (h x)) k
        simp only [Vmap, Pi.pow_apply, Pi.zero_apply] at hV
        exact pow_eq_zero_iff (by norm_num) |>.mp hV
      have e0 := hcol ![1, 0]
      have e1 := hcol ![0, 1]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
      apply hd
      rw [e0.1, e0.2]; ring
    obtain ⟨u, v, huv⟩ := outer_of_det_zero B hdet
    refine ⟨u, v, huv, ?_⟩
    by_cases hu : u 0 = 0 ∧ u 1 = 0
    · rw [hu.1, hu.2]; ring
    by_cases hv : v 0 = 0 ∧ v 1 = 0
    · rw [hv.1, hv.2]; ring
    have hvv : 0 < v 0 ^ 2 + v 1 ^ 2 := by
      rcases not_and_or.mp hv with h0 | h1
      · have := pow_pos (abs_pos.mpr h0) 2; rw [sq_abs] at this; positivity
      · have := pow_pos (abs_pos.mpr h1) 2; rw [sq_abs] at this; positivity
    have key : ∀ i, u i * ((v 0 * u 0 ^ 3 + v 1 * u 1 ^ 3) * (v 0 ^ 2 + v 1 ^ 2) ^ 3) = 0 := by
      intro i
      have e := congrFun (h v) i
      simp only [Vmap, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.pow_apply,
        Pi.zero_apply, huv] at e
      linear_combination e
    rcases not_and_or.mp hu with h0 | h1
    · have := (mul_eq_zero.mp (key 0)).resolve_left h0
      exact (mul_eq_zero.mp this).resolve_right (pow_pos hvv 3).ne'
    · have := (mul_eq_zero.mp (key 1)).resolve_left h1
      exact (mul_eq_zero.mp this).resolve_right (pow_pos hvv 3).ne'
  · rintro ⟨u, v, huv, hrel⟩ x
    funext i
    simp only [Vmap, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.pow_apply, Pi.zero_apply,
      huv]
    linear_combination (u i * (v 0 * x 0 + v 1 * x 1) ^ 3) * hrel

/-- **Every rank-one shear target is invertible, with `F_A⁻¹ = F_{-A}`.** -/
theorem shear_inverse {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) (x : Fin 2 → ℝ) :
    layer (-A) (layer A x) = x := by
  obtain ⟨a, v, hAav, -, -, -, hsh⟩ := hA
  exact (inverse_criterion A).mp ((rank_one_criterion A).mpr ⟨a, v, hAav, hsh⟩) x

theorem shear_inverse' {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) (x : Fin 2 → ℝ) :
    layer A (layer (-A) x) = x := by
  have hA' : ShearTarget (-A) := by
    obtain ⟨a, v, hAav, ha0, ha1, hv, hsh⟩ := hA
    refine ⟨a, -v, fun i j => by simp [hAav], ha0, ha1, neg_ne_zero.mpr hv, ?_⟩
    simp only [Pi.neg_apply]; linarith
  have := shear_inverse hA' x
  rwa [neg_neg] at this

/-! ### The derivative form -/

/-- `DV_B(x) h = 3 (Bx)^{⊙2} ⊙ (Bh)`. -/
def DVmap (B : Matrix (Fin n) (Fin n) ℝ) (x h : Fin n → ℝ) : Fin n → ℝ :=
  fun k => 3 * (B *ᵥ x) k ^ 2 * (B *ᵥ h) k

/-- `DV_B(x)` is the derivative of `V_B` along every line through `x`. -/
theorem hasDerivAt_Vmap_line (B : Matrix (Fin n) (Fin n) ℝ) (x h : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => Vmap B (x + t • h)) (DVmap B x h) 0 := by
  rw [hasDerivAt_pi]
  intro k
  have hlin : ∀ t : ℝ, (B *ᵥ (x + t • h)) k = (B *ᵥ x) k + t * (B *ᵥ h) k := by
    intro t; rw [Matrix.mulVec_add, Matrix.mulVec_smul]; simp
  simp only [Vmap, Pi.pow_apply, hlin, DVmap]
  have h1 : HasDerivAt (fun t : ℝ => (B *ᵥ x) k + t * (B *ᵥ h) k) ((B *ᵥ h) k) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ((B *ᵥ h) k)).const_add ((B *ᵥ x) k)
  convert h1.pow 3 using 1
  simp

/-- **Candidate 1, derivative form** (width two): `DV_B V_B ≡ 0 ↔ B V_B ≡ 0`. -/
theorem deriv_criterion (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ x, DVmap B x (Vmap B x) = 0) ↔ ∀ x, B *ᵥ Vmap B x = 0 := by
  constructor
  · intro h x
    funext k
    -- `g = (B V_B)_k` is continuous and vanishes wherever `ℓ_k = (Bx)_k ≠ 0`
    set g : (Fin 2 → ℝ) → ℝ := fun y => (B *ᵥ Vmap B y) k
    have hg : Continuous g := by
      simp only [g, Vmap, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.pow_apply]
      fun_prop
    have hzero : ∀ y, (B *ᵥ y) k ≠ 0 → g y = 0 := by
      intro y hy
      have e := congrFun (h y) k
      simp only [DVmap, Pi.zero_apply] at e
      rcases mul_eq_zero.mp e with e1 | e2
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          ((mul_eq_zero.mp e1).resolve_left (by norm_num))) hy
      · exact e2
    show g x = 0
    by_cases hx : (B *ᵥ x) k = 0
    · by_cases hrow : B k 0 = 0 ∧ B k 1 = 0
      · simp only [g, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hrow.1, hrow.2]; ring
      · -- a direction `w` with `ℓ_k(w) ≠ 0`
        obtain ⟨w, hw⟩ : ∃ w : Fin 2 → ℝ, (B *ᵥ w) k ≠ 0 := by
          rcases not_and_or.mp hrow with h0 | h1
          · exact ⟨![1, 0], by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0⟩
          · exact ⟨![0, 1], by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h1⟩
        have hline : Continuous fun t : ℝ => g (x + t • w) := hg.comp (by fun_prop)
        have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, g (x + t • w) = 0 := by
          filter_upwards [self_mem_nhdsWithin] with t ht
          apply hzero
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, hx, zero_add,
            smul_eq_mul]
          exact mul_ne_zero ht hw
        have ht := (hline.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
        have h0 : g (x + (0 : ℝ) • w) = 0 :=
          tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm))
        simpa using h0
    · exact hzero x hx
  · intro h x
    funext k
    simp only [DVmap, h x, Pi.zero_apply, mul_zero]

end VectorSLT
