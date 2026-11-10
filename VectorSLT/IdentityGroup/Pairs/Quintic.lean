/-
Paper 2, Appendix A.2: binary quintic forms and the product lower bound behind (A-R).

* `quin`: a binary quintic from its six coefficients;
* `mulQuint w ψ`: the coefficients of `(w · x)² · ψ(x)` for a linear form `w` and a cubic `ψ`;
* `mulQuint_lower`: `m ‖w‖² ‖ψ‖ ≤ ‖mulQuint w ψ‖` for a fixed `m > 0` (coefficient sup norms).
  This is the paper's "polynomial multiplication in fixed degrees gives
  `‖c_i² φ_i‖ ≥ c₀ ‖c_i‖² ‖φ_i‖`", proved by compactness of the product of unit spheres and
  homogeneity.
-/
import VectorSLT.IdentityGroup.Pairs.OnePrefix

namespace VectorSLT.IdentityGroup.Pairs

open MeasureTheory Set Filter Topology VectorSLT MvPolynomial
open scoped Matrix

/-- A binary quintic form from its coefficients of `x⁵, x⁴y, x³y², x²y³, xy⁴, y⁵`. -/
def quin (c : Fin 6 → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  c 0 * x 0 ^ 5 + c 1 * x 0 ^ 4 * x 1 + c 2 * x 0 ^ 3 * x 1 ^ 2 + c 3 * x 0 ^ 2 * x 1 ^ 3 +
    c 4 * x 0 * x 1 ^ 4 + c 5 * x 1 ^ 5

/-- A vector of binary quintic forms. -/
def quinV (T : Fin 2 → Fin 6 → ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => quin (T i) x

theorem quin_smul (c : Fin 6 → ℝ) (s : ℝ) (x : Fin 2 → ℝ) : quin c (s • x) = s ^ 5 * quin c x := by
  simp only [quin, Pi.smul_apply, smul_eq_mul]; ring

theorem continuous_quin_joint {X' : Type*} [TopologicalSpace X'] {c : X' → Fin 6 → ℝ}
    (hc : Continuous c) {x : X' → Fin 2 → ℝ} (hx : Continuous x) :
    Continuous fun q => quin (c q) (x q) := by
  have hc' : ∀ j, Continuous fun q => c q j := fun j => (continuous_apply j).comp hc
  have hx' : ∀ j, Continuous fun q => x q j := fun j => (continuous_apply j).comp hx
  simp only [quin]
  have := hc' 0; have := hc' 1; have := hc' 2; have := hc' 3; have := hc' 4; have := hc' 5
  have := hx' 0; have := hx' 1
  fun_prop

/-- `quin c` as a polynomial. -/
noncomputable def quinPoly (c : Fin 6 → ℝ) : MvPolynomial (Fin 2) ℝ :=
  C (c 0) * X 0 ^ 5 + C (c 1) * X 0 ^ 4 * X 1 + C (c 2) * X 0 ^ 3 * X 1 ^ 2 +
    C (c 3) * X 0 ^ 2 * X 1 ^ 3 + C (c 4) * X 0 * X 1 ^ 4 + C (c 5) * X 1 ^ 5

theorem eval_quinPoly (c : Fin 6 → ℝ) (x : Fin 2 → ℝ) : eval x (quinPoly c) = quin c x := by
  simp [quinPoly, quin]

/-- A quintic form vanishing everywhere has zero coefficients. -/
theorem quin_eq_zero {c : Fin 6 → ℝ} (h : ∀ x, quin c x = 0) : c = 0 := by
  have hp : (Polynomial.C (c 0) * Polynomial.X ^ 5 + Polynomial.C (c 1) * Polynomial.X ^ 4 +
      Polynomial.C (c 2) * Polynomial.X ^ 3 + Polynomial.C (c 3) * Polynomial.X ^ 2 +
      Polynomial.C (c 4) * Polynomial.X + Polynomial.C (c 5) : Polynomial ℝ) = 0 := by
    apply Polynomial.funext; intro s
    have := h ![s, 1]
    simp only [quin, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_zero]
    linear_combination this
  funext j
  have e := fun n => congrArg (fun p : Polynomial ℝ => p.coeff n) hp
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4; have e5 := e 5
  simp [Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_C] at e0 e1 e2 e3 e4 e5
  fin_cases j <;> simp_all

/-- The coefficients of `(w · x)² · cub ψ x`. -/
def mulQuint (w : Fin 2 → ℝ) (ψ : Fin 4 → ℝ) : Fin 6 → ℝ :=
  ![w 0 ^ 2 * ψ 0, w 0 ^ 2 * ψ 1 + 2 * w 0 * w 1 * ψ 0,
    w 0 ^ 2 * ψ 2 + 2 * w 0 * w 1 * ψ 1 + w 1 ^ 2 * ψ 0,
    w 0 ^ 2 * ψ 3 + 2 * w 0 * w 1 * ψ 2 + w 1 ^ 2 * ψ 1,
    2 * w 0 * w 1 * ψ 3 + w 1 ^ 2 * ψ 2, w 1 ^ 2 * ψ 3]

theorem quin_mulQuint (w : Fin 2 → ℝ) (ψ : Fin 4 → ℝ) (x : Fin 2 → ℝ) :
    quin (mulQuint w ψ) x = (w ⬝ᵥ x) ^ 2 * cub ψ x := by
  simp [quin, mulQuint, cub]; ring

theorem mulQuint_smul (s t : ℝ) (w : Fin 2 → ℝ) (ψ : Fin 4 → ℝ) :
    mulQuint (s • w) (t • ψ) = (s ^ 2 * t) • mulQuint w ψ := by
  funext j; fin_cases j <;> simp [mulQuint] <;> ring

theorem continuous_mulQuint : Continuous fun p : (Fin 2 → ℝ) × (Fin 4 → ℝ) => mulQuint p.1 p.2 := by
  refine continuous_pi fun j => ?_
  have hw : ∀ i, Continuous fun p : (Fin 2 → ℝ) × (Fin 4 → ℝ) => p.1 i := fun i =>
    (continuous_apply i).comp continuous_fst
  have hψ : ∀ i, Continuous fun p : (Fin 2 → ℝ) × (Fin 4 → ℝ) => p.2 i := fun i =>
    (continuous_apply i).comp continuous_snd
  have := hw 0; have := hw 1; have := hψ 0; have := hψ 1; have := hψ 2; have := hψ 3
  fin_cases j <;> simp [mulQuint] <;> fun_prop

/-- No zero divisors: `(w · x)² ψ = 0` with `w ≠ 0` forces `ψ = 0`. -/
theorem mulQuint_eq_zero {w : Fin 2 → ℝ} {ψ : Fin 4 → ℝ} (hw : w ≠ 0) (h : mulQuint w ψ = 0) :
    ψ = 0 := by
  have e0 : w 0 ^ 2 * ψ 0 = 0 := congrFun h 0
  have e1 : w 0 ^ 2 * ψ 1 + 2 * w 0 * w 1 * ψ 0 = 0 := congrFun h 1
  have e2 : w 0 ^ 2 * ψ 2 + 2 * w 0 * w 1 * ψ 1 + w 1 ^ 2 * ψ 0 = 0 := congrFun h 2
  have e3 : w 0 ^ 2 * ψ 3 + 2 * w 0 * w 1 * ψ 2 + w 1 ^ 2 * ψ 1 = 0 := congrFun h 3
  have e4 : 2 * w 0 * w 1 * ψ 3 + w 1 ^ 2 * ψ 2 = 0 := congrFun h 4
  have e5 : w 1 ^ 2 * ψ 3 = 0 := congrFun h 5
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1; apply hw; funext i; fin_cases i <;> simp [h0, h1]
    have q : w 1 ^ 2 ≠ 0 := pow_ne_zero 2 h1
    rw [h0] at e2 e3 e4
    have p3 : ψ 3 = 0 := (mul_eq_zero.mp e5).resolve_left q
    have p2 : ψ 2 = 0 := (mul_eq_zero.mp (by linarith : w 1 ^ 2 * ψ 2 = 0)).resolve_left q
    have p1 : ψ 1 = 0 := (mul_eq_zero.mp (by linarith : w 1 ^ 2 * ψ 1 = 0)).resolve_left q
    have p0 : ψ 0 = 0 := (mul_eq_zero.mp (by linarith : w 1 ^ 2 * ψ 0 = 0)).resolve_left q
    funext i; fin_cases i <;> simp [p0, p1, p2, p3]
  · have q : w 0 ^ 2 ≠ 0 := pow_ne_zero 2 h0
    have p0 : ψ 0 = 0 := (mul_eq_zero.mp e0).resolve_left q
    rw [p0] at e1 e2
    have p1 : ψ 1 = 0 := (mul_eq_zero.mp (by linarith : w 0 ^ 2 * ψ 1 = 0)).resolve_left q
    rw [p1] at e2 e3
    have p2 : ψ 2 = 0 := (mul_eq_zero.mp (by linarith : w 0 ^ 2 * ψ 2 = 0)).resolve_left q
    rw [p2] at e3
    have p3 : ψ 3 = 0 := (mul_eq_zero.mp (by linarith : w 0 ^ 2 * ψ 3 = 0)).resolve_left q
    funext i; fin_cases i <;> simp [p0, p1, p2, p3]

/-- **The product lower bound.** `m ‖w‖² ‖ψ‖ ≤ ‖(w · x)² ψ‖` in coefficient sup norms. -/
theorem mulQuint_lower : ∃ m : ℝ, 0 < m ∧ ∀ (w : Fin 2 → ℝ) (ψ : Fin 4 → ℝ),
    m * ‖w‖ ^ 2 * ‖ψ‖ ≤ ‖mulQuint w ψ‖ := by
  have hK : IsCompact (Metric.sphere (0 : Fin 2 → ℝ) 1 ×ˢ Metric.sphere (0 : Fin 4 → ℝ) 1) :=
    (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  have hne : (Metric.sphere (0 : Fin 2 → ℝ) 1 ×ˢ Metric.sphere (0 : Fin 4 → ℝ) 1).Nonempty := by
    refine ⟨(fun _ => 1, fun _ => 1), ?_, ?_⟩ <;> simp [pi_norm_const]
  have hf : ContinuousOn (fun p : (Fin 2 → ℝ) × (Fin 4 → ℝ) => ‖mulQuint p.1 p.2‖)
      (Metric.sphere (0 : Fin 2 → ℝ) 1 ×ˢ Metric.sphere (0 : Fin 4 → ℝ) 1) :=
    (continuous_norm.comp continuous_mulQuint).continuousOn
  obtain ⟨p₀, hp₀, hmin⟩ := hK.exists_isMinOn hne hf
  have hm : 0 < ‖mulQuint p₀.1 p₀.2‖ := by
    apply norm_pos_iff.mpr
    intro h0
    have h1 : p₀.1 ≠ 0 := by
      intro h
      have h' : ‖p₀.1‖ = 1 := mem_sphere_zero_iff_norm.mp hp₀.1
      rw [h, norm_zero] at h'
      exact zero_ne_one h'
    have h2 := mulQuint_eq_zero h1 h0
    have h' : ‖p₀.2‖ = 1 := mem_sphere_zero_iff_norm.mp hp₀.2
    rw [h2, norm_zero] at h'
    exact zero_ne_one h'
  refine ⟨‖mulQuint p₀.1 p₀.2‖, hm, fun w ψ => ?_⟩
  rcases eq_or_ne w 0 with hw | hw
  · rw [hw, norm_zero]
    have : ‖mulQuint p₀.1 p₀.2‖ * (0 : ℝ) ^ 2 * ‖ψ‖ = 0 := by ring
    rw [this]; exact norm_nonneg _
  rcases eq_or_ne ψ 0 with hψ | hψ
  · rw [hψ, norm_zero, mul_zero]; exact norm_nonneg _
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hnψ : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  have hw' : ‖w‖⁻¹ • w ∈ Metric.sphere (0 : Fin 2 → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnw.ne']
  have hψ' : ‖ψ‖⁻¹ • ψ ∈ Metric.sphere (0 : Fin 4 → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnψ.ne']
  have hle : ‖mulQuint p₀.1 p₀.2‖ ≤ ‖mulQuint (‖w‖⁻¹ • w) (‖ψ‖⁻¹ • ψ)‖ :=
    isMinOn_iff.mp hmin (‖w‖⁻¹ • w, ‖ψ‖⁻¹ • ψ) (Set.mk_mem_prod hw' hψ')
  rw [mulQuint_smul, norm_smul] at hle
  have hs : ‖(‖w‖⁻¹ ^ 2 * ‖ψ‖⁻¹ : ℝ)‖ = ‖w‖⁻¹ ^ 2 * ‖ψ‖⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hs] at hle
  have key : ‖w‖⁻¹ ^ 2 * ‖ψ‖⁻¹ * ‖mulQuint w ψ‖ * (‖w‖ ^ 2 * ‖ψ‖) = ‖mulQuint w ψ‖ := by
    field_simp
  calc ‖mulQuint p₀.1 p₀.2‖ * ‖w‖ ^ 2 * ‖ψ‖ = ‖mulQuint p₀.1 p₀.2‖ * (‖w‖ ^ 2 * ‖ψ‖) := by ring
    _ ≤ ‖w‖⁻¹ ^ 2 * ‖ψ‖⁻¹ * ‖mulQuint w ψ‖ * (‖w‖ ^ 2 * ‖ψ‖) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
    _ = ‖mulQuint w ψ‖ := key

end VectorSLT.IdentityGroup.Pairs
