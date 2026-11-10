/-
Paper 2, Proposition `prop:nonshear` (Appendix F): non-shear rank one at position one.

For `A = a vᵀ` with `a₀ a₁ ≠ 0` and `α = v · a^{⊙3} ≠ 0`, Lemma F1 says that the derivative
`𝒟(Δ, P) = L_A Δ + P ∘ F_A` is injective. The proof here is the paper's: put `w = a^{⊙3}/α`
and `z = (-v₁, v₀)`, so that `ℓ(w) = 1`, `ℓ(z) = 0` (`ℓ = v · x`) and
`F_A(σ w + t z) = (σ + α σ³) w + t z`. For fixed `t`, the univariate polynomial
`g(σ) = P_k(σ w + t z)` satisfies `g(s + α s³) = -3 a_k² s² (s δ·w + t δ·z)`, where `δ = Δ_k`.
A degree count (`natDegree (g ∘ (X + α X³)) = 3 · natDegree g ≤ 3`) gives `g = c₁ σ + c₀`, and
comparing coefficients gives `c₀ = c₁ = 0`, `δ·w = 0` and `δ·z = 0`. So `P_k = 0` and `Δ_k = 0`.
The paper's change of input coordinates `T = (ℓ, m)` is the basis `(w, z)` here.

With the first-position machinery (FirstPosition.lean) this gives `Z_N ≤ C N⁻⁴` from
`CubeSumUpper 3`, and with the certified `Zpos_lower_N4` the pair `(4, 1)`.
-/
import VectorSLT.IdentityGroup.Pairs.FirstPosition

namespace VectorSLT.IdentityGroup.Pairs

open MeasureTheory Set Filter Topology VectorSLT MvPolynomial
open scoped Matrix

/-- **A non-shear rank-one target**: `A = a vᵀ` with both rows nonzero and `v · a^{⊙3} ≠ 0`.
(Compare `ShearTarget`, where `v · a^{⊙3} = 0`.) -/
def NonShearTarget (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ a v : Fin 2 → ℝ, (∀ i j, A i j = a i * v j) ∧ a 0 ≠ 0 ∧ a 1 ≠ 0 ∧
    v 0 * a 0 ^ 3 + v 1 * a 1 ^ 3 ≠ 0

/-- `p ↦ (σ ↦ p(σ w + t z))`, as a univariate polynomial. -/
noncomputable def lineHom (w z : Fin 2 → ℝ) (t : ℝ) :
    MvPolynomial (Fin 2) ℝ →ₐ[ℝ] Polynomial ℝ :=
  aeval fun i => Polynomial.C (w i) * Polynomial.X + Polynomial.C (t * z i)

theorem eval_lineHom (w z : Fin 2 → ℝ) (t : ℝ) (p : MvPolynomial (Fin 2) ℝ) (σ : ℝ) :
    (lineHom w z t p).eval σ = eval (σ • w + t • z) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [lineHom]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, Polynomial.eval_mul, hp, map_mul, eval_X]
    simp only [lineHom, aeval_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- The one-variable step of Lemma F1: if `g(s + α s³) = c s³ + e s²` with `α ≠ 0`, then
`g = 0` and `c = e = 0`. -/
theorem comp_cubic_eq {α c e : ℝ} (hα : α ≠ 0) {g : Polynomial ℝ}
    (h : ∀ s : ℝ, g.eval (s + α * s ^ 3) = c * s ^ 3 + e * s ^ 2) :
    g = 0 ∧ c = 0 ∧ e = 0 := by
  set q : Polynomial ℝ := Polynomial.X + Polynomial.C α * Polynomial.X ^ 3
  have hpoly : g.comp q = Polynomial.C c * Polynomial.X ^ 3 + Polynomial.C e * Polynomial.X ^ 2 := by
    apply Polynomial.funext; intro s
    simp only [Polynomial.eval_comp, q, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow]
    exact h s
  have hq : q.natDegree = 3 := by
    simp only [q]
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt] <;>
      rw [Polynomial.natDegree_C_mul_X_pow 3 α hα]
    simp
  have hdeg : g.natDegree ≤ 1 := by
    have h1 : (g.comp q).natDegree = g.natDegree * 3 := by rw [Polynomial.natDegree_comp, hq]
    have h2 : (Polynomial.C c * Polynomial.X ^ 3 + Polynomial.C e * Polynomial.X ^ 2 :
        Polynomial ℝ).natDegree ≤ 3 := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact Polynomial.natDegree_C_mul_X_pow_le c 3
      · exact (Polynomial.natDegree_C_mul_X_pow_le e 2).trans (by norm_num)
    rw [← hpoly, h1] at h2
    omega
  have hg := Polynomial.eq_X_add_C_of_natDegree_le_one hdeg
  set c₁ := g.coeff 1
  set c₀ := g.coeff 0
  rw [hg] at hpoly
  have hc : ∀ n : ℕ, (Polynomial.C c₁ * q + Polynomial.C c₀).coeff n =
      (Polynomial.C c * Polynomial.X ^ 3 + Polynomial.C e * Polynomial.X ^ 2).coeff n := by
    intro n
    rw [← hpoly]
    simp [Polynomial.add_comp, Polynomial.mul_comp]
  have e0 := hc 0
  have e1 := hc 1
  have e2 := hc 2
  have e3 := hc 3
  simp only [q, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X,
    Polynomial.coeff_X_pow, Polynomial.coeff_C] at e0 e1 e2 e3
  norm_num at e0 e1 e2 e3
  have h1 : c₁ = 0 := e1
  have h0 : c₀ = 0 := e0
  refine ⟨?_, ?_, ?_⟩
  · rw [hg, h1, h0]; simp
  · rw [← e3, h1, zero_mul]
  · exact e2.symm

/-- Every point of the plane is `ℓ(y) w + τ z`, for `ℓ(w) = 1` and `z = (-v₁, v₀)`. -/
theorem decomp2 {v w : Fin 2 → ℝ} (hw : v 0 * w 0 + v 1 * w 1 = 1)
    (hv2 : v 0 ^ 2 + v 1 ^ 2 ≠ 0) (y : Fin 2 → ℝ) :
    y = (v 0 * y 0 + v 1 * y 1) • w + ((-v 1 * (y 0 - (v 0 * y 0 + v 1 * y 1) * w 0) +
      v 0 * (y 1 - (v 0 * y 0 + v 1 * y 1) * w 1)) / (v 0 ^ 2 + v 1 ^ 2)) • ![-v 1, v 0] := by
  funext i
  fin_cases i <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    field_simp
  · linear_combination (-(v 0 * y 0 + v 1 * y 1) * v 0) * hw
  · linear_combination (-(v 0 * y 0 + v 1 * y 1) * v 1) * hw

/-- **Lemma F1, one output row.** For `A = a vᵀ` with `α = v · a^{⊙3} ≠ 0` and `a_k ≠ 0`: if
`(δ · x) · 3 (a_k ℓ(x))² + Q(F_A x) = 0` for all `x`, with `ℓ = v · x`, then `δ = 0` and `Q = 0`. -/
theorem nonshear_kernel {a v : Fin 2 → ℝ} (hα : v 0 * a 0 ^ 3 + v 1 * a 1 ^ 3 ≠ 0) {k : Fin 2}
    (hk : a k ≠ 0) {δ : Fin 2 → ℝ} {Q : MvPolynomial (Fin 2) ℝ}
    (h : ∀ x : Fin 2 → ℝ, (δ ⬝ᵥ x) * (3 * (a k * (v ⬝ᵥ x)) ^ 2) +
      eval (fun i => x i + a i ^ 3 * (v ⬝ᵥ x) ^ 3) Q = 0) : δ = 0 ∧ Q = 0 := by
  set α := v 0 * a 0 ^ 3 + v 1 * a 1 ^ 3
  set w : Fin 2 → ℝ := fun i => a i ^ 3 / α
  set z : Fin 2 → ℝ := ![-v 1, v 0]
  have hw : v ⬝ᵥ w = 1 := by
    rw [dot_two]
    show v 0 * (a 0 ^ 3 / α) + v 1 * (a 1 ^ 3 / α) = 1
    rw [← div_self hα]; ring
  have hz : v ⬝ᵥ z = 0 := by rw [dot_two]; simp [z]; ring
  have hv2 : v 0 ^ 2 + v 1 ^ 2 ≠ 0 := by
    intro h0
    have h0' : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have h1' : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    apply hα; show v 0 * a 0 ^ 3 + v 1 * a 1 ^ 3 = 0; rw [h0', h1']; ring
  -- the kernel equation along the line `σ w + t z`
  have hline : ∀ σ t : ℝ, eval ((σ + α * σ ^ 3) • w + t • z) Q =
      (-(3 * a k ^ 2 * (δ ⬝ᵥ w))) * σ ^ 3 + (-(3 * a k ^ 2 * t * (δ ⬝ᵥ z))) * σ ^ 2 := by
    intro σ t
    have hx := h (σ • w + t • z)
    have hl : v ⬝ᵥ (σ • w + t • z) = σ := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, hw, hz]; simp
    have hF : (fun i => (σ • w + t • z) i + a i ^ 3 * (v ⬝ᵥ (σ • w + t • z)) ^ 3) =
        (σ + α * σ ^ 3) • w + t • z := by
      funext i
      rw [hl]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w]
      field_simp
      ring
    rw [hF, hl, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul] at hx
    linear_combination hx
  have hstep : ∀ t : ℝ, (∀ σ : ℝ, eval (σ • w + t • z) Q = 0) ∧ δ ⬝ᵥ w = 0 ∧ t * (δ ⬝ᵥ z) = 0 := by
    intro t
    have hg : ∀ s : ℝ, (lineHom w z t Q).eval (s + α * s ^ 3) =
        (-(3 * a k ^ 2 * (δ ⬝ᵥ w))) * s ^ 3 + (-(3 * a k ^ 2 * t * (δ ⬝ᵥ z))) * s ^ 2 := by
      intro s; rw [eval_lineHom]; exact hline s t
    obtain ⟨h0, hc, he⟩ := comp_cubic_eq hα hg
    have hak : 3 * a k ^ 2 ≠ 0 := by positivity
    refine ⟨fun σ => ?_, ?_, ?_⟩
    · rw [← eval_lineHom, h0, Polynomial.eval_zero]
    · have : 3 * a k ^ 2 * (δ ⬝ᵥ w) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hak
    · have : 3 * a k ^ 2 * (t * (δ ⬝ᵥ z)) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hak
  -- every point is on such a line
  have hdec : ∀ y : Fin 2 → ℝ, y = (v ⬝ᵥ y) • w + ((-v 1 * (y 0 - (v ⬝ᵥ y) * w 0) +
      v 0 * (y 1 - (v ⬝ᵥ y) * w 1)) / (v 0 ^ 2 + v 1 ^ 2)) • z := by
    intro y
    have hw' : v 0 * w 0 + v 1 * w 1 = 1 := by rw [← dot_two]; exact hw
    rw [dot_two]
    exact decomp2 hw' hv2 y
  have hδz : δ ⬝ᵥ z = 0 := by simpa using (hstep 1).2.2
  have hδw : δ ⬝ᵥ w = 0 := (hstep 0).2.1
  constructor
  · have hall : ∀ y, δ ⬝ᵥ y = 0 := by
      intro y
      rw [hdec y, dotProduct_add, dotProduct_smul, dotProduct_smul, hδw, hδz]; simp
    funext i
    have := hall (Pi.single i 1)
    simpa [dotProduct_single] using this
  · apply MvPolynomial.funext; intro y
    rw [hdec y, (hstep _).1, map_zero]

theorem polyBox_ext {d : ℕ} {p q : PolyBox d} (h : p.poly = q.poly) : p = q := Subtype.ext h

/-- **Lemma F1 (injectivity).** For a non-shear rank-one target, `𝒟(Δ, P) = L_A Δ + P ∘ F_A` is
injective on `Mat₂ × PolyBox(27)²` (restricted to the box `[-1,1]²`). -/
theorem nonshear_injective {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : NonShearTarget A) :
    Function.Injective (M0 A 0 (3 ^ 3)) := by
  obtain ⟨a, v, hAav, ha0, ha1, hα⟩ := hA
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  have hrow : ∀ k, w.1 k = 0 ∧ (w.2 k).poly = 0 := by
    intro k
    have hak : a k ≠ 0 := by fin_cases k; exacts [ha0, ha1]
    refine nonshear_kernel hα hak fun x => ?_
    have h := M0_kernel A hw k x
    have hAx : ∀ i, (A *ᵥ x) i = a i * (v ⬝ᵥ x) := by
      intro i; rw [mulVec_two, dot_two, hAav, hAav]; ring
    have hL : layer A x = fun i => x i + a i ^ 3 * (v ⬝ᵥ x) ^ 3 := by
      funext i; rw [layer_apply, show A i ⬝ᵥ x = (A *ᵥ x) i from rfl, hAx]; ring
    rw [hAx, hL] at h
    exact h
  refine Prod.ext (funext fun k => (hrow k).1) (funext fun k => polyBox_ext ?_)
  exact (hrow k).2

/-- **Proposition "non-shear rank one", upper half.** For `A = a vᵀ` with `a₀ a₁ ≠ 0` and
`v · a^{⊙3} ≠ 0`, at position one (Lean `p = 0`), assuming `CubeSumUpper 3`: there is a radius
`r(A) > 0` such that for every input law with finite 162nd moments and a density bounded below on a
box, every prior bounded by `π₁` and every cutoff bounded by `1` vanishing outside the sup-norm
`r`-ball, `Z_N ≤ C N⁻⁴` for large `N`. -/
theorem nonshear_upper {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : NonShearTarget A)
    (h3 : CubeSumUpper 3) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → Zpos μ A φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4) :=
  first_upper (nonshear_injective hA) h3

/-- **Proposition "non-shear rank one": the pair `(4, 1)` at position one**, from
`CubeSumUpper 3`, with the certified lower bound `Zpos_lower_N4`. -/
theorem nonshear_pair {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : NonShearTarget A)
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
  pair_of_upper A 0 (nonshear_upper hA h3)

end VectorSLT.IdentityGroup.Pairs
