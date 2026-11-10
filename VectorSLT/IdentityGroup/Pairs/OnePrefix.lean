/-
Paper 2, Appendix A.3, "a one-block prefix": Theorem `thm:invertible` at paper position two
(Lean `p = 1`): prefix `W₁`, active `W₂ = A + Δ`, suffix group `W₃, W₄`.

The prefix error is exactly `S = V_{W₁}`, a homogeneous cubic; the suffix error `Q` is kept
whole (degree `≤ 9`). With `z = x + S(x)`, `α = (Az)_k`, `β = ((A+Δ)z)_k`, `a = (Ax)_k`,
`h - F_A = (Δ_k · z)(α² + αβ + β²) + S_k(x) + (A S(x))_k (a² + aα + α²) + Q_k(F_{A+Δ}(z))`,
which is `M_η (Δ, S, Q)` with `η = (Δ, S)`, linear in `(Δ, S, Q)` and continuous in `η`, and
`M_0 (Δ', S', Q') = L_A Δ' + DF_A S' + Q' ∘ F_A`, the paper's linear part.

Injectivity (`onePrefix_kernel`): `Q' ∘ F_A` would have degree `3 deg Q' ≥ 6` if `deg Q' ≥ 2`,
while the other terms have degrees `3` and `5`; so `Q'` is affine, then `Q' = 0`; the degree-five
part `3 (Ax)^{⊙2} ⊙ A S'(x)` then forces `S' = 0`, and `L_A Δ' = 0` forces `Δ' = 0`.

The retained space is `Mat₂ × H₃² × PolyBox(9)²`, with a homogeneous cubic in `H₃ ≅ ℝ⁴` stored
by its coefficients of `x³, x²y, xy², y³` (sup norm). The rows `(W₁ k ; W₃ k, W₄ k)` give
`G₁ + G₂` (`rowBound_split` at `i = 0`).
-/
import VectorSLT.IdentityGroup.Pairs.Invertible

namespace VectorSLT.IdentityGroup.Pairs

open MeasureTheory Set Filter Topology VectorSLT MvPolynomial
open scoped Matrix

/-! ### Network facts -/

theorem prefixNet_add (W : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (m n : ℕ) (x : Fin 2 → ℝ) :
    prefixNet W (m + n) x = prefixNet (fun i => W (i + m)) n (prefixNet W m x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← add_assoc, prefixNet_succ, Function.comp_apply, ih, prefixNet_succ,
      Function.comp_apply, add_comm n m]

/-- A binary cubic form from its coefficients of `x³, x²y, xy², y³`. -/
def cub (c : Fin 4 → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  c 0 * x 0 ^ 3 + c 1 * x 0 ^ 2 * x 1 + c 2 * x 0 * x 1 ^ 2 + c 3 * x 1 ^ 3

/-- A vector of binary cubic forms. -/
def cubV (S : Fin 2 → Fin 4 → ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => cub (S i) x

/-- The coefficients of `(w · x)³`. -/
def cubeCoeffs (w : Fin 2 → ℝ) : Fin 4 → ℝ :=
  ![w 0 ^ 3, 3 * w 0 ^ 2 * w 1, 3 * w 0 * w 1 ^ 2, w 1 ^ 3]

theorem cub_cubeCoeffs (w x : Fin 2 → ℝ) : cub (cubeCoeffs w) x = (w ⬝ᵥ x) ^ 3 := by
  simp [cub, cubeCoeffs]; ring

theorem cub_smul (c : Fin 4 → ℝ) (s : ℝ) (x : Fin 2 → ℝ) : cub c (s • x) = s ^ 3 * cub c x := by
  simp only [cub, Pi.smul_apply, smul_eq_mul]; ring

theorem continuous_cub_joint {X' : Type*} [TopologicalSpace X'] {c : X' → Fin 4 → ℝ}
    (hc : Continuous c) {x : X' → Fin 2 → ℝ} (hx : Continuous x) :
    Continuous fun q => cub (c q) (x q) := by
  have hc' : ∀ j, Continuous fun q => c q j := fun j => (continuous_apply j).comp hc
  have hx' : ∀ j, Continuous fun q => x q j := fun j => (continuous_apply j).comp hx
  simp only [cub]
  have := hc' 0; have := hc' 1; have := hc' 2; have := hc' 3
  have := hx' 0; have := hx' 1
  fun_prop

/-- `cub c` as a polynomial. -/
noncomputable def cubPoly (c : Fin 4 → ℝ) : MvPolynomial (Fin 2) ℝ :=
  C (c 0) * X 0 ^ 3 + C (c 1) * X 0 ^ 2 * X 1 + C (c 2) * X 0 * X 1 ^ 2 + C (c 3) * X 1 ^ 3

theorem eval_cubPoly (c : Fin 4 → ℝ) (x : Fin 2 → ℝ) : eval x (cubPoly c) = cub c x := by
  simp [cubPoly, cub]

theorem cub_eq_zero {c : Fin 4 → ℝ} (h : ∀ x, cub c x = 0) : c = 0 := by
  have h0 := h ![1, 0]
  have h1 := h ![0, 1]
  have h2 := h ![1, 1]
  have h3 := h ![1, -1]
  simp [cub] at h0 h1 h2 h3
  funext j
  fin_cases j <;> simp <;> linarith

/-! ### The error map -/

/-- Retained variables at Lean position one: `(Δ, S, Q) ∈ Mat₂ × H₃² × PolyBox(9)²`. -/
abbrev OneDom : Type := (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) × (Fin 2 → PolyBox (3 ^ 2))

/-- Parameters of the error map: `η = (Δ, S)`. -/
abbrev OnePar : Type := (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ)

noncomputable def M1fun (A : Matrix (Fin 2) (Fin 2) ℝ) (η : OnePar) (v : OneDom)
    (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun k =>
  let z := x + cubV η.2 x
  let α := (A *ᵥ z) k
  let β := ((A + Matrix.of η.1) *ᵥ z) k
  let a := (A *ᵥ x) k
  (v.1 k ⬝ᵥ z) * (α ^ 2 + α * β + β ^ 2) + cubV v.2.1 x k +
    (A *ᵥ cubV v.2.1 x) k * (a ^ 2 + a * α + α ^ 2) +
    eval (layer (A + Matrix.of η.1) z) (v.2.2 k).poly

theorem continuous_M1fun (A : Matrix (Fin 2) (Fin 2) ℝ) (v : OneDom) :
    Continuous fun q : OnePar × (Fin 2 → ℝ) => M1fun A q.1 v q.2 := by
  refine continuous_pi fun k => ?_
  have hz : Continuous fun q : OnePar × (Fin 2 → ℝ) => q.2 + cubV q.1.2 q.2 :=
    continuous_snd.add (continuous_pi fun i => continuous_cub_joint
      ((continuous_apply i).comp (continuous_snd.comp continuous_fst)) continuous_snd)
  have hz0 : Continuous fun q : OnePar × (Fin 2 → ℝ) => (q.2 + cubV q.1.2 q.2) 0 :=
    (continuous_apply 0).comp hz
  have hz1 : Continuous fun q : OnePar × (Fin 2 → ℝ) => (q.2 + cubV q.1.2 q.2) 1 :=
    (continuous_apply 1).comp hz
  have hD : ∀ i j, Continuous fun q : OnePar × (Fin 2 → ℝ) => q.1.1 i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_fst.comp continuous_fst))
  have hS : ∀ i, Continuous fun q : OnePar × (Fin 2 → ℝ) => cubV v.2.1 q.2 i := fun i =>
    continuous_cub_joint continuous_const continuous_snd
  have hx0 : Continuous fun q : OnePar × (Fin 2 → ℝ) => q.2 0 :=
    (continuous_apply 0).comp continuous_snd
  have hx1 : Continuous fun q : OnePar × (Fin 2 → ℝ) => q.2 1 :=
    (continuous_apply 1).comp continuous_snd
  have hB : ∀ i j, Continuous fun q : OnePar × (Fin 2 → ℝ) => (A + Matrix.of q.1.1) i j := by
    intro i j; simp only [Matrix.add_apply, Matrix.of_apply]; exact continuous_const.add (hD i j)
  have hL := continuous_layer_joint hB hz
  have hE : Continuous fun q : OnePar × (Fin 2 → ℝ) =>
      eval (layer (A + Matrix.of q.1.1) (q.2 + cubV q.1.2 q.2)) (v.2.2 k).poly :=
    (continuous_eval _).comp hL
  simp only [M1fun]
  refine Continuous.add ?_ hE
  simp only [mulVec_two, dot_two, Matrix.add_apply, Matrix.of_apply]
  have hk0 := hD k 0
  have hk1 := hD k 1
  have hS0 := hS 0
  have hS1 := hS 1
  have hSk := hS k
  fun_prop

/-- `M_η` as a linear map into `C([-1,1]², ℝ²)`. -/
noncomputable def M1 (A : Matrix (Fin 2) (Fin 2) ℝ) (η : OnePar) :
    OneDom →ₗ[ℝ] C(ubox, Fin 2 → ℝ) where
  toFun v := ⟨fun x => M1fun A η v x.1,
    (continuous_M1fun A v).comp (continuous_const.prodMk continuous_subtype_val)⟩
  map_add' v w := by
    ext x k
    simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply, Pi.add_apply, M1fun, cubV, cub,
      Prod.fst_add, Prod.snd_add, PolyBox.poly_add, map_add, add_dotProduct,
      mulVec_two]
    ring
  map_smul' c v := by
    ext x k
    simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, Pi.smul_apply, M1fun, cubV, cub,
      Prod.smul_fst, Prod.smul_snd, PolyBox.poly_smul, smul_eval,
      smul_dotProduct, smul_eq_mul, RingHom.id_apply, mulVec_two]
    ring

theorem M1_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (η : OnePar) (v : OneDom) (x : ubox) (k : Fin 2) :
    M1 A η v x k = M1fun A η v x.1 k := rfl

/-- The retained variables of `θ` at Lean position one. -/
noncomputable def vOne (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) : OneDom :=
  (fun i j => weights θ 1 i j - A i j, fun k => cubeCoeffs (weights θ 0 k),
    fun k => grpErr (fun i => weights θ (i + 2)) 2 k)

/-- The parameters of the error map at `θ`. -/
noncomputable def ηOne (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) : OnePar :=
  ((vOne A θ).1, (vOne A θ).2.1)

/-- **The error map is exact.** -/
theorem errBox_eq_M1 (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) :
    errBox A θ = M1 A (ηOne A θ) (vOne A θ) := by
  ext x k
  rw [errBox_apply, M1_apply]
  set W := weights θ
  have hz : x.1 + cubV (ηOne A θ).2 x.1 = layer (W 0) x.1 := by
    funext i
    simp only [Pi.add_apply, cubV, ηOne, vOne, cub_cubeCoeffs, layer_apply]
    rfl
  have hA : A + Matrix.of (ηOne A θ).1 = W 1 := by ext i j; simp [ηOne, vOne, W]
  have hnet : net θ x.1 = layer (W 1) (layer (W 0) x.1) +
      evalV (fun k => grpErr (fun i => W (i + 2)) 2 k) (layer (W 1) (layer (W 0) x.1)) := by
    funext i
    simp only [Pi.add_apply, evalV, eval_grpErr]
    rw [net, show (4 : ℕ) = 2 + 2 from rfl, prefixNet_add]
    simp only [prefixNet_succ, prefixNet_zero, Function.comp_apply, id]
    ring
  simp only [M1fun]
  rw [hz, hA, hnet]
  have hS : ∀ i, cubV (vOne A θ).2.1 x.1 i = layer (W 0) x.1 i - x.1 i := by
    intro i; simp only [cubV, vOne, cub_cubeCoeffs, layer_apply]; ring
  simp only [Pi.add_apply, evalV]
  rw [layer_apply' (W 1), layer_apply' A, mulVec_two, mulVec_two, mulVec_two, mulVec_two,
    dot_two]
  simp only [hS]
  simp only [vOne, W]
  ring

theorem continuous_ηOne (A : Matrix (Fin 2) (Fin 2) ℝ) : Continuous (ηOne A) := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_pi fun i => continuous_pi fun j =>
      (continuous_weights 1 i j).sub continuous_const
  · refine continuous_pi fun k => continuous_pi fun j => ?_
    simp only [vOne, cubeCoeffs]
    have h0 := continuous_weights 0 k 0
    have h1 := continuous_weights 0 k 1
    fin_cases j <;> simp <;> fun_prop

theorem ηOne_base (A : Matrix (Fin 2) (Fin 2) ℝ) : ηOne A (basePos A 1) = 0 := by
  refine Prod.ext ?_ ?_
  · funext i j; simp [ηOne, vOne, weights_basePos A 1 1 (by norm_num)]
  · funext k j
    simp only [ηOne, vOne, weights_basePos A 1 0 (by norm_num)]
    fin_cases j <;> simp [cubeCoeffs]

/-- **Absorption at Lean position one.** -/
theorem one_absorb (A : Matrix (Fin 2) (Fin 2) ℝ) (hinj : Function.Injective (M1 A 0)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ θ, ‖θ - basePos A 1‖ < r₀ →
      c₀ * ‖vOne A θ‖ ≤ ‖errBox A θ‖ := by
  have hcont : ∀ v : OneDom, Continuous fun η : OnePar => M1 A η v := by
    intro v
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_M1fun A v).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  obtain ⟨c₀, hc₀, hev⟩ := uniform_lower_of_linear (X := OnePar) (x₀ := 0)
    (fun η : OnePar => M1 A η) hcont hinj
  have hev' : ∀ᶠ θ in 𝓝 (basePos A 1), ∀ v, c₀ * ‖v‖ ≤ ‖M1 A (ηOne A θ) v‖ := by
    have ht : Tendsto (ηOne A) (𝓝 (basePos A 1)) (𝓝 0) := by
      have := (continuous_ηOne A).tendsto (basePos A 1)
      rwa [ηOne_base] at this
    exact ht.eventually hev
  obtain ⟨r₀, hr₀, hr⟩ := Metric.eventually_nhds_iff.mp hev'
  refine ⟨r₀, hr₀, c₀, hc₀, fun θ hθ => ?_⟩
  rw [errBox_eq_M1]
  exact hr (by rwa [dist_eq_norm]) _

/-! ### Injectivity for invertible `A` -/

theorem M1_kernel (A : Matrix (Fin 2) (Fin 2) ℝ) {v : OneDom} (hv : M1 A 0 v = 0) (k : Fin 2)
    (x : Fin 2 → ℝ) :
    (v.1 k ⬝ᵥ x) * (3 * (A *ᵥ x) k ^ 2) + cub (v.2.1 k) x +
      3 * (A *ᵥ x) k ^ 2 * (A k 0 * cub (v.2.1 0) x + A k 1 * cub (v.2.1 1) x) +
      eval (layer A x) (v.2.2 k).poly = 0 := by
  set q : MvPolynomial (Fin 2) ℝ :=
    (C (v.1 k 0) * X 0 + C (v.1 k 1) * X 1) * (3 * (C (A k 0) * X 0 + C (A k 1) * X 1) ^ 2) +
      cubPoly (v.2.1 k) + 3 * (C (A k 0) * X 0 + C (A k 1) * X 1) ^ 2 *
        (C (A k 0) * cubPoly (v.2.1 0) + C (A k 1) * cubPoly (v.2.1 1)) +
      bind₁ (layerPoly A) (v.2.2 k).poly
  have hq : ∀ y : Fin 2 → ℝ, eval y q = (v.1 k ⬝ᵥ y) * (3 * (A *ᵥ y) k ^ 2) +
      cub (v.2.1 k) y + 3 * (A *ᵥ y) k ^ 2 *
        (A k 0 * cub (v.2.1 0) y + A k 1 * cub (v.2.1 1) y) +
      eval (layer A y) (v.2.2 k).poly := by
    intro y
    simp only [q, map_add, map_mul, map_pow, eval_C, eval_X, dot_two, mulVec_two, eval_bind₁_eq,
      eval_layerPoly, eval_cubPoly]
    norm_num
  rw [← hq]
  refine eval_eq_zero_of_box (fun y => ?_) x
  have h := congrArg (fun f : C(ubox, Fin 2 → ℝ) => f y k) hv
  simp only [M1_apply, M1fun, ContinuousMap.zero_apply, Pi.zero_apply, Prod.fst_zero,
    Prod.snd_zero] at h
  have h0 : cubV (0 : Fin 2 → Fin 4 → ℝ) y.1 = 0 := by
    funext i; simp [cubV, cub]
  rw [h0, add_zero, show A + Matrix.of (0 : Fin 2 → Fin 2 → ℝ) = A by ext; simp] at h
  rw [hq, ← h]
  simp only [cubV, mulVec_two]
  ring

/-- **Injectivity of `L_A Δ + DF_A S + Q ∘ F_A`** on `Mat₂ × H₃² × PolyBox(9)²`, `det A ≠ 0`. -/
theorem onePrefix_injective {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) :
    Function.Injective (M1 A 0) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  have hk := M1_kernel A hw
  have hhom : ∀ i (s : ℝ) (y : Fin 2 → ℝ), cub (w.2.1 i) (s • y) = s ^ 3 * cub (w.2.1 i) y :=
    fun i s y => cub_smul _ s y
  -- the suffix error vanishes
  have hQ : ∀ k, (w.2.2 k).poly = 0 := by
    intro k
    refine eq_zero_of_layer_odd hA fun y => ⟨-(3 * (w.1 k ⬝ᵥ y) * (A *ᵥ y) k ^ 2 +
      cub (w.2.1 k) y), -(3 * (A *ᵥ y) k ^ 2 *
        (A k 0 * cub (w.2.1 0) y + A k 1 * cub (w.2.1 1) y)), fun s => ?_⟩
    have := hk k (s • y)
    rw [mulVec_smul_apply, dotProduct_smul, smul_eq_mul, hhom, hhom, hhom] at this
    linear_combination this
  -- the degree-five part forces `S = 0`
  have h5 : ∀ y : Fin 2 → ℝ, ∀ k, (A *ᵥ y) k ^ 2 *
      (A k 0 * cub (w.2.1 0) y + A k 1 * cub (w.2.1 1) y) = 0 := by
    intro y k
    have hs : ∀ s : ℝ, 0 * s + (3 * (w.1 k ⬝ᵥ y) * (A *ᵥ y) k ^ 2 + cub (w.2.1 k) y) *
        s ^ 3 + (3 * (A *ᵥ y) k ^ 2 *
          (A k 0 * cub (w.2.1 0) y + A k 1 * cub (w.2.1 1) y)) * s ^ 5 = 0 := by
      intro s
      have := hk k (s • y)
      rw [mulVec_smul_apply, dotProduct_smul, smul_eq_mul, hhom, hhom, hhom, hQ k,
        map_zero, add_zero] at this
      linear_combination this
    have := (odd_poly_zero hs).2.2
    linarith
  have hS : ∀ k, w.2.1 k = 0 := by
    have hf : Continuous fun y : Fin 2 → ℝ => fun k => cub (w.2.1 k) y :=
      continuous_pi fun k => continuous_cub_joint continuous_const continuous_id
    have h0 := vanish_of_dense hA hf fun y hy0 hy1 => by
      apply mulVec_inj_of_det hA
      funext k
      rw [mulVec_two]
      have hk' : (A *ᵥ y) k ≠ 0 := by fin_cases k; exacts [hy0, hy1]
      have := h5 y k
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hk')
    intro k
    exact cub_eq_zero fun y => congrFun (congrFun h0 y) k
  -- and `L_A Δ = 0` forces `Δ = 0`
  have hΔ : w.1 = 0 := by
    funext k
    refine lin_mul_sq_zero (row_ne_zero hA k) fun x => ?_
    have := hk k x
    rw [hS k, hS 0, hS 1, hQ k] at this
    simp only [cub, Pi.zero_apply, map_zero, add_zero, mul_zero, zero_mul] at this
    have e : (A *ᵥ x) k = A k ⬝ᵥ x := rfl
    rw [e] at this
    linear_combination this / 3
  exact Prod.ext hΔ (Prod.ext (funext hS) (funext fun k => Subtype.ext (hQ k)))

/-! ### The comparison and the upper bound -/

/-- The row functional at Lean position one: a one-block prefix and a two-block suffix. -/
noncomputable def gOne (u : Fin 3 → ℝ × ℝ) : ℝ :=
  cubeSumSq (fun _ : Fin 1 => u 0) + cubeSumSq (fun j : Fin 2 => u ((0 : Fin 3).succAbove j))

/-- `G₁` of one form is bounded by the squared coefficient norm of its cube. -/
theorem cubeSumSq_one_le (w : Fin 2 → ℝ) :
    cubeSumSq (fun _ : Fin 1 => (w 0, w 1)) ≤ 4 * ‖cubeCoeffs w‖ ^ 2 := by
  have hc : ∀ j, cubeCoeffs w j ^ 2 ≤ ‖cubeCoeffs w‖ ^ 2 := by
    intro j
    rw [← sq_abs, ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm _ j) 2
  have h0 : (w 0 ^ 3) ^ 2 ≤ ‖cubeCoeffs w‖ ^ 2 := hc 0
  have h1 : (3 * w 0 ^ 2 * w 1) ^ 2 ≤ ‖cubeCoeffs w‖ ^ 2 := hc 1
  have h2 : (3 * w 0 * w 1 ^ 2) ^ 2 ≤ ‖cubeCoeffs w‖ ^ 2 := hc 2
  have h3 : (w 1 ^ 3) ^ 2 ≤ ‖cubeCoeffs w‖ ^ 2 := hc 3
  have e : cubeSumSq (fun _ : Fin 1 => (w 0, w 1)) =
      (w 0 ^ 3) ^ 2 + (w 0 ^ 2 * w 1) ^ 2 + (w 0 * w 1 ^ 2) ^ 2 + (w 1 ^ 3) ^ 2 := by
    simp [cubeSumSq, cubeSum, Fin.sum_univ_four]
  rw [e]
  nlinarith [sq_nonneg (w 0 ^ 2 * w 1), sq_nonneg (w 0 * w 1 ^ 2)]

theorem one_compare (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ Cq : ℝ, ∀ θ, actSq A (Sfun 1 θ).1 + gOne (rowU (Sfun 1 θ).2.1) +
      gOne (rowU (Sfun 1 θ).2.2) ≤ Cq * ‖vOne A θ‖ ^ 2 := by
  obtain ⟨C₂, hC₂, hG₂⟩ := cubeSumSq_le_grpErr 2
  refine ⟨12 + 2 * C₂, fun θ => ?_⟩
  set v := vOne A θ
  have hΔ : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have hS : ∀ k, ‖v.2.1 k‖ ≤ ‖v‖ := fun k =>
    (norm_le_pi_norm v.2.1 k).trans ((norm_fst_le v.2).trans (norm_snd_le v))
  have hQ : ∀ k, ‖v.2.2 k‖ ≤ ‖v‖ := fun k =>
    (norm_le_pi_norm v.2.2 k).trans ((norm_snd_le v.2).trans (norm_snd_le v))
  have hact : actSq A (Sfun 1 θ).1 ≤ 4 * ‖v‖ ^ 2 := by
    rw [actSq_Sfun]
    refine (sum_sq_le_norm v.1).trans ?_
    have := pow_le_pow_left₀ (norm_nonneg _) hΔ 2
    linarith
  have hrow : ∀ k : Fin 2, gOne (rowU (![(Sfun 1 θ).2.1, (Sfun 1 θ).2.2] k)) ≤
      (4 + C₂) * ‖v‖ ^ 2 := by
    intro k
    rw [rowU_Sfun]
    have e1 : (fun _ : Fin 1 => (weights θ (inact 1 0) k 0, weights θ (inact 1 0) k 1)) =
        fun _ : Fin 1 => (weights θ 0 k 0, weights θ 0 k 1) := rfl
    have e2 : (fun j : Fin 2 => (weights θ (inact 1 ((0 : Fin 3).succAbove j)) k 0,
        weights θ (inact 1 ((0 : Fin 3).succAbove j)) k 1)) =
        grpRow (fun i => weights θ (i + 2)) 2 k := by
      funext j; fin_cases j <;> rfl
    simp only [gOne]
    rw [e1, e2]
    have g1 := cubeSumSq_one_le (weights θ 0 k)
    have g2 := hG₂ (fun i => weights θ (i + 2)) k
    have n1 := pow_le_pow_left₀ (norm_nonneg _) (hS k) 2
    have n2 := pow_le_pow_left₀ (norm_nonneg _) (hQ k) 2
    have e3 : ‖grpErr (fun i => weights θ (i + 2)) 2 k‖ = ‖v.2.2 k‖ := rfl
    have e4 : ‖cubeCoeffs (weights θ 0 k)‖ = ‖v.2.1 k‖ := rfl
    rw [e3] at g2
    rw [e4] at g1
    nlinarith
  have h0 := hrow 0
  have h1 := hrow 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  linarith

theorem measurable_gOne : Measurable gOne := by
  unfold gOne
  exact (((continuous_cubeSumSq 1).comp (continuous_pi fun _ => continuous_apply 0)).add
    ((continuous_cubeSumSq 2).comp (continuous_pi fun _ => continuous_apply _))).measurable

/-- **Theorem "invertible active blocks", paper position two (Lean `p = 1`), upper half**, from
`CubeSumUpper 1` and `CubeSumUpper 2`. -/
theorem invertible_two_upper {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0)
    (h1 : CubeSumUpper 1) (h2 : CubeSumUpper 2) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → Zpos μ A φ χ 1 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4) := by
  obtain ⟨r₀, hr₀, c₀, hc₀, habs⟩ := one_absorb A (onePrefix_injective hA)
  obtain ⟨Cq, hq⟩ := one_compare A
  exact upper_of_absorb A 1 (g := gOne) (fun r hr => rowBound_split h1 h2 hr 0)
    measurable_gOne (vOne A) hr₀ hc₀ habs hq

/-- **Theorem "invertible active blocks", paper position two: the pair `(4, 1)`**, from
`CubeSumUpper 1` and `CubeSumUpper 2`, with the certified lower bound `Zpos_lower_N4`. -/
theorem invertible_two_pair {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0)
    (h1 : CubeSumUpper 1) (h2 : CubeSumUpper 2) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ᶠ θ in 𝓝 (basePos A 1), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      VectorSLT.SLT.HasLaplacePair (Zpos μ A φ χ 1) 4 1 :=
  pair_of_upper A 1 (invertible_two_upper hA h1 h2)

end VectorSLT.IdentityGroup.Pairs
