/-
Paper 2, active block first (Lean `p = 0`), with the three inactive blocks kept as one group
(Appendix F, "The error map", and Appendix A.3, the case "active block first").

With `W₁ = A + Δ` and `H = F_{W₄} ∘ F_{W₃} ∘ F_{W₂} = I + P`, the error is exactly
`h - F_A = [F_{A+Δ} - F_A] + P ∘ F_{A+Δ}`. Since `b³ - a³ = (b - a)(a² + ab + b²)`, this is
`M_Δ (Δ, P)`, where for fixed `Δ` the map
`M_Δ (Δ', P')(x)_k = (Δ'_k · x)(a_k² + a_k b_k + b_k²) + P'_k(F_{A+Δ}(x))`,
`a = Ax`, `b = (A+Δ)x`, is linear in `(Δ', P')` and continuous in `Δ`, with
`M_0 (Δ', P') = L_A Δ' + P' ∘ F_A`, the paper's derivative `𝒟`. Injectivity of `M_0` is the
only position-specific input (`first_upper`): Lemma F1 for non-shear rank one (NonShear.lean),
or the substitution argument of A.3 for invertible `A` (Invertible.lean).

`P` is the whole group error, a polynomial map of degree `≤ 27` (`grpErr`), with the sup norm
on `[-1,1]²`; the retained space is `EndDom 27 = Mat₂ × PolyBox(27)²`.
-/
import VectorSLT.IdentityGroup.Pairs.Endpoint

namespace VectorSLT.IdentityGroup.Pairs

open MeasureTheory Set Filter Topology VectorSLT MvPolynomial
open scoped Matrix

/-- Retained variables at an endpoint: the active-block deviation and the whole group error. -/
abbrev EndDom (d : ℕ) : Type := (Fin 2 → Fin 2 → ℝ) × (Fin 2 → PolyBox d)

theorem mulVec_two (B : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) (k : Fin 2) :
    (B *ᵥ x) k = B k 0 * x 0 + B k 1 * x 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem dot_two (u x : Fin 2 → ℝ) : u ⬝ᵥ x = u 0 * x 0 + u 1 * x 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- The first-position error map at active deviation `Δ`, applied to retained variables `v`. -/
noncomputable def M0fun (A : Matrix (Fin 2) (Fin 2) ℝ) (Δ : Fin 2 → Fin 2 → ℝ) {d : ℕ}
    (v : EndDom d) (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun k =>
  (v.1 k ⬝ᵥ x) * ((A *ᵥ x) k ^ 2 + (A *ᵥ x) k * ((A + Matrix.of Δ) *ᵥ x) k +
    ((A + Matrix.of Δ) *ᵥ x) k ^ 2) + eval (layer (A + Matrix.of Δ) x) (v.2 k).poly

theorem continuous_M0fun (A : Matrix (Fin 2) (Fin 2) ℝ) {d : ℕ} (v : EndDom d) :
    Continuous fun q : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → ℝ) => M0fun A q.1 v q.2 := by
  refine continuous_pi fun k => ?_
  have hB : ∀ i j, Continuous fun q : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      (A + Matrix.of q.1) i j := by
    intro i j; simp only [Matrix.add_apply, Matrix.of_apply]; fun_prop
  have hL := continuous_layer_joint hB continuous_snd
  have hE : Continuous fun q : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      eval (layer (A + Matrix.of q.1) q.2) (v.2 k).poly :=
    (continuous_eval _).comp hL
  simp only [M0fun, mulVec_two, dot_two, Matrix.add_apply, Matrix.of_apply]
  refine Continuous.add ?_ hE
  fun_prop

/-- `M_Δ` as a linear map into `C([-1,1]², ℝ²)`. -/
noncomputable def M0 (A : Matrix (Fin 2) (Fin 2) ℝ) (Δ : Fin 2 → Fin 2 → ℝ) (d : ℕ) :
    EndDom d →ₗ[ℝ] C(ubox, Fin 2 → ℝ) where
  toFun v := ⟨fun x => M0fun A Δ v x.1,
    (continuous_M0fun A v).comp (continuous_const.prodMk continuous_subtype_val)⟩
  map_add' v w := by
    ext x k
    simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply, Pi.add_apply, M0fun,
      Prod.fst_add, Prod.snd_add, PolyBox.poly_add, map_add, add_dotProduct]
    ring
  map_smul' c v := by
    ext x k
    simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, Pi.smul_apply, M0fun,
      Prod.smul_fst, Prod.smul_snd, PolyBox.poly_smul, smul_eval, smul_dotProduct, smul_eq_mul,
      RingHom.id_apply]
    ring

theorem M0_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (Δ : Fin 2 → Fin 2 → ℝ) {d : ℕ} (v : EndDom d)
    (x : ubox) (k : Fin 2) : M0 A Δ d v x k = M0fun A Δ v x.1 k := rfl

/-- The retained variables of `θ` at the first position: `Δ = W₁ - A`, and the whole error of
the group `W₂, W₃, W₄`. -/
noncomputable def vFirst (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) : EndDom (3 ^ 3) :=
  (fun i j => weights θ 0 i j - A i j, fun k => grpErr (fun i => weights θ (i + 1)) 3 k)

theorem A_add_vFirst (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) :
    A + Matrix.of (vFirst A θ).1 = weights θ 0 := by
  ext i j; simp [vFirst]

/-- **The error map is exact**: `h_θ - F_A = M_Δ (Δ, P)` on the box, with `(Δ, P) = vFirst θ`. -/
theorem errBox_eq_M0 (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) :
    errBox A θ = M0 A (vFirst A θ).1 (3 ^ 3) (vFirst A θ) := by
  ext x k
  rw [errBox_apply, M0_apply, M0fun, A_add_vFirst]
  have hnet : net θ x.1 k = layer (weights θ 0) x.1 k +
      eval (layer (weights θ 0) x.1) (grpErr (fun i => weights θ (i + 1)) 3 k).poly := by
    rw [eval_grpErr, net, show (4 : ℕ) = 3 + 1 from rfl, prefixNet_shift]; ring
  rw [hnet]
  simp only [vFirst]
  rw [layer_apply', layer_apply', mulVec_two, mulVec_two, dot_two]
  ring

theorem continuous_vFirst_fst (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Continuous fun θ => (vFirst A θ).1 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_weights 0 i j).sub continuous_const

theorem vFirst_base (A : Matrix (Fin 2) (Fin 2) ℝ) : (vFirst A (basePos A 0)).1 = 0 := by
  funext i j
  simp [vFirst, weights_basePos A 0 0 (by norm_num)]

/-- **Absorption at the first position.** If `M_0 = 𝒟` is injective, then near the base point
`c₀ ‖(Δ, P)‖ ≤ ‖h_θ - F_A‖_{[-1,1]²}`. -/
theorem first_absorb (A : Matrix (Fin 2) (Fin 2) ℝ) (hinj : Function.Injective (M0 A 0 (3 ^ 3))) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ θ, ‖θ - basePos A 0‖ < r₀ →
      c₀ * ‖vFirst A θ‖ ≤ ‖errBox A θ‖ := by
  have hcont : ∀ v : EndDom (3 ^ 3), Continuous fun Δ => M0 A Δ (3 ^ 3) v := by
    intro v
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_M0fun A v).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  obtain ⟨c₀, hc₀, hev⟩ := uniform_lower_of_linear (fun Δ => M0 A Δ (3 ^ 3)) hcont hinj
  have hev' : ∀ᶠ θ in 𝓝 (basePos A 0), ∀ v, c₀ * ‖v‖ ≤ ‖M0 A (vFirst A θ).1 (3 ^ 3) v‖ := by
    have ht : Tendsto (fun θ => (vFirst A θ).1) (𝓝 (basePos A 0)) (𝓝 0) := by
      have := (continuous_vFirst_fst A).tendsto (basePos A 0)
      rwa [vFirst_base] at this
    exact ht.eventually hev
  obtain ⟨r₀, hr₀, hr⟩ := Metric.eventually_nhds_iff.mp hev'
  refine ⟨r₀, hr₀, c₀, hc₀, fun θ hθ => ?_⟩
  rw [errBox_eq_M0]
  exact hr (by rwa [dist_eq_norm]) _

/-- `‖Δ‖²`-type bound: `∑ᵢⱼ Δᵢⱼ² ≤ 4 ‖Δ‖²` in the sup norm. -/
theorem sum_sq_le_norm (Δ : Fin 2 → Fin 2 → ℝ) : ∑ i, ∑ j, Δ i j ^ 2 ≤ 4 * ‖Δ‖ ^ 2 := by
  have h : ∀ i j, Δ i j ^ 2 ≤ ‖Δ‖ ^ 2 := by
    intro i j
    have h1 : |Δ i j| ≤ ‖Δ‖ := by
      rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm (Δ i) j).trans (norm_le_pi_norm Δ i)
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  simp only [Fin.sum_univ_two]
  linarith [h 0 0, h 0 1, h 1 0, h 1 1]

theorem rowU_Sfun0 (θ : Raw16) (k : Fin 2) :
    rowU (![(Sfun 0 θ).2.1, (Sfun 0 θ).2.2] k) = grpRow (fun i => weights θ (i + 1)) 3 k := by
  rw [rowU_Sfun]; funext i; fin_cases i <;> rfl

/-- **The group comparison at the first position**:
`‖W₁ - A‖² + G₃(u₀) + G₃(u₁) ≤ C ‖(Δ, P)‖²`. -/
theorem first_compare (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ Cq : ℝ, ∀ θ, actSq A (Sfun 0 θ).1 + cubeSumSq (rowU (Sfun 0 θ).2.1) +
      cubeSumSq (rowU (Sfun 0 θ).2.2) ≤ Cq * ‖vFirst A θ‖ ^ 2 := by
  obtain ⟨C, hC, hG⟩ := cubeSumSq_le_grpErr 3
  refine ⟨4 + 2 * C, fun θ => ?_⟩
  set v := vFirst A θ
  have hΔ : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have hP : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
  have hact : actSq A (Sfun 0 θ).1 ≤ 4 * ‖v‖ ^ 2 := by
    rw [actSq_Sfun]
    refine (sum_sq_le_norm v.1).trans ?_
    have := pow_le_pow_left₀ (norm_nonneg _) hΔ 2
    linarith
  have hrow : ∀ k : Fin 2, cubeSumSq (rowU (![(Sfun 0 θ).2.1, (Sfun 0 θ).2.2] k)) ≤
      C * ‖v‖ ^ 2 := by
    intro k
    rw [rowU_Sfun0]
    refine (hG _ k).trans (mul_le_mul_of_nonneg_left ?_ hC)
    have h1 : ‖grpErr (fun i => weights θ (i + 1)) 3 k‖ ≤ ‖v‖ :=
      (norm_le_pi_norm v.2 k).trans hP
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h0 := hrow 0
  have h1 := hrow 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  linarith

/-! ### From the box to the whole plane -/

theorem eval_bind₁_eq (x : Fin 2 → ℝ) (f : Fin 2 → MvPolynomial (Fin 2) ℝ)
    (p : MvPolynomial (Fin 2) ℝ) : eval x (bind₁ f p) = eval (fun i => eval x (f i)) p := by
  rw [show eval x = eval₂Hom (RingHom.id ℝ) x from rfl, eval₂Hom_bind₁]; rfl

/-- A polynomial vanishing on `[-1,1]²` vanishes everywhere. -/
theorem eval_eq_zero_of_box {p : MvPolynomial (Fin 2) ℝ} (h : ∀ x : ubox, eval x.1 p = 0)
    (x : Fin 2 → ℝ) : eval x p = 0 := by
  have hp : p = 0 := by
    refine funext_set (s := fun _ => Icc (-1 : ℝ) 1) (fun _ => Icc_infinite (by norm_num))
      fun y hy => ?_
    have hy' : y ∈ ubox := by simp only [ubox, ← pi_univ_Icc]; exact hy
    rw [map_zero]; exact h ⟨y, hy'⟩
  rw [hp, map_zero]

/-- The polynomial map `F_A`. -/
noncomputable def layerPoly (A : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) : MvPolynomial (Fin 2) ℝ :=
  X i + (C (A i 0) * X 0 + C (A i 1) * X 1) ^ 3

theorem eval_layerPoly (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    (fun i => eval x (layerPoly A i)) = layer A x := by
  funext i; simp [layerPoly, layer_apply']

/-- **The kernel of `𝒟` at the first position, as an identity on the whole plane.**
If `M_0 v = 0` on the box, then `(Δ'_k · x) · 3 (Ax)_k² + P'_k(F_A x) = 0` for every `x`. -/
theorem M0_kernel (A : Matrix (Fin 2) (Fin 2) ℝ) {d : ℕ} {v : EndDom d} (hv : M0 A 0 d v = 0)
    (k : Fin 2) (x : Fin 2 → ℝ) :
    (v.1 k ⬝ᵥ x) * (3 * (A *ᵥ x) k ^ 2) + eval (layer A x) (v.2 k).poly = 0 := by
  set q : MvPolynomial (Fin 2) ℝ :=
    (C (v.1 k 0) * X 0 + C (v.1 k 1) * X 1) * (3 * (C (A k 0) * X 0 + C (A k 1) * X 1) ^ 2) +
      bind₁ (layerPoly A) (v.2 k).poly
  have hq : ∀ y : Fin 2 → ℝ, eval y q =
      (v.1 k ⬝ᵥ y) * (3 * (A *ᵥ y) k ^ 2) + eval (layer A y) (v.2 k).poly := by
    intro y
    simp only [q, map_add, map_mul, map_pow, eval_C, eval_X, eval_bind₁_eq, eval_layerPoly,
      dot_two, mulVec_two]
    norm_num
  rw [← hq]
  refine eval_eq_zero_of_box (fun y => ?_) x
  have h := congrArg (fun f : C(ubox, Fin 2 → ℝ) => f y k) hv
  simp only [M0_apply, M0fun, ContinuousMap.zero_apply, Pi.zero_apply, Matrix.of_zero,
    add_zero] at h
  rw [hq, ← h]; ring

/-- **Active block first: `Z_N ≤ C N⁻⁴` from injectivity of `𝒟` and `CubeSumUpper 3`**, in the
hypothesis shape of `theoremM_shear`. -/
theorem first_upper {A : Matrix (Fin 2) (Fin 2) ℝ} (hinj : Function.Injective (M0 A 0 (3 ^ 3)))
    (h3 : CubeSumUpper 3) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → Zpos μ A φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4) := by
  obtain ⟨r₀, hr₀, c₀, hc₀, habs⟩ := first_absorb A hinj
  obtain ⟨Cq, hq⟩ := first_compare A
  exact upper_of_absorb A 0 (fun r hr => rowBound_three h3 hr)
    (continuous_cubeSumSq 3).measurable (vFirst A) hr₀ hc₀ habs hq

end VectorSLT.IdentityGroup.Pairs
