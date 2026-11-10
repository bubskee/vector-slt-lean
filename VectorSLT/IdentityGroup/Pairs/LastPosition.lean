/-
Paper 2, Appendix A.3, the case "active block last" (Lean `p = 3`, paper position four).

With `H = F_{W₃} ∘ F_{W₂} ∘ F_{W₁} = I + P` (the whole prefix group error) and `W₄ = A + Δ`, the
error is exactly `h - F_A = F_{A+Δ}(x + P(x)) - F_A(x)`. With `z = x + P(x)`,
`α = (Az)_k`, `β = ((A+Δ)z)_k`, `a = (Ax)_k`, it equals
`(Δ_k · z)(α² + αβ + β²) + P_k(x) + (A P(x))_k (a² + aα + α²)`,
which is `M_η (Δ, P)` for the map
`M_η (Δ', P')(x)_k = (Δ'_k · z)(α² + αβ + β²) + P'_k(x) + (A P'(x))_k (a² + aα + α²)`,
linear in `(Δ', P')`, continuous in `η = (Δ, P)`, with
`M_0 (Δ', P') = L_A Δ' + P' + DV_A P' = L_A Δ' + DF_A P'`, the paper's linear part (A-C).

Injectivity of `M_0` for invertible `A` (`last_injective`) is the paper's multiplication
argument, run along rays: if `n ≥ 2` is the top degree of `s ↦ P'(s y)`, the coefficient of
`s^{n+2}` is `3 (Ay)_k² (A c_n)_k`, which vanishes only if the top coefficients `c_n` do.
-/
import VectorSLT.IdentityGroup.Pairs.PolyAlgebra

namespace VectorSLT.IdentityGroup.Pairs

open MeasureTheory Set Filter Topology VectorSLT MvPolynomial
open scoped Matrix

/-- Evaluation of a vector of polynomials. -/
noncomputable def evalV {d : ℕ} (P : Fin 2 → PolyBox d) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => eval x (P i).poly

/-- The last-position error map at `η = (Δ, P)`, applied to retained variables `v`. -/
noncomputable def M3fun (A : Matrix (Fin 2) (Fin 2) ℝ) {d : ℕ} (η v : EndDom d)
    (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun k =>
  let z := x + evalV η.2 x
  let α := (A *ᵥ z) k
  let β := ((A + Matrix.of η.1) *ᵥ z) k
  let a := (A *ᵥ x) k
  (v.1 k ⬝ᵥ z) * (α ^ 2 + α * β + β ^ 2) + evalV v.2 x k +
    (A *ᵥ evalV v.2 x) k * (a ^ 2 + a * α + α ^ 2)

theorem continuous_evalV_joint {d : ℕ} {X : Type*} [TopologicalSpace X]
    {P : X → Fin 2 → PolyBox d} (hP : Continuous P) {z : X → Fin 2 → ℝ} (hz : Continuous z) :
    Continuous fun q => evalV (P q) (z q) :=
  continuous_pi fun i => continuous_eval_joint ((continuous_apply i).comp hP) hz

theorem continuous_M3fun (A : Matrix (Fin 2) (Fin 2) ℝ) {d : ℕ} (v : EndDom d) :
    Continuous fun q : EndDom d × (Fin 2 → ℝ) => M3fun A q.1 v q.2 := by
  refine continuous_pi fun k => ?_
  have hz : Continuous fun q : EndDom d × (Fin 2 → ℝ) => q.2 + evalV q.1.2 q.2 :=
    continuous_snd.add (continuous_evalV_joint (continuous_snd.comp continuous_fst) continuous_snd)
  have hz0 : Continuous fun q : EndDom d × (Fin 2 → ℝ) => (q.2 + evalV q.1.2 q.2) 0 :=
    (continuous_apply 0).comp hz
  have hz1 : Continuous fun q : EndDom d × (Fin 2 → ℝ) => (q.2 + evalV q.1.2 q.2) 1 :=
    (continuous_apply 1).comp hz
  have hD : ∀ i j, Continuous fun q : EndDom d × (Fin 2 → ℝ) => q.1.1 i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_fst.comp continuous_fst))
  have hv : Continuous fun q : EndDom d × (Fin 2 → ℝ) => evalV v.2 q.2 :=
    continuous_evalV_joint continuous_const continuous_snd
  have hv0 : Continuous fun q : EndDom d × (Fin 2 → ℝ) => evalV v.2 q.2 0 :=
    (continuous_apply 0).comp hv
  have hv1 : Continuous fun q : EndDom d × (Fin 2 → ℝ) => evalV v.2 q.2 1 :=
    (continuous_apply 1).comp hv
  have hvk : Continuous fun q : EndDom d × (Fin 2 → ℝ) => evalV v.2 q.2 k :=
    (continuous_apply k).comp hv
  have hx0 : Continuous fun q : EndDom d × (Fin 2 → ℝ) => q.2 0 :=
    (continuous_apply 0).comp continuous_snd
  have hx1 : Continuous fun q : EndDom d × (Fin 2 → ℝ) => q.2 1 :=
    (continuous_apply 1).comp continuous_snd
  simp only [M3fun, mulVec_two, dot_two, Matrix.add_apply, Matrix.of_apply]
  have hk0 := hD k 0
  have hk1 := hD k 1
  fun_prop

/-- `M_η` as a linear map into `C([-1,1]², ℝ²)`. -/
noncomputable def M3 (A : Matrix (Fin 2) (Fin 2) ℝ) {d : ℕ} (η : EndDom d) :
    EndDom d →ₗ[ℝ] C(ubox, Fin 2 → ℝ) where
  toFun v := ⟨fun x => M3fun A η v x.1,
    (continuous_M3fun A v).comp (continuous_const.prodMk continuous_subtype_val)⟩
  map_add' v w := by
    ext x k
    simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply, Pi.add_apply, M3fun, evalV,
      Prod.fst_add, Prod.snd_add, PolyBox.poly_add, map_add, add_dotProduct, mulVec_two]
    ring
  map_smul' c v := by
    ext x k
    simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, Pi.smul_apply, M3fun, evalV,
      Prod.smul_fst, Prod.smul_snd, PolyBox.poly_smul, smul_eval, smul_dotProduct, smul_eq_mul,
      RingHom.id_apply, mulVec_two]
    ring

theorem M3_apply (A : Matrix (Fin 2) (Fin 2) ℝ) {d : ℕ} (η v : EndDom d) (x : ubox) (k : Fin 2) :
    M3 A η v x k = M3fun A η v x.1 k := rfl

/-- The retained variables of `θ` at the last position: `Δ = W₄ - A`, and the whole error of
the group `W₁, W₂, W₃`. -/
noncomputable def vLast (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) : EndDom (3 ^ 3) :=
  (fun i j => weights θ 3 i j - A i j, fun k => grpErr (weights θ) 3 k)

/-- **The error map is exact**: `h_θ - F_A = M_η (η)` on the box, with `η = vLast θ`. -/
theorem errBox_eq_M3 (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) :
    errBox A θ = M3 A (vLast A θ) (vLast A θ) := by
  ext x k
  rw [errBox_apply, M3_apply]
  have hz : x.1 + evalV (vLast A θ).2 x.1 = prefixNet (weights θ) 3 x.1 := by
    funext i; simp only [Pi.add_apply, evalV, vLast, eval_grpErr]; ring
  have hA : A + Matrix.of (vLast A θ).1 = weights θ 3 := by ext i j; simp [vLast]
  have hnet : net θ x.1 = layer (weights θ 3) (prefixNet (weights θ) 3 x.1) := rfl
  simp only [M3fun]
  rw [hz, hA, hnet]
  have hP : ∀ i, evalV (vLast A θ).2 x.1 i = prefixNet (weights θ) 3 x.1 i - x.1 i := by
    intro i; simp [evalV, vLast, eval_grpErr]
  rw [layer_apply', layer_apply', mulVec_two, mulVec_two, mulVec_two, mulVec_two, dot_two]
  simp only [hP]
  simp only [vLast]
  ring

theorem continuous_vLast (A : Matrix (Fin 2) (Fin 2) ℝ) : Continuous (vLast A) := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_pi fun i => continuous_pi fun j =>
      (continuous_weights 3 i j).sub continuous_const
  · refine continuous_pi fun k => continuous_polyBox_of _ ?_
    have h := continuous_prefixNet_joint (X := Raw16 × ubox) (W := fun q => weights q.1)
      (fun q i j => (continuous_weights q i j).comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd) 3
    have : (fun q : Raw16 × ubox => eval q.2.1 (grpErr (weights q.1) 3 k).poly) =
        fun q => prefixNet (weights q.1) 3 q.2.1 k - q.2.1 k := by
      funext q; rw [eval_grpErr]
    rw [this]
    exact ((continuous_apply k).comp h).sub
      ((continuous_apply k).comp (continuous_subtype_val.comp continuous_snd))

theorem prefixNet_zero_blocks (W : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ)
    (hW : ∀ q < n, W q = 0) (x : Fin 2 → ℝ) : prefixNet W n x = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixNet_succ, Function.comp_apply, ih (fun q hq => hW q (by omega)),
      hW n (by omega), layer_zero_mat]

theorem vLast_base (A : Matrix (Fin 2) (Fin 2) ℝ) : vLast A (basePos A 3) = 0 := by
  refine Prod.ext ?_ ?_
  · funext i j; simp [vLast, weights_basePos A 3 3 (by norm_num)]
  · funext k
    apply Subtype.ext
    show (grpErr (weights (basePos A 3)) 3 k).poly = 0
    apply MvPolynomial.funext; intro x
    rw [eval_grpErr, prefixNet_zero_blocks _ 3 (fun q hq => by
      rw [weights_basePos A 3 q (by omega)]; simp; omega) x, sub_self, map_zero]

/-- **Absorption at the last position.** -/
theorem last_absorb (A : Matrix (Fin 2) (Fin 2) ℝ) (hinj : Function.Injective (M3 A (0 : EndDom (3 ^ 3)))) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ θ, ‖θ - basePos A 3‖ < r₀ →
      c₀ * ‖vLast A θ‖ ≤ ‖errBox A θ‖ := by
  have hcont : ∀ v : EndDom (3 ^ 3), Continuous fun η : EndDom (3 ^ 3) => M3 A η v := by
    intro v
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_M3fun A v).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  obtain ⟨c₀, hc₀, hev⟩ := uniform_lower_of_linear (fun η : EndDom (3 ^ 3) => M3 A η) hcont hinj
  have hev' : ∀ᶠ θ in 𝓝 (basePos A 3), ∀ v, c₀ * ‖v‖ ≤ ‖M3 A (vLast A θ) v‖ := by
    have ht : Tendsto (vLast A) (𝓝 (basePos A 3)) (𝓝 0) := by
      have := (continuous_vLast A).tendsto (basePos A 3)
      rwa [vLast_base] at this
    exact ht.eventually hev
  obtain ⟨r₀, hr₀, hr⟩ := Metric.eventually_nhds_iff.mp hev'
  refine ⟨r₀, hr₀, c₀, hc₀, fun θ hθ => ?_⟩
  rw [errBox_eq_M3]
  exact hr (by rwa [dist_eq_norm]) _

/-- `G₃` is invariant under reordering the forms. -/
theorem cubeSumSq_comp_equiv {k : ℕ} (u : Fin k → ℝ × ℝ) (e : Fin k ≃ Fin k) :
    cubeSumSq (u ∘ e) = cubeSumSq u := by
  have h : cubeSum (u ∘ e) = cubeSum u := by
    funext j
    fin_cases j <;> simp only [cubeSum, Function.comp_apply] <;> simp <;>
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  simp only [cubeSumSq, h]

theorem rowU_Sfun3 (θ : Raw16) (k : Fin 2) :
    rowU (![(Sfun 3 θ).2.1, (Sfun 3 θ).2.2] k) = grpRow (weights θ) 3 k ∘ finRotate 3 := by
  rw [rowU_Sfun]; funext i; fin_cases i <;> rfl

/-- **The group comparison at the last position.** -/
theorem last_compare (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ Cq : ℝ, ∀ θ, actSq A (Sfun 3 θ).1 + cubeSumSq (rowU (Sfun 3 θ).2.1) +
      cubeSumSq (rowU (Sfun 3 θ).2.2) ≤ Cq * ‖vLast A θ‖ ^ 2 := by
  obtain ⟨C, hC, hG⟩ := cubeSumSq_le_grpErr 3
  refine ⟨4 + 2 * C, fun θ => ?_⟩
  set v := vLast A θ
  have hΔ : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have hP : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
  have hact : actSq A (Sfun 3 θ).1 ≤ 4 * ‖v‖ ^ 2 := by
    rw [actSq_Sfun]
    refine (sum_sq_le_norm v.1).trans ?_
    have := pow_le_pow_left₀ (norm_nonneg _) hΔ 2
    linarith
  have hrow : ∀ k : Fin 2, cubeSumSq (rowU (![(Sfun 3 θ).2.1, (Sfun 3 θ).2.2] k)) ≤
      C * ‖v‖ ^ 2 := by
    intro k
    rw [rowU_Sfun3, cubeSumSq_comp_equiv]
    refine (hG _ k).trans (mul_le_mul_of_nonneg_left ?_ hC)
    have h1 : ‖grpErr (weights θ) 3 k‖ ≤ ‖v‖ := (norm_le_pi_norm v.2 k).trans hP
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h0 := hrow 0
  have h1 := hrow 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  linarith

/-- **Active block last: `Z_N ≤ C N⁻⁴` from injectivity of `M_0` and `CubeSumUpper 3`.** -/
theorem last_upper {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hinj : Function.Injective (M3 A (0 : EndDom (3 ^ 3)))) (h3 : CubeSumUpper 3) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → Zpos μ A φ χ 3 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4) := by
  obtain ⟨r₀, hr₀, c₀, hc₀, habs⟩ := last_absorb A hinj
  obtain ⟨Cq, hq⟩ := last_compare A
  exact upper_of_absorb A 3 (fun r hr => rowBound_three h3 hr)
    (continuous_cubeSumSq 3).measurable (vLast A) hr₀ hc₀ habs hq

end VectorSLT.IdentityGroup.Pairs
