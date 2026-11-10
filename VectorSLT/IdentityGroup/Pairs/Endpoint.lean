/-
Paper 2: the common last step of Proposition `prop:nonshear` and Theorem `thm:invertible`.

Given the comparison of the paper (`eq:F-compare`, `eq:A-B`), in the form
* absorption: `c₀ ‖v(θ)‖ ≤ ‖h_θ - F_A‖_{[-1,1]²}` near the base point, for a vector `v(θ)` of
  retained variables in a finite-dimensional normed space, and
* the identity-group comparison: `‖W_p - A‖² + g(u₀) + g(u₁) ≤ C ‖v(θ)‖²`,

(G↓) (`gram_down`) and the product integral (`position_bound`) give `Z_N ≤ C N⁻⁴`, in the
hypothesis shape of `theoremM_shear`. This file also collects network facts used at every
position: continuity in the weights, and the splitting of the network after the first `n`
blocks.
-/
import VectorSLT.IdentityGroup.Pairs.Absorb
import VectorSLT.IdentityGroup.Pairs.GramDown
import VectorSLT.IdentityGroup.Pairs.GroupCubic
import VectorSLT.IdentityGroup.Pairs.Integrate

namespace VectorSLT.IdentityGroup.Pairs

open MeasureTheory Set Filter Topology VectorSLT MvPolynomial

/-! ### Network facts -/

theorem layer_apply' (B : Matrix (Fin 2) (Fin 2) ℝ) (z : Fin 2 → ℝ) (k : Fin 2) :
    layer B z k = z k + (B k 0 * z 0 + B k 1 * z 1) ^ 3 := by
  rw [layer_apply]; simp [dotProduct, Fin.sum_univ_two]

theorem continuous_layer_joint {X : Type*} [TopologicalSpace X]
    {B : X → Matrix (Fin 2) (Fin 2) ℝ} {z : X → Fin 2 → ℝ}
    (hB : ∀ i j, Continuous fun x => B x i j) (hz : Continuous z) :
    Continuous fun x => layer (B x) (z x) := by
  refine continuous_pi fun k => ?_
  simp only [layer_apply']
  have hz0 : Continuous fun x => z x 0 := (continuous_apply 0).comp hz
  have hz1 : Continuous fun x => z x 1 := (continuous_apply 1).comp hz
  have hzk : Continuous fun x => z x k := (continuous_apply k).comp hz
  exact hzk.add ((((hB k 0).mul hz0).add ((hB k 1).mul hz1)).pow 3)

theorem continuous_weights (q : ℕ) (i j : Fin 2) : Continuous fun θ : Raw16 => weights θ q i j := by
  rcases q with _ | _ | _ | m <;> fin_cases i <;> fin_cases j <;> simp [weights, tri] <;>
    fun_prop

/-- `θ ↦ prefixNet (weights θ) n x` is jointly continuous. -/
theorem continuous_prefixNet_joint {X : Type*} [TopologicalSpace X]
    {W : X → ℕ → Matrix (Fin 2) (Fin 2) ℝ} (hW : ∀ q i j, Continuous fun x => W x q i j)
    {z : X → Fin 2 → ℝ} (hz : Continuous z) (n : ℕ) :
    Continuous fun x => prefixNet (W x) n (z x) := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    simp only [prefixNet_succ, Function.comp_apply]
    exact continuous_layer_joint (hW n) ih

/-- The network after its first block: `G_{n+1} = G'_n ∘ F_{W 0}` with `G'` the shifted net. -/
theorem prefixNet_shift (W : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) (x : Fin 2 → ℝ) :
    prefixNet W (n + 1) x = prefixNet (fun i => W (i + 1)) n (layer (W 0) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixNet_succ, Function.comp_apply, ih, prefixNet_succ, Function.comp_apply]

/-- `x ↦ eval x p.poly` is jointly continuous in `(p, x)` on `PolyBox d × ℝ²`. -/
theorem continuous_eval_joint {d : ℕ} {X : Type*} [TopologicalSpace X] {P : X → PolyBox d}
    (hP : Continuous P) {z : X → Fin 2 → ℝ} (hz : Continuous z) :
    Continuous fun x => eval (z x) (P x).poly := by
  have h : (fun x => eval (z x) (P x).poly) =
      fun x => ∑ a ∈ expSet d, coeffL d a (P x) * mono a (z x) := by
    funext x; rw [eval_eq_sum_expSet (P x).totalDegree_le]; rfl
  rw [h]
  refine continuous_finsetSum _ fun a _ => ?_
  exact ((LinearMap.continuous_of_finiteDimensional (coeffL d a)).comp hP).mul
    ((continuous_mono a).comp hz)

/-- A map into `PolyBox d` is continuous if its evaluation on the box is jointly continuous. -/
theorem continuous_polyBox_of {d : ℕ} {X : Type*} [TopologicalSpace X] (P : X → PolyBox d)
    (h : Continuous fun q : X × ubox => eval q.2.1 (P q.1).poly) : Continuous P := by
  have hE : Continuous fun x => evalBox d (P x) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact h
  have hind : Topology.IsInducing (evalBox d) := by
    exact ⟨rfl⟩
  exact hind.continuous_iff.mpr hE

/-! ### Absorption and comparison give the upper bound -/

/-- **Absorption and the group comparison give `Z_N ≤ C N⁻⁴`** at position `p`. -/
theorem upper_of_absorb (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4)
    {g : (Fin 3 → ℝ × ℝ) → ℝ} (hg : ∀ r, 0 < r → RowBound g r) (hgm : Measurable g)
    {V : Type*} [NormedAddCommGroup V] (v : Raw16 → V) {r₀ c₀ Cq : ℝ} (hr₀ : 0 < r₀)
    (hc₀ : 0 < c₀) (habs : ∀ θ, ‖θ - basePos A p‖ < r₀ → c₀ * ‖v θ‖ ≤ ‖errBox A θ‖)
    (hq : ∀ θ, actSq A (Sfun p θ).1 + g (rowU (Sfun p θ).2.1) + g (rowU (Sfun p θ).2.2) ≤
      Cq * ‖v θ‖ ^ 2) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → Zpos μ A φ χ p N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4) := by
  refine ⟨r₀ / 2, half_pos hr₀, ?_⟩
  intro μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ π₁ hπ₁ hφ hχ hχs
  obtain ⟨κ, hκ, hG⟩ := gram_down μ hmom hlh hμ₀ hμ A
  set Cq' := max Cq 1
  have hK : ∀ θ, ‖θ - basePos A p‖ ≤ r₀ / 2 →
      κ * c₀ ^ 2 / Cq' * (actSq A (Sfun p θ).1 + g (rowU (Sfun p θ).2.1) +
        g (rowU (Sfun p θ).2.2)) ≤ popLossA μ A θ := by
    intro θ hθ
    have h1 := habs θ (lt_of_le_of_lt hθ (half_lt_self hr₀))
    have h2 := hq θ
    have hCq : Cq ≤ Cq' := le_max_left _ _
    have hCq1 : 0 < Cq' := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hv0 := norm_nonneg (v θ)
    have h3 : c₀ ^ 2 * ‖v θ‖ ^ 2 ≤ ‖errBox A θ‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 2
    have h4 := hG θ
    have h5 : actSq A (Sfun p θ).1 + g (rowU (Sfun p θ).2.1) + g (rowU (Sfun p θ).2.2) ≤
        Cq' * ‖v θ‖ ^ 2 := h2.trans (mul_le_mul_of_nonneg_right hCq (by positivity))
    calc κ * c₀ ^ 2 / Cq' * (actSq A (Sfun p θ).1 + g (rowU (Sfun p θ).2.1) +
          g (rowU (Sfun p θ).2.2))
        ≤ κ * c₀ ^ 2 / Cq' * (Cq' * ‖v θ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = κ * (c₀ ^ 2 * ‖v θ‖ ^ 2) := by field_simp
      _ ≤ κ * ‖errBox A θ‖ ^ 2 := mul_le_mul_of_nonneg_left h3 hκ.le
      _ ≤ _ := h4
  have hκ' : 0 < κ * c₀ ^ 2 / Cq' := by
    have : 0 < Cq' := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity
  exact position_bound A p (half_pos hr₀) (hg _ (half_pos hr₀)) hgm (popLossA μ A) hκ' hK
    φ χ hπ₁ hφ hχ hχs

/-- **From the upper bound to the pair `(4, 1)`**, with the certified lower bound
`Zpos_lower_N4`. The extra hypotheses are the lower bounds of the prior and the cutoff near the
base point. -/
theorem pair_of_upper (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4)
    (hup : ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → Zpos μ A φ χ p N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4)) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ᶠ θ in 𝓝 (basePos A p), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      VectorSLT.SLT.HasLaplacePair (Zpos μ A φ χ p) 4 1 := by
  obtain ⟨r, hr, hu⟩ := hup
  refine ⟨r, hr, ?_⟩
  intro μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ φ₀ χ₀ π₁ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs
  obtain ⟨c, hc, N₁, hlo⟩ := Zpos_lower_N4 μ hmom A p φ χ hφ₀ hχ₀ hφl hχl
  obtain ⟨C, N₂, hhi⟩ := hu μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs
  exact hasLaplacePair_41 hc hlo hhi

end VectorSLT.IdentityGroup.Pairs
