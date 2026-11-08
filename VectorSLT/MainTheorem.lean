/-
Brief 03, O4: the paper-facing main theorem and the `Fin 4 → Matrix` restatement.

* `rawEquiv`: the sixteen raw weights `Raw16` are exactly the paper's four `2×2` matrices
  `(W₁, W₂, W₃, W₄)` in application order; `net θ = network (rawW θ)`, and the base point at
  position `p` is `Pi.single p A`.
* `mainTheorem_shear`: the depth-four position table `(4,5), (4,1), (4,1), (4,1)` for every
  two-nonzero-row shear target, with Theorem K and Theorem N as the only named hypotheses.
-/
import VectorSLT.LowerPositions

namespace VectorSLT

open MeasureTheory Set Filter Topology

/-! ### The raw-weight network of the paper -/

/-- The paper's raw-weight list `(W₁, W₂, W₃, W₄)`, in application order (Lean `0..3`). -/
def rawW (θ : Raw16) : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ := fun q => weights θ q

/-- Inverse: read the sixteen raw coordinates off four matrices. -/
def ofRawW (W : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ) : Raw16 :=
  (((W 0 0 0, W 0 0 1), (W 0 1 0, W 0 1 1)),
    (((W 1 0 0, W 2 0 0, W 3 0 0), (W 1 0 1, W 2 0 1, W 3 0 1)),
      ((W 1 1 0, W 2 1 0, W 3 1 0), (W 1 1 1, W 2 1 1, W 3 1 1))))

/-- **The parameter space is the paper's**: `Raw16 ≃ (Fin 4 → Matrix (Fin 2) (Fin 2) ℝ)`. -/
def rawEquiv : Raw16 ≃ (Fin 4 → Matrix (Fin 2) (Fin 2) ℝ) where
  toFun := rawW
  invFun := ofRawW
  left_inv θ := rfl
  right_inv W := by
    funext q i j
    fin_cases q <;> fin_cases i <;> fin_cases j <;> rfl

/-- **The Lean network is the paper's raw-weight network** `F_{W₄} ∘ F_{W₃} ∘ F_{W₂} ∘ F_{W₁}`. -/
theorem net_eq_network (θ : Raw16) : net θ = network (rawW θ) := by
  unfold net network
  refine prefixNet_congr _ _ 4 fun q hq => ?_
  simp [extendWeights, hq, rawW]

/-- The network as an explicit composition of the four paper layers. -/
theorem net_eq_comp (θ : Raw16) :
    net θ = layer (rawW θ 3) ∘ layer (rawW θ 2) ∘ layer (rawW θ 1) ∘ layer (rawW θ 0) := by
  rfl

/-- The base point at position `p+1` is `A` in slot `p`, zero elsewhere. -/
theorem rawW_basePos (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4) :
    rawW (basePos A p) = Pi.single p A := by
  funext q
  rw [rawW, weights_basePos A p q q.isLt, Pi.single_apply]
  simp only [Fin.val_inj]

/-- The population loss in paper form: `K(B) = E_μ ‖G_B(x) - F_A(x)‖²`. -/
theorem popLossA_eq_network (μ : Measure (Fin 2 → ℝ)) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (θ : Raw16) :
    popLossA μ A θ = ∫ x, ∑ k, (network (rawW θ) x k - layer A x k) ^ 2 ∂μ := by
  rw [popLossA, net_eq_network]

/-! ### Laplace pairs from two-sided bounds -/

theorem hasLaplacePair_45 {Zf : ℝ → ENNReal} {c C N₀ : ℝ} (hc : 0 < c)
    (h : ∀ N, N₀ ≤ N → ENNReal.ofReal (c * N⁻¹ ^ 4 * Real.log N ^ 4) ≤ Zf N ∧
      Zf N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4 * Real.log N ^ 4)) : VectorSLT.SLT.HasLaplacePair Zf 4 5 := by
  refine ⟨⟨c, hc, max N₀ 1, fun N hN => ?_⟩, ⟨C, max N₀ 1, fun N hN => ?_⟩⟩ <;>
  · have hN0 : 0 < N := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hN)
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, rpow_neg_natCast_eq hN0]
    first | exact (h N ((le_max_left _ _).trans hN)).1 | exact (h N ((le_max_left _ _).trans hN)).2

/-! ### The main theorem -/

/-- **Main theorem (depth four, rank-one shear target with both rows nonzero).**
For every input law with finite 162nd moments and a density bounded below on some box, every
prior `φ` bounded by `π₁` and bounded below near each of the four base points, and every
cutoff `χ ≤ 1` bounded below near `0` and supported in the `r`-ball (`r` depends only on `A`),
assuming Theorem K's upper bound at position four and Theorem N's upper bound at positions two
and three, the four localized integrals have pairs

| position | 1 | 2 | 3 | 4 |
|---|---|---|---|---|
| `(λ, m)` | (4,5) | (4,1) | (4,1) | (4,1) |

Position one is Lean-certified outright; positions two–four are certified in their lower
halves and conditional on `ThmN` / `ThmK` in their upper halves. -/
theorem mainTheorem_shear {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ p : Fin 4, ∀ᶠ θ in 𝓝 (basePos A p), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ThmK μ A φ χ → ThmN μ A φ χ →
      VectorSLT.SLT.HasLaplacePair (Zpos μ A φ χ 0) 4 5 ∧ VectorSLT.SLT.HasLaplacePair (Zpos μ A φ χ 1) 4 1 ∧
        VectorSLT.SLT.HasLaplacePair (Zpos μ A φ χ 2) 4 1 ∧ VectorSLT.SLT.HasLaplacePair (Zpos μ A φ χ 3) 4 1 := by
  obtain ⟨r, hr, h1⟩ := ZN1_two_sided_moments hA
  refine ⟨r, hr, ?_⟩
  intro μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ φ₀ χ₀ π₁ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs hK hN
  obtain ⟨c, C, N₀, hc, h⟩ :=
    h1 μ hmom hlh hμ₀ hμ φ χ hφ₀ hχ₀ (hφl 0) hχl hπ₁ hφ hχ hχs
  exact ⟨hasLaplacePair_45 hc h,
    middle_position_pair hmom hφ₀ hχ₀ 1 (Or.inl rfl) (hφl 1) hχl hN,
    middle_position_pair hmom hφ₀ hχ₀ 2 (Or.inr rfl) (hφl 2) hχl hN,
    position_four_pair hmom hφ₀ hχ₀ (hφl 3) hχl hK.upper⟩

/-- **The first block is the only logarithmic placement**: under the same hypotheses,
`Z_{N,1} / Z_{N,j} → ∞` for `j = 2, 3, 4`. -/
theorem mainTheorem_shear_ratio {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ p : Fin 4, ∀ᶠ θ in 𝓝 (basePos A p), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ThmK μ A φ χ → ThmN μ A φ χ →
      ∀ p : Fin 4, p ≠ 0 →
        Tendsto (fun N => Zpos μ A φ χ 0 N / Zpos μ A φ χ p N) atTop (𝓝 ⊤) := by
  obtain ⟨r, hr, h1⟩ := ZN1_two_sided_moments hA
  refine ⟨r, hr, ?_⟩
  intro μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ φ₀ χ₀ π₁ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs hK hN p hp
  obtain ⟨c, C, N₀, hc, h⟩ :=
    h1 μ hmom hlh hμ₀ hμ φ χ hφ₀ hχ₀ (hφl 0) hχl hπ₁ hφ hχ hχs
  -- two-sided `N⁻⁴` at position `p`
  obtain ⟨c', hc', N₁, hlo⟩ := Zpos_lower_N4 μ hmom A p φ χ hφ₀ hχ₀ (hφl p) hχl
  obtain ⟨C', N₂, hhi⟩ : ∃ C' N₂ : ℝ, ∀ N, N₂ ≤ N →
      Zpos μ A φ χ p N ≤ ENNReal.ofReal (C' * N⁻¹ ^ 4) := by
    fin_cases p
    · exact absurd rfl hp
    · exact hN 1 (Or.inl rfl)
    · exact hN 2 (Or.inr rfl)
    · exact hK.upper
  set C'' := max C' 1
  have hC'' : 0 < C'' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlow : ∀ᶠ N in atTop, ENNReal.ofReal (c / C'' * Real.log N ^ 4) ≤
      Zpos μ A φ χ 0 N / Zpos μ A φ χ p N := by
    filter_upwards [eventually_ge_atTop (max (max N₀ N₁) (max N₂ 1))] with N hN
    have hN0 : N₀ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
    have hN1 : N₁ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
    have hN2 : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
    have hN3 : 1 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
    have hNpos : 0 < N := by linarith
    have hpos : Zpos μ A φ χ p N ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) (hlo N hN1))
    have hfin : Zpos μ A φ χ p N ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hhi N hN2)
    rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hfin)]
    have hlog : 0 ≤ Real.log N := Real.log_nonneg hN3
    calc ENNReal.ofReal (c / C'' * Real.log N ^ 4) * Zpos μ A φ χ p N
        ≤ ENNReal.ofReal (c / C'' * Real.log N ^ 4) * ENNReal.ofReal (C'' * N⁻¹ ^ 4) := by
          refine mul_le_mul' le_rfl ((hhi N hN2).trans (ENNReal.ofReal_le_ofReal ?_))
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = ENNReal.ofReal (c * N⁻¹ ^ 4 * Real.log N ^ 4) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp
      _ ≤ Zpos μ A φ χ 0 N := (h N hN0).1
  have hlim : Tendsto (fun N : ℝ => ENNReal.ofReal (c / C'' * Real.log N ^ 4)) atTop (𝓝 ⊤) := by
    refine ENNReal.tendsto_ofReal_atTop.comp ?_
    refine Tendsto.const_mul_atTop (div_pos hc hC'') ?_
    exact (tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  exact tendsto_nhds_top_mono hlim hlow

/-- **Gaussian form of the main theorem**: standard Gaussian inputs. -/
theorem mainTheorem_shear_gaussian {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) :
    ∃ r : ℝ, 0 < r ∧ ∀ (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ p : Fin 4, ∀ᶠ θ in 𝓝 (basePos A p), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ThmK stdGauss2 A φ χ → ThmN stdGauss2 A φ χ →
      VectorSLT.SLT.HasLaplacePair (Zpos stdGauss2 A φ χ 0) 4 5 ∧
        VectorSLT.SLT.HasLaplacePair (Zpos stdGauss2 A φ χ 1) 4 1 ∧
        VectorSLT.SLT.HasLaplacePair (Zpos stdGauss2 A φ χ 2) 4 1 ∧
        VectorSLT.SLT.HasLaplacePair (Zpos stdGauss2 A φ χ 3) 4 1 := by
  obtain ⟨r, hr, h⟩ := mainTheorem_shear hA
  exact ⟨r, hr, fun φ χ φ₀ χ₀ π₁ => h stdGauss2 (fun i => stdGauss2_moments _ i)
    (lo := fun _ => -1) (hi := fun _ => 1) (fun _ => by norm_num) (pow_pos cG_pos 2)
    stdGauss2_density φ χ⟩

end VectorSLT
