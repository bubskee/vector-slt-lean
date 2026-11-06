/-
L1: the separation theorem `Z_{N,1} / Z_{N,4} ≥ c (log N)⁴`, with Theorem K
(`shear_exceptional_strata.md`, (K1)) as an explicitly named hypothesis.

Same footing for both positions:
* one parameter space `Raw16` (all sixteen raw weights) with Lebesgue measure;
* one loss: the population loss of one input law `μ` against one target `F_A`;
* one prior `φ` and one cutoff profile `χ`, translated to the base point of each position:
  `π_p(θ) = φ(θ) · χ(θ - θ₀⁽ᵖ⁾)`.
The positions differ only in which realization of `F_A` the cutoff localizes at.
-/
import VectorSLT.Normalization

namespace VectorSLT

open MeasureTheory Set Filter Topology

/-- The population loss for target `F_A`: `K(θ) = E_μ ‖h_θ(x) - F_A(x)‖²`. -/
noncomputable def popLossA (μ : Measure (Fin 2 → ℝ)) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (θ : Raw16) : ℝ :=
  ∫ x, ∑ k, (net θ x k - layer A x k) ^ 2 ∂μ

/-- The realization of `F_A` with the active block at position `p+1` (Lean's `p : Fin 4`
counts from 0 in application order) and the other three blocks zero. -/
def basePos (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4) : Raw16 :=
  ofEnt fun i j => (if p = 0 then A i j else 0,
    (if p = 1 then A i j else 0, if p = 2 then A i j else 0, if p = 3 then A i j else 0))

theorem basePos_zero (A : Matrix (Fin 2) (Fin 2) ℝ) : basePos A 0 = baseA A := by
  simp [basePos, baseA, ofEnt]

theorem weights_basePos (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4) (q : ℕ) (hq : q < 4) :
    weights (basePos A p) q = if q = p.val then A else 0 := by
  ext i j
  rcases q with _ | m
  · rw [weights_zero_ent, basePos, ent_ofEnt]
    fin_cases p <;> simp
  · rw [weights_succ_ent, basePos, ent_ofEnt]
    have hm : m < 3 := by omega
    fin_cases p <;> interval_cases m <;> simp [tri]

theorem layer_zero_mat (z : Fin 2 → ℝ) : layer (0 : Matrix (Fin 2) (Fin 2) ℝ) z = z := by
  funext k; simp [layer_apply]

/-- Fidelity check: every `basePos A p` realizes the target exactly. -/
theorem net_basePos (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4) (x : Fin 2 → ℝ) :
    net (basePos A p) x = layer A x := by
  have hw := weights_basePos A p
  simp only [net, prefixNet, Function.comp_apply, id]
  rw [hw 0 (by norm_num), hw 1 (by norm_num), hw 2 (by norm_num), hw 3 (by norm_num)]
  fin_cases p <;> simp [layer_zero_mat]

/-- The localized integral at position `p+1`:
`Z_{N,p+1} = ∫ e^{-N K(θ)} φ(θ) χ(θ - θ₀⁽ᵖ⁺¹⁾) dθ`. -/
noncomputable def Zpos (μ : Measure (Fin 2 → ℝ)) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (φ χ : Raw16 → ENNReal) (p : Fin 4) (N : ℝ) : ENNReal :=
  ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * popLossA μ A θ))) * (φ θ * χ (θ - basePos A p))

/-- **Theorem K, (K1), as a hypothesis**: `c N⁻⁴ ≤ Z_{N,4} ≤ C N⁻⁴` for large `N`. -/
def ThmK (μ : Measure (Fin 2 → ℝ)) (A : Matrix (Fin 2) (Fin 2) ℝ) (φ χ : Raw16 → ENNReal) :
    Prop :=
  ∃ c C N₀ : ℝ, 0 < c ∧ ∀ N, N₀ ≤ N →
    ENNReal.ofReal (c * N⁻¹ ^ 4) ≤ Zpos μ A φ χ 3 N ∧ Zpos μ A φ χ 3 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4)

/-- The upper half of (K1), which is all the separation inequality uses. -/
def ThmKUpper (μ : Measure (Fin 2 → ℝ)) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (φ χ : Raw16 → ENNReal) : Prop :=
  ∃ C N₀ : ℝ, ∀ N, N₀ ≤ N → Zpos μ A φ χ 3 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4)

theorem ThmK.upper {μ A φ χ} (h : ThmK μ A φ χ) : ThmKUpper μ A φ χ := by
  obtain ⟨c, C, N₀, -, h⟩ := h
  exact ⟨C, N₀, fun N hN => (h N hN).2⟩

/-- (G↑) for the population loss of a law supported in the box, `Λ = 2`. -/
theorem popLossA_le {μ : Measure (Fin 2 → ℝ)} [IsProbabilityMeasure μ] {R : ℝ}
    (hμ : ∀ᵐ x ∂μ, ∀ i, |x i| ≤ R) (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) (M : ℝ)
    (hM : 0 ≤ M) (hbd : ∀ x : Fin 2 → ℝ, (∀ i, |x i| ≤ R) →
      ∀ k, |net θ x k - layer A x k| ≤ M) : popLossA μ A θ ≤ 2 * M ^ 2 := by
  unfold popLossA
  have hle : ∀ᵐ x ∂μ, ∑ k, (net θ x k - layer A x k) ^ 2 ≤ 2 * M ^ 2 := by
    filter_upwards [hμ] with x hx
    rw [Fin.sum_univ_two]
    have h0 := sq_le_sq' (abs_le.mp (hbd x hx 0)).1 (abs_le.mp (hbd x hx 0)).2
    have h1 := sq_le_sq' (abs_le.mp (hbd x hx 1)).1 (abs_le.mp (hbd x hx 1)).2
    linarith
  calc ∫ x, ∑ k, (net θ x k - layer A x k) ^ 2 ∂μ ≤ ∫ _x, 2 * M ^ 2 ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
          (integrable_const _) hle
    _ = 2 * M ^ 2 := by simp

/-- **The four-log lower bound at position one**, on the common footing. -/
theorem Zpos_one_lower {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) {R : ℝ}
    (μ : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, ∀ i, |x i| ≤ R)
    (φ χ : Raw16 → ENNReal) {φ₀ χ₀ : ℝ} (hφ₀ : 0 < φ₀) (hχ₀ : 0 < χ₀)
    (hφ : ∀ᶠ θ in 𝓝 (basePos A 0), ENNReal.ofReal φ₀ ≤ φ θ)
    (hχ : ∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ENNReal.ofReal (c * N⁻¹ ^ 4 * Real.log N ^ 4) ≤ Zpos μ A φ χ 0 N := by
  have hπ : ∀ᶠ θ in 𝓝 (baseA A), ENNReal.ofReal (φ₀ * χ₀) ≤ φ θ * χ (θ - basePos A 0) := by
    rw [← basePos_zero]
    have ht : Tendsto (fun θ => θ - basePos A 0) (𝓝 (basePos A 0)) (𝓝 0) := by
      have hc : Continuous fun θ : Raw16 => θ - basePos A 0 := by fun_prop
      have := hc.tendsto (basePos A 0)
      simpa using this
    filter_upwards [hφ, ht.eventually hχ] with θ h1 h2
    rw [ENNReal.ofReal_mul hφ₀.le]
    exact mul_le_mul' h1 h2
  exact propLprime_shear hA (mul_pos hφ₀ hχ₀) (popLossA μ A) (Λ := 2)
    (fun θ M hM hbd => popLossA_le hμ A θ M hM hbd) _ hπ

/-- **L1. The separation theorem.** Assume Theorem K's upper bound at position four
(`ThmKUpper`). Then for the same input law, prior and cutoff profile,
`(c log⁴ N) · Z_{N,4} ≤ Z_{N,1}` for all large `N`. -/
theorem separation {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) {R : ℝ}
    (μ : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, ∀ i, |x i| ≤ R)
    (φ χ : Raw16 → ENNReal) {φ₀ χ₀ : ℝ} (hφ₀ : 0 < φ₀) (hχ₀ : 0 < χ₀)
    (hφ : ∀ᶠ θ in 𝓝 (basePos A 0), ENNReal.ofReal φ₀ ≤ φ θ)
    (hχ : ∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ)
    (hK : ThmKUpper μ A φ χ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₁ : ℝ, ∀ N : ℝ, N₁ ≤ N →
      ENNReal.ofReal (c * Real.log N ^ 4) * Zpos μ A φ χ 3 N ≤ Zpos μ A φ χ 0 N := by
  obtain ⟨c₁, hc₁, N₀, h1⟩ := Zpos_one_lower hA μ hμ φ χ hφ₀ hχ₀ hφ hχ
  obtain ⟨C, N₄, h4⟩ := hK
  set C' := max C 1
  have hC' : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨c₁ / C', div_pos hc₁ hC', max (max N₀ N₄) 1, fun N hN => ?_⟩
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN4 : N₄ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hNinv : 0 ≤ N⁻¹ := inv_nonneg.mpr (by linarith)
  calc ENNReal.ofReal (c₁ / C' * Real.log N ^ 4) * Zpos μ A φ χ 3 N
      ≤ ENNReal.ofReal (c₁ / C' * Real.log N ^ 4) * ENNReal.ofReal (C' * N⁻¹ ^ 4) := by
        gcongr
        exact (h4 N hN4).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
    _ = ENNReal.ofReal (c₁ * N⁻¹ ^ 4 * Real.log N ^ 4) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp
    _ ≤ Zpos μ A φ χ 0 N := h1 N hN0

/-- **The ratio diverges**: with all of (K1) (so `0 < Z_{N,4} < ∞`),
`Z_{N,1} / Z_{N,4} → ∞`. -/
theorem separation_tendsto {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) {R : ℝ}
    (μ : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, ∀ i, |x i| ≤ R)
    (φ χ : Raw16 → ENNReal) {φ₀ χ₀ : ℝ} (hφ₀ : 0 < φ₀) (hχ₀ : 0 < χ₀)
    (hφ : ∀ᶠ θ in 𝓝 (basePos A 0), ENNReal.ofReal φ₀ ≤ φ θ)
    (hχ : ∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ)
    (hK : ThmK μ A φ χ) :
    Tendsto (fun N => Zpos μ A φ χ 0 N / Zpos μ A φ χ 3 N) atTop (𝓝 ⊤) := by
  obtain ⟨c, hc, N₁, hsep⟩ := separation hA μ hμ φ χ hφ₀ hχ₀ hφ hχ hK.upper
  obtain ⟨c₄, C₄, N₄, hc₄, hK4⟩ := hK
  have hlow : ∀ᶠ N in atTop, ENNReal.ofReal (c * Real.log N ^ 4) ≤
      Zpos μ A φ χ 0 N / Zpos μ A φ χ 3 N := by
    filter_upwards [eventually_ge_atTop (max (max N₁ N₄) 1)] with N hN
    have hN1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
    have hN4 : N₄ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
    have hNpos : 0 < N := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hN)
    obtain ⟨hlo, hhi⟩ := hK4 N hN4
    have hpos : Zpos μ A φ χ 3 N ≠ 0 := by
      refine ne_of_gt (lt_of_lt_of_le ?_ hlo)
      exact ENNReal.ofReal_pos.mpr (by positivity)
    have hfin : Zpos μ A φ χ 3 N ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hhi
    rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hfin)]
    exact hsep N hN1
  have hlim : Tendsto (fun N : ℝ => ENNReal.ofReal (c * Real.log N ^ 4)) atTop (𝓝 ⊤) := by
    refine ENNReal.tendsto_ofReal_atTop.comp ?_
    refine Tendsto.const_mul_atTop hc ?_
    exact (tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  exact tendsto_nhds_top_mono hlim hlow

end VectorSLT
