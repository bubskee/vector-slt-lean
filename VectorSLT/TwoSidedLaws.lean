/-
Brief 03, O2: `Z_{N,1} ≍ N⁻⁴ (log N)⁴` without compact support.

Where compact support was used: in `ZN1_two_sided` (L6) the hypothesis `hμR` entered only
(i) to derive the 162nd moments, and (ii) in the *lower* bound `Zpos_one_lower` (through
`popLossA_le`, the compact form of (G↑)). The upper bound (`theoremM`, via `Gdown`) never used
it. Replacing (ii) by `Zpos_one_lower_moments` (L5's moment form of (G↑)) removes it entirely.
No step of the assembly genuinely needs bounded support.
-/
import VectorSLT.ShearUpper
import VectorSLT.Gaussian

namespace VectorSLT

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- **O2. `Z_{N,1} ≍ N⁻⁴ (log N)⁴` for every finite input law with finite 162nd moments and a
density bounded below on some box**, at every two-nonzero-row shear target. -/
theorem ZN1_two_sided_moments {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ᶠ θ in 𝓝 (basePos A 0), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ c C N₀ : ℝ, 0 < c ∧ ∀ N : ℝ, N₀ ≤ N →
        ENNReal.ofReal (c * N⁻¹ ^ 4 * Real.log N ^ 4) ≤ Zpos μ A φ χ 0 N ∧
          Zpos μ A φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4 * Real.log N ^ 4) := by
  obtain ⟨r, hr, hup⟩ := theoremM_shear hA
  refine ⟨r, hr, ?_⟩
  intro μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ φ₀ χ₀ π₁ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs
  obtain ⟨c, hc, N₁, hlow⟩ := Zpos_one_lower_moments hA μ hmom φ χ hφ₀ hχ₀ hφl hχl
  obtain ⟨C, N₂, hu⟩ := hup μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs
  exact ⟨c, C, max N₁ N₂, hc, fun N hN =>
    ⟨hlow N ((le_max_left _ _).trans hN), hu N ((le_max_right _ _).trans hN)⟩⟩

/-! ### The Gaussian instance: a density lower bound on `[-1,1]²` -/

/-- The constant `c₁ = e^{-1/2}/√(2π)`, the minimum of the standard normal density on
`[-1,1]`. -/
noncomputable def cG : ℝ := (√(2 * Real.pi))⁻¹ * Real.exp (-(1 / 2))

theorem cG_pos : 0 < cG := by unfold cG; positivity

theorem gauss1_lower :
    ENNReal.ofReal cG • volume.restrict (Icc (-1 : ℝ) 1) ≤ gaussianReal 0 1 := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, Measure.le_iff]
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply hs, withDensity_apply _ hs, smul_eq_mul,
    ← setLIntegral_const]
  calc ∫⁻ _ in s ∩ Icc (-1) 1, ENNReal.ofReal cG
      ≤ ∫⁻ x in s ∩ Icc (-1) 1, gaussianPDF 0 1 x :=
        setLIntegral_mono (measurable_gaussianPDF 0 1) fun x hx => by
          rw [gaussianPDF]
          apply ENNReal.ofReal_le_ofReal
          have hx2 : x ^ 2 ≤ 1 := by
            have := hx.2; rw [mem_Icc] at this; nlinarith
          rw [gaussianPDFReal]
          simp only [NNReal.coe_one, mul_one, sub_zero, cG]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.exp_le_exp.mpr
          linarith
    _ ≤ ∫⁻ x in s, gaussianPDF 0 1 x := lintegral_mono_set inter_subset_left

/-- **The standard Gaussian on `ℝ²` has density `≥ c₁²` on `[-1,1]²`.** -/
theorem stdGauss2_density :
    ENNReal.ofReal (cG ^ 2) • volume.restrict (cbox (fun _ => -1) (fun _ => 1)) ≤ stdGauss2 := by
  have hc := cG_pos.le
  set I := Icc (-1 : ℝ) 1
  have hprod : (ENNReal.ofReal cG • volume.restrict I).prod (ENNReal.ofReal cG • volume.restrict I)
      ≤ (gaussianReal 0 1).prod (gaussianReal 0 1) := Measure.prod_mono gauss1_lower gauss1_lower
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.prod_restrict] at hprod
  set e := MeasurableEquiv.finTwoArrow (α := ℝ)
  have hG : MeasurePreserving e stdGauss2 ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    measurePreserving_finTwoArrow _
  have hV : MeasurePreserving e volume (volume : Measure (ℝ × ℝ)) :=
    volume_preserving_finTwoArrow ℝ
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
  set t := e.symm ⁻¹' s
  have ht : MeasurableSet t := e.symm.measurable hs
  have hst : e ⁻¹' t = s := by ext x; simp [t]
  have hcb : cbox (fun _ => -1) (fun _ => 1) = e ⁻¹' (I ×ˢ I) := by
    ext x
    simp only [cbox, Set.mem_univ_pi, mem_Icc, Fin.forall_fin_two, mem_preimage, mem_prod, e,
      MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo, I]
    tauto
  have hsc : s ∩ cbox (fun _ => -1) (fun _ => 1) = e ⁻¹' (t ∩ I ×ˢ I) := by
    rw [preimage_inter, ← hcb, hst]
  have h1 := Measure.le_iff'.mp hprod t
  rw [Measure.smul_apply, Measure.restrict_apply ht, smul_eq_mul] at h1
  rw [hsc, hV.measure_preimage_equiv, ← hst, hG.measure_preimage_equiv, ENNReal.ofReal_pow hc,
    sq]
  exact h1

/-- **O2, Gaussian instance. `Z_{N,1} ≍ N⁻⁴ (log N)⁴` for standard Gaussian inputs**, at every
two-nonzero-row shear target. -/
theorem ZN1_two_sided_gaussian {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) :
    ∃ r : ℝ, 0 < r ∧ ∀ (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ᶠ θ in 𝓝 (basePos A 0), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ c C N₀ : ℝ, 0 < c ∧ ∀ N : ℝ, N₀ ≤ N →
        ENNReal.ofReal (c * N⁻¹ ^ 4 * Real.log N ^ 4) ≤ Zpos stdGauss2 A φ χ 0 N ∧
          Zpos stdGauss2 A φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4 * Real.log N ^ 4) := by
  obtain ⟨r, hr, h⟩ := ZN1_two_sided_moments hA
  refine ⟨r, hr, fun φ χ φ₀ χ₀ π₁ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs => ?_⟩
  exact h stdGauss2 (fun i => stdGauss2_moments _ i) (lo := fun _ => -1) (hi := fun _ => 1)
    (fun _ => by norm_num) (pow_pos cG_pos 2) stdGauss2_density φ χ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs

end VectorSLT
