/-
(b) A concrete Gaussian input law: two independent standard normals on `Fin 2 → ℝ`.
It has finite 162nd moments, so `propLprime_moments` and `separation_moments` apply.
-/
import VectorSLT.GeneralInput

namespace VectorSLT

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- The standard Gaussian law on `ℝ²`: `N(0,1) ⊗ N(0,1)`. -/
noncomputable def stdGauss2 : Measure (Fin 2 → ℝ) := Measure.pi fun _ => gaussianReal 0 1

instance : IsProbabilityMeasure stdGauss2 := by unfold stdGauss2; infer_instance

theorem stdGauss2_moments (n : ℕ) (i : Fin 2) :
    Integrable (fun x : Fin 2 → ℝ => |x i| ^ n) stdGauss2 := by
  have h1 : Integrable (fun x : ℝ => ‖id x‖ ^ ((n : ENNReal).toReal)) (gaussianReal 0 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (memLp_id_gaussianReal' (n : ENNReal) (ENNReal.natCast_ne_top n)).integrable_norm_rpow
        (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)
  have h2 : Integrable (fun x : ℝ => |x| ^ n) (gaussianReal 0 1) := by
    simpa [Real.norm_eq_abs, Real.rpow_natCast] using h1
  have hmp := measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) i
  exact hmp.integrable_comp_of_integrable h2

/-- **Proposition L′ for Gaussian inputs**, every two-nonzero-row shear target. -/
theorem propLprime_gaussian {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A)
    {π₀ : ℝ} (hπ₀ : 0 < π₀) (π : Raw16 → ENNReal)
    (hπ : ∀ᶠ θ in 𝓝 (baseA A), ENNReal.ofReal π₀ ≤ π θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ENNReal.ofReal (c * N⁻¹ ^ 4 * Real.log N ^ 4) ≤
        ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * popLossA stdGauss2 A θ))) * π θ :=
  propLprime_moments hA stdGauss2 (fun i => stdGauss2_moments _ i) hπ₀ π hπ

/-- **The separation for Gaussian inputs**, conditional on `ThmKUpper`. -/
theorem separation_gaussian {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A)
    (φ χ : Raw16 → ENNReal) {φ₀ χ₀ : ℝ} (hφ₀ : 0 < φ₀) (hχ₀ : 0 < χ₀)
    (hφ : ∀ᶠ θ in 𝓝 (basePos A 0), ENNReal.ofReal φ₀ ≤ φ θ)
    (hχ : ∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) (hK : ThmKUpper stdGauss2 A φ χ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₁ : ℝ, ∀ N : ℝ, N₁ ≤ N →
      ENNReal.ofReal (c * Real.log N ^ 4) * Zpos stdGauss2 A φ χ 3 N ≤ Zpos stdGauss2 A φ χ 0 N :=
  separation_moments hA stdGauss2 (fun i => stdGauss2_moments _ i) φ χ hφ₀ hχ₀ hφ hχ hK

end VectorSLT
