/-
Paper 2, Appendices A.3 and F: the absorption step, in an abstract form used at every position.

The paper writes the network error as `𝒟 v + E` with `𝒟` an injective linear map and
`‖E‖ ≤ C ‖Δ‖ ‖v‖`, and absorbs `E` for small `‖Δ‖`. We use an equivalent and more convenient
form. The error is written *exactly* as `M_η v`, where `v` is the vector of retained variables,
`M_η` is linear in `v`, and `η ↦ M_η` is continuous with `M_{η₀} = 𝒟`. A continuous family of
linear maps on a finite-dimensional space that is injective at `η₀` stays uniformly injective
near `η₀` (`uniform_lower_of_linear`). This replaces the remainder bound `‖E‖ ≤ C‖Δ‖‖v‖`.
-/
import Mathlib

namespace VectorSLT.IdentityGroup.Pairs

open Filter Topology

variable {X V F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Perturbation of an injective linear map.** If `x ↦ M x` is a family of continuous linear
maps on a finite-dimensional space, continuous at `x₀`, and `M x₀` is injective, then there is
`c > 0` with `c ‖v‖ ≤ ‖M x v‖` for all `v` and all `x` near `x₀`. -/
theorem uniform_lower_of_continuousAt (M : X → V →L[ℝ] F) {x₀ : X} (hM : ContinuousAt M x₀)
    (hinj : Function.Injective (M x₀)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in 𝓝 x₀, ∀ v, c * ‖v‖ ≤ ‖M x v‖ := by
  obtain ⟨K, hK, hanti⟩ :=
    (LinearMap.injective_iff_antilipschitz (M x₀ : V →ₗ[ℝ] F)).mp hinj
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  set σ : ℝ := (K : ℝ)⁻¹
  have hσ : 0 < σ := inv_pos.mpr hK'
  have hlow : ∀ v, σ * ‖v‖ ≤ ‖M x₀ v‖ := by
    intro v
    have h := hanti.le_mul_dist v 0
    rw [dist_zero_right, map_zero, dist_zero_right] at h
    rw [inv_mul_le_iff₀ hK']; exact h
  refine ⟨σ / 2, half_pos hσ, ?_⟩
  have hnear : ∀ᶠ x in 𝓝 x₀, ‖M x - M x₀‖ < σ / 2 := by
    have := hM.eventually (Metric.ball_mem_nhds (M x₀) (half_pos hσ))
    filter_upwards [this] with x hx
    rwa [dist_eq_norm] at hx
  filter_upwards [hnear] with x hx v
  have h1 : ‖(M x - M x₀) v‖ ≤ σ / 2 * ‖v‖ :=
    ((M x - M x₀).le_opNorm v).trans (mul_le_mul_of_nonneg_right hx.le (norm_nonneg _))
  have h2 : ‖M x₀ v‖ ≤ ‖M x v‖ + ‖(M x - M x₀) v‖ := by
    have e : M x₀ v = M x v - (M x - M x₀) v := by simp
    rw [e]; exact norm_sub_le _ _
  linarith [hlow v]

/-- **The absorption lemma, linear-map form.** A family `x ↦ M x` of linear maps on a
finite-dimensional space such that every `x ↦ M x v` is continuous, and `M x₀` injective, is
uniformly injective near `x₀`. -/
theorem uniform_lower_of_linear (M : X → V →ₗ[ℝ] F) (hM : ∀ v, Continuous fun x => M x v)
    {x₀ : X} (hinj : Function.Injective (M x₀)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in 𝓝 x₀, ∀ v, c * ‖v‖ ≤ ‖M x v‖ := by
  set M' : X → V →L[ℝ] F := fun x => LinearMap.toContinuousLinearMap (M x)
  have hcont : Continuous M' := continuous_clm_apply.mpr fun v => by
    simpa [M'] using hM v
  have hinj' : Function.Injective (M' x₀) := by simpa [M'] using hinj
  obtain ⟨c, hc, h⟩ := uniform_lower_of_continuousAt M' hcont.continuousAt hinj'
  exact ⟨c, hc, h.mono fun x hx v => by simpa [M'] using hx v⟩

end VectorSLT.IdentityGroup.Pairs
