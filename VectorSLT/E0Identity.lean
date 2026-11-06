/-
L3: the E₀ identity (pure algebra).

* bordered determinant: `-det [[diag a, a^{⊙2}], [(a^{⊙2})ᵀ, 0]] = (∏ aᵢ) ∑ aᵢ³` for all `n`;
* null direction: `∑ (aᵢ s + c aᵢ t)³ = (∑ aᵢ³) (s + c t)³`.

Mathlib has the matrix determinant lemma only for `IsUnit A.det` (the adjugate form is a
TODO in `SchurComplement.lean`). We prove the identity on `{aᵢ ≠ 0 ∀ i}` by the Schur
complement and extend it to all `a` by continuity and density.
-/
import Mathlib

namespace VectorSLT

open Matrix Finset

variable {n : ℕ}

/-- The bordered matrix `[[diag a, a^{⊙2}], [(a^{⊙2})ᵀ, 0]]`, indexed by `Fin n ⊕ Unit`. -/
def bordered (a : Fin n → ℝ) : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  fromBlocks (diagonal a) (replicateCol Unit (fun i => a i ^ 2))
    (replicateRow Unit (fun i => a i ^ 2)) 0

theorem bordered_det_of_ne (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) :
    -(bordered a).det = (∏ i, a i) * ∑ i, a i ^ 3 := by
  have hdet : IsUnit (diagonal a).det := by
    rw [det_diagonal]; exact (Finset.prod_ne_zero_iff.mpr fun i _ => ha i).isUnit
  let _ : Invertible (diagonal a) := invertibleOfIsUnitDet _ hdet
  rw [bordered, det_fromBlocks₁₁, invOf_eq_nonsing_inv, inv_diagonal, det_diagonal]
  have hinv : Ring.inverse a = fun i => (a i)⁻¹ := by
    have hu : IsUnit a := Pi.isUnit_iff.mpr fun i => (ha i).isUnit
    funext i; simp [Ring.inverse, hu]
  rw [hinv, det_unique]
  simp only [Matrix.sub_apply, Matrix.zero_apply, zero_sub, neg_neg, mul_neg]
  congr 1
  simp only [Matrix.mul_apply, replicateRow_apply, replicateCol_apply, diagonal_apply]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_ite_eq']
  refine Finset.sum_congr rfl fun i _ => ?_
  have := ha i
  field_simp

/-- **The bordered determinant identity**, for every `n` and every `a ∈ ℝⁿ`. -/
theorem bordered_det (a : Fin n → ℝ) : -(bordered a).det = (∏ i, a i) * ∑ i, a i ^ 3 := by
  set g : ℝ → ℝ := fun ε => -(bordered (fun i => a i + ε)).det -
    (∏ i, (a i + ε)) * ∑ i, (a i + ε) ^ 3
  have hg : Continuous g := by
    have hb : Continuous fun ε : ℝ => bordered (fun i => a i + ε) := by
      refine continuous_pi fun p => continuous_pi fun q => ?_
      rcases p with p | p <;> rcases q with q | q <;>
        simp only [bordered, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
          fromBlocks_apply₂₂, diagonal_apply, replicateCol_apply, replicateRow_apply,
          Matrix.zero_apply] <;> first | fun_prop | (split_ifs <;> fun_prop)
    exact (hb.matrix_det.neg).sub (by fun_prop)
  have hzero : ∀ ε ∈ (Set.range fun i => -a i)ᶜ, g ε = 0 := by
    intro ε hε
    have hne : ∀ i, a i + ε ≠ 0 := by
      intro i h; apply hε; exact ⟨i, by linarith⟩
    simp only [g, bordered_det_of_ne _ hne, sub_self]
  have hdense : Dense (Set.range fun i => -a i)ᶜ := (Set.countable_range _).dense_compl ℝ
  have hclosed : IsClosed {ε | g ε = 0} := isClosed_eq hg continuous_const
  have h0 : g 0 = 0 := by
    have : closure (Set.range fun i => -a i)ᶜ ⊆ {ε | g ε = 0} :=
      hclosed.closure_subset_iff.mpr hzero
    exact this (hdense.closure_eq ▸ Set.mem_univ 0)
  simpa [g, sub_eq_zero] using h0

/-- **The null direction**: along `t ↦ (aᵢ, c aᵢ)`, the binary cubic collapses. -/
theorem null_direction (a : Fin n → ℝ) (s t c : ℝ) :
    ∑ i, (a i * s + c * a i * t) ^ 3 = (∑ i, a i ^ 3) * (s + c * t) ^ 3 := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

end VectorSLT
