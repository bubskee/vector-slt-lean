/-
L5, part 1: the network is a polynomial in the input of total degree ≤ 3ⁿ.
-/
import VectorSLT.Network

namespace VectorSLT

open MvPolynomial

/-- The network as a vector of polynomials in the input `x = (X 0, X 1)`. -/
noncomputable def polyNet (W : ℕ → Matrix (Fin 2) (Fin 2) ℝ) :
    ℕ → Fin 2 → MvPolynomial (Fin 2) ℝ
  | 0 => fun k => X k
  | n + 1 => fun k => polyNet W n k + (∑ j, C (W n k j) * polyNet W n j) ^ 3

theorem eval_polyNet (W : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) (x : Fin 2 → ℝ) (k : Fin 2) :
    eval x (polyNet W n k) = prefixNet W n x k := by
  induction n generalizing k with
  | zero => simp [polyNet]
  | succ n ih =>
    simp only [polyNet, map_add, map_pow, map_sum, map_mul, eval_C, ih]
    rw [prefixNet_succ, Function.comp_apply, layer_apply]
    rfl

theorem totalDegree_polyNet (W : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) (k : Fin 2) :
    (polyNet W n k).totalDegree ≤ 3 ^ n := by
  induction n generalizing k with
  | zero => simp [polyNet, totalDegree_X]
  | succ n ih =>
    simp only [polyNet]
    refine (totalDegree_add _ _).trans (max_le ((ih k).trans ?_) ?_)
    · exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n)
    · refine (totalDegree_pow _ _).trans ?_
      have hs : (∑ j, C (W n k j) * polyNet W n j).totalDegree ≤ 3 ^ n := by
        refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
        refine (totalDegree_mul _ _).trans ?_
        simp only [totalDegree_C, zero_add]; exact ih j
      rw [pow_succ]; nlinarith

/-- The target `F_A` as polynomials. -/
noncomputable def polyLayer (A : Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) : MvPolynomial (Fin 2) ℝ :=
  X k + (∑ j, C (A k j) * X j) ^ 3

theorem eval_polyLayer (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) (k : Fin 2) :
    eval x (polyLayer A k) = layer A x k := by
  simp only [polyLayer, map_add, map_pow, map_sum, map_mul, eval_C, eval_X, layer_apply]; rfl

theorem totalDegree_polyLayer (A : Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) :
    (polyLayer A k).totalDegree ≤ 3 := by
  have := totalDegree_polyNet (fun _ => A) 1 k
  simpa [polyNet, polyLayer] using this

/-- The depth-four error `h_W - F_A` is a polynomial of total degree `≤ 81 = 3⁴`. -/
theorem error_isPoly (W : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (k : Fin 2) : ∃ p : MvPolynomial (Fin 2) ℝ, p.totalDegree ≤ 81 ∧
      ∀ x, eval x p = prefixNet W 4 x k - layer A x k := by
  refine ⟨polyNet W 4 k - polyLayer A k, ?_, fun x => ?_⟩
  · refine (totalDegree_sub _ _).trans (max_le ?_ ((totalDegree_polyLayer A k).trans (by norm_num)))
    exact (totalDegree_polyNet W 4 k).trans (by norm_num)
  · rw [map_sub, eval_polyNet, eval_polyLayer]

end VectorSLT
