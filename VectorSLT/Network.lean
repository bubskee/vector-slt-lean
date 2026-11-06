/-
Milestone A: network semantics for cubic residual networks.

Paper model (cubic-chaos @ 34c531e, `results.md` §0):
  V_B(x) = (Bx)^{⊙3},  F_B = I + V_B,  h = F_{W_L} ∘ ⋯ ∘ F_{W_1}.

Brief (lean_brief_vector_01.md, milestone A): at width n and depth D,
  (G_D x)_k = x_k + ∑_{i=1}^{D} (ρ_i^{(k)} · G_{i-1} x)^3,
where ρ_i^{(k)} is row k of B_i and G_0 = id, G_i = F_{B_i} ∘ G_{i-1}.

Lean conventions:
* a state of width `n` is `Fin n → ℝ`; a weight matrix is `Matrix (Fin n) (Fin n) ℝ`;
* row k of `B` is `B k : Fin n → ℝ`, and `ρ · z` is `dotProduct`;
* the Hadamard cube `(Bz)^{⊙3}` is the pointwise power `(B *ᵥ z) ^ 3` in the Pi type;
* layers are indexed from 0: Lean's `W i` is the paper's `B_{i+1}`,
  and `prefixNet W i` is the paper's `G_i` (the first `i` layers).
-/
import Mathlib

namespace VectorSLT

open Matrix Finset

variable {n : ℕ}

/-- One cubic residual layer `F_B(z) = z + (B z)^{⊙3}`. -/
def layer (B : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) : Fin n → ℝ :=
  z + (B *ᵥ z) ^ 3

/-- Coordinate form of a layer: `F_B(z)_k = z_k + (ρ^{(k)} · z)^3`, with `ρ^{(k)} = B k`. -/
theorem layer_apply (B : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) (k : Fin n) :
    layer B z k = z k + (B k ⬝ᵥ z) ^ 3 := by
  rfl

/-- The prefix `G_i = F_{W (i-1)} ∘ ⋯ ∘ F_{W 0}` of a network whose layers, in
application order, are `W 0, W 1, W 2, …` (paper: `B_1, B_2, B_3, …`). `G_0 = id`. -/
def prefixNet (W : ℕ → Matrix (Fin n) (Fin n) ℝ) : ℕ → (Fin n → ℝ) → (Fin n → ℝ)
  | 0 => id
  | i + 1 => layer (W i) ∘ prefixNet W i

@[simp] theorem prefixNet_zero (W : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    prefixNet W 0 = id := rfl

theorem prefixNet_succ (W : ℕ → Matrix (Fin n) (Fin n) ℝ) (i : ℕ) :
    prefixNet W (i + 1) = layer (W i) ∘ prefixNet W i := rfl

/-- Fidelity check: `prefixNet W D` is literally the composition
`F_{W (D-1)} ∘ ⋯ ∘ F_{W 0}` of the list of layer maps, applied first-to-last. -/
theorem prefixNet_eq_foldl (W : ℕ → Matrix (Fin n) (Fin n) ℝ) (D : ℕ) :
    prefixNet W D =
      ((List.range D).map fun i => layer (W i)).foldl (fun g f => f ∘ g) id := by
  induction D with
  | zero => rfl
  | succ D ih => rw [List.range_succ, List.map_append, List.foldl_append, ← ih]; rfl

/-- **Milestone A (sum of cubes), 0-indexed form.** For every width `n`, every depth `D`
and every sequence of weights, output `k` of the depth-`D` network is the input
coordinate plus one cube per layer, the cube of row `k` of that layer applied to the
state entering it. -/
theorem prefixNet_apply_sum_cubes (W : ℕ → Matrix (Fin n) (Fin n) ℝ) (D : ℕ)
    (x : Fin n → ℝ) (k : Fin n) :
    prefixNet W D x k = x k + ∑ i ∈ range D, (W i k ⬝ᵥ prefixNet W i x) ^ 3 := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [prefixNet_succ, Function.comp_apply, layer_apply, ih, sum_range_succ, add_assoc]

/-- **Milestone A, paper indexing.** With `B i := W (i - 1)` for `1 ≤ i ≤ D` and
`G i := prefixNet W i`,
`(G_D x)_k = x_k + ∑_{i=1}^{D} (ρ_i^{(k)} · G_{i-1} x)^3`. -/
theorem prefixNet_apply_sum_cubes_Icc (W : ℕ → Matrix (Fin n) (Fin n) ℝ) (D : ℕ)
    (x : Fin n → ℝ) (k : Fin n) :
    prefixNet W D x k =
      x k + ∑ i ∈ Icc 1 D, (W (i - 1) k ⬝ᵥ prefixNet W (i - 1) x) ^ 3 := by
  rw [prefixNet_apply_sum_cubes, ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp [add_comm 1]

/-! ### Finitely many layers -/

/-- Extend a `Fin D`-indexed weight list by zero matrices (never reached below depth `D`). -/
def extendWeights {D : ℕ} (B : Fin D → Matrix (Fin n) (Fin n) ℝ) :
    ℕ → Matrix (Fin n) (Fin n) ℝ :=
  fun i => if h : i < D then B ⟨i, h⟩ else 0

/-- The depth-`D` network `G_D = F_{B_{D-1}} ∘ ⋯ ∘ F_{B_0}` with exactly `D` weight matrices. -/
def network {D : ℕ} (B : Fin D → Matrix (Fin n) (Fin n) ℝ) : (Fin n → ℝ) → (Fin n → ℝ) :=
  prefixNet (extendWeights B) D

/-- The network with `D` weights is the composition of its `D` layers, first layer first. -/
theorem network_eq_foldl {D : ℕ} (B : Fin D → Matrix (Fin n) (Fin n) ℝ) :
    network B = (List.ofFn fun i => layer (B i)).foldl (fun g f => f ∘ g) id := by
  rw [network, prefixNet_eq_foldl]
  congr 1
  apply List.ext_get <;> simp [extendWeights]
  intro m hm; simp [hm]

/-- **Milestone A, `Fin D` form.** Each summand uses only the true weight `B i` and the
prefix `G_i` made of the layers strictly before `i`. -/
theorem network_apply_sum_cubes {D : ℕ} (B : Fin D → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (k : Fin n) :
    network B x k = x k + ∑ i : Fin D, (B i k ⬝ᵥ prefixNet (extendWeights B) i x) ^ 3 := by
  rw [network, prefixNet_apply_sum_cubes, ← Fin.sum_univ_eq_sum_range]
  simp [extendWeights]

/-- The prefixes used inside `network B` depend only on the weights strictly before `i`. -/
theorem prefixNet_congr (W W' : ℕ → Matrix (Fin n) (Fin n) ℝ) (i : ℕ)
    (h : ∀ j < i, W j = W' j) : prefixNet W i = prefixNet W' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [prefixNet_succ, prefixNet_succ, h i (Nat.lt_succ_self i),
      ih fun j hj => h j (Nat.lt_succ_of_lt hj)]

/-! ### Width two, depth four: the paper's (M2) -/

/-- The normalized shear active matrix `A₀ = [[1, -1], [1, -1]]` of Theorem H §2. -/
def A0 : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 1, -1]

/-- Fidelity check of the target: `F_{A₀}(x, y) = (x + ℓ³, y + ℓ³)` with `ℓ = x - y`. -/
theorem layer_A0 (x : Fin 2 → ℝ) :
    layer A0 x = ![x 0 + (x 0 - x 1) ^ 3, x 1 + (x 0 - x 1) ^ 3] := by
  ext k; fin_cases k <;> simp [layer_apply, A0, dotProduct, Fin.sum_univ_two] <;> ring

/-- Active-row coordinates (Theorem M §2): `m₁ x + m₂ y = α s + ν t` with `s = x - y`,
`t = y`, `α = m₁`, `ν = m₁ + m₂`. -/
theorem active_row_coords (m : Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    m ⬝ᵥ x = m 0 * (x 0 - x 1) + (m 0 + m 1) * x 1 := by
  simp [dotProduct, Fin.sum_univ_two]; ring

/-- Inactive-row coordinates (Theorem M §2): the raw row `(a, b - a)` sends `z` to
`a (z₁ - z₂) + b z₂`. -/
theorem inactive_row_coords (a b : ℝ) (z : Fin 2 → ℝ) :
    ![a, b - a] ⬝ᵥ z = a * (z 0 - z 1) + b * z 1 := by
  simp [dotProduct, Fin.sum_univ_two]; ring

/-- **(M2), Lean form.** At width two and depth four, with the active block first
(`W 0 = M`) followed by `W 1, W 2, W 3` (paper: `B₁, B₂, B₃`), output `k` minus the target
output `F_{A₀,k}` is the sum of four cubes `λ_i^{(k)} = ρ_i^{(k)} · G_{i-1}` minus `s³`. -/
theorem M2_error (W : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) (k : Fin 2) :
    prefixNet W 4 x k - layer A0 x k =
      ∑ i ∈ range 4, (W i k ⬝ᵥ prefixNet W i x) ^ 3 - (x 0 - x 1) ^ 3 := by
  have hA : layer A0 x k = x k + (x 0 - x 1) ^ 3 := by
    rw [layer_A0]; fin_cases k <;> rfl
  rw [prefixNet_apply_sum_cubes, hA]; ring

end VectorSLT
