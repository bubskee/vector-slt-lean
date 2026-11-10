/-
Loss comparison at position four (Lean `p = 3`, empty suffix): the inactive function `G₄`, its
weighted homogeneity (item 3) and the comparison `κ (‖𝐜‖² + G₄(w)) ≤ K` (item 2).

The six inactive generators `leadingMap (w4 V) = (F₀, F₁, Q₁, Φ(B), Q₂, Φ(D))` are the weight-three
parts of six exact error coefficients: `s⁵` and `s⁴t` of row `0`, and `st²`, `t³` of both rows.
These coefficients still contain the active entries. They are removed exactly, without an inverse
function theorem: with `u = α³` and `m = α²ν` for the active row,
* `c₃ = u - 1 + P₀` and `c₂ = 3m + 3P₁` (all moments over the three inactive blocks);
* `α³ [st²]/3 = m² + u P₂`, `α⁶ [t³] = m³ + u² P₃`, `[s⁵]/3 = W₅/3 + u D₀ + m q₀`,
  `α³ [s⁴t]/9 = (u W₄ + 9u² D₁ + 9um q₁ + 6um D₀ + 6m² q₀)/9`
  (`q_i = P_i⁽¹⁾`, `D_i = P_i⁽⁰⁾ - P_i⁽¹⁾`, `W₅`, `W₄` the prefix-internal terms of weight six).
Substituting `u ↦ 1 - P₀`, `m ↦ -P₁` (that is, `𝐜 = 0`) gives polynomials `ĝᵢ(w)` in the inactive
entries alone, and `ĝᵢ = Aᵢ fᵢ + Bᵢ c₃ + Dᵢ c₂` with polynomial `Aᵢ, Bᵢ, Dᵢ` (`ghat_*_eq`). On a
compact ball the multipliers are bounded, so `ĝᵢ² ≲ fᵢ² + c₃² + c₂²`, and (G↓) for the ten
coefficients gives the comparison. `G₄ = ∑ ĝᵢ²`.
-/
import VectorSLT.LossCompare.ChangeVar

namespace VectorSLT.LossCompare

open MeasureTheory Set Filter Metric Topology VectorSLT VectorSLT.LeadingMap
open scoped ENNReal

/-! ### Moments of the inactive blocks -/

section Moments

variable (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ)

/-- `P_i⁽ᵏ⁾ = ∑_l a_l^{3-i} b_l^i` over the three inactive blocks (row `k`). -/
def Pm (k : Fin 2) (i : ℕ) : ℝ := mom V Finset.univ k i
/-- `D_i = P_i⁽⁰⁾ - P_i⁽¹⁾`. -/
def Dm (i : ℕ) : ℝ := Pm V 0 i - Pm V 1 i

/-- The four blocks with zero active block last (position four). -/
def ext4 : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ := ![V 0, V 1, V 2, 0]

/-- `W₅`: the prefix-internal (weight-six) part of the `s⁵` coefficient of row `0`. -/
def W5 : ℝ := e50 (ext4 V) 0
/-- `W₄`: the prefix-internal (weight-six) part of the `s⁴t` coefficient of row `0`. -/
def W4 : ℝ := e41 (ext4 V) 0

end Moments

theorem rowForm_smul (r : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) :
    rowForm (r • B) k = (r * (rowForm B k).1, r * (rowForm B k).2) := by
  simp [rowForm]; ring

theorem Pm_smul (r : ℝ) (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) (i : ℕ) (hi : i ≤ 3) :
    Pm (r • V) k i = r ^ 3 * Pm V k i := by
  simp only [Pm, mom, Pi.smul_apply, rowForm_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_pow, mul_pow]
  have : r ^ (3 - i) * r ^ i = r ^ 3 := by rw [← pow_add, Nat.sub_add_cancel hi]
  linear_combination ((rowForm (V l) k).1 ^ (3 - i) * (rowForm (V l) k).2 ^ i) * this

theorem W5_smul (r : ℝ) (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) : W5 (r • V) = r ^ 6 * W5 V := by
  simp only [W5, e50, etaW, yW, ext4, rA, rB, Fin.sum_univ_four, Finset.sum_filter, Pi.smul_apply]
  simp [rowForm]
  ring

theorem W4_smul (r : ℝ) (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) : W4 (r • V) = r ^ 6 * W4 V := by
  simp only [W4, e41, etaW, yW, etaW', yW', ext4, rA, rB, Fin.sum_univ_four, Finset.sum_filter,
    Pi.smul_apply]
  simp [rowForm]
  ring

/-! ### The six components `h₄(r, V)` -/

section Comps

variable (r : ℝ) (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ)

/-- From `s⁵` (row `0`): `r³ W₅/3 + (1 - r³P₀⁽⁰⁾) D₀ - r³ P₁⁽⁰⁾ q₀`; at `r = 0` it is `F₀ = D₀`. -/
noncomputable def hS5 : ℝ := r ^ 3 * W5 V / 3 + (1 - r ^ 3 * Pm V 0 0) * Dm V 0 - r ^ 3 * Pm V 0 1 * Pm V 1 0

/-- From `s⁴t` (row `0`); at `r = 0` it is `F₁ = D₁`. -/
noncomputable def hS4 : ℝ :=
  ((1 - r ^ 3 * Pm V 0 0) * r ^ 3 * W4 V + 9 * (1 - r ^ 3 * Pm V 0 0) ^ 2 * Dm V 1 -
    9 * r ^ 3 * (1 - r ^ 3 * Pm V 0 0) * Pm V 0 1 * Pm V 1 1 -
    6 * r ^ 3 * (1 - r ^ 3 * Pm V 0 0) * Pm V 0 1 * Dm V 0 +
    6 * r ^ 6 * Pm V 0 1 ^ 2 * Pm V 1 0) / 9

/-- From `st²` (row `k`): `r³ (P₁⁽ᵏ⁾)² + (1 - r³P₀⁽ᵏ⁾) P₂⁽ᵏ⁾`; at `r = 0` it is `P₂⁽ᵏ⁾`. -/
def hST (k : Fin 2) : ℝ := r ^ 3 * Pm V k 1 ^ 2 + (1 - r ^ 3 * Pm V k 0) * Pm V k 2

/-- From `t³` (row `k`): `-r⁶ (P₁⁽ᵏ⁾)³ + (1 - r³P₀⁽ᵏ⁾)² P₃⁽ᵏ⁾`; at `r = 0` it is `P₃⁽ᵏ⁾`. -/
def hT3 (k : Fin 2) : ℝ := -(r ^ 6 * Pm V k 1 ^ 3) + (1 - r ^ 3 * Pm V k 0) ^ 2 * Pm V k 3

/-- The six components, in the order of `leadingMap`: `(F₀, F₁, Q₁, Φ(B), Q₂, Φ(D))`. -/
noncomputable def h4 : Fin 6 → ℝ := ![hS5 r V, hS4 r V, hST r V 0, hT3 r V 0, hST r V 1, hT3 r V 1]

end Comps

/-- **The radial part `H₄(r, ξ) = ∑ᵢ h₄(r, ξ)ᵢ²`.** -/
noncomputable def H4 (r : ℝ) (ξ : Fin 12 → ℝ) : ℝ := ∑ i, h4 r (unflat ξ) i ^ 2

/-- **The inactive function `G₄(w) = H₄(1, w) = ∑ᵢ ĝᵢ(w)²`**, a sum of six squares of
polynomials in the twelve inactive entries. -/
noncomputable def G4 (ξ : Fin 12 → ℝ) : ℝ := H4 1 ξ

section Smul

variable (r : ℝ) (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ)

theorem hS5_smul : hS5 1 (r • V) = r ^ 3 * hS5 r V := by
  simp only [hS5, Dm, W5_smul, Pm_smul r V _ _ (by norm_num : (0 : ℕ) ≤ 3),
    Pm_smul r V _ _ (by norm_num : (1 : ℕ) ≤ 3)]
  ring

theorem hS4_smul : hS4 1 (r • V) = r ^ 3 * hS4 r V := by
  simp only [hS4, Dm, W4_smul, Pm_smul r V _ _ (by norm_num : (0 : ℕ) ≤ 3),
    Pm_smul r V _ _ (by norm_num : (1 : ℕ) ≤ 3)]
  ring

theorem hST_smul (k : Fin 2) : hST 1 (r • V) k = r ^ 3 * hST r V k := by
  simp only [hST, Pm_smul r V _ _ (by norm_num : (0 : ℕ) ≤ 3),
    Pm_smul r V _ _ (by norm_num : (1 : ℕ) ≤ 3), Pm_smul r V _ _ (by norm_num : (2 : ℕ) ≤ 3)]
  ring

theorem hT3_smul (k : Fin 2) : hT3 1 (r • V) k = r ^ 3 * hT3 r V k := by
  simp only [hT3, Pm_smul r V _ _ (by norm_num : (0 : ℕ) ≤ 3),
    Pm_smul r V _ _ (by norm_num : (1 : ℕ) ≤ 3), Pm_smul r V _ _ (by norm_num : (3 : ℕ) ≤ 3)]
  ring

theorem h4_smul (i : Fin 6) : h4 1 (r • V) i = r ^ 3 * h4 r V i := by
  fin_cases i
  · exact hS5_smul r V
  · exact hS4_smul r V
  · exact hST_smul r V 0
  · exact hT3_smul r V 0
  · exact hST_smul r V 1
  · exact hT3_smul r V 1

end Smul

/-- **Item 3, weighted homogeneity**: `G₄(r ξ) = r⁶ H₄(r, ξ)` for every real `r`. -/
theorem G4_smul (r : ℝ) (ξ : Fin 12 → ℝ) : G4 (r • ξ) = r ^ 6 * H4 r ξ := by
  simp only [G4, H4, unflat_smul, h4_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem H4_nonneg (r : ℝ) (ξ : Fin 12 → ℝ) : 0 ≤ H4 r ξ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem G4_nonneg (ξ : Fin 12 → ℝ) : 0 ≤ G4 ξ := H4_nonneg 1 ξ

/-- The leading part: `h₄(0, V)` is the generator vector `leadingMap (w4 V)`. -/
theorem h4_zero (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) : h4 0 V = gens4 V := by
  funext i
  fin_cases i <;>
    simp [h4, hS5, hS4, hST, hT3, Dm, Pm, gens4, leadingMap, rowCubic, w4, cube, mom,
      Fin.sum_univ_three]

/-- **Item 3, the leading part**: `H₄(0, ξ) = ‖gens₄ ξ‖²` (Euclidean), exactly. -/
theorem H4_zero (ξ : Fin 12 → ℝ) : H4 0 ξ = ∑ i, gens4 (unflat ξ) i ^ 2 := by
  simp only [H4, h4_zero]

/-- The same with the sup norm of `ℝ⁶`: `‖gens₄ ξ‖² ≤ H₄(0, ξ) ≤ 6 ‖gens₄ ξ‖²`. -/
theorem H4_zero_bounds (ξ : Fin 12 → ℝ) :
    ‖gens4 (unflat ξ)‖ ^ 2 ≤ H4 0 ξ ∧ H4 0 ξ ≤ 6 * ‖gens4 (unflat ξ)‖ ^ 2 := by
  rw [H4_zero]
  set g := gens4 (unflat ξ)
  constructor
  · obtain ⟨i, hi⟩ := Finite.exists_max fun i => |g i|
    have hn : ‖g‖ = |g i| := by
      apply le_antisymm
      · exact (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun j => by
          rw [Real.norm_eq_abs]; exact hi j
      · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm g i
    rw [hn, sq_abs]
    exact Finset.single_le_sum (f := fun j => g j ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  · calc ∑ i, g i ^ 2 ≤ ∑ _i : Fin 6, ‖g‖ ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [← sq_abs, ← Real.norm_eq_abs]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm g i) 2
      _ = 6 * ‖g‖ ^ 2 := by simp

/-! ### Continuity -/

theorem continuous_Pm (k : Fin 2) (i : ℕ) : Continuous fun ξ : Fin 12 → ℝ => Pm (unflat ξ) k i := by
  simp only [Pm, mom, rowForm, Fin.sum_univ_three, unflat]; fun_prop

theorem continuous_W5 : Continuous fun ξ : Fin 12 → ℝ => W5 (unflat ξ) := by
  simp only [W5, e50, etaW, yW, ext4, rA, rB, Fin.sum_univ_four, Finset.sum_filter, rowForm]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Fin.reduceLT, Fin.lt_irrefl, ite_true, ite_false, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.zero_apply]
  simp only [unflat]
  fun_prop

theorem continuous_W4 : Continuous fun ξ : Fin 12 → ℝ => W4 (unflat ξ) := by
  simp only [W4, e41, etaW, yW, etaW', yW', ext4, rA, rB, Fin.sum_univ_four, Finset.sum_filter,
    rowForm]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Fin.reduceLT, Fin.lt_irrefl, ite_true, ite_false, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.zero_apply]
  simp only [unflat]
  fun_prop

theorem continuous_h4 (i : Fin 6) :
    Continuous fun q : ℝ × (Fin 12 → ℝ) => h4 q.1 (unflat q.2) i := by
  have P : ∀ k i, Continuous fun q : ℝ × (Fin 12 → ℝ) => Pm (unflat q.2) k i :=
    fun k i => (continuous_Pm k i).comp continuous_snd
  have h5 : Continuous fun q : ℝ × (Fin 12 → ℝ) => W5 (unflat q.2) :=
    continuous_W5.comp continuous_snd
  have h4' : Continuous fun q : ℝ × (Fin 12 → ℝ) => W4 (unflat q.2) :=
    continuous_W4.comp continuous_snd
  have P00 := P 0 0; have P01 := P 0 1; have P02 := P 0 2; have P03 := P 0 3
  have P10 := P 1 0; have P11 := P 1 1; have P12 := P 1 2; have P13 := P 1 3
  fin_cases i
  · show Continuous fun q : ℝ × (Fin 12 → ℝ) => hS5 q.1 (unflat q.2)
    simp only [hS5, Dm]; fun_prop
  · show Continuous fun q : ℝ × (Fin 12 → ℝ) => hS4 q.1 (unflat q.2)
    simp only [hS4, Dm]; fun_prop
  · show Continuous fun q : ℝ × (Fin 12 → ℝ) => hST q.1 (unflat q.2) 0
    simp only [hST]; fun_prop
  · show Continuous fun q : ℝ × (Fin 12 → ℝ) => hT3 q.1 (unflat q.2) 0
    simp only [hT3]; fun_prop
  · show Continuous fun q : ℝ × (Fin 12 → ℝ) => hST q.1 (unflat q.2) 1
    simp only [hST]; fun_prop
  · show Continuous fun q : ℝ × (Fin 12 → ℝ) => hT3 q.1 (unflat q.2) 1
    simp only [hT3]; fun_prop

/-- **Item 3, regularity**: `H₄` is jointly continuous in `(r, ξ)`. -/
theorem continuous_H4 : Continuous fun q : ℝ × (Fin 12 → ℝ) => H4 q.1 q.2 :=
  continuous_finsetSum _ fun i _ => (continuous_h4 i).pow 2

theorem continuous_G4 : Continuous G4 := by
  have h : Continuous fun ξ : Fin 12 → ℝ => ((1 : ℝ), ξ) := continuous_const.prodMk continuous_id
  have := continuous_H4.comp h
  unfold G4
  exact this

theorem measurable_G4 : Measurable G4 := continuous_G4.measurable

/-! ### The exact coefficients at position four, split into active and inactive parts -/

theorem inact_three (θ : Raw16) : inact 3 θ = ![rawW θ 0, rawW θ 1, rawW θ 2] := by
  funext l; fin_cases l <;> rfl

section Split

variable (θ : Raw16)

/-- The active row form `(α_k, ν_k)` at position four. -/
def aα (k : Fin 2) : ℝ := rA (rawW θ) 3 k
def aν (k : Fin 2) : ℝ := rB (rawW θ) 3 k

theorem e12_split (k : Fin 2) :
    e12 (rawW θ) k = 3 * aα θ k * aν θ k ^ 2 + 3 * Pm (inact 3 θ) k 2 := by
  rw [inact_three]
  simp only [e12, Pm, mom, aα, aν, rA, rB, Fin.sum_univ_four, Fin.sum_univ_three]
  simp
  ring

theorem e03_split (k : Fin 2) :
    e03 (rawW θ) k = aν θ k ^ 3 + Pm (inact 3 θ) k 3 := by
  rw [inact_three]
  simp only [e03, Pm, mom, aν, rB, Fin.sum_univ_four, Fin.sum_univ_three]
  simp
  ring

theorem e50_split :
    e50 (rawW θ) 0 = W5 (inact 3 θ) + 3 * aα θ 0 ^ 2 *
      (aα θ 0 * Dm (inact 3 θ) 0 + aν θ 0 * Pm (inact 3 θ) 1 0) := by
  rw [inact_three]
  simp only [W5, e50, etaW, yW, ext4, Dm, Pm, mom, aα, aν, rA, rB, Fin.sum_univ_four,
    Fin.sum_univ_three, Finset.sum_filter, rowForm]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Fin.reduceLT, Fin.lt_irrefl, ite_true, ite_false, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.zero_apply]
  ring

theorem e41_split :
    e41 (rawW θ) 0 = W4 (inact 3 θ) + 3 * aα θ 0 ^ 2 *
      (aα θ 0 * (3 * Dm (inact 3 θ) 1) + aν θ 0 * (3 * Pm (inact 3 θ) 1 1)) +
      6 * aα θ 0 * aν θ 0 * (aα θ 0 * Dm (inact 3 θ) 0 + aν θ 0 * Pm (inact 3 θ) 1 0) := by
  rw [inact_three]
  simp only [W4, e41, etaW, yW, etaW', yW', ext4, Dm, Pm, mom, aα, aν, rA, rB, Fin.sum_univ_four,
    Fin.sum_univ_three, Finset.sum_filter, rowForm]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Fin.reduceLT, Fin.lt_irrefl, ite_true, ite_false, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.zero_apply]
  ring

theorem e30_split4 (k : Fin 2) :
    e30 (rawW θ) k = aα θ k ^ 3 - 1 + Pm (inact 3 θ) k 0 := by
  rw [e30_split 3 θ k, P0w, unflat_wOf]; rfl

theorem e21_split4 (k : Fin 2) :
    e21 (rawW θ) k = 3 * aα θ k ^ 2 * aν θ k + 3 * Pm (inact 3 θ) k 1 := by
  rw [e21_split 3 θ k, P1w, unflat_wOf]; rfl

end Split

/-! ### Exact elimination of the active entries -/

/-- `st²`: `ĝ = (α³/3) f - P₂ c₃ - ((α²ν - P₁)/3) c₂`. -/
theorem elim_st (α ν P0 P1 P2 : ℝ) :
    P1 ^ 2 + (1 - P0) * P2 = α ^ 3 / 3 * (3 * α * ν ^ 2 + 3 * P2) + (-P2) * (α ^ 3 - 1 + P0) +
      (-(α ^ 2 * ν - P1) / 3) * (3 * α ^ 2 * ν + 3 * P1) := by ring

/-- `t³`: `ĝ = α⁶ f - (α³ + 1 - P₀) P₃ c₃ - ((m² - m P₁ + P₁²)/3) c₂`, `m = α²ν`. -/
theorem elim_t3 (α ν P0 P1 P3 : ℝ) :
    -P1 ^ 3 + (1 - P0) ^ 2 * P3 = α ^ 6 * (ν ^ 3 + P3) +
      (-((α ^ 3 + (1 - P0)) * P3)) * (α ^ 3 - 1 + P0) +
      (-((α ^ 2 * ν) ^ 2 - α ^ 2 * ν * P1 + P1 ^ 2) / 3) * (3 * α ^ 2 * ν + 3 * P1) := by ring

/-- `s⁵`: `ĝ = f/3 - D₀ c₃ - (q₀/3) c₂`. -/
theorem elim_s5 (α ν P0 P1 D0 q0 W : ℝ) :
    W / 3 + (1 - P0) * D0 - P1 * q0 =
      1 / 3 * (W + 3 * α ^ 2 * (α * D0 + ν * q0)) + (-D0) * (α ^ 3 - 1 + P0) +
        (-q0 / 3) * (3 * α ^ 2 * ν + 3 * P1) := by ring

/-- `s⁴t`: `ĝ = (α³/9) f + B c₃ + D c₂` with explicit polynomial `B`, `D`. -/
theorem elim_s4 (α ν P0 P1 D0 D1 q0 q1 W : ℝ) :
    ((1 - P0) * W + 9 * (1 - P0) ^ 2 * D1 - 9 * (1 - P0) * P1 * q1 - 6 * (1 - P0) * P1 * D0 +
        6 * P1 ^ 2 * q0) / 9 =
      α ^ 3 / 9 * (W + 3 * α ^ 2 * (α * (3 * D1) + ν * (3 * q1)) +
          6 * α * ν * (α * D0 + ν * q0)) +
        (-(W + 9 * (α ^ 3 + (1 - P0)) * D1 + (9 * q1 + 6 * D0) * (α ^ 2 * ν)) / 9) *
          (α ^ 3 - 1 + P0) +
        (-((9 * q1 + 6 * D0) * (1 - P0) / 3 + 2 * q0 * (α ^ 2 * ν - P1)) / 9) *
          (3 * α ^ 2 * ν + 3 * P1) := by ring

/-- The exact coefficients `f_i` matching the six components (`s⁵`, `s⁴t` of row `0`, `st²`, `t³`
of rows `0` and `1`), and the active row each one is eliminated against. -/
def fco (θ : Raw16) : Fin 6 → ℝ :=
  ![e50 (rawW θ) 0, e41 (rawW θ) 0, e12 (rawW θ) 0, e03 (rawW θ) 0, e12 (rawW θ) 1, e03 (rawW θ) 1]
def rowOf : Fin 6 → Fin 2 := ![0, 0, 0, 0, 1, 1]

/-- The multipliers `(Aᵢ, Bᵢ, Dᵢ)` of `ĝᵢ = Aᵢ fᵢ + Bᵢ c₃ + Dᵢ c₂`. -/
noncomputable def mults (θ : Raw16) (i : Fin 6) : ℝ × ℝ × ℝ :=
  let V := inact 3 θ
  let α := aα θ (rowOf i)
  let ν := aν θ (rowOf i)
  let k := rowOf i
  match i with
  | 0 => (1 / 3, -Dm V 0, -Pm V 1 0 / 3)
  | 1 => (α ^ 3 / 9,
      -(W4 V + 9 * (α ^ 3 + (1 - Pm V 0 0)) * Dm V 1 + (9 * Pm V 1 1 + 6 * Dm V 0) * (α ^ 2 * ν)) / 9,
      -((9 * Pm V 1 1 + 6 * Dm V 0) * (1 - Pm V 0 0) / 3 + 2 * Pm V 1 0 * (α ^ 2 * ν - Pm V 0 1)) / 9)
  | 2 | 4 => (α ^ 3 / 3, -Pm V k 2, -(α ^ 2 * ν - Pm V k 1) / 3)
  | 3 | 5 => (α ^ 6, -((α ^ 3 + (1 - Pm V k 0)) * Pm V k 3),
      -((α ^ 2 * ν) ^ 2 - α ^ 2 * ν * Pm V k 1 + Pm V k 1 ^ 2) / 3)

/-- **The elimination identity**: `ĝᵢ(w(θ)) = Aᵢ fᵢ + Bᵢ c₃⁽ᵏ⁾ + Dᵢ c₂⁽ᵏ⁾`, exactly. -/
theorem ghat_eq (θ : Raw16) (i : Fin 6) :
    h4 1 (inact 3 θ) i = (mults θ i).1 * fco θ i + (mults θ i).2.1 * e30 (rawW θ) (rowOf i) +
      (mults θ i).2.2 * e21 (rawW θ) (rowOf i) := by
  fin_cases i
  · simp only [h4, hS5, fco, mults, rowOf, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      e50_split, e30_split4, e21_split4]
    rw [one_pow, one_mul, one_mul, one_mul]
    exact elim_s5 _ _ _ _ _ _ _
  · simp only [h4, hS4, fco, mults, rowOf, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_zero, e41_split, e30_split4, e21_split4]
    simp only [one_pow, one_mul, mul_one]
    exact elim_s4 _ _ _ _ _ _ _ _ _
  all_goals
    first
    | (show hST 1 (inact 3 θ) _ = _
       simp only [hST, fco, mults, rowOf, e12_split, e30_split4, e21_split4,
         one_pow, one_mul]
       exact elim_st _ _ _ _ _)
    | (show hT3 1 (inact 3 θ) _ = _
       simp only [hT3, fco, mults, rowOf, e03_split, e30_split4, e21_split4,
         one_pow, one_mul]
       exact elim_t3 _ _ _ _ _)

/-! ### The comparison (item 2) -/

theorem continuous_Lfun (p : Fin 4) : Continuous (Lfun p) := (Lequiv p).continuous

theorem continuous_wOf (p : Fin 4) : Continuous (wOf p) := continuous_snd.comp (continuous_Lfun p)

/-- The sum of the absolute values of all multipliers. -/
noncomputable def mbound (θ : Raw16) : ℝ :=
  ∑ i, (|(mults θ i).1| + |(mults θ i).2.1| + |(mults θ i).2.2|)

theorem continuous_mbound : Continuous mbound := by
  have hL := continuous_Lfun 3
  have a0 : Continuous fun θ => aα θ 0 := (continuous_fst.comp (continuous_fst.comp
    (continuous_fst.comp hL)))
  have a1 : Continuous fun θ => aα θ 1 := (continuous_fst.comp (continuous_snd.comp
    (continuous_fst.comp hL)))
  have n0 : Continuous fun θ => aν θ 0 := (continuous_snd.comp (continuous_fst.comp
    (continuous_fst.comp hL)))
  have n1 : Continuous fun θ => aν θ 1 := (continuous_snd.comp (continuous_snd.comp
    (continuous_fst.comp hL)))
  have hw := continuous_wOf 3
  have P : ∀ k i, Continuous fun θ => Pm (inact 3 θ) k i := fun k i => by
    simp only [← unflat_wOf]; exact (continuous_Pm k i).comp hw
  have hW4 : Continuous fun θ => W4 (inact 3 θ) := by
    simp only [← unflat_wOf]; exact continuous_W4.comp hw
  have P00 := P 0 0; have P01 := P 0 1; have P02 := P 0 2; have P03 := P 0 3
  have P10 := P 1 0; have P11 := P 1 1; have P12 := P 1 2; have P13 := P 1 3
  refine continuous_finsetSum _ fun i _ => ?_
  fin_cases i <;>
    simp only [mults, rowOf, Dm, Fin.mk_one, Fin.isValue, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
    fun_prop

/-- `g² ≤ 3K² (f² + c₃² + c₂²)` when `g = a f + b c₃ + d c₂` with `|a|, |b|, |d| ≤ K`. -/
theorem sq_le_of_lin {g a b d f c3 c2 K : ℝ} (h : g = a * f + b * c3 + d * c2) (ha : |a| ≤ K)
    (hb : |b| ≤ K) (hd : |d| ≤ K) : g ^ 2 ≤ 3 * K ^ 2 * (f ^ 2 + c3 ^ 2 + c2 ^ 2) := by
  have hK : 0 ≤ K := (abs_nonneg a).trans ha
  have h1 : |g| ≤ K * (|f| + |c3| + |c2|) := by
    rw [h]
    calc |a * f + b * c3 + d * c2| ≤ |a * f| + |b * c3| + |d * c2| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |a| * |f| + |b| * |c3| + |d| * |c2| := by rw [abs_mul, abs_mul, abs_mul]
      _ ≤ K * |f| + K * |c3| + K * |c2| := by
          gcongr
      _ = K * (|f| + |c3| + |c2|) := by ring
  have h2 : g ^ 2 ≤ (K * (|f| + |c3| + |c2|)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : (|f| + |c3| + |c2|) ^ 2 ≤ 3 * (f ^ 2 + c3 ^ 2 + c2 ^ 2) := by
    rw [← sq_abs f, ← sq_abs c3, ← sq_abs c2]
    nlinarith [sq_nonneg (|f| - |c3|), sq_nonneg (|f| - |c2|), sq_nonneg (|c3| - |c2|)]
  calc g ^ 2 ≤ (K * (|f| + |c3| + |c2|)) ^ 2 := h2
    _ = K ^ 2 * (|f| + |c3| + |c2|) ^ 2 := by ring
    _ ≤ K ^ 2 * (3 * (f ^ 2 + c3 ^ 2 + c2 ^ 2)) := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    _ = _ := by ring

/-- The ten coefficients used at position four: `𝐜` and the six `fᵢ`. -/
noncomputable def fam10 : Fin 10 → Fin 2 × (Fin 2 →₀ ℕ) :=
  ![(0, stMono 3 0), (0, stMono 2 1), (1, stMono 3 0), (1, stMono 2 1), (0, stMono 5 0),
    (0, stMono 4 1), (0, stMono 1 2), (0, stMono 0 3), (1, stMono 1 2), (1, stMono 0 3)]

theorem sum_fam10 (θ : Raw16) :
    ∑ j, ((errθ θ (fam10 j).1).coeff (fam10 j).2) ^ 2 =
      ∑ i, cvec θ i ^ 2 + ∑ i, fco θ i ^ 2 := by
  obtain ⟨a0, b0, c0, d0, e0, f0⟩ := errθ_coeffs θ 0
  obtain ⟨a1, b1, c1, d1, -, -⟩ := errθ_coeffs θ 1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, fam10, cvec, fco, Matrix.cons_val_zero,
    Matrix.cons_val_succ, a0, b0, c0, d0, e0, f0, a1, b1, c1, d1]
  ring

/-- The inactive coordinates lie in the ball of the same radius. -/
theorem norm_wOf_sub_le (p : Fin 4) (θ : Raw16) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖wOf p θ‖ ≤ ‖θ - basePos A p‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun n => ?_
  have hb : ∀ l : Fin 3, ∀ i j : Fin 2, rawW (basePos A p) (p.succAbove l) i j = 0 := by
    intro l i j
    rw [rawW_basePos, Pi.single_eq_of_ne (Fin.succAbove_ne p l)]; rfl
  have e : wOf p θ n = rawW (θ - basePos A p) (p.succAbove ⟨n.val / 4, by omega⟩)
      ⟨n.val % 4 / 2, by omega⟩ ⟨n.val % 2, by omega⟩ := by
    rw [rawW_sub', hb, sub_zero]; rfl
  rw [e, Real.norm_eq_abs]
  exact abs_rawW_le _ _ _ _

/-- **Item 2 at position four: the loss comparison.** For an input law with the hypotheses of
`Gdown` and every radius `ρ`, there is `κ > 0` with
`κ (‖𝐜(θ)‖² + G₄(w(θ))) ≤ K(θ)` on the closed `ρ`-ball around `basePos A₀ 3`. -/
theorem loss_compare_four (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ) (ρ : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ θ ∈ closedBall (basePos A0 3) ρ,
      κ * (∑ i, (Ψ 3 θ).1 i ^ 2 + G4 (Ψ 3 θ).2) ≤ popLossA μ A0 θ := by
  obtain ⟨κ₀, hκ₀, hG⟩ := gdown_family μ hmom hlh hμ₀ hμ fam10
  obtain ⟨K, hK⟩ := (isCompact_closedBall (basePos A0 3) ρ).exists_bound_of_continuousOn
    continuous_mbound.continuousOn
  set K' := max K 0
  have hK'0 : 0 ≤ K' := le_max_right _ _
  refine ⟨κ₀ / (1 + 18 * K' ^ 2), by positivity, fun θ hθ => ?_⟩
  have hmb : mbound θ ≤ K' := by
    have := hK θ hθ; rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have hm : ∀ i, |(mults θ i).1| ≤ K' ∧ |(mults θ i).2.1| ≤ K' ∧ |(mults θ i).2.2| ≤ K' := by
    intro i
    have hi : |(mults θ i).1| + |(mults θ i).2.1| + |(mults θ i).2.2| ≤ K' :=
      (Finset.single_le_sum (f := fun i => |(mults θ i).1| + |(mults θ i).2.1| +
        |(mults θ i).2.2|) (fun j _ => by positivity) (Finset.mem_univ i)).trans hmb
    refine ⟨?_, ?_, ?_⟩ <;> linarith [abs_nonneg (mults θ i).1, abs_nonneg (mults θ i).2.1,
      abs_nonneg (mults θ i).2.2]
  set T := ∑ i, cvec θ i ^ 2 + ∑ i, fco θ i ^ 2
  have hT := hG θ
  rw [sum_fam10] at hT
  have hc : ∀ k : Fin 2, e30 (rawW θ) k ^ 2 + e21 (rawW θ) k ^ 2 ≤ ∑ i, cvec θ i ^ 2 := by
    intro k
    simp only [Fin.sum_univ_four, cvec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]
    fin_cases k <;> simp <;> nlinarith [sq_nonneg (e30 (rawW θ) 0), sq_nonneg (e21 (rawW θ) 0),
      sq_nonneg (e30 (rawW θ) 1), sq_nonneg (e21 (rawW θ) 1)]
  have hgi : ∀ i, h4 1 (inact 3 θ) i ^ 2 ≤
      3 * K' ^ 2 * (fco θ i ^ 2 + ∑ j, cvec θ j ^ 2) := by
    intro i
    obtain ⟨ha, hb, hd⟩ := hm i
    have := sq_le_of_lin (ghat_eq θ i) ha hb hd
    have := hc (rowOf i)
    nlinarith [sq_nonneg K']
  have hGw : G4 (Ψ 3 θ).2 ≤ 18 * K' ^ 2 * T := by
    change ∑ i, h4 1 (unflat (wOf 3 θ)) i ^ 2 ≤ _
    rw [unflat_wOf]
    calc ∑ i, h4 1 (inact 3 θ) i ^ 2 ≤ ∑ i, 3 * K' ^ 2 * (fco θ i ^ 2 + ∑ j, cvec θ j ^ 2) :=
          Finset.sum_le_sum fun i _ => hgi i
      _ = 3 * K' ^ 2 * (∑ i, fco θ i ^ 2 + 6 * ∑ j, cvec θ j ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]; simp
      _ ≤ 18 * K' ^ 2 * T := by
          have h1 : 0 ≤ ∑ i, fco θ i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
          have h2 : 0 ≤ ∑ i, cvec θ i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
          simp only [T]; nlinarith [sq_nonneg K']
  have hfin : ∑ i, (Ψ 3 θ).1 i ^ 2 + G4 (Ψ 3 θ).2 ≤ (1 + 18 * K' ^ 2) * T := by
    have h1 : 0 ≤ ∑ i, fco θ i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    change ∑ i, cvec θ i ^ 2 + _ ≤ _
    simp only [T] at hGw ⊢; nlinarith
  calc κ₀ / (1 + 18 * K' ^ 2) * (∑ i, (Ψ 3 θ).1 i ^ 2 + G4 (Ψ 3 θ).2)
      ≤ κ₀ / (1 + 18 * K' ^ 2) * ((1 + 18 * K' ^ 2) * T) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = κ₀ * T := by field_simp
    _ ≤ _ := hT

end VectorSLT.LossCompare
