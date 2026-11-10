/-
Lemma N3: the leading term at the shear target is an injective linear image of the active
coordinates and the slt-bridge generators (item 3 of the leading-map brief).

For `p = 1, 2, 3` (paper positions two, three, four):
* `lead A₀ p Δ V = Λ_p (activeCoords Δ V, gens_p V)` as functions of `x` (`lead_A0_pos2`,
  `lead_A0_pos3`, `lead_A0_pos4`), with `gens_p` the mirrors of slt-bridge's `R2`, `R3`,
  `leadingMap`;
* `Λ_p` is linear and injective (`LamMid_injective`, `LamFour_injective`);
* for fixed `V`, `Δ ↦ activeCoords Δ V` is an invertible linear map of `Δ` plus a term depending
  only on `V` (`activeCoords_eq`), hence a bijection (`activeCoords_bijective`).
So the `ε³` term of the error vanishes iff the active coordinates and the generators all vanish
(`lead_A0_pos2_eq_zero_iff` etc.).
-/
import VectorSLT.LeadingMap.Generators

namespace VectorSLT.LeadingMap

open Matrix Finset

/-! ### Active coordinates -/

/-- The linear part of the active coordinates: `Δ ↦ (3 Δ₀₀, 3 (Δ₀₀ + Δ₀₁), 3 Δ₁₀, 3 (Δ₁₀ + Δ₁₁))`,
i.e. `3 (α_k, ν_k)` in the active-row coordinates `α = m₀`, `ν = m₀ + m₁` of Appendix C. -/
noncomputable def activeLin : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun Δ := ![3 * Δ 0 0, 3 * (Δ 0 0 + Δ 0 1), 3 * Δ 1 0, 3 * (Δ 1 0 + Δ 1 1)]
  map_add' Δ Δ' := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c Δ := by funext i; fin_cases i <;> simp <;> ring
  invFun c := !![c 0 / 3, (c 1 - c 0) / 3; c 2 / 3, (c 3 - c 2) / 3]
  left_inv Δ := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  right_inv c := by funext i; fin_cases i <;> simp <;> ring

/-- **The active coordinates** `c(Δ, V)`: the `s³` and `s²t` coefficients of the two rows of the
leading term, `(3 Δ_{k0} + P₀^{(k)}[all], 3 (Δ_{k0} + Δ_{k1}) + 3 P₁^{(k)}[all])` for `k = 0, 1`
(the `ε³` parts of the paper's `c₃^{(k)}`, `c₂^{(k)}`). -/
def activeCoords (Δ : Matrix (Fin 2) (Fin 2) ℝ) (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) :
    Fin 4 → ℝ :=
  ![3 * Δ 0 0 + mom V univ 0 0, 3 * (Δ 0 0 + Δ 0 1) + 3 * mom V univ 0 1,
    3 * Δ 1 0 + mom V univ 1 0, 3 * (Δ 1 0 + Δ 1 1) + 3 * mom V univ 1 1]

/-- The active coordinates are the invertible linear map `activeLin` of `Δ` plus a term that
depends only on `V`. -/
theorem activeCoords_eq (Δ : Matrix (Fin 2) (Fin 2) ℝ) (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) :
    activeCoords Δ V = activeLin Δ + activeCoords 0 V := by
  funext i; fin_cases i <;> simp [activeCoords, activeLin]

/-- **For fixed `V`, `Δ ↦ c(Δ, V)` is a bijection onto `ℝ⁴`.** -/
theorem activeCoords_bijective (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) :
    Function.Bijective fun Δ => activeCoords Δ V := by
  have : (fun Δ => activeCoords Δ V) = (fun c => c + activeCoords 0 V) ∘ activeLin := by
    funext Δ; exact activeCoords_eq Δ V
  rw [this]
  exact (Equiv.addRight (activeCoords 0 V)).bijective.comp activeLin.bijective

/-! ### The linear maps `Λ_p` -/

/-- Read `poly11` off a function of `x` at `x = (s + t, t)`. -/
theorem poly11_eq_zero_of_fun {κ : Fin 11 → ℝ} (h : ∀ x : Fin 2 → ℝ, poly11 κ (x 0 - x 1) (x 1) = 0) :
    κ = 0 :=
  poly11_eq_zero fun s t => by simpa using h ![s + t, t]

/-- Coefficients of `Λ_mid` (positions two and three), row by row: the Proposition N1 table
rewritten in the active coordinates `c` and the eleven generators `g`. -/
def coeffMid (v : (Fin 4 → ℝ) × (Fin 11 → ℝ)) : Fin 2 → Fin 11 → ℝ :=
  ![![v.1 0, v.1 1, 3 * (v.2 0 + v.2 2), v.2 1 + v.2 3, 3 * v.2 10,
      3 * (3 * v.2 8 + 2 * v.2 2), 3 * (3 * (v.2 0 - v.2 4) + v.2 3), 3 * (v.2 1 - v.2 5),
      3 * v.2 2, 3 * v.2 3, v.2 3],
    ![v.1 2, v.1 3, 3 * (v.2 4 + v.2 6), v.2 5 + v.2 7, 3 * (v.2 10 - v.2 9),
      3 * (3 * v.2 8 + 2 * v.2 6), 3 * (3 * (v.2 0 - v.2 4) + v.2 7), 3 * (v.2 1 - v.2 5),
      3 * v.2 6, 3 * v.2 7, v.2 7]]

/-- **`Λ_mid`** (Lean `p = 1, 2`): `(c, g) ↦ (x ↦ (poly11 (coeffMid (c, g) k) s t)_k)`. -/
def LamMid : (Fin 4 → ℝ) × (Fin 11 → ℝ) →ₗ[ℝ] ((Fin 2 → ℝ) → Fin 2 → ℝ) where
  toFun v x k := poly11 (coeffMid v k) (x 0 - x 1) (x 1)
  map_add' v w := by
    funext x k; fin_cases k <;> simp [coeffMid, poly11] <;> ring
  map_smul' c v := by
    funext x k; fin_cases k <;> simp [coeffMid, poly11] <;> ring

/-- Coefficients of `Λ_four` (Lean `p = 3`), in the six components of `leadingMap`
`(F₀, F₁, Q₁, Φ(B), Q₂, Φ(D))`. -/
def coeffFour (v : (Fin 4 → ℝ) × (Fin 6 → ℝ)) : Fin 2 → Fin 11 → ℝ :=
  ![![v.1 0, v.1 1, 3 * v.2 2, v.2 3, 3 * v.2 0, 9 * v.2 1, 9 * (v.2 2 - v.2 4),
      3 * (v.2 3 - v.2 5), 0, 0, 0],
    ![v.1 2, v.1 3, 3 * v.2 4, v.2 5, 3 * v.2 0, 9 * v.2 1, 9 * (v.2 2 - v.2 4),
      3 * (v.2 3 - v.2 5), 0, 0, 0]]

/-- **`Λ_four`** (Lean `p = 3`). -/
def LamFour : (Fin 4 → ℝ) × (Fin 6 → ℝ) →ₗ[ℝ] ((Fin 2 → ℝ) → Fin 2 → ℝ) where
  toFun v x k := poly11 (coeffFour v k) (x 0 - x 1) (x 1)
  map_add' v w := by
    funext x k; fin_cases k <;> simp [coeffFour, poly11] <;> ring
  map_smul' c v := by
    funext x k; fin_cases k <;> simp [coeffFour, poly11] <;> ring

/-- **`Λ_mid` is injective.** -/
theorem LamMid_injective : Function.Injective LamMid := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have h : ∀ k, coeffMid v k = 0 := fun k =>
    poly11_eq_zero_of_fun fun x => congrFun (congrFun hv x) k
  have h0 := fun i => congrFun (h 0) i
  have h1 := fun i => congrFun (h 1) i
  simp only [coeffMid, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
  have e := fun i : Fin 11 => h0 i
  have f := fun i : Fin 11 => h1 i
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4
  have e5 := e 5; have e6 := e 6; have e7 := e 7; have e8 := e 8
  have f0 := f 0; have f1 := f 1; have f2 := f 2; have f3 := f 3; have f4 := f 4
  have f5 := f 5; have f8 := f 8; have f9 := f 9
  simp at e0 e1 e2 e3 e4 e5 e6 e7 e8 f0 f1 f2 f3 f4 f5 f8 f9
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;> simp <;> linarith

/-- **`Λ_four` is injective.** -/
theorem LamFour_injective : Function.Injective LamFour := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have h : ∀ k, coeffFour v k = 0 := fun k =>
    poly11_eq_zero_of_fun fun x => congrFun (congrFun hv x) k
  have e := fun i : Fin 11 => congrFun (h 0) i
  have f := fun i : Fin 11 => congrFun (h 1) i
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4
  have e5 := e 5; have f0 := f 0; have f1 := f 1; have f2 := f 2; have f3 := f 3
  simp [coeffFour] at e0 e1 e2 e3 e4 e5 f0 f1 f2 f3
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;> simp <;> linarith

/-! ### Lemma N3 -/

/-- **Lemma N3, position two** (Lean `p = 1`):
`lead A₀ 1 Δ V = Λ_mid (c(Δ, V), R2 (w2 V))`. -/
theorem lead_A0_pos2 (Δ : Matrix (Fin 2) (Fin 2) ℝ) (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) :
    lead A0 1 Δ V = LamMid (activeCoords Δ V, gens2 V) := by
  funext x k
  rw [lead_A0_eq_table]
  change _ = poly11 (coeffMid (activeCoords Δ V, gens2 V) k) _ _
  congr 1
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [n1Coeff, coeffMid, activeCoords, gens2, R2, w2, generators, cube, twoCube, momD, mom,
      pre, suf, Finset.sum_filter, Fin.sum_univ_three] <;> ring

/-- **Lemma N3, position three** (Lean `p = 2`):
`lead A₀ 2 Δ V = Λ_mid (c(Δ, V), R3 (w3 V))`. -/
theorem lead_A0_pos3 (Δ : Matrix (Fin 2) (Fin 2) ℝ) (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) :
    lead A0 2 Δ V = LamMid (activeCoords Δ V, gens3 V) := by
  funext x k
  rw [lead_A0_eq_table]
  change _ = poly11 (coeffMid (activeCoords Δ V, gens3 V) k) _ _
  congr 1
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [n1Coeff, coeffMid, activeCoords, gens3, R3, w3, generators, cube, twoCube, momD, mom,
      pre, suf, Finset.sum_filter, Fin.sum_univ_three]
  all_goals ring

/-- **Equation (K-R), position four** (Lean `p = 3`):
`lead A₀ 3 Δ V = Λ_four (c(Δ, V), leadingMap (w4 V))`. -/
theorem lead_A0_pos4 (Δ : Matrix (Fin 2) (Fin 2) ℝ) (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) :
    lead A0 3 Δ V = LamFour (activeCoords Δ V, gens4 V) := by
  funext x k
  rw [lead_A0_eq_table]
  change _ = poly11 (coeffFour (activeCoords Δ V, gens4 V) k) _ _
  congr 1
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [n1Coeff, coeffFour, activeCoords, gens4, leadingMap, rowCubic, w4, cube, momD, mom,
      pre, suf, Finset.sum_filter, Fin.sum_univ_three] <;> ring

/-! ### The zero set of the leading term -/

theorem lead_eq_zero_iff_of {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Λ : (Fin 4 → ℝ) × E →ₗ[ℝ] ((Fin 2 → ℝ) → Fin 2 → ℝ)) (hΛ : Function.Injective Λ)
    (c : Fin 4 → ℝ) (g : E) : Λ (c, g) = 0 ↔ c = 0 ∧ g = 0 := by
  rw [← Prod.mk_eq_zero, ← map_eq_zero_iff Λ hΛ]

/-- At position two the `ε³` term vanishes iff the active coordinates and `R2` vanish. -/
theorem lead_A0_pos2_eq_zero_iff (Δ : Matrix (Fin 2) (Fin 2) ℝ)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) :
    lead A0 1 Δ V = 0 ↔ activeCoords Δ V = 0 ∧ gens2 V = 0 := by
  rw [lead_A0_pos2]; exact lead_eq_zero_iff_of _ LamMid_injective _ _

/-- At position three the `ε³` term vanishes iff the active coordinates and `R3` vanish. -/
theorem lead_A0_pos3_eq_zero_iff (Δ : Matrix (Fin 2) (Fin 2) ℝ)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) :
    lead A0 2 Δ V = 0 ↔ activeCoords Δ V = 0 ∧ gens3 V = 0 := by
  rw [lead_A0_pos3]; exact lead_eq_zero_iff_of _ LamMid_injective _ _

/-- At position four the `ε³` term vanishes iff the active coordinates and `leadingMap`
vanish. -/
theorem lead_A0_pos4_eq_zero_iff (Δ : Matrix (Fin 2) (Fin 2) ℝ)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) :
    lead A0 3 Δ V = 0 ↔ activeCoords Δ V = 0 ∧ gens4 V = 0 := by
  rw [lead_A0_pos4]; exact lead_eq_zero_iff_of _ LamFour_injective _ _

end VectorSLT.LeadingMap
