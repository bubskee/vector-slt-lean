/-
Brief 05, R3: paper-facing names.

Every declaration here is an `alias` of an existing theorem: same type, same proof term, no new
mathematics. The library names are unchanged and remain the primary names. `checks/PaperAudit.lean`
prints each alias next to its original.
-/
import VectorSLT.MainTheorem
import VectorSLT.TwoSidedLaws
import VectorSLT.EtaPopulation
import VectorSLT.E0Identity

namespace VectorSLT

/-! ### Main theorem (depth-four shear table) -/

/-- **Main theorem.** Pairs `(4,5), (4,1), (4,1), (4,1)` at positions one to four for every
two-nonzero-row rank-one shear, conditional on `ThmK` and `ThmN`. -/
alias vector_shear_main_theorem := mainTheorem_shear

/-- **Main theorem, separation form.** `Z_{N,1} / Z_{N,p} → ∞` for `p ≠ 1`, conditional on
`ThmK` and `ThmN`. -/
alias vector_shear_main_theorem_ratio := mainTheorem_shear_ratio

/-- **Main theorem, standard Gaussian inputs**, conditional on `ThmK` and `ThmN`. -/
alias vector_shear_main_theorem_gaussian := mainTheorem_shear_gaussian

/-! ### Position one -/

/-- **Theorem L′** (lower half at position one) for every input law with finite 162nd moments. -/
alias vector_shear_position_one_lower := propLprime_moments

/-- **Theorem M** (upper half at position one) for every two-nonzero-row shear. -/
alias vector_shear_position_one_upper := theoremM_shear

/-- **Position one exact:** `Z_{N,1} ≍ N⁻⁴ (log N)⁴`, i.e. the pair `(4,5)`, unconditionally. -/
alias vector_shear_position_one_exact := ZN1_two_sided_moments

/-- **Position one exact, standard Gaussian inputs.** -/
alias vector_shear_position_one_exact_gaussian := ZN1_two_sided_gaussian

/-! ### Other positions -/

/-- **O3:** `Z_{N,p} ≥ c N⁻⁴` at every position `p` and for every target matrix. -/
alias vector_any_position_lower := Zpos_lower_N4

/-! ### Near-shear targets (finite scale, X4) -/

/-- **X4:** `Z_N(A_η) ≥ c N⁻⁴ (1 + 𝓛_η(N))⁴`, with `c, N₀` uniform in `|η| ≤ 1/10`. -/
alias vector_near_shear_lower := X4_lower_population

/-- **X4, standard Gaussian inputs.** -/
alias vector_near_shear_lower_gaussian := X4_lower_gaussian

/-- **Proposition X1** (`β₀ > 0` branch): normal form `A_η` for rank-one targets. -/
alias vector_near_shear_normal_form := normalize_Aeta

/-! ### Normalization and the E₀ identity -/

/-- **Theorem H §2:** every two-nonzero-row shear is (H2)/(H3)-equivalent to `A₀`. -/
alias vector_shear_normal_form := shear_normalize

/-- **E₀ identity:** the bordered determinant `-det = (∏ aᵢ) Σ aᵢ³`. -/
alias vector_E0_bordered_det := bordered_det

end VectorSLT
