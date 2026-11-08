# VectorSLT

This library holds the Lean 4 certificates for paper 2 of the vector (width-two cubic ResNet) SLT project. Paper 2 covers rank-one shears and their position table, the invertible contrast, the E₀ identity and the near-shear lower bound X4. The mathematics comes from `cubic-chaos` (commits `34c531e` and `b962be0`, then the commit pinned in each brief, the last being `caccd6a`). The coverage is recorded in `formalization_status.md` and checked by `checks/`.

Pins: Lean `v4.35.0` and mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

```bash
lake exe cache get && lake build && lake env lean VectorSLT/Audit.lean && lake env lean checks/PaperAudit.lean
```

| File | Content | Headline |
|---|---|---|
| `Network.lean` | A: semantics `F_B(z)=z+(Bz)^{⊙3}`, sum-of-cubes form, (M2) | `prefixNet_apply_sum_cubes_Icc`, `M2_error` |
| `Sublevel1D.lean` | B: 1-D quadratic sublevel bound, hyperbola-log integral | `volume_abs_quad_le`, `lintegral_min_div_abs_le` |
| `QuadSublevel.lean` | B: Lemma M2 | `lemmaM2`, `lemmaM2_explicit` |
| `LeadingRow.lean` | C: one-row sublevel lower bound `≥ c t log²(1/t)` | `rowSublevel_lower`, `rowLaplace_lower` |
| `LeadingModel.lean` | C: two rows plus four active coordinates, `≥ c N⁻⁴ log⁴ N` | `leadingModel_lower` |
| `ErrorBound.lean` | D: sup-norm network error on the lower region | `err_bound` |
| `FullNetwork.lean` | D: Proposition L′, full network | `propLprime`, `propLprime_population` |
| `E0Identity.lean` | L3: bordered determinant and null direction | `bordered_det`, `null_direction` |
| `Normalization.lean` | L2: Theorem H §2, (H2) and (H3); L′ for every two-nonzero-row shear target | `shear_normalize`, `propLprime_shear` |
| `SLT/Laplace.lean` | L4: Mathlib-only SLT layer: layer cake, volume ⇒ Laplace (both directions), comparability, products, `HasLaplacePair` | `Z_eq_layercake`, `laplaceLower_of_volume`, `laplaceUpper_of_volume`, `HasLaplacePair.prod` |
| `SLT/Monomial.lean` | L4: the 1-D monomial pair `(1/(2k), 1)` | `monomial_hasLaplacePair` |
| `SLT/NormalCrossing.lean`, `SLT/NormalCrossingD.lean` | L4: the d-variable normal-crossing lemma, `λ = min (hᵢ+1)/(2kᵢ)` and `m = #argmin` | `normalCrossing`, `normalCrossing_Z` |
| `SLT/Toolkit.lean` | L6 stage 1: affine lintegral substitution, Laplace from sublevel sets (M4.3), radial split (M5.3) | `lintegral_comp_affine`, `lintegral_exp_neg_le_tsum`, `radial_split` |
| `SLT/InvSqrt.lean` | L6 stage 1: `∫_I |f|^{-1/2} ≤ 4√|I|` when `|f'| ≥ 1` | `lintegral_isqrt_comp_le` |
| `LemmaM3.lean` | L6 stage 1: Lemma M3 (uniform integrability) | `lemmaM3` |
| `GramLower.lean` | L6 stage 2: every linear functional on degree-`≤ d` polynomials is bounded by `L²` on a box | `linear_le_L2` |
| `LemmaM1.lean` | L6 stage 2: Lemma M1 (`c₃, c₂, c₁, Z`) from the `(s,t)` polynomial model | `errP_c3`, `errP_s5` |
| `Gdown.lean` | L6 stage 2: (G↓) for laws with a density bounded below on a box | `Gdown` |
| `LemmaM4.lean` | L6 stage 3: Lemma M4 (one row at frozen amplitudes), slice algebra (M9) | `lemmaM4`, `det_Mt`, `slice_bound` |
| `LemmaM5.lean` | L6 stage 3: Lemma M5 (amplitude integral of one row, pivot chart) | `lemmaM5`, `inner_bound` |
| `ChartLip.lean` | L6 stage 3, F4: bounded-Lipschitz calculus; `E(M9) - E₀` small and 0.47-Lipschitz ⇒ Lemma M3 | `EM9_pert`, `m3Int_of_LB` |
| `PivotRow.lean` | L6 stage 3, F4/F5: one row, pivot first (M4 + M3 + M5) for weights with O(ε³) variation | `pivotRow`, `m3Int_Echart` |
| `RowBound.lean` | L6 stage 3, F5: one row in actual coordinates (three pivots), explicit (M6) weights | `rowBound`, `rowBound_M6` |
| `ActiveCoords.lean` | L6 stage 3, F1–F3: ν Gaussian, α ↦ α³, translation to c₃ | `active_bound`, `cube_subst` |
| `TheoremM.lean` | L6 stage 3, F5/F6 + assembly: **Theorem M** `Z_{N,1} ≤ C N⁻⁴ (log N)⁴`, and `Z_{N,1} ≍ N⁻⁴ (log N)⁴` | `theoremM`, `theoremM_raw`, `ZN1_two_sided` |
| `ShearUpper.lean` | Brief 03, O1: Theorem M and `Z_{N,1} ≍ N⁻⁴ log⁴ N` at every two-nonzero-row shear target | `theoremM_shear`, `ZN1_two_sided_shear` |
| `TwoSidedLaws.lean` | Brief 03, O2: the two-sided bound without compact support; the Gaussian density bound | `ZN1_two_sided_moments`, `ZN1_two_sided_gaussian` |
| `LowerPositions.lean` | Brief 03, O3: `c N⁻⁴ ≤ Z_{N,j}` at every position (anisotropic raw box); `ThmN`; pairs `(4,1)` at positions 2–4 | `Zpos_lower_N4`, `middle_position_pair`, `position_four_pair` |
| `MainTheorem.lean` | Brief 03, O4: the `Fin 4 → Matrix` restatement and the paper-facing position table | `rawEquiv`, `net_eq_network`, `mainTheorem_shear` |
| `InverseCriterion.lean` | Brief 03, O5, Candidate 1: `B V_B ≡ 0 ⇔ F_{-B} ∘ F_B = id`; rank-one shear form; derivative form | `inverse_criterion`, `rank_one_criterion`, `deriv_criterion`, `shear_inverse` |
| `InvertibleSeparation.lean` | Brief 03, O5, Candidate 2: cubic/quintic separation through an invertible active block (function-level, degree-3/5 homogeneous maps) | `sepMap_kernel`, `sepMap_injective` |
| `SepNorm.lean` | Brief 03, F1: `H₃²`, `H₅²` as normed spaces (box sup norm); `Φ_A` on `Mat₂ ⊕ H₃² ⊕ H₅² ⊕ H₃² ⊕ H₅²` has a positive smallest singular value; absorption step of (12) | `sepLin_injective`, `sepLin_lower`, `sep_absorb` |
| `EtaTarget.lean` | Brief 04, X1: the near-shear family `A_η`; Lemma X2 (cubic coefficients, every degree ≠ 3 coefficient and `Z_k` unchanged); Proposition X1 (`β₀ > 0` branch) | `Aeta`, `errPη_c2`, `errPη_coeff_ne3`, `normalize_Aeta` |
| `EtaError.lean` | Brief 04, X4: Lemma L′3 for `A_η` (bounds on `αν² − η²`, `ν³ − η³`; the difference argument for `Δ₀`) | `E1η_bound`, `shiftη_bound`, `err_bound_eta` |
| `EtaLower.lean` | Brief 04, X4: **`Z_N(A_η) ≥ c N⁻⁴ (1 + 𝓛_η(N))⁴`, `c`, `N₀` independent of `|η| ≤ 1/10`** | `X4_lower`, `X4_lower_segment`, `Leta` |
| `EtaPopulation.lean` | Brief 04, X4 for the population loss: moment laws, Gaussian, compact support | `X4_lower_population`, `X4_lower_gaussian`, `X4_lower_compact` |
| `PaperNames.lean` | Brief 05, R3: paper-facing aliases (`alias` only; same types and proofs) | `vector_shear_main_theorem`, `vector_shear_position_one_exact`, `vector_near_shear_lower` |
| `Gaussian.lean` | L′ and the separation for standard Gaussian inputs | `propLprime_gaussian`, `separation_gaussian` |
| `Pairs.lean` | L4: C and D restated as Laplace lower halves; (K1) as a pair | `position_one_laplaceLower`, `ThmK.hasLaplacePair` |
| `PolyModel.lean` | L5: the network as a degree-≤81 polynomial | `error_isPoly` |
| `GeneralInput.lean` | L5: (G↑) for every input law with finite 162nd moments; L′ and the separation without compact support | `l2_le_sup`, `propLprime_moments`, `separation_moments` |
| `Separation.lean` | L1: `Z_{N,1}/Z_{N,4} ≥ c log⁴N`, with Theorem K as the named hypothesis `ThmK` | `separation`, `separation_tendsto` |

## Coverage

`formalization_status.md` has the full correspondence table and states every hypothesis exactly. Each row there is tagged **certified**, **conditional** on a named hypothesis, or **not formalized**. `checks/` holds the focused audit (`PaperAudit.lean`), the build and audit logs, a SHA-256 manifest of the sources, and the before/after declaration-type comparison.

The depth-four shear table is stated for the following setting:
- target: every rank-one shear `A = a vᵀ` with both rows nonzero;
- input law: finite 162nd moments and a density bounded below on some box (standard Gaussian included);
- prior: bounded, and bounded below near each base point;
- cutoff: at most 1, bounded below near 0, and supported in a ball of radius `r(A)`.

Lean positions `p = 0, 1, 2, 3` are the paper's positions 1–4.

| Position | Pair | Lower half | Upper half | Lean |
|---|---|---|---|---|
| 1 | (4,5) | certified (Theorem L′) | certified (Theorem M) | `ZN1_two_sided_moments` (`vector_shear_position_one_exact`) |
| 2 | (4,1) | certified (O3) | conditional on `ThmN` (Theorem N) | `middle_position_pair` |
| 3 | (4,1) | certified (O3) | conditional on `ThmN` (Theorem N) | `middle_position_pair` |
| 4 | (4,1) | certified (O3) | conditional on `ThmKUpper` (Theorem K) | `position_four_pair` |
| all | table | — | conditional on `ThmK`, `ThmN` | `mainTheorem_shear` (`vector_shear_main_theorem`), `mainTheorem_shear_ratio` |

| Further result | Lean | Status |
|---|---|---|
| Normalization (Theorem H §2) | `shear_normalize` | certified |
| Separation `Z_{N,1}/Z_{N,4} ≥ c log⁴ N` | `separation_moments` | conditional on `ThmKUpper` |
| Invertible contrast (O5): inverse criterion; separation through an invertible block, `σ > 0` | `inverse_criterion`, `rank_one_criterion`, `sepMap_injective`, `sepLin_lower`, `sep_absorb` | certified |
| Invertible contrast: network-level placement independence at depths 4 and 5 | — | not formalized |
| E₀ identity | `bordered_det`, `null_direction` | certified |
| X1 normal form (`β₀ > 0`), X2 coefficients | `normalize_Aeta`, `errPη_coeff_ne3`, `errPη_c2` | certified (the `β₀ < 0` swap is not formalized) |
| X4: `Z_N(A_η) ≥ c N⁻⁴ (1 + 𝓛_η(N))⁴`, uniform in `\|η\| ≤ 1/10` | `X4_lower_population`, `X4_lower_gaussian` | certified |
| X5, X6 | — | not formalized |
| Theorems K and N | enter only as `ThmK`/`ThmKUpper` and `ThmN` | not formalized |
| SLT layer (normal crossings, products, comparability) | `VectorSLT.SLT.*` | certified |

`ThmK`, `ThmKUpper` and `ThmN` enter only as hypotheses. Each states the paper's bound on the common footing of `Separation.lean` (`Zpos`, `popLossA`, `φ · χ(θ − θ₀⁽ᵖ⁾)`), and none is proved here.

Every declaration in `VectorSLT/Audit.lean` (199) and `checks/PaperAudit.lean` (63) depends on exactly `propext`, `Classical.choice` and `Quot.sound`.
