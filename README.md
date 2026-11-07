# VectorSLT

This library holds Lean 4 certificates for the first-shear-position four-logarithm lower bound of the vector (width-two cubic ResNet) SLT project. The mathematics comes from `cubic-chaos` (commits `34c531e` and `b962be0`).

Pins: Lean `v4.35.0` and mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

```bash
lake exe cache get && lake build && lake env lean VectorSLT/Audit.lean
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
| `Gaussian.lean` | L′ and the separation for standard Gaussian inputs | `propLprime_gaussian`, `separation_gaussian` |
| `Pairs.lean` | L4: C and D restated as Laplace lower halves; (K1) as a pair | `position_one_laplaceLower`, `ThmK.hasLaplacePair` |
| `PolyModel.lean` | L5: the network as a degree-≤81 polynomial | `error_isPoly` |
| `GeneralInput.lean` | L5: (G↑) for every input law with finite 162nd moments; L′ and the separation without compact support | `l2_le_sup`, `propLprime_moments`, `separation_moments` |
| `Separation.lean` | L1: `Z_{N,1}/Z_{N,4} ≥ c log⁴N`, with Theorem K as the named hypothesis `ThmK` | `separation`, `separation_tendsto` |

Every audited declaration depends only on `propext`, `Classical.choice` and `Quot.sound`.
