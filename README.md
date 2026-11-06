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
| `Gaussian.lean` | L′ and the separation for standard Gaussian inputs | `propLprime_gaussian`, `separation_gaussian` |
| `Pairs.lean` | L4: C and D restated as Laplace lower halves; (K1) as a pair | `position_one_laplaceLower`, `ThmK.hasLaplacePair` |
| `PolyModel.lean` | L5: the network as a degree-≤81 polynomial | `error_isPoly` |
| `GeneralInput.lean` | L5: (G↑) for every input law with finite 162nd moments; L′ and the separation without compact support | `l2_le_sup`, `propLprime_moments`, `separation_moments` |
| `Separation.lean` | L1: `Z_{N,1}/Z_{N,4} ≥ c log⁴N`, with Theorem K as the named hypothesis `ThmK` | `separation`, `separation_tendsto` |

Every audited declaration depends only on `propext`, `Classical.choice` and `Quot.sound`.
