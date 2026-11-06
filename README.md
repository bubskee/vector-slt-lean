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
| `Separation.lean` | L1: `Z_{N,1}/Z_{N,4} ≥ c log⁴N`, with Theorem K as the named hypothesis `ThmK` | `separation`, `separation_tendsto` |

Every audited declaration depends only on `propext`, `Classical.choice` and `Quot.sound`.
