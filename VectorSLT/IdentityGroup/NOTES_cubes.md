# Lemma A-cubes in Lean: notes (branch `p2-cubes`)

Paper 2, Appendix A.1, Lemma "Sums of binary cubes" (`lem:A-cubes`,
`paper/appendices/A_invertible.tex`). The interface is `VectorSLT.IdentityGroup.CubeSumUpper k`
in `VectorSLT/IdentityGroup/Defs.lean`, which this branch commits unchanged.

## Status

| Statement | Lean name | Status |
|---|---|---|
| Upper half, `k = 1` | `VectorSLT.IdentityGroup.cubeSumUpper_one : CubeSumUpper 1` | proved, no hypotheses |
| Upper half, `k = 2` | `VectorSLT.IdentityGroup.cubeSumUpper_two : CubeSumUpper 2` | proved, no hypotheses |
| Upper half, `k = 3` | `VectorSLT.IdentityGroup.cubeSumUpper_three : CubeSumUpper 3` | proved, no hypotheses |
| Upper half, `k = 4` | — | **open** (stretch goal; see "Left open") |
| Lower half, every `k` | `VectorSLT.IdentityGroup.cubeSumLower k : Cubes.CubeSumLower k` | proved, no hypotheses |

`CubeSumLower` is defined in `Cubes/Lower.lean`, not in the shared `Defs.lean`. It says that for
every `r, c > 0` there is `C > 0` with `C N^{-k/3} ≤ ∫_{‖u‖ ≤ r} e^{-cN G_k}` for all `N ≥ 1`.

Build: `lake build VectorSLT.IdentityGroup.Cubes` is clean: no errors, and no warnings from these
files; the only Lake note is the expected "imports Mathlib ... consider adding `module`" on
`Defs.lean`. `VectorSLT.lean` is frozen and does not import this module.

Audit: `lake build VectorSLT.IdentityGroup.AuditCubes`, or
`lake env lean VectorSLT/IdentityGroup/AuditCubes.lean`. This prints axioms for 106 declarations
(the 4 headline restatements and every declaration in `Cubes/*.lean`). Every one depends on
exactly `[propext, Classical.choice, Quot.sound]`. There is no `sorry`, `admit`,
`native_decide`, `set_option` or new axiom.

## Files

* `Cubes/Scaling.lean`: homogeneity. `cubeSumUpper_of_lintegral_lt_top`:
  `∫_{ℝ^{2k}} e^{-G_k} < ∞ → CubeSumUpper k`.
* `Cubes/One.lean`: `k = 1`, plus `outer_le_cubeSumSq` and Gaussian helpers.
* `Cubes/Two.lean`: `k = 2`.
* `Cubes/Chart.lean`: symmetry, radial integration and shear, for any number `n + 1` of forms.
  `cubeSumUpper_of_chart n`: if `∫_{‖w‖ ≤ 2} chartN(w)^{-(n+1)/3} < ∞` then
  `CubeSumUpper (n + 1)`, where `chartN w` is the coefficient norm of `x³ + ∑ ℓ_{w_i}³`.
* `Cubes/Three.lean`: the chart estimate for `n + 1 = 3` (`chart_three`), and `cubeSumUpper_three`.
* `Cubes/Lower.lean`: the lower half.
* `Cubes.lean`: root; imports the above and restates the headline theorems in
  `VectorSLT.IdentityGroup`.
* `AuditCubes.lean`: axiom audit.

## Paper versus Lean

| Paper (proof of `lem:A-cubes`) | Lean |
|---|---|
| `G_k = ‖R_k‖²_coef`, homogeneous of degree six | `cubeSumSq` (Defs), `cubeSumSq_smul` |
| *Zeros*: Vandermonde, so zeros are collinear (k ≤ 3) or two opposite pairs (k = 4) | not formalized and not needed: every Lean bound holds at every point of the box, zeros included |
| *Radial integration*: `∫_0^∞ r^{2k-1} e^{-N r⁶ g} dr = Γ(k/3)/6 · N^{-k/3} g^{-k/3}`, and a finite cover of the sphere | two steps. (1) `cubeSumUpper_of_lintegral_lt_top`: `u ↦ (cN)^{1/6} u` on the whole space, so only `∫ e^{-G} < ∞` is needed. (2) `setLIntegral_chartRegion_le`: the radial variable is the largest coordinate `a₀`, and `lintegral_radial_le` is the same Gamma integral, `∫ |a|^{2n+1} e^{-a⁶ g} da = Γ((n+1)/3)/3 · g^{-(n+1)/3}` |
| finite cover of the sphere by charts | `lintegral_le_mul_setLIntegral_chartRegion`: the sup-norm sphere has `2n` faces, and permutations of the forms with `x ↔ y` map every face onto the face `|a₀| = ‖u‖` (factor `2(n+1)`) |
| "make it `x` by a bounded analytic change of input coordinates" | `shear β : (a, b) ↦ (a, b - βa)`, i.e. `y ↦ y - βx`. `cubeSumSq_shear_le`: factor at most `80` for `abs β ≤ 1`. It preserves volume (`measurePreserving_shear`) and maps the unit ball into the ball of radius 2 (`setLIntegral_chartG_le`) |
| `f₀ = 1 + ∑ αᵢ³, f₁, f₂, f₃` | `H3 p q a b = σ² + τ² + f₂² + f₃²`, forms `(p, q)` and `(a, b)`; `σ = f₀`, `τ = f₁` |
| `k = 1`: `G₁ ≍ ‖u₁‖⁶` | `One.lean`: `G₁ ≥ a⁶ + b⁶ ≥ a² + b² - 2`, a Gaussian |
| `k = 2`: `G₂ ≍ ‖z‖²`, `G₂^{-s}` integrable for `s < 1` | `Two.lean`, a different route (see departures) |
| `k = 3`: `z = (f₀, f₁)` regular in `(q, β_q)`, Jacobian `3q⁴` | the two one-variable substitutions `q ↦ τ` (slope `p²`, `lintegral_ψL_affine_le`) and `p ↦ σ` (derivative `3p²`, `lintegral_ψL_cube_le`) on `p ∈ [-2, -1/2]` |
| on `z = 0`: `f₂ = a b²/(1 + a³)`, residual `g ≳ a² b⁴` | `residual_identity`: `ab² = τ (p²q - a²b) + σ ab² - p³ f₂`, so `ab_sq_le`: `a²b⁴ ≤ 768 H` on the box, at every point, not only on `z = 0` |
| `∫ (‖z‖² + g)^{-1-δ} dz ≤ C g^{-δ}`, `g^{-δ}` integrable for `δ < 1/4` | `inv_le_weights`: `H⁻¹ ≤ 768^{1/5} ‖σ‖^{-4/5} ‖τ‖^{-4/5} ‖a‖^{-2/5} ‖b‖^{-4/5}` (from `min(X, Y, Z) ≤ X^{2/5} Y^{2/5} Z^{1/5}`); every exponent is below one (`lintegral_ψL_lt_top`) |
| "the ball of radius `N^{-1/6}` gives the lower bound" | `cubeSumLower_all`, using `cubeSumSq_le : G_k ≤ 4k² ‖u‖⁶` |

## Departures from the paper's proof

1. **No local charts at the zeros.** The paper proves local integrability of `G_k^{-s}` near
   every nonzero zero, then covers the sphere. The Lean proof uses one global affine chart (the
   face `|a₀| = ‖u‖` of the sup-norm sphere) and the symmetry group of `G_k` to reach it. It
   never classifies the zeros.
2. **Homogeneity on the whole space.** The dependence on `N` and `c` is removed once by scaling
   (`cubeSumUpper_of_lintegral_lt_top`), instead of tracking `N` through the radial integral.
3. **`k = 1, 2` without charts.** `G_k ≥ (∑ aᵢ³)² + (∑ bᵢ³)²` separates the `a`-entries from the
   `b`-entries. For `k = 2`, `(x³ + y³)² ≥ (x⁴/8 + 1/32)(x + y)² - 1/32` (`two_cube_lower`) gives
   a Gaussian in `y` of width `≤ 16 (1 + |x|)^{-2}`. This route fails for `k = 3`: `|∑_{i≤3} aᵢ³|^{-1}`
   is not locally integrable, so `k = 3` needs all four moments.
4. **Exact exponent only.** The paper shows `G₃^{-s}` integrable near collinear zeros for every
   `s < 5/4`. The Lean proof shows integrability of `chartN^{-1}` on the ball of radius 2, which
   is what the radial step needs (`s = k/3 = 1`). The weights `(2/5, 2/5, 1/5)` keep every
   one-variable exponent below one; the paper's margin `1/4` appears as `4/5 < 1` on `|b|`.
5. **The residual on the whole box, not on `z = 0`.** The paper sets `z = 0` and bounds the
   change of `f₂, f₃` by `O(‖z‖)`. `residual_identity` is an exact polynomial identity, so
   `a²b⁴ ≤ 768 H` holds everywhere on the box with no Lipschitz step. Only `f₂` is used; the paper
   also uses `f₃` to get `b⁴(a² + b²)`, which is not needed for integrability.
6. **Choice of the substituted form.** The paper picks a nonzero `αᵢ` at each collinear zero.
   Lean splits the box by `|a| ≤ |p|` or `|p| ≤ |a|` (symmetric under exchanging the two forms).
   On the half `|a| ≤ |p|`, `|σ| < 1/4` forces `p ≤ -1/2` (`le_neg_half_of_sigma_small`), so the
   Jacobians `p²` and `3p²` are bounded below. Where `|σ| ≥ 1/4`, simply `H⁻¹ ≤ 16`.

## Errors or gaps found in A.1

None that affect the statement or the proof. Checked by hand while formalizing:

* `f₂|_{z=0} = ab²/(1 + a³)` and `f₃|_{z=0} = (1 + 2a³) b³/(1 + a³)²` (k = 3): correct.
* `det(½ Hess_{b,d} Q) = ac/D` and the completed-square identity for `a₀ = c₀ = 0` (k = 4):
  correct.
* The radial formula `∫_0^∞ r^{2k-1} e^{-N r⁶ g} dr = Γ(k/3)/6 · N^{-k/3} g^{-k/3}`: correct.

The interface `CubeSumUpper k` is not awkward. As stated it holds for every `r > 0`, not only small
boxes, because the Lean proof bounds the integral over the whole space.

## Left open

* **`k = 4`** (used only in the depth-five remark). `Chart.lean` is general, so
  `cubeSumUpper_of_chart 3` reduces `CubeSumUpper 4` to the estimate
  `∫_{‖w‖ ≤ 2} chartN(w)^{-4/3} < ∞` for three forms `(p, q), (a, b), (c, d)`. What is missing is
  the analogue of `Three.lean`:
  1. a symmetry reduction to the form with the largest `|α|` among three (three regions instead
     of two), then the same `(σ, τ)` substitution;
  2. the residual. The identity analogous to `residual_identity` comes from
     `D Q = ab² + cd² + ac (bc - ad)²` with `D = 1 + a³ + c³`, where `Q` is the paper's
     `𝒬 = ab² + cd² - (a²b + c²d)²/D`;
  3. the missing estimate: `(P² + F₃²)^{-w}` integrable on the box for some `w > 1/3`, where
     `P = ab² + cd² + ac (bc - ad)²` and `F₃` is the cubic residual at `z = 0`. This is the
     paper's analysis of `𝒬` (definite, one-zero-diagonal, and `a₀ = c₀ = 0` cases) together with
     the noncollinear stratum `(a, b) = -(c, d)`, where `P` and `F₃` both vanish. With weights
     `w₁ = w₂ < 1/2` on `σ, τ`, the exponent on the residual must exceed `1/3`; the paper's
     indefinite threshold `1/2` leaves room.
* The paper's sharper local thresholds (`5/4` for `k = 3`, `3/2` for `k = 4`) and the remark
  after the proof are not formalized and not needed.
