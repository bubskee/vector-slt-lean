# Leading maps at positions two, three and four (branch `leading-maps`)

Paper 2, Appendix E.1 (Proposition N1, Lemma N3) and Appendix D.1 (equation (K-R)). The Lean source
is `VectorSLT/LeadingMap.lean` (headline restatements) and `VectorSLT/LeadingMap/*.lean`.

**Outcome.** The table derived in Lean agrees with the paper's Proposition N1 entry for entry, at
both middle positions and (with empty suffix) at position four. The generators agree component by
component with slt-bridge's `SLT.MiddlePositions.generators`, `R2`, `R3` and
`SLT.PositionFour.leadingMap`. No sign, factor or generator is wrong or missing. The paper has one
notation slip (`D_i` defined, `Δ_i` used in the table; see "Departures"). The expansion is proved
with remainder `O(ε⁶)`.

## What is proved

| Paper | Lean | File |
|---|---|---|
| The parameter: inactive entries weight one, active coordinates weight three | `thetaEps A Δ p V ε`: active block `A + ε³ Δ` at Lean position `p`, inactive blocks `ε V₀, ε V₁, ε V₂` in application order (`scaledBlocks`, via `Fin.insertNth`). `thetaEps_zero`: at `ε = 0` it is `basePos A p` | `Expansion.lean` |
| Weight-three part of the error (proof of N1, first display) | `lead A p Δ V x = 3 (A x)^{⊙2} ⊙ (Δ x) + DF_A(x) S_pre(x) + S_suf(F_A x)` | `Expansion.lean` |
| "no error coefficient has weight below three", and the weight-three part is `lead` | `net_expansion`: `net θ_ε x k − F_A(x)_k − ε³ lead A p Δ V x k = O(ε⁶)` at `𝓝 0` (every `A`, `p`, `Δ`, `V`, `x`, `k`); `net_expansion_four`: the same with `O(ε⁴)` | `Expansion.lean` |
| (`lead` is *the* coefficient) | `lead_unique`: any `L` with remainder `O(ε⁴)` equals `lead A p Δ V x k` | `Expansion.lean` |
| Proposition N1 table | `lead_A0_eq_table`: `lead A₀ p Δ V x k = poly11 (n1Coeff p Δ V k) (x₀ − x₁) x₁`, at every Lean `p` (at `p = 0` the prefix is empty, so all `D_i = 0`) | `Table.lean` |
| The eleven monomials are independent | `poly11_eq_zero` | `Table.lean` |
| slt-bridge's maps | real mirrors `Form`, `Cubic`, `cube`, `twoCube`, `Row`, `rowCubic`, `leadingMap`, `generators`, `Row2`, `Row3`, `R2`, `R3` | `Generators.lean` |
| The twelve inactive variables in slt-bridge's layout | `w2 V`, `w3 V`, `w4 V`; `gens2 V = R2 (w2 V)`, `gens3 V = R3 (w3 V)`, `gens4 V = leadingMap (w4 V)` | `Generators.lean` |
| Active coordinates `𝐜` | `activeCoords Δ V = activeLin Δ + activeCoords 0 V` (`activeCoords_eq`), `activeLin` a linear equivalence `Mat₂ ≃ₗ ℝ⁴`; `activeCoords_bijective` | `Tie.lean` |
| Lemma N3 (positions two, three) | `lead_A0_pos2`: `lead A₀ 1 Δ V = LamMid (activeCoords Δ V, gens2 V)`; `lead_A0_pos3`: the same with `gens3`; `LamMid_injective` | `Tie.lean` |
| (K-R) (position four) | `lead_A0_pos4`: `lead A₀ 3 Δ V = LamFour (activeCoords Δ V, gens4 V)`; `LamFour_injective` | `Tie.lean` |
| "`R_j` is the weight-three part with `𝐜 = 0`" | `lead_A0_pos{2,3,4}_eq_zero_iff`: the `ε³` term vanishes iff `activeCoords Δ V = 0` and the generators vanish | `Tie.lean` |
| headline restatements | `leading_expansion`, `leading_term_unique`, `prop_N1_table`, `lemma_N3_position_two`, `lemma_N3_position_three`, `eq_KR_position_four`, `lead_A0_eq_zero_iff` | `LeadingMap.lean` |

Every declaration depends only on `propext`, `Classical.choice`, `Quot.sound`. Nothing has a
hypothesis beyond its arguments.

### How the expansion is proved

`Exp3 f a b` says `f ε = a + ε³ b + O(ε⁶)` in each coordinate. The input `x` is `Exp3` with
`b = 0`. An inactive layer `F_{εB}` adds `ε³ (B z)^{⊙3}` and keeps `Exp3` with `b ↦ b + (B a)^{⊙3}`
(`Exp3.inactive`). The active layer `F_{A+ε³Δ}` gives `a ↦ F_A a`, `b ↦ DF_A(a) b + 3 (A a)^{⊙2} ⊙ (Δ a)`
(`Exp3.active`). Four applications in the order of the blocks give `lead`. The only analytic input
is `IsBigO` algebra for products and sums (`cube_exp`, `cube_small`). No degree-81 polynomial is
expanded.

## The table, derived

Coordinates `s = x₀ − x₁`, `t = x₁`. `F_{A₀}(s, t) = (s, t + s³)`, `A₀ x = (s, s)`, and
`DF_{A₀}(x) u = u + 3 s² (u₀ − u₁, u₀ − u₁)`. Row `k` of an inactive block `V` is the form
`a s + b t`, `a = V k 0`, `b = V k 0 + V k 1` (`rowForm`). Moments of row `k` over a set `X` of
inactive blocks: `P_i[X] = ∑_{l∈X} a_l^{3−i} b_l^i` (`mom`). Prefix cubic `p^k = ∑_{pre} (a s + b t)³`,
suffix cubic `q^k`. `D_i = P_i^{(0)}[pre] − P_i^{(1)}[pre]` (`momD`).

The three terms of `lead A₀ p Δ V x`, row `k`:
* active: `3 s² (Δ_{k0} x₀ + Δ_{k1} x₁) = 3 Δ_{k0} s³ + 3 (Δ_{k0} + Δ_{k1}) s² t`;
* prefix: `p^k + 3 s² (p⁰ − p¹) = p^k + 3 D₀ s⁵ + 9 D₁ s⁴t + 9 D₂ s³t² + 3 D₃ s²t³`;
* suffix: `∑_{suf} (σ + b s³)³ = q^k + 3 s³ ∑ b σ² + 3 s⁶ ∑ b² σ + s⁹ ∑ b³`
  `= q^k + 3 Q₁ s⁵ + 6 Q₂ s⁴t + 3 Q₃ s³t² + 3 Q₂ s⁷ + 3 Q₃ s⁶t + Q₃ s⁹`, with `Q_i = P_i^{(k)}[suf]`.

Sum (`n1Coeff`), compared with the paper:

| monomial | derived (Lean) | paper (Prop. N1) |
|---|---|---|
| `s³` | `3 Δ_{k0} + P₀[all]` | `c₃^{(k)}` (its `ε³` part; see departure 2) |
| `s²t` | `3 (Δ_{k0} + Δ_{k1}) + 3 P₁[all]` | `c₂^{(k)}` (its `ε³` part) |
| `st²` | `3 P₂[all]` | `3 P₂[all]` |
| `t³` | `P₃[all]` | `P₃[all]` |
| `s⁵` | `3 (D₀ + P₁[suf])` | `3 (Δ₀ + P₁[suf])` |
| `s⁴t` | `3 (3 D₁ + 2 P₂[suf])` | `3 (3 Δ₁ + 2 P₂[suf])` |
| `s³t²` | `3 (3 D₂ + P₃[suf])` | `3 (3 Δ₂ + P₃[suf])` |
| `s²t³` | `3 D₃` | `3 Δ₃` |
| `s⁷` | `3 P₂[suf]` | `3 P₂[suf]` |
| `s⁶t` | `3 P₃[suf]` | `3 P₃[suf]` |
| `s⁹` | `P₃[suf]` | `P₃[suf]` |

All other monomials have zero coefficient. With the suffix empty (position four) this is the D.1
list: `st²: 3Q_k`, `t³: Φ(B), Φ(D)`, `s⁵: 3F₀`, `s⁴t: 9F₁`, `s³t²: 9(Q₁ − Q₂)`,
`s²t³: 3(Φ(B) − Φ(D))`. Matches.

## The tie to the generators

Middle positions (`coeffMid`, generators `g = generators p¹ q¹ p² q²`, Lean rows `0, 1` = slt-bridge
rows `1, 2`):

| monomial | row 0 | row 1 |
|---|---|---|
| `s³`, `s²t` | `c₀`, `c₁` | `c₂`, `c₃` |
| `st²` | `3 (g₀ + g₂)` | `3 (g₄ + g₆)` |
| `t³` | `g₁ + g₃` | `g₅ + g₇` |
| `s⁵` | `3 g₁₀` | `3 (g₁₀ − g₉)` |
| `s⁴t` | `3 (3 g₈ + 2 g₂)` | `3 (3 g₈ + 2 g₆)` |
| `s³t²` | `3 (3 (g₀ − g₄) + g₃)` | `3 (3 (g₀ − g₄) + g₇)` |
| `s²t³` | `3 (g₁ − g₅)` | `3 (g₁ − g₅)` |
| `s⁷`, `s⁶t`, `s⁹` | `3 g₂`, `3 g₃`, `g₃` | `3 g₆`, `3 g₇`, `g₇` |

Here `g₀..g₁₀ = p¹₂, p¹₃, q¹₂, q¹₃, p²₂, p²₃, q²₂, q²₃, p¹₁ − p²₁, q¹₁ − q²₁, p¹₀ − p²₀ + q¹₁`. The
`s⁵` row-1 entry uses `D₀ + q²₁ = g₁₀ − g₉`, which is the paper's "the two `s⁵` entries are
equivalent to `h` and `d`". Injectivity: `s³, s²t` give `c`; `s⁷, s⁶t` give `q^k₂, q^k₃`; then
`st², t³` give `p^k₂, p^k₃`; `s⁴t` gives `g₈`; `s⁵` gives `g₁₀` and `g₉`. All fifteen are recovered.

Position four (`coeffFour`, `g = leadingMap (w4 V) = (F₀, F₁, Q₁, Φ(B), Q₂, Φ(D))`): row `k` is
`c_{2k}, c_{2k+1}, 3·(g₂ | g₄), (g₃ | g₅), 3 g₀, 9 g₁, 9 (g₂ − g₄), 3 (g₃ − g₅), 0, 0, 0`.

## Departures from the paper

1. **Scaling instead of weights.** The paper assigns weight one to the twelve inactive entries and
   weight three to the active coordinates `𝐜`. Lean scales along a ray: inactive `ε V`, active
   `A + ε³ Δ`. The `ε³` coefficient is the weight-three part. The expansion is pointwise in `x`
   and along each ray `ε ↦ θ_ε`; it is not stated uniformly in `(Δ, V)` or in `x` on compacts
   (the paper's E.2 uses the weighted-homogeneous form `g(0, r ι η) = r³ 𝒢(r, η)`; see "Open").
2. **Linear active coordinates.** The paper's `c₃^{(k)} = α_k³ − 1 + P₀^{(k)}[all]` and
   `c₂^{(k)} = 3 α_k² ν_k + 3 P₁^{(k)}[all]` are the exact error coefficients, nonlinear in the
   active entries; the paper then changes coordinates by the inverse function theorem. On the ray
   `α_k = 1 + ε³ Δ_{k0}`, `ν_k = ε³ (Δ_{k0} + Δ_{k1})` their `ε³` parts are `activeCoords`. The
   inverse function step is out of scope.
3. **Notation slip in the paper.** E.1 defines `D_i = P_i^{(1)}[prefix] − P_i^{(2)}[prefix]` and the
   table then writes `Δ_i` (as do Lemma N3's `Δ₀` and D.1). They are the same quantity. Lean calls
   it `momD`; `Δ` in Lean is the active perturbation.
4. **Rows.** The paper's rows `k = 1, 2` are Lean rows `0, 1`; slt-bridge's `w.1`, `w.2` (and
   `p₁, q₁`, `p₂, q₂`) are Lean rows `0, 1`. The generator `h = Δ₀ + q¹₁` uses row `0`.
5. **(K-R) order.** The paper's (K-R) lists `(F₀, F₁, Q₁, Q₂, Φ(B), Φ(D))`; slt-bridge's
   `leadingMap` (and so the Lean mirror) lists `(F₀, F₁, Q₁, Φ(B), Q₂, Φ(D))`. This is a permutation
   of components and changes nothing.
6. **Lemma N3 form.** The paper says the components of `R_j` are the generators "up to an
   invertible linear change of generators". Lean states the equivalent: the leading term is an
   injective linear image `Λ_p` of `(𝐜, gens_p)`.
7. **Real mirrors.** slt-bridge's maps are over `ℂ`; the mirrors are the same formulas over `ℝ`,
   with the same names, argument order and component order, inside `VectorSLT.LeadingMap`.
   `Row` there shadows `VectorSLT.Row` (`FullNetwork.lean`, the raw row of `Raw16`) inside the
   namespace; the audits use full names. `twoCube` is not in the two `Defs.lean` copies; it was read
   from slt-bridge `SLT/PositionFour/Upstream/Algebra.lean` (`twoCube g = cube g.1 + cube g.2`,
   `origin/main` at `ade1897`).
8. **All positions.** `net_expansion` and `lead_A0_eq_table` hold at every Lean `p`, including
   `p = 0` (paper position one, out of scope); the tie (item 3) is stated for `p = 1, 2, 3`.

## Open

- A version of the expansion uniform in `(Δ, V)` on bounded sets and in `x` on compacts, or the
  weighted-homogeneous form `g(0, r ι η) = r³ 𝒢(r, η)` with `𝒢` polynomial, used in E.2. The
  network output is a polynomial in `ε³` along each ray, so this is routine but not done.
- The change to the nonlinear active coordinates by the inverse function theorem, the comparison
  of the population loss with `‖𝐜‖² + ‖R_j‖²`, and the complexification statement in slt-bridge
  (the complex maps there are the complexifications of `R2`, `R3`, `leadingMap` here). All out of
  scope for this branch.
