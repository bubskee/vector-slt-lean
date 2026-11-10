# Loss comparison at positions two to four

Paper 2, `paper/appendices/D_positions.tex`: D.2, Proposition N2 (first paragraph:
`K ≍ |𝐜|² + ‖e'(0, w)‖²`; "Radial integral"), D.1 (the active coordinates `𝐜`, Proposition N1,
Lemma N3); Appendix C ("Active change of variables"). (The first pass cited the old `E_n.tex`,
E.1/E.2; same statements.) Lean source: `VectorSLT/LossCompare.lean` (headline restatements) and
`VectorSLT/LossCompare/*.lean`. Audit: the 305 declarations are in `VectorSLT/Audit.lean` (304
on `[propext, Classical.choice, Quot.sound]`, one, `rowOf`, on `[propext]` only), and the eight
headlines in `checks/PaperAudit.lean`. The module was written on the branch `loss-comparison`,
where it had its own audit file and nothing outside `VectorSLT/LossCompare*` was edited. The
release pass imported it from the root `VectorSLT.lean` and moved that audit into the library
audit.

**Status.** Items 1–3 and the packaging in `PositionMargin` form (for every shear target) are
done at positions two, three and four (Lean `p = 1, 2, 3`). Item 4 is left to the slt-bridge zoo
(sketch below). No statement of the paper turned out false; see "Departures" for what differs.
History: position four on `ff34cda`; positions two and three on top of it.

## What is proved

| Brief / paper | Lean | File |
|---|---|---|
| exact error coefficients `s³, s²t, st², t³, s⁵, s⁴t`, every `θ` (E.1; M1) | `errθ_coeffs`: `[err_k]_m = e30 / e21 / e12 / e03 / e50 / e41 (rawW θ) k`, formulas in the row forms `(a_l, b_l)` of the four raw blocks | `Coeffs.lean` |
| (G↓) for the coefficients used | `gdown_family`: for any finite family `(k_j, m_j)`, `κ ∑_j [err_{k_j}]_{m_j}² ≤ K(θ)` | `Coeffs.lean` |
| active coordinates `𝐜 = (c₃⁽ᵏ⁾, c₂⁽ᵏ⁾)` | `cvec θ = (e30 0, e21 0, e30 1, e21 1)`; `e30_split`, `e21_split`: `c₃ = α³ − 1 + P₀`, `c₂ = 3α²ν + 3P₁` at every position | `ChangeVar.lean` |
| inactive coordinates `w` | `wOf p θ = flat (Fin.removeNth p (rawW θ))`, block-major `w(4l+2i+j) = V_l i j` | `ChangeVar.lean` |
| **item 1**, Appendix C change of variables | `cov_bound p (hρ : ρ ≤ 1/2)`: `∫ f(Ψ_p θ) 𝟙_{closedBall (basePos A₀ p) ρ}(θ) dθ ≤ J ∫ f`, every measurable `f ≥ 0`, every `p` | `ChangeVar.lean` |
| **item 2** at position four, Prop. N2 first paragraph (lower half) | `loss_compare_four`: `κ (∑ᵢ 𝐜ᵢ² + G₄(w)) ≤ popLossA μ A₀ θ` on `closedBall (basePos A₀ 3) ρ`, any `ρ`, laws with the `Gdown` hypotheses | `PositionFour.lean` |
| the inactive function | `G₄ = H₄(1, ·) = ∑ᵢ ĝᵢ²`, six explicit polynomials `ĝᵢ = h4 1 (unflat w) i` | `PositionFour.lean` |
| **item 3**, weighted homogeneity (Prop. N2 "Stability": `g(0, r ι η) = r³ 𝒢`) | `G4_smul`: `G₄(r • ξ) = r⁶ H₄(r, ξ)` for every real `r`; `H4_nonneg`; `continuous_H4` (jointly in `(r, ξ)`); `H4_zero`: `H₄(0, ξ) = ∑ᵢ (leadingMap (w4 (unflat ξ)))ᵢ²` exactly; `H4_zero_bounds` (sup norm) | `PositionFour.lean` |
| `PositionMargin` minus the margin, at `A₀` | `MarginData`, `marginData_A0` | `Package.lean` |
| … for every shear target (via `shear_normalize`) | `marginData_shear`, instances `position_four_marginData`, `middle_marginData` | `Package.lean`, `LossCompare.lean` |
| exact `s³t²` and `s⁷` coefficients, every `θ` | `errθ_coeff32`, `errθ_coeff70` (degree-seven truncation `stP_decomp7`, `cube_decomp9`) | `Coeffs7.lean`, `Tables.lean` |
| all coefficients used, as polynomials in the cube moments of the blocks | `C12, C03, C50, C41, C32, C70` on tables `Tab4`; `C12_eq` … `C41_eq` | `Tables.lean` |
| `e'(𝐜, w) − e'(0, w) = O(|𝐜|)` (D.2), every position | `elim_bound`: if `A f = F(z_act, w)` with `F` of class `C¹`, then `F(z₀(w), w)² ≤ K (f² + ‖𝐜‖²)` on compacts | `Elim.lean` |
| **item 2** at positions two, three | `loss_compare_mid` / `middle_comparison`: `κ (∑ᵢ 𝐜ᵢ² + G_p(w)) ≤ popLossA μ A₀ θ` | `MiddleCompare.lean` |
| the inactive functions | `Gmid p = Hmid p 1`, `Hmid p r ξ = ∑ᵢ (Nmid h(r³, ·))ᵢ²`, eleven components | `Middle.lean`, `MiddleCompare.lean` |
| **item 3** at positions two, three | `Gmid_smul`, `Hmid_nonneg`, `continuous_Hmid`; `Hmid_zero_one`: `H(0, ξ) = ∑ᵢ (R2 (w2 (unflat ξ)))ᵢ²`, `Hmid_zero_two`: same with `R3`, `w3`, exactly | `MiddleCompare.lean` |
| Proposition N1 at `𝐜 = 0`, checked again | `Lw_eq`: the weight-three parts of the eleven eliminated coefficients are the N1 entries (`Lexp`), 22 cases | `Middle.lean` |

## Design

**Coordinates.** `Ψ_p θ = (𝐜(θ), w(θ))` with `𝐜` the *exact* `s³, s²t` coefficients of both
rows. These are the same at every position: the degree-three part of the error is
`∑_{all four blocks} (row form)³ − s³`. So `Ψ_p = Φ ∘ L_p` with `L_p` linear (active row forms,
`w`) and `Φ` the triangular map of Appendix C rowwise. `cov_bound`: `ν ↦ 3α²ν + 3P₁` is affine with
slope `≥ 3/4` (`lintegral_comp_affine`), `α ↦ α³` has derivative `≥ 3/4` on `[1/2, 3/2]`
(`lintegral_image_eq_lintegral_abs_deriv_mul`), Fubini over the two rows and over `w`. The linear
maps `L_p : Raw16 ≃ (ℝ×ℝ)² × ℝ¹²` and `(ℝ×ℝ)² ≃ ℝ⁴` cost a finite constant by uniqueness of Haar
measure (`lintegral_comp_clequiv`); `J` is not explicit.

**Elimination instead of the inverse function theorem.** The paper writes the remaining
coefficients as `g(𝐜, w)` (implicitly through the inverse of `(α, ν) ↦ 𝐜`) and uses
`g(𝐜, w) − g(0, w) = O(|𝐜|)`. `g(0, w)` is then not a polynomial in `w` (it involves
`(1 − P₀)^{1/3}`). Lean avoids the inverse: every error coefficient is a polynomial in the active
row entries in which each row's entries occur only through cubes `(α s + ν t)³` of that row, so a
power `α^{3j}` times the coefficient is a polynomial in `u = α³` and `m = α²ν`, and
`u = 1 + c₃ − P₀`, `m = c₂/3 − P₁`. Setting `𝐜 = 0` gives polynomials `ĝᵢ(w)`, and
`ĝᵢ = Aᵢ fᵢ + Bᵢ c₃ + Dᵢ c₂` exactly with polynomial multipliers (`ghat_eq`; the four ring
identities `elim_st`, `elim_t3`, `elim_s5`, `elim_s4`). At the point with `𝐜 = 0` (where it
exists, `α³ = 1 − P₀`, `α²ν = −P₁`), `ĝᵢ(w) = cᵢ (1 − P₀(w))^{jᵢ} gᵢ(0, w)` with constants
`cᵢ ∈ {1/3, 1/9, 1/3, 1}` and `jᵢ ∈ {0, 1, 2}` (the multiplier column below), a factor close to a
constant near `w = 0`; so `G₄` is the paper's `‖g(0, w)‖²` restricted to six coefficients, up to
these factors.
On a compact ball the multipliers are bounded (`continuous_mbound`), so `ĝᵢ² ≤ 3K²(fᵢ² + c₃² + c₂²)`
(`sq_le_of_lin`), and `gdown_family` for the ten coefficients closes the comparison.

**The six coefficients at position four** (only lower bounds on `K` are needed, so a sub-family
suffices): `s⁵`, `s⁴t` of row `0`, and `st²`, `t³` of both rows. With `u, m` of the row in
question, `P_i = P_i⁽ᵏ⁾` over the three inactive blocks, `q_i = P_i⁽¹⁾`, `D_i = P_i⁽⁰⁾ − P_i⁽¹⁾`,
and `W₅, W₄` the prefix-internal terms of `s⁵, s⁴t` (weight six):

| coefficient `f` | multiplier | `F(u, m)` | `ĝ = F(1 − P₀, −P₁)` (normalized) | weight three of `ĝ` |
|---|---|---|---|---|
| `s⁵` (row 0) | `1/3` | `W₅/3 + u D₀ + m q₀` | `W₅/3 + (1−P₀)D₀ − P₁q₀` | `D₀ = F₀` |
| `s⁴t` (row 0) | `α³/9` | `(u W₄ + 9u²D₁ + 9um q₁ + 6um D₀ + 6m² q₀)/9` | same at `(1−P₀, −P₁)` | `D₁ = F₁` |
| `st²` (row k) | `α³/3` | `m² + u P₂` | `P₁² + (1−P₀)P₂` | `P₂⁽ᵏ⁾ = Q₁, Q₂` |
| `t³` (row k) | `α⁶` | `m³ + u² P₃` | `−P₁³ + (1−P₀)²P₃` | `P₃⁽ᵏ⁾ = Φ(B), Φ(D)` |

`h4 r V` is `ĝ` with each weight-`w` term multiplied by `r^{w−3}`, so `ĝ(r V) = r³ h4 r V`
(`h4_smul`) and `h4 0 V = leadingMap (w4 V)` (`h4_zero`, checked by `simp`, so the normalization
is exactly the slt-bridge component order `(F₀, F₁, Q₁, Φ(B), Q₂, Φ(D))`).

**Packaging.** `MarginData μ A φ χ p G ε` is slt-bridge's `PositionMargin μ A φ χ p`
(`zoo/Zoo/TemplateMargin.lean` on `main`) without the clauses `Measurable G`, `2 < s`, `0 ≤ M`,
`AngularMargin G 3 s ε M`; Mathlib vocabulary only. `marginData_shear`: for a shear target `A`
there is `c > 0` such that for every `ε` and cutoff radius `0 ≤ r ≤ c · min(1/2, ε/2)` (and the
prior/cutoff bounds of `mainTheorem_shear`) `MarginData μ A φ χ p G ε` holds with `Ψ' = Ψ_p ∘ T`,
`T` the normalizing automorphism; the input law is pushed forward (`moments_map`, `density_map`)
and the loss compared by `loss_compare`, as in `theoremM_shear`.

## Positions two and three (Lean `p = 1, 2`)

**Coefficients.** Eleven: `st²`, `t³`, `s⁵`, `s⁴t`, `s³t²` of both rows and `s⁷` of row `0`
(`cf`). Their weight-three parts (`Lexp`) in the generators `g = (p¹₂, p¹₃, q¹₂, q¹₃, p²₂, p²₃,
q²₂, q²₃, p¹₁ − p²₁, q¹₁ − q²₁, p¹₀ − p²₀ + q¹₁)` are
`3(g₀+g₂), g₁+g₃, 3(g₄+g₆), g₅+g₇, 3g₁₀, 3(g₁₀−g₉), 3(3g₈+2g₂), 3(3g₈+2g₆), 3(3(g₀−g₄)+g₃),
3(3(g₀−g₄)+g₇), 3g₂`, and `Nmid` inverts this (`Nmid_Lexp`). The paper's Lemma N3 uses `s⁷` and
`s⁶t`; here `s⁷` (row 0) and `s³t²` (both rows) are used instead. `s³t²` is the lowest-degree
coefficient that separates the prefix `t³` moments from the suffix ones, and with `s⁷` of row 0
the eleven are independent (degree at most five alone has rank ten).

**Exact coefficients.** All six coefficient types are polynomials in the table of cube moments
`cube (rowForm (W l) k) = (a³, a²b, ab², b³)` of the four blocks: degree three linear, degree five
a sum over pairs `j < l` of bilinear block terms, `s⁷` cubic (`Tables.lean`, checked against the
network in rational arithmetic before the Lean proof). `s⁷` needed one more truncation level
(`Coeffs7.lean`).

**Elimination.** The active row `k` enters through `(u_k, m_k, n_k, o_k) = (α³, α²ν, αν², ν³)`,
and each coefficient is affine in the `n`'s and `o`'s that occur. A monomial multiplier `Mult j`
in `u₀, u₁` (`u_k`, `u_k²`, `1`, `u_k`, `u_k² u_{k'}`, `u₀` for the six types) clears them, via
`u n = m²`, `u² o = m³`: `Mult j · cf j = Fm p j (z_act, a)` (`mult_identity`, 22 `ring`
identities). `ĝ_j = Fm p j (z₀, a)`. Instead of explicit multipliers of `c₃, c₂` (position four),
`elim_bound` uses that `Fm` is `C¹`, hence Lipschitz on a compact set, and `z_act − z₀ = (c₃⁽⁰⁾,
c₂⁽⁰⁾/3, c₃⁽¹⁾, c₂⁽¹⁾/3)` exactly.

**Homogeneity without expanding.** Under `V ↦ r V` the inactive cube moments scale by `s = r³`,
and the table at `𝐜 = 0` is `e + s y` with `e` the constant table (`u = 1`). Each coefficient
functional is linear, quadratic or cubic in the table and vanishes at `e`, so
`C(e + s y) = s · (C(e + y) − C(y) + s C(y))` (quadratic) and the analogous identity with `C(e − y)`
for the cubic `s⁷` (`pol12` … `pol70`). This gives `ĝ_j(s a) = s h_j(s, a)` with `h_j` an explicit
combination of evaluations of the same functionals (`ghat_smul`), jointly continuous, and
`h_j(0, a) = Lw p a j`, the linear part.

## Item 4: left to the slt-bridge zoo

The radial split, the Gaussian factor and `laplaceUpper_of_angularMargin` are in slt-bridge
(`SLT/Template/Margin.lean`). Re-proving them in vector-slt-lean would duplicate about 300 lines.
`MarginData` makes the zoo glue a few lines (untested sketch, for `zoo/Zoo/TemplateMargin.lean`):

```lean
open VectorSLT.LossCompare in
theorem positionMargin_of_marginData {μ A φ χ p} {G : (Fin 12 → ℝ) → ℝ} {s ε M : ℝ}
    (hG : Measurable G) (hs : 2 < s) (hM : 0 ≤ M) (hA : AngularMargin G 3 s ε M)
    (h : MarginData μ A φ χ p G ε) : PositionMargin μ A φ χ p := by
  obtain ⟨Ψ, J, κ, hΨ, hκ, hJ, hcmp⟩ := h
  exact ⟨Ψ, G, J, κ, s, ε, M, hΨ, hG, hκ, hs, hM, hA, hJ, hcmp⟩

/-- The angular margin of `G₄` from the margin of `H₄` alone. -/
theorem angularMargin_G4 {s ε M : ℝ}
    (h : ∀ r : ℝ, 0 < r → r ≤ ε →
      ∫⁻ ξ in shell 12, ENNReal.ofReal (VectorSLT.LossCompare.H4 r ξ) ^ (-s) ≤ ENNReal.ofReal M) :
    AngularMargin VectorSLT.LossCompare.G4 3 s ε M :=
  ⟨VectorSLT.LossCompare.H4, fun r _ _ ξ _ =>
    ⟨by simpa using VectorSLT.LossCompare.G4_smul r ξ, VectorSLT.LossCompare.H4_nonneg r ξ⟩, h⟩

/-- The same at positions two and three (`p = 1, 2`, `G = Gmid p`, `H = Hmid p`). -/
theorem angularMargin_Gmid {p : Fin 4} (hp : p = 1 ∨ p = 2) {s ε M : ℝ}
    (h : ∀ r : ℝ, 0 < r → r ≤ ε →
      ∫⁻ ξ in shell 12, ENNReal.ofReal (VectorSLT.LossCompare.Hmid p r ξ) ^ (-s) ≤
        ENNReal.ofReal M) :
    AngularMargin (VectorSLT.LossCompare.Gmid p) 3 s ε M :=
  ⟨VectorSLT.LossCompare.Hmid p, fun r _ _ ξ _ =>
    ⟨by simpa using VectorSLT.LossCompare.Gmid_smul hp r ξ,
      VectorSLT.LossCompare.Hmid_nonneg p r ξ⟩, h⟩
```

Then, for a shear target `A`:
* `ThmKUpper μ A φ χ` from `position_four_marginData hA`, `measurable_G4`, `angularMargin_G4`,
  `positionMargin_of_marginData` and `Zpos_upper_of_margin`;
* `ThmN μ A φ χ` from `middle_marginData hA (Or.inl rfl)`, `middle_marginData hA (Or.inr rfl)`,
  `measurable_Gmid`, `angularMargin_Gmid` and the same two zoo lemmas (`thmN_of_margin`);
for cutoffs supported in radius `c · min(1/2, ε/2)` (one `c` per position; the main theorem would
take the minimum of these and the `r` of `mainTheorem_shear`). The only remaining hypotheses are
the three angular margins of `H₄ = H4`, `H₂ = Hmid 1`, `H₃ = Hmid 2` on the shell, with `s > 2`.

## Departures from the paper

1. **No inverse function theorem.** See "Design". `G₄` uses six exact coefficients and `G₂`, `G₃`
   eleven, eliminated against `𝐜` by polynomial identities, not `e'(0, w)` itself.
2. **Lower bound only.** The paper states `K ≍ |𝐜|² + ‖g(0, w)‖²`. An upper bound on `Z_N` needs
   only `≥`, which is what is proved; the `≤` direction is not formalized.
3. **Sub-family.** Six (position four) or eleven (positions two, three) of the error coefficients
   (plus `𝐜`), not all of them. At position four their weight-three parts are exactly the six
   components of `leadingMap`; at positions two and three a fixed invertible linear change `Nmid`
   makes them exactly the eleven components of `R2`, `R3`. So `H_p(0, ·) = ‖gens_p‖²` (Euclidean)
   at all three positions, rather than "bounded above and below by". At the middle positions
   `s³t²` replaces the paper's `s⁶t` (Lemma N3); either works.
4. **`H_p` has higher weights.** `h4 r V` contains `r³` and `r⁶` terms (e.g. `t³`:
   `−r⁶P₁³ + (1 − r³P₀)²P₃`); at the middle positions `h_j(r³, ·)` is a combination of evaluations
   of the coefficient functionals, a polynomial in `(r, ξ)`. In both cases `H_p` is jointly
   continuous, which is what item 3 asks.
5. **Ball, not polydisk; constant not explicit.** `U` is the sup-norm ball of radius `ρ ≤ 1/2`
   (`α_k ∈ [1/2, 3/2]` there); `ν_k` is integrated over all of `ℝ`. `J` comes from Haar
   uniqueness. The comparison holds on any ball (the multipliers are bounded by compactness).
6. **Normalization of the cutoff radius** for a general shear target: `r ≤ c · min(1/2, ε/2)`,
   `c = 1/(‖T‖ + 1)`, so that the transported support stays in the `1/2`-ball and `w` in the
   `ε/2`-ball required by `PositionMargin`.

Nothing in the paper turned out false. Imprecisions noticed:
* (Fixed in `D_positions.tex`, which now writes the analytic map `e'(𝐜, w)`.) The old E.2 wrote
  `g(𝐜, w) − g(0, w) = O(|𝐜|)` without saying `g` is taken in the coordinates `(𝐜, w)`.
* D.1 says "`𝐜` replace the active entries as coordinates". At positions two to four the formulas
  `c₃⁽ᵏ⁾ = α_k³ − 1 + P₀⁽ᵏ⁾`, `c₂⁽ᵏ⁾ = 3α_k²ν_k + 3P₁⁽ᵏ⁾` are exact (all four blocks contribute only
  their linear-part cubes in degree three), which Lean confirms (`errθ_coeffs`, `e30_split`).
