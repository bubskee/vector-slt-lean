# Loss comparison at positions two to four (branch `loss-comparison`)

Paper 2, Appendix E.2, Proposition N2 (first paragraph: `K ≍ |𝐜|² + ‖g(0, w)‖²`; "Radial
integral"), Appendix E.1 (the active coordinates `𝐜`), Appendix C ("Active change of
variables"). Lean source: `VectorSLT/LossCompare.lean` (headline restatements) and
`VectorSLT/LossCompare/*.lean`. Audit: `VectorSLT/LossCompare/Audit.lean` (147 declarations, all
`[propext, Classical.choice, Quot.sound]`). Nothing outside `VectorSLT/LossCompare*` was edited;
the root `VectorSLT.lean`, `VectorSLT/Audit.lean`, `checks/` and `formalization_status.md` are
untouched (build with `lake build VectorSLT.LossCompare.Audit`).

**Status of this pass.** Position four (Lean `p = 3`) is done for items 1–3 and for the
packaging in `PositionMargin` form at every shear target. Item 1 and the packaging are proved at
every position. Positions two and three (Lean `p = 1, 2`) and item 4 are not done (see "Next").
No statement of the paper turned out false; see "Departures" for what differs.

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
| … for every shear target (via `shear_normalize`) | `marginData_shear`, instance `position_four_marginData` | `Package.lean`, `LossCompare.lean` |

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

## Item 4: proposed for the zoo, not done here

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
```

Then `ThmKUpper μ A φ χ` for a shear target `A` follows from `position_four_marginData`,
`measurable_G4`, `angularMargin_G4` and `Zpos_upper_of_margin`, for cutoffs supported in radius
`c · min(1/2, ε/2)` (smaller than the `r` of `mainTheorem_shear` if need be; the main theorem's
statement would take `min r (c · min(1/2, ε/2))`).

## Departures from the paper

1. **No inverse function theorem.** See "Design". `G₄` uses six exact coefficients, eliminated
   against `𝐜` by polynomial identities, not `g(0, w)`.
2. **Lower bound only.** The paper states `K ≍ |𝐜|² + ‖g(0, w)‖²`. An upper bound on `Z_N` needs
   only `≥`, which is what is proved; the `≤` direction is not formalized.
3. **Sub-family.** Six of the error coefficients (plus `𝐜`), not all of them. Their weight-three
   parts are *exactly* the six components of `leadingMap` (no further linear change), so
   `H₄(0, ·) = ‖leadingMap‖²` (Euclidean) rather than "bounded above and below by".
4. **`H₄` has weights three to nine.** `h4 r V` contains `r³` and `r⁶` terms (e.g. `t³`:
   `−r⁶P₁³ + (1 − r³P₀)²P₃`); it is a polynomial in `(r, ξ)`, as item 3 asks.
5. **Ball, not polydisk; constant not explicit.** `U` is the sup-norm ball of radius `ρ ≤ 1/2`
   (`α_k ∈ [1/2, 3/2]` there); `ν_k` is integrated over all of `ℝ`. `J` comes from Haar
   uniqueness. The comparison holds on any ball (the multipliers are bounded by compactness).
6. **Normalization of the cutoff radius** for a general shear target: `r ≤ c · min(1/2, ε/2)`,
   `c = 1/(‖T‖ + 1)`, so that the transported support stays in the `1/2`-ball and `w` in the
   `ε/2`-ball required by `PositionMargin`.

Nothing in the paper turned out false. Imprecisions noticed:
* E.2, Prop. N2: "`g(𝐜, w) − g(0, w) = O(|𝐜|)`" presupposes `g` written in the coordinates
  `(𝐜, w)`, i.e. the local inverse of `(α_k, ν_k) ↦ 𝐜` (Jacobian `3I`, stated in E.1); with it
  `g(0, w)` is analytic but not polynomial in `w`. Harmless; worth a half-sentence.
* E.1 says "`𝐜` replace the active entries as coordinates". At positions two to four the formulas
  `c₃⁽ᵏ⁾ = α_k³ − 1 + P₀⁽ᵏ⁾`, `c₂⁽ᵏ⁾ = 3α_k²ν_k + 3P₁⁽ᵏ⁾` are exact (all four blocks contribute only
  their linear-part cubes in degree three), which Lean confirms (`errθ_coeffs`, `e30_split`).

## Next (positions two and three)

At the middle positions the degree `≤ 5` coefficients do **not** suffice: in Lean's `coeffMid`
the weight-three parts of `st², t³, s⁵, s⁴t, s³t², s²t³` (both rows) satisfy
`(s³t²)₀/3 − (s³t²)₁/3 = (t³)₀ − (t³)₁ − (s²t³)/3` (both sides are `g₃ − g₇`), so they have rank
ten on the eleven generators. Adding the `s⁷` coefficient of row `0` (weight-three part
`3 g₂`) gives rank eleven. So the middle positions need the exact `s⁷` coefficient: a further
truncation level `λ = L + C₃ + C₅ + R₇`, `[λ³]₇ = 3L²C₅ + 3L C₃²`, through the four layers. Its
active entries occur in cubes of both active rows, so the elimination multiplier is
`α₀^{3a} α₁^{3b}`. Items 1 and the packaging are already position-generic.
