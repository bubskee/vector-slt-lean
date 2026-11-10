# Pairs (4,1) from the identity-group interface — notes

Branch `p2-f1-invertible`. Lean `v4.35.0`, mathlib `56a0058`, namespace `VectorSLT.IdentityGroup.Pairs`.
Root import: `VectorSLT.IdentityGroup.Pairs`. Audit: `VectorSLT/IdentityGroup/AuditPairs.lean`.

**The only open hypothesis is `CubeSumUpper k`** (`VectorSLT/IdentityGroup/Defs.lean`, unchanged, k = 1, 2, 3).
No other named hypothesis was introduced. Nothing in the existing library was edited.

## Statement table

Lean positions `p = 0, 1, 2, 3` are the paper's positions one to four. "Shape M" means the hypothesis
shape of `theoremM_shear`, given below.

| Paper | Lean (root alias → working declaration) | Open hypotheses | Status |
|---|---|---|---|
| Prop. `prop:nonshear`, upper half: `Z_N ≤ C N⁻⁴` at position one | `paper_nonshear_upper` → `nonshear_upper` | `CubeSumUpper 3` | conditional |
| Prop. `prop:nonshear`: pair `(4,1)` | `paper_nonshear_pair` → `nonshear_pair` | `CubeSumUpper 3` | conditional |
| Lemma F1 (injectivity of `𝒟`) | `nonshear_injective` (algebra: `nonshear_kernel`, `comp_cubic_eq`) | — | certified |
| Loss comparison `K ≍ ‖Δ‖² + ‖P‖²` (`eq:F-compare`), upper-bound direction | `first_absorb` + `gram_down` (+ `first_compare`) | — | certified |
| Lemma `lem:A-box`, upper half, `∫_box e^{-cNJ_n} ≤ C N^{-2n/3}` | `paper_lemAbox_upper` → `lemAbox_upper` | `CubeSumUpper n` | conditional, every `n` |
| Lemma `lem:A-box`, "`J_k ≥ ‖∑ V_{W_i}‖²`" (degree-three part) | `cubeSumSq_le_grpErr` (`rayCub_grpErr`) | — | certified |
| Thm. `thm:invertible`, upper half, every position | `paper_invertible_upper` (by `fin_cases`) | `CubeSumUpper 1, 2, 3` | conditional |
| Thm. `thm:invertible`: pair `(4,1)`, every position | `paper_invertible_pair` | `CubeSumUpper 1, 2, 3` | conditional |
| — position one (A.3, active first) | `invertible_first_upper`, `invertible_first_pair` | `CubeSumUpper 3` | conditional |
| — position four (A.3, active last) | `invertible_last_upper`, `invertible_last_pair` | `CubeSumUpper 3` | conditional |
| — position two (A.3, one-block prefix) | `invertible_two_upper`, `invertible_two_pair` | `CubeSumUpper 1`, `CubeSumUpper 2` | conditional |
| — position three (A.2, two-block prefix) | `invertible_three_upper`, `invertible_three_pair` | `CubeSumUpper 1`, `CubeSumUpper 2` | conditional |
| A.3 injectivity of `L_AΔ + P∘F_A` / `L_AΔ + DF_A P` | `invertible_first_injective` / `invertible_last_injective` | — | certified |
| A.3 one-block prefix, injectivity of `L_AΔ + DF_A V + Q∘F_A` | `onePrefix_injective` | — | certified |
| A.2 (A-R) `‖R‖ ≤ C‖W'‖³‖T‖` | `abs_R_le` (with `mulQuint_lower`) | — | certified |
| A.2 Lemma `lem:A-sep` (restricted to `T₊ = 0`) | `twoPrefix_injective` via the certified `sepMap_kernel` | — | certified |
| (G↓) for every target, degree ≤ 81 | `gram_down` | — | certified |

"conditional" = proved from the listed `CubeSumUpper` instances and nothing else.

## Exact hypotheses

**Shape M** (upper halves; identical to `theoremM_shear` with `Z_{N,1} ≤ C N⁻⁴ (log N)⁴` replaced by
`Z_{N,p} ≤ C N⁻⁴`):

```
∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
  (∀ i, Integrable (fun x => |x i| ^ (2 * 81)) μ) →
  ∀ {lo hi}, (∀ i, lo i < hi i) → ∀ {μ₀}, 0 < μ₀ → ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
  ∀ (φ χ : Raw16 → ENNReal) {π₁}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ofReal π₁) → (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
  ∃ C N₀, ∀ N, N₀ ≤ N → Zpos μ A φ χ p N ≤ ofReal (C * N⁻¹ ^ 4)
```

The radius `r(A)` depends only on `A` (and the position), not on `μ, φ, χ`. Balls are in the sup norm
of `Raw16`.

**Pair versions** add, as `ZN1_two_sided_shear` does, the lower bounds needed by the certified
`Zpos_lower_N4`: `0 < φ₀`, `0 < χ₀`, `φ ≥ φ₀` near `basePos A p`, `χ ≥ χ₀` near `0`; the conclusion is
`HasLaplacePair (Zpos μ A φ χ p) 4 1` (`pair_of_upper`).

**Targets.**
- `NonShearTarget A`: `∃ a v, (∀ i j, A i j = a i * v j) ∧ a 0 ≠ 0 ∧ a 1 ≠ 0 ∧ v 0 * a 0 ^ 3 + v 1 * a 1 ^ 3 ≠ 0`
  (the paper's `A = avᵀ`, `a₁a₂ ≠ 0`, `vᵀa^{⊙3} ≠ 0`; `v ≠ 0` follows).
- Theorem `thm:invertible`: `A.det ≠ 0`.

## Structure of the proofs

Common skeleton (files in order of import):

1. `Absorb` — `uniform_lower_of_linear`: a family `η ↦ M_η` of linear maps on a finite-dimensional space,
   continuous in `η` pointwise, and injective at `η₀`, satisfies `c‖v‖ ≤ ‖M_η v‖` uniformly near `η₀`.
2. `GramDown` — `gram_down`: `κ ‖h_θ - F_A‖²_{[-1,1]²} ≤ K(θ)` for every target `A`.
3. `GroupCubic` — the degree-three part of a group error along rays; `cubeSumSq_le_grpErr`.
4. `Integrate` — rows of `Raw16` as `Fin 3 → ℝ × ℝ` (measure-preserving `rowE`); `RowBound` from
   `CubeSumUpper` (`rowBound_three`, `rowBound_split`); the product integral `layout_bound`; the block-swap
   involutions `Sfun p` (Jacobian one, `lintegral_Sfun`); `position_bound`.
5. `Endpoint` — `upper_of_absorb`: absorption + group comparison ⇒ Shape M; `pair_of_upper`.
6. Position files: `FirstPosition`/`NonShear` (p = 0, non-shear), `LastPosition`/`Invertible` (p = 0, 3,
   invertible), `OnePrefix` (p = 1), `Quintic`/`TwoPrefix` (p = 2). `LemmaABox` is the standalone Lemma A-box.

Retained variables and error maps, per position:

| Lean p | retained `v` | parameter `η` | exact identity | base map `M_{η₀}` |
|---|---|---|---|---|
| 0 | `(Δ, P)`, `P` whole 3-block suffix error, `PolyBox 27²` | `Δ` | `h - F_A = M_Δ(Δ, P)` (`errBox_eq_M0`) | `L_AΔ + P∘F_A` |
| 3 | `(Δ, P)`, `P` whole 3-block prefix error | `(Δ, P)` | `h - F_A = M_η(Δ, P)` (`errBox_eq_M3`) | `L_AΔ + DF_A P` |
| 1 | `(Δ, V_{W₁}, Q)`, `V_{W₁} ∈ H₃²` (coefficients), `Q` whole 2-block suffix, `PolyBox 9²` | `(Δ, V_{W₁})` | `h - F_A = M_η(v)` (`errBox_eq_M1`) | `L_AΔ + DF_A V + Q∘F_A` |
| 2 | `(Δ, S, T, U) ∈ Mat₂ × H₃² × H₅² × H₃²` | `(Δ, P)` | `h - F_A = M_η(v) + E`, `E` from `R` (`err_split`) | `𝓜` of `lem:A-sep` with `T₊ = 0` |

## Departures from the paper's proofs

1. **Absorption without remainder estimates (p = 0, 1, 3).** The paper writes `h - F = 𝒟v + E` with
   `‖E‖ ≤ C‖Δ‖(‖Δ‖ + ‖P‖)`. We write `h - F = M_η v` *exactly*, using `b³ - a³ = (b - a)(a² + ab + b²)` to
   make the error linear in the retained variables with coefficients depending continuously on `η`
   (e.g. `P ∘ F_{A+Δ}` is linear in `P` for fixed `Δ`). Uniform injectivity near `η₀` then replaces the
   remainder bound. At p = 2 the term `R` of (A-two) is still absorbed by an explicit remainder bound, as in
   the paper.
2. **Norms.** All polynomial maps carry the sup norm on `[-1,1]²` (the library's `PolyBox` norm), not the
   coefficient norm; the two are equivalent in finite dimension. Homogeneous cubics and quintics in the
   retained variables are stored by their 4 resp. 6 coefficients (sup norm), not as polynomials.
3. **(G↓).** The library's `Gdown` is specialized to the shear target `A₀` and to the ten coefficients of
   Theorem M, so it does not apply. `gram_down` is new: it bounds the sup norm on `[-1,1]²` of every
   polynomial of degree ≤ 81 by the `L²` norm on the density box. It uses the certified `toL2_injective`
   and finite-dimensional antilipschitz bounds.
4. **Degree-three part.** Instead of extracting monomial coefficients, `rayCub y` takes the `s³`
   coefficient of `s ↦ P(s y)`; along four rays this recovers the four moments of `cubeSum`
   (`cubeSumSq_le_rays`, `G ≤ 2(S(e₀)² + S(e₁)² + S(1,1)² + S(1,-1)²)`).
5. **Integration.** Only the upper bound is integrated: `Z ≤ π₁ ∫` over all of `ℝ⁴` for `Δ` (a Gaussian,
   `(π/κN)²`) times two row integrals over sup-norm balls, each `≤ C/N` by `CubeSumUpper`. No inner box
   or lower prior bound is needed; the lower half is the certified `Zpos_lower_N4`.
6. **Positions are moved to the first-position layout** by the coordinate involution `Sfun p` (exchange
   block 0 and block p entrywise), with Jacobian one (`det² = 1`). Inside a row the inactive blocks then
   appear in the order `inact p`; `G₃` and `G₂` are invariant under reordering the forms
   (`cubeSumSq_comp_equiv`, `cubeSumSq_two_le` with `add_comm`).
7. **Lemma F1.** The paper's coordinates `T = (ℓ, m)` are realized as the basis `w = a^{⊙3}/α`,
   `z = (-v₁, v₀)` of the input plane, in which `F_A(σw + tz) = (σ + ασ³)w + tz` (`hline`, `decomp2`). The
   degree count is `natDegree (g ∘ (X + αX³)) = 3 natDegree g ≤ 3` in `ℝ[X]` (`comp_cubic_eq`).
8. **A.3 substitution argument (p = 0, 1).** "The top part of `Q ∘ F_A` has degree `3d`": we prove the
   coefficient of `s^{3D}` in `Q(s y + s³ V_A y)` is `Q_D(V_A y)` (`coeff_aeval_cubic`). Since `V_A` is onto,
   `Q_D ≢ 0` gives a contradiction when `3D` is not one of the degrees present (`totalDegree_le_one_of_odd`).
   The affine case is done separately (`eval_affine`, `eq_zero_of_layer_odd`).
9. **A.3 multiplication argument (p = 3)** is run along rays `s ↦ P(s y)` for `y` with `(Ay)₀(Ay)₁ ≠ 0`. The
   coefficient of `s^{n+2}` is `3(Ay)_k² (A c_n)_k`. Density (`vanish_of_dense`, certified) gives `P = 0`.
10. **A.2 (p = 2).** The product bound `‖c_i²φ_i‖ ≥ c₀‖c_i‖²‖φ_i‖` is `mulQuint_lower`, proved by compactness
    of the product of unit spheres, absence of zero divisors (`mulQuint_eq_zero`) and homogeneity. With it,
    (A-R) has the explicit form `|R_k| ≤ (192ρ³ + 768ρ⁶)/m · ‖T_k‖` (`abs_R_le`), and
    `‖E‖ ≤ (1 + 7 amax³) sup|R|` (`norm_E_le`). Injectivity of the base map is the library's certified
    `sepMap_kernel`, with `T₊ = 0` since the suffix is one block.
11. **Lemma A-box** is stated for every `n`, conditional on `CubeSumUpper n` (the paper: `0 ≤ k ≤ 4`, two-sided).
    Only the upper half is formalized. Its proof splits the blocks into the two output rows by a
    measure-preserving map (`measurePreserving_grpRows`).
12. **Retained spaces are slightly larger than the paper's** at p = 0, 3 and for `Q` at p = 1: the group
    error is allowed to be any polynomial of degree ≤ `3^n`, including constant and linear terms. The
    paper's group errors have no terms below degree three. Injectivity is proved on the larger space, which
    is stronger.

## Remarks on the paper's proofs (no error found)

No statement was found false, and every step went through. Three places are worth a sentence in the paper:

- **A.3, one-block prefix.** The step "degrees five and three then eliminate `V_{W₁}` and `Δ`" needs the
  prefix slot to be a *homogeneous cubic*. If that slot ranged over all polynomials of degree ≤ 3, the
  linear map would have a kernel. Example at `A = I`, for any `d₀, d₁`: `S = -Bx`, `Q = Bx`, `B = diag(-3d₀, -3d₁)`,
  `Δ = diag(-2d₀, -2d₁)`. The paper does say the prefix error is exactly `V_{W₁}`, so the argument is right as
  written. The restriction just has to be kept (Lean: `OneDom` stores four cubic coefficients).
- **A.3, "If `Q ≠ 0`, its top part has degree at least nine after substitution"** and **"top homogeneous part
  of degree `d ≥ 3`"** use that a group error has no terms of degree below three. For an arbitrary polynomial
  the affine case needs a separate (easy) step. Lean proves injectivity without this restriction.
- **A.2, (A-R).** The constant is explicit: with `ρ ≥ |W₁|` entrywise and `m` from `mulQuint_lower`,
  `‖R_i‖_{[-1,1]²} ≤ (192ρ³ + 768ρ⁶)/m · ‖T_i‖_coef`.

## Left open

- `CubeSumUpper 1`, `CubeSumUpper 2`, `CubeSumUpper 3` (branch `p2-cubes`).
- Not attempted (outside the brief): Lemma A-box lower half; Lemma A-cubes itself; depth five; the shear
  upper bounds at positions two to four (Theorems N, K).

## Build and audit

```sh
lake build VectorSLT.IdentityGroup.Pairs
lake env lean -DwarningAsError=true -DautoImplicit=false VectorSLT/IdentityGroup/AuditPairs.lean
```

- Build: clean. The only messages from these files are the expected Lake notes that a file "imports
  Mathlib ... consider adding `module`".
- Audit: 235 `#print axioms` lines, one per declaration of `Pairs/*.lean` and `Pairs.lean`. 234 depend on
  exactly `[propext, Classical.choice, Quot.sound]`. One (`inact`, a lookup table) depends on `[propext]`
  alone. None depends on `sorryAx` or any other axiom. The files contain no `sorry`, `admit`,
  `native_decide`, `axiom` or `set_option`.
