# Formal verification coverage (paper 2)

Lean source: vector-slt-lean, release pass on `2d545cd` (namespace `VectorSLT.SLT`). The pass adds paper-facing aliases (`VectorSLT/PaperNames.lean`) and the `checks/` directory. No existing statement or proof changed; `checks/declaration-types.txt` records this.
Lean `v4.35.0`; mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Mathematical source: `cubic-chaos`, read-only, at the commits named in each brief. The last one read is `caccd6a` (`approx_shear_crossover.md`, unchanged since `935beb6`).

Paper 2's main theorem gives the pairs (λ, m) for every rank-one shear with both rows nonzero, by position. The position-one pair (4,5) is fully certified in Lean. So are the lower halves at every position. The upper halves at positions 2–4 depend on Theorems N and K. These enter only as the named hypotheses `ThmN` and `ThmK`/`ThmKUpper`, and neither is proved here. This file records the certified statements and their exact assumptions.

**Indexing.** Lean positions are `p : Fin 4`, so Lean `p = 0, 1, 2, 3` are the paper's positions 1, 2, 3, 4. Raw parameters are `θ : Raw16`, four 2×2 matrices; `rawEquiv : Raw16 ≃ (Fin 4 → Matrix (Fin 2) (Fin 2) ℝ)` and `net_eq_network` identify them with the paper's network `F_{W₄} ∘ ⋯ ∘ F_{W₁}` on `(W₁, …, W₄)`, `F_W(z) = z + (Wz)^{⊙3}`. `rawEquiv` is a relabelling of the sixteen coordinates; Lean does not state that it is measure-preserving, and the certified statements are all on `Raw16` with Lebesgue measure.

## Shared hypotheses

These appear in the shear-table statements (`mainTheorem_shear`, `ZN1_two_sided_moments`, `theoremM_shear`, `middle_position_pair`, `position_four_pair`, `separation_moments`).

- **Target.** `ShearTarget A`: `A i j = a i * v j` with `a 0 ≠ 0`, `a 1 ≠ 0`, `v ≠ 0` and `v 0 * a 0 ^ 3 + v 1 * a 1 ^ 3 = 0`. This is the rank-one shear with both rows nonzero; the one-zero-row stratum is excluded.
- **Input law.** `μ : Measure (Fin 2 → ℝ)` is a finite measure with `Integrable (|x i| ^ 162) μ` for both coordinates. For the upper halves it must also dominate a uniform density on a box: `ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ` with `lo < hi` and `μ₀ > 0`. Probability normalization is not needed. The standard Gaussian `stdGauss2` satisfies both conditions (`stdGauss2_moments`, `stdGauss2_density`), and every `*_gaussian` corollary is stated for it.
- **Loss.** `popLossA μ A θ = ∫ Σₖ (net θ x k − layer A x k)² dμ`, the actual population squared error of the raw-weight network (`popLossA_eq_network`).
- **Prior and cutoff.** The integral is `Zpos μ A φ χ p N = ∫⁻ exp(−N·popLossA) · φ(θ) · χ(θ − θ₀⁽ᵖ⁾)`, with `θ₀⁽ᵖ⁾ = basePos A p` (`A` in slot `p`, zero elsewhere).
  - `φ` is bounded above, `φ ≤ π₁`, and bounded below by `φ₀ > 0` on a neighbourhood of every `θ₀⁽ᵖ⁾`.
  - `χ` satisfies `χ ≤ 1`, is bounded below by `χ₀ > 0` near `0`, and vanishes outside a ball of radius `r(A)`.
  - `r(A) > 0` is produced by the theorem itself (`∃ r, 0 < r ∧ …`), and balls use the sup norm on `Raw16`.
  - No smoothness, measurability or normalization is assumed of `φ` or `χ`.
- **Named hypotheses**, all stated on the same `μ, A, φ, χ`; none is proved in this library.
  - `ThmK μ A φ χ`: `c N⁻⁴ ≤ Z_{N,4} ≤ C N⁻⁴` for large `N` (Theorem K, both halves).
  - `ThmKUpper μ A φ χ`: the upper half of `ThmK` alone.
  - `ThmN μ A φ χ`: `Z_{N,p} ≤ C N⁻⁴` at Lean `p = 1, 2` (paper positions 2 and 3); this is the upper half of Theorem N.

`HasLaplacePair Z λ m` is `LaplaceLower Z λ m ∧ LaplaceUpper Z λ m`, meaning `c N^{−λ} (log N)^{m−1} ≤ Z(N) ≤ C N^{−λ} (log N)^{m−1}` for all `N ≥ N₀`, with `c > 0`. The value `Z` is in `ℝ≥0∞`, so the upper half also states finiteness.

## Correspondence with the paper

Exactly one tag per row:
- **certified**: proved, with no hypothesis beyond the shared ones;
- **conditional (`H`)**: proved from the named hypothesis `H`;
- **not formalized**.

Paper-facing aliases from `PaperNames.lean` are in parentheses.

| Paper result | Principal declaration | Certified content | Status |
|---|---|---|---|
| Main theorem: pairs (4,5), (4,1), (4,1), (4,1) by position | `mainTheorem_shear` (`vector_shear_main_theorem`); `mainTheorem_shear_gaussian` | `HasLaplacePair (Zpos μ A φ χ p)` with `(4,5)` at `p = 0` and `(4,1)` at `p = 1, 2, 3`, for every shear target, moment/box law, prior and cutoff | conditional (`ThmK`, `ThmN`) |
| Main theorem, separation form | `mainTheorem_shear_ratio` (`vector_shear_main_theorem_ratio`) | `Z_{N,1} / Z_{N,p} → ∞` for every `p ≠ 1` | conditional (`ThmK`, `ThmN`) |
| Normalization (Theorem H §2) | `shear_normalize` (`vector_shear_normal_form`); `prefixNet_conj`, `lintegral_linearEquiv` | Every shear target is (H2)/(H3)-conjugate to `A₀ = [[1,−1],[1,−1]]`; the network and the Lebesgue integral transfer | certified |
| Theorem L′ (lower half, position 1) | `propLprime_moments` (`vector_shear_position_one_lower`); `propLprime_shear` (abstract loss `K ≤ Λ·sup-err²` on a box); `propLprime_gaussian` | `c N⁻⁴ (log N)⁴ ≤ ∫ e^{−NK} π` for every shear target; only a positive lower bound of the prior near the base point is assumed | certified |
| Theorem M (upper half, position 1) | `theoremM` (target `A₀`, local prior on the (M2) chart); `theoremM_shear` (`vector_shear_position_one_upper`) | `Z_{N,1} ≤ C N⁻⁴ (log N)⁴` for every shear target and moment/box law; (G↓) proved as `Gdown` | certified |
| Position 1 exact: pair (4,5) | `ZN1_two_sided_moments` (`vector_shear_position_one_exact`); `ZN1_two_sided_gaussian`; `ZN1_two_sided`, `ZN1_two_sided_shear` (compact support) | `c N⁻⁴ (log N)⁴ ≤ Z_{N,1} ≤ C N⁻⁴ (log N)⁴` | certified |
| O3 lower bounds, every position | `Zpos_lower_N4` (`vector_any_position_lower`) | `c N⁻⁴ ≤ Z_{N,p}` at every `p` and for **every** matrix `A`, with no shear hypothesis and no box condition | certified |
| Positions 2 and 3: pair (4,1) | `middle_position_pair` | `HasLaplacePair (Zpos μ A φ χ p) 4 1` at Lean `p = 1, 2` | conditional (`ThmN`) |
| Position 4: pair (4,1) | `position_four_pair`; `ThmK.hasLaplacePair` | `HasLaplacePair (Zpos μ A φ χ 3) 4 1` | conditional (`ThmKUpper`, the upper half of `ThmK`) |
| Separation `Z_{N,1}/Z_{N,4} ≥ c log⁴ N` | `separation_moments`; `separation`, `separation_gaussian` | `c (log N)⁴ Z_{N,4} ≤ Z_{N,1}` | conditional (`ThmKUpper`) |
| Theorem K | — (enters as `ThmK`, `ThmKUpper`) | — | not formalized |
| Theorem N | — (enters as `ThmN`) | — | not formalized |
| Invertible contrast (O5), inverse criterion | `inverse_criterion`, `rank_one_criterion`, `deriv_criterion`, `shear_inverse` | `B (Bx)^{⊙3} ≡ 0 ⇔ F_{−B} ∘ F_B = id`; rank-one form `v·a^{⊙3} = 0`; derivative form | certified |
| Invertible contrast (O5), separation through an invertible block | `sepMap_injective`; `sepLin_injective`, `sepLin_lower`, `sep_absorb` | For `det A ≠ 0`, injectivity of the cubic/quintic separation map on `Mat₂ ⊕ H₃² ⊕ H₅² ⊕ H₃² ⊕ H₅²`; a positive smallest singular value `σ`; absorption of an `O(η)` perturbation | certified |
| Invertible contrast: placement independence at depths 4 and 5 (network level, group estimate (9), (11)–(12)) | — | — | not formalized |
| E₀ identity (bordered Hessian, null direction) | `bordered_det` (`vector_E0_bordered_det`), `null_direction` | `−det [[diag a, a^{⊙2}],[a^{⊙2}ᵀ, 0]] = (∏ aᵢ) Σ aᵢ³`; `Σ (aᵢ s + c aᵢ t)³ = (Σ aᵢ³)(s + c t)³` | certified |
| Mechanism (Φ, null cone and turning, Euler balance, non-shear contrast) beyond the E₀ identity | — | — | not formalized |
| X1: near-shear normal form `A_η` | `normalize_Aeta` (`vector_near_shear_normal_form`) | Branch `β₀ = v₀ a₀³ > 0`: (H2)-conjugate to `A_η` with `η = (v·a^{⊙3})/β₀` | certified |
| X1: branch `β₀ < 0` (coordinate swap) | — | — | not formalized |
| X2: coefficients for `A_η` | `errPη_coeff_ne3`, `errPη_s5`, `errPη_c3`, `errPη_c2`, `errPη_c1`, `errPη_c0`, `eval_errθη` | Only degree-3 coefficients change (`c₂, c₁, c₀` gain `−3η, −3η², −η³`); `Z_k` is unchanged | certified |
| X4: uniform near-shear lower bound | `X4_lower_population` (`vector_near_shear_lower`); `X4_lower_gaussian`; `X4_lower_compact`; `X4_lower`, `X4_lower_segment` (abstract loss) | `c N⁻⁴ (1 + 𝓛_η(N))⁴ ≤ Z_N(A_η)` for all `N ≥ N₀`, with `c, N₀` independent of `\|η\| ≤ 1/10`, where `𝓛_η(N) = log min(N, \|η\|⁻¹)` (`= log N` at `η = 0`, `X4_at_zero`) | certified |
| X5 | — | — | not formalized |
| X6 (full-network saturation; stated in paper 2, companion proof) | — | — | not formalized |
| Reusable SLT layer (`VectorSLT.SLT`, Mathlib only) | `Z_eq_layercake`; `laplaceLower_of_volume`, `laplaceUpper_of_volume`; `HasLaplacePair.of_comparable`, `.of_prior`, `.prod`; `monomial_hasLaplacePair`; `normalCrossing_Z` | Layer cake; volume ⇔ Laplace (both directions); comparable losses and priors; products `(λ₁+λ₂, m₁+m₂−1)`; 1-D monomial `(1/(2k), 1)`; d-variable normal crossing `λ = min (hᵢ+1)/(2kᵢ)`, `m = #argmin` | certified |

X5 and X6 are **not formalized**. Neither is Theorem K or Theorem N: they enter only as hypotheses, and every row that uses them says so.

## Hypothesis differences between rows

- **`mainTheorem_shear`** assumes the two-sided `ThmK` but uses only its upper half (`hK.upper`). The lower half at position 4 is proved independently (`Zpos_lower_N4`). The statement is left as frozen; a weaker form with `ThmKUpper` would also hold.
- **X4 statements** use a stronger prior assumption than the shear table. The prior bound `φ ≥ φ₀` must hold on a ball of a fixed radius `r₀` around every `basePos (A_η) 0` with `|η| ≤ 1/10`, and the cutoff must satisfy `χ ≥ χ₀` on `‖θ‖ < r₀`. This uniformity is what makes `c, N₀` independent of `η`.
- **`theoremM`** (target `A₀`) bounds `φ · χ(θ − θ₀)` by `π₁` times the indicator of the (M2) chart region `UM`. The shear-table form `theoremM_shear` replaces this with the support radius `r(A)`.
- **Compact-support variants** (`ZN1_two_sided`, `ZN1_two_sided_shear`, `separation`, `X4_lower_compact`) take a probability measure supported in `[−R, R]²` in place of the 162nd moments.

## Analytic scope

- `HasLaplacePair Z λ m` certifies the two-sided order `N^{−λ} (log N)^{m−1}` with unspecified constants for large real `N`.
- It does **not** certify the following:
  - a leading constant or an asymptotic expansion;
  - a zeta function, its poles or a meromorphic continuation;
  - the RLCT as an algebraic invariant (the pair is read off from the Laplace integral, which is the paper's working definition);
  - anything about `N` below `N₀`.
- The lower bounds need only local positivity of the prior. The upper bounds need a bounded prior and a cutoff with support of radius `r(A)`. The Laplace integral is over the cutoff's support, not over all of parameter space.
- Theorem M's upper bound is proved for the moment/box laws above. The box condition is used for (G↓) (`Gdown`); laws without a density bounded below on some box are not covered.

## Reproduce

From the repository root:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true -DautoImplicit=false checks/PaperAudit.lean
lake env lean -DwarningAsError=true -DautoImplicit=false VectorSLT/Audit.lean
shasum -a 256 -c checks/lean-sources.sha256
```

All of the following pass:
- the release build;
- the focused audit: 50 principal declarations and 13 aliases, i.e. 63 axiom lines;
- the library audit: 199 declarations.

Every declaration in both audits depends on exactly `propext`, `Classical.choice` and `Quot.sound`. None depends on `sorryAx`, and none depends on any other axiom. The focused audit also prints the definitions that the statements rest on: `Z`, `LaplaceLower`, `LaplaceUpper`, `HasLaplacePair`, `layer`, `net`, `popLossA`, `Zpos`, `basePos`, `ShearTarget`, `ThmK`, `ThmKUpper`, `ThmN`, `Aeta`, `Meta` and `Leta`.

Evidence in `checks/`:
- `lean-build.txt`: a clean rebuild of the library;
- `PaperAudit.txt` and `Audit.txt`: the two audit outputs;
- `lean-sources.sha256`: SHA-256 of every Lean source and the Lake configuration;
- `declaration-types.txt`: the comparison of every `VectorSLT` declaration's type before (`2d545cd`) and after this pass. All 958 existing declarations are identical in module, kind, type hash and type text, and no declaration changed or was removed. The 13 additions are the aliases in `PaperNames.lean`, each with exactly its original's type. The dumps come from `checks/TypeDump.lean` (`DUMP_OUT=<file> lake env lean checks/TypeDump.lean`). They are about 4.5 MB each, so only their SHA-256 hashes are stored.
