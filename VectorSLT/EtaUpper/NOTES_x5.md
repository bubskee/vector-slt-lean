# Proposition X5 (uniform upper bound near a shear): notes

Branch `p2-x5`. New files only; no existing file was edited.

Build: `lake build VectorSLT.EtaUpper`. The default target does not build it, because `VectorSLT.lean` is frozen and does not import it.
Audit: `lake env lean VectorSLT/EtaUpper/AuditX5.lean`. It has 46 lines and every one prints
`[propext, Classical.choice, Quot.sound]`.

## Statement: paper versus Lean

Paper (`main.tex`, `prop:X5`): there is `η₀ > 0` such that for `|η| ≤ η₀` and `N ≥ 2`,
`Z_N(A_η) ≤ C N⁻⁴ (log N)⁴`, with `C` independent of `η`.

Lean (`VectorSLT/EtaUpper.lean`):

* `X5_upper`: `∃ η₀ r > 0, ∀ μ` (finite, 162nd moments, `μ ≥ μ₀ · Leb` on a box) `∀ φ χ π₁`
  (`φ ≤ π₁`, `χ ≤ 1`, `χ = 0` outside the sup-norm `r`-ball) `∃ C N₀, ∀ η, |η| ≤ η₀ → ∀ N ≥ N₀,
  Zpos μ (Aeta η) φ χ 0 N ≤ ofReal (C N⁻⁴ (log N)⁴)`. The cutoff is centred at
  `basePos (Aeta η) 0`, so it moves with `η`, as in `X4_lower_population`.
* `X5_upper_two` is the same with `∀ N ≥ 2` in place of `N ≥ N₀`. This is the paper's range.
* `X5_upper_gaussian` is the `N ≥ 2` form for `stdGauss2`.
* The explicit forms (`X5_upper_explicit`, `X5_upper_explicit_two` in `X5.lean`) are stronger
  than the headline. They take `η₀ = 1/200` and `r = 1/400`, and choose `C` and `N₀` from `μ` and
  `π₁` alone, before `η`, `φ` and `χ`.
* `theoremM_eta` (`TheoremMEta.lean`) is the (M2)-coordinate form. It holds for `|η| ≤ 9/1000`,
  for any prior × cutoff dominated by `π₁ · 1_{UM}`.

The upper bound needs no lower bound on the prior. The paper's prior floor `φ ≥ π₀` near the
segment, and with it the "constants depend on the prior neighbourhood" remark, matters only for
X4. For X5, `C` depends on `μ` (through `κ` of (G↓)) and on `π₁`, and on nothing else.

## Order of constants

1. `ε₁ = 1/100`, the active half-width (`Jν = [-ε₁, ε₁]`, `Iα = [1 - ε₁, 1 + ε₁]`). It is fixed
   by Theorem M's box `UM`, together with `|a|, |b| ≤ 1/20`. Nothing in Theorem M depends on where
   the base point sits inside the box, only on `ε₁`.
2. `η₀ = 1/200 = ε₁/2`. Two constraints apply:
   * base points `(αₖ, νₖ) = (1, η)` must lie inside `UM` with room for the cutoff ball;
   * (A1) needs `|P₁ - η| ≤ 1/100`. On the box `|P₁| ≤ 1/1000`, so `|η| ≤ 9/1000` suffices
     (`P1t_sub_le`).
3. `r = 1/400 = ε₁/4`. In (M2) coordinates `ν = θ₀₀ + θ₀₁` and `b = p + q`, so a raw sup-norm
   `r`-ball moves `ν` and `b` by up to `2r`. Then `|ν| ≤ η₀ + 2r = ε₁` and `|b| ≤ 2r ≤ 1/20`
   (`toM2_mem_UM_eta`).
4. `κ = κ(μ)` from `Gdown_eta` (uniform in `η`). Then `C = π₁ K_c κ'⁻⁴` and `N₀ = e/κ'` with
   `κ' = min(κ, 1)/3`. `K_c = π² · 9 · C_{M5}(1/20)²/4` is absolute.
5. For `N ≥ 2`: `C₂ = π₁ vol(UM) · max(N₀, 2)⁴ / (log 2)⁴`, and the final constant is
   `max(C, 0) + C₂`.

The companion reviewer's point was that Theorem M needs `ε₁` small with `ε₁ ≥ η₀`. This order
satisfies it: `ε₁` comes first and is absolute, and `η₀` and `r` are fixed fractions of it.

## Where Theorem M's proof had to change

The A₀ proof is `theoremM` (`TheoremM.lean`). The target enters it in exactly two places: through
the coefficient functionals in (G↓), and through the row's `G` after eliminating `ν`. Every
change is listed below; everything else is reused as is.

| Theorem M step | Lean (A₀) | Lean (A_η) | Change |
|---|---|---|---|
| (G↓) | `Gdown` | `Gdown_eta` | `c₂ → c₂ - 3η`, `c₁ → c₁ - 3η²` (Lemma X2: `errPη_c2`, `errPη_c1`); `c₃` and `Z` unchanged (`errPη_c3`, `errPη_s5`). `κ` comes from `linear_le_L2` and `l2_le_sup`, which never see the target, so it is uniform in `η`. |
| coefficient form | `SMx`, `sum_coeffs_eq` | `SMxη`, `sum_coeffs_eq_eta` | `P₁ → P₁ - η`, `P₂ → P₂ - η²` |
| (A1) | `A1_core` (`\|P₁\| ≤ 1/1000`) | `A1_core'` (`\|P₁\| ≤ 1/100`), used at `(P₁ - η, P₂ - η²)` | numeric slack only |
| (M5) form | `TMx` with `G = P₂ + P₁²/α³` | `TMxη` with `G_η = (P₂ - η²) + (P₁ - η)²/α³` | `G_η = G - 2ηP₁/γ + η²/γ - η²` |
| F1–F3 (active block) | `active_bound` | `active_bound`, unchanged | shift `t = 3(P₁ - η)`; the ν-integral runs over all of ℝ, so the shift is free |
| split into rows | `Hw`, `split_exp`, `F0r`, `F1r`, `Hw_split` | `Hwη`, `split_exp_eta`, `F0rη`, `F1rη`, `Hwη_split` | carry `G_η` |
| Lemma M4 (slice) | `slice_exists`, `lemmaM4` | `slice_exists_eta`, `lemmaM4_eta` | on a slice `Z = ζ`, `P₁` is affine in `β`, so `G_η` keeps the matrix `M̃` and changes only `L` and `k` (`quadForm_add_affine`). `slice_bound` (Lemma M2) already holds for all `L, k`, so the bound and its constant are unchanged. |
| Lemma M5 / one row | `pivotRow`, `rowBound`, `rowBound_M6` | `pivotRow_eta`, `rowBound_eta`, `rowBound_M6_eta` | integrand only; same constant `3 C_{M5} N⁻¹ (log N)²` |
| F5–F6 (two rows, `c`) | `J_bound`, `UM_inner`, `UM_c`, `UM_bound` | `*_eta` versions | none beyond the integrand |
| assembly | `theoremM` | `theoremM_eta` | `|η| ≤ 9/1000`; `C, N₀` before `η` |
| raw support | `toM2_mem_UM` (ball `1/200` at `θ₀`) | `toM2_mem_UM_eta` (ball `1/400` at `basePos (Aeta η) 0`, `\|η\| ≤ 1/200`) | radius halved |

Reused unchanged: `lemmaM5`, `m3Int_Echart` and the (M9) `E` (`EM9`, `Mt`, `det_Mt`,
`Mt_entries`), `slice_bound`, `lemmaM2_explicit`, `two_rows`, `active_bound`,
`lintegral_gauss2`, `BrowM`, `UM_bound_real`, `UM`, `Wbox`, `measurePreserving_toM2`,
`cub3_le`, `P1t_le`, the (M6) weights (`yRow`, `γRow`, `WOK`, `WDOK`).

The library's `ν`-box is only ever used through `|ν| ≤ ε₁`: once for `|c₂| ≤ 1/10` in (A1), and
once for box membership. `ν ≈ 0` is never used.

## Is the paper's sketch accurate?

Yes. Each of its three sentences checks out in Lean:

* "The proof of Theorem M applies unchanged, with an active neighbourhood that contains the whole
  segment of base points." The box `UM` already contains the segment `|η| ≤ 1/200`. The proof is
  the same proof, with the substitutions in the table above.
* "It never uses ν_k ≈ 0." Correct: only `|ν_k| ≤ ε₁` is used.
* "The terms in η enter each row's slice quadratic only through its linear and constant terms,
  and Lemma M2 is uniform in those." Correct, and in Lean this is literal: `slice_exists_eta`
  keeps `M̃`, and `slice_bound` holds for all `L, k`.

Three points the sketch leaves implicit:

1. "Unchanged" is slightly too strong. (A1) bounds `D = c₂(6P₁ - c₂)/(9α³)` using
   `|P₁| ≤ 1/1000`. For `A_η` the same algebra runs at `P₁ - η`, which is not small unless
   `η` is. This is where a numerical `η₀` comes from (here `9/1000`, used at `1/200`).
2. The cutoff radius must shrink: `1/400` here, against `1/200` for A₀. The ball around the
   moving base point has to stay inside the fixed box.
3. Theorem M (Lean and paper appendix) gives `N ≥ N₀`. The paper's `N ≥ 2` follows at the cost
   of a larger constant, from the trivial bound `Z_N ≤ π₁ vol(UM)` on `[2, N₀]` (`X5_upper_two`).

## Left open

* The saturated bound `Z_N(A_η) ≤ C N⁻⁴ (1 + 𝓛_η(N))⁴` (paper, "Beyond the crossover") is not
  attempted. It needs Proposition `prop:nonshear` with constants tracked in `η`.
* X5 is proved for the normal form `A_η` only. It is not transferred to general rank-one targets
  near a shear through `normalize_Aeta`. That transfer would need the conjugation `d` to stay
  bounded uniformly along the family, and is not needed for the paper's statement.
* Release bookkeeping is not done, because those files are frozen: importing `VectorSLT.EtaUpper`
  from `VectorSLT.lean`, adding the audit lines to `VectorSLT/Audit.lean` and `checks/`, and
  updating `README.md` and `formalization_status.md`. The paper's sentence "Lean does not certify
  Proposition X5" (`main.tex`, line 489) and the coverage table would also need updating.

Size: 1041 lines including the audit and docstrings, against the earlier estimate of 800 to
1200.
