/-
Paper 2, Appendix A.1 (identity groups): shared definitions and the interface between two
formalization branches.

A group of `k` zero blocks must compose to the identity. Its leading error is, in each output
row, a sum of `k` binary cubes `∑ i, (a_i x + b_i y)^3` in that row's own entries. Lemma A-cubes
of the paper says `∫_box e^{-N G_k} ≍ N^{-k/3}` for `1 ≤ k ≤ 4`, where `G_k` is the squared
coefficient norm of that sum.

* Branch `p2-cubes` proves `CubeSumUpper k` (the upper half of Lemma A-cubes).
* Branch `p2-f1-invertible` assumes `CubeSumUpper k` as a named hypothesis and derives the pairs
  of Proposition "non-shear rank one" and Theorem "invertible active blocks".

This file is byte-identical on both branches. Do not edit it on either.
-/
import Mathlib

namespace VectorSLT.IdentityGroup

open MeasureTheory
open scoped ENNReal

/-- The sum of the cubes of `k` real binary linear forms. Form `i` is `a x + b y` with
`(a, b) = u i`. The result is in moment coordinates:
`(∑ a³, ∑ a²b, ∑ ab², ∑ b³)`, the coefficients of `x³, 3x²y, 3xy², y³`. -/
def cubeSum {k : ℕ} (u : Fin k → ℝ × ℝ) : Fin 4 → ℝ :=
  ![∑ i, (u i).1 ^ 3, ∑ i, (u i).1 ^ 2 * (u i).2, ∑ i, (u i).1 * (u i).2 ^ 2, ∑ i, (u i).2 ^ 3]

/-- The paper's `G_k`, up to bounded factors: the squared norm of `cubeSum` in moment
coordinates. Homogeneous of degree six. -/
def cubeSumSq {k : ℕ} (u : Fin k → ℝ × ℝ) : ℝ := ∑ j, cubeSum u j ^ 2

/-- **Interface: the upper half of Lemma A-cubes.** For every radius `r` and every `c > 0`,
`∫_{‖u‖ ≤ r} e^{-c N G_k(u)} du ≤ C N^{-k/3}` for all `N ≥ 1`. The ball is in the sup norm of
`Fin k → ℝ × ℝ`, and `C` may depend on `r` and `c`. -/
def CubeSumUpper (k : ℕ) : Prop :=
  ∀ r c : ℝ, 0 < r → 0 < c → ∃ C : ℝ, ∀ N : ℝ, 1 ≤ N →
    ∫⁻ u in Metric.closedBall (0 : Fin k → ℝ × ℝ) r,
      ENNReal.ofReal (Real.exp (-(c * N * cubeSumSq u))) ≤
        ENNReal.ofReal (C * N ^ (-(k : ℝ) / 3))

end VectorSLT.IdentityGroup
