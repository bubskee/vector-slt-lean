/-
Paper 2, Lemma `lem:A-box` (Appendix A.1), upper half, as a standalone statement.

For a group of `n` blocks `W ∈ (Mat₂)ⁿ` (Lean `Fin n → Fin 2 → Fin 2 → ℝ`, block `i`, row `k`,
column `j`), let `J_n(W) = ∑ₖ ‖(F_{W_{n-1}} ∘ ⋯ ∘ F_{W₀} - I)_k‖²` be the squared norm of the
group error, in the sup norm on `[-1,1]²` (`grpJ`). Then, from `CubeSumUpper n`,
`∫_{‖W‖ ≤ r} e^{-c N J_n(W)} dW ≤ C N^{-2n/3}` for every `r, c > 0` (`lemAbox_upper`).

The proof is the paper's: `J_n ≥ G_n(row 0) + G_n(row 1)` up to a constant
(`cubeSumSq_le_grpErr`, the degree-three part), and the integral factors over the two rows,
each giving `N^{-n/3}` by `CubeSumUpper n`. The coefficient norm of the paper is replaced by the
sup norm on the box; the two are equivalent on the finite-dimensional space of polynomial maps
of degree `≤ 3ⁿ`. Only the upper half is stated; the lower half is not used.
-/
import VectorSLT.IdentityGroup.Pairs.GroupCubic
import VectorSLT.IdentityGroup.Pairs.Integrate

namespace VectorSLT.IdentityGroup.Pairs

open MeasureTheory Set Filter VectorSLT

/-- The blocks of a group as a sequence of matrices (zero past the end). -/
def grpBlocks {n : ℕ} (W : Fin n → Fin 2 → Fin 2 → ℝ) : ℕ → Matrix (Fin 2) (Fin 2) ℝ :=
  fun i => if h : i < n then Matrix.of (W ⟨i, h⟩) else 0

/-- The paper's `J_n`: the squared norm of the group error, summed over the two output rows. -/
noncomputable def grpJ {n : ℕ} (W : Fin n → Fin 2 → Fin 2 → ℝ) : ℝ :=
  ∑ k, ‖grpErr (grpBlocks W) n k‖ ^ 2

/-- The two output rows of a group: row `k` is `i ↦ (W i k 0, W i k 1)`. -/
def grpRows {n : ℕ} (W : Fin n → Fin 2 → Fin 2 → ℝ) : (Fin n → ℝ × ℝ) × (Fin n → ℝ × ℝ) :=
  (fun i => (W i 0 0, W i 0 1), fun i => (W i 1 0, W i 1 1))

theorem grpRow_grpBlocks {n : ℕ} (W : Fin n → Fin 2 → Fin 2 → ℝ) (k : Fin 2) :
    grpRow (grpBlocks W) n k = fun i => (W i k 0, W i k 1) := by
  funext i; simp [grpRow, grpBlocks, i.isLt]

/-- Splitting the blocks into rows preserves Lebesgue measure. -/
theorem measurePreserving_grpRows (n : ℕ) :
    MeasurePreserving (grpRows (n := n)) := by
  have h1 : MeasurePreserving (fun (W : Fin n → Fin 2 → Fin 2 → ℝ) (i : Fin n) =>
      MeasurableEquiv.finTwoArrow (W i)) :=
    volume_preserving_pi fun _ => volume_preserving_finTwoArrow (Fin 2 → ℝ)
  have h2 := volume_measurePreserving_arrowProdEquivProdArrow (Fin 2 → ℝ) (Fin 2 → ℝ) (Fin n)
  have h3 : MeasurePreserving (fun (R : Fin n → Fin 2 → ℝ) (i : Fin n) =>
      MeasurableEquiv.finTwoArrow (R i)) :=
    volume_preserving_pi fun _ => volume_preserving_finTwoArrow ℝ
  have := (h3.prod h3).comp (h2.comp h1)
  convert this using 1
  funext W; rfl

theorem norm_grpRows_le {n : ℕ} (W : Fin n → Fin 2 → Fin 2 → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hW : ‖W‖ ≤ r) (k : Fin 2) : ‖fun i => (W i k 0, W i k 1)‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg hr).mpr fun i => (norm_prod_le_iff).mpr ⟨?_, ?_⟩
  · exact (norm_le_pi_norm (W i k) 0).trans ((norm_le_pi_norm (W i) k).trans
      ((norm_le_pi_norm W i).trans hW))
  · exact (norm_le_pi_norm (W i k) 1).trans ((norm_le_pi_norm (W i) k).trans
      ((norm_le_pi_norm W i).trans hW))

/-- **Lemma A-box, upper half.** For a group of `n` blocks, `CubeSumUpper n` gives
`∫_{‖W‖ ≤ r} e^{-c N J_n(W)} dW ≤ C N^{-2n/3}` for all `N ≥ 1`. -/
theorem lemAbox_upper {n : ℕ} (hn : CubeSumUpper n) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∃ C : ℝ, ∀ N : ℝ, 1 ≤ N →
      ∫⁻ W in Metric.closedBall (0 : Fin n → Fin 2 → Fin 2 → ℝ) r,
        ENNReal.ofReal (Real.exp (-(c * N * grpJ W))) ≤
          ENNReal.ofReal (C * N ^ (-(2 * (n : ℝ)) / 3)) := by
  obtain ⟨C₀, hC₀, hG⟩ := cubeSumSq_le_grpErr n
  set C₀' := max C₀ 1
  have hC₀' : 0 < C₀' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set c' := c / C₀'
  have hc' : 0 < c' := div_pos hc hC₀'
  obtain ⟨C, hC⟩ := hn r c' hr hc'
  refine ⟨max C 0 ^ 2, fun N hN => ?_⟩
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  set X := Fin n → ℝ × ℝ
  set Φ : X → ENNReal := (Metric.closedBall 0 r).indicator
    fun u => ENNReal.ofReal (Real.exp (-(c' * N * cubeSumSq u)))
  have hΦ : Measurable Φ := by
    refine Measurable.indicator ?_ Metric.isClosed_closedBall.measurableSet
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((continuous_cubeSumSq n).measurable).const_mul _).neg)
  have hpt : ∀ W : Fin n → Fin 2 → Fin 2 → ℝ, (Metric.closedBall 0 r).indicator
      (fun W => ENNReal.ofReal (Real.exp (-(c * N * grpJ W)))) W ≤
      Φ (grpRows W).1 * Φ (grpRows W).2 := by
    intro W
    by_cases hW : W ∈ Metric.closedBall (0 : Fin n → Fin 2 → Fin 2 → ℝ) r
    · rw [Set.indicator_of_mem hW]
      have hW' : ‖W‖ ≤ r := by simpa using hW
      have m0 : (grpRows W).1 ∈ Metric.closedBall (0 : X) r := by
        rw [mem_closedBall_zero_iff]; exact norm_grpRows_le W hr.le hW' 0
      have m1 : (grpRows W).2 ∈ Metric.closedBall (0 : X) r := by
        rw [mem_closedBall_zero_iff]; exact norm_grpRows_le W hr.le hW' 1
      simp only [Φ, Set.indicator_of_mem m0, Set.indicator_of_mem m1]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have g0 := hG (grpBlocks W) 0
      have g1 := hG (grpBlocks W) 1
      rw [grpRow_grpBlocks] at g0 g1
      have hJ : cubeSumSq (grpRows W).1 + cubeSumSq (grpRows W).2 ≤ C₀' * grpJ W := by
        simp only [grpJ, Fin.sum_univ_two, grpRows]
        have e0 := norm_nonneg (grpErr (grpBlocks W) n 0)
        have e1 := norm_nonneg (grpErr (grpBlocks W) n 1)
        have : C₀ ≤ C₀' := le_max_left _ _
        nlinarith [sq_nonneg ‖grpErr (grpBlocks W) n 0‖, sq_nonneg ‖grpErr (grpBlocks W) n 1‖]
      have : c' * N * (cubeSumSq (grpRows W).1 + cubeSumSq (grpRows W).2) ≤ c * N * grpJ W := by
        calc c' * N * (cubeSumSq (grpRows W).1 + cubeSumSq (grpRows W).2)
            ≤ c' * N * (C₀' * grpJ W) := mul_le_mul_of_nonneg_left hJ (by positivity)
          _ = c * N * grpJ W := by simp only [c']; field_simp
      linarith
    · rw [Set.indicator_of_notMem hW]; exact bot_le
  have hsplit : ∫⁻ W, Φ (grpRows W).1 * Φ (grpRows W).2 = (∫⁻ u, Φ u) * ∫⁻ u, Φ u := by
    have := (measurePreserving_grpRows n).lintegral_comp (f := fun q : X × X => Φ q.1 * Φ q.2)
      ((hΦ.comp measurable_fst).mul (hΦ.comp measurable_snd))
    rw [this, Measure.volume_eq_prod, lintegral_prod_mul hΦ.aemeasurable hΦ.aemeasurable]
  have hone : ∫⁻ u, Φ u ≤ ENNReal.ofReal (max C 0 * N ^ (-(n : ℝ) / 3)) := by
    rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet]
    exact (hC N hN).trans (ofReal_mul_le_max (by positivity))
  rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  calc ∫⁻ W, _ ≤ ∫⁻ W, Φ (grpRows W).1 * Φ (grpRows W).2 := lintegral_mono hpt
    _ = (∫⁻ u, Φ u) * ∫⁻ u, Φ u := hsplit
    _ ≤ ENNReal.ofReal (max C 0 * N ^ (-(n : ℝ) / 3)) *
          ENNReal.ofReal (max C 0 * N ^ (-(n : ℝ) / 3)) := mul_le_mul' hone hone
    _ = ENNReal.ofReal (max C 0 ^ 2 * N ^ (-(2 * (n : ℝ)) / 3)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : N ^ (-(n : ℝ) / 3) * N ^ (-(n : ℝ) / 3) = N ^ (-(2 * (n : ℝ)) / 3) := by
          rw [← Real.rpow_add hN0]; congr 1; ring
        rw [← this]; ring

end VectorSLT.IdentityGroup.Pairs
