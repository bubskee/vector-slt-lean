/-
Paper 2, the last step of Proposition `prop:nonshear` and of Theorem `thm:invertible`:
integration over product boxes.

Once the loss satisfies `K ≥ κ (‖Δ‖² + g(u₀) + g(u₁))` on the support of the cutoff, where
`u_k` is the row `k` of the three inactive blocks and `g` is the identity-group functional of
that row, the integral factors: the active block gives `N⁻²` (a Gaussian in `ℝ⁴`) and each row
gives `N⁻¹`, by `CubeSumUpper` (`RowBound`). Here:

* `rowU`: the row `k` of the inactive blocks of `Raw16`, as `Fin 3 → ℝ × ℝ`, with the change of
  variables `lintegral_rowU` (a measure-preserving equivalence);
* `rowBound_three`, `rowBound_split`: `RowBound` from `CubeSumUpper 3`, and from `CubeSumUpper 1`
  and `CubeSumUpper 2` for a row split into a one-block and a two-block group;
* `layout_bound`: the product integral on `Raw16`;
* `Sp`: the coordinate involution of `Raw16` that exchanges block `p` with block `0`, used to
  move any position to the first-position layout (`lintegral_Sp`, Jacobian one);
* `position_bound`: the resulting upper bound `Z_N ≤ C N⁻⁴`, at any position.
-/
import VectorSLT.IdentityGroup.Defs
import VectorSLT.LowerPositions
import VectorSLT.TheoremM

namespace VectorSLT.IdentityGroup.Pairs

open MeasureTheory Set Filter Topology VectorSLT

/-! ### Rows of the inactive blocks -/

/-- The row of the three inactive blocks `W₂, W₃, W₄` read from one `Row` of `Raw16`:
form `i` is `(W_{i+2} k 0, W_{i+2} k 1)`. -/
def rowU (ρ : Row) : Fin 3 → ℝ × ℝ := fun i => (tri ρ.1 i, tri ρ.2 i)

/-- `ℝ³ ≃ᵐ (Fin 3 → ℝ)`, `t ↦ ![t.1, t.2.1, t.2.2]`. -/
def triE : (ℝ × ℝ × ℝ) ≃ᵐ (Fin 3 → ℝ) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow.symm).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm

theorem triE_apply (t : ℝ × ℝ × ℝ) (i : Fin 3) : triE t i = tri t i := by
  fin_cases i <;> rfl

theorem measurePreserving_triE : MeasurePreserving triE := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.finTwoArrow (α := ℝ)).symm) :=
    (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ).symm
  exact h1.trans (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0).symm

/-- `Row ≃ᵐ (Fin 3 → ℝ × ℝ)`, equal to `rowU`. -/
def rowE : Row ≃ᵐ (Fin 3 → ℝ × ℝ) :=
  (MeasurableEquiv.prodCongr triE triE).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 3)).symm

theorem rowE_apply (ρ : Row) : rowE ρ = rowU ρ := by
  funext i
  simp only [rowU]
  rw [← triE_apply, ← triE_apply]
  rfl

theorem measurePreserving_rowE : MeasurePreserving rowE :=
  (measurePreserving_triE.prod measurePreserving_triE).trans
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 3)).symm

/-- **Change of variables for a row.** -/
theorem lintegral_rowU (f : (Fin 3 → ℝ × ℝ) → ENNReal) :
    ∫⁻ ρ : Row, f (rowU ρ) = ∫⁻ u, f u := by
  simp_rw [← rowE_apply]
  exact measurePreserving_rowE.lintegral_comp_emb rowE.measurableEmbedding f

/-! ### Row bounds from `CubeSumUpper` -/

theorem continuous_cubeSumSq (k : ℕ) : Continuous (cubeSumSq : (Fin k → ℝ × ℝ) → ℝ) := by
  have h : ∀ j : Fin 4, Continuous fun u : Fin k → ℝ × ℝ => cubeSum u j := by
    intro j
    fin_cases j <;> simp only [cubeSum] <;> simp <;> fun_prop
  unfold cubeSumSq
  exact continuous_finsetSum _ fun j _ => (h j).pow 2

theorem cubeSumSq_nonneg {k : ℕ} (u : Fin k → ℝ × ℝ) : 0 ≤ cubeSumSq u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The row bound.** `∫_{‖u‖ ≤ r} e^{-c N g(u)} ≤ C N⁻¹` for every `c > 0` and `N ≥ 1`, on the
sup-norm ball of `Fin 3 → ℝ × ℝ`. -/
def RowBound (g : (Fin 3 → ℝ × ℝ) → ℝ) (r : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ C : ℝ, ∀ N : ℝ, 1 ≤ N →
    ∫⁻ u in Metric.closedBall (0 : Fin 3 → ℝ × ℝ) r,
      ENNReal.ofReal (Real.exp (-(c * N * g u))) ≤ ENNReal.ofReal (C * N⁻¹)

/-- A three-block identity group: `RowBound G₃` from `CubeSumUpper 3`. -/
theorem rowBound_three (h : CubeSumUpper 3) {r : ℝ} (hr : 0 < r) : RowBound cubeSumSq r := by
  intro c hc
  obtain ⟨C, hC⟩ := h r c hr hc
  refine ⟨C, fun N hN => ?_⟩
  have e : N ^ (-((3 : ℕ) : ℝ) / 3) = N⁻¹ := by
    rw [show (-((3 : ℕ) : ℝ) / 3) = -1 by norm_num, Real.rpow_neg_one]
  rw [← e]; exact hC N hN

theorem ofReal_mul_le_max {a b : ℝ} (hb : 0 ≤ b) :
    ENNReal.ofReal (a * b) ≤ ENNReal.ofReal (max a 0 * b) :=
  ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hb)

/-- A row split into a one-block group (form `i`) and a two-block group (the other two forms):
`RowBound (G₁ + G₂)` from `CubeSumUpper 1` and `CubeSumUpper 2`. -/
theorem rowBound_split (h1 : CubeSumUpper 1) (h2 : CubeSumUpper 2) {r : ℝ} (hr : 0 < r)
    (i : Fin 3) :
    RowBound (fun u => cubeSumSq (fun _ : Fin 1 => u i) +
      cubeSumSq (fun j : Fin 2 => u (i.succAbove j))) r := by
  intro c hc
  obtain ⟨C₁, hC₁⟩ := h1 r c hr hc
  obtain ⟨C₂, hC₂⟩ := h2 r c hr hc
  refine ⟨max C₁ 0 * max C₂ 0, fun N hN => ?_⟩
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  set X := ℝ × ℝ
  set e₁ : (Fin 1 → X) → ENNReal := fun v => ENNReal.ofReal (Real.exp (-(c * N * cubeSumSq v)))
  set e₂ : (Fin 2 → X) → ENNReal := fun v => ENNReal.ofReal (Real.exp (-(c * N * cubeSumSq v)))
  set Φ₁ : X → ENNReal := fun a => {a : X | ‖(fun _ : Fin 1 => a)‖ ≤ r}.indicator
    (fun a => e₁ fun _ => a) a
  set Φ₂ : (Fin 2 → X) → ENNReal := (Metric.closedBall 0 r).indicator e₂
  have hm1 : Measurable fun v : Fin 1 → X => cubeSumSq v := (continuous_cubeSumSq 1).measurable
  have hm2 : Measurable fun v : Fin 2 → X => cubeSumSq v := (continuous_cubeSumSq 2).measurable
  have hs1 : MeasurableSet {a : X | ‖(fun _ : Fin 1 => a)‖ ≤ r} :=
    measurableSet_le (by fun_prop) measurable_const
  have hΦ₁ : Measurable Φ₁ := by
    refine Measurable.indicator ?_ hs1
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((hm1.comp (measurable_pi_iff.mpr fun _ => measurable_id)).const_mul _).neg)
  have hΦ₂ : Measurable Φ₂ := by
    refine Measurable.indicator ?_ Metric.isClosed_closedBall.measurableSet
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hm2.const_mul _).neg)
  -- the integrand is dominated by the split product
  have hpt : ∀ u : Fin 3 → X, (Metric.closedBall 0 r).indicator
      (fun u => ENNReal.ofReal (Real.exp (-(c * N * (cubeSumSq (fun _ : Fin 1 => u i) +
        cubeSumSq (fun j : Fin 2 => u (i.succAbove j))))))) u ≤
      Φ₁ (u i) * Φ₂ (fun j => u (i.succAbove j)) := by
    intro u
    by_cases hu : u ∈ Metric.closedBall (0 : Fin 3 → X) r
    · rw [Set.indicator_of_mem hu]
      have hu' : ‖u‖ ≤ r := by simpa using hu
      have ha : ‖(fun _ : Fin 1 => u i)‖ ≤ r :=
        (pi_norm_le_iff_of_nonneg hr.le).mpr fun _ => (norm_le_pi_norm u i).trans hu'
      have hf : (fun j : Fin 2 => u (i.succAbove j)) ∈ Metric.closedBall (0 : Fin 2 → X) r := by
        rw [mem_closedBall_zero_iff]
        exact (pi_norm_le_iff_of_nonneg hr.le).mpr fun j => (norm_le_pi_norm u _).trans hu'
      simp only [Φ₁, Φ₂, Set.indicator_of_mem hf, Set.indicator_of_mem (show u i ∈
        {a : X | ‖(fun _ : Fin 1 => a)‖ ≤ r} from ha), e₁, e₂]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      apply le_of_eq; congr 2; ring
    · rw [Set.indicator_of_notMem hu]; exact bot_le
  have hsplit : ∫⁻ u : Fin 3 → X, Φ₁ (u i) * Φ₂ (fun j => u (i.succAbove j)) =
      (∫⁻ a, Φ₁ a) * ∫⁻ f, Φ₂ f := by
    have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => X) i
    have := hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
      (fun q : X × (Fin 2 → X) => Φ₁ q.1 * Φ₂ q.2)
    simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply] at this
    calc ∫⁻ u : Fin 3 → X, Φ₁ (u i) * Φ₂ (fun j => u (i.succAbove j))
        = ∫⁻ (a : Fin (2 + 1) → X), Φ₁ (a i) * Φ₂ (i.removeNth a) := rfl
      _ = _ := this
      _ = _ := by
        rw [Measure.volume_eq_prod, lintegral_prod_mul hΦ₁.aemeasurable hΦ₂.aemeasurable]
  have hone : ∫⁻ a, Φ₁ a = ∫⁻ v in Metric.closedBall (0 : Fin 1 → X) r, e₁ v := by
    rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet]
    have hmp := volume_preserving_funUnique (Fin 1) X
    rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    congr 1; funext v
    have hv : (fun _ : Fin 1 => v default) = v := funext fun j => by rw [Subsingleton.elim j]
    simp only [Φ₁, MeasurableEquiv.funUnique_apply]
    by_cases h : ‖v‖ ≤ r
    · have h' : ‖(fun _ : Fin 1 => v default)‖ ≤ r := by rw [hv]; exact h
      rw [Set.indicator_of_mem (show v default ∈ {a : X | ‖(fun _ : Fin 1 => a)‖ ≤ r} from h'),
        Set.indicator_of_mem (show v ∈ Metric.closedBall (0 : Fin 1 → X) r by simpa using h),
        hv]
    · have h' : ¬ ‖(fun _ : Fin 1 => v default)‖ ≤ r := by rw [hv]; exact h
      rw [Set.indicator_of_notMem (show v default ∉ {a : X | ‖(fun _ : Fin 1 => a)‖ ≤ r} from h'),
        Set.indicator_of_notMem (show v ∉ Metric.closedBall (0 : Fin 1 → X) r by simpa using h)]
  have htwo : ∫⁻ f, Φ₂ f = ∫⁻ v in Metric.closedBall (0 : Fin 2 → X) r, e₂ v :=
    lintegral_indicator Metric.isClosed_closedBall.measurableSet _
  have b1 := hC₁ N hN
  have b2 := hC₂ N hN
  rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  calc ∫⁻ u, _ ≤ ∫⁻ u : Fin 3 → X, Φ₁ (u i) * Φ₂ (fun j => u (i.succAbove j)) :=
        lintegral_mono hpt
    _ = (∫⁻ a, Φ₁ a) * ∫⁻ f, Φ₂ f := hsplit
    _ ≤ ENNReal.ofReal (max C₁ 0 * N ^ (-((1 : ℕ) : ℝ) / 3)) *
          ENNReal.ofReal (max C₂ 0 * N ^ (-((2 : ℕ) : ℝ) / 3)) := by
        rw [hone, htwo]
        exact mul_le_mul' (b1.trans (ofReal_mul_le_max (by positivity)))
          (b2.trans (ofReal_mul_le_max (by positivity)))
    _ = ENNReal.ofReal (max C₁ 0 * max C₂ 0 * N⁻¹) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : N ^ (-((1 : ℕ) : ℝ) / 3) * N ^ (-((2 : ℕ) : ℝ) / 3) = N⁻¹ := by
          rw [← Real.rpow_add hN0, show (-((1 : ℕ) : ℝ) / 3 + -((2 : ℕ) : ℝ) / 3) = -1 by norm_num,
            Real.rpow_neg_one]
        rw [← this]; ring

/-! ### The product integral in the first-position layout -/

/-- `‖M - A‖²` (Frobenius) for the active coordinates `θ.1` of `Raw16`. -/
def actSq (A : Matrix (Fin 2) (Fin 2) ℝ) (m : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  (m.1.1 - A 0 0) ^ 2 + (m.1.2 - A 0 1) ^ 2 + (m.2.1 - A 1 0) ^ 2 + (m.2.2 - A 1 1) ^ 2

/-- The Gaussian factor of the active block: `∫ e^{-M ‖m - A‖²} dm = (π/M)²`. -/
theorem lintegral_act (A : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : 0 < M) :
    ∫⁻ m : (ℝ × ℝ) × (ℝ × ℝ), ENNReal.ofReal (Real.exp (-(M * actSq A m))) =
      ENNReal.ofReal (Real.pi / M) * ENNReal.ofReal (Real.pi / M) := by
  set G : ℝ × ℝ → ENNReal := fun c => ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2))))
  have hG : Measurable G := by fun_prop
  have e : ∀ m : (ℝ × ℝ) × (ℝ × ℝ), ENNReal.ofReal (Real.exp (-(M * actSq A m))) =
      G (m.1 - (A 0 0, A 0 1)) * G (m.2 - (A 1 0, A 1 1)) := by
    intro m
    simp only [G, Prod.fst_sub, Prod.snd_sub]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, actSq]
    congr 2; ring
  simp_rw [e]
  rw [Measure.volume_eq_prod, lintegral_prod_mul (f := fun c : ℝ × ℝ => G (c - (A 0 0, A 0 1)))
    (g := fun c : ℝ × ℝ => G (c - (A 1 0, A 1 1)))
    (hG.comp (measurable_id.sub_const _)).aemeasurable
    (hG.comp (measurable_id.sub_const _)).aemeasurable,
    lintegral_sub_right_eq_self G, lintegral_sub_right_eq_self G, lintegral_gauss2 hM]

/-- The row factor `1{‖u‖ ≤ r} e^{-c N g(u)}`. -/
noncomputable def rowF (g : (Fin 3 → ℝ × ℝ) → ℝ) (r c : ℝ) (u : Fin 3 → ℝ × ℝ) : ENNReal :=
  (Metric.closedBall 0 r).indicator (fun u => ENNReal.ofReal (Real.exp (-(c * g u)))) u

/-- The first-position layout integrand:
`e^{-c ‖M - A‖²} · 1{‖u₀‖ ≤ r} e^{-c g(u₀)} · 1{‖u₁‖ ≤ r} e^{-c g(u₁)}`. -/
noncomputable def layoutF (A : Matrix (Fin 2) (Fin 2) ℝ) (g : (Fin 3 → ℝ × ℝ) → ℝ) (r c : ℝ)
    (θ : Raw16) : ENNReal :=
  ENNReal.ofReal (Real.exp (-(c * actSq A θ.1))) * (rowF g r c (rowU θ.2.1) * rowF g r c (rowU θ.2.2))

/-- **The product integral.** With `RowBound g r`, the layout integral at scale `κ N` is
`O(N⁻⁴)`: `N⁻²` from the active block and `N⁻¹` from each row. -/
theorem layout_bound (A : Matrix (Fin 2) (Fin 2) ℝ) {g : (Fin 3 → ℝ × ℝ) → ℝ} {r : ℝ}
    (hg : RowBound g r) (hgm : Measurable g) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, ∀ N : ℝ, 1 ≤ N → ∫⁻ θ, layoutF A g r (κ * N) θ ≤ ENNReal.ofReal (C * N⁻¹ ^ 4) := by
  obtain ⟨C, hC⟩ := hg κ hκ
  refine ⟨(Real.pi / κ) ^ 2 * max C 0 ^ 2, fun N hN => ?_⟩
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  have hR : Measurable (rowF g r (κ * N)) := by
    refine Measurable.indicator ?_ Metric.isClosed_closedBall.measurableSet
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hgm.const_mul _).neg)
  have hRρ : Measurable fun ρ : Row => rowF g r (κ * N) (rowU ρ) := by
    have : (fun ρ : Row => rowF g r (κ * N) (rowU ρ)) = fun ρ => rowF g r (κ * N) (rowE ρ) := by
      funext ρ; rw [rowE_apply]
    rw [this]; exact hR.comp rowE.measurable
  have hrow : ∫⁻ ρ : Row, rowF g r (κ * N) (rowU ρ) ≤ ENNReal.ofReal (max C 0 * N⁻¹) := by
    rw [lintegral_rowU]
    simp only [rowF]
    rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet]
    have := hC N hN
    simp only [mul_assoc] at this ⊢
    exact this.trans (ofReal_mul_le_max (by positivity))
  have hact := lintegral_act A (mul_pos hκ hN0)
  have hAm : Measurable fun m : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (Real.exp (-(κ * N * actSq A m))) := by
    unfold actSq; fun_prop
  calc ∫⁻ θ, layoutF A g r (κ * N) θ
      = (∫⁻ m, ENNReal.ofReal (Real.exp (-(κ * N * actSq A m)))) *
          ((∫⁻ ρ : Row, rowF g r (κ * N) (rowU ρ)) * ∫⁻ ρ : Row, rowF g r (κ * N) (rowU ρ)) := by
        simp only [layoutF]
        rw [Measure.volume_eq_prod, lintegral_prod_mul
          (f := fun m : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (Real.exp (-(κ * N * actSq A m))))
          (g := fun z : Row × Row => rowF g r (κ * N) (rowU z.1) * rowF g r (κ * N) (rowU z.2))
          hAm.aemeasurable
          ((hRρ.comp measurable_fst).mul (hRρ.comp measurable_snd)).aemeasurable]
        congr 1
        rw [Measure.volume_eq_prod (α := Row) (β := Row), lintegral_prod_mul (f := fun ρ : Row => rowF g r (κ * N) (rowU ρ))
          (g := fun ρ : Row => rowF g r (κ * N) (rowU ρ)) hRρ.aemeasurable hRρ.aemeasurable]
    _ ≤ (ENNReal.ofReal (Real.pi / (κ * N)) * ENNReal.ofReal (Real.pi / (κ * N))) *
          (ENNReal.ofReal (max C 0 * N⁻¹) * ENNReal.ofReal (max C 0 * N⁻¹)) := by
        rw [hact]; gcongr
    _ = ENNReal.ofReal ((Real.pi / κ) ^ 2 * max C 0 ^ 2 * N⁻¹ ^ 4) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp

/-! ### Moving any position to the first-position layout -/

/-- Exchange block `0` and block `p` in one entry `((W₁)ᵢⱼ, (W₂)ᵢⱼ, (W₃)ᵢⱼ, (W₄)ᵢⱼ)`. -/
def swapE : Fin 4 → ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ
  | 0, e => e
  | 1, e => (e.2.1, e.1, e.2.2.1, e.2.2.2)
  | 2, e => (e.2.2.1, e.2.1, e.1, e.2.2.2)
  | 3, e => (e.2.2.2, e.2.1, e.2.2.1, e.1)

theorem swapE_swapE (p : Fin 4) (e : ℝ × ℝ × ℝ × ℝ) : swapE p (swapE p e) = e := by
  fin_cases p <;> rfl

/-- The coordinate involution of `Raw16` exchanging block `0` (`W₁`) and block `p`. -/
def Sfun (p : Fin 4) (θ : Raw16) : Raw16 := ofEnt fun i j => swapE p (ent θ i j)

theorem Sfun_Sfun (p : Fin 4) (θ : Raw16) : Sfun p (Sfun p θ) = θ := by
  simp only [Sfun, ent_ofEnt, swapE_swapE]; exact ofEnt_ent θ

/-- `Sfun p` as a linear equivalence. -/
noncomputable def Slin (p : Fin 4) : Raw16 ≃ₗ[ℝ] Raw16 where
  toFun := Sfun p
  invFun := Sfun p
  map_add' x y := by
    simp only [Sfun]; rw [← ofEnt_add]; congr 1; funext i j
    simp only [Pi.add_apply, ent_add]
    fin_cases p <;> rfl
  map_smul' c x := by
    simp only [Sfun, RingHom.id_apply]; rw [← ofEnt_smul]; congr 1; funext i j
    simp only [Pi.smul_apply, ent_smul]
    fin_cases p <;> rfl
  left_inv := Sfun_Sfun p
  right_inv := Sfun_Sfun p

/-- **`Sfun p` preserves Lebesgue measure** (its determinant squares to one). -/
theorem lintegral_Sfun (p : Fin 4) (f : Raw16 → ENNReal) :
    ∫⁻ θ, f (Sfun p θ) = ∫⁻ θ, f θ := by
  have hdet : |(LinearMap.det (Slin p : Raw16 →ₗ[ℝ] Raw16))⁻¹| = 1 := by
    have hsq : LinearMap.det (Slin p : Raw16 →ₗ[ℝ] Raw16) ^ 2 = 1 := by
      have hc : (Slin p : Raw16 →ₗ[ℝ] Raw16) ∘ₗ (Slin p : Raw16 →ₗ[ℝ] Raw16) = LinearMap.id := by
        exact LinearMap.ext fun θ => Sfun_Sfun p θ
      rw [sq, ← LinearMap.det_comp, hc, LinearMap.det_id]
    have habs : |LinearMap.det (Slin p : Raw16 →ₗ[ℝ] Raw16)| = 1 := by
      have h := congrArg abs hsq
      rw [abs_pow, abs_one] at h
      exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by norm_num)).mp h
    rw [abs_inv, habs, inv_one]
  have h := lintegral_linearEquiv (Slin p) (fun θ => f (Sfun p θ))
  rw [hdet, ENNReal.ofReal_one, one_mul] at h
  rw [h]; congr 1; funext θ
  exact congrArg f (Sfun_Sfun p θ)

/-- The inactive blocks of position `p`, in the order in which `Sfun p` lists them. -/
def inact : Fin 4 → Fin 3 → ℕ
  | 0 => ![1, 2, 3]
  | 1 => ![0, 2, 3]
  | 2 => ![1, 0, 3]
  | 3 => ![1, 2, 0]

theorem inact_ne (p : Fin 4) (i : Fin 3) : inact p i ≠ p.val := by
  fin_cases p <;> fin_cases i <;> decide

theorem Sfun_act (p : Fin 4) (θ : Raw16) :
    (Sfun p θ).1 = ((weights θ p 0 0, weights θ p 0 1), (weights θ p 1 0, weights θ p 1 1)) := by
  fin_cases p <;> rfl

theorem rowU_Sfun (p : Fin 4) (θ : Raw16) (k : Fin 2) :
    rowU (![(Sfun p θ).2.1, (Sfun p θ).2.2] k) =
      fun i => (weights θ (inact p i) k 0, weights θ (inact p i) k 1) := by
  funext i
  fin_cases p <;> fin_cases k <;> fin_cases i <;> rfl

theorem actSq_Sfun (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4) (θ : Raw16) :
    actSq A (Sfun p θ).1 = ∑ i, ∑ j, (weights θ p i j - A i j) ^ 2 := by
  rw [Sfun_act, actSq, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]; ring

/-! ### Entries are bounded by the sup norm -/

theorem abs_tri_le (ρ : ℝ × ℝ × ℝ) (m : ℕ) : |tri ρ m| ≤ ‖ρ‖ := by
  rcases m with _ | _ | m
  · simpa [tri] using norm_fst_le ρ
  · simpa [tri, Real.norm_eq_abs] using (norm_fst_le ρ.2).trans (norm_snd_le ρ)
  · simpa [tri, Real.norm_eq_abs] using (norm_snd_le ρ.2).trans (norm_snd_le ρ)

theorem abs_weights_le (η : Raw16) (q : ℕ) (i j : Fin 2) : |weights η q i j| ≤ ‖η‖ := by
  rcases q with _ | m
  · rw [weights_zero_ent]
    have h1 : ‖η.1‖ ≤ ‖η‖ := norm_fst_le η
    fin_cases i <;> fin_cases j <;> simp only [ent] <;>
      simp <;>
      first
      | exact ((norm_fst_le η.1.1).trans (norm_fst_le η.1)).trans h1
      | exact ((norm_snd_le η.1.1).trans (norm_fst_le η.1)).trans h1
      | exact ((norm_fst_le η.1.2).trans (norm_snd_le η.1)).trans h1
      | exact ((norm_snd_le η.1.2).trans (norm_snd_le η.1)).trans h1
  · rw [weights_succ_ent]
    have h2 : ‖η.2‖ ≤ ‖η‖ := norm_snd_le η
    refine (abs_tri_le _ m).trans ?_
    fin_cases i <;> fin_cases j <;> simp only [ent] <;> simp <;>
      first
      | exact ((norm_fst_le η.2.1).trans (norm_fst_le η.2)).trans h2
      | exact ((norm_snd_le η.2.1).trans (norm_fst_le η.2)).trans h2
      | exact ((norm_fst_le η.2.2).trans (norm_snd_le η.2)).trans h2
      | exact ((norm_snd_le η.2.2).trans (norm_snd_le η.2)).trans h2

theorem weights_sub (θ η : Raw16) (q : ℕ) : weights (θ - η) q = weights θ q - weights η q := by
  have h := weights_add (θ - η) η q
  rw [sub_add_cancel] at h
  rw [h]; abel

/-- Off the active position, the weights of `θ` are those of `θ - θ₀⁽ᵖ⁾`. -/
theorem weights_eq_sub_base (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4) (θ : Raw16) {q : ℕ}
    (hq : q < 4) (hqp : q ≠ p.val) : weights θ q = weights (θ - basePos A p) q := by
  rw [weights_sub, weights_basePos A p q hq]; simp [hqp]

theorem inact_lt (p : Fin 4) (i : Fin 3) : inact p i < 4 := by
  fin_cases p <;> fin_cases i <;> decide

theorem rowU_Sfun_norm (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4) (θ : Raw16) (k : Fin 2)
    {r : ℝ} (hr : 0 ≤ r) (hθ : ‖θ - basePos A p‖ ≤ r) :
    ‖rowU (![(Sfun p θ).2.1, (Sfun p θ).2.2] k)‖ ≤ r := by
  rw [rowU_Sfun]
  refine (pi_norm_le_iff_of_nonneg hr).mpr fun i => ?_
  rw [weights_eq_sub_base A p θ (inact_lt p i) (inact_ne p i)]
  refine (norm_prod_le_iff).mpr ⟨?_, ?_⟩ <;> rw [Real.norm_eq_abs] <;>
    exact (abs_weights_le _ _ _ _).trans hθ

/-! ### The upper bound at any position -/

/-- **`Z_N ≤ C N⁻⁴` at position `p`**, from a loss lower bound on the support of the cutoff:
`κ (‖W_p - A‖² + g(u₀) + g(u₁)) ≤ K(θ)` for `‖θ - θ₀⁽ᵖ⁾‖ ≤ r`, where `u_k` is the row `k` of the
inactive blocks in the order `inact p`, and `RowBound g r`. -/
theorem position_bound (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4) {g : (Fin 3 → ℝ × ℝ) → ℝ}
    {r : ℝ} (hr : 0 < r) (hg : RowBound g r) (hgm : Measurable g) (K : Raw16 → ℝ)
    {κ : ℝ} (hκ : 0 < κ)
    (hK : ∀ θ, ‖θ - basePos A p‖ ≤ r →
      κ * (actSq A (Sfun p θ).1 + g (rowU (Sfun p θ).2.1) + g (rowU (Sfun p θ).2.2)) ≤ K θ)
    (φ χ : Raw16 → ENNReal) {π₁ : ℝ} (hπ₁ : 0 ≤ π₁) (hφ : ∀ θ, φ θ ≤ ENNReal.ofReal π₁)
    (hχ : ∀ θ, χ θ ≤ 1) (hχs : ∀ θ, r < ‖θ‖ → χ θ = 0) :
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * K θ))) * (φ θ * χ (θ - basePos A p)) ≤
        ENNReal.ofReal (C * N⁻¹ ^ 4) := by
  obtain ⟨C, hC⟩ := layout_bound A hg hgm hκ
  refine ⟨π₁ * max C 0, 1, fun N hN => ?_⟩
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hpt : ∀ θ, ENNReal.ofReal (Real.exp (-(N * K θ))) * (φ θ * χ (θ - basePos A p)) ≤
      ENNReal.ofReal π₁ * layoutF A g r (κ * N) (Sfun p θ) := by
    intro θ
    by_cases hθ : ‖θ - basePos A p‖ ≤ r
    · have h0 := rowU_Sfun_norm A p θ 0 hr.le hθ
      have h1 := rowU_Sfun_norm A p θ 1 hr.le hθ
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      simp only [layoutF, rowF]
      rw [Set.indicator_of_mem (show rowU (Sfun p θ).2.1 ∈ Metric.closedBall 0 r by simpa using h0),
        Set.indicator_of_mem (show rowU (Sfun p θ).2.2 ∈ Metric.closedBall 0 r by simpa using h1),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add, ← Real.exp_add, mul_comm (ENNReal.ofReal π₁)]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) ?_
      · have := hK θ hθ
        nlinarith
      · calc φ θ * χ (θ - basePos A p) ≤ ENNReal.ofReal π₁ * 1 := mul_le_mul' (hφ θ) (hχ _)
          _ = _ := mul_one _
    · push Not at hθ
      rw [hχs _ hθ, mul_zero, mul_zero]; exact bot_le
  calc ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * K θ))) * (φ θ * χ (θ - basePos A p))
      ≤ ∫⁻ θ, ENNReal.ofReal π₁ * layoutF A g r (κ * N) (Sfun p θ) := lintegral_mono hpt
    _ = ENNReal.ofReal π₁ * ∫⁻ θ, layoutF A g r (κ * N) θ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_Sfun p (layoutF A g r (κ * N))]
    _ ≤ ENNReal.ofReal π₁ * ENNReal.ofReal (max C 0 * N⁻¹ ^ 4) :=
        mul_le_mul' le_rfl ((hC N hN).trans (ofReal_mul_le_max (by positivity)))
    _ = ENNReal.ofReal (π₁ * max C 0 * N⁻¹ ^ 4) := by
        rw [← ENNReal.ofReal_mul hπ₁, mul_assoc]

end VectorSLT.IdentityGroup.Pairs
