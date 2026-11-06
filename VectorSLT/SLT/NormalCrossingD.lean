/-
L4: the `d`-variable normal-crossing lemma, by induction over `Fin (d+1)`.
-/
import VectorSLT.SLT.NormalCrossing
import VectorSLT.SLT.Laplace

namespace SLT

open MeasureTheory Set Filter Real

/-- `Z(N) = ∫_{(0,1]^d} e^{-N ∏ xᵢ^{2kᵢ}} ∏ xᵢ^{hᵢ} dx`. -/
noncomputable def ncZ {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ) (N : ℝ) : ENNReal :=
  ∫⁻ x in Set.pi univ (fun _ => Ioc (0 : ℝ) 1),
    ENNReal.ofReal (Real.exp (-(N * ∏ i, x i ^ (2 * k i))) * ∏ i, x i ^ h i)

theorem ncZ_zero (k : Fin 0 → ℕ) (h : Fin 0 → ℝ) (N : ℝ) :
    ncZ k h N = ENNReal.ofReal (Real.exp (-N)) := by
  unfold ncZ
  rw [lintegral_unique, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  simp [volume_pi_pi]

theorem ncZ_succ {d : ℕ} (k : Fin (d + 1) → ℕ) (h : Fin (d + 1) → ℝ) (N : ℝ) :
    ncZ k h N = stepG (ncZ (Fin.tail k) (Fin.tail h)) (h 0) (k 0) N := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have he : ∀ x : Fin (d + 1) → ℝ, e x = (x 0, Fin.tail x) := fun x => rfl
  set T : Set (Fin d → ℝ) := Set.pi univ (fun _ => Ioc (0 : ℝ) 1)
  set f : ℝ × (Fin d → ℝ) → ENNReal := fun p => ENNReal.ofReal
    (Real.exp (-(N * (p.1 ^ (2 * k 0) * ∏ j, p.2 j ^ (2 * k j.succ)))) *
      (p.1 ^ h 0 * ∏ j, p.2 j ^ h j.succ))
  have hf : Measurable f := by fun_prop
  have hS : Set.pi univ (fun _ => Ioc (0 : ℝ) 1) = e ⁻¹' (Ioc 0 1 ×ˢ T) := by
    ext x
    simp only [Set.mem_pi, mem_univ, forall_const, mem_preimage, he, mem_prod, T, Fin.tail]
    exact ⟨fun h => ⟨h 0, fun j => h j.succ⟩, fun h i => Fin.cases h.1 h.2 i⟩
  have hint : ∀ x : Fin (d + 1) → ℝ,
      ENNReal.ofReal (Real.exp (-(N * ∏ i, x i ^ (2 * k i))) * ∏ i, x i ^ h i) = f (e x) := by
    intro x; simp only [f, he, Fin.prod_univ_succ, Fin.tail]
  unfold ncZ
  simp_rw [hint]
  rw [hS, (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).setLIntegral_comp_preimage
    (measurableSet_Ioc.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)) hf,
    Measure.volume_eq_prod, setLIntegral_prod f hf.aemeasurable]
  unfold stepG
  refine setLIntegral_congr_fun measurableSet_Ioc fun x0 hx0 => ?_
  have hx : 0 ≤ x0 ^ h 0 := Real.rpow_nonneg hx0.1.le _
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) fun y _ => ?_
  simp only [f, Fin.tail]
  rw [← ENNReal.ofReal_mul hx]
  congr 1; ring_nf

/-! ### The exponents: `λ = min μᵢ`, `m = #argmin` -/

/-- `μᵢ = (hᵢ + 1)/(2kᵢ)`. -/
noncomputable def ncMu {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ) (i : Fin d) : ℝ :=
  (h i + 1) / (2 * k i)

/-- `λ = minᵢ μᵢ`. -/
noncomputable def ncLam {d : ℕ} (k : Fin (d + 1) → ℕ) (h : Fin (d + 1) → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (ncMu k h)

/-- `m = #{i : μᵢ = λ}`. -/
noncomputable def ncMult {d : ℕ} (k : Fin (d + 1) → ℕ) (h : Fin (d + 1) → ℝ) : ℕ :=
  (Finset.univ.filter fun i => ncMu k h i = ncLam k h).card

theorem ncLam_le {d : ℕ} (k : Fin (d + 1) → ℕ) (h : Fin (d + 1) → ℝ) (i : Fin (d + 1)) :
    ncLam k h ≤ ncMu k h i := Finset.inf'_le _ (Finset.mem_univ i)

theorem ncLam_succ {d : ℕ} (k : Fin (d + 2) → ℕ) (h : Fin (d + 2) → ℝ) :
    ncLam k h = min (ncMu k h 0) (ncLam (Fin.tail k) (Fin.tail h)) := by
  apply le_antisymm
  · exact le_min (ncLam_le k h 0) (Finset.le_inf' _ _ fun j _ => ncLam_le k h j.succ)
  · refine Finset.le_inf' _ _ fun i _ => ?_
    refine Fin.cases (min_le_left _ _) (fun j => (min_le_right _ _).trans ?_) i
    exact ncLam_le (Fin.tail k) (Fin.tail h) j

theorem ncLam_one (k : Fin 1 → ℕ) (h : Fin 1 → ℝ) : ncLam k h = ncMu k h 0 :=
  le_antisymm (ncLam_le k h 0) (Finset.le_inf' _ _ fun i _ => by rw [Fin.fin_one_eq_zero i])

theorem ncMult_one (k : Fin 1 → ℕ) (h : Fin 1 → ℝ) : ncMult k h = 1 := by
  unfold ncMult; rw [ncLam_one]
  exact Finset.card_eq_one.mpr ⟨0, by ext i; simp [Fin.fin_one_eq_zero i]⟩

theorem ncMult_succ {d : ℕ} (k : Fin (d + 2) → ℕ) (h : Fin (d + 2) → ℝ) :
    ncMult k h = (if ncMu k h 0 = ncLam k h then 1 else 0) +
      (Finset.univ.filter fun j : Fin (d + 1) => ncMu k h j.succ = ncLam k h).card := by
  unfold ncMult
  rw [Fin.card_filter_univ_succ]
  split_ifs <;> simp [add_comm]

theorem ncLam_pos {d : ℕ} {k : Fin (d + 1) → ℕ} {h : Fin (d + 1) → ℝ} (hk : ∀ i, 1 ≤ k i)
    (hh : ∀ i, -1 < h i) : 0 < ncLam k h := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (ncMu k h)
  rw [ncLam, hi, ncMu]
  have : (1 : ℝ) ≤ k i := by exact_mod_cast hk i
  have := hh i
  apply div_pos <;> linarith

theorem ncMult_pos {d : ℕ} (k : Fin (d + 1) → ℕ) (h : Fin (d + 1) → ℝ) : 1 ≤ ncMult k h := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (ncMu k h)
  unfold ncMult
  exact Finset.card_pos.mpr ⟨i, by simp [ncLam, hi]⟩

/-! ### The induction -/

/-- **All the bounds**, for every `d ≥ 1`. -/
theorem ncZ_bound : ∀ (d : ℕ) (k : Fin (d + 1) → ℕ) (h : Fin (d + 1) → ℝ),
    (∀ i, 1 ≤ k i) → (∀ i, -1 < h i) → NCBound (ncZ k h) (ncLam k h) (ncMult k h)
  | 0, k, h, hk, hh => by
    have e : ncZ k h = stepG (fun M => ENNReal.ofReal (Real.exp (-M))) (h 0) (k 0) := by
      funext N; rw [ncZ_succ]; congr 1; funext M; exact ncZ_zero _ _ M
    rw [e, ncLam_one, ncMult_one]
    exact NCBound.base (hh 0) (hk 0)
  | d + 1, k, h, hk, hh => by
    have IH := ncZ_bound d (Fin.tail k) (Fin.tail h) (fun j => hk j.succ) (fun j => hh j.succ)
    have e : ncZ k h = stepG (ncZ (Fin.tail k) (Fin.tail h)) (h 0) (k 0) := by
      funext N; exact ncZ_succ k h N
    rw [e]
    set lamt := ncLam (Fin.tail k) (Fin.tail h)
    set mt := ncMult (Fin.tail k) (Fin.tail h)
    have hμ0 : ncMu k h 0 = (h 0 + 1) / (2 * k 0) := rfl
    have htail : ∀ j : Fin (d + 1), ncMu k h j.succ = ncMu (Fin.tail k) (Fin.tail h) j := fun j => rfl
    have hlamt : 0 < lamt := ncLam_pos (fun j => hk j.succ) (fun j => hh j.succ)
    rcases lt_trichotomy (ncMu k h 0) lamt with hlt | heq | hgt
    · -- the new coordinate wins: (μ₀, 1)
      have hL : ncLam k h = ncMu k h 0 := by rw [ncLam_succ, min_eq_left hlt.le]
      have hM : ncMult k h = 1 := by
        rw [ncMult_succ, if_pos hL.symm]
        have : (Finset.univ.filter fun j : Fin (d + 1) => ncMu k h j.succ = ncLam k h) = ∅ := by
          apply Finset.filter_false_of_mem
          intro j _ hj
          rw [htail, hL] at hj
          have := ncLam_le (Fin.tail k) (Fin.tail h) j
          linarith
        rw [this]; rfl
      rw [hL, hM, hμ0]
      exact IH.step_gt (hh 0) (hk 0) (by rw [← hμ0]; exact hlt)
    · -- a tie: one more logarithm
      have hL : ncLam k h = lamt := by rw [ncLam_succ, heq, min_self]
      have hM : ncMult k h = mt + 1 := by
        rw [ncMult_succ, if_pos (heq.trans hL.symm), add_comm]
        congr 1
        unfold mt ncMult
        congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, htail, hL]; rfl
      rw [hL, hM]
      exact IH.step_eq (ncMult_pos _ _) (hh 0) (hk 0) (by rw [← hμ0]; exact heq.symm)
    · -- the tail wins: (lamt, mt)
      have hL : ncLam k h = lamt := by rw [ncLam_succ, min_eq_right hgt.le]
      have hM : ncMult k h = mt := by
        rw [ncMult_succ, if_neg (by rw [hL]; exact ne_of_gt hgt), zero_add]
        unfold mt ncMult
        congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, htail, hL]; rfl
      rw [hL, hM]
      exact IH.step_lt hlamt.le (hh 0) (hk 0) (by rw [← hμ0]; exact hgt)

/-- From the induction bounds to a learning pair. -/
theorem NCBound.hasLaplacePair {F : ℝ → ENNReal} {lam : ℝ} {m : ℕ} (hF : NCBound F lam m) :
    HasLaplacePair F lam m := by
  obtain ⟨-, -, -, ⟨C, hC⟩, hlow⟩ := hF
  refine ⟨hlow, ⟨max C 0 * 2 ^ (m - 1), Real.exp 1, fun N hN => ?_⟩⟩
  have hN1 : 1 ≤ N := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hN
  have hN0 : 0 < N := by linarith
  have hl : 1 ≤ Real.log N := by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hN
  refine (hC N hN1).trans (ENNReal.ofReal_le_ofReal ?_)
  have h2 : (1 + Real.log N) ^ (m - 1) ≤ 2 ^ (m - 1) * Real.log N ^ (m - 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hp : 0 ≤ N ^ (-lam) := Real.rpow_nonneg hN0.le _
  calc C * N ^ (-lam) * (1 + Real.log N) ^ (m - 1)
      ≤ max C 0 * N ^ (-lam) * (1 + Real.log N) ^ (m - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
          (pow_nonneg (by linarith) _)
    _ ≤ max C 0 * N ^ (-lam) * (2 ^ (m - 1) * Real.log N ^ (m - 1)) := by
        apply mul_le_mul_of_nonneg_left h2; positivity
    _ = _ := by ring

/-- **The normal-crossing lemma** (`d ≥ 1` variables). For `kᵢ ≥ 1` and `hᵢ > -1`,
`∫_{(0,1]^d} e^{-N ∏ xᵢ^{2kᵢ}} ∏ xᵢ^{hᵢ} dx ≍ N^{-λ} (log N)^{m-1}` with
`λ = minᵢ (hᵢ+1)/(2kᵢ)` and `m = #{i : (hᵢ+1)/(2kᵢ) = λ}`. -/
theorem normalCrossing {d : ℕ} (k : Fin (d + 1) → ℕ) (h : Fin (d + 1) → ℝ)
    (hk : ∀ i, 1 ≤ k i) (hh : ∀ i, -1 < h i) :
    HasLaplacePair (ncZ k h) (ncLam k h) (ncMult k h) :=
  (ncZ_bound d k h hk hh).hasLaplacePair

/-- The same, in `Z ν K` form: prior `ν = ∏ xᵢ^{hᵢ} dx` on `(0,1]^d`, loss `K = ∏ xᵢ^{2kᵢ}`. -/
theorem normalCrossing_Z {d : ℕ} (k : Fin (d + 1) → ℕ) (h : Fin (d + 1) → ℝ)
    (hk : ∀ i, 1 ≤ k i) (hh : ∀ i, -1 < h i) :
    HasLaplacePair
      (Z ((volume.restrict (Set.pi univ fun _ => Ioc (0 : ℝ) 1)).withDensity
        fun x => ENNReal.ofReal (∏ i, x i ^ h i)) (fun x => ∏ i, x i ^ (2 * k i)))
      (ncLam k h) (ncMult k h) := by
  have e : Z ((volume.restrict (Set.pi univ fun _ => Ioc (0 : ℝ) 1)).withDensity
        fun x => ENNReal.ofReal (∏ i, x i ^ h i)) (fun x => ∏ i, x i ^ (2 * k i)) = ncZ k h := by
    funext N
    unfold Z ncZ
    rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
    refine setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) fun x hx => ?_
    have : 0 ≤ ∏ i, x i ^ h i :=
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hx i (mem_univ i)).1.le _
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul this, mul_comm]
  rw [e]; exact normalCrossing k h hk hh

end SLT
