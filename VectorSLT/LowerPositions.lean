/-
Brief 03, O3: the lower bound `c N⁻⁴ ≤ Z_{N,j}` at every active position.

Source: Theorem N §1 (`shear_middle_exact.md`, the lower-bound paragraph) and Theorem K §6
(`shear_exceptional_strata.md`, last paragraph), cubic-chaos f40fcb3.

The paper's box is `|u| ≲ N^{-1/2}` in the active coordinates and `|w| ≲ N^{-1/6}` in the
inactive ones. Here it is taken directly in **raw** coordinates (`pBox p t`, `t = N^{-1/6}`):
the four active raw entries in `[-t³, t³]`, the twelve inactive raw entries in `[-t, t]`.
An inactive layer contributes `(Wz)^{⊙3} = O(t³)`, an active perturbation `O(t³)`, so the
sup-norm error on `[-1,1]²` is `O(t³) = O(N^{-1/2})` (`err_box`) and the loss is `O(N⁻¹)`.
The volume is `2¹⁶ t²⁴ = 2¹⁶ N⁻⁴`. (An isotropic raw ball of radius `N^{-1/6}` would move the
active entries by `N^{-1/6}`; the anisotropy is essential, as the paper warns.)

Nothing here uses the shear structure: the bound holds for every target `A`, every position,
and every finite input law with finite 162nd moments.
-/
import VectorSLT.TwoSidedLaws
import VectorSLT.Pairs
import VectorSLT.ErrorBound

namespace VectorSLT

open MeasureTheory Set Filter Topology Matrix

/-! ### One layer, perturbed -/

theorem dot_le {W : Matrix (Fin 2) (Fin 2) ℝ} {w R : ℝ} (hW : ∀ i j, |W i j| ≤ w)
    {y : Fin 2 → ℝ} (hy : ∀ i, |y i| ≤ R) (k : Fin 2) : |W k ⬝ᵥ y| ≤ 2 * w * R := by
  have hw : 0 ≤ w := (abs_nonneg _).trans (hW 0 0)
  simp only [dotProduct, Fin.sum_univ_two]
  calc |W k 0 * y 0 + W k 1 * y 1| ≤ |W k 0| * |y 0| + |W k 1| * |y 1| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ w * R + w * R :=
        add_le_add (mul_le_mul (hW _ _) (hy 0) (abs_nonneg _) hw)
          (mul_le_mul (hW _ _) (hy 1) (abs_nonneg _) hw)
    _ = 2 * w * R := by ring

/-- Trajectory radius bound. -/
noncomputable def Rs (β : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => Rs β n + (2 * (β + 1) * Rs β n) ^ 3

/-- Trajectory error coefficient: the error after `n` layers is `≤ Es β n · t³`. -/
noncomputable def Es (β : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 + 6 * (2 * (β + 1) * Rs β n) ^ 2 * β) * Es β n +
      6 * (2 * (β + 1) * Rs β n) ^ 2 * Rs β n + (2 * Rs β n) ^ 3

theorem Rs_nonneg {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) : 0 ≤ Rs β n := by
  induction n with
  | zero => simp [Rs]
  | succ n ih => simp only [Rs]; positivity

theorem Es_nonneg {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) : 0 ≤ Es β n := by
  induction n with
  | zero => simp [Es]
  | succ n ih => have := Rs_nonneg hβ n; simp only [Es]; positivity

/-- **Trajectory comparison.** Base weights `B` (entries `≤ β`, zero off position `p`) and
perturbations `D` (entries `≤ t³` at position `p`, `≤ t` elsewhere). On `|xᵢ| ≤ 1`, both
trajectories stay in the `Rs`-box and differ by at most `Es · t³`. -/
theorem traj {β t : ℝ} (hβ : 0 ≤ β) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (B D : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ)
    (hB : ∀ q i j, |B q i j| ≤ β) (hB0 : ∀ q, q ≠ p → B q = 0)
    (hD : ∀ q < 4, ∀ i j, |D q i j| ≤ if q = p then t ^ 3 else t)
    {x : Fin 2 → ℝ} (hx : ∀ i, |x i| ≤ 1) :
    ∀ n ≤ 4, (∀ i, |prefixNet (fun q => B q + D q) n x i| ≤ Rs β n) ∧
      (∀ i, |prefixNet B n x i| ≤ Rs β n) ∧
      ∀ i, |prefixNet (fun q => B q + D q) n x i - prefixNet B n x i| ≤ Es β n * t ^ 3 := by
  intro n hn
  induction n with
  | zero => exact ⟨fun i => by simpa [Rs] using hx i, fun i => by simpa [Rs] using hx i,
      fun i => by simp [Es]⟩
  | succ n ih =>
    obtain ⟨hy, hz, he⟩ := ih (by omega)
    set y := prefixNet (fun q => B q + D q) n x
    set z := prefixNet B n x
    set R := Rs β n
    have hR : 0 ≤ R := Rs_nonneg hβ n
    have ht3 : t ^ 3 ≤ 1 := pow_le_one₀ ht0 ht1
    have ht3' : 0 ≤ t ^ 3 := by positivity
    have hDn : ∀ i j, |D n i j| ≤ if n = p then t ^ 3 else t := hD n (by omega)
    have hD1 : ∀ i j, |D n i j| ≤ 1 := fun i j => (hDn i j).trans (by split_ifs <;> assumption)
    have hW : ∀ i j, |(B n + D n) i j| ≤ β + 1 := fun i j => by
      rw [Matrix.add_apply]
      exact (abs_add_le _ _).trans (add_le_add (hB n i j) (hD1 i j))
    have hBn : ∀ i j, |B n i j| ≤ β + 1 := fun i j => (hB n i j).trans (by linarith)
    set m := 2 * (β + 1) * R
    have hm : 0 ≤ m := by positivity
    have hyW : ∀ k, |(B n + D n) k ⬝ᵥ y| ≤ m := fun k => dot_le hW hy k
    have hzB : ∀ k, |B n k ⬝ᵥ z| ≤ m := fun k => dot_le hBn hz k
    have hstep : ∀ (w : Fin 2 → ℝ) (v : ℝ) (k : Fin 2), |w k| ≤ R → |v| ≤ m →
        |w k + v ^ 3| ≤ R + m ^ 3 := by
      intro w v k hw hv
      have hv3 : |v ^ 3| ≤ m ^ 3 := by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hv 3
      exact (abs_add_le _ _).trans (add_le_add hw hv3)
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
    · rw [prefixNet_succ, Function.comp_apply, layer_apply]; exact hstep y _ i (hy i) (hyW i)
    · rw [prefixNet_succ, Function.comp_apply, layer_apply]; exact hstep z _ i (hz i) (hzB i)
    · rw [prefixNet_succ, prefixNet_succ, Function.comp_apply, Function.comp_apply, layer_apply,
        layer_apply]
      show |y i + ((B n + D n) i ⬝ᵥ y) ^ 3 - (z i + (B n i ⬝ᵥ z) ^ 3)| ≤ Es β (n + 1) * t ^ 3
      have hE0 := Es_nonneg hβ n
      have e1 : y i + ((B n + D n) i ⬝ᵥ y) ^ 3 - (z i + (B n i ⬝ᵥ z) ^ 3) =
          (y i - z i) + (((B n + D n) i ⬝ᵥ y) ^ 3 - (B n i ⬝ᵥ z) ^ 3) := by ring
      rw [e1]
      refine (abs_add_le _ _).trans ?_
      by_cases hnp : n = p
      · -- active layer
        have hdiff : |(B n + D n) i ⬝ᵥ y - B n i ⬝ᵥ z| ≤ 2 * β * (Es β n * t ^ 3) +
            2 * t ^ 3 * R := by
          have : (B n + D n) i ⬝ᵥ y - B n i ⬝ᵥ z = B n i ⬝ᵥ (y - z) + D n i ⬝ᵥ y := by
            rw [show ((B n + D n) i) = B n i + D n i from rfl, add_dotProduct, dotProduct_sub]
            ring
          rw [this]
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · exact dot_le (hB n) (fun j => by simpa using he j) i
          · exact dot_le (fun a b => by simpa [hnp] using hDn a b) hy i
        have hc := cube_diff_le (hyW i) (hzB i)
        calc |y i - z i| + |((B n + D n) i ⬝ᵥ y) ^ 3 - (B n i ⬝ᵥ z) ^ 3|
            ≤ Es β n * t ^ 3 + 3 * m ^ 2 * (2 * β * (Es β n * t ^ 3) + 2 * t ^ 3 * R) :=
              add_le_add (he i) (hc.trans (mul_le_mul_of_nonneg_left hdiff (by positivity)))
          _ ≤ Es β (n + 1) * t ^ 3 := by
              simp only [Es]
              have : 0 ≤ (2 * Rs β n) ^ 3 * t ^ 3 := by have := Rs_nonneg hβ n; positivity
              nlinarith
      · -- inactive layer: `B n = 0`
        have hB0n := hB0 n hnp
        have hz0 : B n i ⬝ᵥ z = 0 := by simp [hB0n]
        rw [hz0]
        have hDy : |(B n + D n) i ⬝ᵥ y| ≤ 2 * t * R := by
          rw [hB0n, zero_add]
          exact dot_le (fun a b => by simpa [hnp] using hDn a b) hy i
        have hcube : |((B n + D n) i ⬝ᵥ y) ^ 3 - 0 ^ 3| ≤ (2 * R) ^ 3 * t ^ 3 := by
          rw [zero_pow (by norm_num), sub_zero, abs_pow]
          calc |(B n + D n) i ⬝ᵥ y| ^ 3 ≤ (2 * t * R) ^ 3 :=
                pow_le_pow_left₀ (abs_nonneg _) hDy 3
            _ = (2 * R) ^ 3 * t ^ 3 := by ring
        calc |y i - z i| + |((B n + D n) i ⬝ᵥ y) ^ 3 - 0 ^ 3|
            ≤ Es β n * t ^ 3 + (2 * R) ^ 3 * t ^ 3 := add_le_add (he i) hcube
          _ ≤ Es β (n + 1) * t ^ 3 := by
              simp only [Es]
              have h1 : 0 ≤ 6 * (2 * (β + 1) * Rs β n) ^ 2 * β * Es β n * t ^ 3 := by
                positivity
              have h2 : 0 ≤ 6 * (2 * (β + 1) * Rs β n) ^ 2 * Rs β n * t ^ 3 := by
                have := Rs_nonneg hβ n; positivity
              nlinarith

/-! ### Weights of a translated parameter -/

theorem tri_add (v w : ℝ × ℝ × ℝ) (m : ℕ) : tri (v + w) m = tri v m + tri w m := by
  rcases m with _ | _ | m <;> rfl

theorem weights_add (θ η : Raw16) (q : ℕ) : weights (θ + η) q = weights θ q + weights η q := by
  ext i j
  rcases q with _ | m
  · simp only [Matrix.add_apply, weights_zero_ent, ent_add, Prod.fst_add]
  · simp only [Matrix.add_apply, weights_succ_ent, ent_add, Prod.snd_add, tri_add]

/-! ### The anisotropic raw box -/

/-- Half-width of block `k`: `t³` at the active position, `t` elsewhere. -/
def wd (p : Fin 4) (k : ℕ) (t : ℝ) : ℝ := if k = p.val then t ^ 3 else t

def Ib (δ : ℝ) : Set ℝ := Icc (-δ) δ

def triBox (p : Fin 4) (t : ℝ) : Set (ℝ × ℝ × ℝ) := Ib (wd p 1 t) ×ˢ (Ib (wd p 2 t) ×ˢ Ib (wd p 3 t))

def mBox (p : Fin 4) (t : ℝ) : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (Ib (wd p 0 t) ×ˢ Ib (wd p 0 t)) ×ˢ (Ib (wd p 0 t) ×ˢ Ib (wd p 0 t))

/-- **The anisotropic box** of Theorem K §6 / Theorem N §1, in raw coordinates. -/
def pBox (p : Fin 4) (t : ℝ) : Set Raw16 :=
  mBox p t ×ˢ ((triBox p t ×ˢ triBox p t) ×ˢ (triBox p t ×ˢ triBox p t))

theorem measurableSet_pBox (p : Fin 4) (t : ℝ) : MeasurableSet (pBox p t) := by
  simp only [pBox, mBox, triBox, Ib]
  repeat' first | exact measurableSet_Icc | apply MeasurableSet.prod

theorem vol_Ib (δ : ℝ) : volume (Ib δ) = ENNReal.ofReal (2 * δ) := by
  rw [Ib, Real.volume_Icc]; ring_nf

theorem volume_pBox (p : Fin 4) {t : ℝ} (ht : 0 ≤ t) :
    volume (pBox p t) = ENNReal.ofReal (2 ^ 16 * t ^ 24) := by
  simp only [pBox, mBox, triBox, Measure.volume_eq_prod, Measure.prod_prod, vol_Ib]
  have h1 : 0 ≤ 2 * t ^ 3 := by positivity
  have h2 : 0 ≤ 2 * t := by positivity
  rw [show (2 : ℝ) ^ 16 * t ^ 24 = (2 * t ^ 3) ^ 4 * (2 * t) ^ 12 by ring,
    ENNReal.ofReal_mul (pow_nonneg h1 4), ENNReal.ofReal_pow h1, ENNReal.ofReal_pow h2]
  fin_cases p <;> simp [wd] <;> ring

theorem wd_le {p : Fin 4} {k : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : wd p k t ≤ t := by
  unfold wd; split_ifs
  · calc t ^ 3 ≤ t ^ 1 := pow_le_pow_of_le_one ht0 ht1 (by norm_num)
      _ = t := pow_one t
  · exact le_rfl

theorem pBox_weights {p : Fin 4} {t : ℝ} {η : Raw16} (hη : η ∈ pBox p t) :
    ∀ q < 4, ∀ i j, |weights η q i j| ≤ wd p q t := by
  obtain ⟨⟨⟨m00, m01⟩, ⟨m10, m11⟩⟩, ⟨⟨⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩⟩, ⟨⟨c0, c1, c2⟩,
    ⟨e0, e1, e2⟩⟩⟩⟩ := η
  simp only [pBox, mBox, triBox, Ib, mem_prod, mem_Icc] at hη
  obtain ⟨⟨⟨hm00, hm01⟩, ⟨hm10, hm11⟩⟩, ⟨⟨⟨ha0, ha1, ha2⟩, ⟨hb0, hb1, hb2⟩⟩, ⟨⟨hc0, hc1, hc2⟩,
    ⟨he0, he1, he2⟩⟩⟩⟩ := hη
  intro q hq i j
  interval_cases q <;> fin_cases i <;> fin_cases j <;>
    simp [weights, tri, abs_le] <;> constructor <;> linarith

theorem pBox_norm {p : Fin 4} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {η : Raw16}
    (hη : η ∈ pBox p t) : ‖η‖ ≤ t := by
  have hw : ∀ k, wd p k t ≤ t := fun k => wd_le ht0 ht1
  obtain ⟨⟨⟨m00, m01⟩, ⟨m10, m11⟩⟩, ⟨⟨⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩⟩, ⟨⟨c0, c1, c2⟩,
    ⟨e0, e1, e2⟩⟩⟩⟩ := η
  simp only [pBox, mBox, triBox, Ib, mem_prod, mem_Icc] at hη
  obtain ⟨⟨⟨hm00, hm01⟩, ⟨hm10, hm11⟩⟩, ⟨⟨⟨ha0, ha1, ha2⟩, ⟨hb0, hb1, hb2⟩⟩, ⟨⟨hc0, hc1, hc2⟩,
    ⟨he0, he1, he2⟩⟩⟩⟩ := hη
  have h0 := hw 0; have h1 := hw 1; have h2 := hw 2; have h3 := hw 3
  simp only [Prod.norm_def, max_le_iff, Real.norm_eq_abs, abs_le]
  refine ⟨⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩, ⟨⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩,
    ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩, ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩,
    ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩⟩⟩ <;> linarith

/-- **Error on the box**: `sup_{|xᵢ| ≤ 1} |h_{θ₀⁽ᵖ⁾ + η}(x) - F_A(x)| ≤ Es β 4 · t³`. -/
theorem err_box {A : Matrix (Fin 2) (Fin 2) ℝ} {β : ℝ} (hβ : 0 ≤ β) (hA : ∀ i j, |A i j| ≤ β)
    (p : Fin 4) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {η : Raw16} (hη : η ∈ pBox p t)
    (x : Fin 2 → ℝ) (hx : ∀ i, |x i| ≤ 1) (k : Fin 2) :
    |net (η + basePos A p) x k - layer A x k| ≤ Es β 4 * t ^ 3 := by
  set B : ℕ → Matrix (Fin 2) (Fin 2) ℝ := fun q => if q = p.val then A else 0
  set D : ℕ → Matrix (Fin 2) (Fin 2) ℝ := fun q => weights η q
  have hB : ∀ q i j, |B q i j| ≤ β := by
    intro q i j; simp only [B]; split_ifs
    · exact hA i j
    · simpa using hβ
  have hB0 : ∀ q, q ≠ p.val → B q = 0 := fun q hq => by simp [B, hq]
  have hD : ∀ q < 4, ∀ i j, |D q i j| ≤ if q = p.val then t ^ 3 else t :=
    fun q hq i j => pBox_weights hη q hq i j
  have hnet : net (η + basePos A p) = prefixNet (fun q => B q + D q) 4 := by
    unfold net
    refine prefixNet_congr _ _ 4 fun q hq => ?_
    rw [weights_add, weights_basePos A p q hq, add_comm]
  have hbase : layer A x = prefixNet B 4 x := by
    rw [← net_basePos A p x]
    unfold net
    exact congrFun (prefixNet_congr _ _ 4 fun q hq => weights_basePos A p q hq) x
  rw [hnet, hbase]
  exact (traj hβ ht0 ht1 B D p.val hB hB0 hD hx 4 le_rfl).2.2 k

/-! ### The lower bound -/

/-- **O3. `c N⁻⁴ ≤ Z_{N,p+1}` at every position**, for every target `A`, every finite input
law with finite 162nd moments, and every prior/cutoff bounded below near the base point. -/
theorem Zpos_lower_N4 (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4) (φ χ : Raw16 → ENNReal) {φ₀ χ₀ : ℝ}
    (hφ₀ : 0 < φ₀) (hχ₀ : 0 < χ₀)
    (hφ : ∀ᶠ θ in 𝓝 (basePos A p), ENNReal.ofReal φ₀ ≤ φ θ)
    (hχ : ∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ENNReal.ofReal (c * N⁻¹ ^ 4) ≤ Zpos μ A φ χ p N := by
  obtain ⟨Λ, hΛ⟩ := popLossA_le_moments μ hmom A
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = |A 0 0| + |A 0 1| + |A 1 0| + |A 1 1| := ⟨_, rfl⟩
  have hβ : 0 ≤ β := by rw [hβdef]; positivity
  have hAβ : ∀ i j, |A i j| ≤ β := by
    intro i j; rw [hβdef]
    fin_cases i <;> fin_cases j <;> simp <;> linarith [abs_nonneg (A 0 0), abs_nonneg (A 0 1),
      abs_nonneg (A 1 0), abs_nonneg (A 1 1)]
  set E := Es β 4
  have hE : 0 ≤ E := Es_nonneg hβ 4
  obtain ⟨ε₁, hε₁, hφε⟩ := Metric.eventually_nhds_iff.mp hφ
  obtain ⟨ε₂, hε₂, hχε⟩ := Metric.eventually_nhds_iff.mp hχ
  set ε := min (min ε₁ ε₂) 1
  have hε : 0 < ε := lt_min (lt_min hε₁ hε₂) one_pos
  set Λ' := max Λ 0
  set c := Real.exp (-(Λ' * E ^ 2)) * φ₀ * χ₀ * 2 ^ 16
  refine ⟨c, by positivity, max 1 ((2 / ε) ^ 6), fun N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  -- `t = N^{-1/6}`
  set t := Real.exp (-(Real.log N / 6))
  have ht0 : 0 < t := Real.exp_pos _
  have ht6 : t ^ 6 = N⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_log (inv_pos.mpr hN0), Real.log_inv]; push_cast; ring_nf
  have ht1 : t ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have := Real.log_nonneg hN1; linarith
  have htε : t < ε := by
    by_contra hc
    push Not at hc
    have h6 : ε ^ 6 ≤ t ^ 6 := pow_le_pow_left₀ hε.le hc 6
    rw [ht6] at h6
    have h2 : (2 / ε) ^ 6 ≤ N := (le_max_right _ _).trans hN
    have : (2 / ε) ^ 6 * ε ^ 6 = 64 := by rw [← mul_pow, div_mul_cancel₀ _ hε.ne']; norm_num
    have hNε : N * ε ^ 6 ≤ 1 := by
      calc N * ε ^ 6 ≤ N * N⁻¹ := mul_le_mul_of_nonneg_left h6 hN0.le
        _ = 1 := mul_inv_cancel₀ hN0.ne'
    nlinarith [pow_pos hε 6]
  set b := basePos A p
  set F : Raw16 → ENNReal := fun θ =>
    ENNReal.ofReal (Real.exp (-(N * popLossA μ A θ))) * (φ θ * χ (θ - b))
  have hF : Zpos μ A φ χ p N = ∫⁻ η, F (η + b) := (lintegral_add_right_eq_self F b).symm
  set k0 := ENNReal.ofReal (Real.exp (-(Λ' * E ^ 2))) * (ENNReal.ofReal φ₀ * ENNReal.ofReal χ₀)
  have hpt : ∀ η ∈ pBox p t, k0 ≤ F (η + b) := by
    intro η hη
    have hη' : ‖η‖ ≤ t := pBox_norm ht0.le ht1 hη
    simp only [F, add_sub_cancel_right]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) (mul_le_mul' ?_ ?_)
    · have hK := hΛ (η + b) (E * t ^ 3) (by positivity)
        (fun x hx k => err_box hβ hAβ p ht0.le ht1 hη x hx k)
      have hK' : popLossA μ A (η + b) ≤ Λ' * (E * t ^ 3) ^ 2 :=
        hK.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
      have : N * (Λ' * (E * t ^ 3) ^ 2) = Λ' * E ^ 2 := by
        have : (t ^ 3) ^ 2 = N⁻¹ := by rw [← pow_mul]; exact ht6
        rw [mul_pow, this]; field_simp
      nlinarith
    · apply hφε
      rw [dist_eq_norm, add_sub_cancel_right]
      exact lt_of_le_of_lt hη' (htε.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
    · apply hχε
      rw [dist_zero_right]
      exact lt_of_le_of_lt hη' (htε.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  calc ENNReal.ofReal (c * N⁻¹ ^ 4)
      = k0 * ENNReal.ofReal (2 ^ 16 * t ^ 24) := by
        simp only [k0, c]
        rw [← ENNReal.ofReal_mul hφ₀.le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show t ^ 24 = (t ^ 6) ^ 4 by ring, ht6]; ring
    _ = k0 * volume (pBox p t) := by rw [volume_pBox p ht0.le]
    _ = ∫⁻ _ in pBox p t, k0 := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ η in pBox p t, F (η + b) := setLIntegral_mono' (measurableSet_pBox p t) hpt
    _ ≤ ∫⁻ η, F (η + b) := setLIntegral_le_lintegral _ _
    _ = Zpos μ A φ χ p N := hF.symm

/-! ### Theorem N as a named hypothesis, and the pairs at positions 2–4 -/

/-- **Theorem N, upper half of (N1), as a hypothesis**: at active positions two and three
(Lean `p = 1, 2`), `Z_{N,j} ≤ C N⁻⁴` for large `N`. Nothing stronger is assumed; the lower
half is `Zpos_lower_N4`. -/
def ThmN (μ : Measure (Fin 2 → ℝ)) (A : Matrix (Fin 2) (Fin 2) ℝ) (φ χ : Raw16 → ENNReal) :
    Prop :=
  ∀ p : Fin 4, (p = 1 ∨ p = 2) →
    ∃ C N₀ : ℝ, ∀ N, N₀ ≤ N → Zpos μ A φ χ p N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4)

/-- Turn `c N⁻⁴ ≤ Z ≤ C N⁻⁴` into `HasLaplacePair Z 4 1`. -/
theorem hasLaplacePair_41 {Zf : ℝ → ENNReal} {c C N₁ N₂ : ℝ} (hc : 0 < c)
    (hlo : ∀ N, N₁ ≤ N → ENNReal.ofReal (c * N⁻¹ ^ 4) ≤ Zf N)
    (hhi : ∀ N, N₂ ≤ N → Zf N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4)) : SLT.HasLaplacePair Zf 4 1 := by
  refine ⟨⟨c, hc, max N₁ 1, fun N hN => ?_⟩, ⟨C, max N₂ 1, fun N hN => ?_⟩⟩ <;>
  · have hN0 : 0 < N := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hN)
    simp only [Nat.sub_self, pow_zero, mul_one]
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, rpow_neg_natCast_eq hN0]
    first | exact hlo N ((le_max_left _ _).trans hN) | exact hhi N ((le_max_left _ _).trans hN)

/-- **Position four from the upper half of (K1) alone**: the lower half is now proved. -/
theorem position_four_pair {μ : Measure (Fin 2 → ℝ)} [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {A : Matrix (Fin 2) (Fin 2) ℝ} {φ χ : Raw16 → ENNReal} {φ₀ χ₀ : ℝ}
    (hφ₀ : 0 < φ₀) (hχ₀ : 0 < χ₀)
    (hφ : ∀ᶠ θ in 𝓝 (basePos A 3), ENNReal.ofReal φ₀ ≤ φ θ)
    (hχ : ∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) (hK : ThmKUpper μ A φ χ) :
    SLT.HasLaplacePair (Zpos μ A φ χ 3) 4 1 := by
  obtain ⟨c, hc, N₁, hlo⟩ := Zpos_lower_N4 μ hmom A 3 φ χ hφ₀ hχ₀ hφ hχ
  obtain ⟨C, N₂, hhi⟩ := hK
  exact hasLaplacePair_41 hc hlo hhi

/-- **Positions two and three from `ThmN`.** -/
theorem middle_position_pair {μ : Measure (Fin 2 → ℝ)} [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {A : Matrix (Fin 2) (Fin 2) ℝ} {φ χ : Raw16 → ENNReal} {φ₀ χ₀ : ℝ}
    (hφ₀ : 0 < φ₀) (hχ₀ : 0 < χ₀) (p : Fin 4) (hp : p = 1 ∨ p = 2)
    (hφ : ∀ᶠ θ in 𝓝 (basePos A p), ENNReal.ofReal φ₀ ≤ φ θ)
    (hχ : ∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) (hN : ThmN μ A φ χ) :
    SLT.HasLaplacePair (Zpos μ A φ χ p) 4 1 := by
  obtain ⟨c, hc, N₁, hlo⟩ := Zpos_lower_N4 μ hmom A p φ χ hφ₀ hχ₀ hφ hχ
  obtain ⟨C, N₂, hhi⟩ := hN p hp
  exact hasLaplacePair_41 hc hlo hhi

end VectorSLT
