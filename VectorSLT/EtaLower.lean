/-
Brief 04, X4: the uniform lower bound `Z_N(A_η) ≥ c N⁻⁴ (1 + 𝓛_η(N))⁴`, with `c`, `N₀`
independent of `η`.

Source: cubic-chaos `approx_shear_crossover.md` §3 (pinned `caccd6a`).

Proof, as in the paper: Proposition L′'s region, with
* the active box recentred at `ν ≈ (η - P₁)/α²` (base point `(1, η)`, Lemma X2's `c₂`);
* the error bound `err_bound_eta` (Lemma L′3 parts 1–2 with the bounds on `αν² - η²`,
  `ν³ - η³` and the difference argument for `Δ₀`), which needs `η² |A_k| ≤ 3√t` on each row;
* two row regions:
  - large `𝓛`: amplitude radius `a₁ ∈ [lo, hi]` with
    `hi = min(t^{1/10}, t^{1/6}(η² + t)^{-1/3}/2)` (the paper's `r₊`, with `|η|` replaced by the
    `η`-free-at-zero `(η² + t)^{1/2}`), and `lo = √(t^{1/6} hi)`; the row volume is
    `≥ c t log²(hi/t^{1/6})`, the paper's `cN⁻¹ ∫ log(1/δ) dr/r`;
  - small `𝓛`: the plain box (all six inactive entries in `[-t^{1/6}, t^{1/6}]`), volume `64 t`.

`t = 1/N` throughout. `𝓛_η(N) = log min(N, 1/|η|)`, and `𝓛₀(N) = log N` (`Leta`).
-/
import VectorSLT.EtaError
import VectorSLT.FullNetwork

namespace VectorSLT

open MeasureTheory Set Filter Topology

/-! ### The active box at base point `(1, η)` -/

/-- `α ∈ (1 - A)^{1/3} ± e/10`, then `ν ∈ (η - P₁)/α² ± e/10`. -/
def actBoxη (e η : ℝ) (w : Row) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Icc (cbrt (1 - momA (tri w.1)) - e / 10) (cbrt (1 - momA (tri w.1)) + e / 10) ∧
    z.2 ∈ Icc ((η - momP1 (tri w.1) (tri w.2)) / z.1 ^ 2 - e / 10)
      ((η - momP1 (tri w.1) (tri w.2)) / z.1 ^ 2 + e / 10)}

theorem measurableSet_actBoxη (e η : ℝ) (w : Row) : MeasurableSet (actBoxη e η w) := by
  unfold actBoxη
  simp only [mem_Icc, ofPred_and]
  refine ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)).inter
    ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)) <;> fun_prop

theorem volume_actBoxη (e η : ℝ) (w : Row) :
    volume (actBoxη e η w) = ENNReal.ofReal (e / 5) * ENNReal.ofReal (e / 5) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_actBoxη e η w)]
  set c := cbrt (1 - momA (tri w.1))
  have h : ∀ α : ℝ, volume (Prod.mk α ⁻¹' actBoxη e η w) =
      (Icc (c - e / 10) (c + e / 10)).indicator (fun _ => ENNReal.ofReal (e / 5)) α := by
    intro α
    by_cases hα : α ∈ Icc (c - e / 10) (c + e / 10)
    · rw [indicator_of_mem hα]
      have : Prod.mk α ⁻¹' actBoxη e η w =
          Icc ((η - momP1 (tri w.1) (tri w.2)) / α ^ 2 - e / 10)
            ((η - momP1 (tri w.1) (tri w.2)) / α ^ 2 + e / 10) := by
        ext ν; simp only [mem_preimage, actBoxη, mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨hα, h⟩⟩
      rw [this, Real.volume_Icc]; congr 1; ring
    · rw [indicator_of_notMem hα]
      have : Prod.mk α ⁻¹' actBoxη e η w = ∅ := by
        ext ν; simp only [mem_preimage, actBoxη, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hα h.1
      rw [this, measure_empty]
  simp_rw [h]
  rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc, mul_comm]
  congr 2; ring

/-- Active-row consequences of the η-box: `α ∈ [0.9, 1.1]`, `|c₃| ≤ e`, `|c₂| ≤ e`. -/
theorem act_bounds_eta {e ρ η : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 / 10) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ 1 / 10) {w : Row} (hw : ∀ i < 3, |tri w.1 i| ≤ ρ)
    {z : ℝ × ℝ} (hz : z ∈ actBoxη e η w) :
    (9 / 10 ≤ z.1 ∧ z.1 ≤ 11 / 10) ∧ |z.1 ^ 3 - 1 + momA (tri w.1)| ≤ e ∧
      |3 * z.1 ^ 2 * z.2 + 3 * momP1 (tri w.1) (tri w.2) - 3 * η| ≤ e := by
  have hA := momA_le hw
  have hρ3 : ρ ^ 3 ≤ 1 / 1000 := by
    have := pow_le_pow_left₀ hρ0 hρ 3; norm_num at this; linarith
  set A := momA (tri w.1)
  have hx1 : 95 / 100 ≤ 1 - A := by linarith [(abs_le.mp hA).2]
  have hx2 : 1 - A ≤ 105 / 100 := by linarith [(abs_le.mp hA).1]
  obtain ⟨c1, c2⟩ := cbrt_mem hx1 hx2
  obtain ⟨⟨hz1, hz2⟩, hz3, hz4⟩ := hz
  have hα : 9 / 10 ≤ z.1 ∧ z.1 ≤ 11 / 10 := ⟨by linarith, by linarith⟩
  refine ⟨hα, ?_, ?_⟩
  · have hc := cbrt_cube (show 0 ≤ 1 - A by linarith)
    have e1 : z.1 ^ 3 - 1 + A = z.1 ^ 3 - cbrt (1 - A) ^ 3 := by rw [hc]; ring
    rw [e1]
    have hm1 : |z.1| ≤ 11 / 10 := by rw [abs_of_pos (by linarith)]; exact hα.2
    have hm2 : |cbrt (1 - A)| ≤ 11 / 10 := by rw [abs_of_pos (by linarith)]; linarith
    refine (cube_diff_le hm1 hm2).trans ?_
    have : |z.1 - cbrt (1 - A)| ≤ e / 10 := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg (z.1 - cbrt (1 - A))]
  · have hα0 : z.1 ≠ 0 := by linarith
    have hα2 : 0 < z.1 ^ 2 := by positivity
    set P := momP1 (tri w.1) (tri w.2)
    have e1 : 3 * z.1 ^ 2 * z.2 + 3 * P - 3 * η =
        3 * z.1 ^ 2 * (z.2 - (η - P) / z.1 ^ 2) := by
      field_simp; ring
    rw [e1, abs_mul, abs_of_pos (by positivity)]
    have : |z.2 - (η - P) / z.1 ^ 2| ≤ e / 10 := by rw [abs_le]; constructor <;> linarith
    have h121 : z.1 ^ 2 ≤ 121 / 100 := by nlinarith
    nlinarith [abs_nonneg (z.2 - (η - P) / z.1 ^ 2)]

/-! ### The region `Ω` over a row set `S` -/

/-- `Ω` in (M2) coordinates: both inactive rows in `S`, each active row in its η-box with
`e = √t`. -/
def OmegaEta (S : Set Row) (t η : ℝ) : Set Raw16 :=
  {y | (y.2.1 ∈ S ∧ y.2.2 ∈ S) ∧ (y.1.1 ∈ actBoxη (√t) η y.2.1 ∧ y.1.2 ∈ actBoxη (√t) η y.2.2)}

theorem measurableSet_OmegaEta {S : Set Row} (hS : MeasurableSet S) (t η : ℝ) :
    MeasurableSet (OmegaEta S t η) := by
  unfold OmegaEta actBoxη
  simp only [mem_Icc, ofPred_and]
  refine ((measurable_snd.fst hS).inter (measurable_snd.snd hS)).inter ?_
  refine (((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)).inter
    ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_))).inter
    (((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)).inter
    ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_))) <;> fun_prop

theorem volume_OmegaEta {S : Set Row} (hS : MeasurableSet S) (t η : ℝ) :
    volume (OmegaEta S t η) = ENNReal.ofReal (√t / 5) ^ 4 * (volume S * volume S) := by
  rw [Measure.volume_eq_prod (α := (ℝ × ℝ) × (ℝ × ℝ)) (β := Row × Row),
    Measure.prod_apply_symm (measurableSet_OmegaEta hS t η)]
  have h : ∀ rr : Row × Row, volume ((fun a => (a, rr)) ⁻¹' OmegaEta S t η) =
      (S ×ˢ S).indicator (fun _ => ENNReal.ofReal (√t / 5) ^ 4) rr := by
    intro rr
    by_cases hr : rr ∈ S ×ˢ S
    · rw [indicator_of_mem hr]
      have : (fun a => (a, rr)) ⁻¹' OmegaEta S t η =
          actBoxη (√t) η rr.1 ×ˢ actBoxη (√t) η rr.2 := by
        ext a; simp only [mem_preimage, OmegaEta, mem_ofPred_eq, mem_prod]
        exact ⟨fun h => h.2, fun h => ⟨hr, h⟩⟩
      rw [this, Measure.volume_eq_prod, Measure.prod_prod, volume_actBoxη, volume_actBoxη]
      ring
    · rw [indicator_of_notMem hr]
      have : (fun a => (a, rr)) ⁻¹' OmegaEta S t η = ∅ := by
        ext a; simp only [mem_preimage, OmegaEta, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hr h.1
      rw [this, measure_empty]
  simp_rw [h]
  rw [lintegral_indicator_const (hS.prod hS), Measure.volume_eq_prod (α := Row) (β := Row),
    Measure.prod_prod]

/-! ### Row conditions and the pointwise bounds on `Ω` -/

/-- What `Ω`'s error bound needs from one inactive row: entries `≤ 4 t^{1/10}`, moments
`|Pⱼ| ≤ 3√t`, and the new X4 condition `η² |A| ≤ 3√t`. -/
def RowGood (t η : ℝ) (w : Row) : Prop :=
  (∀ i < 3, |tri w.1 i| ≤ 4 * t ^ ((1 : ℝ) / 10) ∧ |tri w.2 i| ≤ 4 * t ^ ((1 : ℝ) / 10)) ∧
    |momP1 (tri w.1) (tri w.2)| ≤ 3 * √t ∧ |momP2 (tri w.1) (tri w.2)| ≤ 3 * √t ∧
    |momP3 (tri w.2)| ≤ 3 * √t ∧ η ^ 2 * |momA (tri w.1)| ≤ 3 * √t

/-- The smallness conditions on `t = 1/N` used for X4 (they hold for large `N`). -/
def TSmallη (R t : ℝ) : Prop := TSmall R t ∧ t ≤ 1 / 900

/-- The constant of the X4 sup-norm bound. -/
noncomputable def CerrE (R : ℝ) : ℝ := 3 * 10 ^ 12 * 4099 * R ^ 15

/-- **Lemma L′3 for `A_η`, sup-norm form**, on `Ω` over any row set of good rows. -/
theorem omega_err_eta {R t η : ℝ} (hR : 1 ≤ R) (ht : TSmallη R t) (hη : |η| ≤ 1 / 10)
    {S : Set Row} (hS : ∀ w ∈ S, RowGood t η w) {θ : Raw16}
    (hθ : toM2 θ ∈ OmegaEta S t η) {x : Fin 2 → ℝ} (hx : ∀ i, |x i| ≤ R) (k : Fin 2) :
    |net θ x k - layer (Aeta η) x k| ≤ CerrE R * √t := by
  obtain ⟨ht0, ht1, hsq, -, hρs, hρ6⟩ := tsmall_facts hR ht.1
  have hρR := ht.1.2.2
  have hsq30 : √t ≤ 1 / 30 := by
    rw [show (1 / 30 : ℝ) = √(1 / 900) by
      rw [show (1 / 900 : ℝ) = (1 / 30) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt ht.2
  set ρ := 4 * t ^ ((1 : ℝ) / 10)
  have hρ0 : 0 ≤ ρ := by positivity
  set ε := 3 * √t
  have hε0 : 0 ≤ ε := by positivity
  have hε : ε ≤ 1 / 10 := by simp only [ε]; linarith
  set y := toM2 θ
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hθ
  obtain ⟨rb1, p11, p12, p13, hA1⟩ := hS _ h1
  obtain ⟨rb2, p21, p22, p23, hA2⟩ := hS _ h2
  obtain ⟨ab1, c31, c21⟩ := act_bounds_eta (Real.sqrt_nonneg t) hsq hρ0 (by linarith)
    (fun i hi => (rb1 i hi).1) h3
  obtain ⟨ab2, c32, c22⟩ := act_bounds_eta (Real.sqrt_nonneg t) hsq hρ0 (by linarith)
    (fun i hi => (rb2 i hi).1) h4
  have hsε : √t ≤ ε := by simp only [ε]; linarith [Real.sqrt_nonneg t]
  obtain ⟨hl0, hS0, hT0, hl, hS, hT, herr⟩ := net_recursion θ x
  have hs : |x 0 - x 1| ≤ 2 * R := by
    have := abs_sub (x 0) (x 1); linarith [hx 0, hx 1]
  have hb := err_bound_eta hR hε0 hε hρ0 hρR hη
    hs (hx 1) (actα y) (actν y) (inA y) (inB y)
    (fun i k => weights θ i k ⬝ᵥ prefixNet (weights θ) i x)
    (fun i => prefixNet (weights θ) (i + 1) x 0 - prefixNet (weights θ) (i + 1) x 1)
    (fun i => prefixNet (weights θ) (i + 1) x 1)
    (fun k => by fin_cases k; exacts [ab1, ab2])
    (fun k i hi => by fin_cases k; exacts [rb1 i hi, rb2 i hi])
    (fun k => by fin_cases k; exacts [p11, p21])
    (fun k => by fin_cases k; exacts [p12, p22])
    (fun k => by fin_cases k; exacts [p13, p23])
    (fun k => by fin_cases k; exacts [c31.trans hsε, c32.trans hsε])
    (fun k => by fin_cases k; exacts [c21.trans hsε, c22.trans hsε])
    (fun k => by fin_cases k; exacts [hA1, hA2])
    hl0 hS0 hT0 hl hS hT k
  have hlay : net θ x k - layer (Aeta η) x k =
      (net θ x k - layer A0 x k) + (x 0 - x 1) ^ 3 - ((x 0 - x 1) + η * x 1) ^ 3 := by
    rw [layer_Aeta, ← Aeta_zero, layer_Aeta]; ring
  rw [hlay, herr k]
  have e : ∀ u : ℝ, u - (x 0 - x 1) ^ 3 + (x 0 - x 1) ^ 3 - ((x 0 - x 1) + η * x 1) ^ 3 =
      u - ((x 0 - x 1) + η * x 1) ^ 3 := fun u => by ring
  rw [e]
  refine hb.trans ?_
  have : 0 ≤ R ^ 15 := by positivity
  have : ε + ρ ^ 6 ≤ 4099 * √t := by simp only [ε]; linarith
  calc 3 * 10 ^ 12 * R ^ 15 * (ε + ρ ^ 6) ≤ 3 * 10 ^ 12 * R ^ 15 * (4099 * √t) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = CerrE R * √t := by unfold CerrE; ring

set_option maxHeartbeats 800000 in
/-- `Ω` stays near the base point `basePos (A_η) 0`, uniformly in `|η| ≤ 1/10`. -/
theorem omega_near_eta {R t η : ℝ} (hR : 1 ≤ R) (ht : TSmallη R t) (hη : |η| ≤ 1 / 10)
    {S : Set Row} (hS : ∀ w ∈ S, RowGood t η w) {θ : Raw16}
    (hθ : toM2 θ ∈ OmegaEta S t η) :
    dist θ (basePos (Aeta η) 0) ≤ 30 * t ^ ((1 : ℝ) / 10) := by
  obtain ⟨ht0, ht1, hsq, hsqτ, hρs, -⟩ := tsmall_facts hR ht.1
  set τ := t ^ ((1 : ℝ) / 10)
  have hτ0 : 0 ≤ τ := by positivity
  set ρ := 4 * τ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ3 : ρ ^ 3 ≤ ρ := pow_le_of_le_one hρ0 (by linarith) (by norm_num)
  have hsq30 : √t ≤ 1 / 30 := by
    rw [show (1 / 30 : ℝ) = √(1 / 900) by
      rw [show (1 / 900 : ℝ) = (1 / 30) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt ht.2
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hθ
  obtain ⟨rb1, p11, -, -, -⟩ := hS _ h1
  obtain ⟨rb2, p21, -, -, -⟩ := hS _ h2
  have act : ∀ (w : Row) (z : ℝ × ℝ), (∀ i < 3, |tri w.1 i| ≤ ρ) →
      |momP1 (tri w.1) (tri w.2)| ≤ 3 * √t → z ∈ actBoxη (√t) η w →
      |z.1 - 1| ≤ 13 * τ ∧ |z.2 - η| ≤ 9 * τ := by
    intro w z hw hP hz
    obtain ⟨hα, hc3, hc2⟩ := act_bounds_eta (Real.sqrt_nonneg t) hsq hρ0 (by linarith) hw hz
    have hA := momA_le hw
    have h1 := abs_sub_one_le_cube (show 0 ≤ z.1 by linarith [hα.1])
    have := abs_sub (z.1 ^ 3 - 1 + momA (tri w.1)) (momA (tri w.1))
    rw [show z.1 ^ 3 - 1 + momA (tri w.1) - momA (tri w.1) = z.1 ^ 3 - 1 by ring] at this
    have ha1 : |z.1 - 1| ≤ 13 * τ := by linarith
    refine ⟨ha1, ?_⟩
    -- |α²ν - η| ≤ (4/3)·3√t, then ν - η = (α²ν - η)/α² + η(1 - α²)/α²
    set P := momP1 (tri w.1) (tri w.2)
    have hu : |z.1 ^ 2 * z.2 - η| ≤ 4 * √t := by
      have e : 3 * (z.1 ^ 2 * z.2 - η) = (3 * z.1 ^ 2 * z.2 + 3 * P - 3 * η) - 3 * P := by ring
      have h2 : |3 * (z.1 ^ 2 * z.2 - η)| ≤ √t + 3 * (3 * √t) := by
        rw [e]; refine (abs_sub _ _).trans ?_
        rw [abs_mul 3, abs_of_pos (by norm_num : (0:ℝ) < 3)]; linarith
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)] at h2; linarith [Real.sqrt_nonneg t]
    have hα2 : 81 / 100 ≤ z.1 ^ 2 := by nlinarith [hα.1]
    have h1a2 : |1 - z.1 ^ 2| ≤ 21 / 10 * (13 * τ) := by
      have e : 1 - z.1 ^ 2 = -(z.1 - 1) * (z.1 + 1) := by ring
      rw [e, abs_mul, abs_neg, abs_of_pos (show 0 < z.1 + 1 by linarith [hα.1])]
      have := hα.2
      nlinarith [abs_nonneg (z.1 - 1)]
    have hnum : z.1 ^ 2 * (z.2 - η) = (z.1 ^ 2 * z.2 - η) + η * (1 - z.1 ^ 2) := by ring
    have hb : |z.1 ^ 2 * (z.2 - η)| ≤ 4 * √t + 1 / 10 * (21 / 10 * (13 * τ)) := by
      rw [hnum]; refine (abs_add_le _ _).trans ?_
      rw [abs_mul η]
      exact add_le_add hu (mul_le_mul hη h1a2 (abs_nonneg _) (by norm_num))
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)] at hb
    have := mul_le_mul_of_nonneg_right hα2 (abs_nonneg (z.2 - η))
    linarith
  obtain ⟨a1, n1⟩ := act _ _ (fun i hi => (rb1 i hi).1) p11 h3
  obtain ⟨a2, n2⟩ := act _ _ (fun i hi => (rb2 i hi).1) p21 h4
  have r1 := fun i hi => rb1 i hi
  have r2 := fun i hi => rb2 i hi
  obtain ⟨r10, r10'⟩ := r1 0 (by norm_num)
  obtain ⟨r11, r11'⟩ := r1 1 (by norm_num)
  obtain ⟨r12, r12'⟩ := r1 2 (by norm_num)
  obtain ⟨r20, r20'⟩ := r2 0 (by norm_num)
  obtain ⟨r21, r21'⟩ := r2 1 (by norm_num)
  obtain ⟨r22, r22'⟩ := r2 2 (by norm_num)
  simp only [toM2, tri] at a1 n1 a2 n2 r10 r10' r11 r11' r12 r12' r20 r20' r21 r21' r22 r22'
  rw [abs_le] at a1 n1 a2 n2 r10 r10' r11 r11' r12 r12' r20 r20' r21 r21' r22 r22'
  have hb : basePos (Aeta η) 0 = (((1, -1 + η), (1, -1 + η)), ((0, 0), (0, 0))) := by
    simp [basePos, ofEnt, Aeta]
  rw [hb]
  simp only [Prod.dist_eq, Real.dist_eq, max_le_iff]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at *
  and_intros <;> rw [abs_le] <;> constructor <;> linarith

/-! ### The radius-capped row region (large `𝓛`) -/

/-- Amplitudes with radius `a₁ ∈ [lo, hi]` (ratios as in `ampSet`). -/
def ampSetG (lo hi : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {a | a.1 ∈ Icc lo hi ∧
    a.2.1 ∈ Icc (a.1 * (99 / 100)) (a.1 * (101 / 100)) ∧
    a.2.2 ∈ Icc (a.1 * (-101 / 100)) (a.1 * (-99 / 100))}

/-- `lowerRegion` with the radius range `[lo, hi]`. -/
def lowerRegionG (t lo hi : ℝ) : Set ((ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)) :=
  {x | x.1 ∈ ampSetG lo hi ∧ x.2 ∈ bFibre x.1.1 (hfun t x.1.1)
    (rho (x.1.2.1 / x.1.1) (x.1.2.2 / x.1.1)) ((x.1.2.1 / x.1.1) ^ 2) ((x.1.2.2 / x.1.1) ^ 2)}

theorem measurableSet_ampSetG (lo hi : ℝ) : MeasurableSet (ampSetG lo hi) := by
  unfold ampSetG
  simp only [mem_Icc, ofPred_and]
  refine ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)).inter
    (((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)).inter
      ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_))) <;> fun_prop

theorem measurableSet_lowerRegionG (t lo hi : ℝ) : MeasurableSet (lowerRegionG t lo hi) := by
  have hA := measurableSet_ampSetG lo hi
  unfold lowerRegionG bFibre
  simp only [mem_Icc, ofPred_and]
  refine (measurable_fst hA).inter ?_
  refine ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)).inter
    (((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)).inter
      ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_))) <;> fun_prop

/-- For `t^{1/6} ≤ a₁ ≤ t^{1/10}`: `H ≤ 1` and `log(1/H) ≥ (log a₁ - (log t)/6)/2`. -/
theorem hfun_factsG {t a1 : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (ha : t ^ ((1 : ℝ) / 6) ≤ a1) (ha' : a1 ≤ t ^ ((1 : ℝ) / 10)) :
    0 < a1 ∧ a1 ≤ 1 ∧ hfun t a1 ≤ 1 ∧
      (Real.log a1 - Real.log t / 6) / 2 ≤ Real.log (1 / hfun t a1) := by
  have ha0 : 0 < a1 := lt_of_lt_of_le (by positivity) ha
  have ha1 : a1 ≤ 1 := ha'.trans (Real.rpow_le_one ht0.le ht1 (by norm_num))
  have hH0 := hfun_pos ht0 ha0
  have h12 := hfun_pow12 ht0 ha0
  have h6 : t ≤ a1 ^ 6 := by
    have := pow_le_pow_left₀ (by positivity) ha 6
    rwa [← Real.rpow_natCast, ← Real.rpow_mul ht0.le, show (1 : ℝ) / 6 * (6 : ℕ) = 1 by norm_num,
      Real.rpow_one] at this
  refine ⟨ha0, ha1, ?_, ?_⟩
  · have : hfun t a1 ^ 12 ≤ 1 := by
      rw [h12, div_le_one (by positivity)]; nlinarith [pow_pos ha0 6]
    exact (pow_le_one_iff_of_nonneg hH0.le (by norm_num)).mp this
  · have hlogH : Real.log (1 / hfun t a1) = -(1 / 12) * Real.log (t / (5000 * a1 ^ 6)) := by
      rw [← h12, Real.log_pow, one_div, Real.log_inv]; push_cast; ring
    have hl : Real.log (t / (5000 * a1 ^ 6)) =
        Real.log t - Real.log 5000 - 6 * Real.log a1 := by
      rw [Real.log_div ht0.ne' (by positivity), Real.log_mul (by norm_num) (by positivity),
        Real.log_pow]; push_cast; ring
    have h5000 : 0 ≤ Real.log 5000 := Real.log_nonneg (by norm_num)
    rw [hlogH, hl]
    nlinarith

/-- `lowerRegion_sub` for the generalized radius range: for `0 < t ≤ min 1 ((ε/4)^10)`, every point
of `lowerRegionG t lo hi` has all six coordinates in `[-ε, ε]` and `‖P(a,b)‖² ≤ t`. -/
theorem lowerRegionG_sub {ε t lo hi : ℝ} (hε : 0 < ε) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (htε : t ≤ (ε / 4) ^ 10) (hlo : t ^ ((1 : ℝ) / 6) ≤ lo) (hhi : hi ≤ t ^ ((1 : ℝ) / 10))
    (f g : Fin 3 → ℝ)
    (hx : ((f 0, f 1, f 2), (g 0, g 1, g 2)) ∈ lowerRegionG t lo hi) :
    (∀ i, |f i| ≤ ε) ∧ (∀ i, |g i| ≤ ε) ∧ rowPsq f g ≤ t := by
  obtain ⟨⟨hr, ha2, ha3⟩, hb3, hb2, hb1⟩ := hx
  simp only at hr ha2 ha3 hb3 hb2 hb1
  obtain ⟨ha0, -, hH1, -⟩ := hfun_factsG ht0 ht1 (hlo.trans hr.1) (hr.2.trans hhi)
  set a1 := f 0
  set q := f 1 / a1
  set p := f 2 / a1
  set H := hfun t a1
  set ρ := rho q p
  have hH0 : 0 < H := hfun_pos ht0 ha0
  -- amplitude box
  have hbox : InAmpBox q p := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [le_div_iff₀ ha0]; linarith [ha2.1]
    · rw [div_le_iff₀ ha0]; linarith [ha2.2]
    · rw [le_div_iff₀ ha0]; linarith [ha3.1]
    · rw [div_le_iff₀ ha0]; linarith [ha3.2]
  -- scaled coordinates
  set c := g 2 / a1
  set v := (g 1 - ρ * g 2) / a1
  set z := (g 0 + q ^ 2 * g 1 + p ^ 2 * g 2) / a1
  have hb30 : 0 < g 2 := lt_of_lt_of_le (by positivity) hb3.1
  have hc1 : H ^ 3 ≤ c := by rw [le_div_iff₀ ha0]; linarith [hb3.1]
  have hc2 : c ≤ H ^ 2 := by rw [div_le_iff₀ ha0]; linarith [hb3.2]
  have hv1 : H ^ 6 / (2 * c) ≤ v := by
    have e : H ^ 6 / (2 * c) = a1 ^ 2 * H ^ 6 / (2 * g 2) / a1 := by
      simp only [c]; field_simp
    rw [e]; exact div_le_div_of_nonneg_right (by linarith [hb2.1]) ha0.le
  have hv2 : v ≤ H ^ 6 / c := by
    have e : H ^ 6 / c = a1 ^ 2 * H ^ 6 / g 2 / a1 := by
      simp only [c]; field_simp
    rw [e]; exact div_le_div_of_nonneg_right (by linarith [hb2.2]) ha0.le
  have hz : |z| ≤ H ^ 6 := by
    simp only [z]
    rw [abs_div, abs_of_pos ha0, div_le_iff₀ ha0, abs_le]
    constructor <;> nlinarith [hb1.1, hb1.2]
  obtain ⟨hP, hβ1, hβ2, hβ3⟩ := scaled_bound hbox hH0 hH1 hc1 hc2 hv1 hv2 hz
  have e2 : v + ρ * c = g 1 / a1 := by simp only [v, c]; field_simp; ring
  have e1 : z - q ^ 2 * (v + ρ * c) - p ^ 2 * c = g 0 / a1 := by
    rw [e2]; simp only [z, c]; field_simp; ring
  rw [e1] at hβ1
  rw [e1, e2] at hP
  replace hβ2 : |g 1 / a1| ≤ 4 := by rw [← e2]; exact hβ2
  have hf : f = fun i => a1 * (![1, q, p] : Fin 3 → ℝ) i := by
    have := ha0.ne'
    funext i; fin_cases i <;> simp [q, p, a1, this, mul_div_cancel₀]
  have hg : g = fun i => a1 * (![g 0 / a1, g 1 / a1, c] : Fin 3 → ℝ) i := by
    have := ha0.ne'
    funext i; fin_cases i <;> simp [c, a1, this, mul_div_cancel₀]
  -- the small radius
  have hr10 : a1 ≤ ε / 4 := by
    refine (hr.2.trans hhi).trans ?_
    calc t ^ ((1 : ℝ) / 10) ≤ ((ε / 4) ^ 10) ^ ((1 : ℝ) / 10) :=
          Real.rpow_le_rpow ht0.le htε (by norm_num)
      _ = ε / 4 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro i; fin_cases i
    · simp only [Fin.zero_eta]; rw [abs_of_pos ha0]; linarith
    · show |f 1| ≤ ε
      rw [abs_le]; constructor <;> linarith [ha2.1, ha2.2]
    · show |f 2| ≤ ε
      rw [abs_le]; constructor <;> linarith [ha3.1, ha3.2]
  · intro i
    have key : ∀ y : ℝ, |y / a1| ≤ 4 → |y| ≤ ε := by
      intro y hy
      rw [abs_div, abs_of_pos ha0, div_le_iff₀ ha0] at hy; linarith
    fin_cases i
    · exact key _ hβ1
    · exact key _ hβ2
    · exact key _ hβ3
  · rw [hf, hg, rowPsq_smul]
    calc a1 ^ 6 * rowPsq ![1, q, p] ![g 0 / a1, g 1 / a1, c] ≤ a1 ^ 6 * (5000 * H ^ 12) :=
          mul_le_mul_of_nonneg_left hP (by positivity)
      _ = t := by rw [hfun_pow12 ht0 ha0]; field_simp

/-- **Volume of the generalized lower region**: with `D = log lo - (log t)/6 ≥ 0`, at least
`t D log(hi/lo) / (2.5·10⁷)`. This is the paper's `cN⁻¹ ∫ log(1/δ) dr/r` over the radial range,
with `log(1/δ)` bounded below by its value at the lower end `lo`. -/
theorem volume_lowerRegionG {t lo hi : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hlo : t ^ ((1 : ℝ) / 6) ≤ lo) (hlh : lo ≤ hi) (hhi : hi ≤ t ^ ((1 : ℝ) / 10)) :
    ENNReal.ofReal (t * (Real.log lo - Real.log t / 6) * Real.log (hi / lo) / 25000000) ≤
      volume (lowerRegionG t lo hi) := by
  set L := Real.log lo - Real.log t / 6
  have hlo0 : 0 < lo := lt_of_lt_of_le (by positivity) hlo
  have hL : 0 ≤ L := by
    have := Real.log_le_log (by positivity) hlo
    rw [Real.log_rpow ht0] at this; simp only [L]; linarith
  set F : ℝ × ℝ × ℝ → ENNReal := fun a => ENNReal.ofReal (t * L / 10000 / a.1 ^ 3)
  -- fibrewise lower bound
  have hfib : ∀ a : ℝ × ℝ × ℝ, (ampSetG lo hi).indicator F a ≤
      volume (Prod.mk a ⁻¹' lowerRegionG t lo hi) := by
    intro a
    by_cases ha : a ∈ ampSetG lo hi
    · rw [indicator_of_mem ha]
      obtain ⟨ha0, -, hH1, hlog⟩ := hfun_factsG ht0 ht1 (hlo.trans ha.1.1) (ha.1.2.trans hhi)
      have hlog' : L / 2 ≤ Real.log (1 / hfun t a.1) := by
        have := Real.log_le_log hlo0 ha.1.1
        simp only [L]; linarith
      have : Prod.mk a ⁻¹' lowerRegionG t lo hi = bFibre a.1 (hfun t a.1)
          (rho (a.2.1 / a.1) (a.2.2 / a.1)) ((a.2.1 / a.1) ^ 2) ((a.2.2 / a.1) ^ 2) := by
        ext b; simp only [mem_preimage, lowerRegionG, mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
      rw [this, volume_bFibre _ _ _ _ _ ha0 (hfun_pos ht0 ha0) hH1]
      apply ENNReal.ofReal_le_ofReal
      have h12 := hfun_pow12 ht0 ha0
      have e : a.1 ^ 3 * hfun t a.1 ^ 12 = t / 5000 / a.1 ^ 3 := by
        rw [h12]; field_simp
      rw [e]
      calc t * L / 10000 / a.1 ^ 3 = t / 5000 / a.1 ^ 3 * (L / 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog' (by positivity)
    · rw [indicator_of_notMem ha]; exact bot_le
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_lowerRegionG t lo hi)]
  refine le_trans ?_ (lintegral_mono hfib)
  -- integrate the indicator over the amplitudes
  rw [Measure.volume_eq_prod, lintegral_prod _
    ((Measurable.indicator (by fun_prop) (measurableSet_ampSetG lo hi)).aemeasurable)]
  set I := Icc lo hi
  have hin : ∀ a1 : ℝ, I.indicator (fun a1 => ENNReal.ofReal (t * L / 25000000 / (a1 - 0))) a1
      ≤ ∫⁻ y, (ampSetG lo hi).indicator F (a1, y) := by
    intro a1
    by_cases h : a1 ∈ I
    · rw [indicator_of_mem h]
      have ha0 : 0 < a1 := lt_of_lt_of_le hlo0 h.1
      have hset : ∀ y : ℝ × ℝ, (ampSetG lo hi).indicator F (a1, y) =
          (Icc (a1 * (99 / 100)) (a1 * (101 / 100)) ×ˢ
            Icc (a1 * (-101 / 100)) (a1 * (-99 / 100))).indicator
            (fun _ => ENNReal.ofReal (t * L / 10000 / a1 ^ 3)) y := by
        intro y
        by_cases hy : y ∈ Icc (a1 * (99 / 100)) (a1 * (101 / 100)) ×ˢ
            Icc (a1 * (-101 / 100)) (a1 * (-99 / 100))
        · rw [indicator_of_mem hy, indicator_of_mem (show (a1, y) ∈ ampSetG lo hi from ⟨h, hy.1, hy.2⟩)]
        · rw [indicator_of_notMem hy, indicator_of_notMem (fun hh => hy ⟨hh.2.1, hh.2.2⟩)]
      simp_rw [hset]
      rw [lintegral_indicator_const (measurableSet_Icc.prod measurableSet_Icc),
        Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
        ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by positivity)]
      apply le_of_eq; congr 1
      field_simp; ring
    · rw [indicator_of_notMem h]; exact bot_le
  refine le_trans ?_ (lintegral_mono hin)
  rw [lintegral_indicator measurableSet_Icc,
    lintegral_Icc_div_sub _ 0 _ _ (by positivity) (by linarith) hlh]
  apply ENNReal.ofReal_le_ofReal
  rw [sub_zero, sub_zero]; apply le_of_eq; ring

/-! ### Good rows: the radius-capped region and the plain box -/

theorem rpow_sixth_cube {t : ℝ} (ht : 0 ≤ t) : (t ^ ((1 : ℝ) / 6)) ^ 3 = √t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht, Real.sqrt_eq_rpow]; norm_num

theorem sixth_le_tenth {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t ^ ((1 : ℝ) / 6) ≤ t ^ ((1 : ℝ) / 10) :=
  Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by norm_num)

/-- Rows of the radius-capped region are good, once `4 η² hi³ ≤ 3√t`. -/
theorem rowGood_G {t η lo hi : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hlo : t ^ ((1 : ℝ) / 6) ≤ lo) (hhi : hi ≤ t ^ ((1 : ℝ) / 10))
    (hηhi : η ^ 2 * (4 * hi ^ 3) ≤ 3 * √t) {w : Row} (hw : w ∈ lowerRegionG t lo hi) :
    RowGood t η w := by
  set f : Fin 3 → ℝ := ![w.1.1, w.1.2.1, w.1.2.2]
  set g : Fin 3 → ℝ := ![w.2.1, w.2.2.1, w.2.2.2]
  have hε : 0 < 4 * t ^ ((1 : ℝ) / 10) := by positivity
  have htε : t ≤ (4 * t ^ ((1 : ℝ) / 10) / 4) ^ 10 := by
    rw [mul_div_cancel_left₀ _ (by norm_num : (4:ℝ) ≠ 0), ← Real.rpow_natCast,
      ← Real.rpow_mul ht0.le]; norm_num
  obtain ⟨hf, hg, hP⟩ := lowerRegionG_sub hε ht0 ht1 htε hlo hhi f g hw
  have hsplit : rowPsq f g = momP1 (tri w.1) (tri w.2) ^ 2 + momP2 (tri w.1) (tri w.2) ^ 2 +
      momP3 (tri w.2) ^ 2 := by
    simp [rowPsq, rowP, Fin.sum_univ_three, momP1, momP2, momP3, tri, f, g]
  rw [hsplit] at hP
  have hsq : 0 ≤ √t := Real.sqrt_nonneg t
  -- amplitude bound for `A`
  obtain ⟨⟨hr1, hr2⟩, ha2, ha3⟩ := hw.1
  have hlo0 : 0 < lo := lt_of_lt_of_le (by positivity) hlo
  have ha0 : 0 < w.1.1 := lt_of_lt_of_le hlo0 hr1
  have hamp : ∀ i < 3, |tri w.1 i| ≤ 101 / 100 * hi := by
    intro i hi3
    interval_cases i <;> simp only [tri] <;> rw [abs_le] <;> constructor <;>
      nlinarith [ha2.1, ha2.2, ha3.1, ha3.2]
  have hA := momA_le hamp
  have hhi0 : 0 ≤ hi := le_trans hlo0.le (hr1.trans hr2)
  have hA4 : |momA (tri w.1)| ≤ 4 * hi ^ 3 := by
    have : 3 * (101 / 100 * hi) ^ 3 ≤ 4 * hi ^ 3 := by nlinarith [pow_nonneg hhi0 3]
    linarith
  refine ⟨fun i hi3 => ?_, ?_, ?_, ?_, ?_⟩
  · interval_cases i
    · exact ⟨hf 0, hg 0⟩
    · exact ⟨hf 1, hg 1⟩
    · exact ⟨hf 2, hg 2⟩
  · have := sq_nonneg (momP2 (tri w.1) (tri w.2))
    have := sq_nonneg (momP3 (tri w.2))
    have := Real.abs_le_sqrt (show momP1 (tri w.1) (tri w.2) ^ 2 ≤ t by linarith)
    linarith
  · have := sq_nonneg (momP1 (tri w.1) (tri w.2))
    have := sq_nonneg (momP3 (tri w.2))
    have := Real.abs_le_sqrt (show momP2 (tri w.1) (tri w.2) ^ 2 ≤ t by linarith)
    linarith
  · have := sq_nonneg (momP1 (tri w.1) (tri w.2))
    have := sq_nonneg (momP2 (tri w.1) (tri w.2))
    have := Real.abs_le_sqrt (show momP3 (tri w.2) ^ 2 ≤ t by linarith)
    linarith
  · exact (mul_le_mul_of_nonneg_left hA4 (sq_nonneg η)).trans hηhi

/-- The plain box: all six inactive entries of a row in `[-ρ, ρ]`. -/
def cubeRow (ρ : ℝ) : Set Row :=
  (Icc (-ρ) ρ ×ˢ (Icc (-ρ) ρ ×ˢ Icc (-ρ) ρ)) ×ˢ (Icc (-ρ) ρ ×ˢ (Icc (-ρ) ρ ×ˢ Icc (-ρ) ρ))

theorem measurableSet_cubeRow (ρ : ℝ) : MeasurableSet (cubeRow ρ) := by
  unfold cubeRow
  exact (measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)).prod
    (measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc))

theorem volume_cubeRow (ρ : ℝ) : volume (cubeRow ρ) = ENNReal.ofReal (2 * ρ) ^ 6 := by
  unfold cubeRow
  have h2 : volume (Icc (-ρ) ρ ×ˢ Icc (-ρ) ρ) = ENNReal.ofReal (2 * ρ) ^ 2 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, show ρ - -ρ = 2 * ρ by ring]
    ring
  have h3 : volume (Icc (-ρ) ρ ×ˢ (Icc (-ρ) ρ ×ˢ Icc (-ρ) ρ)) = ENNReal.ofReal (2 * ρ) ^ 3 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, h2, Real.volume_Icc,
      show ρ - -ρ = 2 * ρ by ring]
    ring
  rw [Measure.volume_eq_prod, Measure.prod_prod, h3]; ring

theorem momP_cube {a b : ℕ → ℝ} {ρ : ℝ} (ha : ∀ i < 3, |a i| ≤ ρ) (hb : ∀ i < 3, |b i| ≤ ρ) :
    |momP1 a b| ≤ 3 * ρ ^ 3 ∧ |momP2 a b| ≤ 3 * ρ ^ 3 ∧ |momP3 b| ≤ 3 * ρ ^ 3 := by
  have t21 : ∀ i < 3, |a i ^ 2 * b i| ≤ ρ ^ 3 := fun i h => by
    rw [abs_mul, abs_pow, pow_succ]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (ha i h) 2) (hb i h) (abs_nonneg _)
      (sq_nonneg ρ)
  have t12 : ∀ i < 3, |a i * b i ^ 2| ≤ ρ ^ 3 := fun i h => by
    rw [abs_mul, abs_pow, show ρ ^ 3 = ρ * ρ ^ 2 by ring]
    exact mul_le_mul (ha i h) (pow_le_pow_left₀ (abs_nonneg _) (hb i h) 2) (by positivity)
      ((abs_nonneg _).trans (ha i h))
  have t03 : ∀ i < 3, |b i ^ 3| ≤ ρ ^ 3 := fun i h => abs_cube_le (hb i h)
  unfold momP1 momP2 momP3
  refine ⟨?_, ?_, ?_⟩
  · have := abs_add3_le (a 0 ^ 2 * b 0) (a 1 ^ 2 * b 1) (a 2 ^ 2 * b 2)
    linarith [t21 0 (by norm_num), t21 1 (by norm_num), t21 2 (by norm_num)]
  · have := abs_add3_le (a 0 * b 0 ^ 2) (a 1 * b 1 ^ 2) (a 2 * b 2 ^ 2)
    linarith [t12 0 (by norm_num), t12 1 (by norm_num), t12 2 (by norm_num)]
  · have := abs_add3_le (b 0 ^ 3) (b 1 ^ 3) (b 2 ^ 3)
    linarith [t03 0 (by norm_num), t03 1 (by norm_num), t03 2 (by norm_num)]

/-- Rows of the plain box of side `t^{1/6}` are good (for `|η| ≤ 1`). -/
theorem rowGood_cube {t η : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hη : |η| ≤ 1) {w : Row}
    (hw : w ∈ cubeRow (t ^ ((1 : ℝ) / 6))) : RowGood t η w := by
  set ρ := t ^ ((1 : ℝ) / 6)
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ3 : ρ ^ 3 = √t := rpow_sixth_cube ht0.le
  have hρτ : ρ ≤ 4 * t ^ ((1 : ℝ) / 10) := by
    have := sixth_le_tenth ht0 ht1; have : 0 ≤ t ^ ((1 : ℝ) / 10) := by positivity
    simp only [ρ]; linarith
  obtain ⟨⟨h0, h1, h2⟩, h3, h4, h5⟩ := hw
  have ha : ∀ i < 3, |tri w.1 i| ≤ ρ := by
    intro i hi; interval_cases i <;> simp only [tri] <;> rw [abs_le] <;>
      first | exact ⟨h0.1, h0.2⟩ | exact ⟨h1.1, h1.2⟩ | exact ⟨h2.1, h2.2⟩
  have hb : ∀ i < 3, |tri w.2 i| ≤ ρ := by
    intro i hi; interval_cases i <;> simp only [tri] <;> rw [abs_le] <;>
      first | exact ⟨h3.1, h3.2⟩ | exact ⟨h4.1, h4.2⟩ | exact ⟨h5.1, h5.2⟩
  obtain ⟨p1, p2, p3⟩ := momP_cube ha hb
  have hA := momA_le ha
  rw [hρ3] at p1 p2 p3 hA
  have hη2 : η ^ 2 ≤ 1 := by
    have := sq_le_sq' (abs_le.mp hη).1 (abs_le.mp hη).2; linarith
  refine ⟨fun i hi => ⟨(ha i hi).trans hρτ, (hb i hi).trans hρτ⟩, p1, p2, p3, ?_⟩
  calc η ^ 2 * |momA (tri w.1)| ≤ 1 * (3 * √t) :=
        mul_le_mul hη2 hA (abs_nonneg _) (by norm_num)
    _ = 3 * √t := one_mul _

/-! ### The Laplace lower bound over `Ω(S)` -/

/-- **The X4 Laplace step.** For every row set `S` of good rows with volume `≥ v`, the
localized integral is `≥ e^{-Λ C²} π₀ t² v² / 625`. Every constant here is independent of
`η` (`|η| ≤ 1/10`); the prior need only be `≥ π₀` within `r₀` of the base point `(1, η)`. -/
theorem lower_of_region {R Λ π₀ r₀ t N η v : ℝ} (hR : 1 ≤ R) (ht : TSmallη R t)
    (hNt : N * t = 1) (hN0 : 0 < N) (hη : |η| ≤ 1 / 10) (hr : 30 * t ^ ((1 : ℝ) / 10) < r₀)
    {S : Set Row} (hSm : MeasurableSet S) (hS : ∀ w ∈ S, RowGood t η w)
    (hv0 : 0 ≤ v) (hv : ENNReal.ofReal v ≤ volume S)
    (K : Raw16 → ℝ)
    (hK : ∀ θ M, 0 ≤ M → (∀ x : Fin 2 → ℝ, (∀ i, |x i| ≤ R) →
      ∀ k, |net θ x k - layer (Aeta η) x k| ≤ M) → K θ ≤ Λ * M ^ 2)
    (π : Raw16 → ENNReal)
    (hπ : ∀ θ, dist θ (basePos (Aeta η) 0) < r₀ → ENNReal.ofReal π₀ ≤ π θ) (hπ₀ : 0 < π₀) :
    ENNReal.ofReal (Real.exp (-(Λ * CerrE R ^ 2)) * π₀ * t ^ 2 * v ^ 2 / 625) ≤
      ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * K θ))) * π θ := by
  set E := Real.exp (-(Λ * CerrE R ^ 2))
  have ht0 : 0 < t := ht.1.1
  set Ω := toM2 ⁻¹' OmegaEta S t η
  have hΩm : MeasurableSet Ω := measurable_toM2 (measurableSet_OmegaEta hSm t η)
  have hpt : ∀ θ ∈ Ω, ENNReal.ofReal E * ENNReal.ofReal π₀ ≤
      ENNReal.ofReal (Real.exp (-(N * K θ))) * π θ := by
    intro θ hθ
    apply mul_le_mul'
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hKθ := hK θ (CerrE R * √t) (by unfold CerrE; positivity)
        (fun x hx k => omega_err_eta hR ht hη hS hθ hx k)
      have e : Λ * (CerrE R * √t) ^ 2 = Λ * CerrE R ^ 2 * t := by
        rw [mul_pow, Real.sq_sqrt ht0.le]; ring
      rw [e] at hKθ
      have : N * K θ ≤ Λ * CerrE R ^ 2 := by
        calc N * K θ ≤ N * (Λ * CerrE R ^ 2 * t) := mul_le_mul_of_nonneg_left hKθ hN0.le
          _ = Λ * CerrE R ^ 2 * (N * t) := by ring
          _ = Λ * CerrE R ^ 2 := by rw [hNt, mul_one]
      linarith
    · exact hπ θ (lt_of_le_of_lt (omega_near_eta hR ht hη hS hθ) hr)
  have hvol : volume Ω = volume (OmegaEta S t η) :=
    measurePreserving_toM2.measure_preimage (measurableSet_OmegaEta hSm t η).nullMeasurableSet
  calc ENNReal.ofReal (E * π₀ * t ^ 2 * v ^ 2 / 625)
      = ENNReal.ofReal E * ENNReal.ofReal π₀ * (ENNReal.ofReal (√t / 5) ^ 4 *
          (ENNReal.ofReal v * ENNReal.ofReal v)) := by
        rw [← ENNReal.ofReal_mul hv0, ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [div_pow, show √t ^ 4 = (√t ^ 2) ^ 2 by ring, Real.sq_sqrt ht0.le]; ring
    _ ≤ ENNReal.ofReal E * ENNReal.ofReal π₀ * volume (OmegaEta S t η) := by
        rw [volume_OmegaEta hSm]; gcongr
    _ = ∫⁻ θ in Ω, ENNReal.ofReal E * ENNReal.ofReal π₀ := by
        rw [setLIntegral_const, hvol, mul_comm]
    _ ≤ ∫⁻ θ in Ω, ENNReal.ofReal (Real.exp (-(N * K θ))) * π θ := setLIntegral_mono' hΩm hpt
    _ ≤ _ := setLIntegral_le_lintegral _ _

/-! ### `𝓛_η(N)` and the radial cap -/

/-- `min(N, 1/|η|)`, read as `N` at `η = 0` (so `1/0` never appears). -/
noncomputable def Meta (η N : ℝ) : ℝ := if η = 0 then N else min N |η|⁻¹

/-- **`𝓛_η(N) = log min(N, 1/|η|)`**, with `𝓛₀(N) = log N`. -/
noncomputable def Leta (η N : ℝ) : ℝ := Real.log (Meta η N)

theorem Leta_zero (N : ℝ) : Leta 0 N = Real.log N := by simp [Leta, Meta]

theorem Leta_of_ne {η : ℝ} (hη : η ≠ 0) (N : ℝ) : Leta η N = Real.log (min N |η|⁻¹) := by
  simp [Leta, Meta, hη]

theorem Meta_facts {η N : ℝ} (hN : 1 ≤ N) (hη : |η| ≤ 1 / 10) :
    1 ≤ Meta η N ∧ Meta η N ≤ N ∧ η ^ 2 + N⁻¹ ≤ 2 / Meta η N := by
  have hN0 : 0 < N := by linarith
  unfold Meta
  by_cases h0 : η = 0
  · simp only [h0, ite_true]
    refine ⟨hN, le_rfl, ?_⟩
    rw [show (0:ℝ) ^ 2 = 0 by norm_num, zero_add, div_eq_mul_inv]
    have := inv_pos.mpr hN0; linarith
  · simp only [h0, ite_false]
    have ha : 0 < |η| := abs_pos.mpr h0
    have hinv : 10 ≤ |η|⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) ha]; linarith
    have hη2 : η ^ 2 ≤ |η| := by
      rw [← sq_abs]; nlinarith
    refine ⟨le_min hN (by linarith), min_le_left _ _, ?_⟩
    rcases le_total N |η|⁻¹ with h | h
    · rw [min_eq_left h]
      have : |η| ≤ N⁻¹ := by rw [le_inv_comm₀ ha hN0]; exact h
      rw [div_eq_mul_inv]; linarith
    · rw [min_eq_right h, div_eq_mul_inv, inv_inv]
      have : N⁻¹ ≤ |η| := by rw [inv_le_comm₀ hN0 ha]; exact h
      linarith

theorem Leta_facts {η N : ℝ} (hN : 1 ≤ N) (hη : |η| ≤ 1 / 10) :
    0 ≤ Leta η N ∧ Leta η N ≤ Real.log N ∧ Real.log (η ^ 2 + N⁻¹) ≤ Real.log 2 - Leta η N := by
  obtain ⟨h1, h2, h3⟩ := Meta_facts hN hη
  have hM0 : 0 < Meta η N := by linarith
  refine ⟨Real.log_nonneg h1, Real.log_le_log hM0 h2, ?_⟩
  have hpos : 0 < η ^ 2 + N⁻¹ := by have := inv_pos.mpr (by linarith : (0:ℝ) < N); positivity
  calc Real.log (η ^ 2 + N⁻¹) ≤ Real.log (2 / Meta η N) := Real.log_le_log hpos h3
    _ = Real.log 2 - Leta η N := by rw [Real.log_div (by norm_num) hM0.ne']; rfl

/-- The radial cap `r₊ = min(t^{1/10}, t^{1/6} / (2 (η² + t)^{1/3}))`. -/
noncomputable def hiE (t η : ℝ) : ℝ := min (t ^ ((1 : ℝ) / 10)) (t ^ ((1 : ℝ) / 6) / (2 * cbrt (η ^ 2 + t)))

/-- The midpoint (in log scale) `lo = √(t^{1/6} r₊)`. -/
noncomputable def loE (t η : ℝ) : ℝ := √(t ^ ((1 : ℝ) / 6) * hiE t η)

theorem cbrt_pos {x : ℝ} (hx : 0 < x) : 0 < cbrt x := by unfold cbrt; positivity

theorem hiE_facts {t η : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 100) (hη : |η| ≤ 1 / 10) :
    t ^ ((1 : ℝ) / 6) ≤ hiE t η ∧ hiE t η ≤ t ^ ((1 : ℝ) / 10) ∧
      η ^ 2 * (4 * hiE t η ^ 3) ≤ 3 * √t := by
  set x := η ^ 2 + t
  have hx0 : 0 < x := by positivity
  have hη2 : η ^ 2 ≤ 1 / 100 := by
    have := sq_le_sq' (abs_le.mp hη).1 (abs_le.mp hη).2; linarith
  set c := cbrt x
  have hc0 : 0 < c := cbrt_pos hx0
  have hc3 : c ^ 3 = x := cbrt_cube hx0.le
  have hc : c ≤ 1 / 2 := by
    by_contra h; push Not at h
    have : (1 / 2 : ℝ) ^ 3 < c ^ 3 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    rw [hc3] at this; norm_num at this; simp only [x] at this; linarith
  have hs0 : 0 < t ^ ((1 : ℝ) / 6) := by positivity
  have hB : t ^ ((1 : ℝ) / 6) ≤ t ^ ((1 : ℝ) / 6) / (2 * c) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hlo : t ^ ((1 : ℝ) / 6) ≤ hiE t η :=
    le_min (sixth_le_tenth ht0 (by linarith)) hB
  refine ⟨hlo, min_le_left _ _, ?_⟩
  have hh0 : 0 ≤ hiE t η := hs0.le.trans hlo
  have h3 : hiE t η ^ 3 ≤ √t / (8 * x) := by
    have := pow_le_pow_left₀ hh0 (min_le_right _ _ : hiE t η ≤ _) 3
    refine this.trans (le_of_eq ?_)
    rw [div_pow, rpow_sixth_cube ht0.le, mul_pow, hc3]; ring
  have hfrac : η ^ 2 / x ≤ 1 := by
    rw [div_le_one hx0]; simp only [x]; linarith
  calc η ^ 2 * (4 * hiE t η ^ 3) ≤ η ^ 2 * (4 * (√t / (8 * x))) :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg η)
    _ = √t / 2 * (η ^ 2 / x) := by field_simp; ring
    _ ≤ √t / 2 * 1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ ≤ 3 * √t := by linarith [Real.sqrt_nonneg t]

theorem loE_facts {t η : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 100) (hη : |η| ≤ 1 / 10) :
    t ^ ((1 : ℝ) / 6) ≤ loE t η ∧ loE t η ≤ hiE t η ∧
      Real.log (loE t η) - Real.log t / 6 =
        (Real.log (hiE t η) - Real.log t / 6) / 2 ∧
      Real.log (hiE t η / loE t η) = (Real.log (hiE t η) - Real.log t / 6) / 2 := by
  obtain ⟨h1, -, -⟩ := hiE_facts ht0 ht1 hη
  set s := t ^ ((1 : ℝ) / 6)
  set h := hiE t η
  have hs0 : 0 < s := by positivity
  have hh0 : 0 < h := lt_of_lt_of_le hs0 h1
  have hlo1 : s ≤ loE t η := by
    unfold loE
    rw [show s = √(s * s) from (Real.sqrt_mul_self hs0.le).symm]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h1 hs0.le)
  have hlo2 : loE t η ≤ h := by
    unfold loE
    rw [show h = √(h * h) from (Real.sqrt_mul_self hh0.le).symm]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h1 hh0.le)
  have hl : Real.log (loE t η) = (Real.log s + Real.log h) / 2 := by
    unfold loE
    rw [Real.log_sqrt (by positivity), Real.log_mul hs0.ne' hh0.ne']
  have hls : Real.log s = Real.log t / 6 := by
    simp only [s]; rw [Real.log_rpow ht0]; ring
  have hlo0 : 0 < loE t η := lt_of_lt_of_le hs0 hlo1
  refine ⟨hlo1, hlo2, ?_, ?_⟩
  · rw [hl, hls]; ring
  · rw [Real.log_div hh0.ne' hlo0.ne', hl, hls]; ring

/-- **The log count**: `log(r₊ / t^{1/6}) ≥ 𝓛_η(N)/15 - 1`, uniformly in `|η| ≤ 1/10`. -/
theorem log_hiE_ge {N η : ℝ} (hN : 100 ≤ N) (hη : |η| ≤ 1 / 10) :
    Leta η N / 15 - 1 ≤ Real.log (hiE N⁻¹ η) - Real.log N⁻¹ / 6 := by
  have hN0 : 0 < N := by linarith
  have ht0 : 0 < N⁻¹ := inv_pos.mpr hN0
  obtain ⟨hL0, hLN, hLx⟩ := Leta_facts (by linarith : (1:ℝ) ≤ N) hη
  have hlogt : Real.log N⁻¹ = -Real.log N := Real.log_inv N
  have hx0 : 0 < η ^ 2 + N⁻¹ := by positivity
  have hc0 : 0 < cbrt (η ^ 2 + N⁻¹) := cbrt_pos hx0
  unfold hiE
  rcases le_total (N⁻¹ ^ ((1 : ℝ) / 10)) (N⁻¹ ^ ((1 : ℝ) / 6) / (2 * cbrt (η ^ 2 + N⁻¹))) with h | h
  · rw [min_eq_left h, Real.log_rpow ht0, hlogt]
    linarith
  · rw [min_eq_right h, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) hc0.ne', Real.log_rpow ht0]
    have hlc : Real.log (cbrt (η ^ 2 + N⁻¹)) = Real.log (η ^ 2 + N⁻¹) / 3 := by
      unfold cbrt; rw [Real.log_rpow hx0]; ring
    rw [hlc]
    have h2 := Real.log_two_lt_d9
    linarith

/-! ### Theorem X4 -/

/-- **Theorem X4 (the uniform lower bound).** Fix the input-box radius `R ≥ 1`, the
(G↑) constant `Λ`, the prior floor `π₀ > 0` and the prior radius `r₀ > 0`. Then there are
`c > 0` and `N₀`, **depending only on `R, Λ, π₀, r₀`**, such that for every `η` with
`|η| ≤ η₀ = 1/10`, every loss `K` satisfying (G↑) for the target `A_η`, every prior `π` that
is `≥ π₀` within distance `r₀` of the base point `(A_η, 0, 0, 0)`, and every `N ≥ N₀`:

`Z_N = ∫ e^{-N K} π ≥ c N⁻⁴ (1 + 𝓛_η(N))⁴`,  `𝓛_η(N) = log min(N, 1/|η|)`.

The uniformity hypothesis of the paper (one prior `≥ π₀` on a fixed neighbourhood of the whole
segment `{(1, η) : |η| ≤ η₀}`) is `X4_lower_segment`. Both signs of `η` are included. -/
theorem X4_lower {R Λ π₀ r₀ : ℝ} (hR : 1 ≤ R) (hπ₀ : 0 < π₀) (hr₀ : 0 < r₀) :
    ∃ c N₀ : ℝ, 0 < c ∧ ∀ η : ℝ, |η| ≤ 1 / 10 → ∀ K : Raw16 → ℝ,
      (∀ θ M, 0 ≤ M → (∀ x : Fin 2 → ℝ, (∀ i, |x i| ≤ R) →
        ∀ k, |net θ x k - layer (Aeta η) x k| ≤ M) → K θ ≤ Λ * M ^ 2) →
      ∀ π : Raw16 → ENNReal,
      (∀ θ, dist θ (basePos (Aeta η) 0) < r₀ → ENNReal.ofReal π₀ ≤ π θ) →
      ∀ N : ℝ, N₀ ≤ N →
        ENNReal.ofReal (c * N⁻¹ ^ 4 * (1 + Leta η N) ^ 4) ≤
          ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * K θ))) * π θ := by
  set E := Real.exp (-(Λ * CerrE R ^ 2))
  have hE : 0 < E := Real.exp_pos _
  refine ⟨E * π₀ / (625 * 31 ^ 4 * 10 ^ 16), max (max 900 ((4800 * R ^ 3) ^ 10)) ((60 / r₀) ^ 10),
    by positivity, fun η hη K hK π hπ N hN => ?_⟩
  have hN900 : 900 ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN0 : 0 < N := by linarith
  set t := N⁻¹ with htdef
  have ht0 : 0 < t := inv_pos.mpr hN0
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
  have hτ1 : t ^ ((1 : ℝ) / 10) ≤ (4800 * R ^ 3)⁻¹ :=
    inv_rpow_tenth_le (by positivity) ((le_max_right _ _).trans ((le_max_left _ _).trans hN))
  have hτ2 : t ^ ((1 : ℝ) / 10) ≤ (60 / r₀)⁻¹ :=
    inv_rpow_tenth_le (by positivity) ((le_max_right _ _).trans hN)
  have ht900 : t ≤ 1 / 900 := by
    rw [htdef, inv_le_comm₀ hN0 (by norm_num)]; norm_num; linarith
  have hts : TSmallη R t := by
    refine ⟨⟨ht0, by linarith, ?_⟩, ht900⟩
    have := mul_le_mul_of_nonneg_right hτ1 (show 0 ≤ 4 * R ^ 3 by positivity)
    rw [show (4800 * R ^ 3)⁻¹ * (4 * R ^ 3) = 1 / 1200 by field_simp; norm_num] at this
    linarith
  have hr : 30 * t ^ ((1 : ℝ) / 10) < r₀ := by
    rw [inv_div] at hτ2; linarith
  have hNt : N * t = 1 := mul_inv_cancel₀ hN0.ne'
  have ht1 : t ≤ 1 / 100 := by linarith
  have hη1 : |η| ≤ 1 := by linarith
  -- the plain box
  have hcube := lower_of_region hR hts hNt hN0 hη hr (measurableSet_cubeRow _)
    (fun w hw => rowGood_cube ht0 (by linarith) hη1 hw) (v := 64 * t) (by positivity)
    (by
      rw [volume_cubeRow, ← ENNReal.ofReal_pow (by positivity), mul_pow,
        show (t ^ ((1 : ℝ) / 6)) ^ 6 = t by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num]
      norm_num) K hK π hπ hπ₀
  -- the radius-capped region
  obtain ⟨hhi1, hhi2, hhi3⟩ := hiE_facts ht0 ht1 hη
  obtain ⟨hlo1, hlo2, hD, hlog⟩ := loE_facts ht0 ht1 hη
  set lam := Real.log (hiE t η) - Real.log t / 6
  have hlam0 : 0 ≤ lam := by
    have := Real.log_le_log (by positivity) hhi1
    rw [Real.log_rpow ht0] at this; simp only [lam]; linarith
  have hvolG := volume_lowerRegionG ht0 (by linarith) hlo1 hlo2 hhi2
  rw [hD, hlog] at hvolG
  have hG := lower_of_region hR hts hNt hN0 hη hr (measurableSet_lowerRegionG _ _ _)
    (fun w hw => rowGood_G ht0 (by linarith) hlo1 hhi2 hhi3 hw)
    (v := t * (lam / 2) * (lam / 2) / 25000000) (by positivity) hvolG K hK π hπ hπ₀
  have hcount := log_hiE_ge (by linarith : (100:ℝ) ≤ N) hη
  rw [← htdef] at hcount
  obtain ⟨hL0, -, -⟩ := Leta_facts (by linarith : (1:ℝ) ≤ N) hη
  set L := Leta η N
  have hcount' : L / 15 - 1 ≤ lam := hcount
  have hL : 1 + L ≤ 15 * lam + 16 := by linarith
  have ht4 : N⁻¹ ^ 4 = t ^ 4 := rfl
  rw [ht4]
  rcases le_total 1 lam with hl1 | hl1
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hG
    have h31 : 1 + L ≤ 31 * lam := by linarith
    have hp := pow_le_pow_left₀ (by linarith) h31 4
    have e : E * π₀ * t ^ 2 * (t * (lam / 2) * (lam / 2) / 25000000) ^ 2 / 625 =
        E * π₀ / (625 * 31 ^ 4 * 10 ^ 16) * t ^ 4 * (31 * lam) ^ 4 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hcube
    have h31 : 1 + L ≤ 31 := by linarith
    have hp := pow_le_pow_left₀ (by linarith) h31 4
    have e : E * π₀ * t ^ 2 * (64 * t) ^ 2 / 625 =
        E * π₀ / (625 * 31 ^ 4 * 10 ^ 16) * t ^ 4 * (4096 * 10 ^ 16 * 31 ^ 4) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 31 by norm_num) 4]

/-- **X4 under the paper's uniformity hypothesis**: one prior, `≥ π₀` on the
`r₀`-neighbourhood of the whole segment of base points `{(A_η, 0, 0, 0) : |η| ≤ 1/10}`. -/
theorem X4_lower_segment {R Λ π₀ r₀ : ℝ} (hR : 1 ≤ R) (hπ₀ : 0 < π₀) (hr₀ : 0 < r₀)
    (π : Raw16 → ENNReal)
    (hπ : ∀ η', |η'| ≤ 1 / 10 → ∀ θ, dist θ (basePos (Aeta η') 0) < r₀ → ENNReal.ofReal π₀ ≤ π θ) :
    ∃ c N₀ : ℝ, 0 < c ∧ ∀ η : ℝ, |η| ≤ 1 / 10 → ∀ K : Raw16 → ℝ,
      (∀ θ M, 0 ≤ M → (∀ x : Fin 2 → ℝ, (∀ i, |x i| ≤ R) →
        ∀ k, |net θ x k - layer (Aeta η) x k| ≤ M) → K θ ≤ Λ * M ^ 2) →
      ∀ N : ℝ, N₀ ≤ N →
        ENNReal.ofReal (c * N⁻¹ ^ 4 * (1 + Leta η N) ^ 4) ≤
          ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * K θ))) * π θ := by
  obtain ⟨c, N₀, hc, h⟩ := X4_lower (Λ := Λ) hR hπ₀ hr₀
  exact ⟨c, N₀, hc, fun η hη K hK N hN => h η hη K hK π (hπ η hη) N hN⟩

/-- At `η = 0`, X4 is Proposition L′'s four logs: `(1 + log N)⁴ ≥ log⁴ N`. -/
theorem X4_at_zero (N : ℝ) (hN : 1 ≤ N) : Real.log N ^ 4 ≤ (1 + Leta 0 N) ^ 4 := by
  rw [Leta_zero]
  have := Real.log_nonneg hN
  exact pow_le_pow_left₀ this (by linarith) 4

end VectorSLT
