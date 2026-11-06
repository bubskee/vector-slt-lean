/-
Milestone C: the one-row leading-model sublevel lower bound (Theorem L §4).
-/
import VectorSLT.Sublevel1D

namespace VectorSLT

open MeasureTheory Set

/-- The one-row leading cubic model `P(a,b) = (∑ aᵢ² bᵢ, ∑ aᵢ bᵢ², ∑ bᵢ³)` of (L1). -/
def rowP (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![∑ i, a i ^ 2 * b i, ∑ i, a i * b i ^ 2, ∑ i, b i ^ 3]

/-- Squared Euclidean norm of `P(a,b)`. -/
def rowPsq (a b : Fin 3 → ℝ) : ℝ := ∑ i, rowP a b i ^ 2

/-! ### The amplitude box `q ∈ [0.99, 1.01]`, `p ∈ [-1.01, -0.99]` -/

/-- Entries of the quadratic form `M` of (L9) in the amplitudes `(q, p) = (q, a')`. -/
def m11 (q : ℝ) : ℝ := q + q ^ 4
def m12 (q p : ℝ) : ℝ := q ^ 2 * p ^ 2
def m22 (p : ℝ) : ℝ := p + p ^ 4
/-- Discriminant `D = m12² - m11 m22 = -det M`. -/
def discr (q p : ℝ) : ℝ := m12 q p ^ 2 - m11 q * m22 p
/-- The small root `ρ` of `m11 ρ² + 2 m12 ρ + m22 = 0`, so that `Q(b, c)` has the factor `b - ρc`. -/
noncomputable def rho (q p : ℝ) : ℝ := (-m12 q p + √(discr q p)) / m11 q

def InAmpBox (q p : ℝ) : Prop := 99 / 100 ≤ q ∧ q ≤ 101 / 100 ∧ -101 / 100 ≤ p ∧ p ≤ -99 / 100

theorem amp_bounds {q p : ℝ} (h : InAmpBox q p) :
    19 / 10 ≤ m11 q ∧ m11 q ≤ 21 / 10 ∧ 96 / 100 ≤ m12 q p ∧ m12 q p ≤ 105 / 100 ∧
      |m22 p| ≤ 6 / 100 ∧ q ^ 2 ≤ 11 / 10 ∧ p ^ 2 ≤ 11 / 10 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hq2a : 9801 / 10000 ≤ q ^ 2 := by nlinarith
  have hq2b : q ^ 2 ≤ 10201 / 10000 := by nlinarith
  have hp2a : 9801 / 10000 ≤ p ^ 2 := by nlinarith
  have hp2b : p ^ 2 ≤ 10201 / 10000 := by nlinarith
  have hq4a : (9801 / 10000) ^ 2 ≤ q ^ 4 := by
    rw [show q ^ 4 = (q ^ 2) ^ 2 by ring]; exact pow_le_pow_left₀ (by norm_num) hq2a 2
  have hq4b : q ^ 4 ≤ (10201 / 10000) ^ 2 := by
    rw [show q ^ 4 = (q ^ 2) ^ 2 by ring]; exact pow_le_pow_left₀ (by positivity) hq2b 2
  have hp4a : (9801 / 10000) ^ 2 ≤ p ^ 4 := by
    rw [show p ^ 4 = (p ^ 2) ^ 2 by ring]; exact pow_le_pow_left₀ (by norm_num) hp2a 2
  have hp4b : p ^ 4 ≤ (10201 / 10000) ^ 2 := by
    rw [show p ^ 4 = (p ^ 2) ^ 2 by ring]; exact pow_le_pow_left₀ (by positivity) hp2b 2
  have hm12a : 9801 / 10000 * (9801 / 10000) ≤ q ^ 2 * p ^ 2 :=
    mul_le_mul hq2a hp2a (by norm_num) (by positivity)
  have hm12b : q ^ 2 * p ^ 2 ≤ 10201 / 10000 * (10201 / 10000) :=
    mul_le_mul hq2b hp2b (by positivity) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, by linarith, by linarith⟩
  · unfold m11; nlinarith
  · unfold m11; nlinarith
  · unfold m12; nlinarith
  · unfold m12; nlinarith
  · unfold m22; rw [abs_le]; constructor <;> nlinarith

theorem discr_bounds {q p : ℝ} (h : InAmpBox q p) : 1 / 2 ≤ discr q p ∧ discr q p ≤ 2 := by
  obtain ⟨a1, a2, a3, a4, a5, -, -⟩ := amp_bounds h
  obtain ⟨b1, b2⟩ := abs_le.mp a5
  unfold discr
  constructor <;> nlinarith

theorem sqrt_discr_bounds {q p : ℝ} (h : InAmpBox q p) :
    0 < √(discr q p) ∧ √(discr q p) ≤ 3 / 2 := by
  obtain ⟨d1, d2⟩ := discr_bounds h
  refine ⟨Real.sqrt_pos.mpr (by linarith), ?_⟩
  rw [Real.sqrt_le_left (by norm_num)]; linarith

/-- The root identities: `m11 ρ + m12 = √D` and `m11 ρ² + 2 m12 ρ + m22 = 0`. -/
theorem rho_identities {q p : ℝ} (h : InAmpBox q p) :
    m11 q * rho q p + m12 q p = √(discr q p) ∧
      m11 q * rho q p ^ 2 + 2 * m12 q p * rho q p + m22 p = 0 := by
  obtain ⟨a1, -, -⟩ := amp_bounds h
  have hm : m11 q ≠ 0 := by linarith
  have hs := Real.sq_sqrt (show 0 ≤ discr q p by linarith [(discr_bounds h).1])
  have h1 : m11 q * rho q p + m12 q p = √(discr q p) := by
    unfold rho; field_simp; ring
  refine ⟨h1, ?_⟩
  have h2 : rho q p = (√(discr q p) - m12 q p) / m11 q := by unfold rho; ring
  rw [h2]; field_simp
  unfold discr at hs ⊢
  nlinarith [hs]

theorem abs_rho_le {q p : ℝ} (h : InAmpBox q p) : |rho q p| ≤ 1 / 10 := by
  obtain ⟨a1, a2, a3, a4, a5, -, -⟩ := amp_bounds h
  obtain ⟨s0, s1⟩ := sqrt_discr_bounds h
  obtain ⟨i1, i2⟩ := rho_identities h
  -- ρ (m12 + √D) = -m22   (from the two identities)
  have hkey : rho q p * (m12 q p + √(discr q p)) = -m22 p := by nlinarith
  have hpos : 0 < m12 q p + √(discr q p) := by linarith
  have : |rho q p| * (m12 q p + √(discr q p)) = |m22 p| := by
    rw [← abs_of_pos hpos, ← abs_mul, hkey, abs_neg]
  rw [abs_le] at a5 ⊢
  have := abs_nonneg (rho q p)
  constructor <;> nlinarith [abs_le.mp (le_refl |rho q p|), le_abs_self (rho q p), neg_abs_le (rho q p)]

theorem sq_le_of_abs_le {x y : ℝ} (h : |x| ≤ y) : x ^ 2 ≤ y ^ 2 := by
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) h 2

/-- **Scaled one-row estimate on the lower region.** With amplitudes `ã = (1, q, p)` in the
box and `β = (z - q²β₂ - p²β₃, v + ρc, c)`, where `c ∈ [h³, h²]`, `v ∈ [h⁶/(2c), h⁶/c]` and
`|z| ≤ h⁶`, we get `‖P(ã, β)‖² ≤ 5000 h¹²` and `|βᵢ| ≤ 4`. (Here `δ = h⁶` in the
paper's notation.) -/
theorem scaled_bound {q p h c v z : ℝ} (hb : InAmpBox q p) (h0 : 0 < h) (h1 : h ≤ 1)
    (hc1 : h ^ 3 ≤ c) (hc2 : c ≤ h ^ 2) (hv1 : h ^ 6 / (2 * c) ≤ v) (hv2 : v ≤ h ^ 6 / c)
    (hz : |z| ≤ h ^ 6) :
    rowPsq ![1, q, p] ![z - q ^ 2 * (v + rho q p * c) - p ^ 2 * c, v + rho q p * c, c] ≤
        5000 * h ^ 12 ∧
      |z - q ^ 2 * (v + rho q p * c) - p ^ 2 * c| ≤ 4 ∧ |v + rho q p * c| ≤ 4 ∧ |c| ≤ 4 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := amp_bounds hb
  obtain ⟨s0, s1⟩ := sqrt_discr_bounds hb
  obtain ⟨i1, i2⟩ := rho_identities hb
  have hr := abs_rho_le hb
  set ρ := rho q p
  set sD := √(discr q p)
  have h2pos : 0 < h ^ 2 := by positivity
  have hh32 : h ^ 3 ≤ h ^ 2 := by
    rw [show h ^ 3 = h ^ 2 * h by ring]; nlinarith
  have hh62 : h ^ 6 ≤ h ^ 2 := by
    rw [show h ^ 6 = h ^ 2 * h ^ 4 by ring]
    nlinarith [pow_le_one₀ h0.le h1 (n := 4), pow_pos h0 4]
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc1
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv1
  have hvc : v * c ≤ h ^ 6 := by rwa [le_div_iff₀ hc0] at hv2
  have hv3 : v ≤ h ^ 3 := by
    have : h ^ 6 / c ≤ h ^ 6 / h ^ 3 := div_le_div_of_nonneg_left (by positivity) (by positivity) hc1
    rw [show h ^ 6 / h ^ 3 = h ^ 3 by field_simp] at this
    linarith
  have hvv : v ^ 2 ≤ h ^ 6 := by
    have := pow_le_pow_left₀ hv0.le hv3 2; rw [← pow_mul] at this; simpa using this
  -- the pieces
  set β2 := v + ρ * c
  set w := q ^ 2 * β2 + p ^ 2 * c
  set β1 := z - q ^ 2 * β2 - p ^ 2 * c
  have hβ2 : |β2| ≤ 11 / 10 * h ^ 2 := by
    calc |β2| ≤ |v| + |ρ| * |c| := by
          simp only [β2]; rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ h ^ 2 + 1 / 10 * h ^ 2 := by
          rw [abs_of_pos hv0, abs_of_pos hc0]
          exact add_le_add (hv3.trans hh32) (mul_le_mul hr hc2 hc0.le (by norm_num))
      _ = 11 / 10 * h ^ 2 := by ring
  have hc' : |c| ≤ h ^ 2 := by rw [abs_of_pos hc0]; exact hc2
  have hw : |w| ≤ 3 * h ^ 2 := by
    calc |w| ≤ q ^ 2 * |β2| + p ^ 2 * |c| := by
          simp only [w]
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg q), abs_of_nonneg (sq_nonneg p)]
      _ ≤ 11 / 10 * (11 / 10 * h ^ 2) + 11 / 10 * h ^ 2 :=
          add_le_add (mul_le_mul a6 hβ2 (abs_nonneg _) (by norm_num))
            (mul_le_mul a7 hc' (abs_nonneg _) (by norm_num))
      _ ≤ 3 * h ^ 2 := by nlinarith
  have hβ1 : |β1| ≤ 4 * h ^ 2 := by
    have : β1 = z - w := by simp only [β1, w]; ring
    rw [this]
    calc |z - w| ≤ |z| + |w| := abs_sub _ _
      _ ≤ h ^ 2 + 3 * h ^ 2 := add_le_add (hz.trans hh62) hw
      _ = 4 * h ^ 2 := by ring
  -- P₁ = z
  have hP1 : ∑ i, (![1, q, p] : Fin 3 → ℝ) i ^ 2 * (![β1, β2, c] : Fin 3 → ℝ) i = z := by
    simp only [Fin.sum_univ_three]; simp [β1]; ring
  -- P₂ = Q - 2 z w + z²,  Q = m11 v² + 2 √D v c
  have hP2e : ∑ i, (![1, q, p] : Fin 3 → ℝ) i * (![β1, β2, c] : Fin 3 → ℝ) i ^ 2 =
      (m11 q * v ^ 2 + 2 * sD * v * c) - 2 * z * w + z ^ 2 := by
    simp only [Fin.sum_univ_three]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_mul]
    have hQ : m11 q * v ^ 2 + 2 * sD * v * c =
        m11 q * β2 ^ 2 + 2 * m12 q p * β2 * c + m22 p * c ^ 2 := by
      simp only [β2]; rw [← i1]; linear_combination (-c ^ 2) * i2
    rw [hQ]; simp only [β1, w, m11, m12, m22]; ring
  have hP2 : |∑ i, (![1, q, p] : Fin 3 → ℝ) i * (![β1, β2, c] : Fin 3 → ℝ) i ^ 2| ≤
      13 * h ^ 6 := by
    rw [hP2e]
    have h86 : h ^ 8 ≤ h ^ 6 := by
      rw [show h ^ 8 = h ^ 6 * h ^ 2 by ring]
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ h0.le h1)
    have h126 : h ^ 12 ≤ h ^ 6 := by
      rw [show h ^ 12 = h ^ 6 * h ^ 6 by ring]
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ h0.le h1)
    have hQ : |m11 q * v ^ 2 + 2 * sD * v * c| ≤ 6 * h ^ 6 := by
      have t1 : m11 q * v ^ 2 ≤ 21 / 10 * h ^ 6 := mul_le_mul a2 hvv (sq_nonneg _) (by norm_num)
      have t2 : sD * (v * c) ≤ 3 / 2 * h ^ 6 := mul_le_mul s1 hvc (by positivity) (by norm_num)
      rw [abs_of_nonneg (by have := mul_pos hv0 hc0; positivity)]
      have e : m11 q * v ^ 2 + 2 * sD * v * c = m11 q * v ^ 2 + 2 * (sD * (v * c)) := by ring
      rw [e]; linarith [pow_pos h0 6]
    have hzw : |2 * z * w| ≤ 6 * h ^ 6 := by
      rw [abs_mul, abs_mul, abs_two]
      have := mul_le_mul hz hw (abs_nonneg _) (by positivity)
      have e : h ^ 6 * (3 * h ^ 2) = 3 * h ^ 8 := by ring
      linarith
    have hzz : z ^ 2 ≤ h ^ 6 := by
      have := sq_le_of_abs_le hz
      have e : (h ^ 6) ^ 2 = h ^ 12 := by ring
      linarith
    calc _ ≤ |m11 q * v ^ 2 + 2 * sD * v * c| + |2 * z * w| + |z ^ 2| := by
          refine (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 6 * h ^ 6 + 6 * h ^ 6 + h ^ 6 := by
          rw [abs_of_nonneg (sq_nonneg z)]; exact add_le_add (add_le_add hQ hzw) hzz
      _ = 13 * h ^ 6 := by ring
  have hP3 : |∑ i, (![β1, β2, c] : Fin 3 → ℝ) i ^ 3| ≤ 67 * h ^ 6 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    have e1 : |β1 ^ 3| ≤ 64 * h ^ 6 := by
      rw [abs_pow]; calc |β1| ^ 3 ≤ (4 * h ^ 2) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hβ1 3
        _ = 64 * h ^ 6 := by ring
    have e2 : |β2 ^ 3| ≤ 2 * h ^ 6 := by
      rw [abs_pow]; calc |β2| ^ 3 ≤ (11 / 10 * h ^ 2) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hβ2 3
        _ ≤ 2 * h ^ 6 := by nlinarith [pow_pos h0 6]
    have e3 : |c ^ 3| ≤ h ^ 6 := by
      rw [abs_pow]; calc |c| ^ 3 ≤ (h ^ 2) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hc' 3
        _ = h ^ 6 := by ring
    calc _ ≤ |β1 ^ 3| + |β2 ^ 3| + |c ^ 3| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by linarith
  refine ⟨?_, by linarith [pow_le_one₀ h0.le h1 (n := 2)], by linarith [pow_le_one₀ h0.le h1 (n := 2)],
    by linarith [pow_le_one₀ h0.le h1 (n := 2)]⟩
  have hsplit : rowPsq ![1, q, p] ![β1, β2, c] =
      (∑ i, (![1, q, p] : Fin 3 → ℝ) i ^ 2 * (![β1, β2, c] : Fin 3 → ℝ) i) ^ 2 +
      (∑ i, (![1, q, p] : Fin 3 → ℝ) i * (![β1, β2, c] : Fin 3 → ℝ) i ^ 2) ^ 2 +
      (∑ i, (![β1, β2, c] : Fin 3 → ℝ) i ^ 3) ^ 2 := by
    unfold rowPsq; rw [Fin.sum_univ_three]; rfl
  rw [hsplit, hP1]
  have q2 := sq_le_of_abs_le hP2
  have q3 := sq_le_of_abs_le hP3
  have q1 := sq_le_of_abs_le hz
  have e : ∀ C : ℝ, (C * h ^ 6) ^ 2 = C ^ 2 * h ^ 12 := fun C => by ring
  rw [e] at q2 q3
  have : (h ^ 6) ^ 2 = h ^ 12 := by ring
  norm_num at q2 q3
  linarith [pow_pos h0 12]

/-! ### Volume of the `b`-fibre (product region (L13), in raw coordinates) -/

/-- The raw `b`-fibre of the lower region over a fixed amplitude vector, written in the
coordinates `(b₁, (b₂, b₃))`. Here `δ = H⁶`, `β = b / a₁`, `c = β₃ ∈ [H³, H²]`,
`v = β₂ - ρβ₃ ∈ [δ/(2c), δ/c]` and `|z| ≤ δ` with `z = β₁ + q²β₂ + p²β₃`. -/
def bFibre (a1 H ρ q2 p2 : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {b | b.2.2 ∈ Icc (a1 * H ^ 3) (a1 * H ^ 2) ∧
    b.2.1 ∈ Icc (ρ * b.2.2 + a1 ^ 2 * H ^ 6 / (2 * b.2.2)) (ρ * b.2.2 + a1 ^ 2 * H ^ 6 / b.2.2) ∧
    b.1 ∈ Icc (-(q2 * b.2.1 + p2 * b.2.2) - a1 * H ^ 6) (-(q2 * b.2.1 + p2 * b.2.2) + a1 * H ^ 6)}

theorem measurableSet_bFibre (a1 H ρ q2 p2 : ℝ) : MeasurableSet (bFibre a1 H ρ q2 p2) := by
  unfold bFibre
  simp only [mem_Icc, ofPred_and]
  refine ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)).inter
    (((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)).inter
      ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_))) <;> fun_prop

/-- **Exact `b`-fibre volume**: `a₁³ δ² log(1/H)` with `δ = H⁶`. The factor `log(1/H)` is the
hyperbola logarithm: `∫_{a₁H³}^{a₁H²} db₃ / b₃`. -/
theorem volume_bFibre (a1 H ρ q2 p2 : ℝ) (ha1 : 0 < a1) (hH0 : 0 < H) (hH1 : H ≤ 1) :
    volume (bFibre a1 H ρ q2 p2) = ENNReal.ofReal (a1 ^ 3 * H ^ 12 * Real.log (1 / H)) := by
  set T : Set (ℝ × ℝ) := {y | y.2 ∈ Icc (a1 * H ^ 3) (a1 * H ^ 2) ∧
    y.1 ∈ Icc (ρ * y.2 + a1 ^ 2 * H ^ 6 / (2 * y.2)) (ρ * y.2 + a1 ^ 2 * H ^ 6 / y.2)}
  have hT : MeasurableSet T := by
    simp only [T, mem_Icc, ofPred_and]
    refine ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)).inter
      ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)) <;> fun_prop
  have hδ : 0 < a1 * H ^ 6 := by positivity
  -- integrate out b₁
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (measurableSet_bFibre _ _ _ _ _)]
  have h1 : ∀ y : ℝ × ℝ, volume ((fun x => (x, y)) ⁻¹' bFibre a1 H ρ q2 p2) =
      T.indicator (fun _ => ENNReal.ofReal (2 * (a1 * H ^ 6))) y := by
    intro y
    by_cases hy : y ∈ T
    · rw [indicator_of_mem hy]
      have : (fun x => (x, y)) ⁻¹' bFibre a1 H ρ q2 p2 =
          Icc (-(q2 * y.1 + p2 * y.2) - a1 * H ^ 6) (-(q2 * y.1 + p2 * y.2) + a1 * H ^ 6) := by
        ext x; simp only [mem_preimage, bFibre, mem_ofPred_eq]
        exact ⟨fun h => h.2.2, fun h => ⟨hy.1, hy.2, h⟩⟩
      rw [this, Real.volume_Icc]; congr 1; ring
    · rw [indicator_of_notMem hy]
      have : (fun x => (x, y)) ⁻¹' bFibre a1 H ρ q2 p2 = ∅ := by
        ext x; simp only [mem_preimage, bFibre, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hy ⟨h.1, h.2.1⟩
      rw [this, measure_empty]
  simp_rw [h1]
  rw [lintegral_indicator_const hT]
  -- integrate out b₂, then b₃
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hT]
  have h2 : ∀ b3 : ℝ, volume ((fun x => (x, b3)) ⁻¹' T) =
      (Icc (a1 * H ^ 3) (a1 * H ^ 2)).indicator
        (fun b3 => ENNReal.ofReal (a1 ^ 2 * H ^ 6 / 2 / (b3 - 0))) b3 := by
    intro b3
    by_cases hb : b3 ∈ Icc (a1 * H ^ 3) (a1 * H ^ 2)
    · rw [indicator_of_mem hb]
      have : (fun x => (x, b3)) ⁻¹' T =
          Icc (ρ * b3 + a1 ^ 2 * H ^ 6 / (2 * b3)) (ρ * b3 + a1 ^ 2 * H ^ 6 / b3) := by
        ext x; simp only [mem_preimage, T, mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩
      have hb0 : 0 < b3 := lt_of_lt_of_le (by positivity) hb.1
      rw [this, Real.volume_Icc]; congr 1; field_simp; ring
    · rw [indicator_of_notMem hb]
      have : (fun x => (x, b3)) ⁻¹' T = ∅ := by
        ext x; simp only [mem_preimage, T, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hb h.1
      rw [this, measure_empty]
  simp_rw [h2]
  have hle : a1 * H ^ 3 ≤ a1 * H ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ ha1.le
    rw [show H ^ 3 = H ^ 2 * H by ring]
    exact mul_le_of_le_one_right (by positivity) hH1
  rw [lintegral_indicator measurableSet_Icc,
    lintegral_Icc_div_sub _ 0 _ _ (by positivity) (by positivity) hle,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have : (a1 * H ^ 2 - 0) / (a1 * H ^ 3 - 0) = 1 / H := by field_simp; ring
  rw [this]; ring

/-! ### The lower region and its volume -/

/-- `H(a₁) = (t / (5000 a₁⁶))^{1/12}`, so `δ = H⁶ = N^{-1/2} a₁^{-3} / √5000` with `t = 1/N`. -/
noncomputable def hfun (t a1 : ℝ) : ℝ := (t / (5000 * a1 ^ 6)) ^ ((1 : ℝ) / 12)

theorem hfun_pow12 {t a1 : ℝ} (ht : 0 < t) (ha : 0 < a1) :
    hfun t a1 ^ 12 = t / (5000 * a1 ^ 6) := by
  unfold hfun
  rw [show (1 : ℝ) / 12 = ((12 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.rpow_inv_natCast_pow (by positivity) (by norm_num)

theorem hfun_pos {t a1 : ℝ} (ht : 0 < t) (ha : 0 < a1) : 0 < hfun t a1 := by
  unfold hfun; positivity

@[fun_prop] theorem measurable_rho_comp {α : Type*} [MeasurableSpace α] {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => rho (f x) (g x) := by
  unfold rho discr m11 m12 m22; fun_prop

@[fun_prop] theorem measurable_hfun_comp {α : Type*} [MeasurableSpace α] {f : α → ℝ} (t : ℝ)
    (hf : Measurable f) : Measurable fun x => hfun t (f x) := by
  unfold hfun; fun_prop

/-- Amplitudes: radius `a₁ ∈ [t^{1/7}, t^{1/10}]` and ratios `a₂/a₁ ∈ [0.99, 1.01]`,
`a₃/a₁ ∈ [-1.01, -0.99]` (the paper's box about `(q, a') = (1, -1)`). -/
def ampSet (t : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {a | a.1 ∈ Icc (t ^ ((1 : ℝ) / 7)) (t ^ ((1 : ℝ) / 10)) ∧
    a.2.1 ∈ Icc (a.1 * (99 / 100)) (a.1 * (101 / 100)) ∧
    a.2.2 ∈ Icc (a.1 * (-101 / 100)) (a.1 * (-99 / 100))}

/-- The full lower region in raw coordinates `((a₁,a₂,a₃),(b₁,b₂,b₃))`. -/
def lowerRegion (t : ℝ) : Set ((ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)) :=
  {x | x.1 ∈ ampSet t ∧ x.2 ∈ bFibre x.1.1 (hfun t x.1.1)
    (rho (x.1.2.1 / x.1.1) (x.1.2.2 / x.1.1)) ((x.1.2.1 / x.1.1) ^ 2) ((x.1.2.2 / x.1.1) ^ 2)}

theorem measurableSet_ampSet (t : ℝ) : MeasurableSet (ampSet t) := by
  unfold ampSet
  simp only [mem_Icc, ofPred_and]
  refine ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)).inter
    (((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)).inter
      ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_))) <;> fun_prop

theorem measurableSet_lowerRegion (t : ℝ) : MeasurableSet (lowerRegion t) := by
  have hA := measurableSet_ampSet t
  unfold lowerRegion bFibre
  simp only [mem_Icc, ofPred_and]
  refine (measurable_fst hA).inter ?_
  refine ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)).inter
    (((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_)).inter
      ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_))) <;> fun_prop

theorem rpow_le_rpow_small {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t ^ ((1 : ℝ) / 7) ≤ t ^ ((1 : ℝ) / 10) :=
  Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by norm_num)

/-- On the amplitude set, `H ≤ 1` and `log(1/H) ≥ log(1/t)/84`. -/
theorem hfun_facts {t a1 : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (ha : a1 ∈ Icc (t ^ ((1 : ℝ) / 7)) (t ^ ((1 : ℝ) / 10))) :
    0 < a1 ∧ a1 ≤ 1 ∧ hfun t a1 ≤ 1 ∧ Real.log (1 / t) / 84 ≤ Real.log (1 / hfun t a1) := by
  have ha0 : 0 < a1 := lt_of_lt_of_le (by positivity) ha.1
  have ha1 : a1 ≤ 1 := ha.2.trans (Real.rpow_le_one ht0.le ht1 (by norm_num))
  have hH0 := hfun_pos ht0 ha0
  have h12 := hfun_pow12 ht0 ha0
  -- a₁⁷ ≥ t
  have h7 : t ≤ a1 ^ 7 := by
    have := pow_le_pow_left₀ (by positivity) ha.1 7
    rwa [← Real.rpow_natCast, ← Real.rpow_mul ht0.le, show (1 : ℝ) / 7 * (7 : ℕ) = 1 by norm_num,
      Real.rpow_one] at this
  have h76 : a1 ^ 7 ≤ a1 ^ 6 := pow_le_pow_of_le_one ha0.le ha1 (by norm_num)
  refine ⟨ha0, ha1, ?_, ?_⟩
  · have : hfun t a1 ^ 12 ≤ 1 := by
      rw [h12, div_le_one (by positivity)]; nlinarith [pow_pos ha0 6]
    exact (pow_le_one_iff_of_nonneg hH0.le (by norm_num)).mp this
  · -- log(1/H) = -(1/12) log(H¹²) and log(H¹²) ≤ (1/7) log t
    have hlogH : Real.log (1 / hfun t a1) = -(1 / 12) * Real.log (t / (5000 * a1 ^ 6)) := by
      rw [← h12, Real.log_pow, one_div, Real.log_inv]; push_cast; ring
    have hloga : (1 / 7) * Real.log t ≤ Real.log a1 := by
      have := Real.log_le_log (by positivity) ha.1
      rwa [Real.log_rpow ht0] at this
    have hl : Real.log (t / (5000 * a1 ^ 6)) =
        Real.log t - Real.log 5000 - 6 * Real.log a1 := by
      rw [Real.log_div ht0.ne' (by positivity), Real.log_mul (by norm_num) (by positivity),
        Real.log_pow]; push_cast; ring
    have h5000 : 0 ≤ Real.log 5000 := Real.log_nonneg (by norm_num)
    rw [hlogH, hl, one_div, Real.log_inv]
    nlinarith

/-- The constant of milestone C: `1 / 24 500 000 000`. -/
noncomputable def cC : ℝ := 1 / 24500000000

/-- **Volume of the lower region**: at least `c t (log(1/t))²` for `0 < t ≤ 1`. -/
theorem volume_lowerRegion {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ENNReal.ofReal (cC * t * Real.log (1 / t) ^ 2) ≤ volume (lowerRegion t) := by
  set L := Real.log (1 / t)
  have hL : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ ht0]; linarith)
  set F : ℝ × ℝ × ℝ → ENNReal := fun a => ENNReal.ofReal (t * L / 420000 / a.1 ^ 3)
  -- fibrewise lower bound
  have hfib : ∀ a : ℝ × ℝ × ℝ, (ampSet t).indicator F a ≤
      volume (Prod.mk a ⁻¹' lowerRegion t) := by
    intro a
    by_cases ha : a ∈ ampSet t
    · rw [indicator_of_mem ha]
      obtain ⟨ha0, -, hH1, hlog⟩ := hfun_facts ht0 ht1 ha.1
      have : Prod.mk a ⁻¹' lowerRegion t = bFibre a.1 (hfun t a.1)
          (rho (a.2.1 / a.1) (a.2.2 / a.1)) ((a.2.1 / a.1) ^ 2) ((a.2.2 / a.1) ^ 2) := by
        ext b; simp only [mem_preimage, lowerRegion, mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
      rw [this, volume_bFibre _ _ _ _ _ ha0 (hfun_pos ht0 ha0) hH1]
      apply ENNReal.ofReal_le_ofReal
      have h12 := hfun_pow12 ht0 ha0
      have e : a.1 ^ 3 * hfun t a.1 ^ 12 = t / 5000 / a.1 ^ 3 := by
        rw [h12]; field_simp
      rw [e]
      calc t * L / 420000 / a.1 ^ 3 = t / 5000 / a.1 ^ 3 * (L / 84) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
    · rw [indicator_of_notMem ha]; exact bot_le
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_lowerRegion t)]
  refine le_trans ?_ (lintegral_mono hfib)
  -- integrate the indicator over the amplitudes
  rw [Measure.volume_eq_prod, lintegral_prod _
    ((Measurable.indicator (by fun_prop) (measurableSet_ampSet t)).aemeasurable)]
  set I := Icc (t ^ ((1 : ℝ) / 7)) (t ^ ((1 : ℝ) / 10))
  have hin : ∀ a1 : ℝ, I.indicator (fun a1 => ENNReal.ofReal (t * L / 1050000000 / (a1 - 0))) a1
      ≤ ∫⁻ y, (ampSet t).indicator F (a1, y) := by
    intro a1
    by_cases h : a1 ∈ I
    · rw [indicator_of_mem h]
      obtain ⟨ha0, -, -, -⟩ := hfun_facts ht0 ht1 h
      have hset : ∀ y : ℝ × ℝ, (ampSet t).indicator F (a1, y) =
          (Icc (a1 * (99 / 100)) (a1 * (101 / 100)) ×ˢ
            Icc (a1 * (-101 / 100)) (a1 * (-99 / 100))).indicator
            (fun _ => ENNReal.ofReal (t * L / 420000 / a1 ^ 3)) y := by
        intro y
        by_cases hy : y ∈ Icc (a1 * (99 / 100)) (a1 * (101 / 100)) ×ˢ
            Icc (a1 * (-101 / 100)) (a1 * (-99 / 100))
        · rw [indicator_of_mem hy, indicator_of_mem (show (a1, y) ∈ ampSet t from ⟨h, hy.1, hy.2⟩)]
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
    lintegral_Icc_div_sub _ 0 _ _ (by positivity) (by positivity)
      (rpow_le_rpow_small ht0 ht1)]
  apply ENNReal.ofReal_le_ofReal
  have hlog : Real.log ((t ^ ((1 : ℝ) / 10) - 0) / (t ^ ((1 : ℝ) / 7) - 0)) = 3 / 70 * L := by
    rw [sub_zero, sub_zero, Real.log_div (by positivity) (by positivity), Real.log_rpow ht0,
      Real.log_rpow ht0]
    simp only [L, one_div, Real.log_inv]; ring
  rw [hlog]; simp only [cC]; apply le_of_eq; ring

/-! ### The lower region lies in the sublevel set, inside the box -/

theorem rowPsq_smul (s : ℝ) (a b : Fin 3 → ℝ) :
    rowPsq (fun i => s * a i) (fun i => s * b i) = s ^ 6 * rowPsq a b := by
  simp only [rowPsq, rowP, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- Pointwise content of the lower region: for `0 < t ≤ min 1 ((ε/4)^10)`, every point
of `lowerRegion t` has all six coordinates in `[-ε, ε]` and `‖P(a,b)‖² ≤ t`. -/
theorem lowerRegion_sub {ε t : ℝ} (hε : 0 < ε) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (htε : t ≤ (ε / 4) ^ 10) (f g : Fin 3 → ℝ)
    (hx : ((f 0, f 1, f 2), (g 0, g 1, g 2)) ∈ lowerRegion t) :
    (∀ i, |f i| ≤ ε) ∧ (∀ i, |g i| ≤ ε) ∧ rowPsq f g ≤ t := by
  obtain ⟨⟨hr, ha2, ha3⟩, hb3, hb2, hb1⟩ := hx
  simp only at hr ha2 ha3 hb3 hb2 hb1
  obtain ⟨ha0, -, hH1, -⟩ := hfun_facts ht0 ht1 hr
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
    refine hr.2.trans ?_
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

/-! ### Transport to `ℝ³ × ℝ³` and the headline statement -/

/-- `(Fin 3 → ℝ) ≃ᵐ ℝ × ℝ × ℝ`, `f ↦ (f 0, f 1, f 2)`. -/
noncomputable def e3 : (Fin 3 → ℝ) ≃ᵐ ℝ × ℝ × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow)

theorem e3_apply (f : Fin 3 → ℝ) : e3 f = (f 0, f 1, f 2) := rfl

theorem measurePreserving_e3 : MeasurePreserving e3 volume volume := by
  unfold e3
  exact ((MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)).comp
    (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0)

/-- The one-row sublevel set inside the box `[-ε, ε]⁶`. -/
def rowSublevel (ε t : ℝ) : Set ((Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
  {x | (∀ i, x.1 i ∈ Icc (-ε) ε) ∧ (∀ i, x.2 i ∈ Icc (-ε) ε) ∧ rowPsq x.1 x.2 ≤ t}

/-- **Milestone C, explicit form.** For `0 < t ≤ min 1 ((ε/4)¹⁰)`,
`|{(a,b) ∈ [-ε,ε]⁶ : ‖P(a,b)‖² ≤ t}| ≥ cC · t · (log(1/t))²`, `cC = 1/24 500 000 000`. -/
theorem rowSublevel_lower_explicit {ε t : ℝ} (hε : 0 < ε) (ht0 : 0 < t)
    (ht : t ≤ min 1 ((ε / 4) ^ 10)) :
    ENNReal.ofReal (cC * t * Real.log (1 / t) ^ 2) ≤ volume (rowSublevel ε t) := by
  have ht1 : t ≤ 1 := ht.trans (min_le_left _ _)
  have htε : t ≤ (ε / 4) ^ 10 := ht.trans (min_le_right _ _)
  have hmp : MeasurePreserving (e3.prodCongr e3) volume volume :=
    measurePreserving_e3.prod measurePreserving_e3
  refine (volume_lowerRegion ht0 ht1).trans ?_
  rw [← hmp.measure_preimage_equiv]
  apply measure_mono
  intro x hx
  have hx' : ((x.1 0, x.1 1, x.1 2), (x.2 0, x.2 1, x.2 2)) ∈ lowerRegion t := hx
  obtain ⟨h1, h2, h3⟩ := lowerRegion_sub hε ht0 ht1 htε x.1 x.2 hx'
  exact ⟨fun i => abs_le.mp (h1 i), fun i => abs_le.mp (h2 i), h3⟩

/-- **Milestone C** (brief statement shape): for every `ε > 0` there are `c > 0` and `t₀ > 0`
with `|{(a,b) ∈ [-ε,ε]⁶ : ‖P(a,b)‖² ≤ t}| ≥ c t (log(1/t))²` for all `0 < t ≤ t₀`. -/
theorem rowSublevel_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      ENNReal.ofReal (c * t * Real.log (1 / t) ^ 2) ≤ volume (rowSublevel ε t) :=
  ⟨cC, by unfold cC; norm_num, min 1 ((ε / 4) ^ 10), lt_min one_pos (by positivity),
    fun _ ht0 ht => rowSublevel_lower_explicit hε ht0 ht⟩

/-- **Laplace corollary** (one line in the brief):
`∫_{[-ε,ε]⁶} e^{-N‖P‖²} ≥ e^{-1} |{‖P‖² ≤ 1/N}| ≥ e^{-1} cC N^{-1} (log N)²`
for `N ≥ max 1 ((4/ε)^10)`. -/
theorem rowLaplace_lower {ε N : ℝ} (hε : 0 < ε) (hN : max 1 ((4 / ε) ^ 10) ≤ N) :
    ENNReal.ofReal (Real.exp (-1) * cC * N⁻¹ * Real.log N ^ 2) ≤
      ∫⁻ x in {x : (Fin 3 → ℝ) × (Fin 3 → ℝ) |
          (∀ i, x.1 i ∈ Icc (-ε) ε) ∧ (∀ i, x.2 i ∈ Icc (-ε) ε)},
        ENNReal.ofReal (Real.exp (-(N * rowPsq x.1 x.2))) := by
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have ht0 : 0 < N⁻¹ := inv_pos.mpr hN0
  have ht : N⁻¹ ≤ min 1 ((ε / 4) ^ 10) := by
    refine le_min (inv_le_one_of_one_le₀ hN1) ?_
    rw [inv_le_comm₀ hN0 (by positivity), ← inv_pow, inv_div]
    exact (le_max_right _ _).trans hN
  have hvol := rowSublevel_lower_explicit hε ht0 ht
  rw [one_div, inv_inv] at hvol
  calc ENNReal.ofReal (Real.exp (-1) * cC * N⁻¹ * Real.log N ^ 2)
      = ENNReal.ofReal (Real.exp (-1)) * ENNReal.ofReal (cC * N⁻¹ * Real.log N ^ 2) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]; ring_nf
    _ ≤ ENNReal.ofReal (Real.exp (-1)) * volume (rowSublevel ε N⁻¹) := by gcongr
    _ = ∫⁻ x in rowSublevel ε N⁻¹, ENNReal.ofReal (Real.exp (-1)) := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ x in rowSublevel ε N⁻¹, ENNReal.ofReal (Real.exp (-(N * rowPsq x.1 x.2))) := by
        refine setLIntegral_mono ?_ ?_
        · unfold rowPsq rowP; fun_prop
        intro x hx
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have := hx.2.2
        have : N * rowPsq x.1 x.2 ≤ 1 := by
          rw [← le_div_iff₀' hN0, one_div]; exact this
        linarith
    _ ≤ _ := lintegral_mono_set (show rowSublevel ε N⁻¹ ⊆ {x : (Fin 3 → ℝ) × (Fin 3 → ℝ) |
          (∀ i, x.1 i ∈ Icc (-ε) ε) ∧ (∀ i, x.2 i ∈ Icc (-ε) ε)} from fun x hx => ⟨hx.1, hx.2.1⟩)

end VectorSLT
