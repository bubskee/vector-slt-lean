import VectorSLT.IdentityGroup.Cubes.Chart

/-!
# `CubeSumUpper 3`

By `cubeSumUpper_of_chart` it suffices to show `∫_{‖w‖ ≤ 2} H⁻¹ < ∞` over `ℝ⁴`, where
`H(p, q, a, b)` is the coefficient norm of `x³ + (px + qy)³ + (ax + by)³`:
`H = σ² + τ² + f₂² + f₃²` with `σ = 1 + p³ + a³`, `τ = p²q + a²b`, `f₂ = pq² + ab²`,
`f₃ = q³ + b³`. These are the paper's `f₀, …, f₃` (proof of Lemma A-cubes, collinear zeros).

* *Residual* (`ab_sq_le`). The polynomial identity `ab² = τ (p²q - a²b) + σ ab² - p³ f₂`
  gives `a²b⁴ ≤ 768 H` on the box. This is the paper's residual bound `g ≳ a²b⁴` on `z = 0`,
  here without setting `z = (σ, τ)` to zero.
* *Pointwise bound* (`inv_H3_le`). By the symmetry of the two forms take `|a| ≤ |p|`. If
  `|σ| ≥ 1/4` then `H⁻¹ ≤ 16`. Otherwise `p ≤ -1/2`, and from `H ≥ σ², τ², a²b⁴/768`,
  `H⁻¹ ≤ 768^{1/5} |σ|^{-4/5} |τ|^{-4/5} |a|^{-2/5} |b|^{-4/5}`.
* *Integration* (`lintegral_Ψ_lt_top`). For `p ∈ [-2, -1/2]` the maps `q ↦ τ` (slope `p²`) and
  `p ↦ σ` (derivative `3p²`) have derivatives bounded below, so each singular factor integrates
  like `∫_{-20}^{20} |t|^{-θ} dt < ∞` with `θ < 1`.

This replaces the paper's change of coordinates `(q, β_q) ↦ z` by two one-variable
substitutions and the weighted inequality `min(X, Y, Z) ≤ X^{2/5} Y^{2/5} Z^{1/5}`.
-/

namespace VectorSLT.IdentityGroup.Cubes

open MeasureTheory Real Set
open scoped ENNReal

/-! ### The chart polynomial -/

/-- The coefficient norm of `x³ + (px + qy)³ + (ax + by)³`. -/
def H3 (p q a b : ℝ) : ℝ :=
  (1 + p ^ 3 + a ^ 3) ^ 2 + (p ^ 2 * q + a ^ 2 * b) ^ 2 + (p * q ^ 2 + a * b ^ 2) ^ 2 +
    (q ^ 3 + b ^ 3) ^ 2

lemma chartN_two (w : Fin 2 → ℝ × ℝ) : chartN w = H3 (w 0).1 (w 0).2 (w 1).1 (w 1).2 := by
  simp [chartN, cubeSumSq, cubeSum, Fin.sum_univ_succ, H3]
  ring

lemma H3_symm (p q a b : ℝ) : H3 p q a b = H3 a b p q := by unfold H3; ring

lemma sigma_sq_le_H3 (p q a b : ℝ) : (1 + p ^ 3 + a ^ 3) ^ 2 ≤ H3 p q a b := by
  unfold H3; nlinarith [sq_nonneg (p ^ 2 * q + a ^ 2 * b), sq_nonneg (p * q ^ 2 + a * b ^ 2),
    sq_nonneg (q ^ 3 + b ^ 3)]

lemma tau_sq_le_H3 (p q a b : ℝ) : (p ^ 2 * q + a ^ 2 * b) ^ 2 ≤ H3 p q a b := by
  unfold H3; nlinarith [sq_nonneg (1 + p ^ 3 + a ^ 3), sq_nonneg (p * q ^ 2 + a * b ^ 2),
    sq_nonneg (q ^ 3 + b ^ 3)]

lemma sq_le_of_abs_le {x r : ℝ} (h : |x| ≤ r) : x ^ 2 ≤ r ^ 2 := by
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) h 2

/-- The residual identity: `ab² = τ (p²q - a²b) + σ ab² - p³ f₂`. -/
lemma residual_identity (p q a b : ℝ) :
    a * b ^ 2 = (p ^ 2 * q + a ^ 2 * b) * (p ^ 2 * q - a ^ 2 * b) +
      (1 + p ^ 3 + a ^ 3) * (a * b ^ 2) - p ^ 3 * (p * q ^ 2 + a * b ^ 2) := by
  ring

/-- **Residual bound.** On the box `|p|, |q|, |a|, |b| ≤ 2`, `a²b⁴ ≤ 768 H`. -/
lemma ab_sq_le {p q a b : ℝ} (hp : |p| ≤ 2) (hq : |q| ≤ 2) (ha : |a| ≤ 2) (hb : |b| ≤ 2) :
    (a * b ^ 2) ^ 2 ≤ 768 * H3 p q a b := by
  have hp2 : p ^ 2 ≤ 4 := by nlinarith [sq_le_of_abs_le hp]
  have ha2 : a ^ 2 ≤ 4 := by nlinarith [sq_le_of_abs_le ha]
  have hq2 : q ^ 2 ≤ 4 := by nlinarith [sq_le_of_abs_le hq]
  have hb2 : b ^ 2 ≤ 4 := by nlinarith [sq_le_of_abs_le hb]
  have hD : (p ^ 2 * q - a ^ 2 * b) ^ 2 ≤ 256 := by
    have h1 : (p ^ 2 * q) ^ 2 ≤ 64 := by
      rw [mul_pow]
      calc (p ^ 2) ^ 2 * q ^ 2 ≤ 4 ^ 2 * 4 :=
            mul_le_mul (pow_le_pow_left₀ (sq_nonneg p) hp2 2) hq2 (sq_nonneg _) (by positivity)
        _ = 64 := by norm_num
    have h2 : (a ^ 2 * b) ^ 2 ≤ 64 := by
      rw [mul_pow]
      calc (a ^ 2) ^ 2 * b ^ 2 ≤ 4 ^ 2 * 4 :=
            mul_le_mul (pow_le_pow_left₀ (sq_nonneg a) ha2 2) hb2 (sq_nonneg _) (by positivity)
        _ = 64 := by norm_num
    nlinarith [sq_add_le_two (p ^ 2 * q) (-(a ^ 2 * b))]
  have hab : (a * b ^ 2) ^ 2 ≤ 64 := by
    rw [mul_pow]
    calc a ^ 2 * (b ^ 2) ^ 2 ≤ 4 * 4 ^ 2 :=
          mul_le_mul ha2 (pow_le_pow_left₀ (sq_nonneg b) hb2 2) (by positivity) (by norm_num)
      _ = 64 := by norm_num
  have hp3 : (p ^ 3) ^ 2 ≤ 64 := by
    have : (p ^ 3) ^ 2 = (p ^ 2) ^ 3 := by ring
    rw [this]; nlinarith [pow_le_pow_left₀ (sq_nonneg p) hp2 3]
  set τ := p ^ 2 * q + a ^ 2 * b
  set σ := 1 + p ^ 3 + a ^ 3
  set f := p * q ^ 2 + a * b ^ 2
  set D := p ^ 2 * q - a ^ 2 * b
  have hid : a * b ^ 2 = τ * D + σ * (a * b ^ 2) + -(p ^ 3 * f) := by
    rw [residual_identity p q a b]; ring
  have hH : τ ^ 2 + σ ^ 2 + f ^ 2 ≤ H3 p q a b := by
    unfold H3; nlinarith [sq_nonneg (q ^ 3 + b ^ 3)]
  have e := sq_add_le_three (τ * D) (σ * (a * b ^ 2)) (-(p ^ 3 * f))
  rw [← hid] at e
  have t1 : (τ * D) ^ 2 ≤ 256 * τ ^ 2 := by
    rw [mul_pow]; nlinarith [sq_nonneg τ]
  have t2 : (σ * (a * b ^ 2)) ^ 2 ≤ 64 * σ ^ 2 := by
    rw [mul_pow]; nlinarith [sq_nonneg σ]
  have t3 : (-(p ^ 3 * f)) ^ 2 ≤ 64 * f ^ 2 := by
    rw [neg_sq, mul_pow]; nlinarith [sq_nonneg f]
  nlinarith

/-- If `|a| ≤ |p|` and `σ = 1 + p³ + a³` is small, then `p ≤ -1/2`. -/
lemma le_neg_half_of_sigma_small {p a : ℝ} (hap : |a| ≤ |p|) (hσ : |1 + p ^ 3 + a ^ 3| < 1 / 4) :
    p ≤ -1 / 2 := by
  by_contra h
  push Not at h
  have h3 : |a| ^ 3 ≤ |p| ^ 3 := pow_le_pow_left₀ (abs_nonneg a) hap 3
  have ha3 : -|a| ^ 3 ≤ a ^ 3 := by rw [← abs_pow]; exact neg_abs_le _
  have hσ' := (abs_lt.mp hσ).2
  rcases le_or_gt 0 p with hp | hp
  · rw [abs_of_nonneg hp] at h3; nlinarith
  · rw [abs_of_neg hp] at h3
    have : -1 / 8 < p ^ 3 := by nlinarith [sq_nonneg p, sq_nonneg (p + 1 / 2)]
    nlinarith

lemma abs_sigma_le {p a : ℝ} (hp : |p| ≤ 2) (ha : |a| ≤ 2) : |1 + p ^ 3 + a ^ 3| ≤ 20 := by
  have h1 : |p ^ 3| ≤ 8 := by
    rw [abs_pow]; calc |p| ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (abs_nonneg p) hp 3
      _ = 8 := by norm_num
  have h2 : |a ^ 3| ≤ 8 := by
    rw [abs_pow]; calc |a| ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (abs_nonneg a) ha 3
      _ = 8 := by norm_num
  calc |1 + p ^ 3 + a ^ 3| ≤ |1 + p ^ 3| + |a ^ 3| := abs_add_le _ _
    _ ≤ (|1| + |p ^ 3|) + |a ^ 3| := by gcongr; exact abs_add_le _ _
    _ ≤ 20 := by rw [abs_one]; linarith

lemma abs_tau_le {p q a b : ℝ} (hp : |p| ≤ 2) (hq : |q| ≤ 2) (ha : |a| ≤ 2) (hb : |b| ≤ 2) :
    |p ^ 2 * q + a ^ 2 * b| ≤ 20 := by
  have h1 : |p ^ 2 * q| ≤ 8 := by
    rw [abs_mul, abs_pow]
    calc |p| ^ 2 * |q| ≤ 2 ^ 2 * 2 := by gcongr
      _ = 8 := by norm_num
  have h2 : |a ^ 2 * b| ≤ 8 := by
    rw [abs_mul, abs_pow]
    calc |a| ^ 2 * |b| ≤ 2 ^ 2 * 2 := by gcongr
      _ = 8 := by norm_num
  linarith [abs_add_le (p ^ 2 * q) (a ^ 2 * b)]

/-! ### Singular one-variable weights -/

/-- `|x|^{-θ}` as an extended real, equal to `∞` at `x = 0`. -/
noncomputable def ψ (θ x : ℝ) : ℝ≥0∞ := ((ENNReal.ofReal |x|)⁻¹) ^ θ

/-- `ψ θ` cut off outside `[-20, 20]`. -/
noncomputable def ψL (θ x : ℝ) : ℝ≥0∞ := (Icc (-20 : ℝ) 20).indicator (ψ θ) x

lemma measurable_ψ (θ : ℝ) : Measurable (ψ θ) :=
  ((ENNReal.measurable_ofReal.comp continuous_abs.measurable).inv).pow_const θ

@[fun_prop]
lemma measurable_ψL (θ : ℝ) : Measurable (ψL θ) :=
  (measurable_ψ θ).indicator measurableSet_Icc

lemma ψL_eq_ψ {θ x : ℝ} (hx : |x| ≤ 20) : ψL θ x = ψ θ x :=
  indicator_of_mem (show x ∈ Icc (-20 : ℝ) 20 from abs_le.mp hx) _

/-- `∫_{-20}^{20} |x|^{-θ} dx < ∞` for `0 < θ < 1`. -/
lemma lintegral_ψL_lt_top {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) : ∫⁻ x, ψL θ x < ⊤ := by
  set F0 : ℝ → ℝ≥0∞ := fun s => ((ENNReal.ofReal s)⁻¹) ^ θ
  set G : ℝ → ℝ≥0∞ := (Ioc (0 : ℝ) 20).indicator fun s => ENNReal.ofReal (s ^ (-θ)) with hGdef
  have hG : Measurable G :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).indicator measurableSet_Ioc
  have habs : ∀ x, ψL θ x = (Iic (20 : ℝ)).indicator F0 |x| := by
    intro x
    by_cases hx : |x| ≤ 20
    · rw [ψL_eq_ψ hx, indicator_of_mem (show |x| ∈ Iic (20 : ℝ) from hx)]; rfl
    · rw [ψL, indicator_of_notMem (show x ∉ Icc (-20 : ℝ) 20 from fun h => hx (abs_le.mpr h)),
        indicator_of_notMem (show |x| ∉ Iic (20 : ℝ) from hx)]
  have hpt : ∀ s ∈ Ioi (0 : ℝ), (Iic (20 : ℝ)).indicator F0 s ≤ G s := by
    intro s hs
    rw [hGdef]
    by_cases h20 : s ≤ 20
    · rw [indicator_of_mem (show s ∈ Iic (20 : ℝ) from h20),
        indicator_of_mem (show s ∈ Ioc (0 : ℝ) 20 from ⟨hs, h20⟩)]
      refine le_of_eq ?_
      simp only [F0]
      rw [← ENNReal.ofReal_inv_of_pos hs, ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hs.le)
        hθ0.le, Real.inv_rpow hs.le, Real.rpow_neg hs.le]
    · rw [indicator_of_notMem (show s ∉ Iic (20 : ℝ) from h20)]; exact bot_le
  have hint : IntegrableOn (fun s : ℝ => s ^ (-θ)) (Ioc 0 20) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 20) (by linarith)).1
  calc ∫⁻ x, ψL θ x = ∫⁻ x, (Iic (20 : ℝ)).indicator F0 |x| := lintegral_congr habs
    _ = 2 * ∫⁻ s in Ioi 0, (Iic (20 : ℝ)).indicator F0 s := lintegral_comp_abs _
    _ ≤ 2 * ∫⁻ s in Ioi 0, G s := by gcongr 2 * ?_; exact setLIntegral_mono hG hpt
    _ ≤ 2 * ∫⁻ s, G s := by gcongr 2 * ?_; exact setLIntegral_le_lintegral _ _
    _ = 2 * ENNReal.ofReal (∫ s in Ioc 0 20, s ^ (-θ)) := by
        rw [hGdef, lintegral_indicator measurableSet_Ioc, ofReal_integral_eq_lintegral_ofReal hint
          ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs =>
            Real.rpow_nonneg hs.1.le _))]
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top

/-- The affine substitution `t = p² q + c`, with `p² ≥ 1/4`. -/
lemma lintegral_ψL_affine_le {θ p : ℝ} (hp : p ∈ Icc (-2 : ℝ) (-1 / 2)) (c : ℝ) :
    ∫⁻ q, ψL θ (p ^ 2 * q + c) ≤ 4 * ∫⁻ x, ψL θ x := by
  have hp2 : 1 / 4 ≤ p ^ 2 := by nlinarith [hp.2]
  have hp0 : p ^ 2 ≠ 0 := by positivity
  have h := lintegral_comp_smul_eq volume (fun t => ψL θ (t + c)) hp0
  simp only [smul_eq_mul, Module.finrank_self, pow_one] at h
  rw [h, lintegral_add_right_eq_self (fun t => ψL θ t) c]
  gcongr
  rw [abs_inv, abs_of_pos (by positivity : 0 < p ^ 2)]
  calc ENNReal.ofReal (p ^ 2)⁻¹ ≤ ENNReal.ofReal 4 := ENNReal.ofReal_le_ofReal (by
        rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith)
    _ = 4 := by norm_num

/-- The cube substitution `t = p³`, on `p ∈ [-2, -1/2]` where `3p² ≥ 3/4`. -/
lemma lintegral_ψL_cube_le {θ : ℝ} (c : ℝ) :
    ∫⁻ p, (Icc (-2 : ℝ) (-1 / 2)).indicator (fun p => ψL θ (1 + p ^ 3 + c)) p ≤
      2 * ∫⁻ x, ψL θ x := by
  set s := Icc (-2 : ℝ) (-1 / 2)
  set g : ℝ → ℝ≥0∞ := fun t => ψL θ ((1 + c) + t)
  have hg : Measurable g := (measurable_ψL θ).comp (by fun_prop)
  have hderiv : ∀ x ∈ s, HasDerivWithinAt (fun p : ℝ => p ^ 3) (3 * x ^ 2) s x := by
    intro x _
    simpa using (hasDerivAt_pow 3 x).hasDerivWithinAt
  have hinj : InjOn (fun p : ℝ => p ^ 3) s :=
    (Odd.strictMono_pow (by decide : Odd 3)).injective.injOn
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc hderiv hinj g
  calc ∫⁻ p, s.indicator (fun p => ψL θ (1 + p ^ 3 + c)) p
      = ∫⁻ p in s, g (p ^ 3) := by
        rw [lintegral_indicator measurableSet_Icc]
        refine setLIntegral_congr_fun measurableSet_Icc fun p _ => ?_
        simp only [g]; ring_nf
    _ ≤ ∫⁻ p in s, 2 * (ENNReal.ofReal |3 * p ^ 2| * g (p ^ 3)) := by
        refine setLIntegral_mono (by fun_prop) fun p hp => ?_
        have hp2 : 1 / 4 ≤ p ^ 2 := by nlinarith [hp.2]
        have h1 : (1 : ℝ≥0∞) ≤ 2 * ENNReal.ofReal |3 * p ^ 2| := by
          rw [abs_of_nonneg (by positivity), show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (by nlinarith)
        calc g (p ^ 3) = 1 * g (p ^ 3) := (one_mul _).symm
          _ ≤ 2 * ENNReal.ofReal |3 * p ^ 2| * g (p ^ 3) := by gcongr
          _ = _ := mul_assoc _ _ _
    _ = 2 * ∫⁻ t in (fun p : ℝ => p ^ 3) '' s, g t := by
        rw [lintegral_const_mul' _ _ (by norm_num), hcv]
    _ ≤ 2 * ∫⁻ t, g t := by gcongr 2 * ?_; exact setLIntegral_le_lintegral _ _
    _ = 2 * ∫⁻ x, ψL θ x := by rw [lintegral_add_left_eq_self (fun t => ψL θ t) (1 + c)]

/-! ### The pointwise bound -/

lemma inv_le_of_sq_le {H X : ℝ} (h : X ^ 2 ≤ H) :
    (ENNReal.ofReal H)⁻¹ ≤ ((ENNReal.ofReal |X|)⁻¹) ^ (2 : ℕ) := by
  rw [← ENNReal.inv_pow, ← ENNReal.ofReal_pow (abs_nonneg X), sq_abs]
  exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal h)

lemma inv_le_of_prod_le {H A B : ℝ} (h : (A * B ^ 2) ^ 2 ≤ 768 * H) :
    (ENNReal.ofReal H)⁻¹ ≤
      768 * (((ENNReal.ofReal |A|)⁻¹) ^ (2 : ℕ) * ((ENNReal.ofReal |B|)⁻¹) ^ (4 : ℕ)) := by
  have e : ((ENNReal.ofReal |A|)⁻¹) ^ (2 : ℕ) * ((ENNReal.ofReal |B|)⁻¹) ^ (4 : ℕ) =
      (ENNReal.ofReal ((A * B ^ 2) ^ 2))⁻¹ := by
    rw [← ENNReal.inv_pow, ← ENNReal.inv_pow,
      ← ENNReal.mul_inv (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
        (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)),
      ← ENNReal.ofReal_pow (abs_nonneg A), ← ENNReal.ofReal_pow (abs_nonneg B),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    have hA : |A| ^ 2 = A ^ 2 := sq_abs A
    have hB : |B| ^ 4 = B ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]
    rw [hA, hB]; ring
  rw [e]
  have h2 : ENNReal.ofReal ((A * B ^ 2) ^ 2) ≤ 768 * ENNReal.ofReal H := by
    rw [show (768 : ℝ≥0∞) = ENNReal.ofReal 768 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal h
  have h3 := ENNReal.inv_le_inv.mpr h2
  rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by simp))] at h3
  exact (ENNReal.inv_mul_le_iff (by norm_num) (by simp)).mp h3

/-- `min(X, Y, Z) ≤ X^{2/5} Y^{2/5} Z^{1/5}`, in the form used for `H⁻¹`. -/
lemma inv_le_weights {H X Y A B : ℝ} (hX : X ^ 2 ≤ H) (hY : Y ^ 2 ≤ H)
    (hAB : (A * B ^ 2) ^ 2 ≤ 768 * H) :
    (ENNReal.ofReal H)⁻¹ ≤
      (768 : ℝ≥0∞) ^ ((1 : ℝ) / 5) * (ψ (4 / 5) X * ψ (4 / 5) Y * ψ (2 / 5) A * ψ (4 / 5) B) := by
  set t := (ENNReal.ofReal H)⁻¹
  have ht : t = t ^ ((2 : ℝ) / 5) * t ^ ((2 : ℝ) / 5) * t ^ ((1 : ℝ) / 5) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num),
      ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hpow : ∀ (x : ℝ≥0∞) (m : ℕ) (r : ℝ), (x ^ m) ^ r = x ^ ((m : ℝ) * r) := by
    intro x m r; rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  have h1 : t ^ ((2 : ℝ) / 5) ≤ ψ (4 / 5) X := by
    calc t ^ ((2 : ℝ) / 5) ≤ (((ENNReal.ofReal |X|)⁻¹) ^ (2 : ℕ)) ^ ((2 : ℝ) / 5) :=
          ENNReal.rpow_le_rpow (inv_le_of_sq_le hX) (by norm_num)
      _ = ψ (4 / 5) X := by rw [hpow, ψ]; norm_num
  have h2 : t ^ ((2 : ℝ) / 5) ≤ ψ (4 / 5) Y := by
    calc t ^ ((2 : ℝ) / 5) ≤ (((ENNReal.ofReal |Y|)⁻¹) ^ (2 : ℕ)) ^ ((2 : ℝ) / 5) :=
          ENNReal.rpow_le_rpow (inv_le_of_sq_le hY) (by norm_num)
      _ = ψ (4 / 5) Y := by rw [hpow, ψ]; norm_num
  have h3 : t ^ ((1 : ℝ) / 5) ≤ (768 : ℝ≥0∞) ^ ((1 : ℝ) / 5) * (ψ (2 / 5) A * ψ (4 / 5) B) := by
    calc t ^ ((1 : ℝ) / 5) ≤ (768 * (((ENNReal.ofReal |A|)⁻¹) ^ (2 : ℕ) *
          ((ENNReal.ofReal |B|)⁻¹) ^ (4 : ℕ))) ^ ((1 : ℝ) / 5) :=
          ENNReal.rpow_le_rpow (inv_le_of_prod_le hAB) (by norm_num)
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hpow, hpow, ψ, ψ]
          norm_num
  calc t = t ^ ((2 : ℝ) / 5) * t ^ ((2 : ℝ) / 5) * t ^ ((1 : ℝ) / 5) := ht
    _ ≤ ψ (4 / 5) X * ψ (4 / 5) Y *
          ((768 : ℝ≥0∞) ^ ((1 : ℝ) / 5) * (ψ (2 / 5) A * ψ (4 / 5) B)) := by gcongr
    _ = _ := by ring

/-- The singular majorant on one half `|a| ≤ |p|` of the box. -/
noncomputable def Ψ (x : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ≥0∞ :=
  (Icc (-2 : ℝ) (-1 / 2)).indicator (fun p => ψL (4 / 5) (1 + p ^ 3 + x.2.1 ^ 3)) x.1.1 *
    ψL (4 / 5) (x.1.1 ^ 2 * x.1.2 + x.2.1 ^ 2 * x.2.2) * ψL (2 / 5) x.2.1 * ψL (4 / 5) x.2.2

lemma measurable_Ψ : Measurable Ψ := by
  unfold Ψ
  refine Measurable.mul (Measurable.mul (Measurable.mul ?_ ?_) ?_) ?_
  · have : Measurable fun z : ℝ × ℝ => (Icc (-2 : ℝ) (-1 / 2)).indicator
        (fun p => ψL (4 / 5) (1 + p ^ 3 + z.2 ^ 3)) z.1 := by
      have h1 : Measurable fun z : ℝ × ℝ => ψL (4 / 5) (1 + z.1 ^ 3 + z.2 ^ 3) :=
        (measurable_ψL _).comp (by fun_prop)
      have heq : (fun z : ℝ × ℝ => (Icc (-2 : ℝ) (-1 / 2)).indicator
          (fun p => ψL (4 / 5) (1 + p ^ 3 + z.2 ^ 3)) z.1) =
          ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Icc (-2 : ℝ) (-1 / 2)).indicator
            (fun z : ℝ × ℝ => ψL (4 / 5) (1 + z.1 ^ 3 + z.2 ^ 3)) := by
        funext z
        by_cases hz : z.1 ∈ Icc (-2 : ℝ) (-1 / 2)
        · rw [indicator_of_mem
            (show z ∈ (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Icc (-2 : ℝ) (-1 / 2) from hz),
            indicator_of_mem hz]
        · rw [indicator_of_notMem
            (show z ∉ (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Icc (-2 : ℝ) (-1 / 2) from hz),
            indicator_of_notMem hz]
      rw [heq]
      exact h1.indicator (measurableSet_Icc.preimage measurable_fst)
    exact this.comp (measurable_fst.fst.prodMk measurable_snd.fst)
  · exact (measurable_ψL _).comp (by fun_prop)
  · exact (measurable_ψL _).comp (by fun_prop)
  · exact (measurable_ψL _).comp (by fun_prop)

/-- **Pointwise bound** on the half `|a| ≤ |p|` of the box. -/
lemma inv_H3_le {p q a b : ℝ} (hp : |p| ≤ 2) (hq : |q| ≤ 2) (ha : |a| ≤ 2) (hb : |b| ≤ 2)
    (hap : |a| ≤ |p|) :
    (ENNReal.ofReal (H3 p q a b))⁻¹ ≤ 16 + (768 : ℝ≥0∞) ^ ((1 : ℝ) / 5) * Ψ ((p, q), (a, b)) := by
  by_cases hσ : |1 + p ^ 3 + a ^ 3| < 1 / 4
  · have hp' : p ∈ Icc (-2 : ℝ) (-1 / 2) :=
      ⟨(abs_le.mp hp).1, le_neg_half_of_sigma_small hap hσ⟩
    have hΨ : Ψ ((p, q), (a, b)) = ψ (4 / 5) (1 + p ^ 3 + a ^ 3) *
        ψ (4 / 5) (p ^ 2 * q + a ^ 2 * b) * ψ (2 / 5) a * ψ (4 / 5) b := by
      simp only [Ψ]
      rw [indicator_of_mem hp', ψL_eq_ψ (abs_sigma_le hp ha), ψL_eq_ψ (abs_tau_le hp hq ha hb),
        ψL_eq_ψ (by linarith), ψL_eq_ψ (by linarith)]
    rw [hΨ]
    exact (inv_le_weights (sigma_sq_le_H3 p q a b) (tau_sq_le_H3 p q a b)
      (ab_sq_le hp hq ha hb)).trans le_add_self
  · push Not at hσ
    have h16 : (1 : ℝ) / 16 ≤ H3 p q a b := by
      have := sigma_sq_le_H3 p q a b
      have h2 : (1 / 4 : ℝ) ^ 2 ≤ (1 + p ^ 3 + a ^ 3) ^ 2 := by
        rw [← sq_abs (1 + p ^ 3 + a ^ 3)]; exact pow_le_pow_left₀ (by norm_num) hσ 2
      nlinarith
    refine le_trans ?_ le_self_add
    calc (ENNReal.ofReal (H3 p q a b))⁻¹ ≤ (ENNReal.ofReal (1 / 16))⁻¹ :=
          ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal h16)
      _ = 16 := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, one_div, inv_inv]
          norm_num

/-! ### Integration -/

/-- `∫ Ψ < ∞`: integrate `q`, then `p`, then `a` and `b`. -/
lemma lintegral_Ψ_lt_top : ∫⁻ x, Ψ x < ⊤ := by
  set K₄ := ∫⁻ x, ψL (4 / 5) x
  set K₂ := ∫⁻ x, ψL (2 / 5) x
  have hK₄ : K₄ < ⊤ := lintegral_ψL_lt_top (by norm_num) (by norm_num)
  have hK₂ : K₂ < ⊤ := lintegral_ψL_lt_top (by norm_num) (by norm_num)
  -- the `q`-integral
  have hq : ∀ p a b : ℝ, ∫⁻ q, Ψ ((p, q), (a, b)) ≤
      (Icc (-2 : ℝ) (-1 / 2)).indicator (fun p => ψL (4 / 5) (1 + p ^ 3 + a ^ 3)) p *
        (ψL (2 / 5) a * ψL (4 / 5) b * (4 * K₄)) := by
    intro p a b
    set S := (Icc (-2 : ℝ) (-1 / 2)).indicator (fun p => ψL (4 / 5) (1 + p ^ 3 + a ^ 3)) p
    have hrw : ∀ q, Ψ ((p, q), (a, b)) =
        (S * (ψL (2 / 5) a * ψL (4 / 5) b)) * ψL (4 / 5) (p ^ 2 * q + a ^ 2 * b) := by
      intro q; simp only [Ψ, S]; ring
    simp_rw [hrw]
    rw [lintegral_const_mul _
      (by fun_prop : Measurable fun q : ℝ => ψL (4 / 5) (p ^ 2 * q + a ^ 2 * b))]
    by_cases hp : p ∈ Icc (-2 : ℝ) (-1 / 2)
    · calc S * (ψL (2 / 5) a * ψL (4 / 5) b) * ∫⁻ q, ψL (4 / 5) (p ^ 2 * q + a ^ 2 * b)
          ≤ S * (ψL (2 / 5) a * ψL (4 / 5) b) * (4 * K₄) := by
            gcongr; exact lintegral_ψL_affine_le hp _
        _ = _ := by ring
    · have : S = 0 := indicator_of_notMem hp _
      rw [this]; simp
  -- the `p`-integral
  have hp : ∀ a b : ℝ, ∫⁻ p, ∫⁻ q, Ψ ((p, q), (a, b)) ≤
      2 * K₄ * (ψL (2 / 5) a * ψL (4 / 5) b * (4 * K₄)) := by
    intro a b
    calc ∫⁻ p, ∫⁻ q, Ψ ((p, q), (a, b))
        ≤ ∫⁻ p, (Icc (-2 : ℝ) (-1 / 2)).indicator (fun p => ψL (4 / 5) (1 + p ^ 3 + a ^ 3)) p *
            (ψL (2 / 5) a * ψL (4 / 5) b * (4 * K₄)) := lintegral_mono fun p => hq p a b
      _ = (∫⁻ p, (Icc (-2 : ℝ) (-1 / 2)).indicator
            (fun p => ψL (4 / 5) (1 + p ^ 3 + a ^ 3)) p) *
            (ψL (2 / 5) a * ψL (4 / 5) b * (4 * K₄)) := by
          rw [lintegral_mul_const _ (Measurable.indicator
            (f := fun p : ℝ => ψL (4 / 5) (1 + p ^ 3 + a ^ 3)) (by fun_prop) measurableSet_Icc)]
      _ ≤ 2 * K₄ * (ψL (2 / 5) a * ψL (4 / 5) b * (4 * K₄)) := by
          gcongr; exact lintegral_ψL_cube_le _
  calc ∫⁻ x, Ψ x = ∫⁻ y : (ℝ × ℝ) × (ℝ × ℝ), Ψ y.swap :=
        ((Measure.measurePreserving_swap (μ := (volume : Measure (ℝ × ℝ)))
          (ν := (volume : Measure (ℝ × ℝ)))).lintegral_comp measurable_Ψ).symm
    _ ≤ ∫⁻ y₁ : ℝ × ℝ, ∫⁻ y₂ : ℝ × ℝ, Ψ (y₂, y₁) := by
        rw [Measure.volume_eq_prod]; exact lintegral_prod_le (fun y => Ψ y.swap)
    _ ≤ ∫⁻ y₁ : ℝ × ℝ, 2 * K₄ * (ψL (2 / 5) y₁.1 * ψL (4 / 5) y₁.2 * (4 * K₄)) := by
        refine lintegral_mono fun y₁ => ?_
        calc ∫⁻ y₂ : ℝ × ℝ, Ψ (y₂, y₁) ≤ ∫⁻ p, ∫⁻ q, Ψ ((p, q), y₁) := by
              rw [Measure.volume_eq_prod]; exact lintegral_prod_le (fun y₂ => Ψ (y₂, y₁))
          _ ≤ _ := hp y₁.1 y₁.2
    _ = 2 * K₄ * (4 * K₄) * ∫⁻ y₁ : ℝ × ℝ, ψL (2 / 5) y₁.1 * ψL (4 / 5) y₁.2 := by
        rw [← lintegral_const_mul _
          (by fun_prop : Measurable fun y : ℝ × ℝ => ψL (2 / 5) y.1 * ψL (4 / 5) y.2)]
        refine lintegral_congr fun y => ?_
        ring
    _ = 2 * K₄ * (4 * K₄) * (K₂ * K₄) := by
        rw [Measure.volume_eq_prod, lintegral_prod_mul (measurable_ψL _).aemeasurable
          (measurable_ψL _).aemeasurable]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hK₄)
          (ENNReal.mul_lt_top (by norm_num) hK₄)) (ENNReal.mul_lt_top hK₂ hK₄)

/-! ### Assembly -/

lemma mem_closedBall_two_iff (x : (ℝ × ℝ) × (ℝ × ℝ)) :
    (MeasurableEquiv.finTwoArrow.symm x : Fin 2 → ℝ × ℝ) ∈
        Metric.closedBall (0 : Fin 2 → ℝ × ℝ) 2 ↔
      x ∈ Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) 2 := by
  simp only [mem_closedBall_zero_iff, MeasurableEquiv.finTwoArrow, pi_norm_le_iff_of_nonneg
    (show (0 : ℝ) ≤ 2 by norm_num), Fin.forall_fin_two, norm_prod_le_iff]
  simp

/-- **The chart estimate for three forms.** -/
theorem chart_three :
    ∫⁻ w in Metric.closedBall (0 : Fin 2 → ℝ × ℝ) 2,
      ((ENNReal.ofReal (chartN w))⁻¹) ^ ((((2 : ℕ) : ℝ) + 1) / 3) < ⊤ := by
  have hexp : (((2 : ℕ) : ℝ) + 1) / 3 = 1 := by norm_num
  simp_rw [hexp, ENNReal.rpow_one]
  set B := Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) 2 with hB
  set C : ℝ≥0∞ := (768 : ℝ≥0∞) ^ ((1 : ℝ) / 5)
  have hC : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by simp)
  have hpt : ∀ x : (ℝ × ℝ) × (ℝ × ℝ),
      (Metric.closedBall (0 : Fin 2 → ℝ × ℝ) 2).indicator
        (fun w => (ENNReal.ofReal (chartN w))⁻¹) (MeasurableEquiv.finTwoArrow.symm x) ≤
      B.indicator (fun _ => (16 : ℝ≥0∞)) x + (C * Ψ x + C * Ψ x.swap) := by
    intro x
    by_cases hx : x ∈ B
    · rw [indicator_of_mem ((mem_closedBall_two_iff x).mpr hx), indicator_of_mem hx]
      have hx' := hx
      rw [hB, mem_closedBall_zero_iff, norm_prod_le_iff, norm_prod_le_iff, norm_prod_le_iff,
        Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at hx'
      obtain ⟨⟨hp, hq⟩, ⟨ha, hb⟩⟩ := hx'
      have hN : chartN (MeasurableEquiv.finTwoArrow.symm x : Fin 2 → ℝ × ℝ) =
          H3 x.1.1 x.1.2 x.2.1 x.2.2 := by
        rw [chartN_two]; simp [MeasurableEquiv.finTwoArrow]
      rw [hN]
      rcases le_total |x.2.1| |x.1.1| with hap | hpa
      · calc (ENNReal.ofReal (H3 x.1.1 x.1.2 x.2.1 x.2.2))⁻¹ ≤ 16 + C * Ψ x :=
              inv_H3_le hp hq ha hb hap
          _ ≤ 16 + (C * Ψ x + C * Ψ x.swap) := by gcongr; exact le_self_add
      · calc (ENNReal.ofReal (H3 x.1.1 x.1.2 x.2.1 x.2.2))⁻¹
            = (ENNReal.ofReal (H3 x.2.1 x.2.2 x.1.1 x.1.2))⁻¹ := by rw [H3_symm]
          _ ≤ 16 + C * Ψ x.swap := inv_H3_le ha hb hp hq hpa
          _ ≤ 16 + (C * Ψ x + C * Ψ x.swap) := by gcongr; exact le_add_self
    · rw [indicator_of_notMem (fun h => hx ((mem_closedBall_two_iff x).mp h))]
      exact bot_le
  calc ∫⁻ w in Metric.closedBall (0 : Fin 2 → ℝ × ℝ) 2, (ENNReal.ofReal (chartN w))⁻¹
      = ∫⁻ w, (Metric.closedBall (0 : Fin 2 → ℝ × ℝ) 2).indicator
          (fun w => (ENNReal.ofReal (chartN w))⁻¹) w :=
        (lintegral_indicator Metric.isClosed_closedBall.measurableSet _).symm
    _ = ∫⁻ x, (Metric.closedBall (0 : Fin 2 → ℝ × ℝ) 2).indicator
          (fun w => (ENNReal.ofReal (chartN w))⁻¹) (MeasurableEquiv.finTwoArrow.symm x) :=
        ((volume_preserving_finTwoArrow (ℝ × ℝ)).symm.lintegral_comp_emb
          MeasurableEquiv.finTwoArrow.symm.measurableEmbedding _).symm
    _ ≤ ∫⁻ x : (ℝ × ℝ) × (ℝ × ℝ),
          (B.indicator (fun _ => (16 : ℝ≥0∞)) x + (C * Ψ x + C * Ψ x.swap)) :=
        lintegral_mono hpt
    _ = 16 * volume B + (C * (∫⁻ x, Ψ x) + C * ∫⁻ x : (ℝ × ℝ) × (ℝ × ℝ), Ψ x.swap) := by
        rw [lintegral_add_left (measurable_const.indicator
            Metric.isClosed_closedBall.measurableSet),
          lintegral_add_left (measurable_Ψ.const_mul C),
          lintegral_indicator_const Metric.isClosed_closedBall.measurableSet,
          lintegral_const_mul _ measurable_Ψ,
          lintegral_const_mul (f := fun x : (ℝ × ℝ) × (ℝ × ℝ) => Ψ x.swap) _
            (measurable_Ψ.comp measurable_swap)]
    _ = 16 * volume B + (C * (∫⁻ x, Ψ x) + C * ∫⁻ x, Ψ x) := by
        rw [show ∫⁻ x : (ℝ × ℝ) × (ℝ × ℝ), Ψ x.swap = ∫⁻ x, Ψ x from
          (Measure.measurePreserving_swap (μ := (volume : Measure (ℝ × ℝ)))
            (ν := (volume : Measure (ℝ × ℝ)))).lintegral_comp measurable_Ψ]
    _ < ⊤ := by
        have hB' : volume B < ⊤ := measure_closedBall_lt_top
        have hΨ := lintegral_Ψ_lt_top
        exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) hB',
          ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hC.lt_top hΨ,
            ENNReal.mul_lt_top hC.lt_top hΨ⟩⟩

/-- **Lemma A-cubes, upper half, `k = 3`.** -/
theorem cubeSumUpper_three : CubeSumUpper 3 :=
  cubeSumUpper_of_chart 2 chart_three

end VectorSLT.IdentityGroup.Cubes
