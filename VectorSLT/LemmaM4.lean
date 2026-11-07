/-
L6 stage 3, M4: one row at frozen amplitudes (Lemma M4 of `shear_position_one_exact.md` §5,
decomposition §3). Source pinned at cubic-chaos `103cdc7`.

Coordinates: `b = (b_p, β)` with `β = (b_i, b_j) ∈ ℝ²` (pivot first). With
`q = a_i/a_p`, `a' = a_j/a_p`, `u = y_i/y_p`, `v = y_j/y_p`, `c = a_p³/γ`,
`h = (q²(1-u), a'²(1-v))`:
`M̃ = M_{u,v} + c h hᵀ`, `det M̃ = q a' E` (M9).
-/
import VectorSLT.QuadSublevel
import VectorSLT.SLT.Toolkit
import VectorSLT.SLT.InvSqrt

namespace VectorSLT

open MeasureTheory Set Filter Matrix SLT

/-! ### The slice algebra (decomposition A2, A3) -/

/-- The slice matrix `M̃` (entries). -/
noncomputable def mt00 (q u c : ℝ) : ℝ := q + q ^ 4 * u ^ 2 + c * (q ^ 2 * (1 - u)) ^ 2
noncomputable def mt01 (q a' u v c : ℝ) : ℝ :=
  q ^ 2 * a' ^ 2 * u * v + c * (q ^ 2 * (1 - u)) * (a' ^ 2 * (1 - v))
noncomputable def mt11 (a' v c : ℝ) : ℝ := a' + a' ^ 4 * v ^ 2 + c * (a' ^ 2 * (1 - v)) ^ 2

noncomputable def Mt (q a' u v c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![mt00 q u c, mt01 q a' u v c; mt01 q a' u v c, mt11 a' v c]

/-- `E` of (M9). -/
noncomputable def EM9 (q a' u v c : ℝ) : ℝ :=
  1 + q ^ 3 * u ^ 2 + a' ^ 3 * v ^ 2 + c * (q ^ 3 * (1 - u) ^ 2 * (1 + a' ^ 3 * v ^ 2) -
    2 * q ^ 3 * a' ^ 3 * u * v * (1 - u) * (1 - v) + a' ^ 3 * (1 - v) ^ 2 * (1 + q ^ 3 * u ^ 2))

theorem Mt_isSymm (q a' u v c : ℝ) : (Mt q a' u v c).IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- **(M9)**: `det M̃ = q a' E`. -/
theorem det_Mt (q a' u v c : ℝ) : (Mt q a' u v c).det = q * a' * EM9 q a' u v c := by
  rw [det_fin_two]; simp [Mt, mt00, mt01, mt11, EM9]; ring

/-- **The slice reduction (A3)**: on the slice `Z = ζ`, `G = a_p · quadForm M̃ L k`. -/
theorem slice_reduction {ap ai aj yp yi yj γ κ ζ : ℝ} (hap : ap ≠ 0) (hyp : yp ≠ 0)
    (hγ : γ ≠ 0) (β : Fin 2 → ℝ) :
    let q := ai / ap
    let a' := aj / ap
    let u := yi / yp
    let v := yj / yp
    let c := ap ^ 3 / γ
    let w := ζ - κ
    let bp := (w - ai ^ 2 * yi * β 0 - aj ^ 2 * yj * β 1) / (ap ^ 2 * yp)
    let L : Fin 2 → ℝ := ![-(2 * w / (ap ^ 2 * yp)) * (q ^ 2 * u) +
        2 * w * ap / (yp * γ) * (q ^ 2 * (1 - u)),
      -(2 * w / (ap ^ 2 * yp)) * (a' ^ 2 * v) + 2 * w * ap / (yp * γ) * (a' ^ 2 * (1 - v))]
    let k := w ^ 2 / (ap ^ 4 * yp ^ 2) + w ^ 2 / (ap * yp ^ 2 * γ)
    ap ^ 2 * yp * bp + ai ^ 2 * yi * β 0 + aj ^ 2 * yj * β 1 + κ = ζ ∧
    ap * bp ^ 2 + ai * β 0 ^ 2 + aj * β 1 ^ 2 + (ap ^ 2 * bp + ai ^ 2 * β 0 + aj ^ 2 * β 1) ^ 2 / γ
      = ap * quadForm (Mt q a' u v c) L k β := by
  intro q a' u v c w bp L k
  constructor
  · simp only [bp, w]; field_simp; ring
  · rw [quadForm_expand _ (Mt_isSymm _ _ _ _ _)]
    simp only [Mt, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      mt00, mt01, mt11, L, k, bp, w, q, a', u, v, c]
    field_simp
    ring

/-! ### Entry bounds on the pivot chart -/

theorem Mt_entries {q a' u v c : ℝ} (hq : |q| ≤ 1) (ha : |a'| ≤ 1) (hu : |u - 1| ≤ 1 / 8)
    (hv : |v - 1| ≤ 1 / 8) (hc : |c| ≤ 2) : ∀ i j, |Mt q a' u v c i j| ≤ 3 := by
  have hq2 : q ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg q]
  have ha2 : a' ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg a']
  obtain ⟨hu1, hu2⟩ := abs_le.mp hu
  obtain ⟨hv1, hv2⟩ := abs_le.mp hv
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  obtain ⟨hq1, hq1'⟩ := abs_le.mp hq
  obtain ⟨ha1, ha1'⟩ := abs_le.mp ha
  have hq4 : q ^ 4 ≤ 1 := by nlinarith [sq_nonneg q]
  have ha4 : a' ^ 4 ≤ 1 := by nlinarith [sq_nonneg a']
  have hu2' : u ^ 2 ≤ 81 / 64 := by nlinarith
  have hv2' : v ^ 2 ≤ 81 / 64 := by nlinarith
  have hh1 : (q ^ 2 * (1 - u)) ^ 2 ≤ 1 / 64 := by
    rw [mul_pow]; nlinarith [sq_nonneg (q ^ 2), sq_nonneg (1 - u), sq_nonneg q]
  have hh2 : (a' ^ 2 * (1 - v)) ^ 2 ≤ 1 / 64 := by
    rw [mul_pow]; nlinarith [sq_nonneg (a' ^ 2), sq_nonneg (1 - v), sq_nonneg a']
  have hh12 : |q ^ 2 * (1 - u) * (a' ^ 2 * (1 - v))| ≤ 1 / 64 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg q), abs_of_nonneg (sq_nonneg a')]
    have : |1 - u| ≤ 1 / 8 := by rw [abs_sub_comm]; exact hu
    have : |1 - v| ≤ 1 / 8 := by rw [abs_sub_comm]; exact hv
    have e1 : q ^ 2 * |1 - u| ≤ 1 * (1 / 8) :=
      mul_le_mul hq2 (by rw [abs_sub_comm]; exact hu) (abs_nonneg _) zero_le_one
    have e2 : a' ^ 2 * |1 - v| ≤ 1 * (1 / 8) :=
      mul_le_mul ha2 (by rw [abs_sub_comm]; exact hv) (abs_nonneg _) zero_le_one
    have := mul_le_mul e1 e2 (by positivity) (by norm_num)
    linarith
  have huv : |u * v| ≤ 81 / 64 := by
    rw [abs_mul]
    have h1 : |u| ≤ 9 / 8 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |v| ≤ 9 / 8 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg u, abs_nonneg v]
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [Mt, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · unfold mt00
    have t1 : |c * (q ^ 2 * (1 - u)) ^ 2| ≤ 2 * (1 / 64) := by
      rw [abs_mul, abs_sq]
      exact mul_le_mul hc hh1 (sq_nonneg _) (by norm_num)
    have t2 : |q ^ 4 * u ^ 2| ≤ 1 * (81 / 64) := by
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul hq4 hu2' (sq_nonneg _) zero_le_one
    have := abs_add_le (q + q ^ 4 * u ^ 2) (c * (q ^ 2 * (1 - u)) ^ 2)
    have := abs_add_le q (q ^ 4 * u ^ 2)
    linarith
  · unfold mt01
    have t1 : |c * (q ^ 2 * (1 - u)) * (a' ^ 2 * (1 - v))| ≤ 2 * (1 / 64) := by
      rw [mul_assoc, abs_mul]; exact mul_le_mul hc hh12 (abs_nonneg _) (by norm_num)
    have t2 : |q ^ 2 * a' ^ 2 * u * v| ≤ 1 * (81 / 64) := by
      rw [show q ^ 2 * a' ^ 2 * u * v = (q ^ 2 * a' ^ 2) * (u * v) by ring, abs_mul,
        abs_of_nonneg (mul_nonneg (sq_nonneg q) (sq_nonneg a'))]
      have : q ^ 2 * a' ^ 2 ≤ 1 := by
        have := mul_le_mul hq2 ha2 (sq_nonneg _) zero_le_one; linarith
      exact mul_le_mul this huv (abs_nonneg _) zero_le_one
    have := abs_add_le (q ^ 2 * a' ^ 2 * u * v) (c * (q ^ 2 * (1 - u)) * (a' ^ 2 * (1 - v)))
    linarith
  · unfold mt01
    have t1 : |c * (q ^ 2 * (1 - u)) * (a' ^ 2 * (1 - v))| ≤ 2 * (1 / 64) := by
      rw [mul_assoc, abs_mul]; exact mul_le_mul hc hh12 (abs_nonneg _) (by norm_num)
    have t2 : |q ^ 2 * a' ^ 2 * u * v| ≤ 1 * (81 / 64) := by
      rw [show q ^ 2 * a' ^ 2 * u * v = (q ^ 2 * a' ^ 2) * (u * v) by ring, abs_mul,
        abs_of_nonneg (mul_nonneg (sq_nonneg q) (sq_nonneg a'))]
      have : q ^ 2 * a' ^ 2 ≤ 1 := by
        have := mul_le_mul hq2 ha2 (sq_nonneg _) zero_le_one; linarith
      exact mul_le_mul this huv (abs_nonneg _) zero_le_one
    have := abs_add_le (q ^ 2 * a' ^ 2 * u * v) (c * (q ^ 2 * (1 - u)) * (a' ^ 2 * (1 - v)))
    linarith
  · unfold mt11
    have t1 : |c * (a' ^ 2 * (1 - v)) ^ 2| ≤ 2 * (1 / 64) := by
      rw [abs_mul, abs_sq]
      exact mul_le_mul hc hh2 (sq_nonneg _) (by norm_num)
    have t2 : |a' ^ 4 * v ^ 2| ≤ 1 * (81 / 64) := by
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul ha4 hv2' (sq_nonneg _) zero_le_one
    have := abs_add_le (a' + a' ^ 4 * v ^ 2) (c * (a' ^ 2 * (1 - v)) ^ 2)
    have := abs_add_le a' (a' ^ 4 * v ^ 2)
    linarith

/-! ### The slice bound (M4.2 + M4.3) -/

theorem continuous_quadForm (M : Matrix (Fin 2) (Fin 2) ℝ) (L : Fin 2 → ℝ) (k : ℝ) :
    Continuous (quadForm M L k) := by
  unfold quadForm; simp only [dotProduct, mulVec, Fin.sum_univ_two]; fun_prop

/-- `S₁ = ∑ₙ e^{-n}(n+1)`. -/
noncomputable def S1 : ℝ := ∑' n : ℕ, Real.exp (-n) * ((n : ℝ) + 1) ^ 1

theorem S1_pos : 0 < S1 := by
  unfold S1
  refine (summable_exp_neg_mul_pow 1).tsum_pos (fun n => by positivity) 0 (by simp)

/-- The slice constant. -/
noncomputable def Kslice (ε : ℝ) : ℝ := M2const 3 ε * S1

theorem Kslice_pos {ε : ℝ} (hε : 0 < ε) : 0 < Kslice ε :=
  mul_pos (M2const_pos (by norm_num) hε) S1_pos

theorem isqrt_eq_of_ne {D : ℝ} (hD : D ≠ 0) : isqrt D = ENNReal.ofReal (1 / √|D|) := by
  unfold isqrt
  rw [ENNReal.ofReal_rpow_of_pos (abs_pos.mpr hD)]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_neg (abs_nonneg _), inv_eq_one_div]

theorem isqrt_zero : isqrt 0 = ⊤ := by
  unfold isqrt; simp [ENNReal.zero_rpow_of_neg (by norm_num : -(1 / 2 : ℝ) < 0)]

/-- **Slice bound**: for a symmetric `M` with entries `≤ 3`, any `L, k`, `0 < |a_p| ≤ 1`, `N ≥ 1`,
`∫_{square} e^{-N (a_p Q)²} ≤ K N^{-1/2} |a_p|⁻¹ (1 + log N) |det M|^{-1/2}`. -/
theorem slice_bound {ε N : ℝ} (hε : 0 < ε) (hN : 1 ≤ N) {ap : ℝ} (hap : ap ≠ 0)
    (hap1 : |ap| ≤ 1) (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.IsSymm) (hMb : ∀ i j, |M i j| ≤ 3)
    (L : Fin 2 → ℝ) (k : ℝ) :
    ∫⁻ β in square 0 ε, ENNReal.ofReal (Real.exp (-(N * (ap * quadForm M L k β) ^ 2))) ≤
      ENNReal.ofReal (Kslice ε * N ^ (-(1 / 2 : ℝ)) * |ap|⁻¹ * (1 + Real.log N)) *
        isqrt M.det := by
  have hN0 : 0 < N := by linarith
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hap0 : 0 < |ap| := abs_pos.mpr hap
  have hcoef : 0 < Kslice ε * N ^ (-(1 / 2 : ℝ)) * |ap|⁻¹ * (1 + Real.log N) := by
    have := Kslice_pos hε; positivity
  by_cases hD : M.det = 0
  · rw [hD, isqrt_zero, ENNReal.mul_top (by simpa using hcoef)]; exact le_top
  set D := M.det
  have hsD : 0 < √|D| := Real.sqrt_pos.mpr (abs_pos.mpr hD)
  set K := M2const 3 ε * (N ^ (-(1 / 2 : ℝ)) * |ap|⁻¹ * (1 + Real.log N)) / √|D|
  have hK : 0 ≤ K := by have := M2const_pos (by norm_num : (0:ℝ) ≤ 3) hε; positivity
  set g : (Fin 2 → ℝ) → ℝ := fun β => N * (ap * quadForm M L k β) ^ 2
  have hg : Measurable g := (continuous_const.mul
    ((continuous_const.mul (continuous_quadForm M L k)).pow 2)).measurable
  have hsq_meas : MeasurableSet (square (0 : Fin 2 → ℝ) ε) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hsub : ∀ n : ℕ, (volume.restrict (square 0 ε)) {β | g β ≤ n + 1} ≤
      ENNReal.ofReal (K * ((n : ℝ) + 1) ^ 1) := by
    intro n
    set σ := √(((n : ℝ) + 1) / N) / |ap|
    have hσ : 0 < σ := by positivity
    rw [Measure.restrict_apply (measurableSet_le hg measurable_const)]
    have hset : {β | g β ≤ n + 1} ∩ square 0 ε ⊆ {β | β ∈ square 0 ε ∧ |quadForm M L k β| ≤ σ} := by
      rintro β ⟨hβ, hβs⟩
      refine ⟨hβs, ?_⟩
      simp only [g, mem_ofPred_eq] at hβ
      have h2 : quadForm M L k β ^ 2 ≤ ((n : ℝ) + 1) / N / ap ^ 2 := by
        rw [le_div_iff₀ (by positivity), le_div_iff₀ hN0]; nlinarith
      calc |quadForm M L k β| = √(quadForm M L k β ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ √(((n : ℝ) + 1) / N / ap ^ 2) := Real.sqrt_le_sqrt h2
        _ = σ := by rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq_eq_abs]
    refine (measure_mono hset).trans ((lemmaM2_explicit (by norm_num) hε M hM hMb hD L k 0 hσ).trans
      (ENNReal.ofReal_le_ofReal ?_))
    -- σ (1 + log⁺(1/σ)) ≤ (n+1) N^{-1/2} |ap|⁻¹ (1 + log N)
    have hσe : σ = √((n : ℝ) + 1) * (N ^ (-(1 / 2 : ℝ)) * |ap|⁻¹) := by
      simp only [σ]
      rw [Real.sqrt_div' _ hN0.le, Real.sqrt_eq_rpow N, Real.rpow_neg hN0.le]; ring
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hsqn : √((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hlog : Real.posLog (1 / σ) ≤ Real.log N := by
      have h1σ : 1 / σ ≤ √N := by
        rw [div_le_iff₀ hσ, hσe]
        have hN2 : N ^ (-(1 / 2 : ℝ)) = 1 / √N := by
          rw [Real.sqrt_eq_rpow, Real.rpow_neg hN0.le, inv_eq_one_div]
        rw [hN2]
        have hsN : 0 < √N := Real.sqrt_pos.mpr hN0
        have : √N * (√((n : ℝ) + 1) * (1 / √N * |ap|⁻¹)) = √((n : ℝ) + 1) * |ap|⁻¹ := by
          field_simp
        rw [this]
        have h1 : 1 ≤ √((n : ℝ) + 1) := by rw [Real.one_le_sqrt]; exact hn1
        have h2 : 1 ≤ |ap|⁻¹ := one_le_inv₀ hap0 |>.mpr hap1
        nlinarith
      have hσi : 0 < 1 / σ := by positivity
      have h1σ0 : -1 ≤ 1 / σ := by linarith
      calc Real.posLog (1 / σ) ≤ Real.posLog √N := Real.posLog_le_posLog h1σ0 h1σ
        _ = Real.log N / 2 := by
            have h1N : 1 ≤ |√N| := by
              rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact Real.one_le_sqrt.mpr hN
            rw [Real.posLog_eq_log h1N, Real.log_sqrt hN0.le]
        _ ≤ Real.log N := by linarith
    have hM2 := M2const_pos (by norm_num : (0:ℝ) ≤ 3) hε
    have hA : 0 ≤ N ^ (-(1 / 2 : ℝ)) * |ap|⁻¹ := by positivity
    have key : M2const 3 ε * (σ * (1 + Real.posLog (1 / σ))) ≤
        M2const 3 ε * ((((n : ℝ) + 1) * (N ^ (-(1 / 2 : ℝ)) * |ap|⁻¹)) * (1 + Real.log N)) := by
      apply mul_le_mul_of_nonneg_left _ hM2.le
      have hP := Real.posLog_nonneg (x := 1 / σ)
      apply mul_le_mul (by rw [hσe]; exact mul_le_mul_of_nonneg_right hsqn hA) (by linarith)
        (by linarith) (by positivity)
    calc _ = M2const 3 ε * (σ * (1 + Real.posLog (1 / σ))) / √|M.det| := by simp only [σ]
      _ ≤ M2const 3 ε * ((((n : ℝ) + 1) * (N ^ (-(1 / 2 : ℝ)) * |ap|⁻¹)) * (1 + Real.log N)) /
          √|M.det| := div_le_div_of_nonneg_right key hsD.le
      _ = K * ((n : ℝ) + 1) ^ 1 := by simp only [K, D]; ring
  have hgnn : ∀ β, 0 ≤ g β := fun β => by positivity
  have := lintegral_exp_neg_le_of_sublevel hg hgnn hK 1 hsub
  refine this.trans ?_
  rw [isqrt_eq_of_ne hD, ← ENNReal.ofReal_mul hcoef.le]
  apply ENNReal.ofReal_le_ofReal
  simp only [K, Kslice, S1]
  apply le_of_eq; field_simp

/-! ### Lemma M4 -/

theorem lintegral_gaussian {N : ℝ} (hN : 0 < N) :
    ∫⁻ ζ, ENNReal.ofReal (Real.exp (-(N * ζ ^ 2))) = ENNReal.ofReal (√(Real.pi / N)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_gaussian N]; congr 1; funext ζ; ring_nf
  · have := integrable_exp_neg_mul_sq hN
    exact this.congr (Eventually.of_forall fun ζ => by simp only; ring_nf)
  · exact Eventually.of_forall fun ζ => (Real.exp_pos _).le

/-- The slice reduction in existential form: on the slice `Z = ζ`, `G` is `a_p` times a
quadratic form with matrix `M̃`, for some `L, k` depending only on `ζ` (and the constants). -/
theorem slice_exists {ap ai aj yp yi yj γ κ : ℝ} (hap : ap ≠ 0) (hyp : yp ≠ 0) (hγ : γ ≠ 0)
    (ζ : ℝ) : ∃ (L : Fin 2 → ℝ) (k : ℝ), ∀ β : Fin 2 → ℝ,
      let bp := (ζ - (ai ^ 2 * yi * β 0 + aj ^ 2 * yj * β 1 + κ)) / (ap ^ 2 * yp)
      ap * bp ^ 2 + ai * β 0 ^ 2 + aj * β 1 ^ 2 +
        (ap ^ 2 * bp + ai ^ 2 * β 0 + aj ^ 2 * β 1) ^ 2 / γ =
      ap * quadForm (Mt (ai / ap) (aj / ap) (yi / yp) (yj / yp) (ap ^ 3 / γ)) L k β := by
  refine ⟨![-(2 * (ζ - κ) / (ap ^ 2 * yp)) * ((ai / ap) ^ 2 * (yi / yp)) +
        2 * (ζ - κ) * ap / (yp * γ) * ((ai / ap) ^ 2 * (1 - yi / yp)),
      -(2 * (ζ - κ) / (ap ^ 2 * yp)) * ((aj / ap) ^ 2 * (yj / yp)) +
        2 * (ζ - κ) * ap / (yp * γ) * ((aj / ap) ^ 2 * (1 - yj / yp))],
    (ζ - κ) ^ 2 / (ap ^ 4 * yp ^ 2) + (ζ - κ) ^ 2 / (ap * yp ^ 2 * γ), fun β => ?_⟩
  intro bp
  have h := (slice_reduction (ζ := ζ) (κ := κ) (ai := ai) (aj := aj) (yi := yi) (yj := yj)
    hap hyp hγ β).2
  have e : bp = (ζ - κ - ai ^ 2 * yi * β 0 - aj ^ 2 * yj * β 1) / (ap ^ 2 * yp) := by
    simp only [bp]; ring
  rw [e]; exact h

/-- The M4 constant. -/
noncomputable def CM4 (ε : ℝ) : ℝ := 2 * √Real.pi * Kslice ε

theorem M4_final_ineq {ε N ap Ai : ℝ} (hε : 0 < ε) (hN0 : 0 < N) (hlN : 0 ≤ Real.log N)
    (hap0 : 0 < |ap|) (hAinv : |Ai| ≤ 2 * |ap|⁻¹ ^ 2) :
    |Ai| * √(Real.pi / N) * (Kslice ε * N ^ (-(1 / 2 : ℝ)) * |ap|⁻¹ * (1 + Real.log N)) ≤
      CM4 ε * N⁻¹ * |ap|⁻¹ ^ 3 * (1 + Real.log N) := by
  have hKs := Kslice_pos hε
  have hpi : √(Real.pi / N) = √Real.pi * N ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_div' _ hN0.le, Real.sqrt_eq_rpow N, Real.rpow_neg hN0.le, div_eq_mul_inv]
  have hNN : N ^ (-(1 / 2 : ℝ)) * N ^ (-(1 / 2 : ℝ)) = N⁻¹ := by
    rw [← Real.rpow_add hN0]; norm_num; exact Real.rpow_neg_one N
  rw [hpi]
  have hB : 0 ≤ √Real.pi * N ^ (-(1 / 2 : ℝ)) * (Kslice ε * N ^ (-(1 / 2 : ℝ)) * |ap|⁻¹ *
      (1 + Real.log N)) := by positivity
  calc |Ai| * (√Real.pi * N ^ (-(1 / 2 : ℝ))) *
        (Kslice ε * N ^ (-(1 / 2 : ℝ)) * |ap|⁻¹ * (1 + Real.log N))
      = |Ai| * (√Real.pi * N ^ (-(1 / 2 : ℝ)) *
        (Kslice ε * N ^ (-(1 / 2 : ℝ)) * |ap|⁻¹ * (1 + Real.log N))) := by ring
    _ ≤ 2 * |ap|⁻¹ ^ 2 * (√Real.pi * N ^ (-(1 / 2 : ℝ)) *
        (Kslice ε * N ^ (-(1 / 2 : ℝ)) * |ap|⁻¹ * (1 + Real.log N))) :=
        mul_le_mul_of_nonneg_right hAinv hB
    _ = 2 * √Real.pi * Kslice ε * (N ^ (-(1 / 2 : ℝ)) * N ^ (-(1 / 2 : ℝ))) *
        (|ap|⁻¹ ^ 2 * |ap|⁻¹) * (1 + Real.log N) := by ring
    _ = CM4 ε * N⁻¹ * |ap|⁻¹ ^ 3 * (1 + Real.log N) := by
        rw [hNN, ← pow_succ]; unfold CM4; ring


set_option maxHeartbeats 1000000 in
/-- **Lemma M4** (M8, second bound). Pivot coordinate first: `b = (b_p, (b_i, b_j))`. For
`0 < |a_p| ≤ ε ≤ 1`, `|a_i|, |a_j| ≤ |a_p|`, weights within `1/20` of `1`, any shift `κ`, and
`N ≥ 1`:
`∫_{[-ε,ε]³} e^{-N(Z² + G²)} ≤ C_ε N⁻¹ |a_p|⁻³ (1 + log N) |D|^{-1/2}`, `D = q a' E`. -/
theorem lemmaM4 {ε N : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hN : 1 ≤ N)
    {ap ai aj yp yi yj γ κ : ℝ} (hap : ap ≠ 0) (hapε : |ap| ≤ ε) (hai : |ai| ≤ |ap|)
    (haj : |aj| ≤ |ap|) (hyp : |yp - 1| ≤ 1 / 20) (hyi : |yi - 1| ≤ 1 / 20)
    (hyj : |yj - 1| ≤ 1 / 20) (hγ : |γ - 1| ≤ 1 / 20) :
    ∫⁻ b in Icc (-ε) ε ×ˢ square 0 ε, ENNReal.ofReal (Real.exp (-(N *
      ((ap ^ 2 * yp * b.1 + ai ^ 2 * yi * b.2 0 + aj ^ 2 * yj * b.2 1 + κ) ^ 2 +
       (ap * b.1 ^ 2 + ai * b.2 0 ^ 2 + aj * b.2 1 ^ 2 +
         (ap ^ 2 * b.1 + ai ^ 2 * b.2 0 + aj ^ 2 * b.2 1) ^ 2 / γ) ^ 2)))) ≤
      ENNReal.ofReal (CM4 ε * N⁻¹ * |ap|⁻¹ ^ 3 * (1 + Real.log N)) *
        isqrt (ai / ap * (aj / ap) * EM9 (ai / ap) (aj / ap) (yi / yp) (yj / yp) (ap ^ 3 / γ)) := by
  -- constants and ranges
  have hN0 : 0 < N := by linarith
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hap0 : 0 < |ap| := abs_pos.mpr hap
  have hyp0 : 19 / 20 ≤ yp := by linarith [(abs_le.mp hyp).1]
  have hγ0 : 19 / 20 ≤ γ := by linarith [(abs_le.mp hγ).1]
  have hyp' : yp ≠ 0 := by linarith
  have hγ' : γ ≠ 0 := by linarith
  set q := ai / ap
  set a' := aj / ap
  set u := yi / yp
  set v := yj / yp
  set c := ap ^ 3 / γ
  have hq : |q| ≤ 1 := by simp only [q]; rw [abs_div, div_le_one hap0]; exact hai
  have ha' : |a'| ≤ 1 := by simp only [a']; rw [abs_div, div_le_one hap0]; exact haj
  have huv : ∀ y, |y - 1| ≤ 1 / 20 → |y / yp - 1| ≤ 1 / 8 := by
    intro y hy
    have hyp1 : (0 : ℝ) < yp := by linarith
    rw [show y / yp - 1 = (y - yp) / yp by field_simp, abs_div, abs_of_pos hyp1,
      div_le_iff₀ hyp1]
    have := abs_sub_le y 1 yp
    rw [abs_sub_comm 1 yp] at this
    linarith
  have hc : |c| ≤ 2 := by
    simp only [c]
    rw [abs_div, abs_pow, abs_of_pos (by linarith : (0:ℝ) < γ), div_le_iff₀ (by linarith)]
    have : |ap| ^ 3 ≤ 1 := pow_le_one₀ hap0.le (hapε.trans hε1)
    linarith
  have hMb := Mt_entries hq ha' (huv yi hyi) (huv yj hyj) hc
  have hdet : (Mt q a' u v c).det = q * a' * EM9 q a' u v c := det_Mt q a' u v c
  have hap1 : |ap| ≤ 1 := hapε.trans hε1
  -- the integrand as a function of (b_p, β); opaque names to keep elaboration cheap
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ap ^ 2 * yp := ⟨_, rfl⟩
  have hA : A ≠ 0 := by rw [hAdef]; positivity
  obtain ⟨cβ, hcβdef⟩ : ∃ cβ : (Fin 2 → ℝ) → ℝ,
      cβ = fun β => ai ^ 2 * yi * β 0 + aj ^ 2 * yj * β 1 + κ := ⟨_, rfl⟩
  have hcβm : Measurable cβ := by rw [hcβdef]; fun_prop
  obtain ⟨Gx, hGxdef⟩ : ∃ Gx : ℝ → (Fin 2 → ℝ) → ℝ, Gx = fun bp β =>
      ap * bp ^ 2 + ai * β 0 ^ 2 + aj * β 1 ^ 2 +
        (ap ^ 2 * bp + ai ^ 2 * β 0 + aj ^ 2 * β 1) ^ 2 / γ := ⟨_, rfl⟩
  have hGxm : Measurable (Function.uncurry Gx) := by rw [hGxdef]; fun_prop
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : (Fin 2 → ℝ) → ℝ → ENNReal, Φ = fun β ζ =>
      ENNReal.ofReal (Real.exp (-(N * ζ ^ 2))) *
        ENNReal.ofReal (Real.exp (-(N * Gx ((ζ - cβ β) / A) β ^ 2))) := ⟨_, rfl⟩
  have hΦm : Measurable (Function.uncurry Φ) := by
    rw [hΦdef]
    have h1 : Measurable fun p : (Fin 2 → ℝ) × ℝ => Gx ((p.2 - cβ p.1) / A) p.1 :=
      hGxm.comp (((measurable_snd.sub (hcβm.comp measurable_fst)).div_const A).prodMk
        measurable_fst)
    exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_snd.pow_const 2).const_mul N).neg)).mul
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((h1.pow_const 2).const_mul N).neg))
  have hpt : ∀ b : ℝ × (Fin 2 → ℝ), ENNReal.ofReal (Real.exp (-(N *
      ((ap ^ 2 * yp * b.1 + ai ^ 2 * yi * b.2 0 + aj ^ 2 * yj * b.2 1 + κ) ^ 2 +
       (ap * b.1 ^ 2 + ai * b.2 0 ^ 2 + aj * b.2 1 ^ 2 +
         (ap ^ 2 * b.1 + ai ^ 2 * b.2 0 + aj ^ 2 * b.2 1) ^ 2 / γ) ^ 2)))) =
      Φ b.2 (A * b.1 + cβ b.2) := by
    intro b
    have hbp : (A * b.1 + cβ b.2 - cβ b.2) / A = b.1 := by
      rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hA]
    rw [hΦdef]
    simp only [hbp]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, hGxdef, hcβdef, hAdef]
    congr 2; ring
  refine (lintegral_congr fun b => hpt b).trans_le ?_
  have hFm : Measurable fun z : ℝ × (Fin 2 → ℝ) => Φ z.2 (A * z.1 + cβ z.2) :=
    hΦm.comp (measurable_snd.prodMk ((measurable_const.mul measurable_fst).add
      (hcβm.comp measurable_snd)))
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_symm (fun z : ℝ × (Fin 2 → ℝ) => Φ z.2 (A * z.1 + cβ z.2)) hFm.aemeasurable]
  -- the slice bound, uniform in ζ
  set SB := ENNReal.ofReal (Kslice ε * N ^ (-(1 / 2 : ℝ)) * |ap|⁻¹ * (1 + Real.log N)) *
    isqrt (q * a' * EM9 q a' u v c)
  have hslice : ∀ ζ, ∫⁻ β in square 0 ε, Φ β ζ ≤ ENNReal.ofReal (Real.exp (-(N * ζ ^ 2))) * SB := by
    intro ζ
    obtain ⟨L, k, hLk⟩ := slice_exists (κ := κ) (ai := ai) (aj := aj) (yi := yi) (yj := yj)
      hap hyp' hγ' ζ
    have hG : ∀ β, Gx ((ζ - cβ β) / A) β = ap * quadForm (Mt q a' u v c) L k β := by
      intro β; rw [← hLk β, hGxdef, hcβdef, hAdef]
    rw [hΦdef]
    have hm : Measurable fun β : Fin 2 → ℝ =>
        ENNReal.ofReal (Real.exp (-(N * Gx ((ζ - cβ β) / A) β ^ 2))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (((hGxm.comp (((measurable_const.sub hcβm).div_const A).prodMk measurable_id)).pow_const
          2).const_mul N).neg)
    rw [lintegral_const_mul _ hm]
    gcongr
    simp_rw [hG]
    calc _ ≤ _ := slice_bound hε hN hap hap1 _ (Mt_isSymm _ _ _ _ _) hMb L k
      _ = SB := by rw [hdet]
  have hinner : ∀ β, ∫⁻ bp in Icc (-ε) ε, Φ β (A * bp + cβ β) ≤
      ENNReal.ofReal |A⁻¹| * ∫⁻ ζ, Φ β ζ := fun β =>
    setLIntegral_comp_affine_le (hΦm.comp (measurable_const.prodMk measurable_id)) hA (cβ β) _
  calc ∫⁻ β in square 0 ε, ∫⁻ bp in Icc (-ε) ε, Φ β (A * bp + cβ β)
      ≤ ∫⁻ β in square 0 ε, ENNReal.ofReal |A⁻¹| * ∫⁻ ζ, Φ β ζ := lintegral_mono hinner
    _ = ENNReal.ofReal |A⁻¹| * ∫⁻ ζ, ∫⁻ β in square 0 ε, Φ β ζ := by
        rw [lintegral_const_mul (f := fun β => ∫⁻ ζ, Φ β ζ) _ hΦm.lintegral_prod_right',
          lintegral_lintegral_swap (f := Φ) hΦm.aemeasurable]
    _ ≤ ENNReal.ofReal |A⁻¹| * ∫⁻ ζ, ENNReal.ofReal (Real.exp (-(N * ζ ^ 2))) * SB := by
        gcongr with ζ; exact hslice ζ
    _ = ENNReal.ofReal |A⁻¹| * (ENNReal.ofReal (√(Real.pi / N)) * SB) := by
        rw [lintegral_mul_const _ (by fun_prop), lintegral_gaussian hN0]
    _ ≤ _ := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _),
          ← ENNReal.ofReal_mul (by positivity)]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        have hAinv : |A⁻¹| ≤ 2 * |ap|⁻¹ ^ 2 := by
          rw [hAdef, abs_inv, abs_mul, abs_pow, sq_abs, abs_of_pos (by linarith : (0:ℝ) < yp),
            mul_inv, inv_pow]
          have : yp⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
          have : 0 ≤ (ap ^ 2)⁻¹ := by positivity
          rw [sq_abs]
          nlinarith
        exact M4_final_ineq hε hN0 hlN hap0 hAinv

/-- **Lemma M4** (M8, first bound): the trivial bound `(2ε)³`. -/
theorem lemmaM4_trivial {ε : ℝ} (hε : 0 < ε) (F : ℝ × (Fin 2 → ℝ) → ℝ) :
    ∫⁻ b in Icc (-ε) ε ×ˢ square 0 ε, ENNReal.ofReal (Real.exp (-(F b) ^ 2)) ≤
      ENNReal.ofReal ((2 * ε) ^ 3) := by
  calc ∫⁻ b in Icc (-ε) ε ×ˢ square 0 ε, ENNReal.ofReal (Real.exp (-(F b) ^ 2))
      ≤ ∫⁻ b in Icc (-ε) ε ×ˢ square 0 ε, 1 := lintegral_mono fun b => by
        rw [← ENNReal.ofReal_one]; apply ENNReal.ofReal_le_ofReal
        rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg (F b)]
    _ = ENNReal.ofReal ((2 * ε) ^ 3) := by
        rw [setLIntegral_one, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
          square, volume_pi_pi]
        simp only [Real.volume_Icc, Fin.prod_univ_two, zero_add, zero_sub]
        rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by nlinarith)]
        congr 1; ring

end VectorSLT
