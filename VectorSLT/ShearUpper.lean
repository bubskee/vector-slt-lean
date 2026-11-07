/-
Brief 03, O1: Theorem M and `ZN1_two_sided` for every two-nonzero-row shear target.

The transfer uses (H2)/(H3) (`shear_normalize`, `prefixNet_conj`, `net_Tfun`) as L2 did for
`propLprime`. Under the conjugation `Φ z = P_τ D z`:
* the input law becomes `μ' = Φ_* μ` (moments: `moments_map`; density: `density_map`, with
  `μ₀' = μ₀ |det Φ⁻¹|` on a cube of half-width `ρ = minᵢ |dᵢ| (hiᵢ - loᵢ)/2` around `Φ(centre)`);
* the loss satisfies `K_A(T⁻¹θ') ≥ m · K'_{A₀}(θ')` with `m = min(d₀⁻², d₁⁻², 1)`
  (`loss_compare`);
* the raw parameters move by the linear automorphism `T` of `ℝ¹⁶` (Jacobian `|det T|⁻¹`);
* the prior bound `π₁` and the cutoff bound `1` are unchanged; the cutoff support radius
  `1/200` becomes `1/(200 (‖T‖ + 1))`.
-/
import VectorSLT.TheoremM
import VectorSLT.GeneralInput

namespace VectorSLT

open MeasureTheory Set Filter Topology

/-! ### The loss integrand: continuity and integrability -/

theorem continuous_err (θ : Raw16) (A : Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) :
    Continuous fun x : Fin 2 → ℝ => net θ x k - layer A x k := by
  obtain ⟨p, -, hp⟩ := error_isPoly (weights θ) A k
  have : (fun x : Fin 2 → ℝ => net θ x k - layer A x k) = fun x => MvPolynomial.eval x p := by
    funext x; rw [hp]; rfl
  rw [this]; exact MvPolynomial.continuous_eval p

theorem continuous_lossInt (θ : Raw16) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Continuous fun x : Fin 2 → ℝ => ∑ k, (net θ x k - layer A x k) ^ 2 :=
  continuous_finsetSum _ fun k _ => (continuous_err θ A k).pow 2

theorem integrable_lossInt (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    (θ : Raw16) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Integrable (fun x => ∑ k, (net θ x k - layer A x k) ^ 2) μ := by
  obtain ⟨C, -, hL2⟩ := l2_le_sup 81 μ hmom
  refine integrable_finsetSum _ fun k _ => ?_
  obtain ⟨p, hpd, hp⟩ := error_isPoly (weights θ) A k
  have h := (hL2 (PolyBox.mk p hpd)).1
  simp only [PolyBox.poly_mk, hp] at h
  exact h

theorem popLossA_nonneg (μ : Measure (Fin 2 → ℝ)) (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) :
    0 ≤ popLossA μ A θ :=
  integral_nonneg fun x => by positivity

/-! ### The input law under `Φ` -/

theorem continuous_Φs (d : Fin 2 → ℝ) (b : Bool) : Continuous (Φs d b) :=
  continuous_pi fun _ => continuous_const.mul (continuous_apply _)

theorem moments_map {μ : Measure (Fin 2 → ℝ)}
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) (d : Fin 2 → ℝ) (b : Bool) :
    ∀ i, Integrable (fun y : Fin 2 → ℝ => |y i| ^ (2 * 81)) (μ.map (Φs d b)) := by
  intro i
  have hm : Measurable fun y : Fin 2 → ℝ => |y i| ^ (2 * 81) := by fun_prop
  rw [integrable_map_measure hm.aestronglyMeasurable (continuous_Φs d b).aemeasurable]
  have : (fun y : Fin 2 → ℝ => |y i| ^ (2 * 81)) ∘ Φs d b =
      fun x => |d (tau b i)| ^ (2 * 81) * |x (tau b i)| ^ (2 * 81) := by
    funext x; simp only [Function.comp, Φs, abs_mul, mul_pow]
  rw [this]; exact (hmom _).const_mul _

/-- `Ψ = Φ⁻¹` as a linear equivalence of `ℝ²`. -/
noncomputable def Ψlin {d : Fin 2 → ℝ} (hd : ∀ i, d i ≠ 0) (b : Bool) :
    (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun := Ψs d b
  invFun := Φs d b
  map_add' x y := by funext i; simp [Ψs, add_div]
  map_smul' c x := by funext i; simp [Ψs, mul_div_assoc]
  left_inv := Φs_Ψs hd b
  right_inv := Ψs_Φs hd b

/-- A density lower bound on a box survives `Φ_*`, on a smaller box around `Φ(centre)`, with
`μ₀' = μ₀ |det Ψ|`. -/
theorem density_map {μ : Measure (Fin 2 → ℝ)} {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i)
    {μ₀ : ℝ} (hμ₀ : 0 < μ₀) (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ)
    {d : Fin 2 → ℝ} (hd : ∀ i, d i ≠ 0) (b : Bool) :
    ∃ lo' hi' : Fin 2 → ℝ, (∀ i, lo' i < hi' i) ∧ ∃ μ₁ : ℝ, 0 < μ₁ ∧
      ENNReal.ofReal μ₁ • volume.restrict (cbox lo' hi') ≤ μ.map (Φs d b) := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 2 → ℝ, c = fun i => (lo i + hi i) / 2 := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min (|d 0| * ((hi 0 - lo 0) / 2)) (|d 1| * ((hi 1 - lo 1) / 2)) :=
    ⟨_, rfl⟩
  have hρ : 0 < ρ := by
    rw [hρdef]
    exact lt_min (mul_pos (abs_pos.mpr (hd 0)) (by linarith [hlh 0]))
      (mul_pos (abs_pos.mpr (hd 1)) (by linarith [hlh 1]))
  have hρi : ∀ i, ρ ≤ |d i| * ((hi i - lo i) / 2) := by
    intro i; rw [hρdef]; fin_cases i; exacts [min_le_left _ _, min_le_right _ _]
  set L := Ψlin hd b
  set J := |LinearMap.det (L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))|
  have hJ : 0 < J := abs_pos.mpr (LinearEquiv.isUnit_det' L).ne_zero
  refine ⟨fun j => Φs d b c j - ρ, fun j => Φs d b c j + ρ, fun j => by linarith, μ₀ * J,
    mul_pos hμ₀ hJ, ?_⟩
  set B' := cbox (fun j => Φs d b c j - ρ) (fun j => Φs d b c j + ρ)
  have hsub : ∀ y ∈ B', Ψs d b y ∈ cbox lo hi := by
    intro y hy
    simp only [B', cbox, Set.mem_univ_pi, mem_Icc] at hy ⊢
    intro i
    have h := hy (tau b i)
    simp only [Φs, tau_tau] at h
    have hab : |y (tau b i) - d i * c i| ≤ |d i| * ((hi i - lo i) / 2) :=
      (abs_sub_le_iff.mpr ⟨by linarith [h.2], by linarith [h.1]⟩).trans (hρi i)
    have e : Ψs d b y i - c i = (y (tau b i) - d i * c i) / d i := by
      simp only [Ψs]; field_simp [hd i]
    have hdi : 0 < |d i| := abs_pos.mpr (hd i)
    have h2 : |Ψs d b y i - c i| ≤ (hi i - lo i) / 2 := by
      rw [e, abs_div, div_le_iff₀ hdi]; linarith [hab]
    rw [abs_le] at h2
    have hci : c i = (lo i + hi i) / 2 := by rw [hc]
    constructor <;> linarith [h2.1, h2.2]
  rw [Measure.le_iff]
  intro s hs
  have hmeas : MeasurableSet (Φs d b ⁻¹' s) := (continuous_Φs d b).measurable hs
  rw [Measure.smul_apply, Measure.restrict_apply hs,
    Measure.map_apply (continuous_Φs d b).measurable hs, smul_eq_mul]
  have himg : (L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) '' (s ∩ B') ⊆ Φs d b ⁻¹' s ∩ cbox lo hi := by
    rintro _ ⟨y, ⟨hys, hyB⟩, rfl⟩
    refine ⟨?_, hsub y hyB⟩
    show Φs d b (Ψs d b y) ∈ s
    rw [Φs_Ψs hd]; exact hys
  have hvol := Measure.addHaar_image_linearMap (volume : Measure (Fin 2 → ℝ))
    (L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) (s ∩ B')
  have h1 := Measure.le_iff'.mp hμ (Φs d b ⁻¹' s)
  rw [Measure.smul_apply, Measure.restrict_apply hmeas, smul_eq_mul] at h1
  calc ENNReal.ofReal (μ₀ * J) * volume (s ∩ B')
      = ENNReal.ofReal μ₀ * (ENNReal.ofReal J * volume (s ∩ B')) := by
        rw [ENNReal.ofReal_mul hμ₀.le, mul_assoc]
    _ = ENNReal.ofReal μ₀ * volume ((L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) '' (s ∩ B')) := by
        rw [hvol]
    _ ≤ ENNReal.ofReal μ₀ * volume (Φs d b ⁻¹' s ∩ cbox lo hi) :=
        mul_le_mul' le_rfl (measure_mono himg)
    _ ≤ μ (Φs d b ⁻¹' s) := h1

/-! ### Loss comparison under the conjugation -/

/-- `K_{μ,A}(T⁻¹θ') ≥ min(d₀⁻², d₁⁻²) · K_{Φ_*μ, A₀}(θ')`. -/
theorem loss_compare {d : Fin 2 → ℝ} (hd : ∀ i, d i ≠ 0) (b : Bool)
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hact : actW d b A = A0) (μ : Measure (Fin 2 → ℝ))
    [IsFiniteMeasure μ] (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    (θ' : Raw16) :
    min ((d 0)⁻¹ ^ 2) ((d 1)⁻¹ ^ 2) * popLossA (μ.map (Φs d b)) A0 θ' ≤
      popLossA μ A (Tinv d b θ') := by
  set θ := Tinv d b θ'
  have hθ' : Tfun d b θ = θ' := (Tlin hd b).apply_symm_apply θ'
  set m := min ((d 0)⁻¹ ^ 2) ((d 1)⁻¹ ^ 2)
  have hm0 : 0 ≤ m := le_min (by positivity) (by positivity)
  have hmj : ∀ j, m * d j ^ 2 ≤ 1 := by
    intro j
    have hle : m ≤ (d j)⁻¹ ^ 2 := by fin_cases j; exacts [min_le_left _ _, min_le_right _ _]
    calc m * d j ^ 2 ≤ (d j)⁻¹ ^ 2 * d j ^ 2 := mul_le_mul_of_nonneg_right hle (sq_nonneg _)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ (hd j), one_pow]
  have hpt : ∀ x, m * ∑ k, (net θ' (Φs d b x) k - layer A0 (Φs d b x) k) ^ 2 ≤
      ∑ k, (net θ x k - layer A x k) ^ 2 := by
    intro x
    have hnet : net θ' (Φs d b x) = Φs d b (net θ x) := by
      rw [← hθ', net_Tfun hd, Ψs_Φs hd]
    have hlay : layer A0 (Φs d b x) = Φs d b (layer A x) := by
      rw [← hact, ← layer_conj hd, Ψs_Φs hd]
    rw [hnet, hlay]
    have key : ∀ j, m * (d j * net θ x j - d j * layer A x j) ^ 2 ≤
        (net θ x j - layer A x j) ^ 2 := by
      intro j
      have : (d j * net θ x j - d j * layer A x j) ^ 2 =
          d j ^ 2 * (net θ x j - layer A x j) ^ 2 := by ring
      rw [this, ← mul_assoc]
      calc m * d j ^ 2 * (net θ x j - layer A x j) ^ 2
          ≤ 1 * (net θ x j - layer A x j) ^ 2 :=
            mul_le_mul_of_nonneg_right (hmj j) (sq_nonneg _)
        _ = _ := one_mul _
    simp only [Φs, Fin.sum_univ_two, mul_add]
    cases b <;> simp only [tau, Bool.false_eq_true, ite_false, ite_true,
      Equiv.swap_apply_left, Equiv.swap_apply_right] <;> linarith [key 0, key 1]
  unfold popLossA
  rw [integral_map (continuous_Φs d b).aemeasurable
    (continuous_lossInt θ' A0).aestronglyMeasurable, ← integral_const_mul]
  exact integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
    (integrable_lossInt μ hmom θ A) (Eventually.of_forall hpt)

theorem baseA_A0 : baseA A0 = θ₀ := by
  simp [baseA, θ₀, A0]; rfl

/-! ### Theorem M for every two-nonzero-row shear target -/

/-- **O1. Theorem M (upper bound) for every rank-one shear target with both rows nonzero.**
There is a support radius `r = 1/(200 (‖T‖+1))`, depending only on `A`, such that for every
input law with finite 162nd moments and a density bounded below on some box, every prior
bounded by `π₁`, and every cutoff bounded by `1` and vanishing outside the sup-norm `r`-ball,
`Z_{N,1} ≤ C N⁻⁴ (log N)⁴` for large `N`. -/
theorem theoremM_shear {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
        Zpos μ A φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4 * Real.log N ^ 4) := by
  obtain ⟨d, b, hd, hact⟩ := shear_normalize hA
  set T := Tlin hd b
  set Tc : Raw16 →L[ℝ] Raw16 := (T.toContinuousLinearEquiv : Raw16 →L[ℝ] Raw16)
  refine ⟨1 / (200 * (‖Tc‖ + 1)), by positivity, ?_⟩
  intro μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ π₁ hπ₁ hφ hχ hχs
  set μ' := μ.map (Φs d b)
  have hmom' := moments_map hmom d b
  obtain ⟨lo', hi', hlh', μ₁, hμ₁, hμ'⟩ := density_map hlh hμ₀ hμ hd b
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = min (min ((d 0)⁻¹ ^ 2) ((d 1)⁻¹ ^ 2)) 1 := ⟨_, rfl⟩
  have hm0 : 0 < m := by
    have h0 := hd 0; have h1 := hd 1
    rw [hmdef]; exact lt_min (lt_min (by positivity) (by positivity)) one_pos
  have hm1 : m ≤ 1 := by rw [hmdef]; exact min_le_right _ _
  have hmle : m ≤ min ((d 0)⁻¹ ^ 2) ((d 1)⁻¹ ^ 2) := by rw [hmdef]; exact min_le_left _ _
  set φ' : Raw16 → ENNReal := fun θ' => φ (T.symm θ')
  set χ' : Raw16 → ENNReal := fun η => χ (T.symm η)
  have hχs' : ∀ η, 1 / 200 < ‖η‖ → χ' η = 0 := by
    intro η hη
    apply hχs
    by_contra hc
    push Not at hc
    have e : Tc (T.symm η) = η := T.apply_symm_apply η
    have h1 : ‖η‖ ≤ ‖Tc‖ * ‖T.symm η‖ := by
      have := Tc.le_opNorm (T.symm η); rwa [e] at this
    have h2 : ‖Tc‖ * ‖T.symm η‖ ≤ ‖Tc‖ * (1 / (200 * (‖Tc‖ + 1))) :=
      mul_le_mul_of_nonneg_left hc (norm_nonneg _)
    have h3 : ‖Tc‖ * (1 / (200 * (‖Tc‖ + 1))) < 1 / 200 := by
      rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [norm_nonneg Tc]
    linarith
  obtain ⟨C, N₀, hup⟩ := theoremM_raw μ' hmom' hlh' hμ₁ hμ' φ' χ' hπ₁ (fun θ => hφ _)
    (fun θ => hχ _) hχs'
  set J := |(LinearMap.det (T : Raw16 →ₗ[ℝ] Raw16))⁻¹|
  have hJ : 0 ≤ J := abs_nonneg _
  set C' := max C 0
  refine ⟨J * C' * m⁻¹ ^ 4, max (N₀ / m) (1 / m), fun N hN => ?_⟩
  have hN0 : N₀ ≤ m * N := by
    have := (le_max_left _ _).trans hN
    rw [div_le_iff₀ hm0] at this; linarith
  have hN1 : 1 ≤ m * N := by
    have := (le_max_right _ _).trans hN
    rw [div_le_iff₀ hm0] at this; linarith
  have hNpos : 0 < N := by
    have : 0 < m * N := by linarith
    exact pos_of_mul_pos_right this hm0.le
  have hbase : T.symm (basePos A0 0) = basePos A 0 := by
    rw [basePos_zero, basePos_zero, baseA_A0, ← Tfun_baseA hact]
    exact T.symm_apply_apply _
  have hint : ∀ θ', ENNReal.ofReal (Real.exp (-(N * popLossA μ A (T.symm θ')))) *
      (φ (T.symm θ') * χ (T.symm θ' - basePos A 0)) ≤
      ENNReal.ofReal (Real.exp (-((m * N) * popLossA μ' A0 θ'))) *
        (φ' θ' * χ' (θ' - basePos A0 0)) := by
    intro θ'
    have hχeq : χ' (θ' - basePos A0 0) = χ (T.symm θ' - basePos A 0) := by
      simp only [χ', map_sub, hbase]
    rw [hχeq]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) le_rfl
    have hc : min ((d 0)⁻¹ ^ 2) ((d 1)⁻¹ ^ 2) * popLossA μ' A0 θ' ≤
        popLossA μ A (T.symm θ') := loss_compare hd b hact μ hmom θ'
    have hK0 : 0 ≤ popLossA μ' A0 θ' := popLossA_nonneg _ _ _
    have : m * popLossA μ' A0 θ' ≤ popLossA μ A (T.symm θ') :=
      le_trans (mul_le_mul_of_nonneg_right hmle hK0) hc
    nlinarith
  calc Zpos μ A φ χ 0 N
      = ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * popLossA μ A θ))) *
          (φ θ * χ (θ - basePos A 0)) := rfl
    _ = ENNReal.ofReal J * ∫⁻ θ', ENNReal.ofReal (Real.exp (-(N * popLossA μ A (T.symm θ')))) *
          (φ (T.symm θ') * χ (T.symm θ' - basePos A 0)) := lintegral_linearEquiv T _
    _ ≤ ENNReal.ofReal J * Zpos μ' A0 φ' χ' 0 (m * N) := mul_le_mul' le_rfl (lintegral_mono hint)
    _ ≤ ENNReal.ofReal J * ENNReal.ofReal (C * (m * N)⁻¹ ^ 4 * Real.log (m * N) ^ 4) :=
        mul_le_mul' le_rfl (hup _ hN0)
    _ ≤ ENNReal.ofReal (J * C' * m⁻¹ ^ 4 * N⁻¹ ^ 4 * Real.log N ^ 4) := by
        rw [← ENNReal.ofReal_mul hJ]
        apply ENNReal.ofReal_le_ofReal
        have hl0 : 0 ≤ Real.log (m * N) := Real.log_nonneg hN1
        have hl1 : Real.log (m * N) ≤ Real.log N :=
          Real.log_le_log (by linarith) (by nlinarith)
        have hl4 := pow_le_pow_left₀ hl0 hl1 4
        have hCC : C ≤ C' := le_max_left _ _
        have hC'0 : 0 ≤ C' := le_max_right _ _
        rw [mul_inv, mul_pow]
        calc J * (C * (m⁻¹ ^ 4 * N⁻¹ ^ 4) * Real.log (m * N) ^ 4)
            ≤ J * (C' * (m⁻¹ ^ 4 * N⁻¹ ^ 4) * Real.log N ^ 4) := by
              apply mul_le_mul_of_nonneg_left _ hJ
              exact mul_le_mul (mul_le_mul_of_nonneg_right hCC (by positivity)) hl4
                (by positivity) (by positivity)
          _ = _ := by ring

/-- **O1 headline. `Z_{N,1} ≍ N⁻⁴ (log N)⁴` for every two-nonzero-row shear target**, for a
compactly supported input law with a density bounded below on some box. -/
theorem ZN1_two_sided_shear {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure μ] {R : ℝ},
      (∀ᵐ x ∂μ, ∀ i, |x i| ≤ R) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ᶠ θ in 𝓝 (basePos A 0), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ c C N₀ : ℝ, 0 < c ∧ ∀ N : ℝ, N₀ ≤ N →
        ENNReal.ofReal (c * N⁻¹ ^ 4 * Real.log N ^ 4) ≤ Zpos μ A φ χ 0 N ∧
          Zpos μ A φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4 * Real.log N ^ 4) := by
  obtain ⟨r, hr, hup⟩ := theoremM_shear hA
  refine ⟨r, hr, ?_⟩
  intro μ _ R hμR lo hi hlh μ₀ hμ₀ hμ φ χ φ₀ χ₀ π₁ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs
  have hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ := by
    intro i
    have hm : Measurable fun x : Fin 2 → ℝ => |x i| ^ (2 * 81) := by fun_prop
    refine Integrable.of_mem_Icc 0 (R ^ (2 * 81)) hm.aemeasurable ?_
    filter_upwards [hμR] with x hx
    exact ⟨by positivity, pow_le_pow_left₀ (abs_nonneg _) (hx i) _⟩
  obtain ⟨c, hc, N₁, hlow⟩ := Zpos_one_lower hA μ hμR φ χ hφ₀ hχ₀ hφl hχl
  obtain ⟨C, N₂, hu⟩ := hup μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs
  exact ⟨c, C, max N₁ N₂, hc, fun N hN =>
    ⟨hlow N ((le_max_left _ _).trans hN), hu N ((le_max_right _ _).trans hN)⟩⟩

end VectorSLT
