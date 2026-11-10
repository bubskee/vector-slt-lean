/-
Loss comparison, part 2: the coordinates `Ψ_p θ = (𝐜(θ), w(θ))` and the change-of-variables bound
(item 1 of the loss brief), at every position `p`.

* `w(θ) = flat (inact p θ)`: the twelve entries of the three inactive blocks, block-major,
  `w (4l + 2i + j) = V_l i j` (`flat`, `unflat`).
* `𝐜(θ) = (c₃⁽⁰⁾, c₂⁽⁰⁾, c₃⁽¹⁾, c₂⁽¹⁾)`: the exact `s³` and `s²t` coefficients of the error
  (`cvec`). They do not depend on the position: `c₃⁽ᵏ⁾ = α_k³ - 1 + P₀⁽ᵏ⁾`,
  `c₂⁽ᵏ⁾ = 3 α_k² ν_k + 3 P₁⁽ᵏ⁾`, with `(α_k, ν_k)` the row form of row `k` of the active block
  and the moments over the three inactive blocks.
* `cov_bound`: for `ρ ≤ 1/2` and every measurable `f ≥ 0`,
  `∫ f(Ψ_p θ) 𝟙_{‖θ - basePos A₀ p‖ ≤ ρ} dθ ≤ J ∫ f`.

The proof is the triangular map of Appendix C ("Active change of variables"): per active row,
`ν ↦ 3α²ν + 3P₁` is affine with slope `3α² ≥ 3/4`, and `α ↦ α³ - 1 + P₀` has derivative
`3α² ≥ 3/4` on `[1/2, 3/2]`. The linear changes of coordinates (`Raw16` to rows and `w`, and
`(ℝ × ℝ)²` to `ℝ⁴`) only cost constants, by uniqueness of Haar measure.
-/
import VectorSLT.LossCompare.Coeffs

namespace VectorSLT.LossCompare

open MeasureTheory Set Filter Metric Topology VectorSLT VectorSLT.LeadingMap VectorSLT.SLT
open scoped ENNReal

/-! ### Haar transport -/

/-- **Linear changes of variables cost a constant**: for a continuous linear equivalence of
finite-dimensional real spaces with additive Haar measures, `∫ g(Lx) dμ = c ∫ g dν`, `c < ∞`. -/
theorem lintegral_comp_clequiv {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X] [FiniteDimensional ℝ X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y] [FiniteDimensional ℝ Y]
    (μ : Measure X) [μ.IsAddHaarMeasure] (ν : Measure Y) [ν.IsAddHaarMeasure] (L : X ≃L[ℝ] Y) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ g : Y → ℝ≥0∞, Measurable g →
      ∫⁻ x, g (L x) ∂μ = c * ∫⁻ y, g y ∂ν := by
  have h := Measure.isAddLeftInvariant_eq_smul (μ.map L) ν
  refine ⟨(Measure.addHaarScalarFactor (μ.map L) ν : ℝ≥0∞), ENNReal.coe_ne_top, fun g hg => ?_⟩
  have e : ∫⁻ y, g y ∂(μ.map L) =
      ∫⁻ y, g y ∂(Measure.addHaarScalarFactor (μ.map L) ν • ν) :=
    congrArg (fun m : Measure Y => ∫⁻ y, g y ∂m) h
  rw [← lintegral_map hg L.continuous.measurable, e, lintegral_smul_measure]
  rfl

/-! ### One active row -/

/-- The row map `(α, ν) ↦ (α³ - 1 + A, 3α²ν + 3B)`. -/
def rmap (A B : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (z.1 ^ 3 - 1 + A, 3 * z.1 ^ 2 * z.2 + 3 * B)

/-- The active interval `[1/2, 3/2]`. -/
def Iact : Set ℝ := Icc (1 / 2) (3 / 2)

theorem inv_slope_le {α : ℝ} (hα : α ∈ Iact) :
    ENNReal.ofReal |(3 * α ^ 2)⁻¹| ≤ ENNReal.ofReal (4 / 3) := by
  apply ENNReal.ofReal_le_ofReal
  have h1 : (3 : ℝ) / 4 ≤ 3 * α ^ 2 := by nlinarith [hα.1]
  rw [abs_of_pos (by positivity)]
  calc (3 * α ^ 2)⁻¹ ≤ (3 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h1
    _ = 4 / 3 := by norm_num

/-- **One active row**: `∫_{α ∈ [1/2, 3/2]} ∫_ν h(α³ - 1 + A, 3α²ν + 3B) ≤ (16/9) ∫ h`. -/
theorem row_bound (A B : ℝ) {h : ℝ × ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ z in Iact ×ˢ univ, h (rmap A B z) ≤ ENNReal.ofReal (16 / 9) * ∫⁻ z, h z := by
  set H : ℝ → ℝ≥0∞ := fun u => ∫⁻ v, h (u, v)
  have hH : Measurable H := hh.lintegral_prod_right'
  have hcomp : Measurable fun z : ℝ × ℝ => h (rmap A B z) := hh.comp (by unfold rmap; fun_prop)
  rw [Measure.volume_eq_prod, setLIntegral_prod _ hcomp.aemeasurable]
  simp only [Measure.restrict_univ, rmap]
  -- the `ν`-integral
  have hin : ∀ α ∈ Iact, ∫⁻ ν, h (α ^ 3 - 1 + A, 3 * α ^ 2 * ν + 3 * B) ≤
      ENNReal.ofReal (4 / 3) * H (α ^ 3 - 1 + A) := by
    intro α hα
    have ha : (3 * α ^ 2) ≠ 0 := by have := hα.1; positivity
    rw [lintegral_comp_affine (f := fun v => h (α ^ 3 - 1 + A, v))
      (hh.comp measurable_prodMk_left) ha]
    exact mul_le_mul' (inv_slope_le hα) le_rfl
  -- the `α`-integral
  have himg := lintegral_image_eq_lintegral_abs_deriv_mul (s := Iact) (f := fun x => x ^ 3)
    (f' := fun x => 3 * x ^ 2) measurableSet_Icc
    (fun x _ => by simpa using (hasDerivAt_pow 3 x).hasDerivWithinAt)
    ((Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)).injective.injOn)
    (fun u => H (u + (-1 + A)))
  have hout : ∫⁻ α in Iact, H (α ^ 3 - 1 + A) ≤ ENNReal.ofReal (4 / 3) * ∫⁻ u, H u := by
    calc ∫⁻ α in Iact, H (α ^ 3 - 1 + A)
        ≤ ∫⁻ α in Iact, ENNReal.ofReal (4 / 3) *
            (ENNReal.ofReal |3 * α ^ 2| * H (α ^ 3 + (-1 + A))) := by
          refine setLIntegral_mono' measurableSet_Icc fun α hα => ?_
          have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (4 / 3) * ENNReal.ofReal |3 * α ^ 2| := by
            rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one]
            apply ENNReal.ofReal_le_ofReal
            rw [abs_of_nonneg (by positivity)]
            nlinarith [hα.1]
          calc H (α ^ 3 - 1 + A) = 1 * H (α ^ 3 + (-1 + A)) := by rw [one_mul]; ring_nf
            _ ≤ (ENNReal.ofReal (4 / 3) * ENNReal.ofReal |3 * α ^ 2|) *
                H (α ^ 3 + (-1 + A)) := by gcongr
            _ = _ := mul_assoc _ _ _
      _ = ENNReal.ofReal (4 / 3) * ∫⁻ u in (fun x : ℝ => x ^ 3) '' Iact, H (u + (-1 + A)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, himg]
      _ ≤ ENNReal.ofReal (4 / 3) * ∫⁻ u, H (u + (-1 + A)) :=
          mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
      _ = ENNReal.ofReal (4 / 3) * ∫⁻ u, H u := by
          rw [lintegral_add_right_eq_self H (-1 + A)]
  calc ∫⁻ α in Iact, ∫⁻ ν, h (α ^ 3 - 1 + A, 3 * α ^ 2 * ν + 3 * B)
      ≤ ∫⁻ α in Iact, ENNReal.ofReal (4 / 3) * H (α ^ 3 - 1 + A) :=
        setLIntegral_mono' measurableSet_Icc hin
    _ = ENNReal.ofReal (4 / 3) * ∫⁻ α in Iact, H (α ^ 3 - 1 + A) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (4 / 3) * (ENNReal.ofReal (4 / 3) * ∫⁻ u, H u) := by gcongr
    _ = ENNReal.ofReal (16 / 9) * ∫⁻ z, h z := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num), Measure.volume_eq_prod,
          lintegral_prod _ hh.aemeasurable]
        congr 2
        norm_num

/-! ### Two active rows and the inactive coordinates -/

/-- `(ℝ × ℝ)² ≅ ℝ⁴`, `((a, b), (c, d)) ↦ (a, b, c, d)`. -/
noncomputable def K4 : ((ℝ × ℝ) × (ℝ × ℝ)) ≃L[ℝ] (Fin 4 → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z => ![z.1.1, z.1.2, z.2.1, z.2.2]
      invFun := fun c => ((c 0, c 1), (c 2, c 3))
      map_add' := fun z z' => by funext i; fin_cases i <;> rfl
      map_smul' := fun r z => by funext i; fin_cases i <;> rfl
      left_inv := fun z => rfl
      right_inv := fun c => by funext i; fin_cases i <;> rfl }

theorem K4_apply (z : (ℝ × ℝ) × (ℝ × ℝ)) : K4 z = ![z.1.1, z.1.2, z.2.1, z.2.2] := rfl

/-- The intermediate coordinates: the two active rows `(α_k, ν_k)` and the inactive `w`. -/
abbrev Yc := ((ℝ × ℝ) × (ℝ × ℝ)) × (Fin 12 → ℝ)

instance instAddHaarYc : (volume : Measure Yc).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _

/-- Both active rows in `[1/2, 3/2] × ℝ`. -/
def actSet : Set ((ℝ × ℝ) × (ℝ × ℝ)) := (Iact ×ˢ univ) ×ˢ (Iact ×ˢ univ)

/-- The triangular map, rowwise, with moments `P₀ = P0 w`, `P₁ = P1 w` depending on `w`. -/
noncomputable def Φmap (P0 P1 : (Fin 12 → ℝ) → Fin 2 → ℝ) (y : Yc) : (Fin 4 → ℝ) × (Fin 12 → ℝ) :=
  (K4 (rmap (P0 y.2 0) (P1 y.2 0) y.1.1, rmap (P0 y.2 1) (P1 y.2 1) y.1.2), y.2)

theorem continuous_rmap : Continuous fun q : (ℝ × ℝ) × (ℝ × ℝ) => rmap q.1.1 q.1.2 q.2 := by
  unfold rmap; fun_prop

theorem continuous_Φmap {P0 P1 : (Fin 12 → ℝ) → Fin 2 → ℝ} (hP0 : Continuous P0)
    (hP1 : Continuous P1) : Continuous (Φmap P0 P1) := by
  have hr : ∀ k : Fin 2, ∀ g : Yc → ℝ × ℝ, Continuous g →
      Continuous fun y : Yc => rmap (P0 y.2 k) (P1 y.2 k) (g y) := by
    intro k g hg
    exact continuous_rmap.comp (((continuous_apply k).comp (hP0.comp continuous_snd)).prodMk
      ((continuous_apply k).comp (hP1.comp continuous_snd)) |>.prodMk hg)
  unfold Φmap
  exact (K4.continuous.comp ((hr 0 _ (continuous_fst.comp continuous_fst)).prodMk
    (hr 1 _ (continuous_snd.comp continuous_fst)))).prodMk continuous_snd

/-- **Both active rows, for every `w`**: `∫_{actSet × ℝ¹²} f(Φ y) dy ≤ C ∫ f`. -/
theorem active_cov {P0 P1 : (Fin 12 → ℝ) → Fin 2 → ℝ} (hP0 : Continuous P0)
    (hP1 : Continuous P1) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : (Fin 4 → ℝ) × (Fin 12 → ℝ) → ℝ≥0∞, Measurable f →
      ∫⁻ y in actSet ×ˢ (univ : Set (Fin 12 → ℝ)), f (Φmap P0 P1 y) ≤ C * ∫⁻ x, f x := by
  obtain ⟨cK, hcK, hK⟩ := lintegral_comp_clequiv volume volume K4
  refine ⟨ENNReal.ofReal (16 / 9) * ENNReal.ofReal (16 / 9) * cK,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hcK,
    fun f hf => ?_⟩
  have hΦ := continuous_Φmap hP0 hP1
  -- the inner bound, for fixed `w`
  have hw : ∀ w : Fin 12 → ℝ, ∫⁻ z in actSet, f (Φmap P0 P1 (z, w)) ≤
      ENNReal.ofReal (16 / 9) * ENNReal.ofReal (16 / 9) * cK * ∫⁻ c, f (c, w) := by
    intro w
    set r0 := rmap (P0 w 0) (P1 w 0)
    set r1 := rmap (P0 w 1) (P1 w 1)
    have hfw : Measurable fun x : (ℝ × ℝ) × (ℝ × ℝ) => f (K4 x, w) :=
      hf.comp ((K4.continuous.measurable).prodMk measurable_const)
    set G : ℝ × ℝ → ℝ≥0∞ := fun x0 => ∫⁻ x1, f (K4 (x0, x1), w)
    have hG : Measurable G := hfw.lintegral_prod_right'
    have hm : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => f (Φmap P0 P1 (z, w)) :=
      hf.comp (hΦ.measurable.comp (measurable_id.prodMk measurable_const))
    have hinner : ∀ z0 : ℝ × ℝ, ∫⁻ z1 in Iact ×ˢ univ, f (K4 (r0 z0, r1 z1), w) ≤
        ENNReal.ofReal (16 / 9) * G (r0 z0) := fun z0 =>
      row_bound (P0 w 1) (P1 w 1) (h := fun x1 => f (K4 (r0 z0, x1), w))
        (hf.comp ((K4.continuous.measurable.comp (measurable_const.prodMk measurable_id)).prodMk
          measurable_const))
    calc ∫⁻ z in actSet, f (Φmap P0 P1 (z, w))
        = ∫⁻ z0 in Iact ×ˢ univ, ∫⁻ z1 in Iact ×ˢ univ, f (K4 (r0 z0, r1 z1), w) := by
          rw [actSet, Measure.volume_eq_prod, setLIntegral_prod _ hm.aemeasurable]; rfl
      _ ≤ ∫⁻ z0 in Iact ×ˢ univ, ENNReal.ofReal (16 / 9) * G (r0 z0) :=
          lintegral_mono fun z0 => hinner z0
      _ = ENNReal.ofReal (16 / 9) * ∫⁻ z0 in Iact ×ˢ univ, G (r0 z0) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (16 / 9) * (ENNReal.ofReal (16 / 9) * ∫⁻ x0, G x0) :=
          mul_le_mul' le_rfl (row_bound (P0 w 0) (P1 w 0) hG)
      _ = ENNReal.ofReal (16 / 9) * ENNReal.ofReal (16 / 9) * ∫⁻ x, f (K4 x, w) := by
          rw [← mul_assoc, Measure.volume_eq_prod (α := ℝ × ℝ) (β := ℝ × ℝ),
            lintegral_prod _ hfw.aemeasurable]
      _ = _ := by
          rw [hK (fun c => f (c, w)) (hf.comp (measurable_id.prodMk measurable_const)),
            ← mul_assoc]
  have hF : Measurable fun y : Yc => f (Φmap P0 P1 y) := hf.comp hΦ.measurable
  calc ∫⁻ y in actSet ×ˢ (univ : Set (Fin 12 → ℝ)), f (Φmap P0 P1 y)
      = ∫⁻ w, ∫⁻ z in actSet, f (Φmap P0 P1 (z, w)) := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
          lintegral_prod_symm _ hF.aemeasurable]
    _ ≤ ∫⁻ w, ENNReal.ofReal (16 / 9) * ENNReal.ofReal (16 / 9) * cK * ∫⁻ c, f (c, w) :=
        lintegral_mono hw
    _ = ENNReal.ofReal (16 / 9) * ENNReal.ofReal (16 / 9) * cK * ∫⁻ x, f x := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          ENNReal.ofReal_ne_top) hcK), Measure.volume_eq_prod (α := Fin 4 → ℝ),
          lintegral_prod_symm _ hf.aemeasurable]

/-! ### The inactive coordinates `w` -/

/-- Twelve numbers as three `2 × 2` blocks, block-major: `V_l i j = ξ (4l + 2i + j)`. -/
def unflat (ξ : Fin 12 → ℝ) : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ := fun l i j =>
  ξ ⟨4 * l.val + 2 * i.val + j.val, by have := l.isLt; have := i.isLt; have := j.isLt; omega⟩

/-- Three `2 × 2` blocks as twelve numbers, block-major (the inverse of `unflat`). -/
def flat (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) : Fin 12 → ℝ := fun n =>
  V ⟨n.val / 4, by have := n.isLt; omega⟩ ⟨n.val % 4 / 2, by omega⟩ ⟨n.val % 2, by omega⟩

theorem unflat_flat (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) : unflat (flat V) = V := by
  funext l i j; fin_cases l <;> fin_cases i <;> fin_cases j <;> rfl

theorem flat_unflat (ξ : Fin 12 → ℝ) : flat (unflat ξ) = ξ := by
  funext n; fin_cases n <;> rfl

theorem unflat_smul (r : ℝ) (ξ : Fin 12 → ℝ) : unflat (r • ξ) = r • unflat ξ := rfl

theorem continuous_unflat_apply (l : Fin 3) (i j : Fin 2) :
    Continuous fun ξ : Fin 12 → ℝ => unflat ξ l i j := continuous_apply _

/-- The three inactive blocks of `θ` at position `p`, in application order. -/
def inact (p : Fin 4) (θ : Raw16) : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ := Fin.removeNth p (rawW θ)

/-- **The inactive coordinates** `w(θ) ∈ ℝ¹²` at position `p`. -/
def wOf (p : Fin 4) (θ : Raw16) : Fin 12 → ℝ := flat (inact p θ)

theorem unflat_wOf (p : Fin 4) (θ : Raw16) : unflat (wOf p θ) = inact p θ := unflat_flat _

/-! ### The coordinates `Ψ_p` -/

/-- **The active coordinates** `𝐜(θ) = (c₃⁽⁰⁾, c₂⁽⁰⁾, c₃⁽¹⁾, c₂⁽¹⁾)`: the exact `s³` and `s²t`
coefficients of the two error rows (`errθ_coeffs`). -/
def cvec (θ : Raw16) : Fin 4 → ℝ :=
  ![e30 (rawW θ) 0, e21 (rawW θ) 0, e30 (rawW θ) 1, e21 (rawW θ) 1]

/-- **The coordinates** `Ψ_p θ = (𝐜(θ), w(θ))`. -/
def Ψ (p : Fin 4) (θ : Raw16) : (Fin 4 → ℝ) × (Fin 12 → ℝ) := (cvec θ, wOf p θ)

/-- The moments `P₀⁽ᵏ⁾`, `P₁⁽ᵏ⁾` over the three inactive blocks, as functions of `w`. -/
def P0w (ξ : Fin 12 → ℝ) (k : Fin 2) : ℝ := mom (unflat ξ) Finset.univ k 0
def P1w (ξ : Fin 12 → ℝ) (k : Fin 2) : ℝ := mom (unflat ξ) Finset.univ k 1

theorem continuous_P0w : Continuous P0w := by
  refine continuous_pi fun k => ?_
  simp only [P0w, mom, rowForm, Fin.sum_univ_three, unflat]; fun_prop

theorem continuous_P1w : Continuous P1w := by
  refine continuous_pi fun k => ?_
  simp only [P1w, mom, rowForm, Fin.sum_univ_three, unflat]; fun_prop

/-- The linear part of `Ψ_p`: the two active row forms and `w`. -/
def Lfun (p : Fin 4) (θ : Raw16) : Yc :=
  ((rowForm (rawW θ p) 0, rowForm (rawW θ p) 1), wOf p θ)

/-- The active block with row forms `z`: `!![a₀, b₀ - a₀; a₁, b₁ - a₁]`. -/
def actMat (z : (ℝ × ℝ) × (ℝ × ℝ)) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![z.1.1, z.1.2 - z.1.1; z.2.1, z.2.2 - z.2.1]

theorem rawW_add' (θ η : Raw16) : rawW (θ + η) = rawW θ + rawW η := by
  funext q; exact weights_add θ η q

theorem rawW_smul (r : ℝ) (θ : Raw16) : rawW (r • θ) = r • rawW θ := by
  funext q i j; fin_cases q <;> fin_cases i <;> fin_cases j <;> rfl

theorem rawW_ofRawW (W : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ) : rawW (ofRawW W) = W :=
  rawEquiv.right_inv W

/-- `Lfun p` as a continuous linear equivalence `Raw16 ≃ Yc`. -/
noncomputable def Lequiv (p : Fin 4) : Raw16 ≃L[ℝ] Yc :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := Lfun p
      invFun := fun y => ofRawW (Fin.insertNth p (actMat y.1) (unflat y.2))
      map_add' := fun θ η => by
        simp only [Lfun, wOf, inact, rawW_add']
        refine Prod.ext (Prod.ext ?_ ?_) ?_
        · ext
          · simp [rowForm]
          · simp [rowForm]; ring
        · ext
          · simp [rowForm]
          · simp [rowForm]; ring
        · funext n; fin_cases n <;> rfl
      map_smul' := fun r θ => by
        simp only [Lfun, wOf, inact, rawW_smul]
        refine Prod.ext (Prod.ext ?_ ?_) ?_
        · ext
          · simp [rowForm]
          · simp [rowForm]; ring
        · ext
          · simp [rowForm]
          · simp [rowForm]; ring
        · funext n; fin_cases n <;> rfl
      left_inv := fun θ => by
        apply rawEquiv.injective
        change rawW _ = rawW θ
        rw [rawW_ofRawW]
        have hM : actMat (rowForm (rawW θ p) 0, rowForm (rawW θ p) 1) = rawW θ p := by
          ext i j; fin_cases i <;> fin_cases j <;> simp [actMat, rowForm]
        simp only [Lfun, wOf, unflat_flat, hM, inact]
        exact Fin.insertNth_self_removeNth p (rawW θ)
      right_inv := fun y => by
        simp only [Lfun, wOf, inact, rawW_ofRawW, Fin.insertNth_apply_same]
        have hr : Fin.removeNth p (Fin.insertNth (α := fun _ => Matrix (Fin 2) (Fin 2) ℝ) p
            (actMat y.1) (unflat y.2)) = unflat y.2 := by
          simp
        rw [hr, flat_unflat]
        refine Prod.ext (Prod.ext ?_ ?_) rfl <;> ext <;> simp [actMat, rowForm] }

theorem Lequiv_apply (p : Fin 4) (θ : Raw16) : Lequiv p θ = Lfun p θ := rfl

/-- `e30` and `e21` split as the active row plus the inactive moments. -/
theorem e30_split (p : Fin 4) (θ : Raw16) (k : Fin 2) :
    e30 (rawW θ) k = (rowForm (rawW θ p) k).1 ^ 3 - 1 + P0w (wOf p θ) k := by
  rw [P0w, unflat_wOf, e30, Fin.sum_univ_succAbove _ p]
  simp only [rA, mom, inact, Fin.removeNth, pow_zero, mul_one, Nat.sub_zero]
  ring

theorem e21_split (p : Fin 4) (θ : Raw16) (k : Fin 2) :
    e21 (rawW θ) k = 3 * (rowForm (rawW θ p) k).1 ^ 2 * (rowForm (rawW θ p) k).2 +
      3 * P1w (wOf p θ) k := by
  rw [P1w, unflat_wOf, e21, Fin.sum_univ_succAbove _ p]
  simp only [rA, rB, mom, inact, Fin.removeNth, pow_one, Finset.mul_sum]
  norm_num
  simp only [mul_assoc]

/-- `Ψ_p = Φ ∘ L_p`. -/
theorem Ψ_eq (p : Fin 4) (θ : Raw16) : Ψ p θ = Φmap P0w P1w (Lequiv p θ) := by
  refine Prod.ext ?_ rfl
  funext i
  fin_cases i <;> simp [Ψ, cvec, Φmap, Lequiv_apply, Lfun, K4_apply, rmap, e30_split p, e21_split p]

/-! ### The change-of-variables bound -/

/-- `|entry| ≤ ‖θ‖` for every entry of every block (the norm on `Raw16` is the sup norm). -/
theorem abs_rawW_le (θ : Raw16) (q : Fin 4) (i j : Fin 2) : |rawW θ q i j| ≤ ‖θ‖ := by
  rw [← Real.norm_eq_abs]
  fin_cases q <;> fin_cases i <;> fin_cases j <;>
    simp only [rawW, weights, tri, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one] <;>
    repeat (first | exact le_rfl | refine (norm_fst_le _).trans ?_ | refine (norm_snd_le _).trans ?_)

theorem rawW_sub' (θ η : Raw16) (q : Fin 4) (i j : Fin 2) :
    rawW (θ - η) q i j = rawW θ q i j - rawW η q i j := by
  fin_cases q <;> fin_cases i <;> fin_cases j <;> rfl

theorem rawW_A0_base (p : Fin 4) (k : Fin 2) :
    rawW (basePos A0 p) p k 0 = 1 := by
  rw [rawW_basePos, Pi.single_eq_same]; fin_cases k <;> rfl

/-- On the `ρ`-ball around the base point (`ρ ≤ 1/2`) both active amplitudes lie in `[1/2, 3/2]`. -/
theorem Lfun_mem_actSet {p : Fin 4} {ρ : ℝ} (hρ : ρ ≤ 1 / 2) {θ : Raw16}
    (hθ : θ ∈ closedBall (basePos A0 p) ρ) :
    Lfun p θ ∈ actSet ×ˢ (univ : Set (Fin 12 → ℝ)) := by
  have hd : ‖θ - basePos A0 p‖ ≤ ρ := by rwa [mem_closedBall, dist_eq_norm] at hθ
  have h : ∀ k : Fin 2, rawW θ p k 0 ∈ Iact := by
    intro k
    have h1 := abs_rawW_le (θ - basePos A0 p) p k 0
    rw [rawW_sub', rawW_A0_base] at h1
    have h2 := abs_le.mp (h1.trans (hd.trans hρ))
    exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  exact ⟨⟨⟨h 0, mem_univ _⟩, ⟨h 1, mem_univ _⟩⟩, mem_univ _⟩

/-- **Item 1: the change-of-variables bound.** At every position `p` and for every radius
`ρ ≤ 1/2` there is `J` with `∫ f(Ψ_p θ) 𝟙_{‖θ - basePos A₀ p‖ ≤ ρ} dθ ≤ J ∫ f` for every
measurable `f ≥ 0` on `ℝ⁴ × ℝ¹²`. -/
theorem cov_bound (p : Fin 4) {ρ : ℝ} (hρ : ρ ≤ 1 / 2) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ f : (Fin 4 → ℝ) × (Fin 12 → ℝ) → ℝ≥0∞, Measurable f →
      ∫⁻ θ, f (Ψ p θ) * (closedBall (basePos A0 p) ρ).indicator 1 θ ≤
        ENNReal.ofReal J * ∫⁻ y, f y := by
  obtain ⟨cL, hcL, hL⟩ := lintegral_comp_clequiv volume volume (Lequiv p)
  obtain ⟨C, hC, hact⟩ := active_cov continuous_P0w continuous_P1w
  refine ⟨(cL * C).toReal, ENNReal.toReal_nonneg, fun f hf => ?_⟩
  set S := actSet ×ˢ (univ : Set (Fin 12 → ℝ))
  have hS : MeasurableSet S :=
    ((measurableSet_Icc.prod MeasurableSet.univ).prod
      (measurableSet_Icc.prod MeasurableSet.univ)).prod MeasurableSet.univ
  have hF : Measurable (S.indicator fun y => f (Φmap P0w P1w y)) :=
    (hf.comp (continuous_Φmap continuous_P0w continuous_P1w).measurable).indicator hS
  calc ∫⁻ θ, f (Ψ p θ) * (closedBall (basePos A0 p) ρ).indicator 1 θ
      ≤ ∫⁻ θ, S.indicator (fun y => f (Φmap P0w P1w y)) (Lequiv p θ) := by
        refine lintegral_mono fun θ => ?_
        by_cases hθ : θ ∈ closedBall (basePos A0 p) ρ
        · rw [indicator_of_mem hθ, Pi.one_apply, mul_one, Ψ_eq,
            indicator_of_mem (show Lequiv p θ ∈ S from Lfun_mem_actSet hρ hθ)]
        · rw [indicator_of_notMem hθ, mul_zero]; exact bot_le
    _ = cL * ∫⁻ y, S.indicator (fun y => f (Φmap P0w P1w y)) y := hL _ hF
    _ = cL * ∫⁻ y in S, f (Φmap P0w P1w y) := by rw [lintegral_indicator hS]
    _ ≤ cL * (C * ∫⁻ y, f y) := mul_le_mul' le_rfl (hact f hf)
    _ = ENNReal.ofReal (cL * C).toReal * ∫⁻ y, f y := by
        rw [ENNReal.ofReal_toReal (ENNReal.mul_ne_top hcL hC), mul_assoc]

end VectorSLT.LossCompare
