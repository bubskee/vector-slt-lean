/-
X5, step 2: Lemma M4 for the near-shear target (one row at frozen amplitudes).

For `A_η` the row's `G` becomes (eliminate `ν` with `c₂ - 3η`, `P₁ = ∑ aᵢ² bᵢ`, `P₂ = ∑ aᵢ bᵢ²`)
`G_η = P₂ - η² + (P₁ - η)²/γ = G - 2η P₁/γ + η²/γ - η²`.
On a slice `Z = ζ` the extra terms are affine in `β = (b_i, b_j)`: `P₁` is affine there. So the
slice quadratic keeps the matrix `M̃` of (M9) and changes only its linear and constant terms.
`slice_bound` (Lemma M2 on the slice) holds for every `L, k`, so the bound of `lemmaM4` holds
verbatim, with the same constant and no dependence on `η`.
-/
import VectorSLT.LemmaM4

namespace VectorSLT

open MeasureTheory Set Filter Matrix VectorSLT.SLT

/-- Adding an affine function of `β` changes only the linear and constant terms. -/
theorem quadForm_add_affine (M : Matrix (Fin 2) (Fin 2) ℝ) (L l : Fin 2 → ℝ) (k m : ℝ)
    (β : Fin 2 → ℝ) : quadForm M L k β + (l ⬝ᵥ β + m) = quadForm M (L + l) (k + m) β := by
  simp only [quadForm, add_dotProduct]; ring

/-- **The slice reduction for `A_η`**: on the slice `Z = ζ`, `G_η` is `a_p` times a quadratic
form with the **same** matrix `M̃` as for `A₀`. -/
theorem slice_exists_eta {ap ai aj yp yi yj γ κ : ℝ} (hap : ap ≠ 0) (hyp : yp ≠ 0) (hγ : γ ≠ 0)
    (η ζ : ℝ) : ∃ (L : Fin 2 → ℝ) (k : ℝ), ∀ β : Fin 2 → ℝ,
      let bp := (ζ - (ai ^ 2 * yi * β 0 + aj ^ 2 * yj * β 1 + κ)) / (ap ^ 2 * yp)
      ap * bp ^ 2 + ai * β 0 ^ 2 + aj * β 1 ^ 2 - η ^ 2 +
        (ap ^ 2 * bp + ai ^ 2 * β 0 + aj ^ 2 * β 1 - η) ^ 2 / γ =
      ap * quadForm (Mt (ai / ap) (aj / ap) (yi / yp) (yj / yp) (ap ^ 3 / γ)) L k β := by
  obtain ⟨L₀, k₀, hLk⟩ := slice_exists (κ := κ) (ai := ai) (aj := aj) (yi := yi) (yj := yj)
    hap hyp hγ ζ
  set l : Fin 2 → ℝ := ![ap⁻¹ * (-(2 * η) / γ * (ai ^ 2 * (1 - yi / yp))),
    ap⁻¹ * (-(2 * η) / γ * (aj ^ 2 * (1 - yj / yp)))]
  set m : ℝ := ap⁻¹ * (-(2 * η) / γ * ((ζ - κ) / yp) + η ^ 2 / γ - η ^ 2)
  refine ⟨L₀ + l, k₀ + m, fun β => ?_⟩
  intro bp
  rw [← quadForm_add_affine, mul_add, ← hLk β]
  simp only [l, m, bp, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

set_option maxHeartbeats 1000000 in
/-- **Lemma M4 for `A_η`** (M8, second bound), with the bound of `lemmaM4` unchanged:
`∫_{[-ε,ε]³} e^{-N(Z² + G_η²)} ≤ C_ε N⁻¹ |a_p|⁻³ (1 + log N) |D|^{-1/2}`, for every `η` and `κ`. -/
theorem lemmaM4_eta {ε N : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hN : 1 ≤ N)
    {ap ai aj yp yi yj γ κ : ℝ} (η : ℝ) (hap : ap ≠ 0) (hapε : |ap| ≤ ε) (hai : |ai| ≤ |ap|)
    (haj : |aj| ≤ |ap|) (hyp : |yp - 1| ≤ 1 / 20) (hyi : |yi - 1| ≤ 1 / 20)
    (hyj : |yj - 1| ≤ 1 / 20) (hγ : |γ - 1| ≤ 1 / 20) :
    ∫⁻ b in Icc (-ε) ε ×ˢ square 0 ε, ENNReal.ofReal (Real.exp (-(N *
      ((ap ^ 2 * yp * b.1 + ai ^ 2 * yi * b.2 0 + aj ^ 2 * yj * b.2 1 + κ) ^ 2 +
       (ap * b.1 ^ 2 + ai * b.2 0 ^ 2 + aj * b.2 1 ^ 2 - η ^ 2 +
         (ap ^ 2 * b.1 + ai ^ 2 * b.2 0 + aj ^ 2 * b.2 1 - η) ^ 2 / γ) ^ 2)))) ≤
      ENNReal.ofReal (CM4 ε * N⁻¹ * |ap|⁻¹ ^ 3 * (1 + Real.log N)) *
        isqrt (ai / ap * (aj / ap) * EM9 (ai / ap) (aj / ap) (yi / yp) (yj / yp) (ap ^ 3 / γ)) := by
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
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ap ^ 2 * yp := ⟨_, rfl⟩
  have hA : A ≠ 0 := by rw [hAdef]; positivity
  obtain ⟨cβ, hcβdef⟩ : ∃ cβ : (Fin 2 → ℝ) → ℝ,
      cβ = fun β => ai ^ 2 * yi * β 0 + aj ^ 2 * yj * β 1 + κ := ⟨_, rfl⟩
  have hcβm : Measurable cβ := by rw [hcβdef]; fun_prop
  obtain ⟨Gx, hGxdef⟩ : ∃ Gx : ℝ → (Fin 2 → ℝ) → ℝ, Gx = fun bp β =>
      ap * bp ^ 2 + ai * β 0 ^ 2 + aj * β 1 ^ 2 - η ^ 2 +
        (ap ^ 2 * bp + ai ^ 2 * β 0 + aj ^ 2 * β 1 - η) ^ 2 / γ := ⟨_, rfl⟩
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
       (ap * b.1 ^ 2 + ai * b.2 0 ^ 2 + aj * b.2 1 ^ 2 - η ^ 2 +
         (ap ^ 2 * b.1 + ai ^ 2 * b.2 0 + aj ^ 2 * b.2 1 - η) ^ 2 / γ) ^ 2)))) =
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
  set SB := ENNReal.ofReal (Kslice ε * N ^ (-(1 / 2 : ℝ)) * |ap|⁻¹ * (1 + Real.log N)) *
    isqrt (q * a' * EM9 q a' u v c)
  have hslice : ∀ ζ, ∫⁻ β in square 0 ε, Φ β ζ ≤ ENNReal.ofReal (Real.exp (-(N * ζ ^ 2))) * SB := by
    intro ζ
    obtain ⟨L, k, hLk⟩ := slice_exists_eta (κ := κ) (ai := ai) (aj := aj) (yi := yi) (yj := yj)
      hap hyp' hγ' η ζ
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

end VectorSLT
