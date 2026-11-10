/-
Loss comparison at positions two and three: the inactive functions `G_p`, `H_p` (item 3) and the
comparison `κ (‖𝐜‖² + G_p(w)) ≤ K` (item 2), for Lean `p = 1, 2`.

`G_p(w) = ∑ᵢ (Nmid ĝ(w))ᵢ²` with `ĝ_j` the eleven eliminated coefficients of `Middle.lean` and
`Nmid` the fixed invertible linear change to the generators. `H_p(r, ξ) = ∑ᵢ (Nmid h(r³, ·))ᵢ²`.
-/
import VectorSLT.LossCompare.Middle

namespace VectorSLT.LossCompare

open MeasureTheory Set Filter Metric Topology VectorSLT VectorSLT.LeadingMap
open scoped ENNReal

/-! ### Regularity of the building blocks -/

@[fun_prop] theorem contDiff_C12 (k : Fin 2) : ContDiff ℝ 1 fun T : Tab4 => C12 T k := by
  unfold C12; fun_prop
@[fun_prop] theorem contDiff_C03 (k : Fin 2) : ContDiff ℝ 1 fun T : Tab4 => C03 T k := by
  unfold C03; fun_prop
@[fun_prop] theorem contDiff_C50 (k : Fin 2) : ContDiff ℝ 1 fun T : Tab4 => C50 T k := by
  unfold C50 blk50 sg tg; fun_prop
@[fun_prop] theorem contDiff_C41 (k : Fin 2) : ContDiff ℝ 1 fun T : Tab4 => C41 T k := by
  unfold C41 blk41 sg tg; fun_prop
@[fun_prop] theorem contDiff_C32 (k : Fin 2) : ContDiff ℝ 1 fun T : Tab4 => C32 T k := by
  unfold C32 blk32 sg tg; fun_prop
@[fun_prop] theorem contDiff_C70 (k : Fin 2) : ContDiff ℝ 1 fun T : Tab4 => C70 T k := by
  unfold C70 sg5 tg5 E5 blk50 sg tg; fun_prop

@[fun_prop] theorem contDiff_tab_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (p : Fin 4)
    {f : X → Fin 2 → Fin 4 → ℝ} {g : X → Inact} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 fun x => tab p (f x) (g x) := by
  refine contDiff_pi.mpr fun l => ?_
  simp only [LossCompare.tab]
  rcases Fin.eq_self_or_eq_succAbove p l with rfl | ⟨j, rfl⟩
  · simpa using hf
  · simpa using contDiff_pi.mp hg j

@[fun_prop] theorem contDiff_actZ_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {z : X → Fin 4 → ℝ} {n o : X → Fin 2 → ℝ} (hz : ContDiff ℝ 1 z) (hn : ContDiff ℝ 1 n)
    (ho : ContDiff ℝ 1 o) : ContDiff ℝ 1 fun x => actZ (z x) (n x) (o x) := by
  refine contDiff_pi.mpr fun k => contDiff_pi.mpr fun i => ?_
  fin_cases k <;> fin_cases i <;> simp only [LossCompare.actZ] <;> simp <;> fun_prop

theorem contDiff_cubeTab_unflat : ContDiff ℝ 1 fun ξ : Fin 12 → ℝ => cubeTab (unflat ξ) := by
  refine contDiff_pi.mpr fun l => contDiff_pi.mpr fun k => contDiff_pi.mpr fun i => ?_
  fin_cases i <;> simp [cubeTab, cube, rowForm, unflat] <;> fun_prop

theorem contDiff_Fm (p : Fin 4) (j : Fin 11) :
    ContDiff ℝ 1 fun q : (Fin 4 → ℝ) × (Fin 12 → ℝ) => Fm p j q.1 (cubeTab (unflat q.2)) := by
  have ha : ContDiff ℝ 1 fun q : (Fin 4 → ℝ) × (Fin 12 → ℝ) => cubeTab (unflat q.2) :=
    contDiff_cubeTab_unflat.comp contDiff_snd
  fin_cases j <;> simp only [Fm, T0, dN, dO] <;> fun_prop

@[fun_prop] theorem contDiff_Pa (k : Fin 2) (i : Fin 4) : ContDiff ℝ 1 fun a : Inact => Pa a k i := by
  unfold Pa; fun_prop

theorem contDiff_zhat : ContDiff ℝ 1 zhat := by
  refine contDiff_pi.mpr fun i => ?_
  fin_cases i <;> simp only [zhat] <;> simp <;> fun_prop

theorem contDiff_z0a : ContDiff ℝ 1 z0a := by
  refine contDiff_pi.mpr fun i => ?_
  fin_cases i <;> simp only [z0a] <;> simp <;> fun_prop

theorem continuous_hS (p : Fin 4) (j : Fin 11) :
    Continuous fun q : ℝ × Inact => hS p q.1 q.2 j := by
  have hzh : ContDiff ℝ 1 fun q : ℝ × Inact => zhat q.2 := contDiff_zhat.comp contDiff_snd
  have hy : ContDiff ℝ 1 fun q : ℝ × Inact => yTab p q.2 := by
    unfold yTab T0; fun_prop
  have he : ContDiff ℝ 1 fun _ : ℝ × Inact => eTab p := contDiff_const
  have hsa : ContDiff ℝ 1 fun q : ℝ × Inact => q.1 • q.2 := by fun_prop
  have hz : ContDiff ℝ 1 fun q : ℝ × Inact => z0a (q.1 • q.2) := contDiff_z0a.comp hsa
  have hP : ∀ k i, ContDiff ℝ 1 fun q : ℝ × Inact => Pa q.2 k i := fun k i =>
    (contDiff_Pa k i).comp contDiff_snd
  have P00 := hP 0 0; have P01 := hP 0 1; have P10 := hP 1 0; have P11 := hP 1 1
  refine ContDiff.continuous (𝕜 := ℝ) (n := 1) ?_
  fin_cases j <;> simp only [hS, qf, kf, DN, DO, dN, dO, T0] <;> fun_prop

/-! ### `G_p` and `H_p` -/

/-- The normalized radial components `Nmid (h(s, a))`. -/
noncomputable def hvec (p : Fin 4) (s : ℝ) (a : Inact) : Fin 11 → ℝ := Nmid fun j => hS p s a j

/-- **The radial part** `H_p(r, ξ) = ∑ᵢ (Nmid h(r³, ξ))ᵢ²`. -/
noncomputable def Hmid (p : Fin 4) (r : ℝ) (ξ : Fin 12 → ℝ) : ℝ :=
  ∑ i, hvec p (r ^ 3) (cubeTab (unflat ξ)) i ^ 2

/-- **The inactive function** `G_p(w) = H_p(1, w)`, a sum of eleven squares of polynomials. -/
noncomputable def Gmid (p : Fin 4) (ξ : Fin 12 → ℝ) : ℝ := Hmid p 1 ξ

theorem cubeTab_smul (r : ℝ) (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) :
    cubeTab (r • V) = r ^ 3 • cubeTab V := by
  funext l k i
  fin_cases i <;> simp [cubeTab, cube, rowForm] <;> ring

theorem hS_one (p : Fin 4) (hp : p = 1 ∨ p = 2) (a : Inact) (j : Fin 11) :
    hS p 1 a j = ghat p j a := by
  have := ghat_smul hp j 1 a
  rw [one_smul, one_mul] at this
  exact this.symm

/-- **Item 3, weighted homogeneity** (positions two and three): `G_p(r ξ) = r⁶ H_p(r, ξ)`. -/
theorem Gmid_smul {p : Fin 4} (hp : p = 1 ∨ p = 2) (r : ℝ) (ξ : Fin 12 → ℝ) :
    Gmid p (r • ξ) = r ^ 6 * Hmid p r ξ := by
  simp only [Gmid, Hmid, one_pow, unflat_smul, cubeTab_smul]
  have h : hvec p 1 (r ^ 3 • cubeTab (unflat ξ)) = r ^ 3 • hvec p (r ^ 3) (cubeTab (unflat ξ)) := by
    unfold hvec
    rw [← Nmid_smul]
    congr 1
    funext j
    rw [hS_one p hp, ghat_smul hp]; rfl
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem Hmid_nonneg (p : Fin 4) (r : ℝ) (ξ : Fin 12 → ℝ) : 0 ≤ Hmid p r ξ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem Gmid_nonneg (p : Fin 4) (ξ : Fin 12 → ℝ) : 0 ≤ Gmid p ξ := Hmid_nonneg p 1 ξ

/-- **Item 3, regularity**: `H_p` is jointly continuous. -/
theorem continuous_Hmid (p : Fin 4) : Continuous fun q : ℝ × (Fin 12 → ℝ) => Hmid p q.1 q.2 := by
  have hq : Continuous fun q : ℝ × (Fin 12 → ℝ) => (q.1 ^ 3, cubeTab (unflat q.2)) :=
    (continuous_fst.pow 3).prodMk (contDiff_cubeTab_unflat.continuous.comp continuous_snd)
  have hh : ∀ j, Continuous fun q : ℝ × (Fin 12 → ℝ) => hS p (q.1 ^ 3) (cubeTab (unflat q.2)) j :=
    fun j => (continuous_hS p j).comp hq
  refine continuous_finsetSum _ fun i _ => ?_
  refine Continuous.pow ?_ 2
  have h0 := hh 0; have h1 := hh 1; have h2 := hh 2; have h3 := hh 3; have h4 := hh 4
  have h5 := hh 5; have h6 := hh 6; have h7 := hh 7; have h8 := hh 8; have h9 := hh 9
  have h10 := hh 10
  fin_cases i <;> simp only [hvec, Nmid] <;> simp <;> fun_prop

theorem continuous_Gmid (p : Fin 4) : Continuous (Gmid p) := by
  have := (continuous_Hmid p).comp (continuous_const.prodMk continuous_id :
    Continuous fun ξ : Fin 12 → ℝ => ((1 : ℝ), ξ))
  unfold Gmid; exact this

theorem measurable_Gmid (p : Fin 4) : Measurable (Gmid p) := (continuous_Gmid p).measurable

/-- **Item 3, the leading part at position two**: `H₁(0, ξ) = ‖R2(w2 (unflat ξ))‖²`. -/
theorem Hmid_zero_one (ξ : Fin 12 → ℝ) : Hmid 1 0 ξ = ∑ i, R2 (w2 (unflat ξ)) i ^ 2 := by
  simp only [Hmid, hvec, zero_pow (by norm_num : 3 ≠ 0), hS_zero]
  rw [show (fun j => Lw 1 (cubeTab (unflat ξ)) j) = Lw 1 (cubeTab (unflat ξ)) from rfl,
    Nmid_Lw_one]; rfl

/-- **Item 3, the leading part at position three**: `H₂(0, ξ) = ‖R3(w3 (unflat ξ))‖²`. -/
theorem Hmid_zero_two (ξ : Fin 12 → ℝ) : Hmid 2 0 ξ = ∑ i, R3 (w3 (unflat ξ)) i ^ 2 := by
  simp only [Hmid, hvec, zero_pow (by norm_num : 3 ≠ 0), hS_zero]
  rw [show (fun j => Lw 2 (cubeTab (unflat ξ)) j) = Lw 2 (cubeTab (unflat ξ)) from rfl,
    Nmid_Lw_two]; rfl

/-! ### The comparison (item 2) -/

theorem z0w_eq (w : Fin 12 → ℝ) : z0w w = z0a (cubeTab (unflat w)) := by
  funext i
  fin_cases i <;> simp [z0w, z0a, Pa, P0w, P1w, mom, cubeTab, cube]

theorem continuous_Mult_zact (p : Fin 4) (j : Fin 11) :
    Continuous fun θ => Mult j (zact p θ) := by
  have h := continuous_zact p
  have h0 : Continuous fun θ => zact p θ 0 := (continuous_apply 0).comp h
  have h2 : Continuous fun θ => zact p θ 2 := (continuous_apply 2).comp h
  fin_cases j <;> simp only [Mult] <;> fun_prop

/-- `Nmid` is a bounded linear map. -/
theorem Nmid_bound : ∃ KN : ℝ, 0 ≤ KN ∧ ∀ x : Fin 11 → ℝ, ∑ i, Nmid x i ^ 2 ≤ KN * ∑ j, x j ^ 2 := by
  let L : (Fin 11 → ℝ) →ₗ[ℝ] (Fin 11 → ℝ) :=
    { toFun := Nmid, map_add' := Nmid_add, map_smul' := Nmid_smul }
  let Lc := LinearMap.toContinuousLinearMap L
  refine ⟨11 * ‖Lc‖ ^ 2, by positivity, fun x => ?_⟩
  have hsup : ∀ y : Fin 11 → ℝ, ‖y‖ ^ 2 ≤ ∑ j, y j ^ 2 := by
    intro y
    have h0 : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have : ‖y‖ ≤ Real.sqrt (∑ j, y j ^ 2) :=
      (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => by
        rw [Real.norm_eq_abs]
        exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => y j ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ j))
    calc ‖y‖ ^ 2 ≤ Real.sqrt (∑ j, y j ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := Real.sq_sqrt h0
  have hN : ‖Nmid x‖ ≤ ‖Lc‖ * ‖x‖ := Lc.le_opNorm x
  calc ∑ i, Nmid x i ^ 2 ≤ ∑ _i : Fin 11, ‖Nmid x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        rw [← sq_abs, ← Real.norm_eq_abs]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm (Nmid x) i) 2
    _ = 11 * ‖Nmid x‖ ^ 2 := by simp
    _ ≤ 11 * (‖Lc‖ * ‖x‖) ^ 2 := by gcongr
    _ = 11 * ‖Lc‖ ^ 2 * ‖x‖ ^ 2 := by ring
    _ ≤ 11 * ‖Lc‖ ^ 2 * ∑ j, x j ^ 2 := mul_le_mul_of_nonneg_left (hsup x) (by positivity)

/-- The fifteen coefficients used at the middle positions: `𝐜` and the eleven of `cf`. -/
noncomputable def fam15 : Fin 15 → Fin 2 × (Fin 2 →₀ ℕ) :=
  ![(0, stMono 3 0), (0, stMono 2 1), (1, stMono 3 0), (1, stMono 2 1),
    (0, stMono 1 2), (0, stMono 0 3), (1, stMono 1 2), (1, stMono 0 3), (0, stMono 5 0),
    (1, stMono 5 0), (0, stMono 4 1), (1, stMono 4 1), (0, stMono 3 2), (1, stMono 3 2),
    (0, stMono 7 0)]

theorem sum_fam15 (θ : Raw16) :
    ∑ j, ((errθ θ (fam15 j).1).coeff (fam15 j).2) ^ 2 =
      ∑ i, cvec θ i ^ 2 + ∑ j, cf j (cmOf (rawW θ)) ^ 2 := by
  obtain ⟨a0, b0, c0, d0, e0, f0⟩ := errθ_coeffs θ 0
  obtain ⟨a1, b1, c1, d1, e1, f1⟩ := errθ_coeffs θ 1
  have g0 := errθ_coeff32 θ 0; have g1 := errθ_coeff32 θ 1; have h0 := errθ_coeff70 θ 0
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, fam15, cvec, cf, Matrix.cons_val_zero,
    Matrix.cons_val_succ, a0, b0, c0, d0, e0, f0, a1, b1, c1, d1, e1, f1, g0, g1, h0,
    C12_eq, C03_eq, C50_eq, C41_eq]
  simp
  ring

/-- **Item 2 at positions two and three: the loss comparison.** -/
theorem loss_compare_mid {p : Fin 4} (hp : p = 1 ∨ p = 2) (μ : Measure (Fin 2 → ℝ))
    [IsFiniteMeasure μ] (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ) (ρ : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ θ ∈ closedBall (basePos A0 p) ρ,
      κ * (∑ i, (Ψ p θ).1 i ^ 2 + Gmid p (Ψ p θ).2) ≤ popLossA μ A0 θ := by
  obtain ⟨κ₀, hκ₀, hG⟩ := gdown_family μ hmom hlh hμ₀ hμ fam15
  have hS := isCompact_closedBall (basePos A0 p) ρ
  have hel : ∀ j : Fin 11, ∃ K : ℝ, 0 ≤ K ∧ ∀ θ ∈ closedBall (basePos A0 p) ρ,
      ghat p j (cubeTab (inact p θ)) ^ 2 ≤ K * (cf j (cmOf (rawW θ)) ^ 2 + ∑ i, cvec θ i ^ 2) := by
    intro j
    obtain ⟨K, hK0, hK⟩ := elim_bound p (contDiff_Fm p j) hS (continuous_Mult_zact p j)
      (f := fun θ => cf j (cmOf (rawW θ))) (fun θ => by
        rw [mult_identity hp j θ, unflat_wOf])
    refine ⟨K, hK0, fun θ hθ => ?_⟩
    have := hK θ hθ
    simp only [z0w_eq, unflat_wOf] at this
    exact this
  choose K hK0 hK using hel
  obtain ⟨KN, hKN0, hKN⟩ := Nmid_bound
  set Km := ∑ j, K j
  have hKm : 0 ≤ Km := Finset.sum_nonneg fun j _ => hK0 j
  set C := 1 + 11 * KN * Km
  have hC : 0 < C := by positivity
  refine ⟨κ₀ / C, by positivity, fun θ hθ => ?_⟩
  set Sc := ∑ i, cvec θ i ^ 2
  set Sf := ∑ j, cf j (cmOf (rawW θ)) ^ 2
  have hSc : 0 ≤ Sc := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSf : 0 ≤ Sf := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hT := hG θ
  rw [sum_fam15] at hT
  have hgj : ∀ j, ghat p j (cubeTab (inact p θ)) ^ 2 ≤ Km * (Sf + Sc) := by
    intro j
    refine (hK j θ hθ).trans ?_
    have h1 : K j ≤ Km := Finset.single_le_sum (f := K) (fun j _ => hK0 j) (Finset.mem_univ j)
    have h2 : cf j (cmOf (rawW θ)) ^ 2 ≤ Sf :=
      Finset.single_le_sum (f := fun j => cf j (cmOf (rawW θ)) ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ j)
    have h3 : 0 ≤ cf j (cmOf (rawW θ)) ^ 2 + Sc := by positivity
    calc K j * (cf j (cmOf (rawW θ)) ^ 2 + Sc) ≤ Km * (cf j (cmOf (rawW θ)) ^ 2 + Sc) :=
          mul_le_mul_of_nonneg_right h1 h3
      _ ≤ Km * (Sf + Sc) := mul_le_mul_of_nonneg_left (by linarith) hKm
  have hGw : Gmid p (Ψ p θ).2 ≤ 11 * KN * Km * (Sf + Sc) := by
    change ∑ i, hvec p (1 ^ 3) (cubeTab (unflat (wOf p θ))) i ^ 2 ≤ _
    rw [one_pow, unflat_wOf]
    have e : hvec p 1 (cubeTab (inact p θ)) = Nmid fun j => ghat p j (cubeTab (inact p θ)) := by
      unfold hvec; congr 1; funext j; exact hS_one p hp _ j
    rw [e]
    calc ∑ i, Nmid (fun j => ghat p j (cubeTab (inact p θ))) i ^ 2
        ≤ KN * ∑ j, ghat p j (cubeTab (inact p θ)) ^ 2 := hKN _
      _ ≤ KN * ∑ _j : Fin 11, Km * (Sf + Sc) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hgj j) hKN0
      _ = 11 * KN * Km * (Sf + Sc) := by simp; ring
  have hfin : ∑ i, (Ψ p θ).1 i ^ 2 + Gmid p (Ψ p θ).2 ≤ C * (Sc + Sf) := by
    change Sc + Gmid p (Ψ p θ).2 ≤ _
    have : 0 ≤ 11 * KN * Km := by positivity
    simp only [C]; nlinarith
  calc κ₀ / C * (∑ i, (Ψ p θ).1 i ^ 2 + Gmid p (Ψ p θ).2) ≤ κ₀ / C * (C * (Sc + Sf)) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = κ₀ * (Sc + Sf) := by field_simp
    _ ≤ _ := hT

theorem compareA0_mid {p : Fin 4} (hp : p = 1 ∨ p = 2) : CompareA0 p (Gmid p) :=
  fun μ _ hmom _ _ hlh _ hμ₀ hμ ρ => loss_compare_mid hp μ hmom hlh hμ₀ hμ ρ

end VectorSLT.LossCompare
