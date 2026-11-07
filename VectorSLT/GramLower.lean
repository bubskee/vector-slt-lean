/-
L6 stage 2, part 1: the hard Gram direction on a finite-dimensional polynomial space.

For a box `B = ∏ [loᵢ, hiᵢ]` with `loᵢ < hiᵢ`, the map `p ↦ p|_B ∈ L²(B)` is injective on
polynomials of degree `≤ d`, so on this finite-dimensional space every linear functional is
bounded by the `L²(B)` norm: `ℓ(p)² ≤ C ∫_B p²`. For an input law with `μ ≥ μ₀ · Lebesgue`
on `B`, this gives `ℓ(p)² ≤ (C/μ₀) E_μ p²`.
-/
import VectorSLT.GeneralInput

namespace VectorSLT

open MeasureTheory Set Filter Topology MvPolynomial

variable {d : ℕ}

/-- A closed box with nonempty interior. -/
def cbox (lo hi : Fin 2 → ℝ) : Set (Fin 2 → ℝ) := Set.pi univ fun i => Icc (lo i) (hi i)

theorem isCompact_cbox (lo hi : Fin 2 → ℝ) : IsCompact (cbox lo hi) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem volume_cbox_lt_top (lo hi : Fin 2 → ℝ) : volume (cbox lo hi) < ⊤ :=
  (isCompact_cbox lo hi).measure_lt_top

instance (lo hi : Fin 2 → ℝ) : IsFiniteMeasure (volume.restrict (cbox lo hi)) :=
  isFiniteMeasure_restrict.mpr (volume_cbox_lt_top lo hi).ne

theorem memLp_eval_cbox (lo hi : Fin 2 → ℝ) (p : MvPolynomial (Fin 2) ℝ) :
    MemLp (fun x => eval x p) 2 (volume.restrict (cbox lo hi)) := by
  obtain ⟨C, hC⟩ := (isCompact_cbox lo hi).exists_bound_of_continuousOn
    (continuous_eval p).continuousOn
  refine (memLp_top_of_bound (continuous_eval p).aestronglyMeasurable C ?_).mono_exponent
    le_top
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Icc)] with x hx
  exact hC x hx

/-- Restriction to `L²(B)`, as a linear map on `PolyBox d`. -/
noncomputable def toL2 (lo hi : Fin 2 → ℝ) (d : ℕ) :
    PolyBox d →ₗ[ℝ] Lp ℝ 2 (volume.restrict (cbox lo hi)) where
  toFun p := (memLp_eval_cbox lo hi p.poly).toLp _
  map_add' p q := by
    rw [← MemLp.toLp_add]; congr 1; funext x; simp [PolyBox.poly_add]
  map_smul' c p := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]; congr 1; funext x
    simp [PolyBox.poly_smul]

theorem toL2_injective {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) :
    Function.Injective (toL2 lo hi d) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  have hae : (fun x => eval x p.poly) =ᵐ[volume.restrict (cbox lo hi)] 0 := by
    have := (memLp_eval_cbox lo hi p.poly).coeFn_toLp
    rw [show (memLp_eval_cbox lo hi p.poly).toLp _ = 0 from hp] at this
    exact this.symm.trans (Lp.coeFn_zero _ _ _)
  set U : Set (Fin 2 → ℝ) := Set.pi univ fun i => Ioo (lo i) (hi i)
  have hU : IsOpen U := isOpen_set_pi finite_univ fun i _ => isOpen_Ioo
  have hUB : U ⊆ cbox lo hi := pi_mono fun i _ => Ioo_subset_Icc_self
  have hae' : (fun x => eval x p.poly) =ᵐ[volume.restrict U] 0 := ae_restrict_of_ae_restrict_of_subset hUB hae
  have heq := Measure.eqOn_open_of_ae_eq hae' hU (continuous_eval _).continuousOn
    continuousOn_const
  have hp0 : p.poly = 0 := by
    refine funext_set (s := fun i => Ioo (lo i) (hi i)) (fun i => Ioo_infinite (hlh i))
      fun x hx => ?_
    simpa using heq hx
  exact Subtype.ext hp0

theorem norm_toL2_sq (lo hi : Fin 2 → ℝ) (p : PolyBox d) :
    ‖toL2 lo hi d p‖ ^ 2 = ∫ x in cbox lo hi, eval x p.poly ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_eval_cbox lo hi p.poly).coeFn_toLp] with x hx
  simp only [toL2, LinearMap.coe_mk, AddHom.coe_mk] at hx ⊢
  rw [hx, Real.norm_eq_abs, sq_abs]

/-- **Finite-dimensional Gram lower bound.** Every linear functional on degree-`≤ d`
polynomials is bounded by the `L²` norm on any box with nonempty interior. -/
theorem linear_le_L2 {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) (ℓ : PolyBox d →ₗ[ℝ] ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : PolyBox d, ℓ p ^ 2 ≤ C * ∫ x in cbox lo hi, eval x p.poly ^ 2 := by
  set T := toL2 lo hi d
  set e := LinearEquiv.ofInjective T (toL2_injective hlh)
  set inv : LinearMap.range T →ₗ[ℝ] ℝ := ℓ.comp (e.symm : LinearMap.range T →ₗ[ℝ] PolyBox d)
  set Ic := LinearMap.toContinuousLinearMap inv
  refine ⟨‖Ic‖ ^ 2, sq_nonneg _, fun p => ?_⟩
  have h1 : ℓ p = Ic (e p) := by simp [Ic, inv]
  have h2 : ‖(e p : Lp ℝ 2 (volume.restrict (cbox lo hi)))‖ = ‖T p‖ := by
    simp [e, LinearEquiv.ofInjective_apply]
  have h3 : |ℓ p| ≤ ‖Ic‖ * ‖T p‖ := by
    rw [h1, ← Real.norm_eq_abs, ← h2]
    exact Ic.le_opNorm (e p)
  calc ℓ p ^ 2 = |ℓ p| ^ 2 := (sq_abs _).symm
    _ ≤ (‖Ic‖ * ‖T p‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
    _ = ‖Ic‖ ^ 2 * ‖T p‖ ^ 2 := mul_pow _ _ _
    _ = _ := by rw [norm_toL2_sq]

end VectorSLT
