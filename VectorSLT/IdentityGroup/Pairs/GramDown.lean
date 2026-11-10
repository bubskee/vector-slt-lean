/-
Paper 2, hypothesis (G↓) for an arbitrary target `F_A`, in the sup-norm form used by the
absorption step.

The library's `Gdown` (VectorSLT/Gdown.lean) is specialized to the shear target `A₀` and to the
ten coefficients of Theorem M. Here we need (G↓) for every target and for the whole error. We
use the sup norm on the input box `[-1,1]²` (the norm of `PolyBox`), which is equivalent to any
coefficient norm on the finite-dimensional space of polynomials of degree `≤ 81`:
`κ ‖h_θ - F_A‖²_{[-1,1]²} ≤ K(θ)`. The proof reuses `toL2_injective` from GramLower.lean.
-/
import VectorSLT.GramLower
import VectorSLT.ShearUpper

namespace VectorSLT.IdentityGroup.Pairs

open MeasureTheory Set Filter MvPolynomial VectorSLT

/-- The error `h_θ - F_A` of output `k` as an element of `PolyBox 81`. -/
noncomputable def errPoly (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) (k : Fin 2) : PolyBox 81 :=
  PolyBox.mk (polyNet (weights θ) 4 k - polyLayer A k) <| by
    refine (totalDegree_sub _ _).trans (max_le ?_ ((totalDegree_polyLayer A k).trans (by norm_num)))
    exact (totalDegree_polyNet _ 4 k).trans (by norm_num)

theorem eval_errPoly (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) (k : Fin 2) (x : Fin 2 → ℝ) :
    eval x (errPoly A θ k).poly = net θ x k - layer A x k := by
  simp only [errPoly, PolyBox.poly_mk, map_sub, eval_polyNet, eval_polyLayer]; rfl

/-- The network error on the input box `[-1,1]²`, with the sup norm. -/
noncomputable def errBox (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) : C(ubox, Fin 2 → ℝ) :=
  ⟨fun x => net θ x.1 - layer A x.1,
    continuous_pi fun k => (continuous_err θ A k).comp continuous_subtype_val⟩

theorem errBox_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) (x : ubox) (k : Fin 2) :
    errBox A θ x k = net θ x.1 k - layer A x.1 k := rfl

/-- On the box, `|p(x)| ≤ ‖p‖` for `p ∈ PolyBox d`. -/
theorem abs_eval_le_norm {d : ℕ} (p : PolyBox d) (x : ubox) : |eval x.1 p.poly| ≤ ‖p‖ := by
  have h := (evalBox d p).norm_coe_le_norm x
  have h' : |eval x.1 p.poly| ≤ ‖evalBox d p‖ := by
    simpa [evalBox, Real.norm_eq_abs] using h
  exact h'

theorem norm_errBox_sq_le (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) :
    ‖errBox A θ‖ ^ 2 ≤ ∑ k, ‖errPoly A θ k‖ ^ 2 := by
  have hle : ‖errBox A θ‖ ≤ max ‖errPoly A θ 0‖ ‖errPoly A θ 1‖ := by
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun x => ?_
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
    rw [errBox_apply, Real.norm_eq_abs, ← eval_errPoly]
    have h := abs_eval_le_norm (errPoly A θ k) x
    fin_cases k
    · exact h.trans (le_max_left _ _)
    · exact h.trans (le_max_right _ _)
  rw [Fin.sum_univ_two]
  have h0 := norm_nonneg (errBox A θ)
  have h1 := norm_nonneg (errPoly A θ 0)
  have h2 := norm_nonneg (errPoly A θ 1)
  have hsq := pow_le_pow_left₀ h0 hle 2
  rcases max_choice ‖errPoly A θ 0‖ ‖errPoly A θ 1‖ with h | h <;> rw [h] at hsq <;> nlinarith

/-- `‖p‖² ≤ C ∫_B p²` on `PolyBox d`, for a box with nonempty interior. -/
theorem norm_sq_le_L2 {d : ℕ} {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : PolyBox d, ‖p‖ ^ 2 ≤ C * ∫ x in cbox lo hi, eval x p.poly ^ 2 := by
  obtain ⟨K, -, hanti⟩ :=
    (LinearMap.injective_iff_antilipschitz (toL2 lo hi d)).mp (toL2_injective hlh)
  refine ⟨(K : ℝ) ^ 2, by positivity, fun p => ?_⟩
  have h := hanti.le_mul_dist p 0
  rw [dist_zero_right, map_zero, dist_zero_right] at h
  rw [← norm_toL2_sq]
  calc ‖p‖ ^ 2 ≤ ((K : ℝ) * ‖toL2 lo hi d p‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := mul_pow _ _ _

/-- **(G↓) for every target, sup-norm form.** For a finite input law with finite 162nd moments
and `μ ≥ μ₀ · Lebesgue` on a box with nonempty interior, there is `κ > 0` with
`κ ‖h_θ - F_A‖²_{[-1,1]²} ≤ K(θ)` for every `θ`. -/
theorem gram_down (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ θ : Raw16, κ * ‖errBox A θ‖ ^ 2 ≤ popLossA μ A θ := by
  obtain ⟨C, hC, hL2⟩ := norm_sq_le_L2 (d := 81) hlh
  obtain ⟨Cm, -, hmL2⟩ := l2_le_sup 81 μ hmom
  refine ⟨μ₀ / (C + 1), by positivity, fun θ => ?_⟩
  set B := cbox lo hi
  set f : Fin 2 → (Fin 2 → ℝ) → ℝ := fun k x => eval x (errPoly A θ k).poly ^ 2
  have hint : ∀ k, Integrable (f k) μ := fun k => (hmL2 (errPoly A θ k)).1
  have hintB : ∀ k, Integrable (f k) (volume.restrict B) := fun k =>
    (memLp_eval_cbox lo hi (errPoly A θ k).poly).integrable_sq
  have hpop : popLossA μ A θ = ∫ x, ∑ k, f k x ∂μ := by
    unfold popLossA; congr 1; funext x; congr 1; funext k; simp only [f, eval_errPoly]
  have hlow : μ₀ * ∫ x in B, ∑ k, f k x ≤ ∫ x, ∑ k, f k x ∂μ := by
    have := integral_mono_measure (f := fun x => ∑ k, f k x) hμ
      (Eventually.of_forall fun x => Finset.sum_nonneg fun k _ => sq_nonneg _)
      (integrable_finsetSum _ fun k _ => hint k)
    rwa [integral_smul_measure, ENNReal.toReal_ofReal hμ₀.le, smul_eq_mul] at this
  have hsplit : ∫ x in B, ∑ k, f k x = ∑ k, ∫ x in B, f k x :=
    integral_finsetSum _ fun k _ => hintB k
  have hB0 : ∀ k, 0 ≤ ∫ x in B, f k x := fun k => integral_nonneg fun x => sq_nonneg _
  have hrow : ∑ k, ‖errPoly A θ k‖ ^ 2 ≤ (C + 1) * ∑ k, ∫ x in B, f k x := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => (hL2 (errPoly A θ k)).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (hB0 k)
  calc μ₀ / (C + 1) * ‖errBox A θ‖ ^ 2
      ≤ μ₀ / (C + 1) * ((C + 1) * ∑ k, ∫ x in B, f k x) :=
        mul_le_mul_of_nonneg_left ((norm_errBox_sq_le A θ).trans hrow) (by positivity)
    _ = μ₀ * ∫ x in B, ∑ k, f k x := by rw [hsplit]; field_simp
    _ ≤ _ := by rw [hpop]; exact hlow

end VectorSLT.IdentityGroup.Pairs
