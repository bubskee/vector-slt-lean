/-
L5: general input laws.

On the finite-dimensional space of bivariate polynomials of total degree ≤ d, the sup norm on
the box `[-1,1]²` is a norm, so every coefficient is bounded by it. For an input law with
finite moments of order `2d`, `E_μ p² ≤ C · sup_{[-1,1]²} |p|²`. With `d = 81` this gives
(G↑) for the population loss of every such law (Gaussians included), and Proposition L′ and
the separation hold without compact support.
-/
import VectorSLT.PolyModel
import VectorSLT.Pairs

namespace VectorSLT

open MeasureTheory Set Filter Topology MvPolynomial

/-! ### The normed space of polynomials of degree ≤ d, with the sup norm on the box -/

/-- The input box `[-1,1]²`. -/
def ubox : Set (Fin 2 → ℝ) := Icc (-1) 1

instance : CompactSpace ubox := isCompact_iff_compactSpace.mp isCompact_Icc

/-- Polynomials of total degree `≤ d` (type synonym, to carry the box sup norm). -/
def PolyBox (d : ℕ) : Type := ↥(restrictTotalDegree (Fin 2) ℝ d)

variable {d : ℕ}

noncomputable instance : AddCommGroup (PolyBox d) := inferInstanceAs (AddCommGroup ↥(restrictTotalDegree _ _ _))
noncomputable instance : Module ℝ (PolyBox d) := inferInstanceAs (Module ℝ ↥(restrictTotalDegree _ _ _))
instance : FiniteDimensional ℝ (PolyBox d) :=
  inferInstanceAs (Module.Finite ℝ ↥(restrictTotalDegree (Fin 2) ℝ d))

/-- The underlying polynomial. -/
def PolyBox.poly (p : PolyBox d) : MvPolynomial (Fin 2) ℝ :=
  (show ↥(restrictTotalDegree (Fin 2) ℝ d) from p).1

def PolyBox.mk (p : MvPolynomial (Fin 2) ℝ) (hp : p.totalDegree ≤ d) : PolyBox d :=
  (⟨p, (mem_restrictTotalDegree _ _ _).mpr hp⟩ : ↥(restrictTotalDegree (Fin 2) ℝ d))

@[simp] theorem PolyBox.poly_mk (p : MvPolynomial (Fin 2) ℝ) (hp : p.totalDegree ≤ d) :
    (PolyBox.mk p hp).poly = p := rfl

theorem PolyBox.poly_add (p q : PolyBox d) : (p + q).poly = p.poly + q.poly := rfl
theorem PolyBox.poly_smul (c : ℝ) (p : PolyBox d) : (c • p).poly = c • p.poly := rfl
theorem PolyBox.totalDegree_le (p : PolyBox d) : p.poly.totalDegree ≤ d :=
  (mem_restrictTotalDegree _ _ _).mp (show ↥(restrictTotalDegree (Fin 2) ℝ d) from p).2

/-- Evaluation on the box, as a linear map into `C([-1,1]², ℝ)`. -/
noncomputable def evalBox (d : ℕ) : PolyBox d →ₗ[ℝ] C(ubox, ℝ) where
  toFun p := ⟨fun x => eval x.1 p.poly, (continuous_eval _).comp continuous_subtype_val⟩
  map_add' p q := by ext x; simp [PolyBox.poly_add]
  map_smul' c p := by ext x; simp [PolyBox.poly_smul]

theorem evalBox_injective (d : ℕ) : Function.Injective (evalBox d) := by
  intro p q h
  have hpq : p.poly = q.poly := by
    refine funext_set (s := fun _ => Icc (-1 : ℝ) 1) (fun _ => Icc_infinite (by norm_num))
      fun x hx => ?_
    have hx' : x ∈ ubox := by
      simp only [ubox, ← pi_univ_Icc]; exact hx
    have := congrArg (fun f : C(ubox, ℝ) => f ⟨x, hx'⟩) h
    simpa [evalBox] using this
  exact Subtype.ext hpq

noncomputable instance : NormedAddCommGroup (PolyBox d) :=
  NormedAddCommGroup.induced (PolyBox d) C(ubox, ℝ) (evalBox d) (evalBox_injective d)

noncomputable instance : NormedSpace ℝ (PolyBox d) :=
  NormedSpace.induced ℝ (PolyBox d) C(ubox, ℝ) (evalBox d)

theorem PolyBox.norm_le {p : PolyBox d} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x : Fin 2 → ℝ, (∀ i, |x i| ≤ 1) → |eval x p.poly| ≤ M) : ‖p‖ ≤ M := by
  show ‖evalBox d p‖ ≤ M
  refine (ContinuousMap.norm_le _ hM).mpr fun x => ?_
  have hx : ∀ i, |x.1 i| ≤ 1 := fun i => abs_le.mpr ⟨x.2.1 i, x.2.2 i⟩
  simpa [evalBox] using h x.1 hx

/-! ### Moments ⇒ `E_μ p² ≤ C ‖p‖²` -/

/-- The exponents of total degree `≤ d` in two variables. -/
noncomputable def expSet (d : ℕ) : Finset (Fin 2 →₀ ℕ) :=
  (((Finset.range (d + 1)) ×ˢ (Finset.range (d + 1))).image
    (fun ab => Finsupp.single 0 ab.1 + Finsupp.single 1 ab.2)).filter (fun a => a 0 + a 1 ≤ d)

theorem finsupp_fin2_eq (a : Fin 2 →₀ ℕ) : a = Finsupp.single 0 (a 0) + Finsupp.single 1 (a 1) := by
  ext i; fin_cases i <;> simp

theorem support_subset_expSet {p : MvPolynomial (Fin 2) ℝ} (hp : p.totalDegree ≤ d) :
    p.support ⊆ expSet d := by
  intro a ha
  have hdeg : a 0 + a 1 ≤ d := by
    have := le_totalDegree ha
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at this
    omega
  simp only [expSet, Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_range]
  exact ⟨⟨(a 0, a 1), ⟨by omega, by omega⟩, (finsupp_fin2_eq a).symm⟩, hdeg⟩

/-- The monomial `x^a`. -/
noncomputable def mono (a : Fin 2 →₀ ℕ) (x : Fin 2 → ℝ) : ℝ := ∏ i ∈ a.support, x i ^ a i

theorem mono_eq (a : Fin 2 →₀ ℕ) (x : Fin 2 → ℝ) : mono a x = x 0 ^ a 0 * x 1 ^ a 1 := by
  unfold mono
  rw [Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => by
    simp [Finsupp.notMem_support_iff.mp hi]), Fin.prod_univ_two]

theorem continuous_mono (a : Fin 2 →₀ ℕ) : Continuous (mono a) := by
  have : mono a = fun x => x 0 ^ a 0 * x 1 ^ a 1 := funext (mono_eq a)
  rw [this]; fun_prop

theorem eval_eq_sum_expSet {p : MvPolynomial (Fin 2) ℝ} (hp : p.totalDegree ≤ d) (x : Fin 2 → ℝ) :
    eval x p = ∑ a ∈ expSet d, p.coeff a * mono a x := by
  rw [eval_eq]
  refine Finset.sum_subset (support_subset_expSet hp) fun a _ ha => ?_
  rw [notMem_support_iff.mp ha, zero_mul]

theorem mono_sq_le {a : Fin 2 →₀ ℕ} (ha : a 0 + a 1 ≤ d) (x : Fin 2 → ℝ) :
    mono a x ^ 2 ≤ 1 + |x 0| ^ (2 * d) + |x 1| ^ (2 * d) := by
  set m := max (max |x 0| |x 1|) 1
  have hm1 : 1 ≤ m := le_max_right _ _
  have h0 : |x 0| ≤ m := (le_max_left _ _).trans (le_max_left _ _)
  have h1 : |x 1| ≤ m := (le_max_right _ _).trans (le_max_left _ _)
  have e : mono a x ^ 2 = |x 0| ^ (2 * a 0) * |x 1| ^ (2 * a 1) := by
    have key : ∀ (y : ℝ) (n : ℕ), (y ^ n) ^ 2 = |y| ^ (2 * n) := by
      intro y n; rw [pow_mul, sq_abs, ← pow_mul, ← pow_mul, mul_comm]
    rw [mono_eq, mul_pow, key, key]
  rw [e]
  have hp : |x 0| ^ (2 * a 0) * |x 1| ^ (2 * a 1) ≤ m ^ (2 * d) := by
    calc |x 0| ^ (2 * a 0) * |x 1| ^ (2 * a 1) ≤ m ^ (2 * a 0) * m ^ (2 * a 1) :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h0 _) (pow_le_pow_left₀ (abs_nonneg _) h1 _)
            (by positivity) (by positivity)
      _ = m ^ (2 * (a 0 + a 1)) := by rw [← pow_add]; ring_nf
      _ ≤ m ^ (2 * d) := pow_le_pow_right₀ hm1 (by omega)
  refine hp.trans ?_
  have := pow_nonneg (abs_nonneg (x 0)) (2 * d)
  have := pow_nonneg (abs_nonneg (x 1)) (2 * d)
  rcases max_choice (max |x 0| |x 1|) 1 with h | h <;> rw [show m = _ from h]
  · rcases max_choice |x 0| |x 1| with h' | h' <;> rw [h'] <;> linarith
  · rw [one_pow]; linarith

/-- The coefficient functional on `PolyBox d`. -/
noncomputable def coeffL (d : ℕ) (a : Fin 2 →₀ ℕ) : PolyBox d →ₗ[ℝ] ℝ where
  toFun p := p.poly.coeff a
  map_add' p q := by simp [PolyBox.poly_add]
  map_smul' c p := by simp [PolyBox.poly_smul]

theorem coeff_bound (d : ℕ) (a : Fin 2 →₀ ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : PolyBox d, |p.poly.coeff a| ≤ C * ‖p‖ := by
  set T := LinearMap.toContinuousLinearMap (coeffL d a)
  refine ⟨‖T‖, norm_nonneg _, fun p => ?_⟩
  have := T.le_opNorm p
  rw [Real.norm_eq_abs] at this
  exact this

/-- **Finite-dimensional norm comparison.** For an input law with finite moments of order
`2d`, `E_μ p² ≤ C · (sup_{[-1,1]²} |p|)²` for all polynomials of degree `≤ d`. -/
theorem l2_le_sup (d : ℕ) (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * d)) μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : PolyBox d,
      Integrable (fun x => eval x p.poly ^ 2) μ ∧ ∫ x, eval x p.poly ^ 2 ∂μ ≤ C * ‖p‖ ^ 2 := by
  choose Cf hCf0 hCf using coeff_bound d
  set S := expSet d
  set Mx : (Fin 2 → ℝ) → ℝ := fun x => 1 + |x 0| ^ (2 * d) + |x 1| ^ (2 * d)
  have hMx : Integrable Mx μ := ((integrable_const 1).add (hmom 0)).add (hmom 1)
  have hmono : ∀ a ∈ S, Integrable (fun x => mono a x ^ 2) μ := by
    intro a ha
    have hdeg : a 0 + a 1 ≤ d := (Finset.mem_filter.mp ha).2
    refine hMx.mono' ((continuous_mono a).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact mono_sq_le hdeg x
  set C := (S.card : ℝ) * ∑ a ∈ S, Cf a ^ 2 * ∫ x, mono a x ^ 2 ∂μ
  have hC : 0 ≤ C := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun a _ =>
      mul_nonneg (sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
  refine ⟨C, hC, fun p => ?_⟩
  set G : (Fin 2 → ℝ) → ℝ := fun x =>
    (S.card : ℝ) * ∑ a ∈ S, (Cf a ^ 2 * ‖p‖ ^ 2) * mono a x ^ 2
  have hG : Integrable G μ :=
    (integrable_finsetSum _ fun a ha => (hmono a ha).const_mul _).const_mul _
  have hpt : ∀ x, eval x p.poly ^ 2 ≤ G x := by
    intro x
    rw [eval_eq_sum_expSet p.totalDegree_le]
    refine (sq_sum_le_card_mul_sum_sq).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine Finset.sum_le_sum fun a _ => ?_
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    rw [← mul_pow]
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hCf a p) 2
  have hint : Integrable (fun x => eval x p.poly ^ 2) μ :=
    hG.mono' (((continuous_eval p.poly).pow 2).aestronglyMeasurable) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt x)
  refine ⟨hint, ?_⟩
  calc ∫ x, eval x p.poly ^ 2 ∂μ ≤ ∫ x, G x ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hG
          (Eventually.of_forall hpt)
    _ = C * ‖p‖ ^ 2 := by
        simp only [G, C]
        rw [integral_const_mul, integral_finsetSum _ fun a ha => (hmono a ha).const_mul _]
        simp only [integral_const_mul, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring

/-! ### (G↑) for every input law with finite moments of order 162 -/

/-- **(G↑) without compact support.** For a finite input law with `E|xᵢ|^{162} < ∞`, there is
`Λ` such that `K(θ) ≤ Λ M²` whenever every output error is at most `M` on `[-1,1]²`. -/
theorem popLossA_le_moments (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ Λ : ℝ, ∀ θ M, 0 ≤ M → (∀ x : Fin 2 → ℝ, (∀ i, |x i| ≤ 1) →
      ∀ k, |net θ x k - layer A x k| ≤ M) → popLossA μ A θ ≤ Λ * M ^ 2 := by
  obtain ⟨C, hC, hL2⟩ := l2_le_sup 81 μ hmom
  refine ⟨2 * C, fun θ M hM hbd => ?_⟩
  choose p hpdeg hpeval using fun k => error_isPoly (weights θ) A k
  set q : Fin 2 → PolyBox 81 := fun k => PolyBox.mk (p k) (hpdeg k)
  have hq : ∀ k, ‖q k‖ ≤ M := fun k => PolyBox.norm_le hM fun x hx => by
    simp only [q, PolyBox.poly_mk, hpeval]; exact hbd x hx k
  have hfun : (fun x => ∑ k, (net θ x k - layer A x k) ^ 2) =
      fun x => ∑ k, eval x (q k).poly ^ 2 := by
    funext x; congr 1; funext k; simp only [q, PolyBox.poly_mk, hpeval]; rfl
  unfold popLossA
  rw [hfun, integral_finsetSum _ fun k _ => (hL2 (q k)).1, Fin.sum_univ_two]
  have h0 := (hL2 (q 0)).2
  have h1 := (hL2 (q 1)).2
  have e0 : ‖q 0‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hq 0) 2
  have e1 : ‖q 1‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hq 1) 2
  nlinarith [mul_le_mul_of_nonneg_left e0 hC, mul_le_mul_of_nonneg_left e1 hC]

/-- **Proposition L′ for every input law with finite 162nd moments** (Gaussians included),
every two-nonzero-row shear target, and every prior bounded below near the base point. -/
theorem propLprime_moments {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A)
    (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {π₀ : ℝ} (hπ₀ : 0 < π₀) (π : Raw16 → ENNReal)
    (hπ : ∀ᶠ θ in 𝓝 (baseA A), ENNReal.ofReal π₀ ≤ π θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ENNReal.ofReal (c * N⁻¹ ^ 4 * Real.log N ^ 4) ≤
        ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * popLossA μ A θ))) * π θ := by
  obtain ⟨Λ, hΛ⟩ := popLossA_le_moments μ hmom A
  exact propLprime_shear hA hπ₀ (popLossA μ A) hΛ π hπ

/-- The position-one lower bound on the common footing, for moment laws. -/
theorem Zpos_one_lower_moments {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A)
    (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    (φ χ : Raw16 → ENNReal) {φ₀ χ₀ : ℝ} (hφ₀ : 0 < φ₀) (hχ₀ : 0 < χ₀)
    (hφ : ∀ᶠ θ in 𝓝 (basePos A 0), ENNReal.ofReal φ₀ ≤ φ θ)
    (hχ : ∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ENNReal.ofReal (c * N⁻¹ ^ 4 * Real.log N ^ 4) ≤ Zpos μ A φ χ 0 N := by
  have hπ : ∀ᶠ θ in 𝓝 (baseA A), ENNReal.ofReal (φ₀ * χ₀) ≤ φ θ * χ (θ - basePos A 0) := by
    rw [← basePos_zero]
    have hc : Continuous fun θ : Raw16 => θ - basePos A 0 := by fun_prop
    have ht := hc.tendsto (basePos A 0)
    simp only [sub_self] at ht
    filter_upwards [hφ, ht.eventually hχ] with θ h1 h2
    rw [ENNReal.ofReal_mul hφ₀.le]
    exact mul_le_mul' h1 h2
  exact propLprime_moments hA μ hmom (mul_pos hφ₀ hχ₀) _ hπ

/-- The separation inequality from any four-log lower bound at position one. -/
theorem separation_of_lower {μ : Measure (Fin 2 → ℝ)} {A : Matrix (Fin 2) (Fin 2) ℝ}
    {φ χ : Raw16 → ENNReal}
    (h1 : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ENNReal.ofReal (c * N⁻¹ ^ 4 * Real.log N ^ 4) ≤ Zpos μ A φ χ 0 N)
    (hK : ThmKUpper μ A φ χ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₁ : ℝ, ∀ N : ℝ, N₁ ≤ N →
      ENNReal.ofReal (c * Real.log N ^ 4) * Zpos μ A φ χ 3 N ≤ Zpos μ A φ χ 0 N := by
  obtain ⟨c₁, hc₁, N₀, h1⟩ := h1
  obtain ⟨C, N₄, h4⟩ := hK
  set C' := max C 1
  have hC' : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨c₁ / C', div_pos hc₁ hC', max (max N₀ N₄) 1, fun N hN => ?_⟩
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN4 : N₄ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hNinv : 0 ≤ N⁻¹ := inv_nonneg.mpr (by linarith)
  calc ENNReal.ofReal (c₁ / C' * Real.log N ^ 4) * Zpos μ A φ χ 3 N
      ≤ ENNReal.ofReal (c₁ / C' * Real.log N ^ 4) * ENNReal.ofReal (C' * N⁻¹ ^ 4) := by
        gcongr
        exact (h4 N hN4).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
    _ = ENNReal.ofReal (c₁ * N⁻¹ ^ 4 * Real.log N ^ 4) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp
    _ ≤ Zpos μ A φ χ 0 N := h1 N hN0

/-- **L1 + L5: the separation for every input law with finite 162nd moments**, still
conditional on `ThmK`'s upper half. -/
theorem separation_moments {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A)
    (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    (φ χ : Raw16 → ENNReal) {φ₀ χ₀ : ℝ} (hφ₀ : 0 < φ₀) (hχ₀ : 0 < χ₀)
    (hφ : ∀ᶠ θ in 𝓝 (basePos A 0), ENNReal.ofReal φ₀ ≤ φ θ)
    (hχ : ∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) (hK : ThmKUpper μ A φ χ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₁ : ℝ, ∀ N : ℝ, N₁ ≤ N →
      ENNReal.ofReal (c * Real.log N ^ 4) * Zpos μ A φ χ 3 N ≤ Zpos μ A φ χ 0 N :=
  separation_of_lower (Zpos_one_lower_moments hA μ hmom φ χ hφ₀ hχ₀ hφ hχ) hK

end VectorSLT
