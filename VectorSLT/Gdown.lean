/-
L6 stage 2: (G↓), the hard Gram direction for the ten coefficients of Theorem M.

For an input law `μ` with finite 162nd moments and `μ ≥ μ₀ · Lebesgue` on a box with
nonempty interior, the population loss for target `A₀` dominates the ten coefficients of
Lemma M1: `K(θ) ≥ κ ∑ₖ (c₃⁽ᵏ⁾² + c₂⁽ᵏ⁾² + c₁⁽ᵏ⁾² + Z_k²)`, all in (M2) coordinates.
-/
import VectorSLT.LemmaM1
import VectorSLT.GramLower
import VectorSLT.Separation

namespace VectorSLT

open MeasureTheory Set Filter MvPolynomial Finset

/-! ### The polynomial model evaluates to the network -/

theorem eval_bind₁' (x : Fin 2 → ℝ) (f : Fin 2 → Pst) (p : Pst) :
    eval x (bind₁ f p) = eval (fun i => eval x (f i)) p := by
  rw [show eval x = eval₂Hom (RingHom.id ℝ) x from rfl, eval₂Hom_bind₁]; rfl

/-- The `(s,t)` point of an input: `s = x₀ - x₁`, `t = x₁`. -/
def stPt (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![x 0 - x 1, x 1]

theorem eval_lin (x : Fin 2 → ℝ) (p q : ℝ) : eval (stPt x) (lin p q) = p * (x 0 - x 1) + q * x 1 := by
  simp [lin, stPt]

/-- The (M2) coordinates of `θ`, as the arguments of the polynomial model. -/
noncomputable def errθ (θ : Raw16) (k : Fin 2) : Pst :=
  errP (actα (toM2 θ)) (actν (toM2 θ)) (inA (toM2 θ)) (inB (toM2 θ)) k

/-- **The polynomial model is the network**: `err_k(s,t) = h_θ(x)_k - F_{A₀}(x)_k`. -/
theorem eval_errθ (θ : Raw16) (x : Fin 2 → ℝ) (k : Fin 2) :
    eval (stPt x) (errθ θ k) = net θ x k - layer A0 x k := by
  obtain ⟨hl0, hS0, hT0, hl, hS, hT, herr⟩ := net_recursion θ x
  set y := toM2 θ
  set α := actα y
  set ν := actν y
  set a := inA y
  set b := inB y
  set W := weights θ
  set lam : ℕ → Fin 2 → ℝ := fun i k => W i k ⬝ᵥ prefixNet W i x
  set S : ℕ → ℝ := fun i => prefixNet W (i + 1) x 0 - prefixNet W (i + 1) x 1
  set T : ℕ → ℝ := fun i => prefixNet W (i + 1) x 1
  have hst : ∀ i ≤ 3, eval (stPt x) (stP α ν a b i).1 = S i ∧
      eval (stPt x) (stP α ν a b i).2 = T i := by
    intro i hi
    induction i with
    | zero =>
      simp only [stP, map_add, map_sub, map_pow, eval_lin]
      refine ⟨?_, ?_⟩
      · rw [hS0, ← hl0 0, ← hl0 1]; simp [stPt]
      · rw [hT0, ← hl0 1]; simp [stPt]
    | succ i ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      simp only [stP, map_add, map_sub, map_pow, map_mul, eval_C]
      rw [h1, h2, ← hl i (by omega) 0, ← hl i (by omega) 1]
      exact ⟨(hS i (by omega)).symm, (hT i (by omega)).symm⟩
  have hrow : ∀ i ≤ 2, ∀ k, eval (stPt x) (rowPoly α ν a b i k) = lam (i + 1) k := by
    intro i hi k
    obtain ⟨h1, h2⟩ := hst i (by omega)
    simp only [rowPoly, map_add, map_mul, eval_C, h1, h2]
    rw [hl i (by omega) k]
  unfold errθ
  rw [herr k]
  simp only [errP, map_add, map_sub, map_pow, eval_lin]
  rw [hrow 0 (by norm_num), hrow 1 (by norm_num), hrow 2 (by norm_num), ← hl0 k]
  simp [stPt]

/-! ### From `(s,t)` coefficients to linear functionals on `x`-polynomials -/

/-- `x ↦ (s,t) = (x₀ - x₁, x₁)` at the polynomial level, and its inverse. -/
noncomputable def toX : Fin 2 → Pst := ![X 0 - X 1, X 1]
noncomputable def toST : Fin 2 → Pst := ![X 0 + X 1, X 1]

theorem bind_toST_toX (p : Pst) : bind₁ toST (bind₁ toX p) = p := by
  rw [bind₁_bind₁]
  have : (fun i => bind₁ toST (toX i)) = X := by
    funext i; fin_cases i <;> simp [toX, toST]
  rw [this, bind₁_X_left]; rfl

theorem eval_bind_toX (x : Fin 2 → ℝ) (p : Pst) : eval x (bind₁ toX p) = eval (stPt x) p := by
  rw [eval_bind₁']
  have : (fun i => eval x (toX i)) = stPt x := by
    funext i; fin_cases i <;> simp [toX, stPt]
  rw [this]

/-- The functional `p ↦ [p(s+t, t)]_m` on degree-`≤ 81` polynomials in `x`. -/
noncomputable def coeffST (m : Fin 2 →₀ ℕ) : PolyBox 81 →ₗ[ℝ] ℝ where
  toFun p := (bind₁ toST p.poly).coeff m
  map_add' p q := by simp [PolyBox.poly_add]
  map_smul' c p := by simp [PolyBox.poly_smul]

/-- The error of output `k` as an element of `PolyBox 81`. -/
theorem errX_mem (θ : Raw16) (k : Fin 2) : (bind₁ toX (errθ θ k)).totalDegree ≤ 81 := by
  obtain ⟨q, hq, hqe⟩ := error_isPoly (weights θ) A0 k
  have : bind₁ toX (errθ θ k) = q := by
    apply MvPolynomial.funext; intro x
    rw [eval_bind_toX, eval_errθ, hqe]; rfl
  rw [this]; exact hq

noncomputable def errX (θ : Raw16) (k : Fin 2) : PolyBox 81 := PolyBox.mk _ (errX_mem θ k)

theorem coeffST_errX (θ : Raw16) (k : Fin 2) (m : Fin 2 →₀ ℕ) :
    coeffST m (errX θ k) = (errθ θ k).coeff m := by
  simp [coeffST, errX, bind_toST_toX]

theorem eval_errX (θ : Raw16) (k : Fin 2) (x : Fin 2 → ℝ) :
    eval x (errX θ k).poly = net θ x k - layer A0 x k := by
  simp [errX, eval_bind_toX, eval_errθ]

/-! ### (G↓) -/

/-- The ten coefficients of Theorem M (M4), row `k`, in (M2) coordinates. -/
noncomputable def c3M (θ : Raw16) (k : Fin 2) : ℝ :=
  actα (toM2 θ) k ^ 3 - 1 + momA (inA (toM2 θ) k)
noncomputable def c2M (θ : Raw16) (k : Fin 2) : ℝ :=
  3 * actα (toM2 θ) k ^ 2 * actν (toM2 θ) k + 3 * momP1 (inA (toM2 θ) k) (inB (toM2 θ) k)
noncomputable def c1M (θ : Raw16) (k : Fin 2) : ℝ :=
  3 * actα (toM2 θ) k * actν (toM2 θ) k ^ 2 + 3 * momP2 (inA (toM2 θ) k) (inB (toM2 θ) k)
noncomputable def ZM (θ : Raw16) (k : Fin 2) : ℝ :=
  Zmom (actα (toM2 θ)) (inA (toM2 θ)) (inB (toM2 θ)) k

theorem coeffs_errθ (θ : Raw16) (k : Fin 2) :
    (errθ θ k).coeff (stMono 3 0) = c3M θ k ∧ (errθ θ k).coeff (stMono 2 1) = c2M θ k ∧
    (errθ θ k).coeff (stMono 1 2) = c1M θ k ∧ (errθ θ k).coeff (stMono 5 0) = 3 * ZM θ k :=
  ⟨errP_c3 _ _ _ _ k, errP_c2 _ _ _ _ k, errP_c1 _ _ _ _ k, errP_s5 _ _ _ _ k⟩

/-- **(G↓)**. For a finite input law with finite 162nd moments and `μ ≥ μ₀ · Lebesgue` on a box
with nonempty interior, the population loss for target `A₀` satisfies
`K(θ) ≥ κ ∑ₖ (c₃⁽ᵏ⁾² + c₂⁽ᵏ⁾² + c₁⁽ᵏ⁾² + Z_k²)` with `κ > 0` independent of `θ`. -/
theorem Gdown (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ θ : Raw16,
      κ * ∑ k, (c3M θ k ^ 2 + c2M θ k ^ 2 + c1M θ k ^ 2 + ZM θ k ^ 2) ≤ popLossA μ A0 θ := by
  obtain ⟨C1, hC1, h1⟩ := linear_le_L2 hlh (coeffST (stMono 3 0))
  obtain ⟨C2, hC2, h2⟩ := linear_le_L2 hlh (coeffST (stMono 2 1))
  obtain ⟨C3, hC3, h3⟩ := linear_le_L2 hlh (coeffST (stMono 1 2))
  obtain ⟨C4, hC4, h4⟩ := linear_le_L2 hlh (coeffST (stMono 5 0))
  obtain ⟨Cm, -, hL2⟩ := l2_le_sup 81 μ hmom
  set Cs := C1 + C2 + C3 + C4 + 1
  have hCs : 0 < Cs := by positivity
  refine ⟨μ₀ / (4 * Cs), by positivity, fun θ => ?_⟩
  set B := cbox lo hi
  set f : Fin 2 → (Fin 2 → ℝ) → ℝ := fun k x => eval x (errX θ k).poly ^ 2
  -- coefficients against the box integral
  have hrow : ∀ k, c3M θ k ^ 2 + c2M θ k ^ 2 + c1M θ k ^ 2 + ZM θ k ^ 2 ≤
      4 * Cs * ∫ x in B, f k x := by
    intro k
    obtain ⟨e3, e2, e1, e5⟩ := coeffs_errθ θ k
    have g1 := h1 (errX θ k); have g2 := h2 (errX θ k)
    have g3 := h3 (errX θ k); have g4 := h4 (errX θ k)
    rw [coeffST_errX, e3] at g1; rw [coeffST_errX, e2] at g2
    rw [coeffST_errX, e1] at g3; rw [coeffST_errX, e5] at g4
    have hI : 0 ≤ ∫ x in B, f k x := integral_nonneg fun x => sq_nonneg _
    have hZ : ZM θ k ^ 2 ≤ (3 * ZM θ k) ^ 2 := by nlinarith [sq_nonneg (ZM θ k)]
    have : C1 * (∫ x in B, f k x) + C2 * (∫ x in B, f k x) + C3 * (∫ x in B, f k x) +
        C4 * (∫ x in B, f k x) ≤ 4 * Cs * ∫ x in B, f k x := by nlinarith
    simp only [f] at *
    linarith
  -- the box integral against the population loss
  have hint : ∀ k, Integrable (f k) μ := fun k => (hL2 (errX θ k)).1
  have hintB : ∀ k, Integrable (f k) (volume.restrict B) := fun k =>
    (memLp_eval_cbox lo hi (errX θ k).poly).integrable_sq
  have hpop : popLossA μ A0 θ = ∫ x, ∑ k, f k x ∂μ := by
    unfold popLossA; congr 1; funext x; congr 1; funext k; simp only [f, eval_errX]
  have hlow : μ₀ * ∫ x in B, ∑ k, f k x ≤ ∫ x, ∑ k, f k x ∂μ := by
    have := integral_mono_measure (f := fun x => ∑ k, f k x) hμ
      (Eventually.of_forall fun x => Finset.sum_nonneg fun k _ => sq_nonneg (eval x (errX θ k).poly))
      (integrable_finsetSum _ fun k _ => hint k)
    rwa [integral_smul_measure, ENNReal.toReal_ofReal hμ₀.le, smul_eq_mul] at this
  have hsplit : ∫ x in B, ∑ k, f k x = ∑ k, ∫ x in B, f k x :=
    integral_finsetSum _ fun k _ => hintB k
  calc μ₀ / (4 * Cs) * ∑ k, (c3M θ k ^ 2 + c2M θ k ^ 2 + c1M θ k ^ 2 + ZM θ k ^ 2)
      ≤ μ₀ / (4 * Cs) * ∑ k, 4 * Cs * ∫ x in B, f k x :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hrow k) (by positivity)
    _ = μ₀ * ∫ x in B, ∑ k, f k x := by
        rw [hsplit, ← Finset.mul_sum]; field_simp
    _ ≤ _ := by rw [hpop]; exact hlow

end VectorSLT
