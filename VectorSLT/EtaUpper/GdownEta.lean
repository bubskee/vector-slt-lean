/-
X5, step 1: (G↓) for the near-shear target `A_η`, with `κ` independent of `η`.

Copy of `Gdown` with `errθ` replaced by `errθη` (`EtaTarget.lean`). By Lemma X2 the four
coefficient functionals read `c₃`, `c₂ - 3η`, `c₁ - 3η²` and `3 Z` off the `A_η` error, and the
Gram constants of `linear_le_L2` never see the target, so one `κ` serves every `η`.
-/
import VectorSLT.EtaTarget

namespace VectorSLT

open MeasureTheory Set Filter MvPolynomial Finset

/-- The `A_η` error of output `k` as an element of `PolyBox 81`. -/
theorem errXη_mem (η : ℝ) (θ : Raw16) (k : Fin 2) : (bind₁ toX (errθη η θ k)).totalDegree ≤ 81 := by
  obtain ⟨q, hq, hqe⟩ := error_isPoly (weights θ) (Aeta η) k
  have : bind₁ toX (errθη η θ k) = q := by
    apply MvPolynomial.funext; intro x
    rw [eval_bind_toX, eval_errθη, hqe]; rfl
  rw [this]; exact hq

noncomputable def errXη (η : ℝ) (θ : Raw16) (k : Fin 2) : PolyBox 81 :=
  PolyBox.mk _ (errXη_mem η θ k)

theorem coeffST_errXη (η : ℝ) (θ : Raw16) (k : Fin 2) (m : Fin 2 →₀ ℕ) :
    coeffST m (errXη η θ k) = (errθη η θ k).coeff m := by
  simp [coeffST, errXη, bind_toST_toX]

theorem eval_errXη (η : ℝ) (θ : Raw16) (k : Fin 2) (x : Fin 2 → ℝ) :
    eval x (errXη η θ k).poly = net θ x k - layer (Aeta η) x k := by
  simp [errXη, eval_bind_toX, eval_errθη]

/-- `c₂ - 3η` for target `A_η` (Lemma X2), row `k`, (M2) coordinates. -/
noncomputable def c2Mη (η : ℝ) (θ : Raw16) (k : Fin 2) : ℝ :=
  3 * actα (toM2 θ) k ^ 2 * actν (toM2 θ) k + 3 * momP1 (inA (toM2 θ) k) (inB (toM2 θ) k) - 3 * η
/-- `c₁ - 3η²` for target `A_η` (Lemma X2). -/
noncomputable def c1Mη (η : ℝ) (θ : Raw16) (k : Fin 2) : ℝ :=
  3 * actα (toM2 θ) k * actν (toM2 θ) k ^ 2 + 3 * momP2 (inA (toM2 θ) k) (inB (toM2 θ) k) -
    3 * η ^ 2

theorem coeffs_errθη (η : ℝ) (θ : Raw16) (k : Fin 2) :
    (errθη η θ k).coeff (stMono 3 0) = c3M θ k ∧ (errθη η θ k).coeff (stMono 2 1) = c2Mη η θ k ∧
    (errθη η θ k).coeff (stMono 1 2) = c1Mη η θ k ∧
      (errθη η θ k).coeff (stMono 5 0) = 3 * ZM θ k := by
  refine ⟨errPη_c3 _ _ _ _ η k, ?_, ?_, errPη_s5 _ _ _ _ η k⟩
  · rw [errθη, errPη_c2, c2Mη]; ring
  · rw [errθη, errPη_c1, c1Mη]; ring

/-- **(G↓) for `A_η`, uniform in `η`.** For a finite input law with finite 162nd moments and
`μ ≥ μ₀ · Lebesgue` on a box with nonempty interior there is `κ > 0` such that for **every** `η`
and every `θ`, `K_{A_η}(θ) ≥ κ ∑ₖ (c₃² + (c₂ - 3η)² + (c₁ - 3η²)² + Z²)`. -/
theorem Gdown_eta (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (η : ℝ) (θ : Raw16),
      κ * ∑ k, (c3M θ k ^ 2 + c2Mη η θ k ^ 2 + c1Mη η θ k ^ 2 + ZM θ k ^ 2) ≤
        popLossA μ (Aeta η) θ := by
  obtain ⟨C1, hC1, h1⟩ := linear_le_L2 hlh (coeffST (stMono 3 0))
  obtain ⟨C2, hC2, h2⟩ := linear_le_L2 hlh (coeffST (stMono 2 1))
  obtain ⟨C3, hC3, h3⟩ := linear_le_L2 hlh (coeffST (stMono 1 2))
  obtain ⟨C4, hC4, h4⟩ := linear_le_L2 hlh (coeffST (stMono 5 0))
  obtain ⟨Cm, -, hL2⟩ := l2_le_sup 81 μ hmom
  set Cs := C1 + C2 + C3 + C4 + 1
  have hCs : 0 < Cs := by positivity
  refine ⟨μ₀ / (4 * Cs), by positivity, fun η θ => ?_⟩
  set B := cbox lo hi
  set f : Fin 2 → (Fin 2 → ℝ) → ℝ := fun k x => eval x (errXη η θ k).poly ^ 2
  have hrow : ∀ k, c3M θ k ^ 2 + c2Mη η θ k ^ 2 + c1Mη η θ k ^ 2 + ZM θ k ^ 2 ≤
      4 * Cs * ∫ x in B, f k x := by
    intro k
    obtain ⟨e3, e2, e1, e5⟩ := coeffs_errθη η θ k
    have g1 := h1 (errXη η θ k); have g2 := h2 (errXη η θ k)
    have g3 := h3 (errXη η θ k); have g4 := h4 (errXη η θ k)
    rw [coeffST_errXη, e3] at g1; rw [coeffST_errXη, e2] at g2
    rw [coeffST_errXη, e1] at g3; rw [coeffST_errXη, e5] at g4
    have hI : 0 ≤ ∫ x in B, f k x := integral_nonneg fun x => sq_nonneg _
    have hZ : ZM θ k ^ 2 ≤ (3 * ZM θ k) ^ 2 := by nlinarith [sq_nonneg (ZM θ k)]
    have : C1 * (∫ x in B, f k x) + C2 * (∫ x in B, f k x) + C3 * (∫ x in B, f k x) +
        C4 * (∫ x in B, f k x) ≤ 4 * Cs * ∫ x in B, f k x := by nlinarith
    simp only [f] at *
    linarith
  have hint : ∀ k, Integrable (f k) μ := fun k => (hL2 (errXη η θ k)).1
  have hintB : ∀ k, Integrable (f k) (volume.restrict B) := fun k =>
    (memLp_eval_cbox lo hi (errXη η θ k).poly).integrable_sq
  have hpop : popLossA μ (Aeta η) θ = ∫ x, ∑ k, f k x ∂μ := by
    unfold popLossA; congr 1; funext x; congr 1; funext k; simp only [f, eval_errXη]
  have hlow : μ₀ * ∫ x in B, ∑ k, f k x ≤ ∫ x, ∑ k, f k x ∂μ := by
    have := integral_mono_measure (f := fun x => ∑ k, f k x) hμ
      (Eventually.of_forall fun x => Finset.sum_nonneg fun k _ =>
        sq_nonneg (eval x (errXη η θ k).poly))
      (integrable_finsetSum _ fun k _ => hint k)
    rwa [integral_smul_measure, ENNReal.toReal_ofReal hμ₀.le, smul_eq_mul] at this
  have hsplit : ∫ x in B, ∑ k, f k x = ∑ k, ∫ x in B, f k x :=
    integral_finsetSum _ fun k _ => hintB k
  calc μ₀ / (4 * Cs) * ∑ k, (c3M θ k ^ 2 + c2Mη η θ k ^ 2 + c1Mη η θ k ^ 2 + ZM θ k ^ 2)
      ≤ μ₀ / (4 * Cs) * ∑ k, 4 * Cs * ∫ x in B, f k x :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hrow k) (by positivity)
    _ = μ₀ * ∫ x in B, ∑ k, f k x := by
        rw [hsplit, ← Finset.mul_sum]; field_simp
    _ ≤ _ := by rw [hpop]; exact hlow

end VectorSLT
