/-
Paper 2, Appendix A.2: Theorem `thm:invertible` at paper position three (Lean `p = 2`): prefix
group `W₁, W₂`, active `W₃ = A + Δ`, suffix `W₄`.

The prefix error splits as in (A-two): `P = S + T + R` with, row by row, `c = W₂ x`,
`φ = W₂ V_{W₁}(x)`, `S = V_{W₁} + V_{W₂}` (cubic), `T = 3 c^{⊙2} ⊙ φ` (quintic) and
`R = 3 c ⊙ φ^{⊙2} + φ^{⊙3}`. The suffix error is `U = V_{W₄}`. With `z = x + P(x)`, the error is
exactly `M_η (Δ, S, T, U) + E`, where (`err_split`)
* `M_η (Δ', S', T', U')(x)_k = (Δ'_k · z)(α² + αβ + β²) + G_k + (A G)_k (a² + aα + α²)
  + U'_k(F_{A+Δ}(z))`, `G = S' + T'`, `η = (Δ, P)`, linear in the retained variables and
  continuous in `η`, with `M_0` the separation map `𝓜` of Lemma `lem:A-sep` (`T₊ = 0`);
* `E_k = R_k + (A R)_k (a² + aα + α²)` is the contribution of `R`.

(A-R) (`abs_R_le`): `|R_k(x)| ≤ (192 ρ³ + 768 ρ⁶)/m · ‖T_k‖` on the box, where `ρ` bounds the
entries of `W₁` and `m` is the constant of `mulQuint_lower`. So `E` is absorbed near the base
point, and injectivity of `M_0` is the certified `sepMap_kernel`. The retained space is
`Mat₂ × H₃² × H₅² × H₃²`, with forms stored by their coefficients (sup norm).
-/
import VectorSLT.IdentityGroup.Pairs.Quintic

namespace VectorSLT.IdentityGroup.Pairs

open MeasureTheory Set Filter Topology VectorSLT MvPolynomial
open scoped Matrix

/-! ### Coefficient forms: linearity and bounds on the box -/

theorem cub_add (c c' : Fin 4 → ℝ) (x : Fin 2 → ℝ) : cub (c + c') x = cub c x + cub c' x := by
  simp only [cub, Pi.add_apply]; ring

theorem cub_smul_coeff (a : ℝ) (c : Fin 4 → ℝ) (x : Fin 2 → ℝ) : cub (a • c) x = a * cub c x := by
  simp only [cub, Pi.smul_apply, smul_eq_mul]; ring

theorem quin_smul_coeff (a : ℝ) (c : Fin 6 → ℝ) (x : Fin 2 → ℝ) :
    quin (a • c) x = a * quin c x := by
  simp only [quin, Pi.smul_apply, smul_eq_mul]; ring

theorem abs_coord_le_one {x : Fin 2 → ℝ} (hx : x ∈ ubox) (i : Fin 2) : |x i| ≤ 1 :=
  abs_le.mpr ⟨hx.1 i, hx.2 i⟩

theorem abs_dot_le {w x : Fin 2 → ℝ} (hx : x ∈ ubox) : |w ⬝ᵥ x| ≤ 2 * ‖w‖ := by
  rw [dot_two]
  have h0 := abs_coord_le_one hx 0
  have h1 := abs_coord_le_one hx 1
  have w0 : |w 0| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w 0
  have w1 : |w 1| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w 1
  calc |w 0 * x 0 + w 1 * x 1| ≤ |w 0| * |x 0| + |w 1| * |x 1| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ ‖w‖ * 1 + ‖w‖ * 1 := by gcongr
    _ = 2 * ‖w‖ := by ring

theorem abs_cub_le {c : Fin 4 → ℝ} {x : Fin 2 → ℝ} (hx : x ∈ ubox) : |cub c x| ≤ 4 * ‖c‖ := by
  have h0 := abs_coord_le_one hx 0
  have h1 := abs_coord_le_one hx 1
  have hc : ∀ j, |c j| ≤ ‖c‖ := fun j => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm c j
  have m : ∀ (a b : ℕ), |x 0 ^ a * x 1 ^ b| ≤ 1 := fun a b => by
    rw [abs_mul, abs_pow, abs_pow]
    calc |x 0| ^ a * |x 1| ^ b ≤ 1 * 1 :=
          mul_le_mul (pow_le_one₀ (abs_nonneg _) h0) (pow_le_one₀ (abs_nonneg _) h1)
            (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have t : ∀ j (a b : ℕ), |c j * (x 0 ^ a * x 1 ^ b)| ≤ ‖c‖ := fun j a b => by
    rw [abs_mul]
    calc |c j| * |x 0 ^ a * x 1 ^ b| ≤ ‖c‖ * 1 := by gcongr; exacts [hc j, m a b]
      _ = ‖c‖ := mul_one _
  have e : cub c x = c 0 * (x 0 ^ 3 * x 1 ^ 0) + c 1 * (x 0 ^ 2 * x 1 ^ 1) +
      c 2 * (x 0 ^ 1 * x 1 ^ 2) + c 3 * (x 0 ^ 0 * x 1 ^ 3) := by simp only [cub]; ring
  rw [e]
  have := t 0 3 0; have := t 1 2 1; have := t 2 1 2; have := t 3 0 3
  calc _ ≤ |c 0 * (x 0 ^ 3 * x 1 ^ 0)| + |c 1 * (x 0 ^ 2 * x 1 ^ 1)| +
        |c 2 * (x 0 ^ 1 * x 1 ^ 2)| + |c 3 * (x 0 ^ 0 * x 1 ^ 3)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ 4 * ‖c‖ := by linarith

theorem norm_cubeCoeffs_le (u : Fin 2 → ℝ) : ‖cubeCoeffs u‖ ≤ 3 * ‖u‖ ^ 3 := by
  have u0 : |u 0| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm u 0
  have u1 : |u 1| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm u 1
  have hn := norm_nonneg u
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  rw [Real.norm_eq_abs]
  fin_cases j <;> simp only [cubeCoeffs, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, abs_mul, abs_pow] <;>
    norm_num
  · calc |u 0| ^ 3 ≤ ‖u‖ ^ 3 := pow_le_pow_left₀ (abs_nonneg _) u0 3
      _ ≤ 3 * ‖u‖ ^ 3 := by nlinarith [pow_nonneg hn 3]
  · have u0' : u 0 ^ 2 ≤ ‖u‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) u0 2
    calc 3 * u 0 ^ 2 * |u 1| ≤ 3 * ‖u‖ ^ 2 * ‖u‖ := by
          gcongr
      _ = 3 * ‖u‖ ^ 3 := by ring
  · have u1' : u 1 ^ 2 ≤ ‖u‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) u1 2
    calc 3 * |u 0| * u 1 ^ 2 ≤ 3 * ‖u‖ * ‖u‖ ^ 2 := by
          gcongr
      _ = 3 * ‖u‖ ^ 3 := by ring
  · calc |u 1| ^ 3 ≤ ‖u‖ ^ 3 := pow_le_pow_left₀ (abs_nonneg _) u1 3
      _ ≤ 3 * ‖u‖ ^ 3 := by nlinarith [pow_nonneg hn 3]

/-! ### The error map -/

/-- Retained variables at Lean position two: `(Δ, S, T, U) ∈ Mat₂ × H₃² × H₅² × H₃²`. -/
abbrev TwoDom : Type :=
  (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) × (Fin 2 → Fin 6 → ℝ) × (Fin 2 → Fin 4 → ℝ)

/-- Parameters of the error map: `η = (Δ, P)`, with `P` the whole prefix error. -/
abbrev TwoPar : Type := (Fin 2 → Fin 2 → ℝ) × (Fin 2 → PolyBox (3 ^ 2))

/-- `G = S + T`, the cubic and quintic parts of the prefix error. -/
def gV (v : TwoDom) (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => cub (v.2.1 i) x + quin (v.2.2.1 i) x

noncomputable def M2fun (A : Matrix (Fin 2) (Fin 2) ℝ) (η : TwoPar) (v : TwoDom)
    (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun k =>
  let z := x + evalV η.2 x
  let α := (A *ᵥ z) k
  let β := ((A + Matrix.of η.1) *ᵥ z) k
  let a := (A *ᵥ x) k
  (v.1 k ⬝ᵥ z) * (α ^ 2 + α * β + β ^ 2) + gV v x k +
    (A *ᵥ gV v x) k * (a ^ 2 + a * α + α ^ 2) + cub (v.2.2.2 k) (layer (A + Matrix.of η.1) z)

theorem continuous_M2fun (A : Matrix (Fin 2) (Fin 2) ℝ) (v : TwoDom) :
    Continuous fun q : TwoPar × (Fin 2 → ℝ) => M2fun A q.1 v q.2 := by
  refine continuous_pi fun k => ?_
  have hz : Continuous fun q : TwoPar × (Fin 2 → ℝ) => q.2 + evalV q.1.2 q.2 :=
    continuous_snd.add (continuous_evalV_joint (continuous_snd.comp continuous_fst) continuous_snd)
  have hz0 : Continuous fun q : TwoPar × (Fin 2 → ℝ) => (q.2 + evalV q.1.2 q.2) 0 :=
    (continuous_apply 0).comp hz
  have hz1 : Continuous fun q : TwoPar × (Fin 2 → ℝ) => (q.2 + evalV q.1.2 q.2) 1 :=
    (continuous_apply 1).comp hz
  have hD : ∀ i j, Continuous fun q : TwoPar × (Fin 2 → ℝ) => q.1.1 i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_fst.comp continuous_fst))
  have hG : ∀ i, Continuous fun q : TwoPar × (Fin 2 → ℝ) => gV v q.2 i := fun i =>
    (continuous_cub_joint continuous_const continuous_snd).add
      (continuous_quin_joint continuous_const continuous_snd)
  have hx0 : Continuous fun q : TwoPar × (Fin 2 → ℝ) => q.2 0 :=
    (continuous_apply 0).comp continuous_snd
  have hx1 : Continuous fun q : TwoPar × (Fin 2 → ℝ) => q.2 1 :=
    (continuous_apply 1).comp continuous_snd
  have hB : ∀ i j, Continuous fun q : TwoPar × (Fin 2 → ℝ) => (A + Matrix.of q.1.1) i j := by
    intro i j; simp only [Matrix.add_apply, Matrix.of_apply]; exact continuous_const.add (hD i j)
  have hL := continuous_layer_joint hB hz
  have hE : Continuous fun q : TwoPar × (Fin 2 → ℝ) =>
      cub (v.2.2.2 k) (layer (A + Matrix.of q.1.1) (q.2 + evalV q.1.2 q.2)) :=
    continuous_cub_joint continuous_const hL
  simp only [M2fun]
  refine Continuous.add ?_ hE
  simp only [mulVec_two, dot_two, Matrix.add_apply, Matrix.of_apply]
  have hk0 := hD k 0
  have hk1 := hD k 1
  have hG0 := hG 0
  have hG1 := hG 1
  have hGk := hG k
  fun_prop

/-- `M_η` as a linear map into `C([-1,1]², ℝ²)`. -/
noncomputable def M2 (A : Matrix (Fin 2) (Fin 2) ℝ) (η : TwoPar) :
    TwoDom →ₗ[ℝ] C(ubox, Fin 2 → ℝ) where
  toFun v := ⟨fun x => M2fun A η v x.1,
    (continuous_M2fun A v).comp (continuous_const.prodMk continuous_subtype_val)⟩
  map_add' v w := by
    ext x k
    simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply, Pi.add_apply, M2fun, gV, cub, quin,
      Prod.fst_add, Prod.snd_add, add_dotProduct, mulVec_two]
    ring
  map_smul' c v := by
    ext x k
    simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, Pi.smul_apply, M2fun, gV, cub,
      quin, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul, RingHom.id_apply,
      mulVec_two]
    ring

theorem M2_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (η : TwoPar) (v : TwoDom) (x : ubox) (k : Fin 2) :
    M2 A η v x k = M2fun A η v x.1 k := rfl

/-- The cubic `φ_k = W₂ k · V_{W₁}(x)`, by its coefficients. -/
noncomputable def psiTwo (θ : Raw16) (k : Fin 2) : Fin 4 → ℝ :=
  weights θ 1 k 0 • cubeCoeffs (weights θ 0 0) + weights θ 1 k 1 • cubeCoeffs (weights θ 0 1)

/-- The retained variables of `θ` at Lean position two. -/
noncomputable def vTwo (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) : TwoDom :=
  (fun i j => weights θ 2 i j - A i j,
    fun k => cubeCoeffs (weights θ 0 k) + cubeCoeffs (weights θ 1 k),
    fun k => (3 : ℝ) • mulQuint (weights θ 1 k) (psiTwo θ k),
    fun k => cubeCoeffs (weights θ 3 k))

/-- The parameters of the error map at `θ`. -/
noncomputable def ηTwo (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) : TwoPar :=
  ((vTwo A θ).1, fun k => grpErr (weights θ) 2 k)

/-- The remainder `R = P - S - T` of the prefix error. -/
noncomputable def Rtwo (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => evalV (ηTwo A θ).2 x i - gV (vTwo A θ) x i

theorem cub_psiTwo (θ : Raw16) (k : Fin 2) (x : Fin 2 → ℝ) :
    cub (psiTwo θ k) x = weights θ 1 k ⬝ᵥ Vmap (weights θ 0) x := by
  simp only [psiTwo, cub_add, cub_smul_coeff, cub_cubeCoeffs, dot_two, Vmap, Pi.pow_apply,
    mulVec_two]

/-- **The remainder is `3 c φ² + φ³`.** -/
theorem Rtwo_eq (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) (x : Fin 2 → ℝ) (k : Fin 2) :
    Rtwo A θ x k = 3 * (weights θ 1 k ⬝ᵥ x) * cub (psiTwo θ k) x ^ 2 + cub (psiTwo θ k) x ^ 3 := by
  simp only [Rtwo, evalV, ηTwo, eval_grpErr, gV, vTwo, cub_add, cub_cubeCoeffs, quin_smul_coeff,
    quin_mulQuint, cub_psiTwo]
  have h2 : prefixNet (weights θ) 2 x = layer (weights θ 1) (layer (weights θ 0) x) := rfl
  rw [h2, layer_apply, layer_eq_add_Vmap (weights θ 0) x, dotProduct_add]
  simp only [Pi.add_apply, Vmap, Pi.pow_apply]
  have e : (weights θ 0 *ᵥ x) k = weights θ 0 k ⬝ᵥ x := rfl
  rw [e]
  ring

/-- **The exact split** `h - F_A = M_η (Δ, S, T, U) + E`, `E_k = R_k + (A R)_k (a² + aα + α²)`. -/
theorem err_split (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) (x : Fin 2 → ℝ) (k : Fin 2) :
    net θ x k - layer A x k = M2fun A (ηTwo A θ) (vTwo A θ) x k +
      (Rtwo A θ x k + (A *ᵥ Rtwo A θ x) k * ((A *ᵥ x) k ^ 2 +
        (A *ᵥ x) k * (A *ᵥ (x + evalV (ηTwo A θ).2 x)) k +
        (A *ᵥ (x + evalV (ηTwo A θ).2 x)) k ^ 2)) := by
  set W := weights θ
  have hz : x + evalV (ηTwo A θ).2 x = prefixNet W 2 x := by
    funext i; simp only [Pi.add_apply, evalV, ηTwo, eval_grpErr, W]; ring
  have hA : A + Matrix.of (ηTwo A θ).1 = W 2 := by ext i j; simp [ηTwo, vTwo, W]
  have hnet : net θ x = layer (W 3) (layer (W 2) (prefixNet W 2 x)) := rfl
  have hP : ∀ i, evalV (ηTwo A θ).2 x i = prefixNet W 2 x i - x i := by
    intro i; simp [evalV, ηTwo, eval_grpErr, W]
  have hU : ∀ y, cub ((vTwo A θ).2.2.2 k) y = (W 3 k ⬝ᵥ y) ^ 3 := fun y => cub_cubeCoeffs _ y
  set z := prefixNet W 2 x with hzdef
  set y := layer (W 2) z with hydef
  have hy : y k = z k + (W 2 k ⬝ᵥ z) ^ 3 := layer_apply _ _ _
  have hnetk : net θ x k = y k + (W 3 k ⬝ᵥ y) ^ 3 := by rw [hnet]; exact layer_apply _ _ _
  have hR : ∀ i, Rtwo A θ x i = z i - x i - gV (vTwo A θ) x i := by
    intro i; rw [Rtwo, hP]
  simp only [M2fun]
  rw [hz, hA, hU, hnetk, hy]
  rw [layer_apply' A]
  have hΔ : ∀ i j, (vTwo A θ).1 i j = W 2 i j - A i j := fun _ _ => rfl
  simp only [mulVec_two, dot_two, hR, hΔ]
  ring

/-! ### (A-R): the remainder is small relative to the quintic part -/

theorem norm_psiTwo_le (θ : Raw16) (k : Fin 2) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hW0 : ∀ i j, |weights θ 0 i j| ≤ ρ) : ‖psiTwo θ k‖ ≤ 6 * ‖weights θ 1 k‖ * ρ ^ 3 := by
  have hu : ∀ j, ‖cubeCoeffs (weights θ 0 j)‖ ≤ 3 * ρ ^ 3 := by
    intro j
    have hn : ‖weights θ 0 j‖ ≤ ρ :=
      (pi_norm_le_iff_of_nonneg hρ).mpr fun i => by rw [Real.norm_eq_abs]; exact hW0 j i
    exact (norm_cubeCoeffs_le _).trans (by gcongr)
  have hw : ∀ j, |weights θ 1 k j| ≤ ‖weights θ 1 k‖ := fun j => by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ j
  calc ‖psiTwo θ k‖ ≤ ‖weights θ 1 k 0 • cubeCoeffs (weights θ 0 0)‖ +
        ‖weights θ 1 k 1 • cubeCoeffs (weights θ 0 1)‖ := norm_add_le _ _
    _ = |weights θ 1 k 0| * ‖cubeCoeffs (weights θ 0 0)‖ +
        |weights θ 1 k 1| * ‖cubeCoeffs (weights θ 0 1)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖weights θ 1 k‖ * (3 * ρ ^ 3) + ‖weights θ 1 k‖ * (3 * ρ ^ 3) := by
        gcongr
        · exact hw 0
        · exact hu 0
        · exact hw 1
        · exact hu 1
    _ = 6 * ‖weights θ 1 k‖ * ρ ^ 3 := by ring

/-- **(A-R).** On the box, `|R_k(x)| ≤ (192 ρ³ + 768 ρ⁶)/m · ‖T_k‖`, where `ρ` bounds the entries
of `W₁` and `m` is a constant of `mulQuint_lower`. -/
theorem abs_R_le {m : ℝ} (hm : 0 < m)
    (hmq : ∀ (w : Fin 2 → ℝ) (ψ : Fin 4 → ℝ), m * ‖w‖ ^ 2 * ‖ψ‖ ≤ ‖mulQuint w ψ‖)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hW0 : ∀ i j, |weights θ 0 i j| ≤ ρ) {x : Fin 2 → ℝ} (hx : x ∈ ubox) (k : Fin 2) :
    |Rtwo A θ x k| ≤ (192 * ρ ^ 3 + 768 * ρ ^ 6) / m * ‖(vTwo A θ).2.2.1 k‖ := by
  set w := weights θ 1 k
  set ψ := psiTwo θ k
  set a := ‖w‖
  set b := ‖ψ‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hc : |w ⬝ᵥ x| ≤ 2 * a := abs_dot_le hx
  have hφ : |cub ψ x| ≤ 4 * b := abs_cub_le hx
  have hψ : b ≤ 6 * a * ρ ^ 3 := norm_psiTwo_le θ k hρ hW0
  have hT : 3 * (m * a ^ 2 * b) ≤ ‖(vTwo A θ).2.2.1 k‖ := by
    have e : (vTwo A θ).2.2.1 k = (3 : ℝ) • mulQuint w ψ := rfl
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact mul_le_mul_of_nonneg_left (hmq w ψ) (by norm_num)
  have hR : |Rtwo A θ x k| ≤ 96 * a * b ^ 2 + 64 * b ^ 3 := by
    rw [Rtwo_eq]
    have h1 : |3 * (w ⬝ᵥ x) * cub ψ x ^ 2| ≤ 3 * (2 * a) * (4 * b) ^ 2 := by
      rw [abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      gcongr
    have h2 : |cub ψ x ^ 3| ≤ (4 * b) ^ 3 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hφ 3
    calc _ ≤ |3 * (w ⬝ᵥ x) * cub ψ x ^ 2| + |cub ψ x ^ 3| := abs_add_le _ _
      _ ≤ 3 * (2 * a) * (4 * b) ^ 2 + (4 * b) ^ 3 := add_le_add h1 h2
      _ = 96 * a * b ^ 2 + 64 * b ^ 3 := by ring
  have hρ3 : 0 ≤ ρ ^ 3 := pow_nonneg hρ 3
  have k1 : 96 * a * b ^ 2 ≤ 576 * a ^ 2 * b * ρ ^ 3 := by
    have : 96 * a * b * b ≤ 96 * a * b * (6 * a * ρ ^ 3) :=
      mul_le_mul_of_nonneg_left hψ (by positivity)
    nlinarith
  have k2 : 64 * b ^ 3 ≤ 2304 * a ^ 2 * b * ρ ^ 6 := by
    have hb2 : b ^ 2 ≤ (6 * a * ρ ^ 3) ^ 2 := pow_le_pow_left₀ hb hψ 2
    have : 64 * b * b ^ 2 ≤ 64 * b * (6 * a * ρ ^ 3) ^ 2 :=
      mul_le_mul_of_nonneg_left hb2 (by positivity)
    nlinarith
  calc |Rtwo A θ x k| ≤ 576 * a ^ 2 * b * ρ ^ 3 + 2304 * a ^ 2 * b * ρ ^ 6 := by linarith
    _ = (192 * ρ ^ 3 + 768 * ρ ^ 6) / m * (3 * (m * a ^ 2 * b)) := by field_simp; ring
    _ ≤ (192 * ρ ^ 3 + 768 * ρ ^ 6) / m * ‖(vTwo A θ).2.2.1 k‖ :=
        mul_le_mul_of_nonneg_left hT (by positivity)

/-! ### Absorbing `E` -/

/-- A bound for the entries of `A`. -/
def amax (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := |A 0 0| + |A 0 1| + |A 1 0| + |A 1 1|

theorem amax_nonneg (A : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ amax A := by unfold amax; positivity

theorem abs_mulVec_le (A : Matrix (Fin 2) (Fin 2) ℝ) {z : Fin 2 → ℝ} {t : ℝ}
    (hz : ∀ j, |z j| ≤ t) (k : Fin 2) : |(A *ᵥ z) k| ≤ amax A * t := by
  have ht : 0 ≤ t := (abs_nonneg _).trans (hz 0)
  rw [mulVec_two]
  have hk : |A k 0| + |A k 1| ≤ amax A := by
    unfold amax; fin_cases k <;> simp <;> linarith [abs_nonneg (A 0 0), abs_nonneg (A 0 1),
      abs_nonneg (A 1 0), abs_nonneg (A 1 1)]
  calc |A k 0 * z 0 + A k 1 * z 1| ≤ |A k 0| * |z 0| + |A k 1| * |z 1| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |A k 0| * t + |A k 1| * t := by gcongr; exacts [hz 0, hz 1]
    _ = (|A k 0| + |A k 1|) * t := by ring
    _ ≤ amax A * t := mul_le_mul_of_nonneg_right hk ht

/-- **The `E` term is controlled by `R`**, when the prefix error is small: `‖E‖ ≤ (1 + 7 a³) B`. -/
theorem norm_E_le (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : Raw16) {B : ℝ}
    (hB : ∀ x ∈ ubox, ∀ k, |Rtwo A θ x k| ≤ B) (hP : ‖(ηTwo A θ).2‖ ≤ 1) :
    ‖errBox A θ - M2 A (ηTwo A θ) (vTwo A θ)‖ ≤ (1 + 7 * amax A ^ 3) * B := by
  have h0 : (0 : Fin 2 → ℝ) ∈ ubox := ⟨fun _ => by norm_num, fun _ => by norm_num⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 h0 0)
  have hA := amax_nonneg A
  refine (ContinuousMap.norm_le _ (by positivity)).mpr fun x => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
  rw [ContinuousMap.sub_apply, Pi.sub_apply, errBox_apply, M2_apply, err_split,
    add_sub_cancel_left, Real.norm_eq_abs]
  have hx := x.2
  have hR := hB x.1 hx
  set z := x.1 + evalV (ηTwo A θ).2 x.1
  have hz : ∀ j, |z j| ≤ 2 := by
    intro j
    have h1 := abs_coord_le_one hx j
    have h2 : |evalV (ηTwo A θ).2 x.1 j| ≤ 1 :=
      (abs_eval_le_norm _ x).trans ((norm_le_pi_norm _ j).trans hP)
    calc |z j| = |x.1 j + evalV (ηTwo A θ).2 x.1 j| := rfl
      _ ≤ |x.1 j| + |evalV (ηTwo A θ).2 x.1 j| := abs_add_le _ _
      _ ≤ 2 := by linarith
  have ha : |(A *ᵥ x.1) k| ≤ amax A * 1 := abs_mulVec_le A (abs_coord_le_one hx) k
  have hα : |(A *ᵥ z) k| ≤ amax A * 2 := abs_mulVec_le A hz k
  have hAR : |(A *ᵥ Rtwo A θ x.1) k| ≤ amax A * B := abs_mulVec_le A (fun j => hR j) k
  have hQ : |(A *ᵥ x.1) k ^ 2 + (A *ᵥ x.1) k * (A *ᵥ z) k + (A *ᵥ z) k ^ 2| ≤
      7 * amax A ^ 2 := by
    have e1 : |(A *ᵥ x.1) k ^ 2| ≤ amax A ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
    have e2 : |(A *ᵥ x.1) k * (A *ᵥ z) k| ≤ amax A * (2 * amax A) := by
      rw [abs_mul]; exact mul_le_mul (by linarith) (by linarith) (abs_nonneg _) hA
    have e3 : |(A *ᵥ z) k ^ 2| ≤ (2 * amax A) ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
    calc _ ≤ |(A *ᵥ x.1) k ^ 2| + |(A *ᵥ x.1) k * (A *ᵥ z) k| + |(A *ᵥ z) k ^ 2| := by
          refine (abs_add_le _ _).trans ?_; gcongr; exact abs_add_le _ _
      _ ≤ amax A ^ 2 + amax A * (2 * amax A) + (2 * amax A) ^ 2 := by gcongr
      _ = 7 * amax A ^ 2 := by ring
  calc |Rtwo A θ x.1 k + (A *ᵥ Rtwo A θ x.1) k * ((A *ᵥ x.1) k ^ 2 +
        (A *ᵥ x.1) k * (A *ᵥ z) k + (A *ᵥ z) k ^ 2)|
      ≤ |Rtwo A θ x.1 k| + |(A *ᵥ Rtwo A θ x.1) k| *
          |(A *ᵥ x.1) k ^ 2 + (A *ᵥ x.1) k * (A *ᵥ z) k + (A *ᵥ z) k ^ 2| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ B + amax A * B * (7 * amax A ^ 2) := by gcongr; exact hR k
    _ = (1 + 7 * amax A ^ 3) * B := by ring

theorem continuous_ηTwo (A : Matrix (Fin 2) (Fin 2) ℝ) : Continuous (ηTwo A) := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_pi fun i => continuous_pi fun j =>
      (continuous_weights 2 i j).sub continuous_const
  · refine continuous_pi fun k => continuous_polyBox_of _ ?_
    have h := continuous_prefixNet_joint (X := Raw16 × ubox) (W := fun q => weights q.1)
      (fun q i j => (continuous_weights q i j).comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd) 2
    have : (fun q : Raw16 × ubox => eval q.2.1 (grpErr (weights q.1) 2 k).poly) =
        fun q => prefixNet (weights q.1) 2 q.2.1 k - q.2.1 k := by
      funext q; rw [eval_grpErr]
    rw [this]
    exact ((continuous_apply k).comp h).sub
      ((continuous_apply k).comp (continuous_subtype_val.comp continuous_snd))

theorem ηTwo_base (A : Matrix (Fin 2) (Fin 2) ℝ) : ηTwo A (basePos A 2) = 0 := by
  refine Prod.ext ?_ ?_
  · funext i j; simp [ηTwo, vTwo, weights_basePos A 2 2 (by norm_num)]
  · funext k
    apply Subtype.ext
    show (grpErr (weights (basePos A 2)) 2 k).poly = 0
    apply MvPolynomial.funext; intro x
    rw [eval_grpErr, prefixNet_zero_blocks _ 2 (fun q hq => by
      rw [weights_basePos A 2 q (by omega)]; simp; omega) x, sub_self, map_zero]

/-- **Absorption at Lean position two**, with the remainder `E` absorbed by (A-R). -/
theorem two_absorb (A : Matrix (Fin 2) (Fin 2) ℝ) (hinj : Function.Injective (M2 A 0)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ θ, ‖θ - basePos A 2‖ < r₀ →
      c₀ * ‖vTwo A θ‖ ≤ ‖errBox A θ‖ := by
  obtain ⟨m, hm, hmq⟩ := mulQuint_lower
  have hcont : ∀ v : TwoDom, Continuous fun η : TwoPar => M2 A η v := by
    intro v
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_M2fun A v).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  obtain ⟨c₀, hc₀, hev⟩ := uniform_lower_of_linear (X := TwoPar) (x₀ := 0)
    (fun η : TwoPar => M2 A η) hcont hinj
  have ht : Tendsto (ηTwo A) (𝓝 (basePos A 2)) (𝓝 0) := by
    have := (continuous_ηTwo A).tendsto (basePos A 2)
    rwa [ηTwo_base] at this
  have hev1 := ht.eventually hev
  have hev2 : ∀ᶠ θ in 𝓝 (basePos A 2), ‖(ηTwo A θ).2‖ ≤ 1 := by
    have := ht.eventually (Metric.closedBall_mem_nhds (0 : TwoPar) one_pos)
    filter_upwards [this] with θ hθ
    rw [dist_zero_right] at hθ
    exact (norm_snd_le _).trans hθ
  obtain ⟨r, hr, hrr⟩ := Metric.eventually_nhds_iff.mp (hev1.and hev2)
  set KE := 1 + 7 * amax A ^ 3
  have hKE : 0 < KE := by have := amax_nonneg A; positivity
  set ρ₀ := min 1 (c₀ * m / (1920 * KE))
  have hρ₀ : 0 < ρ₀ := lt_min one_pos (by positivity)
  refine ⟨min r ρ₀, lt_min hr hρ₀, c₀ / 2, half_pos hc₀, fun θ hθ => ?_⟩
  set ρ := ‖θ - basePos A 2‖
  have hρ : 0 ≤ ρ := norm_nonneg _
  have hρr : ρ < r := lt_of_lt_of_le hθ (min_le_left _ _)
  have hρ1 : ρ ≤ 1 := (lt_of_lt_of_le hθ (min_le_right _ _)).le.trans (min_le_left _ _)
  have hρc : ρ ≤ c₀ * m / (1920 * KE) :=
    (lt_of_lt_of_le hθ (min_le_right _ _)).le.trans (min_le_right _ _)
  obtain ⟨hlow, hP⟩ := hrr (show dist θ (basePos A 2) < r by rwa [dist_eq_norm])
  set v := vTwo A θ
  have hW0 : ∀ i j, |weights θ 0 i j| ≤ ρ := by
    intro i j
    rw [weights_eq_sub_base A 2 θ (by norm_num) (by decide)]
    exact abs_weights_le _ _ _ _
  have hT : ∀ k, ‖v.2.2.1 k‖ ≤ ‖v‖ := fun k =>
    (norm_le_pi_norm _ k).trans ((norm_fst_le _).trans ((norm_snd_le _).trans (norm_snd_le v)))
  have hρ3 : ρ ^ 3 ≤ ρ := by
    calc ρ ^ 3 = ρ * ρ ^ 2 := by ring
      _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hρ hρ1) hρ
      _ = ρ := mul_one ρ
  have hρ6 : ρ ^ 6 ≤ ρ := by
    calc ρ ^ 6 = ρ * ρ ^ 5 := by ring
      _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hρ hρ1) hρ
      _ = ρ := mul_one ρ
  have hB : ∀ x ∈ ubox, ∀ k, |Rtwo A θ x k| ≤ 960 * ρ / m * ‖v‖ := by
    intro x hx k
    refine (abs_R_le hm hmq A θ hρ hW0 hx k).trans ?_
    have h1 : (192 * ρ ^ 3 + 768 * ρ ^ 6) / m ≤ 960 * ρ / m := by
      apply div_le_div_of_nonneg_right _ hm.le; linarith
    exact mul_le_mul h1 (hT k) (norm_nonneg _) (by positivity)
  have hE := norm_E_le A θ hB hP
  have hE' : KE * (960 * ρ / m * ‖v‖) ≤ c₀ / 2 * ‖v‖ := by
    have : KE * (960 * ρ / m) ≤ c₀ / 2 := by
      rw [show KE * (960 * ρ / m) = 960 * KE * ρ / m by ring, div_le_iff₀ hm]
      have := mul_le_mul_of_nonneg_left hρc (show (0 : ℝ) ≤ 960 * KE by positivity)
      calc 960 * KE * ρ ≤ 960 * KE * (c₀ * m / (1920 * KE)) := this
        _ = c₀ / 2 * m := by field_simp; ring
    calc KE * (960 * ρ / m * ‖v‖) = KE * (960 * ρ / m) * ‖v‖ := by ring
      _ ≤ c₀ / 2 * ‖v‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have h1 := hlow v
  have h2 : ‖M2 A (ηTwo A θ) v‖ ≤ ‖errBox A θ‖ + ‖errBox A θ - M2 A (ηTwo A θ) v‖ := by
    have := norm_sub_le (errBox A θ) (errBox A θ - M2 A (ηTwo A θ) v)
    rwa [sub_sub_cancel] at this
  linarith

/-! ### Injectivity: the certified separation lemma -/

theorem homDeg_cubV (S : Fin 2 → Fin 4 → ℝ) : HomDeg 3 (cubV S) :=
  ⟨continuous_pi fun i => continuous_cub_joint continuous_const continuous_id, fun r z => by
    funext i; simp only [cubV, Pi.smul_apply, smul_eq_mul, cub_smul]⟩

theorem homDeg_quinV (T : Fin 2 → Fin 6 → ℝ) : HomDeg 5 (quinV T) :=
  ⟨continuous_pi fun i => continuous_quin_joint continuous_const continuous_id, fun r z => by
    funext i; simp only [quinV, Pi.smul_apply, smul_eq_mul, quin_smul]⟩

theorem homDeg_zero5 : HomDeg 5 (fun _ : Fin 2 → ℝ => (0 : Fin 2 → ℝ)) :=
  ⟨continuous_const, fun r z => by simp⟩

/-- The kernel of `M_0` at Lean position two lies in the kernel of the separation map `sepMap`
(with `T₊ = 0`), on the whole plane. -/
theorem M2_kernel (A : Matrix (Fin 2) (Fin 2) ℝ) {v : TwoDom} (hv : M2 A 0 v = 0)
    (x : Fin 2 → ℝ) :
    sepMap A (Matrix.of v.1) (cubV v.2.1) (quinV v.2.2.1) (cubV v.2.2.2) (fun _ => 0) x = 0 := by
  funext k
  set q : MvPolynomial (Fin 2) ℝ :=
    (C (v.1 k 0) * X 0 + C (v.1 k 1) * X 1) * (3 * (C (A k 0) * X 0 + C (A k 1) * X 1) ^ 2) +
      (cubPoly (v.2.1 k) + quinPoly (v.2.2.1 k)) + 3 * (C (A k 0) * X 0 + C (A k 1) * X 1) ^ 2 *
        (C (A k 0) * (cubPoly (v.2.1 0) + quinPoly (v.2.2.1 0)) +
          C (A k 1) * (cubPoly (v.2.1 1) + quinPoly (v.2.2.1 1))) +
      bind₁ (layerPoly A) (cubPoly (v.2.2.2 k))
  have hq : ∀ y : Fin 2 → ℝ, eval y q =
      sepMap A (Matrix.of v.1) (cubV v.2.1) (quinV v.2.2.1) (cubV v.2.2.2) (fun _ => 0) y k := by
    intro y
    simp only [q, map_add, map_mul, map_pow, eval_C, eval_X, eval_bind₁_eq, eval_layerPoly,
      eval_cubPoly, eval_quinPoly, sepMap, Lmap, DVmap, Pi.add_apply, cubV, quinV, mulVec_two,
      Matrix.of_apply, Pi.zero_apply]
    norm_num
    ring
  rw [← hq]
  refine eval_eq_zero_of_box (fun y => ?_) x
  have h := congrArg (fun f : C(ubox, Fin 2 → ℝ) => f y k) hv
  simp only [M2_apply, M2fun, ContinuousMap.zero_apply, Pi.zero_apply, Prod.fst_zero,
    Prod.snd_zero] at h
  have h0 : evalV (0 : Fin 2 → PolyBox (3 ^ 2)) y.1 = 0 := by
    funext i; simp only [evalV, Pi.zero_apply]; rfl
  rw [h0, add_zero, show A + Matrix.of (0 : Fin 2 → Fin 2 → ℝ) = A by ext; simp] at h
  rw [hq, ← h]
  simp only [sepMap, Lmap, DVmap, Pi.add_apply, cubV, quinV, gV, mulVec_two, dot_two,
    Matrix.of_apply, Pi.zero_apply]
  ring

/-- **Injectivity of the separation map `𝓜` (`T₊ = 0`) on `Mat₂ × H₃² × H₅² × H₃²`**, from the
certified `sepMap_kernel`. -/
theorem twoPrefix_injective {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) :
    Function.Injective (M2 A 0) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  obtain ⟨hΔ, hS, hT, hU, -⟩ := sepMap_kernel hA (homDeg_cubV w.2.1) (homDeg_quinV w.2.2.1)
    (homDeg_cubV w.2.2.2) homDeg_zero5 (M2_kernel A hw)
  have h1 : w.1 = 0 := by
    funext i j; exact congrFun (congrFun hΔ i) j
  have h2 : w.2.1 = 0 := funext fun i => cub_eq_zero fun x => congrFun (congrFun hS x) i
  have h3 : w.2.2.1 = 0 := funext fun i => quin_eq_zero fun x => congrFun (congrFun hT x) i
  have h4 : w.2.2.2 = 0 := funext fun i => cub_eq_zero fun x => congrFun (congrFun hU x) i
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))

/-! ### The comparison and the upper bound -/

/-- The row functional at Lean position two: a two-block prefix and a one-block suffix. -/
noncomputable def gTwo (u : Fin 3 → ℝ × ℝ) : ℝ :=
  cubeSumSq (fun _ : Fin 1 => u 2) + cubeSumSq (fun j : Fin 2 => u ((2 : Fin 3).succAbove j))

theorem measurable_gTwo : Measurable gTwo := by
  unfold gTwo
  exact (((continuous_cubeSumSq 1).comp (continuous_pi fun _ => continuous_apply 2)).add
    ((continuous_cubeSumSq 2).comp (continuous_pi fun _ => continuous_apply _))).measurable

/-- `G₂` of two forms is bounded by the squared coefficient norm of the sum of their cubes. -/
theorem cubeSumSq_two_le (w w' : Fin 2 → ℝ) :
    cubeSumSq ![(w 0, w 1), (w' 0, w' 1)] ≤ 4 * ‖cubeCoeffs w + cubeCoeffs w'‖ ^ 2 := by
  set c := cubeCoeffs w + cubeCoeffs w'
  have hc : ∀ j, c j ^ 2 ≤ ‖c‖ ^ 2 := by
    intro j
    rw [← sq_abs, ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm _ j) 2
  have h0 : (w 0 ^ 3 + w' 0 ^ 3) ^ 2 ≤ ‖c‖ ^ 2 := hc 0
  have h1 : (3 * w 0 ^ 2 * w 1 + 3 * w' 0 ^ 2 * w' 1) ^ 2 ≤ ‖c‖ ^ 2 := hc 1
  have h2 : (3 * w 0 * w 1 ^ 2 + 3 * w' 0 * w' 1 ^ 2) ^ 2 ≤ ‖c‖ ^ 2 := hc 2
  have h3 : (w 1 ^ 3 + w' 1 ^ 3) ^ 2 ≤ ‖c‖ ^ 2 := hc 3
  have e : cubeSumSq ![(w 0, w 1), (w' 0, w' 1)] = (w 0 ^ 3 + w' 0 ^ 3) ^ 2 +
      (w 0 ^ 2 * w 1 + w' 0 ^ 2 * w' 1) ^ 2 + (w 0 * w 1 ^ 2 + w' 0 * w' 1 ^ 2) ^ 2 +
      (w 1 ^ 3 + w' 1 ^ 3) ^ 2 := by
    simp [cubeSumSq, cubeSum, Fin.sum_univ_four, Fin.sum_univ_two]
  rw [e]
  nlinarith [sq_nonneg (w 0 ^ 2 * w 1 + w' 0 ^ 2 * w' 1),
    sq_nonneg (w 0 * w 1 ^ 2 + w' 0 * w' 1 ^ 2)]

theorem two_compare (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ Cq : ℝ, ∀ θ, actSq A (Sfun 2 θ).1 + gTwo (rowU (Sfun 2 θ).2.1) +
      gTwo (rowU (Sfun 2 θ).2.2) ≤ Cq * ‖vTwo A θ‖ ^ 2 := by
  refine ⟨20, fun θ => ?_⟩
  set v := vTwo A θ
  have hΔ : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have hS : ∀ k, ‖v.2.1 k‖ ≤ ‖v‖ := fun k =>
    (norm_le_pi_norm v.2.1 k).trans ((norm_fst_le v.2).trans (norm_snd_le v))
  have hU : ∀ k, ‖v.2.2.2 k‖ ≤ ‖v‖ := fun k =>
    (norm_le_pi_norm _ k).trans ((norm_snd_le _).trans ((norm_snd_le _).trans (norm_snd_le v)))
  have hact : actSq A (Sfun 2 θ).1 ≤ 4 * ‖v‖ ^ 2 := by
    rw [actSq_Sfun]
    refine (sum_sq_le_norm v.1).trans ?_
    have := pow_le_pow_left₀ (norm_nonneg _) hΔ 2
    linarith
  have hrow : ∀ k : Fin 2, gTwo (rowU (![(Sfun 2 θ).2.1, (Sfun 2 θ).2.2] k)) ≤ 8 * ‖v‖ ^ 2 := by
    intro k
    rw [rowU_Sfun]
    have e1 : (fun _ : Fin 1 => (weights θ (inact 2 2) k 0, weights θ (inact 2 2) k 1)) =
        fun _ : Fin 1 => (weights θ 3 k 0, weights θ 3 k 1) := rfl
    have e2 : (fun j : Fin 2 => (weights θ (inact 2 ((2 : Fin 3).succAbove j)) k 0,
        weights θ (inact 2 ((2 : Fin 3).succAbove j)) k 1)) =
        ![(weights θ 1 k 0, weights θ 1 k 1), (weights θ 0 k 0, weights θ 0 k 1)] := by
      funext j; fin_cases j <;> rfl
    simp only [gTwo]
    rw [e1, e2]
    have g1 := cubeSumSq_one_le (weights θ 3 k)
    have g2 := cubeSumSq_two_le (weights θ 1 k) (weights θ 0 k)
    have e3 : ‖cubeCoeffs (weights θ 3 k)‖ = ‖v.2.2.2 k‖ := rfl
    have e4 : ‖cubeCoeffs (weights θ 1 k) + cubeCoeffs (weights θ 0 k)‖ = ‖v.2.1 k‖ := by
      rw [add_comm]; rfl
    rw [e3] at g1
    rw [e4] at g2
    have n1 := pow_le_pow_left₀ (norm_nonneg _) (hU k) 2
    have n2 := pow_le_pow_left₀ (norm_nonneg _) (hS k) 2
    linarith
  have h0 := hrow 0
  have h1 := hrow 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  linarith

/-- **Theorem "invertible active blocks", paper position three (Lean `p = 2`), upper half**, from
`CubeSumUpper 1` and `CubeSumUpper 2`. -/
theorem invertible_three_upper {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0)
    (h1 : CubeSumUpper 1) (h2 : CubeSumUpper 2) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → Zpos μ A φ χ 2 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4) := by
  obtain ⟨r₀, hr₀, c₀, hc₀, habs⟩ := two_absorb A (twoPrefix_injective hA)
  obtain ⟨Cq, hq⟩ := two_compare A
  exact upper_of_absorb A 2 (g := gTwo) (fun r hr => rowBound_split h1 h2 hr 2)
    measurable_gTwo (vTwo A) hr₀ hc₀ habs hq

/-- **Theorem "invertible active blocks", paper position three: the pair `(4, 1)`**, from
`CubeSumUpper 1` and `CubeSumUpper 2`, with the certified lower bound `Zpos_lower_N4`. -/
theorem invertible_three_pair {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0)
    (h1 : CubeSumUpper 1) (h2 : CubeSumUpper 2) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ᶠ θ in 𝓝 (basePos A 2), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      VectorSLT.SLT.HasLaplacePair (Zpos μ A φ χ 2) 4 1 :=
  pair_of_upper A 2 (invertible_three_upper hA h1 h2)

end VectorSLT.IdentityGroup.Pairs
