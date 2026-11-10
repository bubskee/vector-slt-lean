/-
Loss comparison, part 4: the elimination bound, at every position.

The active row `k` enters every error coefficient used here only through `u_k = α_k³` and
`m_k = α_k² ν_k`, after multiplying by a suitable power of `α_k³` (a polynomial `A`). So
`A f = F(z_act, w)` with `F` polynomial and `z_act = (u₀, m₀, u₁, m₁)`. At `𝐜 = 0` one would have
`z = z₀(w) = (1 - P₀⁽⁰⁾, -P₁⁽⁰⁾, 1 - P₀⁽¹⁾, -P₁⁽¹⁾)`, and `z_act - z₀ = (c₃⁽⁰⁾, c₂⁽⁰⁾/3, c₃⁽¹⁾, c₂⁽¹⁾/3)`
exactly (`zact_sub`). The eliminated coefficient `ĝ(w) = F(z₀(w), w)` is then a polynomial in `w`,
and since `F` is locally Lipschitz, `ĝ² ≤ K (f² + ‖𝐜‖²)` on any compact set (`elim_bound`). This
replaces the explicit multipliers of position four.
-/
import VectorSLT.LossCompare.Package

namespace VectorSLT.LossCompare

open MeasureTheory Set Filter Metric Topology VectorSLT VectorSLT.LeadingMap
open scoped ENNReal NNReal

/-- The active `(u₀, m₀, u₁, m₁) = (α₀³, α₀²ν₀, α₁³, α₁²ν₁)` at position `p`. -/
def zact (p : Fin 4) (θ : Raw16) : Fin 4 → ℝ :=
  ![(rowForm (rawW θ p) 0).1 ^ 3, (rowForm (rawW θ p) 0).1 ^ 2 * (rowForm (rawW θ p) 0).2,
    (rowForm (rawW θ p) 1).1 ^ 3, (rowForm (rawW θ p) 1).1 ^ 2 * (rowForm (rawW θ p) 1).2]

/-- The point `𝐜 = 0` in the coordinates `(u, m)`: `(1 - P₀⁽⁰⁾, -P₁⁽⁰⁾, 1 - P₀⁽¹⁾, -P₁⁽¹⁾)`. -/
def z0w (w : Fin 12 → ℝ) : Fin 4 → ℝ := ![1 - P0w w 0, -P1w w 0, 1 - P0w w 1, -P1w w 1]

theorem zact_sub (p : Fin 4) (θ : Raw16) :
    zact p θ - z0w (wOf p θ) =
      ![e30 (rawW θ) 0, e21 (rawW θ) 0 / 3, e30 (rawW θ) 1, e21 (rawW θ) 1 / 3] := by
  funext i
  fin_cases i <;> simp [zact, z0w, e30_split p, e21_split p] <;> ring

theorem continuous_zact (p : Fin 4) : Continuous (zact p) := by
  have hL := continuous_Lfun p
  have r00 : Continuous fun θ => (rowForm (rawW θ p) 0).1 :=
    continuous_fst.comp (continuous_fst.comp (continuous_fst.comp hL))
  have r01 : Continuous fun θ => (rowForm (rawW θ p) 0).2 :=
    continuous_snd.comp (continuous_fst.comp (continuous_fst.comp hL))
  have r10 : Continuous fun θ => (rowForm (rawW θ p) 1).1 :=
    continuous_fst.comp (continuous_snd.comp (continuous_fst.comp hL))
  have r11 : Continuous fun θ => (rowForm (rawW θ p) 1).2 :=
    continuous_snd.comp (continuous_snd.comp (continuous_fst.comp hL))
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp only [zact] <;> simp <;> fun_prop

theorem continuous_z0w : Continuous z0w := by
  have h0 := continuous_P0w
  have h1 := continuous_P1w
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp only [z0w] <;> simp <;> fun_prop

theorem norm_le_sum_abs (v : Fin 4 → ℝ) : ‖v‖ ≤ ∑ i, |v i| :=
  (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).mpr fun i => by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun i => |v i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)

theorem sq_sum5_le (x y z u v : ℝ) :
    (x + y + z + u + v) ^ 2 ≤ 5 * (x ^ 2 + y ^ 2 + z ^ 2 + u ^ 2 + v ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - u), sq_nonneg (x - v),
    sq_nonneg (y - z), sq_nonneg (y - u), sq_nonneg (y - v), sq_nonneg (z - u), sq_nonneg (z - v),
    sq_nonneg (u - v)]

/-- **The elimination bound.** If `A f = F(z_act, w)` with `F` of class `C¹` and `A` continuous,
then `F(z₀(w), w)² ≤ K (f² + ‖𝐜‖²)` on every compact set of parameters. -/
theorem elim_bound (p : Fin 4) {F : (Fin 4 → ℝ) × (Fin 12 → ℝ) → ℝ} (hF : ContDiff ℝ 1 F)
    {S : Set Raw16} (hS : IsCompact S) {A f : Raw16 → ℝ} (hA : Continuous A)
    (hid : ∀ θ, A θ * f θ = F (zact p θ, wOf p θ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ θ ∈ S, F (z0w (wOf p θ), wOf p θ) ^ 2 ≤ K * (f θ ^ 2 + ∑ i, cvec θ i ^ 2) := by
  set g1 : Raw16 → (Fin 4 → ℝ) × (Fin 12 → ℝ) := fun θ => (zact p θ, wOf p θ)
  set g2 : Raw16 → (Fin 4 → ℝ) × (Fin 12 → ℝ) := fun θ => (z0w (wOf p θ), wOf p θ)
  have hg1 : Continuous g1 := (continuous_zact p).prodMk (continuous_wOf p)
  have hg2 : Continuous g2 := (continuous_z0w.comp (continuous_wOf p)).prodMk (continuous_wOf p)
  have hT : IsCompact (g1 '' S ∪ g2 '' S) := (hS.image hg1).union (hS.image hg2)
  obtain ⟨KL, hKL⟩ := (hF.locallyLipschitz.locallyLipschitzOn (s := g1 '' S ∪ g2 '' S)).exists_lipschitzOnWith_of_compact hT
  obtain ⟨KA, hKA⟩ := hS.exists_bound_of_continuousOn hA.continuousOn
  set K' := max KA (KL : ℝ)
  have hK'0 : 0 ≤ K' := le_max_of_le_right KL.2
  refine ⟨5 * K' ^ 2, by positivity, fun θ hθ => ?_⟩
  have hc : ∀ i, |(zact p θ - z0w (wOf p θ)) i| ≤ |cvec θ i| := by
    intro i
    rw [zact_sub]
    fin_cases i <;> simp [cvec, abs_div] <;>
      exact div_le_self (abs_nonneg _) (by norm_num)
  have hdist : dist (g1 θ) (g2 θ) ≤ ∑ i, |cvec θ i| := by
    rw [dist_eq_norm]
    have : g1 θ - g2 θ = (zact p θ - z0w (wOf p θ), 0) := by
      simp only [g1, g2, Prod.mk_sub_mk, sub_self]
    rw [this, Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
    exact (norm_le_sum_abs _).trans (Finset.sum_le_sum fun i _ => hc i)
  have hlip : |F (g1 θ) - F (g2 θ)| ≤ KL * ∑ i, |cvec θ i| := by
    have := hKL.dist_le_mul (g1 θ) (Or.inl ⟨θ, hθ, rfl⟩) (g2 θ) (Or.inr ⟨θ, hθ, rfl⟩)
    rw [Real.dist_eq] at this
    exact this.trans (mul_le_mul_of_nonneg_left hdist KL.2)
  have hAθ : |A θ| ≤ K' := by
    have := hKA θ hθ; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hbound : |F (g2 θ)| ≤ K' * (|f θ| + ∑ i, |cvec θ i|) := by
    have e : F (g2 θ) = A θ * f θ - (F (g1 θ) - F (g2 θ)) := by rw [hid θ]; ring
    rw [e]
    calc |A θ * f θ - (F (g1 θ) - F (g2 θ))| ≤ |A θ * f θ| + |F (g1 θ) - F (g2 θ)| :=
          abs_sub _ _
      _ ≤ K' * |f θ| + K' * ∑ i, |cvec θ i| := by
          rw [abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_right hAθ (abs_nonneg _))
            (hlip.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
              (Finset.sum_nonneg fun i _ => abs_nonneg _)))
      _ = _ := by ring
  have h2 : F (g2 θ) ^ 2 ≤ (K' * (|f θ| + ∑ i, |cvec θ i|)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hbound 2
  have h5 := sq_sum5_le |f θ| |cvec θ 0| |cvec θ 1| |cvec θ 2| |cvec θ 3|
  simp only [sq_abs] at h5
  calc F (z0w (wOf p θ), wOf p θ) ^ 2 = F (g2 θ) ^ 2 := rfl
    _ ≤ (K' * (|f θ| + ∑ i, |cvec θ i|)) ^ 2 := h2
    _ = K' ^ 2 * (|f θ| + |cvec θ 0| + |cvec θ 1| + |cvec θ 2| + |cvec θ 3|) ^ 2 := by
        rw [Fin.sum_univ_four]; ring
    _ ≤ K' ^ 2 * (5 * (f θ ^ 2 + cvec θ 0 ^ 2 + cvec θ 1 ^ 2 + cvec θ 2 ^ 2 + cvec θ 3 ^ 2)) :=
        mul_le_mul_of_nonneg_left h5 (sq_nonneg _)
    _ = 5 * K' ^ 2 * (f θ ^ 2 + ∑ i, cvec θ i ^ 2) := by rw [Fin.sum_univ_four]; ring

end VectorSLT.LossCompare
