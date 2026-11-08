/-
L4, an end-to-end use of the volume ⇒ Laplace API: the one-variable monomial
`K(x) = x^{2k}` on `(0,1]` with Lebesgue measure has pair `(1/(2k), 1)`.
(The full normal-crossing lemma in `d` variables is `normalCrossing` / `normalCrossing_Z` in
SLT/NormalCrossingD.lean.)
-/
import VectorSLT.SLT.Laplace

namespace VectorSLT.SLT

open MeasureTheory Set Real

theorem volume_monomial_sublevel {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) :
    V (volume.restrict (Ioc (0 : ℝ) 1)) (fun x => x ^ (2 * k)) t =
      ENNReal.ofReal (min 1 (t ^ ((1 : ℝ) / (2 * k)))) := by
  have h2k : (2 * k : ℕ) ≠ 0 := by omega
  set r := t ^ ((1 : ℝ) / (2 * k))
  have hr : 0 < r := Real.rpow_pos_of_pos ht _
  have hrk : r ^ (2 * k) = t := by
    simp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    push_cast; field_simp; simp
  unfold V
  rw [Measure.restrict_apply (measurableSet_le (by fun_prop) measurable_const)]
  have hset : {x : ℝ | x ^ (2 * k) ≤ t} ∩ Ioc 0 1 = Ioc 0 (min 1 r) := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioc, le_min_iff]
    constructor
    · rintro ⟨hx, hx0, hx1⟩
      refine ⟨hx0, hx1, ?_⟩
      rw [← hrk] at hx
      exact (pow_le_pow_iff_left₀ hx0.le hr.le h2k).mp hx
    · rintro ⟨hx0, hx1, hxr⟩
      refine ⟨?_, hx0, hx1⟩
      rw [← hrk]; exact pow_le_pow_left₀ hx0.le hxr _
  rw [hset, Real.volume_Ioc, sub_zero]

theorem monomial_hasLaplacePair {k : ℕ} (hk : 1 ≤ k) :
    HasLaplacePair (Z (volume.restrict (Ioc (0 : ℝ) 1)) (fun x => x ^ (2 * k)))
      ((1 : ℝ) / (2 * k)) 1 := by
  have hlam : (0 : ℝ) < 1 / (2 * k) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  have hK : Measurable fun x : ℝ => x ^ (2 * k) := by fun_prop
  constructor
  · refine laplaceLower_of_volume hK one_pos one_pos fun t ht ht1 => ?_
    rw [volume_monomial_sublevel hk ht, Nat.sub_self, pow_zero, mul_one, one_mul]
    apply ENNReal.ofReal_le_ofReal
    rw [min_eq_right (Real.rpow_le_one ht.le ht1 hlam.le)]
  · refine laplaceUpper_of_volume (C := 1) hK (fun x => by rw [pow_mul]; positivity) zero_le_one
      hlam fun t ht => ?_
    rw [volume_monomial_sublevel hk ht, Nat.sub_self, pow_zero, mul_one, one_mul]
    exact ENNReal.ofReal_le_ofReal (min_le_right _ _)

end VectorSLT.SLT
