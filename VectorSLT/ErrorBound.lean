/-
Milestone D, analytic core: the sup-norm error bound behind Lemma L′3.

This follows the analytic alternative of `shear_position_one_lower_exact.md` §7: instead of
the weight-six coefficient identity (L′1), we bound `|λᵢ - Lᵢ|` and `|λᵢ³ - Lᵢ³|`
directly along the network trajectory on a compact input box. Everything here is a
statement about real numbers satisfying the (M2) recursion. The link to the actual network
`prefixNet` is in `FullNetwork.lean`.

Notation (paper → Lean):
* input coordinates `s = x - y`, `t = y`;
* active rows `λ₀⁽ᵏ⁾ = αₖ s + νₖ t` (`lam 0 k`);
* state after block `i` in `(s,t)`-coordinates: `(S i, T i)`, with `(S 0, T 0)` after the
  active block;
* inactive block `i ∈ {1,2,3}`, row `k`: `λᵢ⁽ᵏ⁾ = aₖ,ᵢ S_{i-1} + bₖ,ᵢ T_{i-1}` (`lam i k`),
  with Lean's `a k (i-1)`, `b k (i-1)`.
-/
import Mathlib

namespace VectorSLT

/-- Cube moments of one row: `A = ∑ aᵢ³`, `P_j = ∑ aᵢ^{3-j} bᵢ^j` (over the three blocks). -/
def momA (a : ℕ → ℝ) : ℝ := a 0 ^ 3 + a 1 ^ 3 + a 2 ^ 3
def momP1 (a b : ℕ → ℝ) : ℝ := a 0 ^ 2 * b 0 + a 1 ^ 2 * b 1 + a 2 ^ 2 * b 2
def momP2 (a b : ℕ → ℝ) : ℝ := a 0 * b 0 ^ 2 + a 1 * b 1 ^ 2 + a 2 * b 2 ^ 2
def momP3 (b : ℕ → ℝ) : ℝ := b 0 ^ 3 + b 1 ^ 3 + b 2 ^ 3

theorem cube_diff_le {x y m : ℝ} (hx : |x| ≤ m) (hy : |y| ≤ m) :
    |x ^ 3 - y ^ 3| ≤ 3 * m ^ 2 * |x - y| := by
  have hm : 0 ≤ m := (abs_nonneg x).trans hx
  have e : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
  rw [e, abs_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have h1 : x ^ 2 ≤ m ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  have h2 : y ^ 2 ≤ m ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
  have h3 : |x * y| ≤ m ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul hx hy (abs_nonneg _) hm
  calc |x ^ 2 + x * y + y ^ 2| ≤ x ^ 2 + |x * y| + y ^ 2 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_nonneg (sq_nonneg y)]
        exact add_le_add ((abs_add_le _ _).trans (by rw [abs_of_nonneg (sq_nonneg x)])) le_rfl
    _ ≤ 3 * m ^ 2 := by linarith

theorem abs_cube_le {x m : ℝ} (hx : |x| ≤ m) : |x ^ 3| ≤ m ^ 3 := by
  rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hx 3

theorem abs_add3_le (x y z : ℝ) : |x + y + z| ≤ |x| + |y| + |z| :=
  (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)

theorem abs_add4_le (x y z w : ℝ) : |x + y + z + w| ≤ |x| + |y| + |z| + |w| :=
  (abs_add_le _ _).trans (add_le_add (abs_add3_le _ _ _) le_rfl)

theorem abs_lin_le {a b x y ρ : ℝ} (ha : |a| ≤ ρ) (hb : |b| ≤ ρ) :
    |a * x + b * y| ≤ ρ * (|x| + |y|) := by
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
    (mul_le_mul_of_nonneg_right hb (abs_nonneg _))

theorem momA_le {a : ℕ → ℝ} {ρ : ℝ} (h : ∀ i < 3, |a i| ≤ ρ) : |momA a| ≤ 3 * ρ ^ 3 := by
  unfold momA
  have := abs_add3_le (a 0 ^ 3) (a 1 ^ 3) (a 2 ^ 3)
  linarith [abs_cube_le (h 0 (by norm_num)), abs_cube_le (h 1 (by norm_num)),
    abs_cube_le (h 2 (by norm_num))]

/-- `|ν| ≤ 2ε` from `|3α²ν + 3P₁| ≤ ε`, `|P₁| ≤ ε`, `α ≥ 0.9`. -/
theorem nu_le {α ν P1 ε : ℝ} (hα : 9 / 10 ≤ α) (hc2 : |3 * α ^ 2 * ν + 3 * P1| ≤ ε)
    (hP1 : |P1| ≤ ε) : |ν| ≤ 2 * ε := by
  have e : 3 * α ^ 2 * ν = (3 * α ^ 2 * ν + 3 * P1) - 3 * P1 := by ring
  have h : |3 * α ^ 2 * ν| ≤ 4 * ε := by
    rw [e]; refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]; linarith
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 3 * α ^ 2)] at h
  have hα2 : 81 / 100 ≤ α ^ 2 := by nlinarith
  have h0 := abs_nonneg ν
  have : 3 * (81 / 100) * |ν| ≤ 3 * α ^ 2 * |ν| :=
    mul_le_mul_of_nonneg_right (by linarith) h0
  linarith

/-- `|α - 1| ≤ |α³ - 1|` for `α ≥ 0`. -/
theorem abs_sub_one_le_cube {α : ℝ} (hα : 0 ≤ α) : |α - 1| ≤ |α ^ 3 - 1| := by
  have e : α ^ 3 - 1 = (α - 1) * (α ^ 2 + α + 1) := by ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < α ^ 2 + α + 1)]
  have : 1 ≤ α ^ 2 + α + 1 := by nlinarith
  nlinarith [abs_nonneg (α - 1)]

/-- E1: the weight-zero part plus the `s³` part of weight three. -/
theorem E1_bound {R ε s t α ν A P1 l : ℝ} (hR : 1 ≤ R) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 10)
    (hs : |s| ≤ 2 * R) (ht : |t| ≤ R) (hα : 9 / 10 ≤ α ∧ α ≤ 11 / 10) (hν : |ν| ≤ 2 * ε)
    (hc3 : |α ^ 3 - 1 + A| ≤ ε) (hc2 : |3 * α ^ 2 * ν + 3 * P1| ≤ ε) (hP1 : |P1| ≤ ε)
    (hl : l = α * s + ν * t) :
    |l ^ 3 - s ^ 3 + A * s ^ 3| ≤ 50 * R ^ 3 * ε := by
  have hR0 : 0 ≤ R := by linarith
  have e : l ^ 3 - s ^ 3 + A * s ^ 3 = (α ^ 3 - 1 + A) * s ^ 3 +
      ((3 * α ^ 2 * ν + 3 * P1) - 3 * P1) * (s ^ 2 * t) +
      (3 * α * ν ^ 2) * (s * t ^ 2) + ν ^ 3 * t ^ 3 := by rw [hl]; ring
  rw [e]
  have hs3 : |s ^ 3| ≤ (2 * R) ^ 3 := abs_cube_le hs
  have hs2t : |s ^ 2 * t| ≤ (2 * R) ^ 2 * R := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hs 2) ht (abs_nonneg _) (by positivity)
  have hst2 : |s * t ^ 2| ≤ (2 * R) * R ^ 2 := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hs (pow_le_pow_left₀ (abs_nonneg _) ht 2) (by positivity) (by positivity)
  have ht3 : |t ^ 3| ≤ R ^ 3 := abs_cube_le ht
  have hc2' : |(3 * α ^ 2 * ν + 3 * P1) - 3 * P1| ≤ 4 * ε := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]; linarith
  have hν2 : ν ^ 2 ≤ (2 * ε) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hν 2
  have h3a : |3 * α * ν ^ 2| ≤ 4 * (2 * ε) ^ 2 := by
    rw [abs_of_nonneg (by have := hα.1; positivity)]
    have : 3 * α ≤ 4 := by linarith [hα.2]
    exact mul_le_mul this hν2 (sq_nonneg _) (by norm_num)
  have t1 := mul_le_mul hc3 hs3 (abs_nonneg _) hε0
  have t2 := mul_le_mul hc2' hs2t (abs_nonneg _) (by positivity)
  have t3 := mul_le_mul h3a hst2 (abs_nonneg _) (by positivity)
  have t4 := mul_le_mul (abs_cube_le hν) ht3 (abs_nonneg _) (by positivity)
  rw [← abs_mul] at t1 t2 t3 t4
  have hsum := abs_add4_le ((α ^ 3 - 1 + A) * s ^ 3)
    (((3 * α ^ 2 * ν + 3 * P1) - 3 * P1) * (s ^ 2 * t)) ((3 * α * ν ^ 2) * (s * t ^ 2))
    (ν ^ 3 * t ^ 3)
  have hR3 : 0 ≤ R ^ 3 := by positivity
  have hε2 : ε ^ 2 ≤ ε / 10 := by nlinarith
  have hε3 : ε ^ 3 ≤ ε / 100 := by nlinarith
  have k1 : ε * (2 * R) ^ 3 = 8 * (R ^ 3 * ε) := by ring
  have k2 : 4 * ε * ((2 * R) ^ 2 * R) = 16 * (R ^ 3 * ε) := by ring
  have k3 : 4 * (2 * ε) ^ 2 * ((2 * R) * R ^ 2) = 32 * (R ^ 3 * ε ^ 2) := by ring
  have k4 : (2 * ε) ^ 3 * R ^ 3 = 8 * (R ^ 3 * ε ^ 3) := by ring
  have m2 : R ^ 3 * ε ^ 2 ≤ R ^ 3 * (ε / 10) := mul_le_mul_of_nonneg_left hε2 hR3
  have m3 : R ^ 3 * ε ^ 3 ≤ R ^ 3 * (ε / 100) := mul_le_mul_of_nonneg_left hε3 hR3
  nlinarith

/-- E2: `|A (S₀³ - s³)|`, the shift of the cubic's argument. -/
theorem E2_bound {R ε ρ s S0 A : ℝ} (hR : 1 ≤ R) (hε0 : 0 ≤ ε) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hA : |A| ≤ 3 * ρ ^ 3) (hSb : |S0| ≤ 56 * R ^ 3) (hs : |s| ≤ 56 * R ^ 3)
    (hSs : |S0 - s| ≤ R ^ 3 * (216 * ε + 324 * ρ ^ 3)) :
    |A * (S0 ^ 3 - s ^ 3)| ≤ 10 ^ 7 * R ^ 9 * (ε + ρ ^ 6) := by
  have hd := cube_diff_le hSb hs
  rw [abs_mul]
  have h1 := mul_le_mul hA (hd.trans (mul_le_mul_of_nonneg_left hSs (by positivity)))
    (abs_nonneg _) (by positivity)
  have hρ3 : ρ ^ 3 ≤ 1 := pow_le_one₀ hρ0 hρ1
  have h2 : ρ ^ 3 * ε ≤ ε := by nlinarith
  have e : 3 * ρ ^ 3 * (3 * (56 * R ^ 3) ^ 2 * (R ^ 3 * (216 * ε + 324 * ρ ^ 3))) =
      28224 * R ^ 9 * (216 * (ρ ^ 3 * ε) + 324 * ρ ^ 6) := by ring
  rw [e] at h1
  have hR9 : 0 ≤ R ^ 9 := by positivity
  have h3 : 28224 * R ^ 9 * (216 * (ρ ^ 3 * ε) + 324 * ρ ^ 6) ≤
      28224 * R ^ 9 * (216 * ε + 324 * ρ ^ 6) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  have h4 : 28224 * R ^ 9 * (216 * ε + 324 * ρ ^ 6) ≤ 10 ^ 7 * R ^ 9 * (ε + ρ ^ 6) := by
    have := pow_nonneg hρ0 6
    have : 0 ≤ R ^ 9 * ε := by positivity
    have : 0 ≤ R ^ 9 * ρ ^ 6 := by positivity
    nlinarith
  linarith

/-- E3: the remaining moments of the frozen-state cubic. -/
theorem E3_bound {R ε S0 T0 P1 P2 P3 : ℝ} (hR : 1 ≤ R) (hε0 : 0 ≤ ε)
    (hSb : |S0| ≤ 56 * R ^ 3) (hTb : |T0| ≤ 28 * R ^ 3)
    (hP1 : |P1| ≤ ε) (hP2 : |P2| ≤ ε) (hP3 : |P3| ≤ ε) :
    |3 * P1 * S0 ^ 2 * T0 + 3 * P2 * S0 * T0 ^ 2 + P3 * T0 ^ 3| ≤ 5 * 10 ^ 5 * R ^ 9 * ε := by
  have hR0 : 0 ≤ R := by linarith
  have hS2 : |S0 ^ 2 * T0| ≤ (56 * R ^ 3) ^ 2 * (28 * R ^ 3) := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hSb 2) hTb (abs_nonneg _) (by positivity)
  have hT2 : |S0 * T0 ^ 2| ≤ (56 * R ^ 3) * (28 * R ^ 3) ^ 2 := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hSb (pow_le_pow_left₀ (abs_nonneg _) hTb 2) (by positivity) (by positivity)
  have hT3 : |T0 ^ 3| ≤ (28 * R ^ 3) ^ 3 := abs_cube_le hTb
  have e : 3 * P1 * S0 ^ 2 * T0 + 3 * P2 * S0 * T0 ^ 2 + P3 * T0 ^ 3 =
      3 * (P1 * (S0 ^ 2 * T0)) + 3 * (P2 * (S0 * T0 ^ 2)) + P3 * T0 ^ 3 := by ring
  rw [e]
  have t1 := mul_le_mul hP1 hS2 (abs_nonneg _) hε0
  have t2 := mul_le_mul hP2 hT2 (abs_nonneg _) hε0
  have t3 := mul_le_mul hP3 hT3 (abs_nonneg _) hε0
  rw [← abs_mul] at t1 t2 t3
  have := abs_add3_le (3 * (P1 * (S0 ^ 2 * T0))) (3 * (P2 * (S0 * T0 ^ 2))) (P3 * T0 ^ 3)
  rw [abs_mul 3, abs_mul 3, abs_of_pos (by norm_num : (0:ℝ) < 3)] at this
  have k : 3 * (ε * ((56 * R ^ 3) ^ 2 * (28 * R ^ 3))) + 3 * (ε * ((56 * R ^ 3) *
      (28 * R ^ 3) ^ 2)) + ε * (28 * R ^ 3) ^ 3 = 417088 * (R ^ 9 * ε) := by ring
  have : 0 ≤ R ^ 9 * ε := by positivity
  nlinarith

/-- The shift `S₀ - s = λ₀⁽¹⁾³ - λ₀⁽²⁾³` is `O(ε + ρ³)`. -/
theorem shift_bound {R ε ρ s t : ℝ} {α ν : Fin 2 → ℝ} {l : Fin 2 → ℝ} (hR : 1 ≤ R)
    (hs : |s| ≤ 2 * R) (ht : |t| ≤ R) (hl : ∀ k, l k = α k * s + ν k * t)
    (hlb : ∀ k, |l k| ≤ 3 * R) (hα1 : ∀ k, |α k - 1| ≤ ε + 3 * ρ ^ 3)
    (hν : ∀ k, |ν k| ≤ 2 * ε) :
    |l 0 ^ 3 - l 1 ^ 3| ≤ R ^ 3 * (216 * ε + 324 * ρ ^ 3) := by
  have hR0 : 0 ≤ R := by linarith
  refine (cube_diff_le (hlb 0) (hlb 1)).trans ?_
  have hd : |l 0 - l 1| ≤ 2 * (ε + 3 * ρ ^ 3) * (2 * R) + 4 * ε * R := by
    rw [hl 0, hl 1, show α 0 * s + ν 0 * t - (α 1 * s + ν 1 * t) =
      ((α 0 - 1) - (α 1 - 1)) * s + (ν 0 - ν 1) * t by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |(α 0 - 1) - (α 1 - 1)| ≤ 2 * (ε + 3 * ρ ^ 3) := by
      linarith [abs_sub (α 0 - 1) (α 1 - 1), hα1 0, hα1 1]
    have h2 : |ν 0 - ν 1| ≤ 4 * ε := by linarith [abs_sub (ν 0) (ν 1), hν 0, hν 1]
    exact add_le_add (mul_le_mul h1 hs (abs_nonneg _) ((abs_nonneg _).trans h1))
      (mul_le_mul h2 ht (abs_nonneg _) ((abs_nonneg _).trans h2))
  have := mul_le_mul_of_nonneg_left hd (show 0 ≤ 3 * (3 * R) ^ 2 by positivity)
  have e : 3 * (3 * R) ^ 2 * (2 * (ε + 3 * ρ ^ 3) * (2 * R) + 4 * ε * R) =
      R ^ 3 * (216 * ε + 324 * ρ ^ 3) := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- **Sup-norm error bound** (analytic Lemma L′3). Under the region bounds
(`|inactive| ≤ ρ`, `|Pⱼ| ≤ ε`, `|c₃| ≤ ε`, `|c₂| ≤ ε`, `α ∈ [0.9, 1.1]`) and for inputs with
`|s| ≤ 2R`, `|t| ≤ R`, the output error `∑_{i=0}^3 λᵢ³ - s³` of each row is at most
`3·10¹² R¹⁵ (ε + ρ⁶)`. -/
theorem err_bound {R ε ρ s t : ℝ} (hR : 1 ≤ R) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 10) (hρ0 : 0 ≤ ρ)
    (hρ : ρ * R ^ 3 ≤ 1 / 1200) (hs : |s| ≤ 2 * R) (ht : |t| ≤ R)
    (α ν : Fin 2 → ℝ) (a b : Fin 2 → ℕ → ℝ) (lam : ℕ → Fin 2 → ℝ) (S T : ℕ → ℝ)
    (hα : ∀ k, 9 / 10 ≤ α k ∧ α k ≤ 11 / 10)
    (hab : ∀ k, ∀ i < 3, |a k i| ≤ ρ ∧ |b k i| ≤ ρ)
    (hP1 : ∀ k, |momP1 (a k) (b k)| ≤ ε) (hP2 : ∀ k, |momP2 (a k) (b k)| ≤ ε)
    (hP3 : ∀ k, |momP3 (b k)| ≤ ε)
    (hc3 : ∀ k, |α k ^ 3 - 1 + momA (a k)| ≤ ε)
    (hc2 : ∀ k, |3 * α k ^ 2 * ν k + 3 * momP1 (a k) (b k)| ≤ ε)
    (hl0 : ∀ k, lam 0 k = α k * s + ν k * t)
    (hS0 : S 0 = s + lam 0 0 ^ 3 - lam 0 1 ^ 3) (hT0 : T 0 = t + lam 0 1 ^ 3)
    (hl : ∀ i < 3, ∀ k, lam (i + 1) k = a k i * S i + b k i * T i)
    (hS : ∀ i < 3, S (i + 1) = S i + lam (i + 1) 0 ^ 3 - lam (i + 1) 1 ^ 3)
    (hT : ∀ i < 3, T (i + 1) = T i + lam (i + 1) 1 ^ 3)
    (k : Fin 2) :
    |lam 0 k ^ 3 + lam 1 k ^ 3 + lam 2 k ^ 3 + lam 3 k ^ 3 - s ^ 3| ≤
      3 * 10 ^ 12 * R ^ 15 * (ε + ρ ^ 6) := by
  have hR0 : 0 < R := by linarith
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
  have hRR : R ≤ R ^ 3 := le_self_pow₀ hR (by norm_num)
  have hρ1 : ρ ≤ 1 := by nlinarith
  have hν : ∀ k, |ν k| ≤ 2 * ε := fun k => nu_le (hα k).1 (hc2 k) (hP1 k)
  -- λ₀ bounded
  have hl0b : ∀ k, |lam 0 k| ≤ 3 * R := by
    intro k
    rw [hl0 k]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos (by linarith [(hα k).1] : 0 < α k)]
    have h1 := mul_le_mul (hα k).2 hs (abs_nonneg _) (by norm_num)
    have h2 := mul_le_mul (hν k) ht (abs_nonneg _) (by positivity)
    have : 2 * ε * R ≤ 1 / 5 * R := by nlinarith
    linarith
  have hl0c : ∀ k, |lam 0 k ^ 3| ≤ 27 * R ^ 3 := fun k => by
    have := abs_cube_le (hl0b k); linarith [show (3 * R) ^ 3 = 27 * R ^ 3 by ring]
  -- initial state
  have hSb : |S 0| ≤ 56 * R ^ 3 := by
    rw [hS0]
    have h1 := (abs_sub (s + lam 0 0 ^ 3) (lam 0 1 ^ 3)).trans
      (add_le_add (abs_add_le s _) le_rfl)
    linarith [hl0c 0, hl0c 1]
  have hTb : |T 0| ≤ 28 * R ^ 3 := by
    rw [hT0]
    have := abs_add_le t (lam 0 1 ^ 3)
    linarith [hl0c 1]
  -- trajectory: μ = 120 ρ R³ ≤ 1/10
  set μ := 120 * ρ * R ^ 3 with hμ
  have hμ0 : 0 ≤ μ := by positivity
  have hμ1 : μ ≤ 1 / 10 := by rw [hμ]; linarith
  have hμ3 : μ ^ 3 ≤ μ / 100 := by
    have : μ ^ 2 ≤ 1 / 100 := by nlinarith
    nlinarith
  have hlam_of : ∀ i < 3, |S i| + |T i| ≤ 120 * R ^ 3 → ∀ k, |lam (i + 1) k| ≤ μ := by
    intro i hi hST k
    obtain ⟨ha, hb⟩ := hab k i hi
    rw [hl i hi k]
    calc _ ≤ ρ * (|S i| + |T i|) := abs_lin_le ha hb
      _ ≤ ρ * (120 * R ^ 3) := mul_le_mul_of_nonneg_left hST hρ0
      _ = μ := by rw [hμ]; ring
  have hdS : ∀ i < 3, (∀ k, |lam (i + 1) k| ≤ μ) →
      |S (i + 1) - S i| ≤ 2 * μ ^ 3 ∧ |T (i + 1) - T i| ≤ μ ^ 3 := by
    intro i hi h
    have c0 := abs_cube_le (h 0)
    have c1 := abs_cube_le (h 1)
    constructor
    · rw [hS i hi, show S i + lam (i + 1) 0 ^ 3 - lam (i + 1) 1 ^ 3 - S i =
        lam (i + 1) 0 ^ 3 - lam (i + 1) 1 ^ 3 by ring]
      linarith [abs_sub (lam (i + 1) 0 ^ 3) (lam (i + 1) 1 ^ 3)]
    · rw [hT i hi, add_sub_cancel_left]; exact c1
  have hST0 : |S 0| + |T 0| ≤ 120 * R ^ 3 := by linarith
  have hl1 := hlam_of 0 (by norm_num) hST0
  obtain ⟨dS1, dT1⟩ := hdS 0 (by norm_num) hl1
  have hST1 : |S 1| + |T 1| ≤ 120 * R ^ 3 := by
    have := abs_sub_abs_le_abs_sub (S 1) (S 0)
    have := abs_sub_abs_le_abs_sub (T 1) (T 0)
    linarith
  have hl2 := hlam_of 1 (by norm_num) hST1
  obtain ⟨dS2, dT2⟩ := hdS 1 (by norm_num) hl2
  have hD2 : |S 2 - S 0| + |T 2 - T 0| ≤ 6 * μ ^ 3 := by
    have := abs_sub_le (S 2) (S 1) (S 0)
    have := abs_sub_le (T 2) (T 1) (T 0)
    linarith
  have hST2 : |S 2| + |T 2| ≤ 120 * R ^ 3 := by
    have := abs_sub_abs_le_abs_sub (S 2) (S 0)
    have := abs_sub_abs_le_abs_sub (T 2) (T 0)
    linarith
  have hl3 := hlam_of 2 (by norm_num) hST2
  have hD1 : |S 1 - S 0| + |T 1 - T 0| ≤ 6 * μ ^ 3 := by linarith [pow_nonneg hμ0 3]
  have hD0 : |S 0 - S 0| + |T 0 - T 0| ≤ 6 * μ ^ 3 := by simp; positivity
  -- frozen-state forms Lᵢ = aᵢ S₀ + bᵢ T₀
  set Lf : ℕ → Fin 2 → ℝ := fun i k => a k i * S 0 + b k i * T 0
  have hLb : ∀ i < 3, ∀ k, |Lf i k| ≤ μ := by
    intro i hi k
    obtain ⟨ha, hb⟩ := hab k i hi
    calc |Lf i k| ≤ ρ * (|S 0| + |T 0|) := abs_lin_le ha hb
      _ ≤ ρ * (120 * R ^ 3) := mul_le_mul_of_nonneg_left hST0 hρ0
      _ = μ := by rw [hμ]; ring
  have hcmp : ∀ i < 3, |S i - S 0| + |T i - T 0| ≤ 6 * μ ^ 3 →
      (∀ k, |lam (i + 1) k| ≤ μ) → ∀ k,
      |lam (i + 1) k ^ 3 - Lf i k ^ 3| ≤ 18 * ρ * μ ^ 5 := by
    intro i hi hD hlb k
    obtain ⟨ha, hb⟩ := hab k i hi
    have hdiff : |lam (i + 1) k - Lf i k| ≤ ρ * (6 * μ ^ 3) := by
      rw [hl i hi k, show a k i * S i + b k i * T i - Lf i k =
        a k i * (S i - S 0) + b k i * (T i - T 0) by simp only [Lf]; ring]
      exact (abs_lin_le ha hb).trans (mul_le_mul_of_nonneg_left hD hρ0)
    calc |lam (i + 1) k ^ 3 - Lf i k ^ 3| ≤ 3 * μ ^ 2 * |lam (i + 1) k - Lf i k| :=
          cube_diff_le (hlb k) (hLb i hi k)
      _ ≤ 3 * μ ^ 2 * (ρ * (6 * μ ^ 3)) := mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = 18 * ρ * μ ^ 5 := by ring
  have hE4 : |(lam 1 k ^ 3 - Lf 0 k ^ 3) + (lam 2 k ^ 3 - Lf 1 k ^ 3) +
      (lam 3 k ^ 3 - Lf 2 k ^ 3)| ≤ 54 * ρ * μ ^ 5 := by
    have e1 := hcmp 0 (by norm_num) hD0 hl1 k
    have e2 := hcmp 1 (by norm_num) hD1 hl2 k
    have e3 := hcmp 2 (by norm_num) hD2 hl3 k
    have := abs_add3_le (lam 1 k ^ 3 - Lf 0 k ^ 3) (lam 2 k ^ 3 - Lf 1 k ^ 3)
      (lam 3 k ^ 3 - Lf 2 k ^ 3)
    linarith
  have hE4' : 54 * ρ * μ ^ 5 ≤ 2.1 * 10 ^ 12 * R ^ 15 * ρ ^ 6 := by
    have e : 54 * ρ * μ ^ 5 = 54 * 120 ^ 5 * (R ^ 15 * ρ ^ 6) := by rw [hμ]; ring
    have : 0 ≤ R ^ 15 * ρ ^ 6 := by positivity
    rw [e]; nlinarith
  -- decomposition err = E1 + E2 + E3 + E4
  have hdecomp : lam 0 k ^ 3 + lam 1 k ^ 3 + lam 2 k ^ 3 + lam 3 k ^ 3 - s ^ 3 =
      (lam 0 k ^ 3 - s ^ 3 + momA (a k) * s ^ 3) + momA (a k) * (S 0 ^ 3 - s ^ 3) +
      (3 * momP1 (a k) (b k) * S 0 ^ 2 * T 0 + 3 * momP2 (a k) (b k) * S 0 * T 0 ^ 2 +
        momP3 (b k) * T 0 ^ 3) +
      ((lam 1 k ^ 3 - Lf 0 k ^ 3) + (lam 2 k ^ 3 - Lf 1 k ^ 3) + (lam 3 k ^ 3 - Lf 2 k ^ 3)) := by
    simp only [Lf, momA, momP1, momP2, momP3]; ring
  have hE1 := E1_bound hR hε0 hε hs ht (hα k) (hν k) (hc3 k) (hc2 k) (hP1 k) (hl0 k)
  have hA : ∀ j, |momA (a j)| ≤ 3 * ρ ^ 3 := fun j => momA_le fun i hi => (hab j i hi).1
  have hα1 : ∀ j, |α j - 1| ≤ ε + 3 * ρ ^ 3 := by
    intro j
    refine (abs_sub_one_le_cube (by linarith [(hα j).1])).trans ?_
    have := abs_sub (α j ^ 3 - 1 + momA (a j)) (momA (a j))
    rw [show α j ^ 3 - 1 + momA (a j) - momA (a j) = α j ^ 3 - 1 by ring] at this
    linarith [hc3 j, hA j]
  have hSs : |S 0 - s| ≤ R ^ 3 * (216 * ε + 324 * ρ ^ 3) := by
    rw [show S 0 - s = lam 0 0 ^ 3 - lam 0 1 ^ 3 by rw [hS0]; ring]
    exact shift_bound hR hs ht hl0 hl0b hα1 hν
  have hE2 := E2_bound hR hε0 hρ0 hρ1 (hA k) hSb (hs.trans (by linarith)) hSs
  have hE3 := E3_bound hR hε0 hSb hTb (hP1 k) (hP2 k) (hP3 k)
  rw [hdecomp]
  have hsum := abs_add4_le (lam 0 k ^ 3 - s ^ 3 + momA (a k) * s ^ 3)
    (momA (a k) * (S 0 ^ 3 - s ^ 3))
    (3 * momP1 (a k) (b k) * S 0 ^ 2 * T 0 + 3 * momP2 (a k) (b k) * S 0 * T 0 ^ 2 +
      momP3 (b k) * T 0 ^ 3)
    ((lam 1 k ^ 3 - Lf 0 k ^ 3) + (lam 2 k ^ 3 - Lf 1 k ^ 3) + (lam 3 k ^ 3 - Lf 2 k ^ 3))
  have h9 : R ^ 9 ≤ R ^ 15 := pow_le_pow_right₀ hR (by norm_num)
  have h3' : R ^ 3 ≤ R ^ 15 := pow_le_pow_right₀ hR (by norm_num)
  have hρ6 : 0 ≤ ρ ^ 6 := pow_nonneg hρ0 6
  have k1 : 50 * R ^ 3 * ε ≤ 50 * R ^ 15 * ε := by
    have := mul_le_mul_of_nonneg_right h3' hε0; linarith
  have k2 : 10 ^ 7 * R ^ 9 * (ε + ρ ^ 6) ≤ 10 ^ 7 * R ^ 15 * (ε + ρ ^ 6) := by
    have := mul_le_mul_of_nonneg_right h9 (add_nonneg hε0 hρ6); linarith
  have k3 : 5 * 10 ^ 5 * R ^ 9 * ε ≤ 5 * 10 ^ 5 * R ^ 15 * ε := by
    have := mul_le_mul_of_nonneg_right h9 hε0; linarith
  have : 0 ≤ R ^ 15 * ε := by positivity
  have : 0 ≤ R ^ 15 * ρ ^ 6 := by positivity
  nlinarith

end VectorSLT
