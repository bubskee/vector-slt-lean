/-
Brief 04, X4, part 1: the sup-norm error bound for target `A_η` (Lemma L′3 with base point
`(α, ν) = (1, η)`).

Source: cubic-chaos `approx_shear_crossover.md` §3 (pinned `caccd6a`).

Changes from `err_bound`:
* `c₂` is `3(α²ν + P₁ - η)` (Lemma X2), so `e = α²ν - η` is small but `ν ≈ η` is not;
* part 1 (`E1η`): `λ₀³ - ℓ³ + A s³ = c₃s³ + 3e s²t + 3(αν² - η²)st² + (ν³ - η³)t³`, and
  `α³(αν² - η²) = η²(1 - α³) + 2ηe + e²`, `α⁶(ν³ - η³) = η³(1 - α⁶) + 3η²e + 3ηe² + e³`;
  so the new hypothesis is `η² |A| ≤ ε` (the paper's `η² r³ ≤ C N^{-1/2}`);
* part 2 (`shiftη`, the paper's difference argument for `Δ₀`):
  `α₀²α₁²(ν₀ - ν₁) = α₁²(u₀ - u₁) + u₁(α₁² - α₀²)` with `uₖ = αₖ²νₖ`.
-/
import VectorSLT.EtaTarget

namespace VectorSLT

/-- **E1η**: the weight-zero part plus the `s³` part, for target `ℓ = s + η t`. -/
theorem E1η_bound {R ε s t α ν A P1 η l : ℝ} (hR : 1 ≤ R) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 10)
    (hs : |s| ≤ 2 * R) (ht : |t| ≤ R) (hα : 9 / 10 ≤ α ∧ α ≤ 11 / 10) (hη : |η| ≤ 1 / 10)
    (hηA : η ^ 2 * |A| ≤ ε)
    (hc3 : |α ^ 3 - 1 + A| ≤ ε) (hc2 : |3 * α ^ 2 * ν + 3 * P1 - 3 * η| ≤ ε) (hP1 : |P1| ≤ ε)
    (hl : l = α * s + ν * t) :
    |l ^ 3 - (s + η * t) ^ 3 + A * s ^ 3| ≤ 50 * R ^ 3 * ε := by
  have hR0 : 0 ≤ R := by linarith
  set e := α ^ 2 * ν - η with he
  have hae : |e| ≤ 4 / 3 * ε := by
    have h1 : 3 * e = (3 * α ^ 2 * ν + 3 * P1 - 3 * η) - 3 * P1 := by rw [he]; ring
    have h2 : |3 * e| ≤ 4 * ε := by
      rw [h1]; refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]; linarith
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)] at h2; linarith
  have hα3 : 729 / 1000 ≤ α ^ 3 := by nlinarith [hα.1]
  have hα3u : α ^ 3 ≤ 1331 / 1000 := by nlinarith [hα.2, hα.1]
  have h1a : |1 - α ^ 3| ≤ |A| + ε := by
    have : 1 - α ^ 3 = A - (α ^ 3 - 1 + A) := by ring
    rw [this]; exact (abs_sub _ _).trans (by linarith)
  have hη2 : η ^ 2 ≤ 1 / 100 := by
    have := sq_le_sq' (abs_le.mp hη).1 (abs_le.mp hη).2; linarith
  have hη2' : η ^ 2 * |1 - α ^ 3| ≤ 101 / 100 * ε := by
    have := mul_le_mul_of_nonneg_left h1a (sq_nonneg η)
    have : η ^ 2 * ε ≤ 1 / 100 * ε := mul_le_mul_of_nonneg_right hη2 hε0
    nlinarith [abs_nonneg A]
  have he2 : e ^ 2 ≤ 2 / 10 * ε := by
    have := sq_le_sq' (abs_le.mp hae).1 (abs_le.mp hae).2; nlinarith
  have hηe : |η * e| ≤ 2 / 10 * ε := by
    rw [abs_mul]; nlinarith [abs_nonneg η, abs_nonneg e]
  -- c₁ part
  set X1 := α * ν ^ 2 - η ^ 2
  have hX1e : α ^ 3 * X1 = η ^ 2 * (1 - α ^ 3) + 2 * (η * e) + e ^ 2 := by
    simp only [X1, he]; ring
  have hX1 : |X1| ≤ 3 * ε := by
    have hb : |α ^ 3 * X1| ≤ 101 / 100 * ε + 2 * (2 / 10 * ε) + 2 / 10 * ε := by
      rw [hX1e]
      refine (abs_add3_le _ _ _).trans ?_
      rw [abs_mul (η ^ 2), abs_of_nonneg (sq_nonneg η), abs_mul 2, abs_two,
        abs_of_nonneg (sq_nonneg e)]
      linarith
    rw [abs_mul, abs_of_pos (by linarith)] at hb
    have := mul_le_mul_of_nonneg_right hα3 (abs_nonneg X1)
    linarith
  -- c₀ part
  set X0 := ν ^ 3 - η ^ 3
  have hX0e : α ^ 6 * X0 = η * (η ^ 2 * (1 - α ^ 3)) * (1 + α ^ 3) + 3 * η * (η * e) +
      3 * η * e ^ 2 + e ^ 3 := by
    simp only [X0, he]; ring
  have hX0 : |X0| ≤ ε := by
    have hη1 : |η| ≤ 1 / 10 := hη
    have t1 : |η * (η ^ 2 * (1 - α ^ 3)) * (1 + α ^ 3)| ≤ 1 / 10 * (101 / 100 * ε) * (2331 / 1000) := by
      rw [abs_mul, abs_mul, abs_mul (η ^ 2), abs_of_nonneg (sq_nonneg η),
        abs_of_pos (by linarith : (0:ℝ) < 1 + α ^ 3)]
      have := mul_le_mul hη1 hη2' (by positivity) (by norm_num)
      exact mul_le_mul this (by linarith) (by linarith) (by positivity)
    have t2 : |3 * η * (η * e)| ≤ 3 * (1 / 10) * (2 / 10 * ε) := by
      rw [abs_mul, abs_mul 3, abs_of_pos (by norm_num : (0:ℝ) < 3)]
      exact mul_le_mul (by linarith) hηe (abs_nonneg _) (by positivity)
    have t3 : |3 * η * e ^ 2| ≤ 3 * (1 / 10) * (2 / 10 * ε) := by
      rw [abs_mul, abs_mul 3, abs_of_pos (by norm_num : (0:ℝ) < 3), abs_of_nonneg (sq_nonneg e)]
      exact mul_le_mul (by linarith) he2 (sq_nonneg _) (by positivity)
    have t4 : |e ^ 3| ≤ 1 / 20 * ε := by
      have e3 : |e ^ 3| = e ^ 2 * |e| := by rw [abs_pow, pow_succ, sq_abs]
      rw [e3]
      have h1 : |e| ≤ 4 / 30 := by linarith
      have := mul_le_mul he2 h1 (abs_nonneg _) (by positivity)
      linarith
    have hb : |α ^ 6 * X0| ≤ 1 / 2 * ε := by
      rw [hX0e]
      have := abs_add4_le (η * (η ^ 2 * (1 - α ^ 3)) * (1 + α ^ 3)) (3 * η * (η * e))
        (3 * η * e ^ 2) (e ^ 3)
      linarith
    have hα6 : 1 / 2 ≤ α ^ 6 := by
      have : α ^ 6 = α ^ 3 * α ^ 3 := by ring
      rw [this]; nlinarith
    rw [abs_mul, abs_of_pos (by linarith)] at hb
    have := mul_le_mul_of_nonneg_right hα6 (abs_nonneg X0)
    linarith
  have hdec : l ^ 3 - (s + η * t) ^ 3 + A * s ^ 3 = (α ^ 3 - 1 + A) * s ^ 3 +
      (3 * e) * (s ^ 2 * t) + (3 * X1) * (s * t ^ 2) + X0 * t ^ 3 := by
    rw [hl]; simp only [X1, X0, he]; ring
  rw [hdec]
  have hs3 : |s ^ 3| ≤ (2 * R) ^ 3 := abs_cube_le hs
  have hs2t : |s ^ 2 * t| ≤ (2 * R) ^ 2 * R := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hs 2) ht (abs_nonneg _) (by positivity)
  have hst2 : |s * t ^ 2| ≤ (2 * R) * R ^ 2 := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hs (pow_le_pow_left₀ (abs_nonneg _) ht 2) (by positivity) (by positivity)
  have ht3 : |t ^ 3| ≤ R ^ 3 := abs_cube_le ht
  have h3e : |3 * e| ≤ 4 * ε := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]; linarith
  have h3X : |3 * X1| ≤ 9 * ε := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]; linarith
  have t1 := mul_le_mul hc3 hs3 (abs_nonneg _) hε0
  have t2 := mul_le_mul h3e hs2t (abs_nonneg _) (by positivity)
  have t3 := mul_le_mul h3X hst2 (abs_nonneg _) (by positivity)
  have t4 := mul_le_mul hX0 ht3 (abs_nonneg _) hε0
  rw [← abs_mul] at t1 t2 t3 t4
  have hsum := abs_add4_le ((α ^ 3 - 1 + A) * s ^ 3) ((3 * e) * (s ^ 2 * t))
    ((3 * X1) * (s * t ^ 2)) (X0 * t ^ 3)
  have k1 : ε * (2 * R) ^ 3 = 8 * (R ^ 3 * ε) := by ring
  have k2 : 4 * ε * ((2 * R) ^ 2 * R) = 16 * (R ^ 3 * ε) := by ring
  have k3 : 9 * ε * ((2 * R) * R ^ 2) = 18 * (R ^ 3 * ε) := by ring
  have k4 : ε * R ^ 3 = R ^ 3 * ε := by ring
  have : 0 ≤ R ^ 3 * ε := by positivity
  linarith

/-- **The difference argument** (`Δ₀`): with `νₖ ≈ η` not small, `λ₀⁽⁰⁾ - λ₀⁽¹⁾` is still
`O(ε + ρ³)`, because `α₀²α₁²(ν₀ - ν₁) = α₁²(u₀ - u₁) + u₁(α₁² - α₀²)`, `uₖ = αₖ²νₖ`. -/
theorem shiftη_bound {R ε ρ s t η : ℝ} {α ν : Fin 2 → ℝ} {l : Fin 2 → ℝ} (hR : 1 ≤ R)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 10) (hρ : 0 ≤ ρ) (hη : |η| ≤ 1 / 10)
    (hs : |s| ≤ 2 * R) (ht : |t| ≤ R) (hl : ∀ k, l k = α k * s + ν k * t)
    (hlb : ∀ k, |l k| ≤ 3 * R) (hα : ∀ k, 9 / 10 ≤ α k ∧ α k ≤ 11 / 10)
    (hα1 : ∀ k, |α k - 1| ≤ ε + 3 * ρ ^ 3)
    (hu : ∀ k, |α k ^ 2 * ν k - η| ≤ 4 / 3 * ε) :
    |l 0 ^ 3 - l 1 ^ 3| ≤ R ^ 3 * (300 * ε + 460 * ρ ^ 3) := by
  have hR0 : 0 ≤ R := by linarith
  have hρ3 : 0 ≤ ε + 3 * ρ ^ 3 := (abs_nonneg _).trans (hα1 0)
  have hdα : |α 0 - α 1| ≤ 2 * (ε + 3 * ρ ^ 3) := by
    have : α 0 - α 1 = (α 0 - 1) - (α 1 - 1) := by ring
    rw [this]; exact (abs_sub _ _).trans (by linarith [hα1 0, hα1 1])
  set u0 := α 0 ^ 2 * ν 0
  set u1 := α 1 ^ 2 * ν 1
  have hdu : |u0 - u1| ≤ 8 / 3 * ε := by
    have : u0 - u1 = (u0 - η) - (u1 - η) := by ring
    rw [this]; exact (abs_sub _ _).trans (by linarith [hu 0, hu 1])
  have hu1 : |u1| ≤ 24 / 100 := by
    have : u1 = (u1 - η) + η := by ring
    rw [this]; refine (abs_add_le _ _).trans ?_; linarith [hu 1]
  have hdα2 : |α 1 ^ 2 - α 0 ^ 2| ≤ 22 / 10 * (2 * (ε + 3 * ρ ^ 3)) := by
    have e : α 1 ^ 2 - α 0 ^ 2 = -(α 0 - α 1) * (α 0 + α 1) := by ring
    rw [e, abs_mul, abs_neg, abs_of_pos (show 0 < α 0 + α 1 by linarith [(hα 0).1, (hα 1).1])]
    have := (hα 0).2; have := (hα 1).2
    nlinarith [abs_nonneg (α 0 - α 1)]
  have hnum : α 0 ^ 2 * α 1 ^ 2 * (ν 0 - ν 1) = α 1 ^ 2 * (u0 - u1) + u1 * (α 1 ^ 2 - α 0 ^ 2) := by
    simp only [u0, u1]; ring
  have ha12 : α 1 ^ 2 ≤ 121 / 100 := by nlinarith [(hα 1).1, (hα 1).2]
  have hden : 6561 / 10000 ≤ α 0 ^ 2 * α 1 ^ 2 := by
    have h0 : 81 / 100 ≤ α 0 ^ 2 := by nlinarith [(hα 0).1]
    have h1 : 81 / 100 ≤ α 1 ^ 2 := by nlinarith [(hα 1).1]
    nlinarith
  have hdν : |ν 0 - ν 1| ≤ 7 * ε + 5 * ρ ^ 3 := by
    have hb : |α 0 ^ 2 * α 1 ^ 2 * (ν 0 - ν 1)| ≤
        121 / 100 * (8 / 3 * ε) + 24 / 100 * (22 / 10 * (2 * (ε + 3 * ρ ^ 3))) := by
      rw [hnum]; refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (α 1))]
      exact add_le_add (mul_le_mul ha12 hdu (abs_nonneg _) (by norm_num))
        (mul_le_mul hu1 hdα2 (abs_nonneg _) (by norm_num))
    rw [abs_mul, abs_of_pos (by linarith)] at hb
    have hρ0 : 0 ≤ ρ ^ 3 := pow_nonneg hρ 3
    nlinarith [abs_nonneg (ν 0 - ν 1)]
  refine (cube_diff_le (hlb 0) (hlb 1)).trans ?_
  have hd : |l 0 - l 1| ≤ 2 * (ε + 3 * ρ ^ 3) * (2 * R) + (7 * ε + 5 * ρ ^ 3) * R := by
    rw [hl 0, hl 1, show α 0 * s + ν 0 * t - (α 1 * s + ν 1 * t) =
      (α 0 - α 1) * s + (ν 0 - ν 1) * t by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul hdα hs (abs_nonneg _) (by positivity))
      (mul_le_mul hdν ht (abs_nonneg _) ((abs_nonneg _).trans hdν))
  have := mul_le_mul_of_nonneg_left hd (show 0 ≤ 3 * (3 * R) ^ 2 by positivity)
  have hρ0 : 0 ≤ ρ ^ 3 := pow_nonneg hρ 3
  have e : 3 * (3 * R) ^ 2 * (2 * (ε + 3 * ρ ^ 3) * (2 * R) + (7 * ε + 5 * ρ ^ 3) * R) =
      R ^ 3 * (297 * ε + 459 * ρ ^ 3) := by ring
  have : R ^ 3 * (297 * ε + 459 * ρ ^ 3) ≤ R ^ 3 * (300 * ε + 460 * ρ ^ 3) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- E2 with the larger shift constant of `shiftη_bound`. -/
theorem E2η_bound {R ε ρ s S0 A : ℝ} (hR : 1 ≤ R) (hε0 : 0 ≤ ε) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hA : |A| ≤ 3 * ρ ^ 3) (hSb : |S0| ≤ 56 * R ^ 3) (hs : |s| ≤ 56 * R ^ 3)
    (hSs : |S0 - s| ≤ R ^ 3 * (300 * ε + 460 * ρ ^ 3)) :
    |A * (S0 ^ 3 - s ^ 3)| ≤ 2 * 10 ^ 7 * R ^ 9 * (ε + ρ ^ 6) := by
  have hd := cube_diff_le hSb hs
  rw [abs_mul]
  have h1 := mul_le_mul hA (hd.trans (mul_le_mul_of_nonneg_left hSs (by positivity)))
    (abs_nonneg _) (by positivity)
  have hρ3 : ρ ^ 3 ≤ 1 := pow_le_one₀ hρ0 hρ1
  have h2 : ρ ^ 3 * ε ≤ ε := by nlinarith
  have e : 3 * ρ ^ 3 * (3 * (56 * R ^ 3) ^ 2 * (R ^ 3 * (300 * ε + 460 * ρ ^ 3))) =
      28224 * R ^ 9 * (300 * (ρ ^ 3 * ε) + 460 * ρ ^ 6) := by ring
  rw [e] at h1
  have hR9 : 0 ≤ R ^ 9 := by positivity
  have h3 : 28224 * R ^ 9 * (300 * (ρ ^ 3 * ε) + 460 * ρ ^ 6) ≤
      28224 * R ^ 9 * (460 * ε + 460 * ρ ^ 6) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  have h4 : 28224 * R ^ 9 * (460 * ε + 460 * ρ ^ 6) ≤ 2 * 10 ^ 7 * R ^ 9 * (ε + ρ ^ 6) := by
    have := pow_nonneg hρ0 6
    have : 0 ≤ R ^ 9 * ε := by positivity
    have : 0 ≤ R ^ 9 * ρ ^ 6 := by positivity
    nlinarith
  linarith

set_option maxHeartbeats 1000000 in
/-- **Sup-norm error bound for target `A_η`** (Lemma L′3 of X4). The hypotheses of
`err_bound`, with `c₂ = 3(α²ν + P₁ - η)` (Lemma X2), `|η| ≤ 1/10`, and the new row condition
`η² |A| ≤ ε`. The output error `∑ λᵢ³ - ℓ³`, `ℓ = s + η t`, is at most `3·10¹² R¹⁵ (ε + ρ⁶)`. -/
theorem err_bound_eta {R ε ρ s t η : ℝ} (hR : 1 ≤ R) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 10) (hρ0 : 0 ≤ ρ)
    (hρ : ρ * R ^ 3 ≤ 1 / 1200) (hη : |η| ≤ 1 / 10) (hs : |s| ≤ 2 * R) (ht : |t| ≤ R)
    (α ν : Fin 2 → ℝ) (a b : Fin 2 → ℕ → ℝ) (lam : ℕ → Fin 2 → ℝ) (S T : ℕ → ℝ)
    (hα : ∀ k, 9 / 10 ≤ α k ∧ α k ≤ 11 / 10)
    (hab : ∀ k, ∀ i < 3, |a k i| ≤ ρ ∧ |b k i| ≤ ρ)
    (hP1 : ∀ k, |momP1 (a k) (b k)| ≤ ε) (hP2 : ∀ k, |momP2 (a k) (b k)| ≤ ε)
    (hP3 : ∀ k, |momP3 (b k)| ≤ ε)
    (hc3 : ∀ k, |α k ^ 3 - 1 + momA (a k)| ≤ ε)
    (hc2 : ∀ k, |3 * α k ^ 2 * ν k + 3 * momP1 (a k) (b k) - 3 * η| ≤ ε)
    (hηA : ∀ k, η ^ 2 * |momA (a k)| ≤ ε)
    (hl0 : ∀ k, lam 0 k = α k * s + ν k * t)
    (hS0 : S 0 = s + lam 0 0 ^ 3 - lam 0 1 ^ 3) (hT0 : T 0 = t + lam 0 1 ^ 3)
    (hl : ∀ i < 3, ∀ k, lam (i + 1) k = a k i * S i + b k i * T i)
    (hS : ∀ i < 3, S (i + 1) = S i + lam (i + 1) 0 ^ 3 - lam (i + 1) 1 ^ 3)
    (hT : ∀ i < 3, T (i + 1) = T i + lam (i + 1) 1 ^ 3)
    (k : Fin 2) :
    |lam 0 k ^ 3 + lam 1 k ^ 3 + lam 2 k ^ 3 + lam 3 k ^ 3 - (s + η * t) ^ 3| ≤
      3 * 10 ^ 12 * R ^ 15 * (ε + ρ ^ 6) := by
  have hR0 : 0 < R := by linarith
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
  have hRR : R ≤ R ^ 3 := le_self_pow₀ hR (by norm_num)
  have hρ1 : ρ ≤ 1 := by nlinarith
  have hu : ∀ k, |α k ^ 2 * ν k - η| ≤ 4 / 3 * ε := by
    intro k
    have h1 : 3 * (α k ^ 2 * ν k - η) =
        (3 * α k ^ 2 * ν k + 3 * momP1 (a k) (b k) - 3 * η) - 3 * momP1 (a k) (b k) := by ring
    have h2 : |3 * (α k ^ 2 * ν k - η)| ≤ 4 * ε := by
      rw [h1]; refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]; linarith [hc2 k, hP1 k]
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)] at h2; linarith
  have hν : ∀ k, |ν k| ≤ 3 / 10 := by
    intro k
    have h1 : |α k ^ 2 * ν k| ≤ 1 / 10 + 4 / 3 * ε := by
      have : α k ^ 2 * ν k = (α k ^ 2 * ν k - η) + η := by ring
      rw [this]; exact (abs_add_le _ _).trans (by linarith [hu k])
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)] at h1
    have ha2 : 81 / 100 ≤ α k ^ 2 := by nlinarith [(hα k).1]
    have := mul_le_mul_of_nonneg_right ha2 (abs_nonneg (ν k))
    linarith
  -- λ₀ bounded
  have hl0b : ∀ k, |lam 0 k| ≤ 3 * R := by
    intro k
    rw [hl0 k]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos (by linarith [(hα k).1] : 0 < α k)]
    have h1 := mul_le_mul (hα k).2 hs (abs_nonneg _) (by norm_num)
    have h2 := mul_le_mul (hν k) ht (abs_nonneg _) (by positivity)
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
  have hdecomp : lam 0 k ^ 3 + lam 1 k ^ 3 + lam 2 k ^ 3 + lam 3 k ^ 3 - (s + η * t) ^ 3 =
      (lam 0 k ^ 3 - (s + η * t) ^ 3 + momA (a k) * s ^ 3) + momA (a k) * (S 0 ^ 3 - s ^ 3) +
      (3 * momP1 (a k) (b k) * S 0 ^ 2 * T 0 + 3 * momP2 (a k) (b k) * S 0 * T 0 ^ 2 +
        momP3 (b k) * T 0 ^ 3) +
      ((lam 1 k ^ 3 - Lf 0 k ^ 3) + (lam 2 k ^ 3 - Lf 1 k ^ 3) + (lam 3 k ^ 3 - Lf 2 k ^ 3)) := by
    simp only [Lf, momA, momP1, momP2, momP3]; ring
  have hA : ∀ j, |momA (a j)| ≤ 3 * ρ ^ 3 := fun j => momA_le fun i hi => (hab j i hi).1
  have hE1 := E1η_bound hR hε0 hε hs ht (hα k) hη (hηA k) (hc3 k) (hc2 k) (hP1 k) (hl0 k)
  have hα1 : ∀ j, |α j - 1| ≤ ε + 3 * ρ ^ 3 := by
    intro j
    refine (abs_sub_one_le_cube (by linarith [(hα j).1])).trans ?_
    have := abs_sub (α j ^ 3 - 1 + momA (a j)) (momA (a j))
    rw [show α j ^ 3 - 1 + momA (a j) - momA (a j) = α j ^ 3 - 1 by ring] at this
    linarith [hc3 j, hA j]
  have hSs : |S 0 - s| ≤ R ^ 3 * (300 * ε + 460 * ρ ^ 3) := by
    rw [show S 0 - s = lam 0 0 ^ 3 - lam 0 1 ^ 3 by rw [hS0]; ring]
    exact shiftη_bound hR hε0 hε hρ0 hη hs ht hl0 hl0b hα hα1 hu
  have hE2 := E2η_bound hR hε0 hρ0 hρ1 (hA k) hSb (hs.trans (by linarith)) hSs
  have hE3 := E3_bound hR hε0 hSb hTb (hP1 k) (hP2 k) (hP3 k)
  rw [hdecomp]
  have hsum := abs_add4_le (lam 0 k ^ 3 - (s + η * t) ^ 3 + momA (a k) * s ^ 3)
    (momA (a k) * (S 0 ^ 3 - s ^ 3))
    (3 * momP1 (a k) (b k) * S 0 ^ 2 * T 0 + 3 * momP2 (a k) (b k) * S 0 * T 0 ^ 2 +
      momP3 (b k) * T 0 ^ 3)
    ((lam 1 k ^ 3 - Lf 0 k ^ 3) + (lam 2 k ^ 3 - Lf 1 k ^ 3) + (lam 3 k ^ 3 - Lf 2 k ^ 3))
  have h9 : R ^ 9 ≤ R ^ 15 := pow_le_pow_right₀ hR (by norm_num)
  have h3' : R ^ 3 ≤ R ^ 15 := pow_le_pow_right₀ hR (by norm_num)
  have hρ6 : 0 ≤ ρ ^ 6 := pow_nonneg hρ0 6
  have k1 : 50 * R ^ 3 * ε ≤ 50 * R ^ 15 * ε := by
    have := mul_le_mul_of_nonneg_right h3' hε0; linarith
  have k2 : 2 * 10 ^ 7 * R ^ 9 * (ε + ρ ^ 6) ≤ 2 * 10 ^ 7 * R ^ 15 * (ε + ρ ^ 6) := by
    have := mul_le_mul_of_nonneg_right h9 (add_nonneg hε0 hρ6); linarith
  have k3 : 5 * 10 ^ 5 * R ^ 9 * ε ≤ 5 * 10 ^ 5 * R ^ 15 * ε := by
    have := mul_le_mul_of_nonneg_right h9 hε0; linarith
  have : 0 ≤ R ^ 15 * ε := by positivity
  have : 0 ≤ R ^ 15 * ρ ^ 6 := by positivity
  nlinarith

end VectorSLT
