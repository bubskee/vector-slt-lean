/-
L6 stage 3, F4: Lemma M3's hypotheses for the (M9) `E` with amplitude-dependent weights.

A small calculus of "bounded and Lipschitz on `S`" (`LB f S B L`), enough to show: if the
chart weights `u - 1`, `v - 1`, `c` are `1/100`-small and `1/100`-Lipschitz along each
coordinate slice, then `E(M9) - E₀` is `1/10`-small and `47/100`-Lipschitz, and Lemma M3
applies (through `lemmaM3_core`, in expansion form: no derivatives are computed).
-/
import VectorSLT.LemmaM5

namespace VectorSLT

open Set SLT

/-- `f` is bounded by `B` and `L`-Lipschitz on `S`. -/
def LB (f : ℝ → ℝ) (S : Set ℝ) (B L : ℝ) : Prop :=
  (∀ x ∈ S, |f x| ≤ B) ∧ ∀ x ∈ S, ∀ y ∈ S, |f y - f x| ≤ L * |y - x|

namespace LB

variable {f g : ℝ → ℝ} {S : Set ℝ} {B L B' L' : ℝ}

theorem mono (h : LB f S B L) (hB : B ≤ B') (hL : L ≤ L') : LB f S B' L' :=
  ⟨fun x hx => (h.1 x hx).trans hB,
    fun x hx y hy => (h.2 x hx y hy).trans (mul_le_mul_of_nonneg_right hL (abs_nonneg _))⟩

theorem congr (h : LB f S B L) (hfg : ∀ x ∈ S, f x = g x) : LB g S B L :=
  ⟨fun x hx => hfg x hx ▸ h.1 x hx,
    fun x hx y hy => by rw [← hfg x hx, ← hfg y hy]; exact h.2 x hx y hy⟩

theorem const (a : ℝ) : LB (fun _ => a) S |a| 0 :=
  ⟨fun _ _ => le_rfl, fun _ _ _ _ => by simp⟩

theorem const' {a b : ℝ} (hab : |a| ≤ b) : LB (fun _ => a) S b 0 := (const a).mono hab le_rfl

theorem id' (hS : S ⊆ Icc (-1) 1) : LB (fun x => x) S 1 1 :=
  ⟨fun x hx => abs_le.mpr (hS hx), fun x _ y _ => by simp⟩

theorem add (hf : LB f S B L) (hg : LB g S B' L') :
    LB (fun x => f x + g x) S (B + B') (L + L') :=
  ⟨fun x hx => (abs_add_le _ _).trans (add_le_add (hf.1 x hx) (hg.1 x hx)),
    fun x hx y hy => by
      have h1 := hf.2 x hx y hy
      have h2 := hg.2 x hx y hy
      calc |f y + g y - (f x + g x)| = |(f y - f x) + (g y - g x)| := by ring_nf
        _ ≤ |f y - f x| + |g y - g x| := abs_add_le _ _
        _ ≤ _ := by rw [add_mul]; linarith⟩

theorem neg (hf : LB f S B L) : LB (fun x => -f x) S B L :=
  ⟨fun x hx => by rw [abs_neg]; exact hf.1 x hx,
    fun x hx y hy => by rw [show -f y - -f x = -(f y - f x) by ring, abs_neg]; exact hf.2 x hx y hy⟩

theorem sub (hf : LB f S B L) (hg : LB g S B' L') :
    LB (fun x => f x - g x) S (B + B') (L + L') :=
  (hf.add hg.neg).congr fun x _ => by ring

theorem mul (hf : LB f S B L) (hg : LB g S B' L') :
    LB (fun x => f x * g x) S (B * B') (B * L' + B' * L) :=
  ⟨fun x hx => by
      rw [abs_mul]
      exact mul_le_mul (hf.1 x hx) (hg.1 x hx) (abs_nonneg _) ((abs_nonneg _).trans (hf.1 x hx)),
    fun x hx y hy => by
      have hB : 0 ≤ B := (abs_nonneg _).trans (hf.1 x hx)
      have hB' : 0 ≤ B' := (abs_nonneg _).trans (hg.1 x hx)
      have e : f y * g y - f x * g x = f y * (g y - g x) + g x * (f y - f x) := by ring
      rw [e]
      calc |f y * (g y - g x) + g x * (f y - f x)|
          ≤ |f y| * |g y - g x| + |g x| * |f y - f x| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ B * (L' * |y - x|) + B' * (L * |y - x|) := by
            gcongr
            · exact hf.1 y hy
            · exact hg.2 x hx y hy
            · exact hg.1 x hx
            · exact hf.2 x hx y hy
        _ = (B * L' + B' * L) * |y - x| := by ring⟩

theorem div (hf : LB f S B L) (hg : LB g S B' L') {m : ℝ} (hm : 0 < m)
    (hgm : ∀ x ∈ S, m ≤ |g x|) :
    LB (fun x => f x / g x) S (B / m) (L / m + B * L' / m ^ 2) :=
  ⟨fun x hx => by
      rw [abs_div]
      exact div_le_div₀ ((abs_nonneg _).trans (hf.1 x hx)) (hf.1 x hx) hm (hgm x hx),
    fun x hx y hy => by
      have hB : 0 ≤ B := (abs_nonneg _).trans (hf.1 x hx)
      have hgx : g x ≠ 0 := fun h => by have := hgm x hx; rw [h, abs_zero] at this; linarith
      have hgy : g y ≠ 0 := fun h => by have := hgm y hy; rw [h, abs_zero] at this; linarith
      have e : f y / g y - f x / g x = (f y - f x) / g y + f x * (g x - g y) / (g x * g y) := by
        field_simp; ring
      rw [e]
      have h1 : |(f y - f x) / g y| ≤ L * |y - x| / m := by
        rw [abs_div]
        exact div_le_div₀ ((abs_nonneg _).trans (hf.2 x hx y hy)) (hf.2 x hx y hy) hm (hgm y hy)
      have h2 : |f x * (g x - g y) / (g x * g y)| ≤ B * (L' * |y - x|) / m ^ 2 := by
        rw [abs_div, abs_mul, abs_mul, sq]
        have hl := hg.2 y hy x hx
        rw [abs_sub_comm x y] at hl
        have hnum : |f x| * |g x - g y| ≤ B * (L' * |y - x|) :=
          mul_le_mul (hf.1 x hx) hl (abs_nonneg _) hB
        have hden : m * m ≤ |g x| * |g y| :=
          mul_le_mul (hgm x hx) (hgm y hy) hm.le (abs_nonneg _)
        exact div_le_div₀ ((mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans hnum) hnum
          (by positivity) hden
      calc _ ≤ |(f y - f x) / g y| + |f x * (g x - g y) / (g x * g y)| := abs_add_le _ _
        _ ≤ L * |y - x| / m + B * (L' * |y - x|) / m ^ 2 := add_le_add h1 h2
        _ = (L / m + B * L' / m ^ 2) * |y - x| := by ring⟩

theorem cube (hS : S ⊆ Icc (-1) 1) : LB (fun x => x ^ 3) S 1 3 :=
  ((((id' hS).mul (id' hS)).mul (id' hS)).congr fun x _ => by ring).mono (by norm_num)
    (by norm_num)

theorem continuousOn (h : LB f S B L) : ContinuousOn f S := by
  refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal L) fun x hx y hy => ?_).continuousOn
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
  calc |f x - f y| ≤ L * |x - y| := h.2 y hy x hx
    _ ≤ max L 0 * |x - y| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)

theorem sum {ι : Type*} (T : Finset ι) {F : ι → ℝ → ℝ} {Bi Li : ι → ℝ}
    (h : ∀ i ∈ T, LB (F i) S (Bi i) (Li i)) (hS : S.Nonempty) :
    LB (fun x => ∑ i ∈ T, F i x) S (∑ i ∈ T, Bi i) (∑ i ∈ T, Li i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    obtain ⟨x₀, -⟩ := hS
    simpa using (const (S := S) (0 : ℝ))
  | insert i T hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end LB

/-! ### `E(M9) - E₀` is small and `0.47`-Lipschitz -/

theorem EM9_sub_E0 (q x U V c : ℝ) :
    EM9 q x (1 + U) (1 + V) c - (1 + q ^ 3 + x ^ 3) =
      q ^ 3 * (U * (U + 2)) + x ^ 3 * (V * (V + 2)) +
        c * (q ^ 3 * U ^ 2 * (1 + x ^ 3 * (1 + V) ^ 2) -
          2 * q ^ 3 * x ^ 3 * (1 + U) * (1 + V) * U * V + x ^ 3 * V ^ 2 * (1 + q ^ 3 * (1 + U) ^ 2)) := by
  unfold EM9; ring

theorem EM9_symm (q a' u v c : ℝ) : EM9 q a' u v c = EM9 a' q v u c := by unfold EM9; ring

/-- **The perturbation bound (F4).** Along a slice in the second variable, with
`u = 1 + U`, `v = 1 + V`, and `U, V, c` all `1/100`-small and `1/100`-Lipschitz. -/
theorem EM9_pert {S : Set ℝ} (hS : S ⊆ Icc (-1) 1) {q : ℝ} (hq : |q| ≤ 1) {U V c : ℝ → ℝ}
    (hU : LB U S (1 / 100) (1 / 100)) (hV : LB V S (1 / 100) (1 / 100))
    (hc : LB c S (1 / 100) (1 / 100)) :
    LB (fun x => EM9 q x (1 + U x) (1 + V x) (c x) - (1 + q ^ 3 + x ^ 3)) S (1 / 10)
      (47 / 100) := by
  have hq3 : LB (fun _ => q ^ 3) S 1 0 := LB.const' (by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hq)
  have hx3 := LB.cube hS
  have h2 : LB (fun _ => (2 : ℝ)) S 2 0 := LB.const' (by norm_num)
  have h1 : LB (fun _ => (1 : ℝ)) S 1 0 := LB.const' (by norm_num)
  have hU2 := hU.add h2
  have hV2 := hV.add h2
  have h1U := h1.add hU
  have h1V := h1.add hV
  have t1 := hq3.mul (hU.mul hU2)
  have t2 := hx3.mul (hV.mul hV2)
  have b1 := (hq3.mul (hU.mul hU)).mul (h1.add (hx3.mul (h1V.mul h1V)))
  have b2 := ((((h2.mul hq3).mul hx3).mul h1U).mul h1V).mul hU |>.mul hV
  have b3 := (hx3.mul (hV.mul hV)).mul (h1.add (hq3.mul (h1U.mul h1U)))
  have key := (t1.add t2).add (hc.mul ((b1.sub b2).add b3))
  refine (key.congr fun x _ => ?_).mono (by norm_num) (by norm_num)
  rw [EM9_sub_E0]; ring

/-! ### From the perturbation bound to Lemma M3 -/

theorem cube_expand_pos {x y : ℝ} (hx : x ∈ Icc (7 / 10 : ℝ) 1) (hy : y ∈ Icc (7 / 10 : ℝ) 1) :
    147 / 100 * |y - x| ≤ |y ^ 3 - x ^ 3| := by
  rw [show y ^ 3 - x ^ 3 = (y - x) * (y ^ 2 + x * y + x ^ 2) by ring, abs_mul, mul_comm]
  gcongr
  rw [abs_of_pos (by nlinarith [hx.1, hy.1])]
  nlinarith [hx.1, hy.1]

theorem cube_expand_neg {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) (-(7 / 10))) (hy : y ∈ Icc (-1 : ℝ) (-(7 / 10))) :
    147 / 100 * |y - x| ≤ |y ^ 3 - x ^ 3| := by
  rw [show y ^ 3 - x ^ 3 = (y - x) * (y ^ 2 + x * y + x ^ 2) by ring, abs_mul, mul_comm]
  gcongr
  rw [abs_of_pos (by nlinarith [hx.2, hy.2])]
  nlinarith [hx.2, hy.2]

theorem outerExp_of_LB {F : ℝ → ℝ} {K B : ℝ}
    (h : LB (fun x => F x - (K + x ^ 3)) (Icc (-1) 1) B (47 / 100)) : OuterExp F := by
  have key : ∀ x y, x ∈ Icc (-1 : ℝ) 1 → y ∈ Icc (-1 : ℝ) 1 →
      147 / 100 * |y - x| ≤ |y ^ 3 - x ^ 3| → |y - x| ≤ |F y - F x| := by
    intro x y hx hy hc
    have hl := h.2 x hx y hy
    have e : F y - F x = (y ^ 3 - x ^ 3) + ((F y - (K + y ^ 3)) - (F x - (K + x ^ 3))) := by ring
    have := abs_sub (F y - F x) ((F y - (K + y ^ 3)) - (F x - (K + x ^ 3)))
    rw [show F y - F x - (F y - (K + y ^ 3) - (F x - (K + x ^ 3))) = y ^ 3 - x ^ 3 by
      ring] at this
    linarith
  constructor
  · intro x hx y hy
    exact key x y ⟨by linarith [hx.1], hx.2⟩ ⟨by linarith [hy.1], hy.2⟩ (cube_expand_pos hx hy)
  · intro x hx y hy
    exact key x y ⟨hx.1, by linarith [hx.2]⟩ ⟨hy.1, by linarith [hy.2]⟩ (cube_expand_neg hx hy)

/-- **Lemma M3 from slice perturbation bounds.** -/
theorem m3Int_of_LB (E : ℝ × ℝ → ℝ) (hEm : Measurable E)
    (ha : ∀ q, |q| ≤ 1 → LB (fun x => E (q, x) - (1 + q ^ 3 + x ^ 3)) (Icc (-1) 1) (1 / 10)
      (47 / 100))
    (hq : ∀ a, |a| ≤ 1 → LB (fun x => E (x, a) - (1 + a ^ 3 + x ^ 3)) (Icc (-1) 1) (1 / 10)
      (47 / 100)) : M3Int E := by
  have hcont : ∀ {F : ℝ → ℝ} {K B L : ℝ},
      LB (fun x => F x - (K + x ^ 3)) (Icc (-1) 1) B L → ContinuousOn F (Icc (-1) 1) := by
    intro F K B L h
    have hg : ContinuousOn (fun x : ℝ => K + x ^ 3) (Icc (-1) 1) := by fun_prop
    exact (ContinuousOn.add (f := fun x => F x - (K + x ^ 3)) (g := fun x => K + x ^ 3)
      h.continuousOn hg).congr fun x _ => by simp only [Pi.add_apply]; ring
  refine lemmaM3_core E hEm (fun q hq1 => hcont (ha q hq1))
    (fun a ha7 => hcont (hq a (by linarith [ha7]))) (fun q a hq1 ha1 => ?_)
    (fun q hq1 => outerExp_of_LB (ha q hq1)) (fun a ha7 => outerExp_of_LB (hq a (by linarith)))
  exact (ha q hq1).1 a (abs_le.mp ha1)

end VectorSLT
