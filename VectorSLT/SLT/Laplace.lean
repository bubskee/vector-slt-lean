/-
L4: learning-coefficient basics, independent of ResNets (namespace `VectorSLT.SLT`, Mathlib only).

For a measure `ν` (prior × cutoff, as a measure) and a loss `K`,
  `Z(N) = ∫ e^{-N K} dν`, `V(t) = ν{K ≤ t}`.
`HasLaplacePair Z λ m` says `Z(N) ≍ N^{-λ} (log N)^{m-1}` for large `N`.
-/
import Mathlib

namespace VectorSLT.SLT

open MeasureTheory Set Filter Real

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The Laplace integral `Z(N) = ∫ e^{-N K} dν`. -/
noncomputable def Z (ν : Measure α) (K : α → ℝ) (N : ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (-(N * K x))) ∂ν

/-- The sublevel volume `V(t) = ν{K ≤ t}`. -/
def V (ν : Measure α) (K : α → ℝ) (t : ℝ) : ENNReal := ν {x | K x ≤ t}

/-- `Z(N) ≥ c N^{-λ} (log N)^{m-1}` for all large `N`. -/
def LaplaceLower (Zf : ℝ → ENNReal) (lam : ℝ) (m : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N, N₀ ≤ N →
    ENNReal.ofReal (c * N ^ (-lam) * Real.log N ^ (m - 1)) ≤ Zf N

/-- `Z(N) ≤ C N^{-λ} (log N)^{m-1}` for all large `N`. -/
def LaplaceUpper (Zf : ℝ → ENNReal) (lam : ℝ) (m : ℕ) : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℝ, ∀ N, N₀ ≤ N →
    Zf N ≤ ENNReal.ofReal (C * N ^ (-lam) * Real.log N ^ (m - 1))

/-- The learning pair `(λ, m)`: `Z(N) ≍ N^{-λ} (log N)^{m-1}`. -/
def HasLaplacePair (Zf : ℝ → ENNReal) (lam : ℝ) (m : ℕ) : Prop :=
  LaplaceLower Zf lam m ∧ LaplaceUpper Zf lam m

/-! ### Volume ⇒ Laplace, lower direction -/

/-- `Z(N) ≥ e^{-1} V(1/N)` for `N > 0`. -/
theorem Z_ge_V {ν : Measure α} {K : α → ℝ} (hK : Measurable K) {N : ℝ} (hN : 0 < N) :
    ENNReal.ofReal (Real.exp (-1)) * V ν K N⁻¹ ≤ Z ν K N := by
  have hmeas : Measurable fun x => ENNReal.ofReal (Real.exp (-(N * K x))) := by fun_prop
  refine le_trans ?_ (mul_meas_ge_le_lintegral₀ hmeas.aemeasurable
    (ENNReal.ofReal (Real.exp (-1))))
  unfold V
  gcongr with x
  intro hx
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have : N * K x ≤ 1 := by rw [← le_div_iff₀' hN, one_div]; exact hx
  linarith

/-- **Volume ⇒ Laplace (lower).** If `V(t) ≥ c t^λ (log 1/t)^{m-1}` for `0 < t ≤ t₀`, then
`Z(N) ≥ e^{-1} c N^{-λ} (log N)^{m-1}` for `N ≥ 1/t₀`. -/
theorem laplaceLower_of_volume {ν : Measure α} {K : α → ℝ} (hK : Measurable K)
    {lam c t₀ : ℝ} {m : ℕ} (hc : 0 < c) (ht₀ : 0 < t₀)
    (hV : ∀ t, 0 < t → t ≤ t₀ →
      ENNReal.ofReal (c * t ^ lam * Real.log (1 / t) ^ (m - 1)) ≤ V ν K t) :
    LaplaceLower (Z ν K) lam m := by
  refine ⟨Real.exp (-1) * c, by positivity, t₀⁻¹, fun N hNt => ?_⟩
  have hN : 0 < N := lt_of_lt_of_le (inv_pos.mpr ht₀) hNt
  have ht : N⁻¹ ≤ t₀ := by rw [inv_le_comm₀ hN ht₀]; exact hNt
  have h1 := hV N⁻¹ (inv_pos.mpr hN) ht
  rw [one_div, inv_inv, Real.inv_rpow hN.le, ← Real.rpow_neg hN.le] at h1
  refine le_trans ?_ (Z_ge_V hK hN)
  rw [mul_assoc, mul_assoc, ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc c]
  gcongr

/-! ### Comparability of losses and priors -/

theorem Z_mono_loss {ν : Measure α} {K K' : α → ℝ} (h : ∀ x, K x ≤ K' x) {N : ℝ} (hN : 0 ≤ N) :
    Z ν K' N ≤ Z ν K N := by
  apply lintegral_mono; intro x
  apply ENNReal.ofReal_le_ofReal; apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_left (h x) hN; linarith

/-- If `c K ≤ K' ≤ C K` then `Z_K(C N) ≤ Z_{K'}(N) ≤ Z_K(c N)`. -/
theorem Z_comparable {ν : Measure α} {K K' : α → ℝ} {c C : ℝ}
    (hlo : ∀ x, c * K x ≤ K' x) (hhi : ∀ x, K' x ≤ C * K x) {N : ℝ} (hN : 0 ≤ N) :
    Z ν K (C * N) ≤ Z ν K' N ∧ Z ν K' N ≤ Z ν K (c * N) := by
  have e : ∀ (a : ℝ) x, a * N * K x = N * (a * K x) := fun a x => by ring
  constructor
  · have := Z_mono_loss (ν := ν) (K := K') (K' := fun x => C * K x) hhi hN
    simp only [Z] at this ⊢; simpa [e] using this
  · have := Z_mono_loss (ν := ν) (K := fun x => c * K x) (K' := K') hlo hN
    simp only [Z] at this ⊢; simpa [e] using this

/-- For `C > 0`: eventually `(log N)/2 ≤ log(C N) ≤ 2 log N`. -/
theorem log_mul_bounds {C : ℝ} (hC : 0 < C) :
    ∃ N₀, ∀ N, N₀ ≤ N → 0 ≤ Real.log (C * N) ∧ Real.log N / 2 ≤ Real.log (C * N) ∧
      Real.log (C * N) ≤ 2 * Real.log N := by
  refine ⟨max (max (C⁻¹ ^ 2) C) (max C⁻¹ 1), fun N hN => ?_⟩
  have h1 : C⁻¹ ^ 2 ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have h2 : C ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have h3 : C⁻¹ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have h4 : 1 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hN0 : 0 < N := by linarith
  rw [Real.log_mul hC.ne' hN0.ne']
  have hlN : 0 ≤ Real.log N := Real.log_nonneg h4
  have a1 : -Real.log C ≤ Real.log N := by
    rw [← Real.log_inv]; exact Real.log_le_log (by positivity) h3
  have a2 : Real.log C ≤ Real.log N := Real.log_le_log hC h2
  have a3 : -2 * Real.log C ≤ Real.log N := by
    have := Real.log_le_log (by positivity) h1
    rw [Real.log_pow, Real.log_inv] at this; push_cast at this; linarith
  refine ⟨by linarith, by linarith, by linarith⟩

theorem rpow_neg_mul {C N lam : ℝ} (hC : 0 < C) (hN : 0 < N) :
    (C * N) ^ (-lam) = C ^ (-lam) * N ^ (-lam) := Real.mul_rpow hC.le hN.le

theorem Z_ge_of_le_mul {ν : Measure α} {K K' : α → ℝ} {C : ℝ} (hhi : ∀ x, K' x ≤ C * K x)
    {N : ℝ} (hN : 0 ≤ N) : Z ν K (C * N) ≤ Z ν K' N := by
  have := Z_mono_loss (ν := ν) (K := K') (K' := fun x => C * K x) hhi hN
  have e : ∀ x, C * N * K x = N * (C * K x) := fun x => by ring
  simp only [Z] at this ⊢; simpa [e] using this

theorem Z_le_of_mul_le {ν : Measure α} {K K' : α → ℝ} {c : ℝ} (hlo : ∀ x, c * K x ≤ K' x)
    {N : ℝ} (hN : 0 ≤ N) : Z ν K' N ≤ Z ν K (c * N) := by
  have := Z_mono_loss (ν := ν) (K := fun x => c * K x) (K' := K') hlo hN
  have e : ∀ x, c * N * K x = N * (c * K x) := fun x => by ring
  simp only [Z] at this ⊢; simpa [e] using this

/-- **Loss comparability preserves the lower half of a pair**: `K' ≤ C K` and a lower bound
for `Z_K` give one for `Z_{K'}`, with constant `c C^{-λ} 2^{-(m-1)}`. -/
theorem LaplaceLower.of_le_mul {ν : Measure α} {K K' : α → ℝ} {C lam : ℝ} {m : ℕ}
    (hC : 0 < C) (hhi : ∀ x, K' x ≤ C * K x) (h : LaplaceLower (Z ν K) lam m) :
    LaplaceLower (Z ν K') lam m := by
  obtain ⟨c, hc, N₀, hN₀⟩ := h
  obtain ⟨N₁, hN₁⟩ := log_mul_bounds hC
  refine ⟨c * C ^ (-lam) * (1 / 2) ^ (m - 1), by positivity,
    max (max (N₀ / C) N₁) 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hA : N₀ ≤ C * N := by
    have := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
    rw [div_le_iff₀ hC] at this; linarith
  obtain ⟨l0, l1, -⟩ := hN₁ N ((le_max_right _ _).trans ((le_max_left _ _).trans hN))
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN1
  refine le_trans ?_ ((hN₀ (C * N) hA).trans (Z_ge_of_le_mul hhi hN0.le))
  apply ENNReal.ofReal_le_ofReal
  rw [rpow_neg_mul hC hN0]
  have hp : (1 / 2 : ℝ) ^ (m - 1) * Real.log N ^ (m - 1) ≤ Real.log (C * N) ^ (m - 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hpos : 0 ≤ c * C ^ (-lam) * N ^ (-lam) := by positivity
  calc c * C ^ (-lam) * (1 / 2) ^ (m - 1) * N ^ (-lam) * Real.log N ^ (m - 1)
      = (c * C ^ (-lam) * N ^ (-lam)) * ((1 / 2) ^ (m - 1) * Real.log N ^ (m - 1)) := by ring
    _ ≤ (c * C ^ (-lam) * N ^ (-lam)) * Real.log (C * N) ^ (m - 1) :=
        mul_le_mul_of_nonneg_left hp hpos
    _ = c * (C ^ (-lam) * N ^ (-lam)) * Real.log (C * N) ^ (m - 1) := by ring

/-- **Loss comparability preserves the upper half of a pair**: `c K ≤ K'` with `c > 0`. -/
theorem LaplaceUpper.of_mul_le {ν : Measure α} {K K' : α → ℝ} {c lam : ℝ} {m : ℕ}
    (hc : 0 < c) (hlo : ∀ x, c * K x ≤ K' x) (h : LaplaceUpper (Z ν K) lam m) :
    LaplaceUpper (Z ν K') lam m := by
  obtain ⟨C₀, N₀, hN₀⟩ := h
  obtain ⟨N₁, hN₁⟩ := log_mul_bounds hc
  refine ⟨max C₀ 0 * c ^ (-lam) * 2 ^ (m - 1), max (max (N₀ / c) N₁) 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hA : N₀ ≤ c * N := by
    have := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
    rw [div_le_iff₀ hc] at this; linarith
  obtain ⟨l0, -, l2⟩ := hN₁ N ((le_max_right _ _).trans ((le_max_left _ _).trans hN))
  refine (Z_le_of_mul_le hlo hN0.le).trans ((hN₀ (c * N) hA).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  rw [rpow_neg_mul hc hN0]
  have hp : Real.log (c * N) ^ (m - 1) ≤ 2 ^ (m - 1) * Real.log N ^ (m - 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ l0 l2 _
  have hpos : 0 ≤ max C₀ 0 * (c ^ (-lam) * N ^ (-lam)) := by positivity
  calc C₀ * (c ^ (-lam) * N ^ (-lam)) * Real.log (c * N) ^ (m - 1)
      ≤ max C₀ 0 * (c ^ (-lam) * N ^ (-lam)) * Real.log (c * N) ^ (m - 1) := by
        gcongr; exact le_max_left _ _
    _ ≤ max C₀ 0 * (c ^ (-lam) * N ^ (-lam)) * (2 ^ (m - 1) * Real.log N ^ (m - 1)) :=
        mul_le_mul_of_nonneg_left hp hpos
    _ = _ := by ring

/-- **Comparable losses have the same pair.** -/
theorem HasLaplacePair.of_comparable {ν : Measure α} {K K' : α → ℝ} {c C lam : ℝ} {m : ℕ}
    (hc : 0 < c) (hC : 0 < C) (hlo : ∀ x, c * K x ≤ K' x) (hhi : ∀ x, K' x ≤ C * K x)
    (h : HasLaplacePair (Z ν K) lam m) : HasLaplacePair (Z ν K') lam m :=
  ⟨h.1.of_le_mul hC hhi, h.2.of_mul_le hc hlo⟩

/-- **Comparable priors**: `c ν ≤ ν' ≤ C ν` as measures. -/
theorem Z_prior_comparable {ν ν' : Measure α} {K : α → ℝ} {c C : ENNReal}
    (hlo : c • ν ≤ ν') (hhi : ν' ≤ C • ν) (N : ℝ) :
    c * Z ν K N ≤ Z ν' K N ∧ Z ν' K N ≤ C * Z ν K N := by
  constructor
  · rw [Z, Z, ← smul_eq_mul, ← lintegral_smul_measure]; exact lintegral_mono' hlo le_rfl
  · rw [Z, Z, ← smul_eq_mul, ← lintegral_smul_measure]; exact lintegral_mono' hhi le_rfl

theorem HasLaplacePair.of_prior {ν ν' : Measure α} {K : α → ℝ} {c C : ℝ} {lam : ℝ} {m : ℕ}
    (hc : 0 < c) (hlo : ENNReal.ofReal c • ν ≤ ν') (hhi : ν' ≤ ENNReal.ofReal C • ν)
    (h : HasLaplacePair (Z ν K) lam m) : HasLaplacePair (Z ν' K) lam m := by
  obtain ⟨⟨c₀, hc₀, N₀, h₀⟩, ⟨C₁, N₁, h₁⟩⟩ := h
  refine ⟨⟨c * c₀, by positivity, N₀, fun N hN => ?_⟩, ⟨max C 0 * C₁, N₁, fun N hN => ?_⟩⟩
  · refine le_trans ?_ (Z_prior_comparable (K := K) hlo hhi N).1
    rw [mul_assoc, mul_assoc, ENNReal.ofReal_mul hc.le, ← mul_assoc c₀]
    gcongr; exact h₀ N hN
  · refine (Z_prior_comparable (K := K) hlo hhi N).2.trans ?_
    calc ENNReal.ofReal C * Z ν K N ≤ ENNReal.ofReal (max C 0) *
          ENNReal.ofReal (C₁ * N ^ (-lam) * Real.log N ^ (m - 1)) := by
          gcongr
          · exact le_max_left _ _
          · exact h₁ N hN
      _ = ENNReal.ofReal (max C 0 * (C₁ * N ^ (-lam) * Real.log N ^ (m - 1))) :=
          (ENNReal.ofReal_mul (le_max_right _ _)).symm
      _ = _ := by ring_nf

/-! ### Products: losses in disjoint variable blocks -/

/-- `Z_{K₁ ⊕ K₂} = Z_{K₁} · Z_{K₂}` on a product measure (Tonelli). -/
theorem Z_prod {ν₁ : Measure α} {ν₂ : Measure β} [SFinite ν₂] {K₁ : α → ℝ} {K₂ : β → ℝ}
    (h₁ : Measurable K₁) (h₂ : Measurable K₂) (N : ℝ) :
    Z (ν₁.prod ν₂) (fun p => K₁ p.1 + K₂ p.2) N = Z ν₁ K₁ N * Z ν₂ K₂ N := by
  unfold Z
  rw [← lintegral_prod_mul (by fun_prop) (by fun_prop)]
  congr 1; funext p
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; congr 2; ring

/-- **Pairs add over disjoint blocks**: `(λ₁, m₁)` and `(λ₂, m₂)` give `(λ₁+λ₂, m₁+m₂-1)`. -/
theorem HasLaplacePair.prod {ν₁ : Measure α} {ν₂ : Measure β} [SFinite ν₂]
    {K₁ : α → ℝ} {K₂ : β → ℝ} (h₁ : Measurable K₁) (h₂ : Measurable K₂)
    {l₁ l₂ : ℝ} {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (H₁ : HasLaplacePair (Z ν₁ K₁) l₁ m₁) (H₂ : HasLaplacePair (Z ν₂ K₂) l₂ m₂) :
    HasLaplacePair (Z (ν₁.prod ν₂) (fun p => K₁ p.1 + K₂ p.2)) (l₁ + l₂) (m₁ + m₂ - 1) := by
  obtain ⟨⟨a₁, ha₁, A₁, hA₁⟩, ⟨b₁, B₁, hB₁⟩⟩ := H₁
  obtain ⟨⟨a₂, ha₂, A₂, hA₂⟩, ⟨b₂, B₂, hB₂⟩⟩ := H₂
  have key : ∀ N : ℝ, 1 ≤ N → ∀ x y : ℝ, (x * N ^ (-l₁) * Real.log N ^ (m₁ - 1)) *
      (y * N ^ (-l₂) * Real.log N ^ (m₂ - 1)) =
      x * y * N ^ (-(l₁ + l₂)) * Real.log N ^ (m₁ + m₂ - 1 - 1) := by
    intro N hN x y
    have hN0 : 0 < N := by linarith
    rw [neg_add, Real.rpow_add hN0, show m₁ + m₂ - 1 - 1 = (m₁ - 1) + (m₂ - 1) by omega,
      pow_add]; ring
  refine ⟨⟨a₁ * a₂, by positivity, max (max A₁ A₂) 1, fun N hN => ?_⟩,
    ⟨max b₁ 0 * max b₂ 0, max (max B₁ B₂) 1, fun N hN => ?_⟩⟩
  · have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
    have hl : 0 ≤ Real.log N := Real.log_nonneg hN1
    have hN0 : 0 < N := by linarith
    rw [Z_prod h₁ h₂, ← key N hN1, ENNReal.ofReal_mul
      (mul_nonneg (mul_nonneg ha₁.le (by positivity)) (pow_nonneg hl _))]
    exact mul_le_mul' (hA₁ N ((le_max_left _ _).trans ((le_max_left _ _).trans hN)))
      (hA₂ N ((le_max_right _ _).trans ((le_max_left _ _).trans hN)))
  · have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
    have hN0 : 0 < N := by linarith
    have hl : 0 ≤ Real.log N := Real.log_nonneg hN1
    rw [Z_prod h₁ h₂, ← key N hN1, ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul' ((hB₁ N ((le_max_left _ _).trans ((le_max_left _ _).trans hN))).trans ?_)
      ((hB₂ N ((le_max_right _ _).trans ((le_max_left _ _).trans hN))).trans ?_) <;>
    · apply ENNReal.ofReal_le_ofReal; gcongr; exact le_max_left _ _

/-! ### The layer-cake identity -/

/-- `∫_{(0,∞)} 1{a ≤ s} e^{-s} ds = e^{-a}` for `a ≥ 0`. -/
theorem lintegral_Ioi_indicator_exp {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ s in Ioi 0, (Ici a).indicator (fun s => ENNReal.ofReal (Real.exp (-s))) s =
      ENNReal.ofReal (Real.exp (-a)) := by
  rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hset : (Ici a ∩ Ioi 0 : Set ℝ) =ᵐ[volume] Ioi a := by
    rcases eq_or_lt_of_le ha with h | h
    · subst h
      have e : (Ici 0 ∩ Ioi 0 : Set ℝ) = Ioi 0 := inter_eq_right.mpr Ioi_subset_Ici_self
      rw [e]
    · have e : (Ici a ∩ Ioi 0 : Set ℝ) = Ici a :=
        inter_eq_left.mpr (fun x (hx : a ≤ x) => show (0:ℝ) < x from lt_of_lt_of_le h hx)
      rw [e]; exact Ioi_ae_eq_Ici.symm
  rw [setLIntegral_congr hset, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_exp_neg_Ioi]
  · exact (exp_neg_integrableOn_Ioi a one_pos).congr_fun (fun x _ => by simp) measurableSet_Ioi
  · exact Eventually.of_forall fun x => (Real.exp_pos _).le

/-- **Layer cake**: for a nonnegative measurable loss and `N > 0`,
`Z(N) = ∫_0^∞ e^{-s} V(s/N) ds`, i.e. `∫_0^∞ N e^{-Nt} V(t) dt` after `s = Nt`. -/
theorem Z_eq_layercake {ν : Measure α} [SFinite ν] {K : α → ℝ} (hK : Measurable K)
    (hK0 : ∀ x, 0 ≤ K x) {N : ℝ} (hN : 0 < N) :
    Z ν K N = ∫⁻ s in Ioi 0, ENNReal.ofReal (Real.exp (-s)) * V ν K (s / N) := by
  set F : α → ℝ → ENNReal := fun x s =>
    {p : α × ℝ | N * K p.1 ≤ p.2}.indicator (fun p => ENNReal.ofReal (Real.exp (-p.2))) (x, s)
  have hF : Measurable (Function.uncurry F) := by
    refine Measurable.indicator (by fun_prop) ?_
    exact measurableSet_le (by fun_prop) measurable_snd
  have h1 : ∀ x, ENNReal.ofReal (Real.exp (-(N * K x))) = ∫⁻ s in Ioi 0, F x s := by
    intro x
    rw [← lintegral_Ioi_indicator_exp (mul_nonneg hN.le (hK0 x))]
    rfl
  unfold Z
  simp_rw [h1]
  rw [lintegral_lintegral_swap hF.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
  have : (fun x => F x s) = {x | K x ≤ s / N}.indicator
      (fun _ => ENNReal.ofReal (Real.exp (-s))) := by
    funext x
    simp only [F, Set.indicator, mem_ofPred_eq]
    congr 1
    rw [le_div_iff₀ hN, mul_comm]
  rw [this, lintegral_indicator_const (measurableSet_le hK measurable_const)]
  rfl

/-! ### Volume ⇒ Laplace, upper direction -/

/-- The constant `I(λ,k) = ∫_0^∞ e^{-s} s^λ (1 + |log s|)^k ds`. -/
noncomputable def gammaLog (lam : ℝ) (k : ℕ) : ENNReal :=
  ∫⁻ s in Ioi 0, ENNReal.ofReal (Real.exp (-s) * s ^ lam * (1 + |Real.log s|) ^ k)

theorem one_add_abs_log_le {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    1 + |Real.log s| ≤ (1 + 1 / δ) * (s ^ δ + s ^ (-δ)) := by
  have h1 : 0 < s ^ δ := Real.rpow_pos_of_pos hs δ
  have h2 : 0 < s ^ (-δ) := Real.rpow_pos_of_pos hs (-δ)
  rcases le_total 1 s with hs1 | hs1
  · have hl : 0 ≤ Real.log s := Real.log_nonneg hs1
    have hlog := Real.log_le_rpow_div hs.le hδ
    have : 1 ≤ s ^ δ := Real.one_le_rpow hs1 hδ.le
    rw [abs_of_nonneg hl]
    have e : (1 + 1 / δ) * (s ^ δ + s ^ (-δ)) = s ^ δ + s ^ δ / δ + (1 + 1 / δ) * s ^ (-δ) := by
      ring
    rw [e]
    have : 0 ≤ (1 + 1 / δ) * s ^ (-δ) := by positivity
    linarith
  · have hl : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1
    have hlog := Real.log_le_rpow_div (inv_pos.mpr hs).le hδ
    rw [Real.log_inv, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le] at hlog
    have : 1 ≤ s ^ (-δ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs1 (by linarith)
    rw [abs_of_nonpos hl]
    have e : (1 + 1 / δ) * (s ^ δ + s ^ (-δ)) = s ^ (-δ) + s ^ (-δ) / δ + (1 + 1 / δ) * s ^ δ := by
      ring
    rw [e]
    have : 0 ≤ (1 + 1 / δ) * s ^ δ := by positivity
    linarith

theorem add_pow_le_two_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    (a + b) ^ k ≤ 2 ^ k * (a ^ k + b ^ k) := by
  have hm : a + b ≤ 2 * max a b := by
    have := le_max_left a b; have := le_max_right a b; linarith
  calc (a + b) ^ k ≤ (2 * max a b) ^ k := pow_le_pow_left₀ (by positivity) hm k
    _ = 2 ^ k * max a b ^ k := mul_pow _ _ _
    _ ≤ 2 ^ k * (a ^ k + b ^ k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rcases le_total a b with h | h
        · rw [max_eq_right h]; have := pow_nonneg ha k; linarith
        · rw [max_eq_left h]; have := pow_nonneg hb k; linarith

theorem gammaLog_lt_top {lam : ℝ} (hlam : 0 < lam) (k : ℕ) : gammaLog lam k < ⊤ := by
  set δ := lam / (2 * (k + 1))
  have hδ : 0 < δ := by positivity
  have hkδ : (k : ℝ) * δ ≤ lam / 2 := by
    simp only [δ]; rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set B := (1 + 1 / δ) ^ k * 2 ^ k
  have hB : 0 ≤ B := by positivity
  set g : ℝ → ℝ := fun s => B * (Real.exp (-s) * s ^ (lam + k * δ + 1 - 1) +
    Real.exp (-s) * s ^ (lam - k * δ + 1 - 1))
  have hg : IntegrableOn g (Ioi 0) :=
    ((Real.GammaIntegral_convergent (by positivity)).add
      (Real.GammaIntegral_convergent (by linarith))).const_mul B
  have hpt : ∀ s ∈ Ioi (0 : ℝ), Real.exp (-s) * s ^ lam * (1 + |Real.log s|) ^ k ≤ g s := by
    intro s hs
    have hs : 0 < s := hs
    have h1 := one_add_abs_log_le hs hδ
    have h2 : (1 + |Real.log s|) ^ k ≤ (1 + 1 / δ) ^ k * (s ^ δ + s ^ (-δ)) ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 k
    have h3 := add_pow_le_two_pow (Real.rpow_pos_of_pos hs δ).le
      (Real.rpow_pos_of_pos hs (-δ)).le k
    have e1 : (s ^ δ) ^ k = s ^ ((k : ℝ) * δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le, mul_comm]
    have e2 : (s ^ (-δ)) ^ k = s ^ (-((k : ℝ) * δ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]; ring_nf
    rw [e1, e2] at h3
    have e3 : s ^ lam * s ^ ((k : ℝ) * δ) = s ^ (lam + k * δ + 1 - 1) := by
      rw [← Real.rpow_add hs]; ring_nf
    have e4 : s ^ lam * s ^ (-((k : ℝ) * δ)) = s ^ (lam - k * δ + 1 - 1) := by
      rw [← Real.rpow_add hs]; ring_nf
    have hE : 0 ≤ Real.exp (-s) * s ^ lam := by positivity
    calc Real.exp (-s) * s ^ lam * (1 + |Real.log s|) ^ k
        ≤ Real.exp (-s) * s ^ lam * ((1 + 1 / δ) ^ k * (2 ^ k * (s ^ ((k : ℝ) * δ) +
            s ^ (-((k : ℝ) * δ))))) :=
          mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))) hE
      _ = g s := by
          simp only [g, B]; rw [← e3, ← e4]; ring
  calc gammaLog lam k ≤ ∫⁻ s in Ioi 0, ENNReal.ofReal (g s) := by
        apply setLIntegral_mono (by fun_prop)
        intro s hs; exact ENNReal.ofReal_le_ofReal (hpt s hs)
    _ < ⊤ := hg.lintegral_lt_top

/-- **Volume ⇒ Laplace (upper), explicit form.** If `V(t) ≤ C t^λ (1+|log t|)^k` for all
`t > 0`, then `Z(N) ≤ C N^{-λ} (1 + log N)^k · I(λ,k)` for `N ≥ 1`. -/
theorem Z_le_of_volume {ν : Measure α} [SFinite ν] {K : α → ℝ} (hK : Measurable K)
    (hK0 : ∀ x, 0 ≤ K x) {C lam : ℝ} {k : ℕ} (hC : 0 ≤ C)
    (hV : ∀ t, 0 < t → V ν K t ≤ ENNReal.ofReal (C * t ^ lam * (1 + |Real.log t|) ^ k))
    {N : ℝ} (hN : 1 ≤ N) :
    Z ν K N ≤ ENNReal.ofReal (C * N ^ (-lam) * (1 + Real.log N) ^ k) * gammaLog lam k := by
  have hN0 : 0 < N := by linarith
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN
  rw [Z_eq_layercake hK hK0 hN0, gammaLog, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Ioi
  intro s hs
  have hs : 0 < s := hs
  calc ENNReal.ofReal (Real.exp (-s)) * V ν K (s / N)
      ≤ ENNReal.ofReal (Real.exp (-s)) *
          ENNReal.ofReal (C * (s / N) ^ lam * (1 + |Real.log (s / N)|) ^ k) := by
        gcongr; exact hV (s / N) (div_pos hs hN0)
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hp : (s / N) ^ lam = s ^ lam * N ^ (-lam) := by
        rw [Real.div_rpow hs.le hN0.le, Real.rpow_neg hN0.le, div_eq_mul_inv]
      have hlog : 1 + |Real.log (s / N)| ≤ (1 + |Real.log s|) * (1 + Real.log N) := by
        rw [Real.log_div hs.ne' hN0.ne']
        have := abs_sub (Real.log s) (Real.log N)
        rw [abs_of_nonneg hlN] at this
        nlinarith [abs_nonneg (Real.log s)]
      have hlogk : (1 + |Real.log (s / N)|) ^ k ≤
          (1 + |Real.log s|) ^ k * (1 + Real.log N) ^ k := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hlog k
      rw [hp]
      have hA : 0 ≤ Real.exp (-s) * (C * (s ^ lam * N ^ (-lam))) := by positivity
      calc Real.exp (-s) * (C * (s ^ lam * N ^ (-lam)) * (1 + |Real.log (s / N)|) ^ k)
          = Real.exp (-s) * (C * (s ^ lam * N ^ (-lam))) * (1 + |Real.log (s / N)|) ^ k := by
            ring
        _ ≤ Real.exp (-s) * (C * (s ^ lam * N ^ (-lam))) *
            ((1 + |Real.log s|) ^ k * (1 + Real.log N) ^ k) := mul_le_mul_of_nonneg_left hlogk hA
        _ = C * N ^ (-lam) * (1 + Real.log N) ^ k *
            (Real.exp (-s) * s ^ lam * (1 + |Real.log s|) ^ k) := by ring

/-- **Volume ⇒ Laplace (upper).** A global sublevel bound `V(t) ≤ C t^λ (1+|log t|)^{m-1}`
with `λ > 0` gives `Z(N) ≤ C' N^{-λ} (log N)^{m-1}` for large `N`. -/
theorem laplaceUpper_of_volume {ν : Measure α} [SFinite ν] {K : α → ℝ} (hK : Measurable K)
    (hK0 : ∀ x, 0 ≤ K x) {C lam : ℝ} {m : ℕ} (hC : 0 ≤ C) (hlam : 0 < lam)
    (hV : ∀ t, 0 < t → V ν K t ≤ ENNReal.ofReal (C * t ^ lam * (1 + |Real.log t|) ^ (m - 1))) :
    LaplaceUpper (Z ν K) lam m := by
  set I := gammaLog lam (m - 1)
  have hI := gammaLog_lt_top hlam (m - 1)
  refine ⟨C * 2 ^ (m - 1) * I.toReal, Real.exp 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hN
  have hN0 : 0 < N := by linarith
  have hlN : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hN
  refine (Z_le_of_volume hK hK0 hC hV hN1).trans ?_
  rw [← ENNReal.ofReal_toReal hI.ne, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h2 : (1 + Real.log N) ^ (m - 1) ≤ 2 ^ (m - 1) * Real.log N ^ (m - 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hA : 0 ≤ C * N ^ (-lam) := by positivity
  have hI0 : 0 ≤ I.toReal := ENNReal.toReal_nonneg
  calc C * N ^ (-lam) * (1 + Real.log N) ^ (m - 1) * I.toReal
      ≤ C * N ^ (-lam) * (2 ^ (m - 1) * Real.log N ^ (m - 1)) * I.toReal := by gcongr
    _ = _ := by ring

end VectorSLT.SLT
