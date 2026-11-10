/-
The leading term of the network error at every position, for every target (item 1 of the
leading-map brief; paper 2, the first display in the proof of Proposition N1, Appendix E.1).

Scale the parameters with `ε`: the active block (Lean position `p`) is `A + ε³ Δ`, and the three
inactive blocks are `ε V₀, ε V₁, ε V₂` in application order (`thetaEps`). Every layer is then the
identity plus a term of order `ε³`, so the network is `F_A` plus `ε³` times a first-order
perturbation term `lead A p Δ V`, plus `O(ε⁶)` (`net_thetaEps_expansion`):

  `lead A p Δ V x = 3 (A x)^{⊙2} ⊙ (Δ x) + DF_A(x) · S_pre(x) + S_suf(F_A x)`,

with `DF_A(x) u = u + 3 (A x)^{⊙2} ⊙ (A u)` and `S_pre`, `S_suf` the sums of `(V_l ·)^{⊙3}` over the
inactive blocks before and after the active one.

The proof never expands the network: `Exp3 f a b` says `f ε = a + ε³ b + O(ε⁶)` coordinatewise, and
it is preserved by an inactive layer (`Exp3.inactive`) and by the active layer (`Exp3.active`).
-/
import VectorSLT.MainTheorem

namespace VectorSLT.LeadingMap

open Asymptotics Filter Topology Matrix Finset

/-! ### The scaled parameter -/

/-- The four blocks of the scaled parameter, in application order: `A + ε³ Δ` at position `p`,
and `ε V_l` at the `l`-th inactive position `p.succAbove l` (so the inactive blocks keep their
order). -/
def scaledBlocks (A Δ : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (ε : ℝ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ :=
  Fin.insertNth (α := fun _ => Matrix (Fin 2) (Fin 2) ℝ) p (A + ε ^ 3 • Δ) fun l => ε • V l

/-- The scaled parameter `θ_ε ∈ Raw16`: active block `A + ε³ Δ` at Lean position `p`, inactive
blocks `ε V_l`. -/
def thetaEps (A Δ : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (ε : ℝ) : Raw16 :=
  ofRawW (scaledBlocks A Δ p V ε)

/-- Fidelity check: the paper's four matrices of `θ_ε` are the scaled blocks. -/
theorem rawW_thetaEps (A Δ : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (ε : ℝ) :
    rawW (thetaEps A Δ p V ε) = scaledBlocks A Δ p V ε :=
  rawEquiv.right_inv _

/-- Fidelity check: at `ε = 0`, `θ_ε` is the base point `basePos A p` of position `p`. -/
theorem thetaEps_zero (A Δ : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) : thetaEps A Δ p V 0 = basePos A p := by
  apply rawEquiv.injective
  change rawW _ = rawW _
  rw [rawW_thetaEps, rawW_basePos]
  funext q
  rw [scaledBlocks]
  rcases Fin.eq_self_or_eq_succAbove p q with h | ⟨l, rfl⟩
  · subst h; simp
  · simp [Fin.succAbove_ne]

/-! ### The leading term -/

/-- The inactive blocks before the active one (prefix): `l` with `p.succAbove l < p`. -/
def pre (p : Fin 4) : Finset (Fin 3) := univ.filter fun l => l.val < p.val

/-- The inactive blocks after the active one (suffix). -/
def suf (p : Fin 4) : Finset (Fin 3) := univ.filter fun l => p.val ≤ l.val

/-- `S_pre(z) = ∑_{prefix} (V_l z)^{⊙3}`. -/
def Spre (p : Fin 4) (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (z : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ∑ l ∈ pre p, (V l *ᵥ z) ^ 3

/-- `S_suf(z) = ∑_{suffix} (V_l z)^{⊙3}`. -/
def Ssuf (p : Fin 4) (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (z : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ∑ l ∈ suf p, (V l *ᵥ z) ^ 3

/-- The derivative of `F_A` at `x`: `DF_A(x) u = u + 3 (A x)^{⊙2} ⊙ (A u)`. -/
def dLayer (A : Matrix (Fin 2) (Fin 2) ℝ) (x u : Fin 2 → ℝ) : Fin 2 → ℝ :=
  u + 3 * (A *ᵥ x) ^ 2 * (A *ᵥ u)

/-- **The leading term** (coefficient of `ε³`):
`lead A p Δ V x = 3 (A x)^{⊙2} ⊙ (Δ x) + DF_A(x) S_pre(x) + S_suf(F_A x)`. -/
def lead (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4) (Δ : Matrix (Fin 2) (Fin 2) ℝ)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  3 * (A *ᵥ x) ^ 2 * (Δ *ᵥ x) + dLayer A x (Spre p V x) + Ssuf p V (layer A x)

/-! ### First-order expansions in `ε³` -/

/-- `f ε = a + ε³ b + O(ε⁶)` as `ε → 0`, in each coordinate. -/
def Exp3 (f : ℝ → Fin 2 → ℝ) (a b : Fin 2 → ℝ) : Prop :=
  ∀ k, (fun ε => f ε k - a k - ε ^ 3 * b k) =O[𝓝 0] fun ε : ℝ => ε ^ 6

theorem isBigO_pow_one (n : ℕ) (hn : 0 < n) : (fun ε : ℝ => ε ^ n) =O[𝓝 0] fun _ => (1 : ℝ) := by
  have : Tendsto (fun ε : ℝ => ε ^ n) (𝓝 0) (𝓝 0) := by
    simpa [zero_pow hn.ne'] using (continuous_pow n).tendsto (0 : ℝ)
  exact this.isBigO_one ℝ

theorem isBigO_six_three : (fun ε : ℝ => ε ^ 6) =O[𝓝 0] fun ε : ℝ => ε ^ 3 := by
  have h := (isBigO_pow_one 3 (by norm_num)).mul (isBigO_refl (fun ε : ℝ => ε ^ 3) (𝓝 0))
  refine h.congr (fun ε => by ring) (fun ε => by ring)

theorem isBigO_one_mul {f g : ℝ → ℝ} (hf : f =O[𝓝 0] fun _ => (1 : ℝ))
    (hg : g =O[𝓝 0] fun _ => (1 : ℝ)) : (fun ε => f ε * g ε) =O[𝓝 0] fun _ => (1 : ℝ) :=
  (hf.mul hg).congr_right fun _ => mul_one 1

theorem isBigO_cube_const (β : ℝ) : (fun ε : ℝ => ε ^ 3 * β) =O[𝓝 0] fun ε : ℝ => ε ^ 3 :=
  ((isBigO_refl (fun ε : ℝ => ε ^ 3) (𝓝 0)).mul (isBigO_const_const β one_ne_zero _)).congr_right
    fun _ => mul_one _

theorem mulVec_apply_two (B : Matrix (Fin 2) (Fin 2) ℝ) (z : Fin 2 → ℝ) (k : Fin 2) :
    (B *ᵥ z) k = B k ⬝ᵥ z := rfl

theorem smul_row (c : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) : (c • B) k = c • B k := rfl

theorem add_row (A B : Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) : (A + B) k = A k + B k := rfl

theorem isBigO_cube_mul {g : ℝ → ℝ} (h : g =O[𝓝 0] fun ε : ℝ => ε ^ 3) :
    (fun ε => ε ^ 3 * g ε) =O[𝓝 0] fun ε : ℝ => ε ^ 6 :=
  ((isBigO_refl (fun ε : ℝ => ε ^ 3) (𝓝 0)).mul h).congr_right fun ε => by ring

theorem isBigO_one_of_three {g : ℝ → ℝ} (h : g =O[𝓝 0] fun ε : ℝ => ε ^ 3) :
    g =O[𝓝 0] fun _ => (1 : ℝ) :=
  h.trans (isBigO_pow_one 3 (by norm_num))

theorem Exp3.const (x : Fin 2 → ℝ) : Exp3 (fun _ => x) x 0 := by
  intro k
  simp only [sub_self, Pi.zero_apply, mul_zero]
  exact isBigO_zero _ _

theorem Exp3.congr {f f' : ℝ → Fin 2 → ℝ} {a a' b b' : Fin 2 → ℝ} (h : Exp3 f a b)
    (hf : ∀ ε, f ε = f' ε) (ha : a = a') (hb : b = b') : Exp3 f' a' b' := by
  subst ha hb
  have : f = f' := funext hf
  subst this
  exact h

/-- The displacement is `O(ε³)`. -/
theorem Exp3.small {f : ℝ → Fin 2 → ℝ} {a b : Fin 2 → ℝ} (h : Exp3 f a b) (k : Fin 2) :
    (fun ε => f ε k - a k) =O[𝓝 0] fun ε : ℝ => ε ^ 3 := by
  exact ((h k).trans isBigO_six_three).add (isBigO_cube_const (b k)) |>.congr_left
    fun ε => by ring

/-- A linear form of an expansion. -/
theorem Exp3.dot {f : ℝ → Fin 2 → ℝ} {a b : Fin 2 → ℝ} (h : Exp3 f a b) (c : Fin 2 → ℝ) :
    (fun ε => c ⬝ᵥ f ε - c ⬝ᵥ a - ε ^ 3 * (c ⬝ᵥ b)) =O[𝓝 0] fun ε : ℝ => ε ^ 6 := by
  refine (((h 0).const_mul_left (c 0)).add ((h 1).const_mul_left (c 1))).congr_left fun ε => ?_
  simp only [dotProduct, Fin.sum_univ_two]
  ring

/-- A linear form of a displacement. -/
theorem Exp3.dot_small {f : ℝ → Fin 2 → ℝ} {a b : Fin 2 → ℝ} (h : Exp3 f a b) (c : Fin 2 → ℝ) :
    (fun ε => c ⬝ᵥ f ε - c ⬝ᵥ a) =O[𝓝 0] fun ε : ℝ => ε ^ 3 := by
  refine (((h.small 0).const_mul_left (c 0)).add ((h.small 1).const_mul_left (c 1))).congr_left
    fun ε => ?_
  simp only [dotProduct, Fin.sum_univ_two]
  ring

/-- Cubing a displacement of order `ε³`. -/
theorem cube_small {g : ℝ → ℝ} {α : ℝ} (h : (fun ε => g ε - α) =O[𝓝 0] fun ε : ℝ => ε ^ 3) :
    (fun ε => g ε ^ 3 - α ^ 3) =O[𝓝 0] fun ε : ℝ => ε ^ 3 := by
  have hg : g =O[𝓝 0] fun _ => (1 : ℝ) :=
    ((isBigO_one_of_three h).add (isBigO_const_const α one_ne_zero _)).congr_left
      fun ε => by ring
  have hq : (fun ε => g ε ^ 2 + g ε * α + α ^ 2) =O[𝓝 0] fun _ => (1 : ℝ) :=
    (((isBigO_one_mul hg hg).add (isBigO_one_mul hg (isBigO_const_const α one_ne_zero _))).add
      (isBigO_const_const (α ^ 2) one_ne_zero _)).congr_left fun ε => by ring
  exact (h.mul hq).congr (fun ε => by ring) fun ε => by ring

/-- Cubing a first-order expansion: `(α + ε³ β + O(ε⁶))³ = α³ + ε³ 3α²β + O(ε⁶)`. -/
theorem cube_exp {g : ℝ → ℝ} {α β : ℝ}
    (h : (fun ε => g ε - α - ε ^ 3 * β) =O[𝓝 0] fun ε : ℝ => ε ^ 6) :
    (fun ε => g ε ^ 3 - α ^ 3 - ε ^ 3 * (3 * α ^ 2 * β)) =O[𝓝 0] fun ε : ℝ => ε ^ 6 := by
  have he : (fun ε => g ε - α) =O[𝓝 0] fun ε : ℝ => ε ^ 3 := by
    exact (h.trans isBigO_six_three).add (isBigO_cube_const β) |>.congr_left fun ε => by ring
  have hb : (fun ε => 3 * α + (g ε - α)) =O[𝓝 0] fun _ => (1 : ℝ) :=
    (isBigO_const_const (3 * α) one_ne_zero _).add (isBigO_one_of_three he)
  have hsq : (fun ε => (g ε - α) * (g ε - α)) =O[𝓝 0] fun ε : ℝ => ε ^ 6 :=
    (he.mul he).congr_right fun ε => by ring
  have h3 := (h.const_mul_left (3 * α ^ 2)).add ((hb.mul hsq).congr_right fun ε => one_mul _)
  exact h3.congr (fun ε => by ring) fun ε => by ring

/-- **An inactive layer `F_{εB}` adds `ε³ (B a)^{⊙3}` to the first-order term.** -/
theorem Exp3.inactive {f : ℝ → Fin 2 → ℝ} {a b : Fin 2 → ℝ} (h : Exp3 f a b)
    (B : Matrix (Fin 2) (Fin 2) ℝ) :
    Exp3 (fun ε => layer (ε • B) (f ε)) a (b + (B *ᵥ a) ^ 3) := by
  intro k
  have hc := cube_small (h.dot_small (B k))
  refine ((h k).add (isBigO_cube_mul hc)).congr_left fun ε => ?_
  simp only [layer_apply, Pi.add_apply, Pi.pow_apply, mulVec_apply_two, smul_row,
    smul_dotProduct, smul_eq_mul]
  ring

/-- **The active layer `F_{A + ε³Δ}`**: the first-order term becomes
`DF_A(a) b + 3 (A a)^{⊙2} ⊙ (Δ a)`. -/
theorem Exp3.active {f : ℝ → Fin 2 → ℝ} {a b : Fin 2 → ℝ} (h : Exp3 f a b)
    (A Δ : Matrix (Fin 2) (Fin 2) ℝ) :
    Exp3 (fun ε => layer (A + ε ^ 3 • Δ) (f ε)) (layer A a)
      (dLayer A a b + 3 * (A *ᵥ a) ^ 2 * (Δ *ᵥ a)) := by
  intro k
  have hg : (fun ε => (A k ⬝ᵥ f ε + ε ^ 3 * (Δ k ⬝ᵥ f ε)) - A k ⬝ᵥ a -
      ε ^ 3 * (A k ⬝ᵥ b + Δ k ⬝ᵥ a)) =O[𝓝 0] fun ε : ℝ => ε ^ 6 :=
    ((h.dot (A k)).add (isBigO_cube_mul (h.dot_small (Δ k)))).congr_left fun ε => by ring
  refine ((h k).add (cube_exp hg)).congr_left fun ε => ?_
  simp only [layer_apply, dLayer, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, mulVec_apply_two,
    add_row, smul_row, add_dotProduct, smul_dotProduct, smul_eq_mul, Pi.ofNat_apply]
  ring

/-! ### The expansion of the network -/

theorem net_thetaEps_apply (A Δ : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (ε : ℝ) (x : Fin 2 → ℝ) :
    net (thetaEps A Δ p V ε) x =
      layer (scaledBlocks A Δ p V ε 3) (layer (scaledBlocks A Δ p V ε 2)
        (layer (scaledBlocks A Δ p V ε 1) (layer (scaledBlocks A Δ p V ε 0) x))) := by
  rw [net_eq_comp, rawW_thetaEps]; rfl

/-- **First-order expansion of the network, every target and position**:
`net θ_ε x = F_A x + ε³ lead A p Δ V x + O(ε⁶)` coordinatewise. -/
theorem net_thetaEps_exp3 (A Δ : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    Exp3 (fun ε => net (thetaEps A Δ p V ε) x) (layer A x) (lead A p Δ V x) := by
  have h0 := Exp3.const x
  fin_cases p
  · refine ((((h0.active A Δ).inactive (V 0)).inactive (V 1)).inactive (V 2)).congr
      (fun ε => by rw [net_thetaEps_apply]; rfl) rfl ?_
    funext k; fin_cases k <;> simp [lead, Spre, Ssuf, pre, suf, dLayer,
      Fin.sum_univ_three] <;> ring
  · refine ((((h0.inactive (V 0)).active A Δ).inactive (V 1)).inactive (V 2)).congr
      (fun ε => by rw [net_thetaEps_apply]; rfl) rfl ?_
    funext k; fin_cases k <;> simp [lead, Spre, Ssuf, pre, suf, Finset.sum_filter, dLayer,
      Fin.sum_univ_three] <;> ring
  · refine ((((h0.inactive (V 0)).inactive (V 1)).active A Δ).inactive (V 2)).congr
      (fun ε => by rw [net_thetaEps_apply]; rfl) rfl ?_
    funext k; fin_cases k <;> simp [lead, Spre, Ssuf, pre, suf, Finset.sum_filter, dLayer,
      Fin.sum_univ_three] <;> ring
  · refine ((((h0.inactive (V 0)).inactive (V 1)).inactive (V 2)).active A Δ).congr
      (fun ε => by rw [net_thetaEps_apply]; rfl) rfl ?_
    funext k; fin_cases k <;> simp [lead, Spre, Ssuf, pre, suf, Finset.sum_filter, dLayer,
      Fin.sum_univ_three] <;> ring

/-- **Item 1 (the expansion), remainder `O(ε⁶)`.** For every target `A`, position `p`,
perturbation `Δ` of the active block, inactive blocks `V`, input `x` and output `k`:
`net θ_ε x k - F_A(x)_k - ε³ lead A p Δ V x k = O(ε⁶)` as `ε → 0`. -/
theorem net_expansion (A Δ : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) (k : Fin 2) :
    (fun ε => net (thetaEps A Δ p V ε) x k - layer A x k - ε ^ 3 * lead A p Δ V x k)
      =O[𝓝 0] fun ε : ℝ => ε ^ 6 :=
  net_thetaEps_exp3 A Δ p V x k

/-- The same with the remainder `O(ε⁴)`, the form asked for in the brief. -/
theorem net_expansion_four (A Δ : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 4)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) (k : Fin 2) :
    (fun ε => net (thetaEps A Δ p V ε) x k - layer A x k - ε ^ 3 * lead A p Δ V x k)
      =O[𝓝 0] fun ε : ℝ => ε ^ 4 := by
  have h : (fun ε : ℝ => ε ^ 6) =O[𝓝 0] fun ε : ℝ => ε ^ 4 :=
    ((isBigO_pow_one 2 (by norm_num)).mul (isBigO_refl (fun ε : ℝ => ε ^ 4) (𝓝 0))).congr
      (fun ε => by ring) fun ε => by ring
  exact (net_expansion A Δ p V x k).trans h

end VectorSLT.LeadingMap
