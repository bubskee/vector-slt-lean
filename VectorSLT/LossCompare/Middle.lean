/-
Loss comparison at positions two and three (Lean `p = 1, 2`).

Eleven exact error coefficients are used: `st²`, `t³`, `s⁵`, `s⁴t`, `s³t²` of both rows and `s⁷`
of row `0` (`cf`). Their weight-three parts determine the eleven generators of `R2` / `R3`; the
coefficients of degree at most five alone have rank ten.

For each coefficient `f = cf j (table)`, the active row `k` enters through the cube moments
`(u_k, m_k, n_k, o_k) = (α³, α²ν, αν², ν³)`, and `f` is affine in the `n`'s and `o`'s that occur.
With a monomial multiplier `A_j = Mult j (u, m)` the products `u n = m²`, `u² o = m³` turn
`A_j f` into a polynomial `Fm p j (u, m, w)` (`mult_identity`), and `ĝ_j(w) = Fm p j (z₀(w), w)`.
-/
import VectorSLT.LossCompare.Elim
import VectorSLT.LossCompare.Tables

namespace VectorSLT.LossCompare

open MeasureTheory Set Filter Metric Topology VectorSLT VectorSLT.LeadingMap
open scoped ENNReal

/-! ### Tables at a position -/

/-- Cube moments of the three inactive blocks. -/
abbrev Inact := Fin 3 → Fin 2 → Fin 4 → ℝ

/-- The four-block table with the active rows `act` at position `p`. -/
def tab (p : Fin 4) (act : Fin 2 → Fin 4 → ℝ) (a : Inact) : Tab4 :=
  Fin.insertNth (α := fun _ => Fin 2 → Fin 4 → ℝ) p act a

theorem tab_one (act : Fin 2 → Fin 4 → ℝ) (a : Inact) : tab 1 act a = ![a 0, act, a 1, a 2] := by
  funext l; fin_cases l <;> rfl

theorem tab_two (act : Fin 2 → Fin 4 → ℝ) (a : Inact) : tab 2 act a = ![a 0, a 1, act, a 2] := by
  funext l; fin_cases l <;> rfl

/-- The cube moments of three blocks. -/
def cubeTab (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) : Inact := fun l k => cube (rowForm (V l) k)

theorem cmOf_eq_tab (p : Fin 4) (θ : Raw16) :
    cmOf (rawW θ) = tab p (fun k => cube (rowForm (rawW θ p) k)) (cubeTab (inact p θ)) := by
  funext l
  unfold cmOf tab cubeTab inact
  rcases Fin.eq_self_or_eq_succAbove p l with rfl | ⟨j, rfl⟩
  · simp
  · simp [Fin.removeNth]

/-- Active rows from `z = (u₀, m₀, u₁, m₁)` and the higher moments `n`, `o`. -/
def actZ (z : Fin 4 → ℝ) (n o : Fin 2 → ℝ) : Fin 2 → Fin 4 → ℝ :=
  ![![z 0, z 1, n 0, o 0], ![z 2, z 3, n 1, o 1]]

theorem cube_rows (p : Fin 4) (θ : Raw16) :
    (fun k => cube (rowForm (rawW θ p) k)) = actZ (zact p θ)
      (fun k => (rowForm (rawW θ p) k).1 * (rowForm (rawW θ p) k).2 ^ 2)
      (fun k => (rowForm (rawW θ p) k).2 ^ 3) := by
  funext k i
  fin_cases k <;> fin_cases i <;> rfl

/-! ### The eleven coefficients, multipliers and eliminated forms -/

/-- The eleven coefficient functionals. -/
def cf (j : Fin 11) (T : Tab4) : ℝ :=
  match j with
  | 0 => C12 T 0 | 1 => C03 T 0 | 2 => C12 T 1 | 3 => C03 T 1 | 4 => C50 T 0 | 5 => C50 T 1
  | 6 => C41 T 0 | 7 => C41 T 1 | 8 => C32 T 0 | 9 => C32 T 1 | 10 => C70 T 0

/-- The multipliers, monomials in `u₀ = z 0`, `u₁ = z 2`. -/
def Mult (j : Fin 11) (z : Fin 4 → ℝ) : ℝ :=
  match j with
  | 0 => z 0 | 1 => z 0 ^ 2 | 2 => z 2 | 3 => z 2 ^ 2 | 4 => 1 | 5 => 1 | 6 => z 0 | 7 => z 2
  | 8 => z 0 ^ 2 * z 2 | 9 => z 2 ^ 2 * z 0 | 10 => z 0

/-- The table with `n = o = 0`. -/
def T0 (p : Fin 4) (z : Fin 4 → ℝ) (a : Inact) : Tab4 := tab p (actZ z 0 0) a

/-- The coefficient of `n_k` (`C` is affine in it). -/
def dN (p : Fin 4) (C : Tab4 → ℝ) (k : Fin 2) (z : Fin 4 → ℝ) (a : Inact) : ℝ :=
  C (tab p (actZ z (Pi.single k 1) 0) a) - C (T0 p z a)

/-- The coefficient of `o_k`. -/
def dO (p : Fin 4) (C : Tab4 → ℝ) (k : Fin 2) (z : Fin 4 → ℝ) (a : Inact) : ℝ :=
  C (tab p (actZ z 0 (Pi.single k 1)) a) - C (T0 p z a)

/-- **The eliminated polynomials** `Fm p j (u, m, a) = Mult j · cf j` with `n = m²/u`,
`o = m³/u²` cleared. -/
def Fm (p : Fin 4) (j : Fin 11) (z : Fin 4 → ℝ) (a : Inact) : ℝ :=
  match j with
  | 0 => z 0 * C12 (T0 p z a) 0 + z 1 ^ 2 * dN p (C12 · 0) 0 z a
  | 1 => z 0 ^ 2 * C03 (T0 p z a) 0 + z 1 ^ 3 * dO p (C03 · 0) 0 z a
  | 2 => z 2 * C12 (T0 p z a) 1 + z 3 ^ 2 * dN p (C12 · 1) 1 z a
  | 3 => z 2 ^ 2 * C03 (T0 p z a) 1 + z 3 ^ 3 * dO p (C03 · 1) 1 z a
  | 4 => C50 (T0 p z a) 0
  | 5 => C50 (T0 p z a) 1
  | 6 => z 0 * C41 (T0 p z a) 0 + z 1 ^ 2 * dN p (C41 · 0) 0 z a
  | 7 => z 2 * C41 (T0 p z a) 1 + z 3 ^ 2 * dN p (C41 · 1) 1 z a
  | 8 => z 0 ^ 2 * z 2 * C32 (T0 p z a) 0 + z 0 * z 2 * z 1 ^ 2 * dN p (C32 · 0) 0 z a +
      z 0 ^ 2 * z 3 ^ 2 * dN p (C32 · 0) 1 z a + z 2 * z 1 ^ 3 * dO p (C32 · 0) 0 z a
  | 9 => z 2 ^ 2 * z 0 * C32 (T0 p z a) 1 + z 2 * z 0 * z 3 ^ 2 * dN p (C32 · 1) 1 z a +
      z 2 ^ 2 * z 1 ^ 2 * dN p (C32 · 1) 0 z a + z 0 * z 3 ^ 3 * dO p (C32 · 1) 1 z a
  | 10 => z 0 * C70 (T0 p z a) 0 + z 1 ^ 2 * dN p (C70 · 0) 0 z a

/-- The active moments of row forms `(α_k, ν_k)`. -/
def zOf (α ν : Fin 2 → ℝ) : Fin 4 → ℝ := ![α 0 ^ 3, α 0 ^ 2 * ν 0, α 1 ^ 3, α 1 ^ 2 * ν 1]

theorem mult_identity_one (j : Fin 11) (α ν : Fin 2 → ℝ) (a : Inact) :
    Mult j (zOf α ν) * cf j (tab 1 (actZ (zOf α ν) (fun k => α k * ν k ^ 2) (fun k => ν k ^ 3)) a) =
      Fm 1 j (zOf α ν) a := by
  fin_cases j <;>
    simp only [Mult, cf, Fm, T0, dN, dO, tab_one, actZ, zOf, C12, C03, C50, C41, C32, C70, sg5,
      tg5, E5, blk50, blk41, blk32, sg, tg, Fin.sum_univ_four, Finset.sum_filter] <;>
    simp <;> ring

theorem mult_identity_two (j : Fin 11) (α ν : Fin 2 → ℝ) (a : Inact) :
    Mult j (zOf α ν) * cf j (tab 2 (actZ (zOf α ν) (fun k => α k * ν k ^ 2) (fun k => ν k ^ 3)) a) =
      Fm 2 j (zOf α ν) a := by
  fin_cases j <;>
    simp only [Mult, cf, Fm, T0, dN, dO, tab_two, actZ, zOf, C12, C03, C50, C41, C32, C70, sg5,
      tg5, E5, blk50, blk41, blk32, sg, tg, Fin.sum_univ_four, Finset.sum_filter] <;>
    simp <;> ring

/-- **The multiplier identity** at positions two and three: `Mult j · cf j = Fm p j` at every
parameter. -/
theorem mult_identity {p : Fin 4} (hp : p = 1 ∨ p = 2) (j : Fin 11) (θ : Raw16) :
    Mult j (zact p θ) * cf j (cmOf (rawW θ)) = Fm p j (zact p θ) (cubeTab (inact p θ)) := by
  have hz : zact p θ = zOf (fun k => (rowForm (rawW θ p) k).1) (fun k => (rowForm (rawW θ p) k).2) := by
    funext i; fin_cases i <;> rfl
  rw [cmOf_eq_tab p, cube_rows, hz]
  rcases hp with rfl | rfl
  · exact mult_identity_one j _ _ _
  · exact mult_identity_two j _ _ _

/-! ### Weighted homogeneity -/

/-- `P_i⁽ᵏ⁾` of the inactive table. -/
def Pa (a : Inact) (k : Fin 2) (i : Fin 4) : ℝ := ∑ l, a l k i

/-- The point `𝐜 = 0` from the inactive table: `(1 - P₀⁽⁰⁾, -P₁⁽⁰⁾, 1 - P₀⁽¹⁾, -P₁⁽¹⁾)`. -/
def z0a (a : Inact) : Fin 4 → ℝ := ![1 - Pa a 0 0, -Pa a 0 1, 1 - Pa a 1 0, -Pa a 1 1]
/-- Its weight-three part. -/
def zhat (a : Inact) : Fin 4 → ℝ := ![-Pa a 0 0, -Pa a 0 1, -Pa a 1 0, -Pa a 1 1]

/-- The constant table: active `u = 1`, everything else `0`. -/
def eTab (p : Fin 4) : Tab4 := T0 p ![1, 0, 1, 0] 0
/-- The weight-three table. -/
def yTab (p : Fin 4) (a : Inact) : Tab4 := T0 p (zhat a) a

theorem T0_scale {p : Fin 4} (hp : p = 1 ∨ p = 2) (s : ℝ) (a : Inact) :
    T0 p (z0a (s • a)) (s • a) = eTab p + s • yTab p a := by
  funext l k i
  rcases hp with rfl | rfl <;>
  fin_cases l <;> fin_cases k <;> fin_cases i <;>
    simp [T0, eTab, yTab, tab_one, tab_two, actZ, z0a, zhat, Pa, Finset.mul_sum] <;> ring

section Polarization

variable {p : Fin 4} (hp : p = 1 ∨ p = 2) (s : ℝ) (y : Tab4)
include hp

theorem pol12 (k : Fin 2) : C12 (eTab p + s • y) k = s * C12 y k := by
  rcases hp with rfl | rfl <;> fin_cases k <;>
    simp [C12, eTab, T0, tab_one, tab_two, actZ, Fin.sum_univ_four] <;> ring

theorem pol03 (k : Fin 2) : C03 (eTab p + s • y) k = s * C03 y k := by
  rcases hp with rfl | rfl <;> fin_cases k <;>
    simp [C03, eTab, T0, tab_one, tab_two, actZ, Fin.sum_univ_four] <;> ring

theorem pol50 (k : Fin 2) : C50 (eTab p + s • y) k =
    s * (C50 (eTab p + y) k - C50 y k + s * C50 y k) := by
  rcases hp with rfl | rfl <;> fin_cases k <;>
    simp [C50, blk50, sg, tg, eTab, T0, tab_one, tab_two, actZ, Fin.sum_univ_four,
      Finset.sum_filter] <;> ring

theorem pol41 (k : Fin 2) : C41 (eTab p + s • y) k =
    s * (C41 (eTab p + y) k - C41 y k + s * C41 y k) := by
  rcases hp with rfl | rfl <;> fin_cases k <;>
    simp [C41, blk41, sg, tg, eTab, T0, tab_one, tab_two, actZ, Fin.sum_univ_four,
      Finset.sum_filter] <;> ring

theorem pol32 (k : Fin 2) : C32 (eTab p + s • y) k =
    s * (C32 (eTab p + y) k - C32 y k + s * C32 y k) := by
  rcases hp with rfl | rfl <;> fin_cases k <;>
    simp [C32, blk32, sg, tg, eTab, T0, tab_one, tab_two, actZ, Fin.sum_univ_four,
      Finset.sum_filter] <;> ring

theorem pol70 : C70 (eTab p + s • y) 0 =
    s * ((C70 (eTab p + y) 0 - C70 (eTab p - y) 0) / 2 - C70 y 0 +
      s * ((C70 (eTab p + y) 0 + C70 (eTab p - y) 0) / 2) + s ^ 2 * C70 y 0) := by
  rcases hp with rfl | rfl <;>
    simp [C70, sg5, tg5, E5, blk50, sg, tg, eTab, T0, tab_one, tab_two, actZ, Fin.sum_univ_four,
      Finset.sum_filter] <;> ring

end Polarization

/-- **The eliminated coefficients** `ĝ_j(a) = Fm p j (z₀(a), a)`, polynomials in the inactive
cube moments. -/
def ghat (p : Fin 4) (j : Fin 11) (a : Inact) : ℝ := Fm p j (z0a a) a

section Radial

variable (p : Fin 4) (s : ℝ) (a : Inact)

/-- The quadratic factor `C(e + y) - C(y) + s C(y)`. -/
def qf (C : Tab4 → ℝ) : ℝ := C (eTab p + yTab p a) - C (yTab p a) + s * C (yTab p a)

/-- The cubic factor of `C₇₀`. -/
noncomputable def kf : ℝ :=
  (C70 (eTab p + yTab p a) 0 - C70 (eTab p - yTab p a) 0) / 2 - C70 (yTab p a) 0 +
    s * ((C70 (eTab p + yTab p a) 0 + C70 (eTab p - yTab p a) 0) / 2) + s ^ 2 * C70 (yTab p a) 0

/-- `dN` and `dO` along the scaled point. -/
def DN (C : Tab4 → ℝ) (k : Fin 2) : ℝ := dN p C k (z0a (s • a)) (s • a)
def DO (C : Tab4 → ℝ) (k : Fin 2) : ℝ := dO p C k (z0a (s • a)) (s • a)

/-- **The radial components** `h_j(s, a)`, with `ĝ_j(s a) = s h_j(s, a)` (`ghat_smul`). -/
noncomputable def hS (j : Fin 11) : ℝ :=
  match j with
  | 0 => (1 - s * Pa a 0 0) * C12 (yTab p a) 0 + s * Pa a 0 1 ^ 2 * DN p s a (C12 · 0) 0
  | 1 => (1 - s * Pa a 0 0) ^ 2 * C03 (yTab p a) 0 - s ^ 2 * Pa a 0 1 ^ 3 * DO p s a (C03 · 0) 0
  | 2 => (1 - s * Pa a 1 0) * C12 (yTab p a) 1 + s * Pa a 1 1 ^ 2 * DN p s a (C12 · 1) 1
  | 3 => (1 - s * Pa a 1 0) ^ 2 * C03 (yTab p a) 1 - s ^ 2 * Pa a 1 1 ^ 3 * DO p s a (C03 · 1) 1
  | 4 => qf p s a (C50 · 0)
  | 5 => qf p s a (C50 · 1)
  | 6 => (1 - s * Pa a 0 0) * qf p s a (C41 · 0) + s * Pa a 0 1 ^ 2 * DN p s a (C41 · 0) 0
  | 7 => (1 - s * Pa a 1 0) * qf p s a (C41 · 1) + s * Pa a 1 1 ^ 2 * DN p s a (C41 · 1) 1
  | 8 => (1 - s * Pa a 0 0) ^ 2 * (1 - s * Pa a 1 0) * qf p s a (C32 · 0) +
      (1 - s * Pa a 0 0) * (1 - s * Pa a 1 0) * s * Pa a 0 1 ^ 2 * DN p s a (C32 · 0) 0 +
      (1 - s * Pa a 0 0) ^ 2 * s * Pa a 1 1 ^ 2 * DN p s a (C32 · 0) 1 -
      (1 - s * Pa a 1 0) * s ^ 2 * Pa a 0 1 ^ 3 * DO p s a (C32 · 0) 0
  | 9 => (1 - s * Pa a 1 0) ^ 2 * (1 - s * Pa a 0 0) * qf p s a (C32 · 1) +
      (1 - s * Pa a 1 0) * (1 - s * Pa a 0 0) * s * Pa a 1 1 ^ 2 * DN p s a (C32 · 1) 1 +
      (1 - s * Pa a 1 0) ^ 2 * s * Pa a 0 1 ^ 2 * DN p s a (C32 · 1) 0 -
      (1 - s * Pa a 0 0) * s ^ 2 * Pa a 1 1 ^ 3 * DO p s a (C32 · 1) 1
  | 10 => (1 - s * Pa a 0 0) * kf p s a + s * Pa a 0 1 ^ 2 * DN p s a (C70 · 0) 0

end Radial

theorem Pa_smul (s : ℝ) (a : Inact) (k : Fin 2) (i : Fin 4) : Pa (s • a) k i = s * Pa a k i := by
  simp [Pa, Finset.mul_sum]

theorem z0a_smul (s : ℝ) (a : Inact) :
    z0a (s • a) = ![1 - s * Pa a 0 0, -(s * Pa a 0 1), 1 - s * Pa a 1 0, -(s * Pa a 1 1)] := by
  simp only [z0a, Pa_smul]

/-- **Weighted homogeneity of the eliminated coefficients**: `ĝ_j(s a) = s h_j(s, a)`. -/
theorem ghat_smul {p : Fin 4} (hp : p = 1 ∨ p = 2) (j : Fin 11) (s : ℝ) (a : Inact) :
    ghat p j (s • a) = s * hS p s a j := by
  have hT := T0_scale hp s a
  have hz := z0a_smul s a
  have e0 : z0a (s • a) 0 = 1 - s * Pa a 0 0 := by rw [hz]; rfl
  have e1 : z0a (s • a) 1 = -(s * Pa a 0 1) := by rw [hz]; rfl
  have e2 : z0a (s • a) 2 = 1 - s * Pa a 1 0 := by rw [hz]; rfl
  have e3 : z0a (s • a) 3 = -(s * Pa a 1 1) := by rw [hz]; rfl
  fin_cases j <;>
    simp only [ghat, Fm, hS, qf, kf, DN, DO, hT, e0, e1, e2, e3, pol12 hp, pol03 hp, pol50 hp,
      pol41 hp, pol32 hp, pol70 hp, Fin.isValue] <;>
    ring

/-! ### The leading part: the generators of `R2` and `R3` -/

/-- The weight-three parts `L_j(a) = h_j(0, a)`. -/
noncomputable def Lw (p : Fin 4) (a : Inact) (j : Fin 11) : ℝ :=
  match j with
  | 0 => C12 (yTab p a) 0 | 1 => C03 (yTab p a) 0 | 2 => C12 (yTab p a) 1 | 3 => C03 (yTab p a) 1
  | 4 => C50 (eTab p + yTab p a) 0 - C50 (yTab p a) 0
  | 5 => C50 (eTab p + yTab p a) 1 - C50 (yTab p a) 1
  | 6 => C41 (eTab p + yTab p a) 0 - C41 (yTab p a) 0
  | 7 => C41 (eTab p + yTab p a) 1 - C41 (yTab p a) 1
  | 8 => C32 (eTab p + yTab p a) 0 - C32 (yTab p a) 0
  | 9 => C32 (eTab p + yTab p a) 1 - C32 (yTab p a) 1
  | 10 => (C70 (eTab p + yTab p a) 0 - C70 (eTab p - yTab p a) 0) / 2 - C70 (yTab p a) 0

theorem hS_zero (p : Fin 4) (a : Inact) (j : Fin 11) : hS p 0 a j = Lw p a j := by
  fin_cases j <;> simp [hS, Lw, qf, kf]

/-- The linear change from the eleven weight-three parts to the eleven generators
`(p¹₂, p¹₃, q¹₂, q¹₃, p²₂, p²₃, q²₂, q²₃, p¹₁ - p²₁, q¹₁ - q²₁, p¹₀ - p²₀ + q¹₁)`. -/
noncomputable def Nmid (L : Fin 11 → ℝ) : Fin 11 → ℝ :=
  let g2 := L 10 / 3
  let g0 := L 0 / 3 - g2
  let g8 := (L 6 / 3 - 2 * g2) / 3
  let g6 := (L 7 / 3 - 3 * g8) / 2
  let g4 := L 2 / 3 - g6
  let g3 := L 8 / 3 - 3 * (g0 - g4)
  let g7 := L 9 / 3 - 3 * (g0 - g4)
  let g10 := L 4 / 3
  ![g0, L 1 - g3, g2, g3, g4, L 3 - g7, g6, g7, g8, g10 - L 5 / 3, g10]

theorem Nmid_smul (c : ℝ) (L : Fin 11 → ℝ) : Nmid (c • L) = c • Nmid L := by
  funext i; fin_cases i <;> simp [Nmid] <;> ring

theorem Nmid_add (L L' : Fin 11 → ℝ) : Nmid (L + L') = Nmid L + Nmid L' := by
  funext i; fin_cases i <;> simp [Nmid] <;> ring

/-- The eleven generators from the inactive moments: prefix `p_i⁽ᵏ⁾`, suffix `q_i⁽ᵏ⁾`. -/
def gvec (pre suf : Fin 2 → Fin 4 → ℝ) : Fin 11 → ℝ :=
  ![pre 0 2, pre 0 3, suf 0 2, suf 0 3, pre 1 2, pre 1 3, suf 1 2, suf 1 3,
    pre 0 1 - pre 1 1, suf 0 1 - suf 1 1, pre 0 0 - pre 1 0 + suf 0 1]

/-- The weight-three parts in terms of the generators (the Proposition N1 table at `𝐜 = 0`). -/
def Lexp (g : Fin 11 → ℝ) : Fin 11 → ℝ :=
  ![3 * (g 0 + g 2), g 1 + g 3, 3 * (g 4 + g 6), g 5 + g 7, 3 * g 10, 3 * (g 10 - g 9),
    3 * (3 * g 8 + 2 * g 2), 3 * (3 * g 8 + 2 * g 6), 3 * (3 * (g 0 - g 4) + g 3),
    3 * (3 * (g 0 - g 4) + g 7), 3 * g 2]

theorem Nmid_Lexp (g : Fin 11 → ℝ) : Nmid (Lexp g) = g := by
  funext i; fin_cases i <;> simp [Nmid, Lexp]

/-- Prefix and suffix moments at positions two (`p = 1`) and three (`p = 2`). -/
def preM (p : Fin 4) (a : Inact) : Fin 2 → Fin 4 → ℝ := if p = 1 then a 0 else a 0 + a 1
def sufM (p : Fin 4) (a : Inact) : Fin 2 → Fin 4 → ℝ := if p = 1 then a 1 + a 2 else a 2

theorem Lw_eq {p : Fin 4} (hp : p = 1 ∨ p = 2) (a : Inact) (j : Fin 11) :
    Lw p a j = Lexp (gvec (preM p a) (sufM p a)) j := by
  rcases hp with rfl | rfl <;> fin_cases j <;>
    simp only [Lw, Lexp, gvec, preM, sufM, C12, C03, C50, C41, C32, C70, sg5, tg5, E5, blk50,
      blk41, blk32, sg, tg, eTab, yTab, T0, tab_one, tab_two, actZ, zhat, Pa, Fin.sum_univ_four,
      Fin.sum_univ_three, Finset.sum_filter] <;>
    simp <;> ring

/-- **Position two: the leading part is `R2`.** -/
theorem Nmid_Lw_one (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) :
    Nmid (Lw 1 (cubeTab V)) = gens2 V := by
  have : Lw 1 (cubeTab V) = Lexp (gvec (preM 1 (cubeTab V)) (sufM 1 (cubeTab V))) :=
    funext (Lw_eq (Or.inl rfl) _)
  rw [this, Nmid_Lexp]
  funext i
  fin_cases i <;> simp [gvec, preM, sufM, cubeTab, gens2, R2, w2, generators, twoCube]

/-- **Position three: the leading part is `R3`.** -/
theorem Nmid_Lw_two (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) :
    Nmid (Lw 2 (cubeTab V)) = gens3 V := by
  have : Lw 2 (cubeTab V) = Lexp (gvec (preM 2 (cubeTab V)) (sufM 2 (cubeTab V))) :=
    funext (Lw_eq (Or.inr rfl) _)
  rw [this, Nmid_Lexp]
  funext i
  fin_cases i <;> simp [gvec, preM, sufM, cubeTab, gens3, R3, w3, generators, twoCube]

end VectorSLT.LossCompare