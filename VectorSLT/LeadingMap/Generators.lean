/-
Real mirrors of the slt-bridge leading maps (item 3 of the leading-map brief).

slt-bridge (https://github.com/bubskee/slt-bridge) defines three complex maps on `ℂ¹²`:
`SLT.MiddlePositions.R2`, `SLT.MiddlePositions.R3` (both through `SLT.MiddlePositions.generators`)
and `SLT.PositionFour.leadingMap`, in `SLT/MiddlePositions/Defs.lean`,
`SLT/PositionFour/Defs.lean` and `SLT/PositionFour/Upstream/Algebra.lean` (`twoCube`). The
definitions below are the same formulas with `ℂ` replaced by `ℝ`, the same names, the same
argument order and the same component order. Each docstring names the definition it mirrors.

The last section feeds them from the network: `gens2`, `gens3`, `gens4` are the generator vectors
of the inactive blocks `V` at Lean positions `1, 2, 3` (paper positions two, three, four), with
row `k` of block `V_l` read as the form `rowForm (V l) k`.
-/
import VectorSLT.LeadingMap.Table

namespace VectorSLT.LeadingMap

/-! ### Mirrors of slt-bridge -/

/-- Mirrors `SLT.PositionFour.Form` (`ℂ × ℂ`): a binary linear form `a s + b t` as `(a, b)`. -/
abbrev Form := ℝ × ℝ

/-- Mirrors `SLT.PositionFour.Cubic` (`Fin 4 → ℂ`): a binary cubic in moment coordinates,
`P = P₀ s³ + 3 P₁ s² t + 3 P₂ s t² + P₃ t³`. -/
abbrev Cubic := Fin 4 → ℝ

/-- Mirrors `SLT.PositionFour.cube`: `(a s + b t)³ ↦ (a³, a² b, a b², b³)`. -/
def cube (l : Form) : Cubic := ![l.1 ^ 3, l.1 ^ 2 * l.2, l.1 * l.2 ^ 2, l.2 ^ 3]

/-- Mirrors `SLT.PositionFour.twoCube` (`SLT/PositionFour/Upstream/Algebra.lean`):
`twoCube g = cube g.1 + cube g.2`. -/
def twoCube (g : Form × Form) : Cubic := cube g.1 + cube g.2

/-- Mirrors `SLT.PositionFour.Row`: a row of the three inactive blocks, three linear forms. -/
abbrev Row := Fin 3 → Form

/-- Mirrors `SLT.PositionFour.rowCubic`: `T(l₁, l₂, l₃) = l₁³ + l₂³ + l₃³`. -/
def rowCubic (r : Row) : Cubic := ∑ i, cube (r i)

/-- Mirrors `SLT.PositionFour.leadingMap`, component by component:
`(rowCubic w.1 0 - rowCubic w.2 0, rowCubic w.1 1 - rowCubic w.2 1, rowCubic w.1 2,
rowCubic w.1 3, rowCubic w.2 2, rowCubic w.2 3)`. -/
def leadingMap (w : Row × Row) : Fin 6 → ℝ :=
  ![rowCubic w.1 0 - rowCubic w.2 0, rowCubic w.1 1 - rowCubic w.2 1,
    rowCubic w.1 2, rowCubic w.1 3, rowCubic w.2 2, rowCubic w.2 3]

/-- Mirrors `SLT.MiddlePositions.generators`, component by component:
`p₁ 2, p₁ 3, q₁ 2, q₁ 3, p₂ 2, p₂ 3, q₂ 2, q₂ 3, p₁ 1 - p₂ 1, q₁ 1 - q₂ 1, p₁ 0 - p₂ 0 + q₁ 1`. -/
def generators (p₁ q₁ p₂ q₂ : Cubic) : Fin 11 → ℝ :=
  ![p₁ 2, p₁ 3, q₁ 2, q₁ 3, p₂ 2, p₂ 3, q₂ 2, q₂ 3,
    p₁ 1 - p₂ 1, q₁ 1 - q₂ 1, p₁ 0 - p₂ 0 + q₁ 1]

/-- Mirrors `SLT.MiddlePositions.Row2`: one prefix form and a pair of suffix forms. -/
abbrev Row2 := Form × (Form × Form)

/-- Mirrors `SLT.MiddlePositions.Row3`: a pair of prefix forms and one suffix form. -/
abbrev Row3 := (Form × Form) × Form

/-- Mirrors `SLT.MiddlePositions.R2`:
`generators (cube w.1.1) (twoCube w.1.2) (cube w.2.1) (twoCube w.2.2)`. -/
def R2 (w : Row2 × Row2) : Fin 11 → ℝ :=
  generators (cube w.1.1) (twoCube w.1.2) (cube w.2.1) (twoCube w.2.2)

/-- Mirrors `SLT.MiddlePositions.R3`:
`generators (twoCube w.1.1) (cube w.1.2) (twoCube w.2.1) (cube w.2.2)`. -/
def R3 (w : Row3 × Row3) : Fin 11 → ℝ :=
  generators (twoCube w.1.1) (cube w.1.2) (twoCube w.2.1) (cube w.2.2)

/-! ### The inactive variables of the network, in slt-bridge's layout -/

/-- Position two (Lean `p = 1`): prefix block `V₀`, suffix blocks `V₁, V₂`; the first row of
slt-bridge is Lean row `0`. -/
def w2 (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) : Row2 × Row2 :=
  ((rowForm (V 0) 0, (rowForm (V 1) 0, rowForm (V 2) 0)),
    (rowForm (V 0) 1, (rowForm (V 1) 1, rowForm (V 2) 1)))

/-- Position three (Lean `p = 2`): prefix blocks `V₀, V₁`, suffix block `V₂`. -/
def w3 (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) : Row3 × Row3 :=
  (((rowForm (V 0) 0, rowForm (V 1) 0), rowForm (V 2) 0),
    ((rowForm (V 0) 1, rowForm (V 1) 1), rowForm (V 2) 1))

/-- Position four (Lean `p = 3`): all three blocks are prefix. -/
def w4 (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) : Row × Row :=
  (fun l => rowForm (V l) 0, fun l => rowForm (V l) 1)

/-- The generators at position two: `R2 (w2 V)`. -/
def gens2 (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) : Fin 11 → ℝ := R2 (w2 V)

/-- The generators at position three: `R3 (w3 V)`. -/
def gens3 (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) : Fin 11 → ℝ := R3 (w3 V)

/-- The generators at position four: `leadingMap (w4 V)`. -/
def gens4 (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) : Fin 6 → ℝ := leadingMap (w4 V)

end VectorSLT.LeadingMap
