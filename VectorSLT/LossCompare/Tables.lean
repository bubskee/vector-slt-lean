/-
Loss comparison, part 1c: the error coefficients as polynomials in the cube moments of the
blocks.

Write row `k` of block `l` as `a s + b t` and its cube in moment coordinates
`cube (a, b) = (a³, a²b, ab², b³)` (the slt-bridge `cube`). A table `T : Tab4` holds these
moments, `T l k`, for the four blocks in application order. Every coefficient used is a
polynomial in the table: the degree-three coefficients are linear, the degree-five ones are sums
over pairs of blocks `j < l` of a bilinear form in `(T l k, T j)` (`blk50`, `blk41`, `blk32`),
and the `s⁷` coefficient is cubic (`C70`). `errθ_tab` ties them to the error of `θ`, with
`T = cmOf (rawW θ)`.
-/
import VectorSLT.LossCompare.Coeffs7

namespace VectorSLT.LossCompare

open MvPolynomial Finset VectorSLT VectorSLT.LeadingMap

/-- Cube-moment tables: block, row, moment index. -/
abbrev Tab4 := Fin 4 → Fin 2 → Fin 4 → ℝ

/-- The table of the four raw blocks. -/
def cmOf (W : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ) : Tab4 := fun l k => cube (rowForm (W l) k)

section Functionals

variable (T : Tab4)

/-- Moments of the cubic state increment before block `l`: row `0` minus row `1`. -/
def sg (l i : Fin 4) : ℝ := ∑ j ∈ univ.filter (· < l), (T j 0 i - T j 1 i)
/-- Moments of the cubic state increment before block `l`: row `1`. -/
def tg (l i : Fin 4) : ℝ := ∑ j ∈ univ.filter (· < l), T j 1 i

/-- The `s⁵` part of `(row form)³` for block moments `c` and state moments `σ, τ`. -/
def blk50 (c σ τ : Fin 4 → ℝ) : ℝ := 3 * (c 0 * σ 0 + c 1 * τ 0)
/-- The `s⁴t` part. -/
def blk41 (c σ τ : Fin 4 → ℝ) : ℝ := 3 * (3 * (c 0 * σ 1 + c 1 * τ 1) + 2 * (c 1 * σ 0 + c 2 * τ 0))
/-- The `s³t²` part. -/
def blk32 (c σ τ : Fin 4 → ℝ) : ℝ :=
  3 * (3 * (c 0 * σ 2 + c 1 * τ 2) + 6 * (c 1 * σ 1 + c 2 * τ 1) + (c 2 * σ 0 + c 3 * τ 0))

/-- `[err_k]_{st²} = 3 ∑_l a_l b_l²`. -/
def C12 (k : Fin 2) : ℝ := 3 * ∑ l, T l k 2
/-- `[err_k]_{t³} = ∑_l b_l³`. -/
def C03 (k : Fin 2) : ℝ := ∑ l, T l k 3
/-- `[err_k]_{s⁵}`. -/
def C50 (k : Fin 2) : ℝ := ∑ l, blk50 (T l k) (sg T l) (tg T l)
/-- `[err_k]_{s⁴t}`. -/
def C41 (k : Fin 2) : ℝ := ∑ l, blk41 (T l k) (sg T l) (tg T l)
/-- `[err_k]_{s³t²}`. -/
def C32 (k : Fin 2) : ℝ := ∑ l, blk32 (T l k) (sg T l) (tg T l)

/-- The `s⁵` part contributed by block `l`, row `k`. -/
def E5 (l : Fin 4) (k : Fin 2) : ℝ := blk50 (T l k) (sg T l) (tg T l)
/-- `s⁵` moments of the quintic state increment before block `l`. -/
def sg5 (l : Fin 4) : ℝ := ∑ j ∈ univ.filter (· < l), (E5 T j 0 - E5 T j 1)
def tg5 (l : Fin 4) : ℝ := ∑ j ∈ univ.filter (· < l), E5 T j 1

/-- `[err_k]_{s⁷} = ∑_l (3 (a³ σ₅ + a²b τ₅) + 3 (a³ σ₀² + 2a²b σ₀τ₀ + ab² τ₀²))`. -/
def C70 (k : Fin 2) : ℝ :=
  ∑ l, (3 * (T l k 0 * sg5 T l + T l k 1 * tg5 T l) +
    3 * (T l k 0 * sg T l 0 ^ 2 + 2 * T l k 1 * sg T l 0 * tg T l 0 + T l k 2 * tg T l 0 ^ 2))

end Functionals

/-! ### The tie to the error -/

theorem cmOf_apply (W : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ) (l : Fin 4) (k : Fin 2) :
    cmOf W l k = ![rA W l k ^ 3, rA W l k ^ 2 * rB W l k, rA W l k * rB W l k ^ 2, rB W l k ^ 3] :=
  rfl

theorem cmOf0 (W : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ) (l : Fin 4) (k : Fin 2) :
    cmOf W l k 0 = rA W l k ^ 3 := rfl
theorem cmOf1 (W : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ) (l : Fin 4) (k : Fin 2) :
    cmOf W l k 1 = rA W l k ^ 2 * rB W l k := rfl
theorem cmOf2 (W : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ) (l : Fin 4) (k : Fin 2) :
    cmOf W l k 2 = rA W l k * rB W l k ^ 2 := rfl
theorem cmOf3 (W : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ) (l : Fin 4) (k : Fin 2) :
    cmOf W l k 3 = rB W l k ^ 3 := rfl

theorem C12_eq (W : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) : C12 (cmOf W) k = e12 W k := by
  simp only [C12, e12, cmOf_apply, Fin.sum_univ_four]
  simp; ring

theorem C03_eq (W : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) : C03 (cmOf W) k = e03 W k := by
  simp only [C03, e03, cmOf_apply, Fin.sum_univ_four]
  simp

theorem C50_eq (W : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) : C50 (cmOf W) k = e50 W k := by
  simp only [C50, e50, blk50, sg, tg, etaW, yW, cmOf_apply, Fin.sum_univ_four, Finset.sum_filter]
  simp
  ring

theorem C41_eq (W : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) : C41 (cmOf W) k = e41 W k := by
  simp only [C41, e41, blk41, sg, tg, etaW, yW, etaW', yW', cmOf_apply, Fin.sum_univ_four,
    Finset.sum_filter]
  simp
  ring

/-- **The `s³t²` coefficient from the raw blocks.** -/
theorem errθ_coeff32 (θ : Raw16) (k : Fin 2) :
    (errθ θ k).coeff (stMono 3 2) = C32 (cmOf (rawW θ)) k := by
  have hα : ∀ k', actα (toM2 θ) k' = rA (rawW θ) 0 k' := fun k' => (toM2_rows θ k').1
  have hν : ∀ k', actν (toM2 θ) k' = rB (rawW θ) 0 k' := fun k' => (toM2_rows θ k').2.1
  have ha0 : ∀ k', inA (toM2 θ) k' 0 = rA (rawW θ) 1 k' := fun k' => (toM2_rows θ k').2.2.1
  have ha1 : ∀ k', inA (toM2 θ) k' 1 = rA (rawW θ) 2 k' := fun k' => (toM2_rows θ k').2.2.2.1
  have ha2 : ∀ k', inA (toM2 θ) k' 2 = rA (rawW θ) 3 k' := fun k' => (toM2_rows θ k').2.2.2.2.1
  have hb0 : ∀ k', inB (toM2 θ) k' 0 = rB (rawW θ) 1 k' :=
    fun k' => (toM2_rows θ k').2.2.2.2.2.1
  have hb1 : ∀ k', inB (toM2 θ) k' 1 = rB (rawW θ) 2 k' :=
    fun k' => (toM2_rows θ k').2.2.2.2.2.2.1
  have hb2 : ∀ k', inB (toM2 θ) k' 2 = rB (rawW θ) 3 k' :=
    fun k' => (toM2_rows θ k').2.2.2.2.2.2.2
  unfold errθ
  rw [errP_s32]
  simp only [sum_range_succ, sum_range_zero, zero_add, rowPoly_cube32, cubRow_coeff,
    cubS_coeff12, cubT_coeff12, cubS_coeff21, cubT_coeff21, cubS_coeff, cubT_coeff,
    hα, hν, ha0, ha1, ha2, hb0, hb1, hb2]
  simp only [C32, blk32, sg, tg, cmOf0, cmOf1, cmOf2, cmOf3, Fin.sum_univ_four,
    Finset.sum_filter]
  simp only [Fin.isValue, Fin.reduceLT, Fin.lt_irrefl, ite_true, ite_false, add_zero]
  ring

/-- **The `s⁷` coefficient from the raw blocks.** -/
theorem errθ_coeff70 (θ : Raw16) (k : Fin 2) :
    (errθ θ k).coeff (stMono 7 0) = C70 (cmOf (rawW θ)) k := by
  have hα : ∀ k', actα (toM2 θ) k' = rA (rawW θ) 0 k' := fun k' => (toM2_rows θ k').1
  have hν : ∀ k', actν (toM2 θ) k' = rB (rawW θ) 0 k' := fun k' => (toM2_rows θ k').2.1
  have ha0 : ∀ k', inA (toM2 θ) k' 0 = rA (rawW θ) 1 k' := fun k' => (toM2_rows θ k').2.2.1
  have ha1 : ∀ k', inA (toM2 θ) k' 1 = rA (rawW θ) 2 k' := fun k' => (toM2_rows θ k').2.2.2.1
  have ha2 : ∀ k', inA (toM2 θ) k' 2 = rA (rawW θ) 3 k' := fun k' => (toM2_rows θ k').2.2.2.2.1
  have hb0 : ∀ k', inB (toM2 θ) k' 0 = rB (rawW θ) 1 k' :=
    fun k' => (toM2_rows θ k').2.2.2.2.2.1
  have hb1 : ∀ k', inB (toM2 θ) k' 1 = rB (rawW θ) 2 k' :=
    fun k' => (toM2_rows θ k').2.2.2.2.2.2.1
  have hb2 : ∀ k', inB (toM2 θ) k' 2 = rB (rawW θ) 3 k' :=
    fun k' => (toM2_rows θ k').2.2.2.2.2.2.2
  unfold errθ
  rw [errP_s70]
  simp only [sum_range_succ, sum_range_zero, zero_add, rowPoly_cube70, cubRow_coeff,
    quinS, quinT, coeff_sum, coeff_sub, quinRow_coeff50, cubS_coeff, cubT_coeff,
    hα, ha0, ha1, ha2, hb0, hb1, hb2]
  simp only [C70, sg5, tg5, E5, blk50, sg, tg, cmOf0, cmOf1, cmOf2, Fin.sum_univ_four,
    Finset.sum_filter]
  simp only [Fin.isValue, Fin.reduceLT, Fin.lt_irrefl, ite_true, ite_false, add_zero]
  ring

end VectorSLT.LossCompare
