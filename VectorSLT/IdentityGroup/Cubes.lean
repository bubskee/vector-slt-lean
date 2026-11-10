import VectorSLT.IdentityGroup.Cubes.Scaling
import VectorSLT.IdentityGroup.Cubes.One
import VectorSLT.IdentityGroup.Cubes.Two
import VectorSLT.IdentityGroup.Cubes.Chart
import VectorSLT.IdentityGroup.Cubes.Three
import VectorSLT.IdentityGroup.Cubes.Lower

/-!
# Lemma A-cubes (paper 2, Appendix A.1): the interface `CubeSumUpper k` for `k = 1, 2, 3`

Headline results, with no hypotheses:

* `VectorSLT.IdentityGroup.cubeSumUpper_one : CubeSumUpper 1`
* `VectorSLT.IdentityGroup.cubeSumUpper_two : CubeSumUpper 2`
* `VectorSLT.IdentityGroup.cubeSumUpper_three : CubeSumUpper 3`
* `VectorSLT.IdentityGroup.cubeSumLower k` : the matching lower bound, for every `k`.

Files:

* `Cubes/Scaling.lean`: homogeneity; `CubeSumUpper k` follows from `∫ e^{-G_k} < ∞`.
* `Cubes/One.lean`, `Cubes/Two.lean`: `k = 1, 2` by Gaussian bounds.
* `Cubes/Chart.lean`: symmetry, radial integration and shear, for any number of forms.
* `Cubes/Three.lean`: the chart estimate for three forms.
* `Cubes/Lower.lean`: the lower bound.

See `VectorSLT/IdentityGroup/NOTES_cubes.md` for the correspondence with the paper.
-/

namespace VectorSLT.IdentityGroup

/-- **Lemma A-cubes, upper half, `k = 1`.** -/
theorem cubeSumUpper_one : CubeSumUpper 1 := Cubes.cubeSumUpper_one

/-- **Lemma A-cubes, upper half, `k = 2`.** -/
theorem cubeSumUpper_two : CubeSumUpper 2 := Cubes.cubeSumUpper_two

/-- **Lemma A-cubes, upper half, `k = 3`.** -/
theorem cubeSumUpper_three : CubeSumUpper 3 := Cubes.cubeSumUpper_three

/-- **Lemma A-cubes, lower half, every `k`.** -/
theorem cubeSumLower (k : ℕ) : Cubes.CubeSumLower k := Cubes.cubeSumLower_all k

end VectorSLT.IdentityGroup
