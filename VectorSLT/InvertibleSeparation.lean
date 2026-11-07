/-
Brief 03, O5, Candidate 2 (`formalization_candidates.md`; `results.md` §4.2): cubic/quintic
separation through an invertible active block.

For `A ∈ GL₂(ℝ)` the map
`(Δ, S₋, T₋, S₊, T₊) ↦ 3(Ax)^{⊙2} ⊙ Δx + DF_A(S₋ + T₋) + (S₊ + T₊) ∘ F_A`
has trivial kernel (`sepMap_kernel`), hence is injective (`sepMap_injective`).

Function-level form: `S±` range over *continuous* maps homogeneous of degree 3 and `T±` over
continuous maps homogeneous of degree 5. This contains the paper's `H₃²`, `H₅²` (homogeneous
polynomial maps), so it is the paper's injectivity, in a slightly more general class.
The proof follows the paper's degree order 15, 9, 7, 5, 3, extracting each top degree by the
scaling `x ↦ r x`, `r → ∞` (`u = r⁻² → 0⁺`) instead of polynomial grading:
* degree 15: `T₊ ∘ V_A = 0`, and `V_A` is surjective, so `T₊ = 0`;
* degree 9: `S₊ ∘ V_A = 0`, so `S₊ = 0`;
* degree 7: `DV_A T₋ = 0`; `DV_A(x)` is invertible where `(Ax)₀(Ax)₁ ≠ 0`, a dense set;
* degree 5: `T₋ + DV_A S₋ = 0`, so `DV_A S₋ = 0`, so `S₋ = 0`;
* degree 3: `L_A(Δ) + S₋ = 0`, so `L_A(Δ) = 0`, so `Δ = 0`.
The paper's subsequent norm lower bound (positive smallest singular value of this fixed linear
map on the 44-dimensional space) is not formalized here.
-/
import VectorSLT.InverseCriterion

namespace VectorSLT

open Matrix Filter Topology

/-- Continuous and positively-and-negatively homogeneous of degree `d`. -/
def HomDeg (d : ℕ) (S : (Fin 2 → ℝ) → (Fin 2 → ℝ)) : Prop :=
  Continuous S ∧ ∀ (r : ℝ) (z : Fin 2 → ℝ), S (r • z) = r ^ d • S z

/-- `L_A(Δ)(x) = 3 (Ax)^{⊙2} ⊙ Δx`. -/
def Lmap (A Δ : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun k => 3 * (A *ᵥ x) k ^ 2 * (Δ *ᵥ x) k

/-- The separation map of `results.md` (11). `DF_A(x) h = h + DV_A(x) h`. -/
def sepMap (A Δ : Matrix (Fin 2) (Fin 2) ℝ) (Sm Tm Sp Tp : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  Lmap A Δ x + (Sm x + Tm x) + DVmap A x (Sm x + Tm x) + Sp (layer A x) + Tp (layer A x)

variable {A : Matrix (Fin 2) (Fin 2) ℝ}

theorem isUnit_of_det (hA : A.det ≠ 0) : IsUnit A.det := isUnit_iff_ne_zero.mpr hA

theorem mulVec_inj_of_det (hA : A.det ≠ 0) {h : Fin 2 → ℝ} (h0 : A *ᵥ h = 0) : h = 0 := by
  calc h = (A⁻¹ * A) *ᵥ h := by rw [Matrix.nonsing_inv_mul _ (isUnit_of_det hA), one_mulVec]
    _ = A⁻¹ *ᵥ (A *ᵥ h) := (mulVec_mulVec _ _ _).symm
    _ = 0 := by rw [h0, mulVec_zero]

/-- `V_A` is surjective for invertible `A`. -/
theorem Vmap_surj (hA : A.det ≠ 0) (y : Fin 2 → ℝ) : ∃ x, Vmap A x = y := by
  refine ⟨A⁻¹ *ᵥ fun i => rcbrt (y i), ?_⟩
  rw [Vmap, mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_of_det hA), one_mulVec]
  funext i; simp [rcbrt_cube]

/-- Vanishing of a continuous map off the two lines `(Ax)₀ = 0`, `(Ax)₁ = 0` forces vanishing. -/
theorem vanish_of_dense (hA : A.det ≠ 0) {f : (Fin 2 → ℝ) → (Fin 2 → ℝ)} (hf : Continuous f)
    (h : ∀ x, (A *ᵥ x) 0 ≠ 0 → (A *ᵥ x) 1 ≠ 0 → f x = 0) : f = 0 := by
  funext x
  set w := A⁻¹ *ᵥ fun _ => (1 : ℝ)
  have hw : A *ᵥ w = fun _ => 1 := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_of_det hA), one_mulVec]
  have hlin : ∀ (t : ℝ) (k : Fin 2), (A *ᵥ (x + t • w)) k = (A *ᵥ x) k + t := by
    intro t k; rw [mulVec_add, mulVec_smul, hw]; simp
  have hline : Continuous fun t : ℝ => f (x + t • w) := hf.comp (by fun_prop)
  have hk : ∀ k, ∀ᶠ t in 𝓝[≠] (0 : ℝ), (A *ᵥ x) k + t ≠ 0 := by
    intro k
    by_cases h0 : (A *ᵥ x) k = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [h0, zero_add]; exact ht
    · have hc : Continuous fun t : ℝ => (A *ᵥ x) k + t := by fun_prop
      have := hc.continuousAt.eventually_ne (x := (0 : ℝ)) (by simpa using h0)
      exact this.filter_mono nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), f (x + t • w) = 0 := by
    filter_upwards [hk 0, hk 1] with t h0 h1
    exact h _ (by rw [hlin]; exact h0) (by rw [hlin]; exact h1)
  have ht := (hline.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have := tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm))
  simpa using this

theorem DV_inj (hA : A.det ≠ 0) {x h : Fin 2 → ℝ} (h0 : (A *ᵥ x) 0 ≠ 0)
    (h1 : (A *ᵥ x) 1 ≠ 0) (hD : DVmap A x h = 0) : h = 0 := by
  apply mulVec_inj_of_det hA
  funext k
  have e := congrFun hD k
  simp only [DVmap, Pi.zero_apply, mul_eq_zero, OfNat.ofNat_ne_zero, false_or,
    pow_eq_zero_iff (two_ne_zero)] at e
  fin_cases k
  · exact e.resolve_left h0
  · exact e.resolve_left h1

/-- The limit `u → 0⁺`. -/
theorem zero_of_pos {g : ℝ → (Fin 2 → ℝ)} (hg : Continuous g) (h : ∀ u > 0, g u = 0) :
    g 0 = 0 := by
  have ht : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : g =ᶠ[𝓝[>] 0] fun _ => 0 := eventually_nhdsWithin_of_forall fun u hu => h u hu
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' hev.symm)

/-- Every `u > 0` is `r⁻²` for some `r ≠ 0`. -/
theorem exists_r (u : ℝ) (hu : 0 < u) : ∃ r : ℝ, r ≠ 0 ∧ (r⁻¹) ^ 2 = u :=
  ⟨(√u)⁻¹, inv_ne_zero (Real.sqrt_pos.mpr hu).ne', by rw [inv_inv, Real.sq_sqrt hu.le]⟩

/-- **The scaling expansion.** For `r ≠ 0`, with `W = V_A(x) + r⁻² x`,
`Φ(r x) = r³ a + r⁵ b + r⁷ c + r⁹ S₊(W) + r¹⁵ T₊(W)`. -/
theorem sep_scale {Δ : Matrix (Fin 2) (Fin 2) ℝ} {Sm Tm Sp Tp : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (hSm : HomDeg 3 Sm) (hTm : HomDeg 5 Tm) (hSp : HomDeg 3 Sp) (hTp : HomDeg 5 Tp)
    (x : Fin 2 → ℝ) {r : ℝ} (hr : r ≠ 0) :
    sepMap A Δ Sm Tm Sp Tp (r • x) =
      r ^ 3 • (Lmap A Δ x + Sm x) + r ^ 5 • (Tm x + DVmap A x (Sm x)) +
        r ^ 7 • DVmap A x (Tm x) + r ^ 9 • Sp (Vmap A x + (r⁻¹) ^ 2 • x) +
          r ^ 15 • Tp (Vmap A x + (r⁻¹) ^ 2 • x) := by
  have hF : layer A (r • x) = r ^ 3 • (Vmap A x + (r⁻¹) ^ 2 • x) := by
    funext k
    simp only [layer, Vmap, mulVec_smul, Pi.add_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [sepMap, hF, hSp.2, hTp.2, hSm.2, hTm.2]
  funext k
  simp only [Lmap, DVmap, mulVec_smul, mulVec_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Candidate 2: trivial kernel.** -/
theorem sepMap_kernel (hA : A.det ≠ 0) {Δ : Matrix (Fin 2) (Fin 2) ℝ}
    {Sm Tm Sp Tp : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (hSm : HomDeg 3 Sm) (hTm : HomDeg 5 Tm) (hSp : HomDeg 3 Sp) (hTp : HomDeg 5 Tp)
    (h : ∀ x, sepMap A Δ Sm Tm Sp Tp x = 0) :
    Δ = 0 ∧ Sm = 0 ∧ Tm = 0 ∧ Sp = 0 ∧ Tp = 0 := by
  have cSm := hSm.1; have cTm := hTm.1; have cSp := hSp.1; have cTp := hTp.1
  -- shorthand
  set a : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun x => Lmap A Δ x + Sm x
  set b : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun x => Tm x + DVmap A x (Sm x)
  set c : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun x => DVmap A x (Tm x)
  have hsc := fun x {r : ℝ} (hr : r ≠ 0) => sep_scale (A := A) (Δ := Δ) hSm hTm hSp hTp x hr
  -- degree 15
  have hTp0 : Tp = 0 := by
    funext y
    obtain ⟨x, rfl⟩ := Vmap_surj hA y
    set g : ℝ → (Fin 2 → ℝ) := fun u => u ^ 6 • a x + u ^ 5 • b x + u ^ 4 • c x +
      u ^ 3 • Sp (Vmap A x + u • x) + Tp (Vmap A x + u • x)
    have hg : Continuous g := by simp only [g]; fun_prop
    have hpos : ∀ u > 0, g u = 0 := by
      intro u hu
      obtain ⟨r, hr, rfl⟩ := exists_r u hu
      have e := hsc x hr
      rw [h] at e
      have e2 : r ^ 15 • g ((r⁻¹) ^ 2) = 0 := by
        rw [e]; funext k
        simp only [g, a, b, c, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
      exact (smul_eq_zero.mp e2).resolve_left (pow_ne_zero _ hr)
    have := zero_of_pos hg hpos
    simpa [g] using this
  -- degree 9
  have hSp0 : Sp = 0 := by
    funext y
    obtain ⟨x, rfl⟩ := Vmap_surj hA y
    set g : ℝ → (Fin 2 → ℝ) := fun u => u ^ 3 • a x + u ^ 2 • b x + u • c x +
      Sp (Vmap A x + u • x)
    have hg : Continuous g := by simp only [g]; fun_prop
    have hpos : ∀ u > 0, g u = 0 := by
      intro u hu
      obtain ⟨r, hr, rfl⟩ := exists_r u hu
      have e := hsc x hr
      rw [h, hTp0] at e
      have e2 : r ^ 9 • g ((r⁻¹) ^ 2) = 0 := by
        rw [e]; funext k
        simp only [g, a, b, c, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        field_simp
        try ring
      exact (smul_eq_zero.mp e2).resolve_left (pow_ne_zero _ hr)
    have := zero_of_pos hg hpos
    simpa [g] using this
  -- the remaining polynomial identity `r³ a + r⁵ b + r⁷ c = 0`
  have hpoly : ∀ x, ∀ r : ℝ, r ≠ 0 → r ^ 3 • a x + r ^ 5 • b x + r ^ 7 • c x = 0 := by
    intro x r hr
    have e := hsc x hr
    rw [h, hTp0, hSp0] at e
    rw [e]; funext k; simp [a, b, c]
  -- degree 7
  have hc0 : ∀ x, c x = 0 := by
    intro x
    set g : ℝ → (Fin 2 → ℝ) := fun u => u ^ 2 • a x + u • b x + c x
    have hg : Continuous g := by simp only [g]; fun_prop
    have hpos : ∀ u > 0, g u = 0 := by
      intro u hu
      obtain ⟨r, hr, rfl⟩ := exists_r u hu
      have e2 : r ^ 7 • g ((r⁻¹) ^ 2) = 0 := by
        rw [← hpoly x r hr]; funext k
        simp only [g, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
      exact (smul_eq_zero.mp e2).resolve_left (pow_ne_zero _ hr)
    simpa [g] using zero_of_pos hg hpos
  -- degree 5
  have hb0 : ∀ x, b x = 0 := by
    intro x
    set g : ℝ → (Fin 2 → ℝ) := fun u => u • a x + b x
    have hg : Continuous g := by simp only [g]; fun_prop
    have hpos : ∀ u > 0, g u = 0 := by
      intro u hu
      obtain ⟨r, hr, rfl⟩ := exists_r u hu
      have e2 : r ^ 5 • g ((r⁻¹) ^ 2) = 0 := by
        rw [← hpoly x r hr, hc0 x]; funext k
        simp only [g, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        field_simp
        try ring
      exact (smul_eq_zero.mp e2).resolve_left (pow_ne_zero _ hr)
    simpa [g] using zero_of_pos hg hpos
  -- degree 3
  have ha0 : ∀ x, a x = 0 := by
    intro x
    have := hpoly x 1 one_ne_zero
    rw [hb0 x, hc0 x] at this
    simpa using this
  -- the algebra
  have hTm0 : Tm = 0 := vanish_of_dense hA cTm fun x h0 h1 => DV_inj hA h0 h1 (hc0 x)
  have hSm0 : Sm = 0 := by
    refine vanish_of_dense hA cSm fun x h0 h1 => DV_inj hA h0 h1 ?_
    have := hb0 x
    simp only [b, hTm0, Pi.zero_apply, zero_add] at this
    exact this
  have hΔ : Δ = 0 := by
    have hv : (fun x => Δ *ᵥ x) = 0 := by
      refine vanish_of_dense hA (by fun_prop) fun x h0 h1 => ?_
      have hL := ha0 x
      simp only [a, hSm0, Pi.zero_apply, add_zero] at hL
      funext k
      have e := congrFun hL k
      simp only [Lmap, Pi.zero_apply, mul_eq_zero, OfNat.ofNat_ne_zero, false_or,
        pow_eq_zero_iff two_ne_zero] at e
      fin_cases k
      · exact e.resolve_left h0
      · exact e.resolve_left h1
    ext i j
    have := congrFun (congrFun hv (Pi.single j 1)) i
    simpa [mulVec_single] using this
  exact ⟨hΔ, hSm0, hTm0, hSp0, hTp0⟩

theorem HomDeg.sub {d : ℕ} {S S' : (Fin 2 → ℝ) → (Fin 2 → ℝ)} (h : HomDeg d S)
    (h' : HomDeg d S') : HomDeg d (S - S') :=
  ⟨h.1.sub h'.1, fun r z => by simp [h.2, h'.2, smul_sub]⟩

theorem sepMap_sub (A Δ Δ' : Matrix (Fin 2) (Fin 2) ℝ)
    (Sm Tm Sp Tp Sm' Tm' Sp' Tp' : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (x : Fin 2 → ℝ) :
    sepMap A Δ Sm Tm Sp Tp x - sepMap A Δ' Sm' Tm' Sp' Tp' x =
      sepMap A (Δ - Δ') (Sm - Sm') (Tm - Tm') (Sp - Sp') (Tp - Tp') x := by
  funext k
  simp only [sepMap, Lmap, DVmap, Pi.add_apply, Pi.sub_apply, sub_mulVec, mulVec_add,
    mulVec_sub]
  ring

/-- **Candidate 2: injectivity** of the separation map on
`Mat₂ ⊕ (deg-3) ⊕ (deg-5) ⊕ (deg-3) ⊕ (deg-5)`, for invertible `A`. -/
theorem sepMap_injective (hA : A.det ≠ 0) {Δ Δ' : Matrix (Fin 2) (Fin 2) ℝ}
    {Sm Tm Sp Tp Sm' Tm' Sp' Tp' : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (hSm : HomDeg 3 Sm) (hTm : HomDeg 5 Tm) (hSp : HomDeg 3 Sp) (hTp : HomDeg 5 Tp)
    (hSm' : HomDeg 3 Sm') (hTm' : HomDeg 5 Tm') (hSp' : HomDeg 3 Sp') (hTp' : HomDeg 5 Tp')
    (h : ∀ x, sepMap A Δ Sm Tm Sp Tp x = sepMap A Δ' Sm' Tm' Sp' Tp' x) :
    Δ = Δ' ∧ Sm = Sm' ∧ Tm = Tm' ∧ Sp = Sp' ∧ Tp = Tp' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sepMap_kernel hA (hSm.sub hSm') (hTm.sub hTm') (hSp.sub hSp')
    (hTp.sub hTp') fun x => by rw [← sepMap_sub, h x, sub_self]
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2, sub_eq_zero.mp h3, sub_eq_zero.mp h4,
    sub_eq_zero.mp h5⟩

end VectorSLT
