/-
L2: Theorem H §2's normalization, (H2) and (H3), and the transfer of Proposition L′ to
every rank-one shear target with both rows nonzero.
-/
import VectorSLT.FullNetwork

namespace VectorSLT

open MeasureTheory Set Filter Topology Matrix

/-! ### Real cube root -/

/-- The real (odd) cube root. -/
noncomputable def rcbrt (x : ℝ) : ℝ :=
  if 0 ≤ x then x ^ ((1 : ℝ) / 3) else -((-x) ^ ((1 : ℝ) / 3))

theorem rcbrt_cube (x : ℝ) : rcbrt x ^ 3 = x := by
  unfold rcbrt
  have h3 : (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ := by norm_num
  split_ifs with h
  · rw [h3]; exact Real.rpow_inv_natCast_pow h (by norm_num)
  · rw [neg_pow, h3, Real.rpow_inv_natCast_pow (by linarith) (by norm_num)]; ring

theorem cube_injective {x y : ℝ} (h : x ^ 3 = y ^ 3) : x = y := by
  exact (Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)).injective h

theorem rcbrt_eq_of_cube {x y : ℝ} (h : y ^ 3 = x) : rcbrt x = y :=
  cube_injective (by rw [rcbrt_cube, h])

/-! ### (H2): diagonal conjugation, and the coordinate swap -/

/-- `τ_b` is the identity (`b = false`) or the coordinate swap (`b = true`). -/
def tau (b : Bool) (i : Fin 2) : Fin 2 := if b then Equiv.swap 0 1 i else i

theorem tau_tau (b : Bool) (i : Fin 2) : tau b (tau b i) = i := by
  cases b <;> fin_cases i <;> rfl

/-- Weight action `W ↦ P_τ D^{1/3} W D⁻¹ P_τ⁻¹`: entry `(i,j)` is
`∛(d_{τi}) W_{τi,τj} / d_{τj}`. -/
noncomputable def actW (d : Fin 2 → ℝ) (b : Bool) (W : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => rcbrt (d (tau b i)) / d (tau b j) * W (tau b i) (tau b j)

/-- Input/output change `Φ z = P_τ D z`. -/
def Φs (d : Fin 2 → ℝ) (b : Bool) (z : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => d (tau b i) * z (tau b i)
/-- Its inverse `Ψ = D⁻¹ P_τ⁻¹`. -/
noncomputable def Ψs (d : Fin 2 → ℝ) (b : Bool) (y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => y (tau b i) / d i

theorem Ψs_Φs {d : Fin 2 → ℝ} (hd : ∀ i, d i ≠ 0) (b : Bool) (z : Fin 2 → ℝ) :
    Ψs d b (Φs d b z) = z := by
  funext i; simp only [Ψs, Φs, tau_tau]; field_simp [hd i]

theorem Φs_Ψs {d : Fin 2 → ℝ} (hd : ∀ i, d i ≠ 0) (b : Bool) (y : Fin 2 → ℝ) :
    Φs d b (Ψs d b y) = y := by
  funext i; simp only [Ψs, Φs, tau_tau]; field_simp [hd (tau b i)]

/-- **(H2) with permutation**: `Φ ∘ F_W ∘ Φ⁻¹ = F_{act W}`. -/
theorem layer_conj {d : Fin 2 → ℝ} (hd : ∀ i, d i ≠ 0) (b : Bool)
    (W : Matrix (Fin 2) (Fin 2) ℝ) (z : Fin 2 → ℝ) :
    Φs d b (layer W (Ψs d b z)) = layer (actW d b W) z := by
  funext i
  have key : ∀ r X D : ℝ, r ^ 3 = D → D * X ^ 3 = (r * X) ^ 3 := by
    intro r X D h; rw [mul_pow, h]
  simp only [Φs, layer_apply]
  rw [mul_add, key (rcbrt (d (tau b i))) _ _ (rcbrt_cube _)]
  congr 1
  · simp only [Ψs, tau_tau]; field_simp [hd (tau b i)]
  · congr 1
    cases b <;> fin_cases i <;>
      simp [Ψs, actW, tau, dotProduct, Fin.sum_univ_two, Equiv.swap_apply_def] <;> ring

/-- (H2) for the whole network: `Φ ∘ G_n ∘ Φ⁻¹` is the network with weights `act Wᵢ`. -/
theorem prefixNet_conj {d : Fin 2 → ℝ} (hd : ∀ i, d i ≠ 0) (b : Bool)
    (W : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) (z : Fin 2 → ℝ) :
    Φs d b (prefixNet W n (Ψs d b z)) = prefixNet (fun i => actW d b (W i)) n z := by
  induction n with
  | zero => simp [Φs_Ψs hd]
  | succ n ih =>
    rw [prefixNet_succ, prefixNet_succ, Function.comp_apply, Function.comp_apply, ← ih,
      ← layer_conj hd b, Ψs_Φs hd]

/-! ### (H3): every two-nonzero-row rank-one shear is conjugate to `A₀` -/

/-- A rank-one shear target with both rows nonzero: `A = a vᵀ`, `a₀, a₁ ≠ 0`, `v ≠ 0`,
`vᵀ a^{⊙3} = 0`. -/
def ShearTarget (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ a v : Fin 2 → ℝ, (∀ i j, A i j = a i * v j) ∧ a 0 ≠ 0 ∧ a 1 ≠ 0 ∧ v ≠ 0 ∧
    v 0 * a 0 ^ 3 + v 1 * a 1 ^ 3 = 0

/-- **(H3)**, with the paper's explicit `D = diag(k/a₀³, k/a₁³)`, `k = |β|^{3/2}`,
`β = v₀a₀³`, and a swap iff `β < 0`. -/
theorem shear_normalize {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) :
    ∃ (d : Fin 2 → ℝ) (b : Bool), (∀ i, d i ≠ 0) ∧ actW d b A = A0 := by
  obtain ⟨a, v, hAav, ha0, ha1, hv, hsh⟩ := hA
  set β := v 0 * a 0 ^ 3
  have hβ : β ≠ 0 := by
    intro h0
    have hv0 : v 0 = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h) ha0
    have hv1 : v 1 = 0 := by
      have : v 1 * a 1 ^ 3 = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h) ha1
    exact hv (funext fun i => by fin_cases i <;> simp [hv0, hv1])
  set g := √|β|
  have hg : 0 < g := Real.sqrt_pos.mpr (abs_pos.mpr hβ)
  have hg2 : g ^ 2 = |β| := Real.sq_sqrt (abs_nonneg _)
  set d : Fin 2 → ℝ := fun i => g ^ 3 / a i ^ 3
  have hd : ∀ i, d i ≠ 0 := by
    intro i; fin_cases i <;> simp [d, hg.ne', ha0, ha1]
  have hr : ∀ i, rcbrt (d i) = g / a i := by
    intro i; apply rcbrt_eq_of_cube; simp only [d]; rw [div_pow]
  have hv1 : v 1 * a 1 ^ 3 = -β := by simp only [β]; linarith
  refine ⟨d, decide (β < 0), hd, ?_⟩
  ext i j
  have e : ∀ m n : Fin 2, rcbrt (d m) / d n * A m n = v n * a n ^ 3 / |β| := by
    intro m n
    rw [hr, hAav]
    simp only [d]
    have := (show a m ≠ 0 by fin_cases m <;> assumption)
    have := (show a n ≠ 0 by fin_cases n <;> assumption)
    rw [← hg2]; field_simp
  have hv0 : v 0 * a 0 ^ 3 = β := rfl
  have q1 : β / β = 1 := div_self hβ
  have q2 : -β / β = -1 := by rw [neg_div, q1]
  have q3 : β / -β = -1 := by rw [div_neg, q1]
  have q4 : -β / -β = 1 := by rw [neg_div_neg_eq, q1]
  simp only [actW, Matrix.of_apply, e]
  rcases lt_or_gt_of_ne hβ with hneg | hpos
  · have hdec : decide (β < 0) = true := decide_eq_true hneg
    rw [abs_of_neg hneg, hdec]
    fin_cases i <;> fin_cases j <;> simp only [tau, A0, ite_true, Fin.zero_eta, Fin.mk_one,
      Equiv.swap_apply_left, Equiv.swap_apply_right, hv0, hv1, q3, q4] <;> rfl
  · have hdec : decide (β < 0) = false := decide_eq_false (by linarith)
    rw [abs_of_pos hpos, hdec]
    fin_cases i <;> fin_cases j <;> simp only [tau, A0, Bool.false_eq_true, ite_false,
      Fin.zero_eta, Fin.mk_one, hv0, hv1, q1, q2] <;> rfl

/-! ### The induced linear map on the sixteen raw weights -/

/-- Entry `(i,j)` of all four matrices: `(M_{ij}, ((B₁)_{ij}, (B₂)_{ij}, (B₃)_{ij}))`. -/
def ent (θ : Raw16) (i j : Fin 2) : ℝ × (ℝ × ℝ × ℝ) :=
  (![![θ.1.1.1, θ.1.1.2], ![θ.1.2.1, θ.1.2.2]] i j, ![![θ.2.1.1, θ.2.1.2], ![θ.2.2.1, θ.2.2.2]] i j)

def ofEnt (e : Fin 2 → Fin 2 → ℝ × (ℝ × ℝ × ℝ)) : Raw16 :=
  ((((e 0 0).1, (e 0 1).1), ((e 1 0).1, (e 1 1).1)),
    (((e 0 0).2, (e 0 1).2), ((e 1 0).2, (e 1 1).2)))

theorem ent_ofEnt (e : Fin 2 → Fin 2 → ℝ × (ℝ × ℝ × ℝ)) : ent (ofEnt e) = e := by
  funext i j; fin_cases i <;> fin_cases j <;> rfl

theorem ofEnt_ent (θ : Raw16) : ofEnt (ent θ) = θ := rfl

theorem weights_zero_ent (θ : Raw16) (i j : Fin 2) : weights θ 0 i j = (ent θ i j).1 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem weights_succ_ent (θ : Raw16) (m : ℕ) (i j : Fin 2) :
    weights θ (m + 1) i j = tri (ent θ i j).2 m := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tri_smul (c : ℝ) (v : ℝ × ℝ × ℝ) (m : ℕ) : tri (c • v) m = c * tri v m := by
  rcases m with _ | _ | m <;> rfl

/-- The entry scale `∛(dᵢ)/dⱼ`. -/
noncomputable def sc (d : Fin 2 → ℝ) (i j : Fin 2) : ℝ := rcbrt (d i) / d j

theorem sc_ne {d : Fin 2 → ℝ} (hd : ∀ i, d i ≠ 0) (i j : Fin 2) : sc d i j ≠ 0 := by
  have : rcbrt (d i) ≠ 0 := by
    intro h; apply hd i; rw [← rcbrt_cube (d i), h]; norm_num
  exact div_ne_zero this (hd j)

noncomputable def Tfun (d : Fin 2 → ℝ) (b : Bool) (θ : Raw16) : Raw16 :=
  ofEnt fun i j => sc d (tau b i) (tau b j) • ent θ (tau b i) (tau b j)

noncomputable def Tinv (d : Fin 2 → ℝ) (b : Bool) (θ : Raw16) : Raw16 :=
  ofEnt fun i j => (sc d i j)⁻¹ • ent θ (tau b i) (tau b j)

theorem ent_add (θ θ' : Raw16) (i j : Fin 2) : ent (θ + θ') i j = ent θ i j + ent θ' i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem ent_smul (c : ℝ) (θ : Raw16) (i j : Fin 2) : ent (c • θ) i j = c • ent θ i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem ofEnt_add (e e' : Fin 2 → Fin 2 → ℝ × (ℝ × ℝ × ℝ)) :
    ofEnt (e + e') = ofEnt e + ofEnt e' := rfl

theorem ofEnt_smul (c : ℝ) (e : Fin 2 → Fin 2 → ℝ × (ℝ × ℝ × ℝ)) :
    ofEnt (c • e) = c • ofEnt e := rfl

/-- The raw-parameter map of the symmetry, as a linear equivalence of `ℝ¹⁶`. -/
noncomputable def Tlin {d : Fin 2 → ℝ} (hd : ∀ i, d i ≠ 0) (b : Bool) : Raw16 ≃ₗ[ℝ] Raw16 where
  toFun := Tfun d b
  invFun := Tinv d b
  map_add' x y := by
    simp only [Tfun]; rw [← ofEnt_add]; congr 1; funext i j
    simp only [Pi.add_apply, ent_add, smul_add]
  map_smul' c x := by
    simp only [Tfun, RingHom.id_apply]; rw [← ofEnt_smul]; congr 1; funext i j
    simp only [Pi.smul_apply, ent_smul, smul_comm c]
  left_inv θ := by
    simp only [Tinv, Tfun, ent_ofEnt, tau_tau, smul_smul]
    conv_rhs => rw [← ofEnt_ent θ]
    congr 1; funext i j; rw [inv_mul_cancel₀ (sc_ne hd i j), one_smul]
  right_inv θ := by
    simp only [Tinv, Tfun, ent_ofEnt, tau_tau, smul_smul]
    conv_rhs => rw [← ofEnt_ent θ]
    congr 1; funext i j; rw [mul_inv_cancel₀ (sc_ne hd _ _), one_smul]

theorem weights_Tfun {d : Fin 2 → ℝ} (b : Bool) (θ : Raw16) (k : ℕ) (hk : k < 4) :
    weights (Tfun d b θ) k = actW d b (weights θ k) := by
  ext i j
  rcases k with _ | m
  · rw [weights_zero_ent, Tfun, ent_ofEnt, actW, Matrix.of_apply, weights_zero_ent]; rfl
  · rw [weights_succ_ent, Tfun, ent_ofEnt, actW, Matrix.of_apply, weights_succ_ent]
    exact tri_smul _ _ _

/-- The network transforms by `Φ`: `h_{Tθ} = Φ ∘ h_θ ∘ Φ⁻¹`. -/
theorem net_Tfun {d : Fin 2 → ℝ} (hd : ∀ i, d i ≠ 0) (b : Bool) (θ : Raw16) (z : Fin 2 → ℝ) :
    net (Tfun d b θ) z = Φs d b (net θ (Ψs d b z)) := by
  rw [net, net, prefixNet_conj hd]
  exact congrFun (prefixNet_congr _ _ 4 fun k hk => weights_Tfun b θ k hk) z

/-- The raw base point of a general target: active block `A`, inactive blocks zero. -/
def baseA (A : Matrix (Fin 2) (Fin 2) ℝ) : Raw16 := (((A 0 0, A 0 1), (A 1 0, A 1 1)), 0)

theorem Tfun_baseA {d : Fin 2 → ℝ} {b : Bool} {A : Matrix (Fin 2) (Fin 2) ℝ}
    (h : actW d b A = A0) : Tfun d b (baseA A) = θ₀ := by
  have hent : ∀ i j, sc d (tau b i) (tau b j) • ent (baseA A) (tau b i) (tau b j) =
      (A0 i j, 0) := by
    intro i j
    have hij : ent (baseA A) (tau b i) (tau b j) = (A (tau b i) (tau b j), 0) := by
      generalize tau b i = p; generalize tau b j = q
      fin_cases p <;> fin_cases q <;> rfl
    rw [hij, ← h]
    simp [actW, sc]
  simp only [Tfun, hent]
  simp [ofEnt, θ₀, A0]

/-! ### Transfer of Proposition L′ to every two-nonzero-row shear target -/

instance : BorelSpace (Row × Row) := inferInstance
instance : SecondCountableTopology (Row × Row) := inferInstance
instance : MeasurableAdd₂ (Row × Row) := ⟨continuous_add.measurable⟩
instance : BorelSpace Raw16 := inferInstance
instance : SecondCountableTopology Raw16 := inferInstance
instance : MeasurableAdd₂ Raw16 := ⟨continuous_add.measurable⟩

instance : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _
instance : (volume : Measure (ℝ × ℝ × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _
instance : (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _
instance : (volume : Measure Row).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _
instance : (volume : Measure (Row × Row)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _
instance : (volume : Measure Raw16).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _

/-- Change of variables under a linear automorphism of `ℝ¹⁶`:
`∫ f = |det T|⁻¹ ∫ f ∘ T⁻¹`. -/
theorem lintegral_linearEquiv (T : Raw16 ≃ₗ[ℝ] Raw16) (f : Raw16 → ENNReal) :
    ∫⁻ θ, f θ = ENNReal.ofReal |(LinearMap.det (T : Raw16 →ₗ[ℝ] Raw16))⁻¹| *
      ∫⁻ θ, f (T.symm θ) := by
  set T' := T.toContinuousLinearEquiv
  set e := T'.toHomeomorph.toMeasurableEquiv
  have he : (e : Raw16 → Raw16) = T := rfl
  have hdet : LinearMap.det (T : Raw16 →ₗ[ℝ] Raw16) ≠ 0 := (LinearEquiv.isUnit_det' T).ne_zero
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure Raw16) hdet
  have h1 := lintegral_map_equiv (μ := (volume : Measure Raw16)) (fun θ => f (T.symm θ)) e
  rw [show ((T : Raw16 →ₗ[ℝ] Raw16) : Raw16 → Raw16) = T from rfl] at hmap
  rw [he, hmap, lintegral_smul_measure] at h1
  simp only [LinearEquiv.symm_apply_apply] at h1
  rw [← h1, smul_eq_mul]

/-- **Proposition L′ for every rank-one shear target with both rows nonzero.**
The hypotheses are those of `propLprime`, with target `F_A` and base point `(A, 0, 0, 0)`. -/
theorem propLprime_shear {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A)
    {R Λ π₀ : ℝ} (hπ₀ : 0 < π₀) (K : Raw16 → ℝ)
    (hK : ∀ θ M, 0 ≤ M → (∀ x : Fin 2 → ℝ, (∀ i, |x i| ≤ R) →
      ∀ k, |net θ x k - layer A x k| ≤ M) → K θ ≤ Λ * M ^ 2)
    (π : Raw16 → ENNReal) (hπ : ∀ᶠ θ in 𝓝 (baseA A), ENNReal.ofReal π₀ ≤ π θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ENNReal.ofReal (c * N⁻¹ ^ 4 * Real.log N ^ 4) ≤
        ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * K θ))) * π θ := by
  obtain ⟨d, b, hd, hact⟩ := shear_normalize hA
  set T := Tlin hd b
  have hTf : ∀ θ, T θ = Tfun d b θ := fun _ => rfl
  have hTsymm : ∀ θ, T.symm θ = Tinv d b θ := fun _ => rfl
  -- new input radius and output factor
  set Dm := max |d 0| |d 1|
  set Em := max |(d 0)⁻¹| |(d 1)⁻¹|
  set R' := max 1 (Dm * R)
  have hR' : 1 ≤ R' := le_max_left _ _
  have hdle : ∀ i, |d i| ≤ Dm := fun i => by fin_cases i; exacts [le_max_left _ _, le_max_right _ _]
  have hdinv : ∀ i, |(d i)⁻¹| ≤ Em := fun i => by
    fin_cases i; exacts [le_max_left _ _, le_max_right _ _]
  have hEm : 0 ≤ Em := (abs_nonneg _).trans (hdinv 0)
  -- the transported loss satisfies (G↑) for A₀ on the larger box
  have hK' : ∀ θ' M, 0 ≤ M → (∀ x : Fin 2 → ℝ, (∀ i, |x i| ≤ R') →
      ∀ k, |net θ' x k - layer A0 x k| ≤ M) → K (T.symm θ') ≤ (Λ * Em ^ 2) * M ^ 2 := by
    intro θ' M hM hbd
    set θ := T.symm θ'
    have hθ' : Tfun d b θ = θ' := by rw [← hTf]; exact T.apply_symm_apply θ'
    have := hK θ (Em * M) (mul_nonneg hEm hM) (fun x hx k => ?_)
    · calc K θ ≤ Λ * (Em * M) ^ 2 := this
        _ = Λ * Em ^ 2 * M ^ 2 := by ring
    -- error of θ at x = Ψ (error of θ' at Φ x)
    have hΦx : ∀ i, |Φs d b x i| ≤ R' := by
      intro i
      simp only [Φs, abs_mul]
      calc |d (tau b i)| * |x (tau b i)| ≤ Dm * R :=
            mul_le_mul (hdle _) (hx _) (abs_nonneg _) ((abs_nonneg _).trans (hdle 0))
        _ ≤ R' := le_max_right _ _
    have hnet : net θ' (Φs d b x) = Φs d b (net θ x) := by
      rw [← hθ', net_Tfun hd, Ψs_Φs hd]
    have hlay : layer A0 (Φs d b x) = Φs d b (layer A x) := by
      rw [← hact, ← layer_conj hd, Ψs_Φs hd]
    have e1 : net θ x k - layer A x k =
        (net θ' (Φs d b x) (tau b k) - layer A0 (Φs d b x) (tau b k)) * (d k)⁻¹ := by
      rw [hnet, hlay]; simp only [Φs, tau_tau]; field_simp [hd k]
    rw [e1, abs_mul]
    rw [mul_comm Em M]
    exact mul_le_mul (hbd _ hΦx _) (hdinv k) (abs_nonneg _) hM
  -- the transported prior is bounded below near θ₀
  have hbase : T.symm θ₀ = baseA A := by
    rw [← Tfun_baseA hact, ← hTf]; exact T.symm_apply_apply _
  have hcont : Continuous (T.symm : Raw16 → Raw16) :=
    T.symm.toContinuousLinearEquiv.continuous
  have hπ' : ∀ᶠ θ' in 𝓝 θ₀, ENNReal.ofReal π₀ ≤ π (T.symm θ') := by
    have ht : Tendsto (T.symm : Raw16 → Raw16) (𝓝 θ₀) (𝓝 (baseA A)) := by
      rw [← hbase]; exact hcont.tendsto θ₀
    exact ht.eventually hπ
  obtain ⟨c', hc', N₀, hmain⟩ :=
    propLprime hR' hπ₀ (fun θ' => K (T.symm θ')) hK' (fun θ' => π (T.symm θ')) hπ'
  set J := |(LinearMap.det (T : Raw16 →ₗ[ℝ] Raw16))⁻¹|
  have hJ : 0 < J := by
    have : LinearMap.det (T : Raw16 →ₗ[ℝ] Raw16) ≠ 0 := (LinearEquiv.isUnit_det' T).ne_zero
    exact abs_pos.mpr (inv_ne_zero this)
  refine ⟨J * c', mul_pos hJ hc', N₀, fun N hN => ?_⟩
  rw [lintegral_linearEquiv T]
  calc ENNReal.ofReal (J * c' * N⁻¹ ^ 4 * Real.log N ^ 4)
      = ENNReal.ofReal J * ENNReal.ofReal (c' * N⁻¹ ^ 4 * Real.log N ^ 4) := by
        rw [← ENNReal.ofReal_mul hJ.le]; ring_nf
    _ ≤ _ := by gcongr; exact hmain N hN

end VectorSLT
