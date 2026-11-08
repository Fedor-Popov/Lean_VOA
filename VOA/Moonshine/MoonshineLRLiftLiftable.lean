import VOA.Moonshine.MoonshineCNMonsterActionLift
import VOA.Moonshine.MoonshineLRGriessTransfer
import VOA.Moonshine.MoonshineLRLiftWBlock

/-!
# Rationality criteria for the chosen lattice lifts

The untwisted block is already rational. Thus rationality of the normalized
charge action in the spin dictionary suffices for liftability in `MonsterAction`.
All criteria concern the existing choice of `liftTwVnatAut`.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen
open VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterAction
open VOA.Moonshine.MonsterGriess.Spin
open VOA.Moonshine.InvForm
open Extraspecial
open scoped TensorProduct Matrix

variable (ι : leech.carrier →ₗ[ℤ] leech.carrier)
  (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)

/-- Rationality of the chosen normalized twisted lift in the full spin dictionary. -/
def liftLiftableSpinRational : Prop :=
  ∀ N : SpaceW, ∃ N' : SpaceW,
    liftTwNormalizedPlusEquiv ι hι (liftWScalar ι hι) (spinDict N) = spinDict N'

/-- The untwisted rational formula, expressed directly through `griessNat`. -/
theorem liftLiftableUntwisted (hsurj : Function.Surjective ι) (A : symMat) (x : SpaceX) :
    liftTwVnatAut ι hι hsurj (griessNat (A, x, 0) : Vnat) =
      griessNat (liftBlockSymMat ι A, griessTrX (liftSignX ι hι (griessTrX x)), 0) := by
  simpa only [griessIso_tmul] using griessTrLiftSignNat_untwisted ι hι hsurj A x

/-- Combine a specified rational spin action with the known untwisted action. -/
theorem liftLiftableGriessNat (hsurj : Function.Surjective ι)
    (W : SpaceW → SpaceW)
    (hW : ∀ N, liftTwNormalizedPlusEquiv ι hι (liftWScalar ι hι) (spinDict N) =
      spinDict (W N)) (u : SpaceB) :
    liftTwVnatAut ι hι hsurj (griessNat u : Vnat) =
      griessNat (liftBlockSymMat ι u.1,
        griessTrX (liftSignX ι hι (griessTrX u.2.1)), W u.2.2) := by
  have hU := congrArg Prod.fst (liftLiftableUntwisted ι hι hsurj u.1 u.2.1)
  rw [griessNat_coe, griessNat_coe, liftTwVnatAut_apply] at hU ⊢
  exact Prod.ext hU (hW u.2.2)

/-- Stage 1: rationality of the spin block suffices for a liftable Monster element. -/
theorem liftLiftableOfSpinRational (hsurj : Function.Surjective ι)
    (hW : liftLiftableSpinRational ι hι) :
    ∃ g : liftableSubgroup, monsterLift g = liftTwVnatAut ι hι hsurj := by
  classical
  exact isVnatLiftable_of_rational _ fun u =>
    ⟨_, liftLiftableGriessNat ι hι hsurj (fun N => (hW N).choose)
      (fun N => (hW N).choose_spec) u⟩

/-- The rational spin condition is also necessary for these block-preserving lifts. -/
theorem liftLiftableIffSpinRational (hsurj : Function.Surjective ι) :
    (∃ g : liftableSubgroup, monsterLift g = liftTwVnatAut ι hι hsurj) ↔
      liftLiftableSpinRational ι hι := by
  constructor
  · rintro ⟨g, hg⟩ N
    refine ⟨(((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) (spinBlock N)).2.2, ?_⟩
    have h := monsterLift_apply_griessNat g (spinBlock N)
    rw [hg, griessNat_coe, griessNat_coe, liftTwVnatAut_apply] at h
    exact congrArg Prod.snd h
  · exact liftLiftableOfSpinRational ι hι hsurj

/-- The oscillator action in Conway coordinates is the existing rational lattice matrix. -/
theorem liftLiftableOscillator (j : Fin 24) :
    oscMatrix leech leech ι *ᵥ conwayVec j =
      ∑ i, axiomToConway (liftBlockMatrix ι) i j • conwayVec i := by
  funext a
  have h := congrFun (congrFun (liftBlockMatrix_frame ι) a) j
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, conwayFrame,
    Matrix.of_apply, conwayVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_comm] using h.symm

/-- A matrix description of the chosen normalized charge action, on one top state. -/
theorem liftLiftableSpinTopState (R : Matrix SpinIdx SpinIdx ℂ)
    (hR : ∀ s : SpinRep, (liftWScalar ι hι : ℂ) • liftWSpinCharge ι hι s = R *ᵥ s)
    (v : Fin (rank leech) → ℂ) (s : SpinRep) :
    liftTwNormalizedPlusEquiv ι hι (liftWScalar ι hι) (spinTopState v s) =
      spinTopState (oscMatrix leech leech ι *ᵥ v) (R *ᵥ s) := by
  rw [spinTopState_apply, liftWNormalized_hP, ← liftWSpinCharge_spec,
    ← spinIso_smul, hR, spinTopState_apply]

/-- On complex spin matrices the action is `N ↦ R N Qᵀ`. -/
theorem liftLiftableSpinTopVec (R : Matrix SpinIdx SpinIdx ℂ)
    (hR : ∀ s : SpinRep, (liftWScalar ι hι : ℂ) • liftWSpinCharge ι hι s = R *ᵥ s)
    (N : Matrix SpinIdx (Fin 24) ℂ) :
    liftTwNormalizedPlusEquiv ι hι (liftWScalar ι hι) (spinTopVec N) =
      spinTopVec (R * N * (axiomToConway (liftBlockMatrix ι))ᵀ) := by
  rw [spinTopVec_apply, map_sum]
  calc
    _ = ∑ j, spinTopState
        (∑ i, axiomToConway (liftBlockMatrix ι) i j • conwayVec i)
        (fun s => (R * N) s j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [liftLiftableSpinTopState ι hι R hR, liftLiftableOscillator]
      rfl
    _ = _ := sum_spinTopState_recombine _ _

/-- Rational normalized charge coordinates give an explicit rational `W`-block formula. -/
theorem liftLiftableSpinDict (R : Matrix SpinIdx SpinIdx ℚ)
    (hR : ∀ s : SpinRep, (liftWScalar ι hι : ℂ) • liftWSpinCharge ι hι s =
      R.map (Rat.castHom ℂ) *ᵥ s) (N : SpaceW) :
    liftTwNormalizedPlusEquiv ι hι (liftWScalar ι hι) (spinDict N) =
      spinDict (R * N * (liftBlockMatrix ι)ᵀ) := by
  rw [spinDict_apply, map_smul, liftLiftableSpinTopVec ι hι _ hR, spinDict_apply,
    spinToConway_mul_right, spinToConway_mul_left, axiomToConway_transpose]

/-- A rational matrix for the chosen normalized charge action suffices for liftability. -/
theorem liftLiftableOfChargeMatrix (hsurj : Function.Surjective ι)
    (R : Matrix SpinIdx SpinIdx ℚ)
    (hR : ∀ s : SpinRep, (liftWScalar ι hι : ℂ) • liftWSpinCharge ι hι s =
      R.map (Rat.castHom ℂ) *ᵥ s) :
    ∃ g : liftableSubgroup, monsterLift g = liftTwVnatAut ι hι hsurj ∧
      ∀ u : SpaceB, ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) u =
        (liftBlockSymMat ι u.1, griessTrX (liftSignX ι hι (griessTrX u.2.1)),
          R * u.2.2 * (liftBlockMatrix ι)ᵀ) := by
  have hW := liftLiftableSpinDict ι hι R hR
  obtain ⟨g, hg⟩ := liftLiftableOfSpinRational ι hι hsurj (fun N => ⟨_, hW N⟩)
  refine ⟨g, hg, fun u => griessNat_coe_injective ?_⟩
  rw [← monsterLift_apply_griessNat, hg]
  exact liftLiftableGriessNat ι hι hsurj _ hW u

/-- Orthogonal matrices preserve the bilinear dot product. -/
theorem liftLiftableOrthogonalDot {n : Type*} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℂ) (hR : Rᵀ * R = 1) (s t : n → ℂ) :
    (R *ᵥ s) ⬝ᵥ (R *ᵥ t) = s ⬝ᵥ t := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
    hR, Matrix.one_mulVec]

/-- The chosen form normalization makes the charge action orthogonal in spin coordinates. -/
theorem liftLiftableChargeDot (s t : SpinRep) :
    ((liftWScalar ι hι : ℂ) • liftWSpinCharge ι hι s) ⬝ᵥ
        ((liftWScalar ι hι : ℂ) • liftWSpinCharge ι hι t) = s ⬝ᵥ t := by
  have hstate (v : Fin (rank leech) → ℂ) (w : SpinRep) :
      liftTwNormalizedPlusEquiv ι hι (liftWScalar ι hι) (spinTopState v w) =
        spinTopState (oscMatrix leech leech ι *ᵥ v)
          ((liftWScalar ι hι : ℂ) • liftWSpinCharge ι hι w) := by
    rw [spinTopState_apply, liftWNormalized_hP, spinTopState_apply,
      spinIso_smul, liftWSpinCharge_spec]
  have h := (liftTwExists_formScalar ι hι).choose_spec
    (spinTopState (conwayVec 0) s) (spinTopState (conwayVec 0) t)
  change TPForm (liftTwNormalizedPlusEquiv ι hι (liftWScalar ι hι) _)
    (liftTwNormalizedPlusEquiv ι hι (liftWScalar ι hι) _) = _ at h
  rw [hstate, hstate, TPForm_spinTopState, TPForm_spinTopState] at h
  have hQ := liftLiftableOrthogonalDot (oscMatrix leech leech ι)
    (oscMatrix_transpose_mul leech leech leech_posDef leech_posDef ι hι)
    (conwayVec 0) (conwayVec 0)
  change (∑ a, (oscMatrix leech leech ι *ᵥ conwayVec 0) a *
    (oscMatrix leech leech ι *ᵥ conwayVec 0) a) =
      ∑ a, conwayVec 0 a * conwayVec 0 a at hQ
  rw [hQ, sum_conwayVec_mul, if_pos rfl] at h
  exact mul_left_cancel₀ spinFormScale_ne_zero
    (mul_right_cancel₀ (by norm_num : -(1 / 2 : ℂ) * 8 ≠ 0) h)

/-- A projectively orthogonal rational charge operator has only a sign ambiguity after
the already chosen form normalization. This does not choose a new VOA lift. -/
theorem liftLiftableChargeSign (R : Matrix SpinIdx SpinIdx ℚ) (horth : Rᵀ * R = 1)
    (z : ℂ) (hz : ∀ s : SpinRep,
      liftWSpinCharge ι hι s = z • (R.map (Rat.castHom ℂ) *ᵥ s)) :
    ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧
      ∀ s : SpinRep, (liftWScalar ι hι : ℂ) • liftWSpinCharge ι hι s =
        (ε • R).map (Rat.castHom ℂ) *ᵥ s := by
  classical
  have horthC : (R.map (Rat.castHom ℂ))ᵀ * R.map (Rat.castHom ℂ) = 1 := by
    have h := congrArg (fun M => M.map (Rat.castHom ℂ)) horth
    dsimp only at h
    rw [Matrix.map_mul (f := Rat.castHom ℂ)] at h
    simpa using h
  let e : SpinRep := Pi.single spinIdxBase 1
  have he : e ⬝ᵥ e = 1 := by simp [e]
  have hn (s : SpinRep) : (liftWScalar ι hι : ℂ) • liftWSpinCharge ι hι s =
      ((liftWScalar ι hι : ℂ) * z) • (R.map (Rat.castHom ℂ) *ᵥ s) := by
    rw [hz]
    funext i
    exact (mul_assoc _ _ _).symm
  have h := liftLiftableChargeDot ι hι e e
  rw [hn, smul_dotProduct, dotProduct_smul,
    liftLiftableOrthogonalDot _ horthC, he] at h
  have hsign : ((liftWScalar ι hι : ℂ) * z) * ((liftWScalar ι hι : ℂ) * z) = 1 := by
    simpa only [smul_eq_mul, mul_one] using h
  have hex : ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧
      (ε : ℂ) = (liftWScalar ι hι : ℂ) * z := by
    rcases mul_self_eq_one_iff.mp hsign with hpos | hneg
    · exact ⟨1, Or.inl rfl, by simpa only [Rat.cast_one] using hpos.symm⟩
    · exact ⟨-1, Or.inr rfl, by simpa only [Rat.cast_neg, Rat.cast_one] using hneg.symm⟩
  obtain ⟨ε, hε, hcast⟩ := hex
  refine ⟨ε, hε, fun s => ?_⟩
  rw [hn, ← hcast]
  have hmap : (ε • R).map (Rat.castHom ℂ) = (ε : ℂ) • R.map (Rat.castHom ℂ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Rat.coe_castHom, smul_eq_mul,
      Rat.cast_mul]
  rw [hmap, Matrix.smul_mulVec]

/-- A rational orthogonal representative of the projective charge intertwiner suffices. -/
theorem liftLiftableOfProjectiveCharge (hsurj : Function.Surjective ι)
    (R : Matrix SpinIdx SpinIdx ℚ) (horth : Rᵀ * R = 1)
    (hproj : ∃ z : ℂ, ∀ s : SpinRep,
      liftWSpinCharge ι hι s = z • (R.map (Rat.castHom ℂ) *ᵥ s)) :
    ∃ g : liftableSubgroup, monsterLift g = liftTwVnatAut ι hι hsurj := by
  obtain ⟨z, hz⟩ := hproj
  obtain ⟨ε, _, hε⟩ := liftLiftableChargeSign ι hι R horth z hz
  obtain ⟨g, hg, _⟩ := liftLiftableOfChargeMatrix ι hι hsurj (ε • R) hε
  exact ⟨g, hg⟩

/-- Commuting with the lattice charge operators forces a spin endomorphism to be scalar. -/
theorem liftLiftableSpinCommuteScalar (F : Module.End ℂ (SpinIdx → ℂ))
    (hF : ∀ (α : leech.carrier) (s : SpinRep),
      F (spinOp (coordOfRed (red leech α)) *ᵥ s) =
        spinOp (coordOfRed (red leech α)) *ᵥ F s) :
    ∃ z : ℂ, ∀ s : SpinRep, F s = z • s := by
  have hall (a : alg (cocMat leech)) :
      ∀ s : SpinRep, F (spinAlgHom a s) = spinAlgHom a (F s) := by
    have ha : a ∈ Submodule.span ℂ (Set.range (eA leech)) := by rw [span_eA]; trivial
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨α, rfl⟩ := ha
      intro s
      rw [spinAlgHom_eA]
      exact hF α s
    | zero => intro s; simp
    | add a b _ _ ha hb => intro s; simp only [map_add, LinearMap.add_apply, ha, hb]
    | smul c a _ ha =>
      intro s
      simp only [map_smul, LinearMap.smul_apply, ha]
  have hc : F ∈ Set.center (Module.End ℂ (SpinIdx → ℂ)) := by
    rw [Semigroup.mem_center_iff]
    intro A
    obtain ⟨a, ha⟩ := spinAlgHom_surjective A
    apply LinearMap.ext
    intro s
    change A (F s) = F (A s)
    rw [← ha]
    exact (hall a s).symm
  obtain ⟨z, hz, h⟩ := Module.End.mem_center_iff.mp hc
  exact ⟨z, fun s => by simpa using LinearMap.congr_fun h s⟩

/-- The chosen charge operator intertwines the phased extraspecial spin matrices. -/
theorem liftLiftableChargeIntertwine (α : leech.carrier) (s : SpinRep) :
    liftWSpinCharge ι hι (spinOp (coordOfRed (red leech α)) *ᵥ s) =
      latCob leech leech ι α •
        (spinOp (coordOfRed (red leech (ι α))) *ᵥ liftWSpinCharge ι hι s) := by
  apply spinIso.injective
  rw [liftWSpinCharge_spec, spinIso_spinOp, liftTwChargeEquiv_eT]
  erw [spinIso_smul, spinIso_spinOp, liftWSpinCharge_spec]

/-- Any invertible intertwiner for the same charge action is proportional to the chosen one. -/
theorem liftLiftableProjectiveOfIntertwiner (E : SpinRep ≃ₗ[ℂ] SpinRep)
    (hE : ∀ (α : leech.carrier) (s : SpinRep),
      E (spinOp (coordOfRed (red leech α)) *ᵥ s) =
        latCob leech leech ι α • (spinOp (coordOfRed (red leech (ι α))) *ᵥ E s)) :
    ∃ z : ℂ, ∀ s : SpinRep, liftWSpinCharge ι hι s = z • E s := by
  let F : Module.End ℂ SpinRep := E.symm.toLinearMap.comp (liftWSpinCharge ι hι).toLinearMap
  have hEF (s : SpinRep) : E (F s) = liftWSpinCharge ι hι s := E.apply_symm_apply _
  obtain ⟨z, hz⟩ := liftLiftableSpinCommuteScalar F (fun α s => by
    apply E.injective
    erw [hEF, liftLiftableChargeIntertwine, hE, hEF])
  exact ⟨z, fun s => by rw [← hEF]; erw [hz, map_smul]⟩

/-- A rational orthogonal charge intertwiner suffices, independently of all choices.
The remaining generator calculation is exactly the explicit equation `hinter`. -/
theorem liftLiftableOfRationalIntertwiner (hsurj : Function.Surjective ι)
    (R : Matrix SpinIdx SpinIdx ℚ) (horth : Rᵀ * R = 1)
    (hinter : ∀ (α : leech.carrier) (s : SpinRep),
      R.map (Rat.castHom ℂ) *ᵥ (spinOp (coordOfRed (red leech α)) *ᵥ s) =
        latCob leech leech ι α •
          (spinOp (coordOfRed (red leech (ι α))) *ᵥ (R.map (Rat.castHom ℂ) *ᵥ s))) :
    ∃ g : liftableSubgroup, monsterLift g = liftTwVnatAut ι hι hsurj := by
  letI : FiniteDimensional ℂ SpinRep :=
    inferInstanceAs (FiniteDimensional ℂ (SpinIdx → ℂ))
  have horthC : (R.map (Rat.castHom ℂ))ᵀ * R.map (Rat.castHom ℂ) = 1 := by
    have h := congrArg (fun M => M.map (Rat.castHom ℂ)) horth
    dsimp only at h
    rw [Matrix.map_mul (f := Rat.castHom ℂ)] at h
    simpa using h
  let A : Module.End ℂ SpinRep := Matrix.mulVecLin (R.map (Rat.castHom ℂ))
  have hA : Function.Injective A := by
    intro s t h
    have h' := congrArg (fun w => (R.map (Rat.castHom ℂ))ᵀ *ᵥ w) h
    change (R.map (Rat.castHom ℂ))ᵀ *ᵥ (R.map (Rat.castHom ℂ) *ᵥ s) =
      (R.map (Rat.castHom ℂ))ᵀ *ᵥ (R.map (Rat.castHom ℂ) *ᵥ t) at h'
    simpa only [Matrix.mulVec_mulVec, horthC, Matrix.one_mulVec] using h'
  let E := LinearEquiv.ofInjectiveEndo A hA
  apply liftLiftableOfProjectiveCharge ι hι hsurj R horth
  exact liftLiftableProjectiveOfIntertwiner ι hι E hinter

end VOA.Moonshine.ConwayNorton.M8
