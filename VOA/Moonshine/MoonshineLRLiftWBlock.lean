import VOA.Moonshine.MoonshineLRLiftTwisted3
import VOA.Moonshine.MoonshineLRLiftExtraAut
import VOA.Moonshine.MoonshineLRFinOrderIsing
import VOA.Moonshine.MoonshineCNGriessFrameBlock

/-!
# Twisted weight-two blocks of the lattice and extraspecial lifts

The spanning vectors are `hP v t = h_v(-1/2) ⊗ t`. The lattice lift acts by
`Q` on the oscillator and its normalized charge intertwiner on `t`; the
extraspecial lift acts only on `t`. We express both actions in `spinIso`
coordinates, including the exact phased spin matrix for the extraspecial action.

The imported modules supply no final identification with the rational `SpaceW`.
Matching its oscillator frame and fixing the spin-isomorphism/form normalization
remain dictionary work. These statements do not assert rationality of the lifts.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA IntegralLattice LatGen TwistedHeisenberg MvPolynomial
open VOA.Moonshine.AutMonster VOA.Moonshine.SigmaTop VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess
open scoped BigOperators TensorProduct Matrix

/-- Rank transport of the action on a single half-integer oscillator. -/
theorem liftWCast_hT (L : IntegralLattice.{0}) (hEven : L.Even)
    (hU : IsUnit (gramMat L).det) (hPos : L.PosDef)
    (ι : L.carrier →ₗ[ℤ] L.carrier)
    (hι : ∀ α β, L.form (ι α) (ι β) = L.form α β)
    {r : ℕ} (hr : rank L = r) (v : Fin (rank L) → ℂ) (t : ExtraT L hEven hU) :
    liftTwCastEquiv L hEven hU hPos ι hι hr
        ((∑ a, v a • (X (0, Fin.cast hr a) : FockT r)) ⊗ₜ t) =
      (∑ a, (oscMatrix L L ι *ᵥ v) a • (X (0, Fin.cast hr a) : FockT r)) ⊗ₜ
        liftTwChargeEquiv L ι hEven hU hι t := by
  subst hr
  change liftTwTensorEquiv _ _ _ _ ((∑ a, v a • X (0, a)) ⊗ₜ t) = _
  rw [liftTwTensorEquiv_tmul]
  congr 1
  exact fockMap_Xcomb _ _ _ rfl 0

section Lattice

variable (ι : leech.carrier →ₗ[ℤ] leech.carrier)
  (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)

/-- The unnormalized twisted lift on the spanning vectors of weight two. -/
theorem liftWPlus_hP (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    liftTwPlusEquiv ι hι (hP v t) =
      hP (oscMatrix leech leech ι *ᵥ v)
        (liftTwChargeEquiv leech ι leech_even leech_isUnit_det_gramMat hι t) := by
  apply Subtype.ext
  exact liftWCast_hT leech leech_even leech_isUnit_det_gramMat leech_posDef
    ι hι leech_rank v t

/-- Any chosen normalization scalar can be placed on the charge factor. -/
theorem liftWNormalized_hP (c : ℂˣ) (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    liftTwNormalizedPlusEquiv ι hι c (hP v t) =
      hP (oscMatrix leech leech ι *ᵥ v)
        ((c : ℂ) • liftTwChargeEquiv leech ι leech_even leech_isUnit_det_gramMat hι t) := by
  rw [liftTwNormalizedPlusEquiv_apply, liftWPlus_hP, hP_smul_right]

/-- The exact scalar selected by the existing form-normalized VOA lift. -/
def liftWScalar : ℂˣ := (liftTwExists_formScalar ι hι).choose

/-- The lattice lift on a pure twisted weight-two vector inside `Vnat`. -/
theorem liftWNat_hP (hsurj : Function.Surjective ι)
    (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    liftTwVnatAut ι hι hsurj ((0, hP v t) : Vnat) =
      (0, hP (oscMatrix leech leech ι *ᵥ v)
        ((liftWScalar ι hι : ℂ) •
          liftTwChargeEquiv leech ι leech_even leech_isUnit_det_gramMat hι t)) := by
  rw [liftTwVnatAut_apply, map_zero, liftWNormalized_hP]
  rfl

/-- The charge intertwiner in the complex spin coordinates. -/
def liftWSpinCharge : SpinRep ≃ₗ[ℂ] SpinRep :=
  ((spinIso.restrictScalars ℂ).trans
    (liftTwChargeEquiv leech ι leech_even leech_isUnit_det_gramMat hι)).trans
      (spinIso.restrictScalars ℂ).symm

theorem liftWSpinCharge_spec (s : SpinRep) :
    spinIso (liftWSpinCharge ι hι s) =
      liftTwChargeEquiv leech ι leech_even leech_isUnit_det_gramMat hι (spinIso s) := by
  exact spinIso.apply_symm_apply _

/-- The lattice lift in spin coordinates, retaining its chosen scalar. -/
theorem liftWNat_spin (hsurj : Function.Surjective ι)
    (v : Fin (rank leech) → ℂ) (s : SpinRep) :
    liftTwVnatAut ι hι hsurj ((0, hP v (spinIso s)) : Vnat) =
      (0, hP (oscMatrix leech leech ι *ᵥ v)
        (spinIso ((liftWScalar ι hι : ℂ) • liftWSpinCharge ι hι s))) := by
  rw [spinIso_smul, liftWSpinCharge_spec, liftWNat_hP]

end Lattice

/-- The raw extraspecial action leaves the oscillator unchanged. -/
theorem liftWExtraPlus_hP (μ : leech.carrier)
    (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    extraPlusPhi μ (hP v t) = hP v (eT leech leech_even leech_isUnit_det_gramMat μ t) := by
  apply Subtype.ext
  exact extraPhi_tmul leech leech_even leech_isUnit_det_gramMat μ 24 (hvec v) t

/-- The normalized extraspecial action on weight-two generators. -/
theorem liftWExtraIsometry_hP (μ : leech.carrier)
    (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    extraPlusIsometry μ (hP v t) =
      hP v (extraPlusFormScalar μ • eT leech leech_even leech_isUnit_det_gramMat μ t) := by
  rw [extraPlusIsometry, LinearMap.smul_apply, liftWExtraPlus_hP, hP_smul_right]

/-- The extraspecial VOA lift on a pure twisted weight-two vector. -/
theorem liftWExtraNat_hP (μ : leech.carrier)
    (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    extraVnatAut μ ((0, hP v t) : Vnat) =
      (0, hP v (extraPlusFormScalar μ •
        eT leech leech_even leech_isUnit_det_gramMat μ t)) := by
  rw [extraVnatAut_apply, map_zero, liftWExtraIsometry_hP]

/-- The spin matrix is exactly the unnormalized charge action in spin coordinates. -/
theorem liftWExtra_spinOp (μ : leech.carrier) (s : SpinRep) :
    spinIso.symm (eT leech leech_even leech_isUnit_det_gramMat μ (spinIso s)) =
      (spinOp (coordOfRed (red leech μ))).mulVec s := by
  rw [← spinIso_spinOp, spinIso.symm_apply_apply]

/-- The normalized extraspecial VOA lift is the scalar times the phased spin matrix. -/
theorem liftWExtraNat_spin (μ : leech.carrier)
    (v : Fin (rank leech) → ℂ) (s : SpinRep) :
    extraVnatAut μ ((0, hP v (spinIso s)) : Vnat) =
      (0, hP v (spinIso (extraPlusFormScalar μ •
        ((spinOp (coordOfRed (red leech μ))).mulVec s : SpinRep)))) := by
  erw [spinIso_smul, spinIso_spinOp]
  exact liftWExtraNat_hP μ v (spinIso s)

/-- These spin-coordinate generators span the entire twisted weight-two space. -/
theorem liftWWeightTwo_span :
    plusModule.weight (2 : ℂ) = Submodule.span ℂ
      {y | ∃ (v : Fin (rank leech) → ℂ) (s : SpinRep), y = hP v (spinIso s)} := by
  rw [twistedPlus_grading_two_eq_span]
  congr 1
  ext y
  constructor
  · rintro ⟨v, t, rfl⟩
    obtain ⟨s, rfl⟩ := spinIso.surjective t
    exact ⟨v, s, rfl⟩
  · rintro ⟨v, s, rfl⟩
    exact ⟨v, spinIso s, rfl⟩

/-- Complex spin coordinates in the existing 24-vector oscillator frame `cw`. -/
def liftWData : (Fin 24 → SpinRep) →ₗ[ℂ] TP where
  toFun N := ∑ j, hPL j (spinIso (N j))
  map_add' N M := by
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c N := by
    simp only [Pi.smul_apply, spinIso_smul, map_smul, Finset.smul_sum, RingHom.id_apply]

theorem liftWData_apply (N : Fin 24 → SpinRep) :
    liftWData N = ∑ j, hP (cw j) (spinIso (N j)) := rfl

/-- Every family of spin coordinates gives a twisted weight-two vector. -/
theorem liftWData_mem_weight (N : Fin 24 → SpinRep) :
    liftWData N ∈ plusModule.weight (2 : ℂ) :=
  Submodule.sum_mem _ fun j _ => hP_mem_weight (cw j) (spinIso (N j))

/-- Coordinate extraction is a left inverse, so the finite-family map is faithful. -/
theorem liftWData_component (N : Fin 24 → SpinRep) (j : Fin 24) :
    compW j (liftWData N) = spinIso (N j) := by
  rw [liftWData_apply, map_sum]
  simp only [compW_hP]
  simp

theorem liftWData_injective : Function.Injective liftWData := by
  intro N M h
  funext j
  apply spinIso.injective
  simpa only [liftWData_component] using congrArg (compW j) h

/-- The frame expansion of a spanning vector in spin coordinates. -/
theorem liftWData_hP (v : Fin (rank leech) → ℂ) (s : SpinRep) :
    liftWData (fun j => ((∑ a, v a * cw j a) / 8) • s) = hP v (spinIso s) := by
  rw [liftWData_apply]
  conv_rhs => rw [vec_eq_sum_cw v, hP_sum_left]
  apply Finset.sum_congr rfl
  intro j _
  rw [spinIso_smul, hP_smul_right, hP_smul_left]

/-- The finite-family coordinates cover precisely the entire weight-two twisted space. -/
theorem liftWData_range : LinearMap.range liftWData = plusModule.weight (2 : ℂ) := by
  apply le_antisymm
  · rintro _ ⟨N, rfl⟩
    exact liftWData_mem_weight N
  · rw [liftWWeightTwo_span, Submodule.span_le]
    rintro _ ⟨v, s, rfl⟩
    exact ⟨_, liftWData_hP v s⟩

/-- A complex coordinate equivalence, before choosing the rational Griess dictionary. -/
def liftWEquiv : (Fin 24 → SpinRep) ≃ₗ[ℂ] plusModule.weight (2 : ℂ) :=
  (LinearEquiv.ofInjective liftWData liftWData_injective).trans
    (LinearEquiv.ofEq _ _ liftWData_range)

/-- All 24 spin columns transform by `Q` on their oscillator and `c ρ` on their charge. -/
theorem liftWNat_data (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)
    (hsurj : Function.Surjective ι) (N : Fin 24 → SpinRep) :
    liftTwVnatAut ι hι hsurj ((0, liftWData N) : Vnat) =
      (0, ∑ j, hP (oscMatrix leech leech ι *ᵥ cw j)
        (spinIso ((liftWScalar ι hι : ℂ) • liftWSpinCharge ι hι (N j)))) := by
  rw [liftTwVnatAut_apply, map_zero, liftWData_apply, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [liftWNormalized_hP, spinIso_smul, liftWSpinCharge_spec]
  rfl

/-- The extraspecial block is columnwise multiplication by the normalized spin matrix. -/
theorem liftWExtraNat_data (μ : leech.carrier) (N : Fin 24 → SpinRep) :
    extraVnatAut μ ((0, liftWData N) : Vnat) =
      (0, liftWData (fun j => extraPlusFormScalar μ •
        ((spinOp (coordOfRed (red leech μ))).mulVec (N j) : SpinRep))) := by
  rw [extraVnatAut_apply, map_zero, liftWData_apply, liftWData_apply, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  erw [spinIso_smul, spinIso_spinOp]
  exact liftWExtraIsometry_hP μ (cw j) (spinIso (N j))

/-- The oscillator matrix in the `cw` frame; these frame vectors have squared norm eight. -/
def liftWFrameMatrix (ι : leech.carrier →ₗ[ℤ] leech.carrier) :
    Matrix (Fin 24) (Fin 24) ℂ :=
  fun b a => (∑ k, (oscMatrix leech leech ι *ᵥ cw a) k * cw b k) / 8

/-- The complete lattice action on the 24 spin columns. -/
def liftWLatticeData (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)
    (N : Fin 24 → SpinRep) : Fin 24 → SpinRep :=
  fun b => ∑ a, liftWFrameMatrix ι b a •
    ((liftWScalar ι hι : ℂ) • liftWSpinCharge ι hι (N a))

/-- The lattice lift intertwines the finite-family coordinates with their explicit action. -/
theorem liftWNat_coordinates (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)
    (hsurj : Function.Surjective ι) (N : Fin 24 → SpinRep) :
    liftTwVnatAut ι hι hsurj ((0, liftWData N) : Vnat) =
      (0, liftWData (liftWLatticeData ι hι N)) := by
  rw [liftWNat_data]
  have he : liftWLatticeData ι hι N = ∑ a, fun b => liftWFrameMatrix ι b a •
      ((liftWScalar ι hι : ℂ) • liftWSpinCharge ι hι (N a)) := by
    ext b
    simp only [liftWLatticeData, Finset.sum_apply]
  rw [he, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact (liftWData_hP (oscMatrix leech leech ι *ᵥ cw a)
    ((liftWScalar ι hι : ℂ) • liftWSpinCharge ι hι (N a))).symm

end VOA.Moonshine.ConwayNorton.M8
