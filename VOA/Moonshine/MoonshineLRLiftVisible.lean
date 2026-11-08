import VOA.Moonshine.MoonshineLRLiftLiftable4
import VOA.Moonshine.MonsterGriess.ParityEqualsVisible

/-!
# The visible-pair dictionary for lattice lifts

Visible lattice matrices act on row vectors, whereas the oscillator matrices act on
columns. Transport through `leechEquiv` therefore gives the transpose matrix.

Every visible lattice component has a rational chosen lattice lift (`liftVisChosenLiftable`).
Its spin action differs from the specified visible pair by a rational signed permutation
(`liftVisChosenBlocks`). The remaining gap is to identify and cancel that discrepancy as
an extraspecial action, including its central sign. Compatibility gives the same charge
labels, but does not identify the chosen cocycle signs.

`liftVisParity_ext` eliminates a separate short-coordinate comparison once the matrix and
spin blocks match. `liftVisLiftableOfCharge` gives the exact visible-pair conclusion under
the normalized charge identity.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen
open VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterAction
open VOA.Moonshine.MonsterGriess.Spin VOA.Moonshine.MonsterGriess.SpinLattice
open VOA.Moonshine.MonsterGriess.LeechMatch
open VOA.Moonshine.MonsterGriess.ScalarKernel
open VOA.Moonshine.MonsterGriess.Visible
open scoped Matrix

/-- The integral lattice equivalence underlying a visible lattice matrix. -/
def liftVisCodeEquiv (g : latticeO) :
    codeLatticeSubgroup Code.allOnes_mem_C ≃+
      codeLatticeSubgroup Code.allOnes_mem_C where
  toFun := latHom g
  invFun := latHom g⁻¹
  left_inv u := by rw [← latHom_mul, mul_inv_cancel, latHom_one]
  right_inv u := by rw [← latHom_mul, inv_mul_cancel, latHom_one]
  map_add' := (latHom g).map_add

/-- Transport the row action to the Leech lattice model. -/
def liftVisIsometry (g : latticeO) : leech.carrier →ₗ[ℤ] leech.carrier :=
  ((leechEquiv.trans (liftVisCodeEquiv g)).trans leechEquiv.symm).toAddMonoidHom.toIntLinearMap

theorem liftVisIsometry_coordinates (g : latticeO) (α : leech.carrier) :
    leechEquiv (liftVisIsometry g α) = latHom g (leechEquiv α) :=
  leechEquiv.apply_symm_apply _

theorem liftVisIsometry_surjective (g : latticeO) :
    Function.Surjective (liftVisIsometry g) :=
  ((leechEquiv.trans (liftVisCodeEquiv g)).trans leechEquiv.symm).surjective

theorem liftVisIsometry_ratVec (g : latticeO) (α : leech.carrier) :
    ratVec (leechEquiv (liftVisIsometry g α)) = ratVec (leechEquiv α) ᵥ* mat g := by
  rw [liftVisIsometry_coordinates, ratVec_latHom]

theorem liftVisIsometry_form (g : latticeO) (α β : leech.carrier) :
    leech.form (liftVisIsometry g α) (liftVisIsometry g β) = leech.form α β := by
  apply Int.cast_injective (α := ℚ)
  rw [← codeForm_leechEquiv, ← codeForm_leechEquiv]
  change codeForm (ratVec (leechEquiv (liftVisIsometry g α)))
    (ratVec (leechEquiv (liftVisIsometry g β))) =
      codeForm (ratVec (leechEquiv α)) (ratVec (leechEquiv β))
  rw [liftVisIsometry_ratVec, liftVisIsometry_ratVec]
  exact codeForm_vecMul_vecMul (mat_mul_transpose g) _ _

/-- The precise transpose convention relating the two lattice actions. -/
theorem liftVisBlockMatrix (g : latticeO) :
    liftBlockMatrix (liftVisIsometry g) = (mat g)ᵀ := by
  ext i j
  have h := congrFun (liftVisIsometry_ratVec g (conwayAxis (piPerm.symm j))) i
  change (vec (liftVisIsometry g (conwayAxis (piPerm.symm j))) (piPerm.symm i) : ℚ) =
    _ at h
  have he : ratVec (leechEquiv (conwayAxis (piPerm.symm j))) =
      (8 : ℚ) • Pi.single j 1 := by
    funext k
    change ((vec (conwayAxis (piPerm.symm j)) (piPerm.symm k) : ℤ) : ℚ) = _
    rw [vec_conwayAxis]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Equiv.apply_eq_iff_eq, Int.cast_mul, Int.cast_ofNat, Int.cast_ite,
      Int.cast_one, Int.cast_zero]
  rw [he, Matrix.smul_vecMul, Matrix.single_vecMul] at h
  change _ / 8 = mat g j i
  rw [h]
  simp

theorem liftVisSymMat (g : latticeO) (A : symMat) :
    liftBlockSymMat (liftVisIsometry g) A = thetaA (mat g) A := by
  apply Subtype.ext
  change liftBlockMatrix (liftVisIsometry g) * (A : Matrix _ _ ℚ) *
    (liftBlockMatrix (liftVisIsometry g))ᵀ = _
  rw [liftVisBlockMatrix, Matrix.transpose_transpose]
  rfl

theorem liftVisWBlock (p : Pvis) (N : SpaceW) :
    (p.1.1 : Matrix SpinIdx SpinIdx ℚ)ᵀ * N *
      (liftBlockMatrix (liftVisIsometry p.1.2))ᵀ =
        thetaW (p.1.1 : Matrix SpinIdx SpinIdx ℚ) (mat p.1.2) N := by
  rw [liftVisBlockMatrix, Matrix.transpose_transpose]
  rfl

/-- The two reductions of a Leech vector represent the same rational lattice class. -/
theorem liftVisClass (α : leech.carrier) :
    phi0 (coordOfRed (red leech α)) = Submodule.Quotient.mk (leechEquiv α) := by
  apply axiomRed_injective
  rw [← latRedLin_apply, latRedLin_coordOfRed, axiomRed_mk,
    AddEquiv.symm_apply_apply]

/-- Compatibility identifies the noncentral coordinates of the conjugated charge. -/
theorem liftVisConjCoord (p : Pvis) (α : leech.carrier) :
    coordOf (conjQ p (rep (coordOfRed (red leech α)))) =
      coordOfRed (red leech (liftVisIsometry p.1.2 α)) := by
  apply phi0_injective
  let r := rep (coordOfRed (red leech α))
  have hr : Multiplicative.toAdd (phi (QuotientGroup.mk r)) =
      Submodule.Quotient.mk (leechEquiv α) :=
    (toAdd_phi_mk r).trans
      ((congrArg phi0 (coordOf_rep _)).trans (liftVisClass α))
  calc
    phi0 (coordOf (conjQ p r)) =
        modTwoEnd p.1.2 (Multiplicative.toAdd (phi (QuotientGroup.mk r))) :=
      (toAdd_phi_mk _).symm.trans (phi_conjQ p r)
    _ = modTwoEnd p.1.2 (Submodule.Quotient.mk (leechEquiv α)) :=
      congrArg (modTwoEnd p.1.2) hr
    _ = Submodule.Quotient.mk (latHom p.1.2 (leechEquiv α)) :=
      modTwoEnd_mk _ _
    _ = Submodule.Quotient.mk (leechEquiv (liftVisIsometry p.1.2 α)) :=
      congrArg Submodule.Quotient.mk (liftVisIsometry_coordinates _ _).symm
    _ = _ := (liftVisClass _).symm

/-- The central sign supplied by the actual visible pair. -/
def liftVisWeight (p : Pvis) (α : leech.carrier) : ℚ :=
  MonsterGriess.sgn (centralCoord (conjQ p (rep (coordOfRed (red leech α)))))

theorem liftVisWeight_sign (p : Pvis) (α : leech.carrier) :
    liftVisWeight p α = 1 ∨ liftVisWeight p α = -1 := by
  unfold liftVisWeight
  rcases zmod_two_cases (centralCoord (conjQ p (rep (coordOfRed (red leech α))))) with
    h | h
  · left; rw [h]; rfl
  · right; rw [h]; rfl

/-- The rational spin matrix of a lattice vector is its chosen representative in `Q`. -/
theorem liftVisRepMatrix (α : leech.carrier) :
    ((rep (coordOfRed (red leech α)) : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      liftMonoQmat α := by
  rw [coe_Q_eq, centralCoord_rep, coordOf_rep]
  rfl

theorem liftVisIntertwineOfConj {n : Type*} [Fintype n] [DecidableEq n]
    (R S A B : Matrix n n ℚ) (e : ℚ) (hSR : S * R = 1)
    (h : e • B = R * A * S) : R * A = e • (B * R) := by
  calc
    R * A = R * A * (S * R) := by rw [hSR, Matrix.mul_one]
    _ = (R * A * S) * R := (Matrix.mul_assoc _ _ _).symm
    _ = e • (B * R) := by rw [← h, Matrix.smul_mul]

/-- The visible spin matrix intertwines all lattice charges with its own central sign. -/
theorem liftVisIntertwine (p : Pvis) (α : leech.carrier) :
    (p.1.1 : Matrix SpinIdx SpinIdx ℚ)ᵀ * liftMonoQmat α =
      liftVisWeight p α • (liftMonoQmat (liftVisIsometry p.1.2 α) *
        (p.1.1 : Matrix SpinIdx SpinIdx ℚ)ᵀ) := by
  have h := conjQ_mat p (rep (coordOfRed (red leech α)))
  rw [(isDyadicSpinNormalizer p).coe_inv, liftVisRepMatrix, coe_Q_eq,
    qmatR_eq_sgn_smul, liftVisConjCoord] at h
  exact liftVisIntertwineOfConj _ _ _ _ _
    (isDyadicSpinNormalizer p).mul_transpose h

theorem liftVisSpinOrthogonal (p : Pvis) :
    ((p.1.1 : Matrix SpinIdx SpinIdx ℚ)ᵀ)ᵀ *
      (p.1.1 : Matrix SpinIdx SpinIdx ℚ)ᵀ = 1 := by
  rw [Matrix.transpose_transpose]
  exact (isDyadicSpinNormalizer p).mul_transpose

/-- Equality of the two sign conventions on 24 basis vectors suffices for rationality
of the chosen lattice lift. This hypothesis is not implied merely by compatibility mod center. -/
theorem liftVisLiftableOfBasisWeight (p : Pvis)
    (hweight : ∀ j, liftVisWeight p (latticeBasis leech j) =
      liftMonoWeight (liftVisIsometry p.1.2) (latticeBasis leech j)) :
    ∃ g : liftableSubgroup, monsterLift g =
      liftTwVnatAut (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2)
        (liftVisIsometry_surjective p.1.2) := by
  apply liftGenOfBasisIntertwiner _ (liftVisIsometry_form p.1.2)
    (liftVisIsometry_surjective p.1.2) _ (liftVisSpinOrthogonal p)
  intro j
  rw [← hweight j]
  exact liftVisIntertwine p _

open VOA.Moonshine.MonsterGriess.Parity

/-- Multiplication on `W` detects every short-coordinate vector. -/
theorem liftVisLwX_injective : Function.Injective (fun x : SpaceX => Lw (inX x)) := by
  classical
  intro x y h
  funext c
  have ht := congrArg
    (fun F => LinearMap.trace ℚ SpaceW (F * Lw (inX (Pi.single c 1)))) h
  dsimp only at ht
  rw [trace_Lw_mul_Lw, trace_Lw_mul_Lw] at ht
  simp only [Am_inX, xs_inX, Matrix.trace_zero,
    mul_zero, zero_add, dotProduct_single, mul_one] at ht
  exact mul_left_cancel₀ (by norm_num : (4608 : ℚ) ≠ 0) ht

/-- Two parity automorphisms with the same `W` action have the same `X` action. -/
theorem liftVisResX_eq {f g : SpaceB ≃ₗ[ℚ] SpaceB}
    (hf : IsParityAut f) (hg : IsParityAut g) (hW : resW f = resW g) :
    resX f = resX g := by
  apply LinearMap.ext
  intro x
  apply liftVisLwX_injective
  dsimp only
  rw [← hf.apply_inX, ← hg.apply_inX]
  apply LinearMap.ext
  intro N
  obtain ⟨M, hM⟩ := hf.resWEquiv.surjective N
  change resW f M = N at hM
  rw [← hM, ← hf.resW_Lw rfl, hW, hg.resW_Lw rfl]

/-- The symmetric-matrix and spin blocks determine a parity automorphism completely. -/
theorem liftVisParity_ext {f g : SpaceB ≃ₗ[ℚ] SpaceB}
    (hf : IsParityAut f) (hg : IsParityAut g)
    (hA : resA f = resA g) (hW : resW f = resW g) : f = g := by
  have hX := liftVisResX_eq hf hg hW
  apply LinearEquiv.ext
  intro u
  rw [hf.apply_eq, hg.apply_eq, hA, hX, hW]

/-- A visible pair regarded as an orthogonal Griess automorphism. -/
def liftVisAut (p : Pvis) : AutO :=
  ⟨thetaEquiv p, Gvis_le_AutO (thetaEquiv_mem_Gvis p)⟩

theorem liftVisParity (p : Pvis) : IsParityAut (thetaEquiv p) :=
  ⟨theta_gmul p, bform_theta p, theta_xB p⟩

/-- An exact normalized charge matrix proves liftability of the specified visible pair;
no independent calculation of its `X` block is required. -/
theorem liftVisLiftableOfCharge (p : Pvis)
    (hcharge : ∀ v : SpinRep,
      (liftWScalar (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2) : ℂ) •
        liftWSpinCharge (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2) v =
          ((p.1.1 : Matrix SpinIdx SpinIdx ℚ)ᵀ).map (Rat.castHom ℂ) *ᵥ v) :
    IsVnatLiftable (liftVisAut p) := by
  obtain ⟨g, _, hg⟩ := liftLiftableOfChargeMatrix (liftVisIsometry p.1.2)
    (liftVisIsometry_form p.1.2) (liftVisIsometry_surjective p.1.2) _ hcharge
  let f : SpaceB ≃ₗ[ℚ] SpaceB := (g : AutO)
  have hf : IsParityAut f := by
    refine ⟨g.val.property.1, g.val.property.2, fun u => ?_⟩
    change ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) (xB u) =
      xB (((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) u)
    rw [xB_apply, hg, hg, xB_apply]
    simp only [Matrix.mul_neg, Matrix.neg_mul]
  have hA : resA f = resA (thetaEquiv p) := by
    apply LinearMap.ext
    intro A
    change (f (inA A)).1 = (thetaEquiv p (inA A)).1
    rw [thetaEquiv_apply, theta_inA]
    change (((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) (inA A)).1 = _
    rw [hg]
    exact liftVisSymMat p.1.2 A
  have hW : resW f = resW (thetaEquiv p) := by
    apply LinearMap.ext
    intro N
    change (f (inW N)).2.2 = (thetaEquiv p (inW N)).2.2
    rw [thetaEquiv_apply, theta_inW]
    change (((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) (inW N)).2.2 = _
    rw [hg]
    exact liftVisWBlock p N
  have he : (g : AutO) = liftVisAut p :=
    Subtype.ext (liftVisParity_ext hf (liftVisParity p) hA hW)
  rw [← he]
  exact mem_liftableSubgroup.mp g.property

/-- Rational orthogonality survives extension to the complex spin module. -/
theorem liftVisOrthogonal_cast (R : Matrix SpinIdx SpinIdx ℚ) (hR : Rᵀ * R = 1) :
    (R.map (Rat.castHom ℂ))ᵀ * R.map (Rat.castHom ℂ) = 1 := by
  have h := congrArg (fun M => M.map (Rat.castHom ℂ)) hR
  dsimp only at h
  rw [Matrix.map_mul (f := Rat.castHom ℂ)] at h
  simpa using h

/-- The complex linear equivalence attached to a rational orthogonal spin matrix. -/
def liftVisMatrixEquiv (R : Matrix SpinIdx SpinIdx ℚ) (hR : Rᵀ * R = 1) :
    (SpinIdx → ℂ) ≃ₗ[ℂ] (SpinIdx → ℂ) :=
  { Matrix.mulVecLin (R.map (Rat.castHom ℂ)) with
    invFun := fun v => (R.map (Rat.castHom ℂ))ᵀ *ᵥ v
    left_inv := fun v => by
      change (R.map (Rat.castHom ℂ))ᵀ *ᵥ (R.map (Rat.castHom ℂ) *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, liftVisOrthogonal_cast R hR, Matrix.one_mulVec]
    right_inv := fun v => by
      change R.map (Rat.castHom ℂ) *ᵥ ((R.map (Rat.castHom ℂ))ᵀ *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, mul_eq_one_comm.mp (liftVisOrthogonal_cast R hR),
        Matrix.one_mulVec] }

theorem liftVisMatrixEquiv_apply (R : Matrix SpinIdx SpinIdx ℚ)
    (hR : Rᵀ * R = 1) (v : SpinIdx → ℂ) :
    liftVisMatrixEquiv R hR v = R.map (Rat.castHom ℂ) *ᵥ v := by
  change Matrix.mulVecLin (R.map (Rat.castHom ℂ)) v = _
  rfl

/-- Casting a rational signed intertwining equation gives an operator equation. -/
theorem liftVisIntertwine_cast (R A B : Matrix SpinIdx SpinIdx ℚ) (e : ℚ)
    (h : R * A = e • (B * R)) (v : SpinIdx → ℂ) :
    R.map (Rat.castHom ℂ) *ᵥ (A.map (Rat.castHom ℂ) *ᵥ v) =
      (e : ℂ) • (B.map (Rat.castHom ℂ) *ᵥ (R.map (Rat.castHom ℂ) *ᵥ v)) := by
  have he : (e • (B * R)).map (Rat.castHom ℂ) =
      (e : ℂ) • ((B * R).map (Rat.castHom ℂ)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Rat.coe_castHom, smul_eq_mul,
      Rat.cast_mul]
  have hc := congrArg (fun M => M.map (Rat.castHom ℂ)) h
  dsimp only at hc
  rw [Matrix.map_mul (f := Rat.castHom ℂ), he,
    Matrix.map_mul (f := Rat.castHom ℂ)] at hc
  rw [Matrix.mulVec_mulVec, hc, Matrix.smul_mulVec, Matrix.mulVec_mulVec]

/-- Orthogonal comparison of the chosen charge operator with the visible spin action. -/
def liftVisRelativeCharge (p : Pvis) : (SpinIdx → ℂ) ≃ₗ[ℂ] (SpinIdx → ℂ) :=
  (liftSpinCharge (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2)).trans
    (liftVisMatrixEquiv _ (liftVisSpinOrthogonal p)).symm

/-- The relative operator fixes every charge label, with an explicit residual sign. -/
theorem liftVisRelativeCharge_intertwine (p : Pvis) (α : leech.carrier)
    (v : SpinIdx → ℂ) :
    liftVisRelativeCharge p ((liftMonoQmat α).map (Rat.castHom ℂ) *ᵥ v) =
      ((liftMonoWeight (liftVisIsometry p.1.2) α * liftVisWeight p α : ℚ) : ℂ) •
        ((liftMonoQmat α).map (Rat.castHom ℂ) *ᵥ liftVisRelativeCharge p v) := by
  let E := liftVisMatrixEquiv _ (liftVisSpinOrthogonal p)
  let C := liftSpinCharge (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2)
  have hEC (w : SpinIdx → ℂ) : E (liftVisRelativeCharge p w) = C w :=
    E.apply_symm_apply _
  have hE (w : SpinIdx → ℂ) :
      E ((liftMonoQmat α).map (Rat.castHom ℂ) *ᵥ w) =
        (liftVisWeight p α : ℂ) •
          ((liftMonoQmat (liftVisIsometry p.1.2 α)).map (Rat.castHom ℂ) *ᵥ E w) :=
    liftVisIntertwine_cast _ _ _ _ (liftVisIntertwine p α) w
  have hs : (liftVisWeight p α : ℂ) * (liftVisWeight p α : ℂ) = 1 := by
    rcases liftVisWeight_sign p α with h | h <;> rw [h] <;> norm_num
  apply E.injective
  rw [hEC, map_smul, hE, hEC, smul_smul, Rat.cast_mul,
    mul_assoc, hs, mul_one]
  exact liftSpinCharge_intertwine _ (liftVisIsometry_form p.1.2) α v

/-- The residual sign operator is a rational signed permutation. -/
theorem liftVisRelativeCharge_signed (p : Pvis) :
    ∃ (σ : Equiv.Perm SpinIdx) (ε : SpinIdx → ZMod 2), ∀ v : SpinIdx → ℂ,
      liftVisRelativeCharge p v =
        (liftGenSignedMatrix σ ε).map (Rat.castHom ℂ) *ᵥ v := by
  let R := (p.1.1 : Matrix SpinIdx SpinIdx ℚ)ᵀ
  have horth := liftVisOrthogonal_cast R (liftVisSpinOrthogonal p)
  have hdot (v w : SpinIdx → ℂ) :
      liftVisRelativeCharge p v ⬝ᵥ liftVisRelativeCharge p w = v ⬝ᵥ w := by
    change ((R.map (Rat.castHom ℂ))ᵀ *ᵥ
      liftSpinCharge (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2) v) ⬝ᵥ
      ((R.map (Rat.castHom ℂ))ᵀ *ᵥ
      liftSpinCharge (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2) w) = _
    rw [liftLiftableOrthogonalDot _ (by
      rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp horth)]
    exact liftLiftableChargeDot _ (liftVisIsometry_form p.1.2) v w
  apply liftSpinRational_of_diagonal (liftVisRelativeCharge p) hdot liftSpinTestValue
    (fun t i =>
      ((liftMonoWeight (liftVisIsometry p.1.2) (liftSpinTestVector t) *
        liftVisWeight p (liftSpinTestVector t) : ℚ) : ℂ) * liftSpinTestValue t i) _
    liftSpinTest_separates
  intro t v
  have h := liftVisRelativeCharge_intertwine p (liftSpinTestVector t) v
  rw [liftSpinTest_diagonal] at h
  refine h.trans ?_
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
  exact (mul_assoc _ _ _).symm

/-- The chosen normalized charge action is the prescribed visible matrix followed by
an explicitly characterized rational signed permutation. -/
theorem liftVisCharge_signed (p : Pvis) :
    ∃ (σ : Equiv.Perm SpinIdx) (ε : SpinIdx → ZMod 2), ∀ v : SpinRep,
      (liftWScalar (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2) : ℂ) •
        liftWSpinCharge (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2) v =
          ((p.1.1 : Matrix SpinIdx SpinIdx ℚ)ᵀ * liftGenSignedMatrix σ ε).map
            (Rat.castHom ℂ) *ᵥ v := by
  obtain ⟨σ, ε, h⟩ := liftVisRelativeCharge_signed p
  refine ⟨σ, ε, fun v => ?_⟩
  have hv := congrArg (liftVisMatrixEquiv _ (liftVisSpinOrthogonal p)) (h v)
  change (liftVisMatrixEquiv _ (liftVisSpinOrthogonal p))
    ((liftVisMatrixEquiv _ (liftVisSpinOrthogonal p)).symm
      (liftSpinCharge (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2) v)) = _ at hv
  rw [LinearEquiv.apply_symm_apply, liftVisMatrixEquiv_apply,
    Matrix.mulVec_mulVec, ← Matrix.map_mul (f := Rat.castHom ℂ)] at hv
  exact hv

/-- Every visible lattice component has a rational chosen normalized charge action. -/
theorem liftVisCharge_rational (p : Pvis) :
    ∃ R : Matrix SpinIdx SpinIdx ℚ, ∀ v : SpinRep,
      (liftWScalar (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2) : ℂ) •
        liftWSpinCharge (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2) v =
          R.map (Rat.castHom ℂ) *ᵥ v := by
  obtain ⟨σ, ε, h⟩ := liftVisCharge_signed p
  exact ⟨_, h⟩

/-- Unconditional liftability of the chosen lattice lift of every visible lattice component. -/
theorem liftVisChosenLiftable (p : Pvis) :
    ∃ g : liftableSubgroup, monsterLift g =
      liftTwVnatAut (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2)
        (liftVisIsometry_surjective p.1.2) := by
  obtain ⟨R, hR⟩ := liftVisCharge_rational p
  obtain ⟨g, hg, _⟩ := liftLiftableOfChargeMatrix _ (liftVisIsometry_form p.1.2)
    (liftVisIsometry_surjective p.1.2) R hR
  exact ⟨g, hg⟩

/-- The unconditional lift, with the precise remaining signed-permutation discrepancy.
Proving that discrepancy extraspecial permits cancellation without an `X`-block calculation. -/
theorem liftVisChosenBlocks (p : Pvis) :
    ∃ (σ : Equiv.Perm SpinIdx) (ε : SpinIdx → ZMod 2) (g : liftableSubgroup),
      monsterLift g =
        liftTwVnatAut (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2)
          (liftVisIsometry_surjective p.1.2) ∧
      ∀ u : SpaceB, ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) u =
        (thetaA (mat p.1.2) u.1,
          griessTrX (liftSignX (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2)
            (griessTrX u.2.1)),
          (p.1.1 : Matrix SpinIdx SpinIdx ℚ)ᵀ * liftGenSignedMatrix σ ε *
            u.2.2 * mat p.1.2) := by
  obtain ⟨σ, ε, h⟩ := liftVisCharge_signed p
  obtain ⟨g, hg, hblocks⟩ := liftLiftableOfChargeMatrix _ (liftVisIsometry_form p.1.2)
    (liftVisIsometry_surjective p.1.2) _ h
  refine ⟨σ, ε, g, hg, fun u => ?_⟩
  refine (hblocks u).trans (Prod.ext (liftVisSymMat _ _) (Prod.ext rfl ?_))
  exact congrArg
    (fun M => (p.1.1 : Matrix SpinIdx SpinIdx ℚ)ᵀ * liftGenSignedMatrix σ ε * u.2.2 * M)
    ((congrArg Matrix.transpose (liftVisBlockMatrix p.1.2)).trans
      (Matrix.transpose_transpose (mat p.1.2)))

end VOA.Moonshine.ConwayNorton.M8
