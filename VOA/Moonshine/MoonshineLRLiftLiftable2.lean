import VOA.Moonshine.MoonshineLRLiftLiftable

/-!
# Phases of monomial lifts and the all-coordinate sign change

The raw comparison coboundary is a sign precisely when the diagonal lattice
cocycles agree. For every Leech isometry its ratio with the two spin refinements
is a sign. Thus the unphased intertwining equation has rational coefficients.

The explicit monomial case proved here is the all-coordinate sign change,
corresponding to the all-ones Golay word. Its rational spin intertwiner is `1`.
The other Golay sign changes and the Mathieu permutations remain open.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen
open VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterAction
open VOA.Moonshine.MonsterGriess.Spin
open VOA.Moonshine.MonsterGriess.LeechMatch
open scoped Matrix

/-- The square of the spin refinement, including the quadratic-form sign. -/
theorem liftMonoRefinement_sq (α : leech.carrier) :
    signRefinement (coordOfRed (red leech α)) ^ 2 =
      latticeCocycle leech α α * (-1 : ℂ) ^ (leech.form α α / 2) := by
  let p := coordOfRed (red leech α)
  have h0 : p + p = 0 := by
    rw [← two_smul (ZMod 2) p, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have h := signRefinement_add p p
  rw [h0, signRefinement_zero] at h
  have hs : signRefinement p ^ 2 = Extraspecial.sgn (signForm p p) := by
    calc
      signRefinement p ^ 2 = signRefinement p ^ 2 *
          (Extraspecial.sgn (signForm p p) * Extraspecial.sgn (signForm p p)) := by
            rw [Extraspecial.sgn_mul_self, mul_one]
      _ = (signRefinement p * signRefinement p * Extraspecial.sgn (signForm p p)) *
          Extraspecial.sgn (signForm p p) := by ring
      _ = Extraspecial.sgn (signForm p p) := by rw [← h, one_mul]
  rw [hs, signForm_apply, Extraspecial.sgn_add]
  dsimp only [p]
  rw [cocycleExp_coordOfRed, pair_coordOfRed_red,
    ← Extraspecial.neg_one_zpow_eq_sgn, latticeCocycle_eq_coc]
  rfl

/-- The spin refinement never vanishes. -/
theorem liftMonoRefinement_ne_zero (α : leech.carrier) :
    signRefinement (coordOfRed (red leech α)) ≠ 0 := by
  have h := liftMonoRefinement_sq α
  intro hz
  rw [hz, zero_pow (by decide : 2 ≠ 0)] at h
  exact (mul_ne_zero (latticeCocycle_ne_zero leech α α)
    (zpow_ne_zero (leech.form α α / 2) (by norm_num : (-1 : ℂ) ≠ 0))) h.symm

section Phases

variable (ι : leech.carrier →ₗ[ℤ] leech.carrier)
  (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)

include hι in
/-- Exact test for the raw coboundary to be real: equality of diagonal cocycles. -/
theorem liftMonoLatCob_sign_iff (α : leech.carrier) :
    (latCob leech leech ι α = 1 ∨ latCob leech leech ι α = -1) ↔
      latticeCocycle leech α α = latticeCocycle leech (ι α) (ι α) := by
  rw [← sq_eq_one_iff, liftSignLatCob_sq ι hι,
    div_eq_one_iff_eq (latticeCocycle_ne_zero leech _ _)]

include hι in
/-- Imaginary raw phases occur exactly when the diagonal cocycles have opposite signs. -/
theorem liftMonoLatCob_imaginary_iff (α : leech.carrier) :
    (latCob leech leech ι α = Complex.I ∨ latCob leech leech ι α = -Complex.I) ↔
      latticeCocycle leech α α = -latticeCocycle leech (ι α) (ι α) := by
  rw [← sq_eq_sq_iff_eq_or_eq_neg, Complex.I_sq, liftSignLatCob_sq ι hι,
    div_eq_iff (latticeCocycle_ne_zero leech _ _), neg_one_mul]

/-- The coefficient after removing the spin matrices' own phases. -/
def liftMonoPhase (α : leech.carrier) : ℂ :=
  latCob leech leech ι α * signRefinement (coordOfRed (red leech (ι α))) /
    signRefinement (coordOfRed (red leech α))

include hι in
/-- The spin phases compensate the comparison coboundary for every Leech isometry. -/
theorem liftMonoPhase_sq (α : leech.carrier) : liftMonoPhase ι α ^ 2 = 1 := by
  rw [liftMonoPhase, div_pow, mul_pow, liftSignLatCob_sq ι hι,
    liftMonoRefinement_sq, liftMonoRefinement_sq, hι]
  field_simp [latticeCocycle_ne_zero]

include hι in
/-- The compensated coefficient is always a real rational sign. -/
theorem liftMonoPhase_sign (α : leech.carrier) :
    liftMonoPhase ι α = 1 ∨ liftMonoPhase ι α = -1 :=
  sq_eq_one_iff.mp (liftMonoPhase_sq ι hι α)

/-- The rational sign in the unphased intertwining equation. -/
def liftMonoWeight (α : leech.carrier) : ℚ :=
  if liftMonoPhase ι α = 1 then 1 else -1

include hι in
theorem liftMonoWeight_cast (α : leech.carrier) :
    (liftMonoWeight ι α : ℂ) = liftMonoPhase ι α := by
  rcases liftMonoPhase_sign ι hι α with h | h
  · simp [liftMonoWeight, h]
  · norm_num [liftMonoWeight, h]

theorem liftMonoWeight_sign (α : leech.carrier) :
    liftMonoWeight ι α = 1 ∨ liftMonoWeight ι α = -1 := by
  unfold liftMonoWeight
  split_ifs <;> simp

include hι in
/-- The rational sign exactly absorbs both spin phases and the lattice coboundary. -/
theorem liftMonoWeight_phase (α : leech.carrier) :
    (liftMonoWeight ι α : ℂ) * signRefinement (coordOfRed (red leech α)) =
      latCob leech leech ι α * signRefinement (coordOfRed (red leech (ι α))) := by
  rw [liftMonoWeight_cast ι hι, liftMonoPhase,
    div_mul_cancel₀ _ (liftMonoRefinement_ne_zero α)]

/-- The rational unphased spin matrix of a lattice class. -/
def liftMonoQmat (α : leech.carrier) : Matrix SpinIdx SpinIdx ℚ :=
  qmatR ℚ 0 (coordOfRed (red leech α)).1 (coordOfRed (red leech α)).2

theorem liftMonoQmat_map (α : leech.carrier) :
    (liftMonoQmat α).map (Rat.castHom ℂ) =
      qmatR ℂ 0 (coordOfRed (red leech α)).1 (coordOfRed (red leech α)).2 :=
  map_qmatR (Rat.castHom ℂ) 0 _ _

/-- A wholly rational matrix equation suffices for the original, phased criterion. -/
theorem liftMonoOfUnphasedIntertwiner (hsurj : Function.Surjective ι)
    (R : Matrix SpinIdx SpinIdx ℚ) (horth : Rᵀ * R = 1)
    (hinter : ∀ α : leech.carrier,
      R * liftMonoQmat α = liftMonoWeight ι α • (liftMonoQmat (ι α) * R)) :
    ∃ g : liftableSubgroup, monsterLift g = liftTwVnatAut ι hι hsurj := by
  apply liftLiftableOfRationalIntertwiner ι hι hsurj R horth
  intro α s
  have hmap (r : ℚ) (M : Matrix SpinIdx SpinIdx ℚ) :
      (r • M).map (Rat.castHom ℂ) = (r : ℂ) • M.map (Rat.castHom ℂ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Rat.coe_castHom, smul_eq_mul,
      Rat.cast_mul]
  have hC := congrArg (fun M => M.map (Rat.castHom ℂ)) (hinter α)
  dsimp only at hC
  rw [Matrix.map_mul (f := Rat.castHom ℂ), hmap,
    Matrix.map_mul (f := Rat.castHom ℂ), liftMonoQmat_map, liftMonoQmat_map] at hC
  rw [spinOp, spinOp, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.smul_mulVec,
    smul_smul, Matrix.mulVec_mulVec, hC, Matrix.smul_mulVec, smul_smul,
    mul_comm (signRefinement _), liftMonoWeight_phase ι hι, Matrix.mulVec_mulVec]

end Phases

/-- The monomial isometry associated with the all-ones Golay word. -/
def liftMonoNeg : leech.carrier →ₗ[ℤ] leech.carrier := -LinearMap.id

theorem liftMonoNeg_apply (α : leech.carrier) : liftMonoNeg α = -α := rfl

theorem liftMonoNeg_isometry (α β : leech.carrier) :
    leech.form (liftMonoNeg α) (liftMonoNeg β) = leech.form α β := by
  change leech.form (-α) (-β) = leech.form α β
  simp only [map_neg, LinearMap.neg_apply, neg_neg]

theorem liftMonoNeg_surjective : Function.Surjective liftMonoNeg := by
  intro α
  exact ⟨-α, neg_neg α⟩

/-- In Conway coordinates this really negates each of the twenty-four coordinates. -/
theorem liftMonoNeg_coordinates (α : leech.carrier) (i : Fin 24) :
    (leechEquiv (liftMonoNeg α) : Fin 24 → ℤ) i = -(leechEquiv α : Fin 24 → ℤ) i := by
  rw [liftMonoNeg_apply, map_neg]
  rfl

/-- The coordinate sign word for this isometry is the all-ones Golay word. -/
theorem liftMonoNeg_allOnes :
    allOnes ∈ MonsterGriess.Code.C ∧ ∀ (α : leech.carrier) (i : Fin 24),
      (leechEquiv (liftMonoNeg α) : Fin 24 → ℤ) i =
        (if allOnes i = 0 then 1 else -1) * (leechEquiv α : Fin 24 → ℤ) i := by
  refine ⟨MonsterGriess.Code.allOnes_mem_C, fun α i => ?_⟩
  rw [liftMonoNeg_coordinates]
  simp [allOnes]

/-- Simultaneous negation preserves the entire integer cocycle exponent. -/
theorem liftMonoNeg_cocDiff : cocDiff leech leech liftMonoNeg = 0 := by
  ext α β
  simp [cocDiff, liftMonoNeg]

/-- For this monomial generator the raw coboundary is exactly one. -/
theorem liftMonoNeg_latCob (α : leech.carrier) : latCob leech leech liftMonoNeg α = 1 := by
  rw [latCob, liftMonoNeg_cocDiff]
  simp [cobSign, symForm, symMatrix]

/-- Negation acts trivially on the lattice modulo two. -/
theorem liftMonoNeg_red (α : leech.carrier) : red leech (liftMonoNeg α) = red leech α := by
  rw [liftMonoNeg_apply, map_neg]
  ext i
  exact CharTwo.neg_eq _

/-- The explicit rational orthogonal intertwiner for the all-coordinate sign change. -/
def liftMonoNegMatrix : Matrix SpinIdx SpinIdx ℚ := 1

theorem liftMonoNegMatrix_orthogonal : liftMonoNegMatrixᵀ * liftMonoNegMatrix = 1 := by
  simp [liftMonoNegMatrix]

theorem liftMonoNegMatrix_intertwine (α : leech.carrier) (s : SpinRep) :
    liftMonoNegMatrix.map (Rat.castHom ℂ) *ᵥ
        (spinOp (coordOfRed (red leech α)) *ᵥ s) =
      latCob leech leech liftMonoNeg α •
        (spinOp (coordOfRed (red leech (liftMonoNeg α))) *ᵥ
          (liftMonoNegMatrix.map (Rat.castHom ℂ) *ᵥ s)) := by
  simp [liftMonoNegMatrix, liftMonoNeg_latCob, liftMonoNeg_red]

/-- The chosen VOA lift of the all-coordinate sign change is liftable in the rational Monster
framework. -/
theorem liftMonoNeg_liftable :
    ∃ g : liftableSubgroup,
      monsterLift g = liftTwVnatAut liftMonoNeg liftMonoNeg_isometry liftMonoNeg_surjective :=
  liftLiftableOfRationalIntertwiner liftMonoNeg liftMonoNeg_isometry liftMonoNeg_surjective
    liftMonoNegMatrix liftMonoNegMatrix_orthogonal liftMonoNegMatrix_intertwine

end VOA.Moonshine.ConwayNorton.M8
