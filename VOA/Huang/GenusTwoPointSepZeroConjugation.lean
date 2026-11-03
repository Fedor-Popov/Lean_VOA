import VOA.Huang.GenusTwoPointSepTriangular

/-!
# Reduction of the full square-mode law to the two energy operators

The two named zero-mode conjugation predicates below remain proof obligations.
They concern just L(0), not all vertex modes. The reduction uses the proved
square-mode weight commutator and triangularity of the actual exponentials.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA GenusOne
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The state energy-operator case of the normalized coordinate theorem. -/
def NormalizedStateZeroConjugation (W : VertexOperatorAlgebra V) : Prop :=
  ∀ a : V, Lsq W 0 (normalizedStateChange W a) = normalizedStateChange W (W.L 0 a)

/-- The module energy-operator case of the normalized coordinate theorem. -/
def NormalizedModuleZeroConjugation (P : LWModule W) : Prop :=
  ∀ x : P.carrier, sqL P.isMod 0 (normalizedCoordinateChange P x) =
    normalizedCoordinateChange P (mode (P.isMod.YM W.conformalVector) 1 x)

/-- An ordinary energy eigenvector cannot lie strictly below its own level. -/
theorem round_eigenvector_eq_zero_of_lower (P : LWModule W) {d e : ℤ}
    (hde : d < e) {x : P.carrier} (hx : x ∈ moduleLevelLE P d)
    (he : mode (P.isMod.YM W.conformalVector) 1 x = (P.h + e) • x) : x = 0 := by
  let D := mode (P.isMod.YM W.conformalVector) 1
  let S : Set ℂ := {α | α ≠ P.h + e}
  have hdis : Disjoint (Module.End.eigenspace D (P.h + e))
      (⨆ α ∈ S, Module.End.eigenspace D α) :=
    (Module.End.eigenspaces_iSupIndep D).disjoint_biSup (by simp [S])
  have hsub : moduleLevelLE P d ≤ ⨆ α ∈ S, Module.End.eigenspace D α := by
    refine iSup_le fun j => ?_
    have hj : P.h + ((j : ℤ) : ℂ) ∈ S := by
      change P.h + ((j : ℤ) : ℂ) ≠ P.h + (e : ℂ)
      intro h
      have hc := add_left_cancel h
      have hi : (j : ℤ) = e := by exact_mod_cast hc
      have := j.2
      omega
    refine le_iSup_of_le (P.h + ((j : ℤ) : ℂ)) (le_iSup_of_le hj ?_)
    intro y hy
    exact Module.End.mem_eigenspace_iff.mpr (P.isMod.L0_weight _ _ hy)
  exact Submodule.disjoint_def.mp hdis _ (Module.End.mem_eigenspace_iff.mpr he) (hsub hx)

/-- Conditional square-weight uniqueness. The inverse is the actual finite exponential. -/
theorem square_eigenvector_eq_zero_of_lower (P : LWModule W)
    (hP : NormalizedModuleZeroConjugation P) {d e : ℤ} (hde : d < e)
    {x : P.carrier} (hx : x ∈ moduleLevelLE P d)
    (he : sqL P.isMod 0 x = (P.h + e) • x) : x = 0 := by
  have hround : mode (P.isMod.YM W.conformalVector) 1
      ((normalizedCoordinateChange P).symm x) =
      (P.h + e) • (normalizedCoordinateChange P).symm x := by
    apply (normalizedCoordinateChange P).injective
    rw [← hP, LinearEquiv.apply_symm_apply, map_smul,
      LinearEquiv.apply_symm_apply, he]
  have hz := round_eigenvector_eq_zero_of_lower P hde
    (normalizedCoordinateChange_symm_mem P hx) hround
  simpa using congrArg (normalizedCoordinateChange P) hz

/-- On homogeneous inputs the full mode conjugation follows from energy conjugation. -/
theorem normalizedSquareConjugation_of_zero_homogeneous (P : LWModule W)
    (hV : NormalizedStateZeroConjugation W) (hP : NormalizedModuleZeroConjugation P)
    {k e : ℤ} {a : V} (ha : a ∈ W.grading k)
    {x : P.carrier} (hx : x ∈ P.isMod.weight (P.h + e)) (m : ℤ) :
    normalizedCoordinateChange P (mode (P.isMod.YM a) m x) =
      SquareModule.sqMode P.isMod m (normalizedStateChange W a)
        (normalizedCoordinateChange P x) := by
  apply sub_eq_zero.mp
  apply square_eigenvector_eq_zero_of_lower P hP
    (by omega : k + e - m - 2 < k + e - m - 1)
    (normalizedSquare_defect_mem_lower P ha (mem_moduleLevelLE P le_rfl hx) m)
  have heV : Lsq W 0 (normalizedStateChange W a) =
      (k : ℂ) • normalizedStateChange W a := by
    rw [hV, W.L_zero_grading a ha, map_smul]
  have heP : sqL P.isMod 0 (normalizedCoordinateChange P x) =
      (P.h + e) • normalizedCoordinateChange P x := by
    rw [hP, P.isMod.L0_weight _ _ hx, map_smul]
  have hm := mode_mem_weight P.isMod ha hx m
  have heM : sqL P.isMod 0 (normalizedCoordinateChange P (mode (P.isMod.YM a) m x)) =
      (P.h + e + k - m - 1) •
        normalizedCoordinateChange P (mode (P.isMod.YM a) m x) := by
    rw [hP, P.isMod.L0_weight _ _ hm, map_smul]
  rw [map_sub, heM, SquareModule.sqMode_weight heV heP m]
  have h₁ : P.h + (e : ℂ) + k - m - 1 = P.h + ((k + e - m - 1 : ℤ) : ℂ) := by
    push_cast; ring
  have h₂ : (k : ℂ) + (P.h + e) - m - 1 = P.h + ((k + e - m - 1 : ℤ) : ℂ) := by
    push_cast; ring
  rw [h₁, h₂, smul_sub]

/-- The unchanged all-mode target, conditional only on the two energy-operator laws. -/
theorem normalizedSquareConjugation_of_zero (P : LWModule W)
    (hV : NormalizedStateZeroConjugation W) (hP : NormalizedModuleZeroConjugation P) :
    NormalizedSquareConjugation P := by
  intro a m x
  refine ordinaryGrading_induction W (P := fun a =>
    normalizedCoordinateChange P (mode (P.isMod.YM a) m x) =
      SquareModule.sqMode P.isMod m (normalizedStateChange W a)
        (normalizedCoordinateChange P x)) ?_ ?_ ?_ a
  · intro k a ha
    refine FusionTop.induction_weight P.isMod x (by simp) ?_ ?_
    · intro x y hx hy
      simp only [map_add, hx, hy]
    · intro α x hx
      rcases FusionTop.eq_zero_or_level P hx with rfl | ⟨n, rfl⟩
      · simp
      · exact normalizedSquareConjugation_of_zero_homogeneous P hV hP ha hx m
  · simp
  · intro a b ha hb
    simp only [map_add, mode_add, LinearMap.add_apply, ha, hb]

/-- The Huang normalization consumer needs only the energy laws. -/
theorem huangU_conjugation_of_zero (P : LWModule W)
    (hV : NormalizedStateZeroConjugation W) (hP : NormalizedModuleZeroConjugation P)
    (a : V) (m : ℤ) (x : P.carrier) :
    huangU P 0 (mode (P.isMod.YM a) m ((huangU P 0).symm x)) = huangModeScale m •
      SquareModule.sqMode P.isMod m (huangStateU W a) x :=
  huangU_conjugation_of_squareConjugation P (normalizedSquareConjugation_of_zero P hV hP) a m x

end VOA.Huang.GenusTwoPoint.Separate
