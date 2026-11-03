import VOA.Classification.COne.OrbC2bOcta

/-! # Precise residuals for the concrete two-step route

The two moving-pair propositions below concern actual, constructed actions.
They remain OPEN (true by Miyamoto's solvable orbifold theorem). Standard-form
propositions are also OPEN: conjugacy of the complex tetrahedral/octahedral
embeddings has not been formalized here. Neither is silently inferred from
an abstract group isomorphism.
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbC2b
open VOA

instance cubicFinite : Finite (Subgroup.zpowers kleinCubic) :=
  (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, kleinCubic_cube⟩).finite_zpowers.to_subtype

instance cubicFintype : Fintype (Subgroup.zpowers kleinCubic) := Fintype.ofFinite _

instance involutionFinite : Finite (Subgroup.zpowers tetraInvolution) :=
  (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨2, by norm_num, tetraInvolution_square⟩).finite_zpowers.to_subtype

instance involutionFintype : Fintype (Subgroup.zpowers tetraInvolution) := Fintype.ofFinite _

/-- OPEN: the cubic step on the known strongly rational norm-eight plus VOA. -/
def CubicMovingPairSpan : Prop := OrbC2.MovingPairSpanFinite (Subgroup.zpowers kleinCubic)

/-- OPEN: the involution step on the tetrahedral fixed algebra. -/
def InvolutionMovingPairSpan : Prop :=
  OrbC2.MovingPairSpanFinite (Subgroup.zpowers tetraInvolution)

/-- OPEN geometric identification, implied by conjugacy of tetrahedral embeddings. -/
def TetrahedralStandardForm : Prop :=
  ∀ G : Subgroup (Aut (V2m 1 le_rfl)), Nonempty (G ≃* alternatingGroup (Fin 4)) →
    VOAIsomorphic (orbifoldVOA G) (orbifoldVOA tetra)

/-- OPEN geometric identification, implied by conjugacy of octahedral embeddings. -/
def OctahedralStandardForm : Prop :=
  ∀ G : Subgroup (Aut (V2m 1 le_rfl)), Nonempty (G ≃* Equiv.Perm (Fin 4)) →
    VOAIsomorphic (orbifoldVOA G) (orbifoldVOA octa)

/-- Lossless equivalence for the standard tetrahedral embedding. -/
theorem cubicMovingPairSpan_iff_tetra_c2 :
    CubicMovingPairSpan ↔ C2Cofinite (orbifoldVOA tetra) := by
  obtain ⟨e, he, _⟩ := tetra_cubic_iso
  constructor
  · intro h
    exact ConverseUniverse.c2Cofinite_of_iso e.symm (isVOAHom_symm' e he)
      ((OrbC2.movingPairSpanFinite_iff_c2Cofinite
        (Subgroup.zpowers kleinCubic) klein_stronglyRational.c2Cofinite).mp h)
  · intro h
    exact OrbC2.movingPairSpanFinite_of_c2Cofinite _
      (ConverseUniverse.c2Cofinite_of_iso e he h)

/-- Once the cubic step holds, the involution criterion is also lossless. -/
theorem involutionMovingPairSpan_iff_octa_c2 (hC : CubicMovingPairSpan) :
    InvolutionMovingPairSpan ↔ C2Cofinite (orbifoldVOA octa) := by
  obtain ⟨e, he, _⟩ := octa_involution_iso
  constructor
  · intro h
    exact ConverseUniverse.c2Cofinite_of_iso e.symm (isVOAHom_symm' e he)
      ((OrbC2.movingPairSpanFinite_iff_c2Cofinite (Subgroup.zpowers tetraInvolution)
        (cubicMovingPairSpan_iff_tetra_c2.mp hC)).mp h)
  · intro h
    exact OrbC2.movingPairSpanFinite_of_c2Cofinite _
      (ConverseUniverse.c2Cofinite_of_iso e he h)

theorem tetrahedralMovingPairSpan_of_cubic (hF : TetrahedralStandardForm)
    (hC : CubicMovingPairSpan) : OrbC2.TetrahedralMovingPairSpan := by
  intro G _ hG
  obtain ⟨e, he, _⟩ := hF G hG
  exact OrbC2.movingPairSpanFinite_of_c2Cofinite G
    (ConverseUniverse.c2Cofinite_of_iso e he (cubicMovingPairSpan_iff_tetra_c2.mp hC))

theorem octahedralMovingPairSpan_of_cubic_involution (hF : OctahedralStandardForm)
    (hC : CubicMovingPairSpan) (hI : InvolutionMovingPairSpan) :
    OrbC2.OctahedralMovingPairSpan := by
  intro G _ hG
  obtain ⟨e, he, _⟩ := hF G hG
  exact OrbC2.movingPairSpanFinite_of_c2Cofinite G
    (ConverseUniverse.c2Cofinite_of_iso e he
      ((involutionMovingPairSpan_iff_octa_c2 hC).mp hI))

/-- Conditional B2; all unproved geometry and mode bounds remain explicit. -/
theorem solvableExceptionalOrbifoldC2Fact_of_tower
    (hA : TetrahedralStandardForm) (hS : OctahedralStandardForm)
    (hC : CubicMovingPairSpan) (hI : InvolutionMovingPairSpan) :
    SolvableExceptionalOrbifoldC2Fact :=
  OrbC2.solvableExceptionalOrbifoldC2Fact_of_movingPairs
    (tetrahedralMovingPairSpan_of_cubic hA hC)
    (octahedralMovingPairSpan_of_cubic_involution hS hC hI)

end VOA.Classification.COne.OrbC2b
