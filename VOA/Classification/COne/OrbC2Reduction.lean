import VOA.Classification.COne.OrbC2Binomial
import VOA.Classification.COne.OrbC2Examples
import VOA.Classification.COne.OrbPosSolvable

/-!
# Exact remaining B2 relations

`TetrahedralMovingPairSpan` and `OctahedralMovingPairSpan` are unproved
finite-span assertions on the actual intrinsic C₂ quotients. Their conjunction
is equivalent to B2, as proved below. They are not axioms, and this file does
not claim B2. They isolate precisely the averaged products of nonfixed inputs
that require VOA relations.

Truth in the literature: Miyamoto, arXiv:1306.5031, Theorem 1, together with
the lossless averaging criterion. The independent polynomial obstruction
(Lemma 13) is proved in `OrbC2Binomial`; the VOA coefficient-space construction
and its skew-symmetry/Borcherds identities are still needed to apply it.
-/

namespace VOA.Classification.COne.OrbC2
open VOA

/-- Remaining tetrahedral finite-span statement. No rationality is assumed. -/
def TetrahedralMovingPairSpan : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))) [Fintype G],
    Nonempty (G ≃* alternatingGroup (Fin 4)) → MovingPairSpanFinite G

/-- Remaining octahedral finite-span statement. No rationality is assumed. -/
def OctahedralMovingPairSpan : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))) [Fintype G],
    Nonempty (G ≃* Equiv.Perm (Fin 4)) → MovingPairSpanFinite G

/-- The exact implication back to the original B2 target. -/
theorem solvableExceptionalOrbifoldC2Fact_of_movingPairs
    (hA : TetrahedralMovingPairSpan) (hS : OctahedralMovingPairSpan) :
    SolvableExceptionalOrbifoldC2Fact := by
  intro G hG
  letI : Finite G := exceptionalV2Group_finite (hG.elim Or.inl (Or.inr ∘ Or.inl))
  letI := Fintype.ofFinite G
  apply (movingPairSpanFinite_iff_c2Cofinite G (V2m_c2Cofinite 1 le_rfl)).mp
  exact hG.elim (hA G) (hS G)

/-- Both residuals are true exactly when B2 is true; no silent strengthening or weakening. -/
theorem solvableExceptionalOrbifoldC2Fact_iff_movingPairs :
    SolvableExceptionalOrbifoldC2Fact ↔
      TetrahedralMovingPairSpan ∧ OctahedralMovingPairSpan := by
  constructor
  · intro h
    exact ⟨fun G _ hG => movingPairSpanFinite_of_c2Cofinite G (h G (Or.inl hG)),
      fun G _ hG => movingPairSpanFinite_of_c2Cofinite G (h G (Or.inr hG))⟩
  · rintro ⟨hA, hS⟩
    exact solvableExceptionalOrbifoldC2Fact_of_movingPairs hA hS

/-- The same explicit relation criterion for the stronger solvable-group target. -/
theorem finiteSolvableV2OrbifoldC2_of_movingPairs
    (h : ∀ (G : Subgroup (Aut (V2m 1 le_rfl))) [Fintype G] [IsSolvable G],
      MovingPairSpanFinite G) : OrbPos.FiniteSolvableV2OrbifoldC2 := by
  intro G _ _
  letI := Fintype.ofFinite G
  exact (movingPairSpanFinite_iff_c2Cofinite G (V2m_c2Cofinite 1 le_rfl)).mp (h G)

end VOA.Classification.COne.OrbC2
