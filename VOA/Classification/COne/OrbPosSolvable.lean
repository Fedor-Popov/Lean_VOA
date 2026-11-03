import VOA.Classification.COne.ExceptionalOrbifoldNice
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.GroupTheory.Solvable

/-!
# The finite-group endpoint of B2

Solvability is proved, but Miyamoto's C₂ theorem is not proved here.
The remaining proposition is its specialization to finite solvable subgroups
of the already simple C₂-cofinite CFT-type lattice VOA V₂.
Source: arXiv:1306.5031, Theorem 1.
-/

namespace VOA.Classification.COne.OrbPos
open VOA VertexOperatorAlgebra

theorem alternating_fin_four_solvable : IsSolvable (alternatingGroup (Fin 4)) := by
  let K := alternatingGroup.kleinFour (Fin 4)
  have h4 : Nat.card (Fin 4) = 4 := by simp
  letI : K.Normal := alternatingGroup.normal_kleinFour h4
  letI : IsKleinFour K := alternatingGroup.kleinFour_isKleinFour h4
  letI : IsMulCommutative K := IsKleinFour.isMulCommutative
  letI : IsSolvable K := isSolvable_of_comm fun a b => mul_comm' a b
  have hc : Nat.card (alternatingGroup (Fin 4) ⧸ K) = 3 := by
    have he := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [alternatingGroup.card_of_card_eq_four h4,
      alternatingGroup.kleinFour_card_of_card_eq_four h4] at he
    omega
  letI : IsCyclic (alternatingGroup (Fin 4) ⧸ K) := isCyclic_of_prime_card hc
  letI : IsSolvable (alternatingGroup (Fin 4) ⧸ K) :=
    isSolvable_of_comm fun a b => mul_comm' a b
  apply solvable_of_ker_le_range K.subtype (QuotientGroup.mk' K)
  simp

theorem perm_fin_four_solvable : IsSolvable (Equiv.Perm (Fin 4)) := by
  letI := alternating_fin_four_solvable
  apply solvable_of_ker_le_range (alternatingGroup (Fin 4)).subtype
    (Equiv.Perm.sign : Equiv.Perm (Fin 4) →* ℤˣ)
  rw [Subgroup.range_subtype, alternatingGroup_eq_sign_ker]

theorem solvableExceptionalGroup_isSolvable
    (G : Subgroup (Aut (V2m 1 le_rfl)))
    (hG : Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (G ≃* Equiv.Perm (Fin 4))) : IsSolvable G := by
  rcases hG with hG | hG
  · obtain ⟨e⟩ := hG
    letI := alternating_fin_four_solvable
    exact solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
  · obtain ⟨e⟩ := hG
    letI := perm_fin_four_solvable
    exact solvable_of_solvable_injective (f := e.toMonoidHom) e.injective

/-- Still open: the VOA content of Miyamoto's solvable-orbifold theorem,
specialized to V₂. Solvability alone is not a C₂ proof. -/
def FiniteSolvableV2OrbifoldC2 : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))) [Finite G] [IsSolvable G],
    C2Cofinite (orbifoldVOA G)

theorem solvableExceptionalOrbifoldC2Fact_of_finiteSolvable
    (h : FiniteSolvableV2OrbifoldC2) : SolvableExceptionalOrbifoldC2Fact := by
  intro G hG
  have he : IsExceptionalV2Group G := hG.elim Or.inl (Or.inr ∘ Or.inl)
  letI := exceptionalV2Group_finite he
  letI := solvableExceptionalGroup_isSolvable G hG
  exact h G

end VOA.Classification.COne.OrbPos
