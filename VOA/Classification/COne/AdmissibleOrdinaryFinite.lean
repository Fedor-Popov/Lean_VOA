import VOA.Classification.COne.AdmissibleOrdinaryC2
import VOA.Huang.ZhuFiniteIrr

/-!
# Finiteness transfer to irreducible admissible modules

C₂-cofiniteness makes the existing injection from ordinary to admissible
isomorphism classes surjective. The Zhu finiteness theorem can consequently
be transferred with its explicit bottom-projection hypothesis intact.

The C₂-cofinite semisimple finiteness proposition is true, but its unconditional
proof is not supplied here: the available Zhu correspondence requires `Pr`.
-/

namespace VOA.Classification.COne.AdmissibleOrdinary

open VOA.VHat VOA.VHat.DLM3

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱}

/-- Every irreducible admissible class has an ordinary representative. -/
theorem ΦtoΦadm_surjective (hC2 : C2Cofinite W) :
    Function.Surjective (ΦtoΦadm W) := by
  intro q
  induction q using Quotient.inductionOn with
  | h P =>
    obtain ⟨O, hO⟩ := irreducible_admissible_isOrdinary hC2 P.isMod P.irreducible
    have hi : O.IsIrreducible := by
      change Nontrivial P.carrier ∧ ∀ Q : WeakModule.Submodule' O.toWeakModule,
        Q.carrier = ⊥ ∨ Q.carrier = ⊤
      rw [hO]
      exact P.irreducible
    let R : IrrModule W := { carrier := P.carrier, isMod := O, irreducible := hi }
    refine ⟨Quotient.mk (IrrModule.setoid W) R, Quotient.sound ?_⟩
    refine ⟨{ toLinearEquiv := LinearEquiv.refl ℂ P.carrier, map_act := ?_ }⟩
    intro a n x
    change O.toWeakModule.act a n x = P.isMod.toWeakModule.act a n x
    rw [hO]

/-- On the C₂-cofinite locus finiteness transfers in the reverse direction too. -/
theorem finite_Φadm_of_finite_Φ (hC2 : C2Cofinite W) (hfin : Finite (Φ W)) :
    Finite (Φadm W) := by
  letI := hfin
  exact Finite.of_surjective _ (ΦtoΦadm_surjective hC2)

/-- Named true residual: C₂-cofiniteness and semisimplicity of Zhu's algebra
imply finitely many irreducible admissible classes. -/
def C2SemisimpleAdmissibleFiniteness (W : VertexOperatorAlgebra 𝒱) : Prop :=
  C2Cofinite W → (letI := instRingA W; IsSemisimpleRing (A W)) → Finite (Φadm W)

/-- The residual finiteness statement, conditional on the exact datum required
by the library's Zhu correspondence. -/
theorem c2SemisimpleAdmissibleFiniteness_of_bottomProjection
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) :
    C2SemisimpleAdmissibleFiniteness W := by
  intro hC2 hss
  exact finite_Φadm_of_finite_Φ hC2
    (VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite Pr hC2 hss)

/-- DLM 8.1(b) under C₂-cofiniteness, Zhu semisimplicity and an explicit
bottom projection. The rationality antecedent is again unused. -/
theorem dlmFinitelyManyIrredAdmissible_of_bottomProjection
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hC2 : C2Cofinite W) (hss : letI := instRingA W; IsSemisimpleRing (A W)) :
    DLMFinitelyManyIrredAdmissible W :=
  fun _ => c2SemisimpleAdmissibleFiniteness_of_bottomProjection Pr hC2 hss

end VOA.Classification.COne.AdmissibleOrdinary
