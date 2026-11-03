import VOA.DeligneAudit.D4LeviKSPairThetaIter

/-! The zero-pair case of the symmetric PAIR kernel theorem. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

theorem pairVariable_injective_zero (a c : ℕ) :
    Function.Injective (pairVariable a 0 c) := by
  intro s t h
  have hleft (u : PairSource a 0 c) :
      pairSectionVariable a 0 c (pairVariable a 0 c u) = u := by
    rcases u with x | yz
    · rcases x with z | x
      · exact z.elim0
      · rfl
    · rcases yz with z | z
      · exact z.elim0
      · rfl
  calc
    s = pairSectionVariable a 0 c (pairVariable a 0 c s) := (hleft s).symm
    _ = pairSectionVariable a 0 c (pairVariable a 0 c t) := congrArg _ h
    _ = t := hleft t

theorem pairRestriction_injective_zero (a c : ℕ) :
    Function.Injective (pairRestriction a 0 c) := by
  exact rename_injective (pairVariable a 0 c) (pairVariable_injective_zero a c)

theorem pairSymmetricRestriction_injective_zero (a c : ℕ) :
    Function.Injective (pairSymmetricRestriction a 0 c) := by
  intro P Q h
  apply Subtype.ext
  apply pairRestriction_injective_zero a c
  simpa only [pairSymmetricRestriction_apply] using congrArg Subtype.val h

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- With no Y letters the restriction map has no paired variables, so
    its kernel vanishes for every current module and every key prefix. -/
theorem pairKernelPrefix_zero
    (ρ : CurrentModule D4sector.f V) (w : V) (m i a c : ℕ) :
    PairKernelPrefix ρ w m i a 0 c := by
  intro P hP
  have hzero : P = 0 :=
    pairSymmetricRestriction_injective_zero a c (by simpa using hP)
  subst P
  simp [xyzEvaluation]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairVariable_injective_zero
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_injective_zero
#print axioms VOA.DeligneAudit.D4Levi.pairSymmetricRestriction_injective_zero
#print axioms VOA.DeligneAudit.D4Levi.pairKernelPrefix_zero
