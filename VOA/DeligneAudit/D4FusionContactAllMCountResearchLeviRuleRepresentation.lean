import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleDerivation
import VOA.DeligneAudit.A2SectorWeyl

/-! A genuine current-module structure for all18 checked differential
operators. The commutator is proved, not supplied as a representation input. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
noncomputable section
variable (K : Type*) [Field K]

def structureCoeff (a b c : Fin 18) : K :=
  if c = bracketTarget a b then (bracketCoeff a b:K) else 0

def representation (m : ℕ) :
    VOA.DeligneAudit.SectorWeyl.CurrentModule (structureCoeff K) (Ring K m) where
  op a k := (deriv K m a k).toLinearMap
  comm a b k l p := by
    have h := congrArg (fun D : Derivation K (Ring K m) (Ring K m) => D p)
      (deriv_bracket K m a b k l)
    change deriv K m a k (deriv K m b l p) - deriv K m b l (deriv K m a k p) =
      ∑ e, structureCoeff K a b e • deriv K m e (k+l) p
    simp only [structureCoeff,ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    simpa only [Derivation.commutator_apply,Derivation.smul_apply,Int.cast_smul_eq_zsmul] using h

end
#print axioms representation
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
