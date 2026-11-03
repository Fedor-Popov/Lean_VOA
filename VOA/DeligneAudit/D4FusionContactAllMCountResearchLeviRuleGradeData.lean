import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleGrading

/-! Small exact grading identities for the original nine contact colors. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules

def cWeight (i : Fin 9) : ℤ := if i=8 then 1 else 0

def bitWeight : Fin 3 → Fin 9 → ℤ := ![
  ![0,1,0,0,1,1,0,1,0],
  ![0,0,1,0,1,0,1,1,0],
  ![0,0,0,1,0,1,1,1,0]]

def axisIncrement (d : Fin 3) (a : Fin 18) : ℤ := if a=negative d then 1 else 0

theorem cWeight_nonneg : ∀ i, 0 ≤ cWeight i := by decide +kernel
theorem bitWeight_le_one : ∀ d i, bitWeight d i ≤ 1 := by decide +kernel

theorem cartan_color_rule : ∀ h i,
    coeff (cartan h) i=0 ∨ target (cartan h) i=i := by decide +kernel

theorem negative_bit_rule : ∀ a d i, (7 ≤ a.val ∧ a.val<10) →
    coeff a i=0 ∨ bitWeight d (target a i)=bitWeight d i+axisIncrement d a := by
  decide +kernel

theorem contact_c_rule : ∀ a i, 10 ≤ a.val →
    coeff a i=0 ∨ cWeight (target a i)=cWeight i-1 := by decide +kernel

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
