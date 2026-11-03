import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticProductVanishingPower

/-! The quadratic/cubic polar ideal is genuinely smaller than the original
candidate ideal. The original current-degree-zero witness separates them. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

theorem quadraticCubicPolarIdeal_lt_candidate (m : ℕ) (hm : 3 ≤ m) :
    quadraticCubicPolarIdeal m < AllM.candidateIdeal m :=
  lt_of_le_of_lt (quadraticCubicPolarIdeal_le_powerBounded m)
    (LeviRules.powerBoundedIdeal_lt_candidate m 3 (by omega) hm)

theorem zeroModeWitness_not_mem_quadraticCubicPolarIdeal (m : ℕ) (hm : 3 ≤ m) :
    LeviRules.zeroModeWitness m ∉ quadraticCubicPolarIdeal m := by
  intro hw
  have hp := quadraticCubicPolarIdeal_le_powerBounded m hw
  exact LeviRules.zeroModeWitness_ne_zero m (by omega)
    (LeviRules.powerBoundedIdeal_current_zero m 3 hm hp (LeviRules.zeroModeWitness_graded m))

end
#print axioms quadraticCubicPolarIdeal_lt_candidate
#print axioms zeroModeWitness_not_mem_quadraticCubicPolarIdeal
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
