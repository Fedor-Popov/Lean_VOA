import VOA.DeligneAudit.LeviTypeA2CertCompoundLength

/-! Finite radical key support from the sharp compound-root nilpotence. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : VOA.DeligneAudit.SectorWeyl.CurrentModule
    VOA.AffineSl3.bracketTable V) (w : V)

private theorem secondModes_length (l : List (Fin 2 × ℕ)) :
    (secondModes l).length = l.countP (fun x => x.1 = 1) := by
  simp [secondModes, List.countP_eq_length_filter]

/-- The compound-colour count cutoff in mixed radical words. -/
theorem a2_radicalWord_zero_of_second_count (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (hN : A2CompoundNilpotence ρ w p q)
    (l : List (Fin 2 × ℕ))
    (hl : p + q < l.countP (fun x => x.1 = 1)) :
    radicalWord (a2RadicalOp ρ) l • w = 0 := by
  have hsecond :
      ((secondModes l).map fun s => a2RadicalOp ρ 1 s).prod w = 0 := by
    have hlen : p + q < (secondModes l).length := by
      rw [secondModes_length]
      exact hl
    simpa [a2RadicalOp] using
      a2_compound_word_length_zero ρ w p q h hN (secondModes l) hlen
  rw [radicalWord_split ρ l, mul_smul]
  change ((firstModes l).map fun s => a2RadicalOp ρ 0 s).prod •
    ((secondModes l).map fun s => a2RadicalOp ρ 1 s).prod w = 0
  rw [hsecond, smul_zero]

/-- Sharp compound-root nilpotence supplies both raw radical count cutoffs. -/
theorem a2RadicalCountCutoff_of_compoundNilpotence (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (hN : A2CompoundNilpotence ρ w p q) :
    A2RadicalCountCutoff ρ w p q := by
  intro l hl
  rcases hl with hfirst | hsecond
  · exact a2_radicalWord_zero_of_first_count ρ w p q h l hfirst
  · exact a2_radicalWord_zero_of_second_count ρ w p q h hN l hsecond

/-- Under the one sharp zero-mode input, the explicit box contains every
nonzero radical key layer. -/
theorem a2KeyBox_contains_nonzero_of_compoundNilpotence (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (hN : A2CompoundNilpotence ρ w p q)
    (k : A2RadicalKey) (hk : a2KeyLayer ρ w k ≠ ⊥) :
    k ∈ a2KeyBox p q :=
  a2KeyBox_contains_nonzero ρ w p q k h
    (a2RadicalCountCutoff_of_compoundNilpotence ρ w p q h hN) hk

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_radicalWord_zero_of_second_count
#print axioms VOA.DeligneAudit.A3Sector.a2RadicalCountCutoff_of_compoundNilpotence
#print axioms VOA.DeligneAudit.A3Sector.a2KeyBox_contains_nonzero_of_compoundNilpotence
