import VOA.DeligneAudit.SL4TRadicalPowerSums

/-! The full Cartan power-sum action on merged radical multiplicity spaces. -/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)
variable (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))

include h

/-- The omitted Cartan current preserves the closure of earlier radical counts. -/
theorem higherRadicalCountClosure_extra_cartan (d : Fin 3 → ℕ) (s : ℕ) :
    higherRadicalCountClosure ρ w d ≤
      (higherRadicalCountClosure ρ w d).comap (ρ.op 12 s) := by
  apply a3LeviClosure_extra_inv
  intro r
  apply iSup_le
  intro k
  apply iSup_le
  intro hk v hv
  change ρ.op 12 r v ∈ ⨆ k, ⨆ (_ : higherRadicalCounts d k), a3KeyLayer ρ w k
  by_cases hr : r = 0
  · subst r
    rw [a3_extra_cartan_weight_key ρ w a b c h k hv]
    exact Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem hk hv))
  · have hk' : higherRadicalCounts d (a3KeyShift r k) := hk
    exact Submodule.mem_iSup_of_mem (a3KeyShift r k)
      (Submodule.mem_iSup_of_mem hk'
        (a3_extra_cartan_pos_maps_key ρ w a b c h r (by omega) k hv))

/-- Every alphabet current preserves the quotient relations. -/
theorem higherRadicalCountClosure_alphabet_current (d : Fin 3 → ℕ)
    (j : Fin 3) (s : ℕ) :
    higherRadicalCountClosure ρ w d ≤
      (higherRadicalCountClosure ρ w d).comap (radicalAlphabetCurrent ρ j s) := by
  intro v hv
  let N := higherRadicalCountClosure ρ w d
  have h₀ := higherRadicalCountClosure_extra_cartan ρ w a b c h d s hv
  have h₁ := a3LeviClosure_inv ρ _ 6 s hv
  have h₂ := a3LeviClosure_inv ρ _ 7 s hv
  exact N.smul_mem _ (N.add_mem (N.add_mem (N.neg_mem h₀) (N.smul_mem _ h₁))
    (N.smul_mem _ h₂))

/-- The Cartan realization of alphabet power sums on the merged Levi quotient. -/
def radicalAlphabetQuotCurrent (d : Fin 3 → ℕ) (j : Fin 3) (s : ℕ) :
    Module.End ℂ (V ⧸ higherRadicalCountClosure ρ w d) :=
  (higherRadicalCountClosure ρ w d).mapQ (higherRadicalCountClosure ρ w d)
    (radicalAlphabetCurrent ρ j s)
    (higherRadicalCountClosure_alphabet_current ρ w a b c h d j s)

theorem radicalAlphabetQuotCurrent_mk (d : Fin 3 → ℕ) (j : Fin 3) (s : ℕ) (v : V) :
    radicalAlphabetQuotCurrent ρ w a b c h d j s
      ((higherRadicalCountClosure ρ w d).mkQ v) =
        (higherRadicalCountClosure ρ w d).mkQ (radicalAlphabetCurrent ρ j s v) := rfl

/-- Positive alphabet currents restrict to the actual multiplicity subspace. -/
theorem radicalCountMultiplicity_alphabet_current (d : Fin 3 → ℕ)
    (j : Fin 3) (s : ℕ) (hs : 0 < s) :
    radicalCountMultiplicity ρ w d ≤ (radicalCountMultiplicity ρ w d).comap
      (radicalAlphabetQuotCurrent ρ w a b c h d j s) := by
  rintro x ⟨v, hv, rfl⟩
  exact ⟨_, radicalCountLayer_alphabet_current ρ w a b c h d j s hs hv, rfl⟩

/-- The quotient Cartan action still shifts modes by the corresponding power sum. -/
theorem radicalAlphabetQuotCurrent_word (d : Fin 3 → ℕ) (j : Fin 3)
    (s : ℕ) (hs : 0 < s) (l : List (Fin 3 × ℕ)) :
    radicalAlphabetQuotCurrent ρ w a b c h d j s
      ((higherRadicalCountClosure ρ w d).mkQ
        (LeviTypeA.radicalWord (radicalOp ρ) l • w)) =
      (higherRadicalCountClosure ρ w d).mkQ (radicalPowerSumWord ρ w j s l) := by
  rw [radicalAlphabetQuotCurrent_mk, radicalAlphabetCurrent_word ρ w a b c h j s hs]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.higherRadicalCountClosure_extra_cartan
#print axioms VOA.DeligneAudit.SL4T.higherRadicalCountClosure_alphabet_current
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabetQuotCurrent_mk
#print axioms VOA.DeligneAudit.SL4T.radicalCountMultiplicity_alphabet_current
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabetQuotCurrent_word
