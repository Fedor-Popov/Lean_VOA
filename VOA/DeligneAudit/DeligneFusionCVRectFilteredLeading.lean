import VOA.DeligneAudit.DeligneFusionCVRectFilteredCoeff

/-!
# Exactness of actual PBW symbols

A length symbol vanishes exactly when its actual vector belongs to the
shorter-word filtration. Thus proved graded annihilators can be converted
back to source coefficient relations modulo shorter actual PBW words.
-/

namespace VOA.DeligneAudit.A2.CVRectFiltered

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule bracketTable V) (w : V)

theorem readAmbient_symbol (n : ℕ) (v : V) :
    readAmbient R w n (symbol R w n v) = (Pbelow R w n).mkQ v := by
  change (Pbelow R w n).mkQ ((Finsupp.single n v) n) = _
  simp

theorem symbol_eq_zero_iff (n : ℕ) (v : V) :
    symbol R w n v = 0 ↔ v ∈ Pbelow R w n := by
  constructor
  · intro hv
    have hh := congrArg (readAmbient R w n) hv
    rw [readAmbient_symbol, map_zero] at hh
    exact (Submodule.Quotient.mk_eq_zero _).mp hh
  · exact symbol_zero_of_mem R w

theorem orderedCoeff_mem_iff_zero (p q r s : ℕ) :
    orderedCoeff R w p q r s ∈ Pbelow R w (p + q + r) ↔
      gradedOrderedCoeff R w p q r s = 0 := by
  constructor
  · exact gradedOrderedCoeff_zero R w p q r s
  · intro hv
    apply (symbol_eq_zero_iff R w _ _).mp
    rw [← orderedCoeff_symbol, hv]
    rfl

end

end VOA.DeligneAudit.A2.CVRectFiltered

#print axioms VOA.DeligneAudit.A2.CVRectFiltered.symbol_eq_zero_iff
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.orderedCoeff_mem_iff_zero
