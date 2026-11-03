import VOA.DeligneAudit.D4FusionContactM2Packets
import VOA.DeligneAudit.D4FusionContactM2CountBound

/-! # Dimension consequences of an actual finite normal span

Finiteness is derived from the spanning vectors, never assumed of the
ambient quotient. The later concrete m=2 application supplies the checked
normal-word span and the exact cardinality 784.
-/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {N : ℕ}

theorem finite_finrank_le_of_span_fin (v : Fin N → V)
    (hspan : Submodule.span ℂ (Set.range v) = ⊤) :
    FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤ N := by
  let P := Submodule.span ℂ (Set.range v)
  letI : FiniteDimensional ℂ P :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hsurj : Function.Surjective P.subtype := by
    intro x
    refine ⟨⟨x,?_⟩,rfl⟩
    rw [show P = ⊤ from hspan]
    exact Submodule.mem_top
  letI : FiniteDimensional ℂ V := Module.Finite.of_surjective P.subtype hsurj
  refine ⟨inferInstance,?_⟩
  have hr := finrank_range_le_card (R := ℂ) v
  change Module.finrank ℂ (Submodule.span ℂ (Set.range v)) ≤ Fintype.card (Fin N) at hr
  rw [hspan,finrank_top] at hr
  simpa only [Fintype.card_fin] using hr

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.finite_finrank_le_of_span_fin
