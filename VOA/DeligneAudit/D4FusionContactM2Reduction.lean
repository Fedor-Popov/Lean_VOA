import VOA.DeligneAudit.D4FusionContactM2ReductionCore
import VOA.DeligneAudit.D4FusionContactM2Packets
import VOA.DeligneAudit.D4FusionContactPolynomialCutoff

/-! The actual checked packets span the concrete m2 polynomial quotient.
This step uses no count, independence, finite-dimensionality or rank premise. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

/-- Actual normal-word spanning, ready for the independently checked
normalEnumeration length to give the numerical bound. -/
theorem m2_normalEnumeration_span :
    Submodule.span ℂ (Set.range fun i : Fin normalEnumeration.length =>
      (m2ModelIdeal.restrictScalars ℂ).mkQ
        (polyWord ((normalEnumeration.get i).map varIndex))) = ⊤ := by
  apply quotient_normal_words_span varIndex m2ModelIdeal
    (by intro x; exact ⟨flatten x.1 x.2, variable_flatten x.1 x.2⟩)
    packets leaders packets_heads
  · intro row hrow
    exact (show candidateIdeal ≤ m2ModelIdeal from le_sup_left)
      (List.forall_iff_forall_mem.mp packets_mem row hrow)
  · exact List.forall_iff_forall_mem.mp packets_reducing
  · intro l hl
    apply (show highWordIdeal 2 ≤ m2ModelIdeal from le_sup_right)
    exact Ideal.subset_span ⟨l.map varIndex, by simpa only [List.length_map] using hl, rfl⟩

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.m2_normalEnumeration_span
