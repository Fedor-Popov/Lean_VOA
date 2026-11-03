import VOA.DeligneAudit.LeviTypeA3GradedOrderedCount
import VOA.DeligneAudit.LeviTypeA3TerminalFinite

/-! The all-weight rank theorem reduces exactly to the fixed-key KS bound. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- The remaining fixed-key three-box inequality suffices for the full
all-weight type-A₃ cyclic rank bound. -/
theorem a3_all_weight_rank_of_ks (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (hKS : ∀ i : Fin ((a3KeyBox a b c).card),
      Module.finrank ℂ
        (a3KeyLayer ρ w (a3KeyEnum a b c i) ⧸
          (a3KeyPrefix ρ w (a3KeyEnum a b c) i.val).comap
            (a3KeyLayer ρ w (a3KeyEnum a b c i)).subtype) ≤
        a3EffectiveMultiplicity a b c (a3KeyEnum a b c i)) :
    FiniteDimensional ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) ∧
      Module.finrank ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) ≤
        4 ^ a * 6 ^ b * 4 ^ c := by
  obtain ⟨hfinite, hraw⟩ :=
    a3_all_weight_finite_and_raw_sum ρ w a b c h
  refine ⟨hfinite, ?_⟩
  calc
    Module.finrank ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) ≤
        ∑ i : Fin ((a3KeyBox a b c).card),
          a3KeyOrbitLength b c (a3KeyEnum a b c i) *
            Module.finrank ℂ
              (a3KeyLayer ρ w (a3KeyEnum a b c i) ⧸
                (a3KeyPrefix ρ w (a3KeyEnum a b c) i.val).comap
                  (a3KeyLayer ρ w (a3KeyEnum a b c i)).subtype) := hraw
    _ ≤ ∑ i : Fin ((a3KeyBox a b c).card),
          a3KeyOrbitLength b c (a3KeyEnum a b c i) *
            a3EffectiveMultiplicity a b c (a3KeyEnum a b c i) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.mul_le_mul_left _ (hKS i)
    _ ≤ 4 ^ a * 6 ^ b * 4 ^ c := a3_ordered_key_count_power a b c

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_all_weight_rank_of_ks
