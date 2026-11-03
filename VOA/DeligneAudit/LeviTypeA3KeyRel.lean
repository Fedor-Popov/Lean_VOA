import VOA.DeligneAudit.LeviTypeA3KeySharpQuot

/-! A key class is a local Weyl vector for the embedded `sl₃[t]`. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_key_A2_localWeyl (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (k : A3RadicalKey) {v : V} (hv : v ∈ a3KeyLayer ρ w k)
    (hp : 0 ≤ a3KeyLabelInt b c 0 k)
    (hq : 0 ≤ a3KeyLabelInt b c 1 k) :
    A2LocalWeylRel (a3KeyLeviQuotCurrent ρ w b c k)
      ((a3HigherLeviClosure ρ w b c k).mkQ v)
      (a3KeyLabelInt b c 0 k).toNat (a3KeyLabelInt b c 1 k).toNat := by
  let N := a3HigherLeviClosure ρ w b c k
  let Q := a3KeyLeviQuotCurrent ρ w b c k
  have hsharp0 := a3_key_lowering_sharp_quot ρ w a b c h 0 k hv
  have hsharp1 := a3_key_lowering_sharp_quot ρ w a b c h 1 k hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he r
    fin_cases e <;> norm_num at he
    · exact a3_key_raising_quot ρ w a b c h 0 r k hv
    · exact a3_key_raising_quot ρ w a b c h 2 r k hv
    · exact a3_key_raising_quot ρ w a b c h 1 r k hv
  · intro e he r hr
    fin_cases e <;> norm_num at he
    · exact a3_key_cartan_pos_quot ρ w a b c h 0 r hr k hv
    · exact a3_key_cartan_pos_quot ρ w a b c h 1 r hr k hv
  · have hc := a3_key_cartan_zero_quot ρ w a b c h 0 k hv
    have hcast : ((a3KeyLabelInt b c 0 k).toNat : ℂ) =
        (a3KeyLabelInt b c 0 k : ℂ) := by
      exact_mod_cast (Int.toNat_of_nonneg hp)
    simpa [a3KeyLabel_eq_int, hcast] using hc
  · have hc := a3_key_cartan_zero_quot ρ w a b c h 1 k hv
    have hcast : ((a3KeyLabelInt b c 1 k).toNat : ℂ) =
        (a3KeyLabelInt b c 1 k : ℂ) := by
      exact_mod_cast (Int.toNat_of_nonneg hq)
    simpa [a3KeyLabel_eq_int, hcast] using hc
  · exact hsharp0.2 hp
  · exact hsharp1.2 hq

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_key_A2_localWeyl
