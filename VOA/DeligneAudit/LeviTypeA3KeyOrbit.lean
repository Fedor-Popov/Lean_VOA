import VOA.DeligneAudit.LeviTypeA3KeyRel

/-! The full Levi current orbit of one key class has the `sl₃` Weyl bound. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_key_cyclic_rank (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (k : A3RadicalKey) {v : V} (hv : v ∈ a3KeyLayer ρ w k)
    (hp : 0 ≤ a3KeyLabelInt b c 0 k)
    (hq : 0 ≤ a3KeyLabelInt b c 1 k) :
    let Q := a3KeyLeviQuotCurrent ρ w b c k
    let x := (a3HigherLeviClosure ρ w b c k).mkQ v
    FiniteDimensional ℂ (VOA.DeligneAudit.UnivG.cycSubG Q x) ∧
      Module.finrank ℂ (VOA.DeligneAudit.UnivG.cycSubG Q x) ≤
        3 ^ (a3KeyLabelInt b c 0 k).toNat *
          3 ^ (a3KeyLabelInt b c 1 k).toNat := by
  exact a2_all_weight_rank _ _ _ _
    (a3_key_A2_localWeyl ρ w a b c h k hv hp hq)

theorem a3_key_negative_zero (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 2) (k : A3RadicalKey)
    {v : V} (hv : v ∈ a3KeyLayer ρ w k)
    (hi : a3KeyLabelInt b c i k < 0) :
    (a3HigherLeviClosure ρ w b c k).mkQ v = 0 :=
  (a3_key_lowering_sharp_quot ρ w a b c h i k hv).1 hi

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_key_cyclic_rank
#print axioms VOA.DeligneAudit.A3Sector.a3_key_negative_zero
