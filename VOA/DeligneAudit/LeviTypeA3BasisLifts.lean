import VOA.DeligneAudit.LeviTypeA3HigherPrefix
import VOA.DeligneAudit.LeviTypeA2CertBasisLifts

/-! Basis lifts for one finite key layer modulo an earlier prefix. -/

namespace VOA.DeligneAudit.A3Sector

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem a3_keyQuot_basis_lifts (F S : Submodule ℂ V)
    [FiniteDimensional ℂ S] :
    ∃ v : Fin (Module.finrank ℂ (S ⧸ F.comap S.subtype)) → S,
      S ≤ F ⊔ Submodule.span ℂ (Set.range fun j => (v j : V)) :=
  a2_keyQuot_basis_lifts F S

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_keyQuot_basis_lifts
