import VOA.DeligneAudit.LeviTypeA3Current

/-! The `sl₃[t]` action on quotients by stable Levi subspaces. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V)

/-- The quotient of the embedded `sl₃[t]` current action. -/
def a3LeviQuotCurrent (N : Submodule ℂ V)
    (hN : ∀ a r, N ≤ N.comap (ρ.op (a3LeviColour a) r)) :
    CurrentModule VOA.AffineSl3.bracketTable (V ⧸ N) :=
  VOA.DeligneAudit.UnivG.quotRepG (a3LeviCurrent ρ) N hN

theorem a3LeviQuotCurrent_op (N : Submodule ℂ V)
    (hN : ∀ a r, N ≤ N.comap (ρ.op (a3LeviColour a) r))
    (a : Fin 8) (r : ℕ) (v : V) :
    (a3LeviQuotCurrent ρ N hN).op a r (N.mkQ v) =
      N.mkQ (ρ.op (a3LeviColour a) r v) := rfl

/-- The canonical quotient by the closure of any Levi subspace. -/
def a3LeviClosureQuotCurrent (S : Submodule ℂ V) :
    CurrentModule VOA.AffineSl3.bracketTable (V ⧸ a3LeviClosure ρ S) :=
  a3LeviQuotCurrent ρ (a3LeviClosure ρ S)
    (fun a r => a3LeviClosure_inv ρ S a r)

theorem a3LeviClosureQuotCurrent_op (S : Submodule ℂ V)
    (a : Fin 8) (r : ℕ) (v : V) :
    (a3LeviClosureQuotCurrent ρ S).op a r
      ((a3LeviClosure ρ S).mkQ v) =
        (a3LeviClosure ρ S).mkQ (ρ.op (a3LeviColour a) r v) := rfl

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3LeviQuotCurrent
#print axioms VOA.DeligneAudit.A3Sector.a3LeviQuotCurrent_op
#print axioms VOA.DeligneAudit.A3Sector.a3LeviClosureQuotCurrent
#print axioms VOA.DeligneAudit.A3Sector.a3LeviClosureQuotCurrent_op
