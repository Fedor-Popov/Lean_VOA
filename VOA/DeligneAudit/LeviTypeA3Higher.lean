import VOA.DeligneAudit.LeviTypeA3KeyInsert

/-! Strictly higher keys and the changes produced by Levi raising currents. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

def a3KeyShift (r : ℕ) (k : A3RadicalKey) : A3RadicalKey :=
  { k with degree := k.degree + r }

def a3KeyRaisedOne (r : ℕ) (k : A3RadicalKey) : A3RadicalKey :=
  ⟨k.d₁ + 1, k.d₂ - 1, k.d₃, k.degree + r⟩

def a3KeyRaisedTwo (r : ℕ) (k : A3RadicalKey) : A3RadicalKey :=
  ⟨k.d₁, k.d₂ + 1, k.d₃ - 1, k.degree + r⟩

theorem a3KeyLess_raised_one (b c r : ℕ) (k : A3RadicalKey)
    (hk : 0 < k.d₂) : a3KeyLess b c k (a3KeyRaisedOne r k) := by
  dsimp [a3KeyLess, a3KeyHeight, a3KeyRaisedOne]
  left
  omega

theorem a3KeyLess_raised_two (b c r : ℕ) (k : A3RadicalKey)
    (hk : 0 < k.d₃) : a3KeyLess b c k (a3KeyRaisedTwo r k) := by
  dsimp [a3KeyLess, a3KeyHeight, a3KeyRaisedTwo]
  left
  omega

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- The span of radical layers strictly higher in the total key order. -/
def a3HigherKeySpan (b c : ℕ) (k : A3RadicalKey) : Submodule ℂ V :=
  ⨆ (j : A3RadicalKey) (_ : a3KeyLess b c k j), a3KeyLayer ρ w j

theorem a3KeyLayer_le_higher (b c : ℕ) (k j : A3RadicalKey)
    (hj : a3KeyLess b c k j) :
    a3KeyLayer ρ w j ≤ a3HigherKeySpan ρ w b c k := by
  unfold a3HigherKeySpan
  exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)

/-- Higher keys form a stable quotient after taking Levi closure. -/
def a3HigherLeviClosure (b c : ℕ) (k : A3RadicalKey) : Submodule ℂ V :=
  a3LeviClosure ρ (a3HigherKeySpan ρ w b c k)

theorem a3HigherLeviClosure_contains (b c : ℕ) (k : A3RadicalKey) :
    a3HigherKeySpan ρ w b c k ≤ a3HigherLeviClosure ρ w b c k :=
  a3LeviClosure_contains ρ _

theorem a3HigherLeviClosure_inv (b c : ℕ) (k : A3RadicalKey)
    (a : Fin 8) (r : ℕ) :
    a3HigherLeviClosure ρ w b c k ≤
      (a3HigherLeviClosure ρ w b c k).comap (ρ.op (a3LeviColour a) r) :=
  a3LeviClosure_inv ρ _ a r

/-- The standard `sl₃[t]` action on the quotient above a key. -/
def a3KeyLeviQuotCurrent (b c : ℕ) (k : A3RadicalKey) :
    CurrentModule VOA.AffineSl3.bracketTable
      (V ⧸ a3HigherLeviClosure ρ w b c k) :=
  a3LeviQuotCurrent ρ _ (fun a r => a3HigherLeviClosure_inv ρ w b c k a r)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3KeyLess_raised_one
#print axioms VOA.DeligneAudit.A3Sector.a3KeyLess_raised_two
#print axioms VOA.DeligneAudit.A3Sector.a3KeyLayer_le_higher
#print axioms VOA.DeligneAudit.A3Sector.a3HigherLeviClosure_contains
#print axioms VOA.DeligneAudit.A3Sector.a3HigherLeviClosure_inv
#print axioms VOA.DeligneAudit.A3Sector.a3KeyLeviQuotCurrent
