import VOA.DeligneAudit.LeviTypeA2CertKeyCartan

/-! The node-two raising current replaces a compound radical letter by a simple one. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V)

/-- The key after one `F₂` is replaced by `F₁`. -/
def a2KeyRaised (r : ℕ) (k : A2RadicalKey) : A2RadicalKey :=
  ⟨k.d₁ + 1, k.d₂ - 1, k.degree + r⟩

/-- The raising replacement strictly increases node-two height. -/
theorem a2KeyLess_raised (q r : ℕ) (k : A2RadicalKey)
    (hk : 0 < k.d₂) : a2KeyLess q k (a2KeyRaised r k) := by
  dsimp [a2KeyLess, a2KeyHeight, a2KeyRaised]
  left
  omega

/-- `e₂(r)` commutes with `F₁(s)`. -/
theorem a2_raising_simple_comm (r s : ℕ) :
    ρ.op 1 r * a2RadicalOp ρ 0 s -
      a2RadicalOp ρ 0 s * ρ.op 1 r = 0 := by
  change ρ.op 1 r * ρ.op 3 s - ρ.op 3 s * ρ.op 1 r = 0
  rw [op_comm_end]
  simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]

/-- `e₂(r)` replaces `F₂(s)` with `F₁(r+s)`. -/
theorem a2_raising_compound_comm (r s : ℕ) :
    ρ.op 1 r * a2RadicalOp ρ 1 s -
      a2RadicalOp ρ 1 s * ρ.op 1 r = a2RadicalOp ρ 0 (r + s) := by
  change ρ.op 1 r * ρ.op 5 s - ρ.op 5 s * ρ.op 1 r = ρ.op 3 (r + s)
  rw [op_comm_end]
  simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2KeyLess_raised
#print axioms VOA.DeligneAudit.A3Sector.a2_raising_simple_comm
#print axioms VOA.DeligneAudit.A3Sector.a2_raising_compound_comm
