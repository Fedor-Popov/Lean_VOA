import VOA.DeligneAudit.DeligneSectorD4TableData

/-! A single nonzero bracket for each colour of the D4 Chevalley basis. -/

namespace VOA.DeligneAudit.Toroidal.D4

open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse

/-- The two basis colours whose bracket is a nonzero multiple of the given colour. -/
def bracketPair (c : Fin 28) : Fin 28 × Fin 28 :=
  match c.val with
  | 0 => (7, 19)
  | 1 => (6, 18)
  | 2 => (5, 17)
  | 3 => (4, 16)
  | 4 => (1, 4)
  | 5 => (1, 5)
  | 6 => (0, 6)
  | 7 => (0, 7)
  | 8 => (0, 8)
  | 9 => (0, 9)
  | 10 => (0, 10)
  | 11 => (0, 11)
  | 12 => (0, 12)
  | 13 => (0, 13)
  | 14 => (0, 14)
  | 15 => (1, 15)
  | 16 => (1, 16)
  | 17 => (1, 17)
  | 18 => (0, 18)
  | 19 => (0, 19)
  | 20 => (0, 20)
  | 21 => (0, 21)
  | 22 => (0, 22)
  | 23 => (0, 23)
  | 24 => (0, 24)
  | 25 => (0, 25)
  | 26 => (0, 26)
  | _ => (1, 27)

/-- Every chosen bracket has a nonzero coefficient at its target colour. -/
theorem bracketPair_nonzero :
    ∀ c : Fin 28, fZ br (bracketPair c).1 (bracketPair c).2 c ≠ 0 := by
  decide +kernel

/-- Every chosen bracket has no other colour component. -/
theorem bracketPair_off :
    ∀ c e : Fin 28, e ≠ c → fZ br (bracketPair c).1 (bracketPair c).2 e = 0 := by
  decide +kernel

end VOA.DeligneAudit.Toroidal.D4

#print axioms VOA.DeligneAudit.Toroidal.D4.bracketPair_nonzero
#print axioms VOA.DeligneAudit.Toroidal.D4.bracketPair_off
