import VOA.DeligneAudit.D4LeviKeyRel

/-! The remaining gl4 Cartan colour acts diagonally on the six radical letters. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.DeligneSector.Sparse

def extraWeight : Fin 6 → ℤ
  | 0 => -2
  | 1 | 2 | 3 | 4 => -1
  | 5 => 0

def extraLabel (k : RadicalKey) : ℤ :=
  -2 * k.e - k.x - k.u - k.up - k.y

theorem extra_bracket (j : Fin 6) :
    VOA.DeligneAudit.DeligneSector.D4.br 0 (radicalColour j) =
      if extraWeight j = 0 then [] else
        [((radicalColour j).val, extraWeight j)] := by
  fin_cases j <;> decide

set_option maxHeartbeats 8000000 in
private theorem extra_coefficient_int : ∀ (j : Fin 6) (z : Fin 28),
    fZ VOA.DeligneAudit.DeligneSector.D4.br 0 (radicalColour j) z =
      if z = radicalColour j then extraWeight j else 0 := by
  decide +kernel

theorem extra_coefficient (j : Fin 6) (z : Fin 28) :
    VOA.DeligneAudit.DeligneSector.D4.fD4 0 (radicalColour j) z =
      if z = radicalColour j then (extraWeight j : ℂ) else 0 := by
  simpa only [VOA.DeligneAudit.DeligneSector.D4.fD4, fC,
    Int.cast_ite, Int.cast_zero] using
      congrArg (fun n : ℤ => (n : ℂ)) (extra_coefficient_int j z)

theorem extraLabel_cons (j : Fin 6) (s : ℕ)
    (l : List (Fin 6 × ℕ)) :
    extraLabel (wordKey ((j, s) :: l)) =
      extraLabel (wordKey l) + extraWeight j := by
  fin_cases j <;> simp [extraLabel, extraWeight, wordKey] <;> ring

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.extra_bracket
#print axioms VOA.DeligneAudit.D4Levi.extra_coefficient
#print axioms VOA.DeligneAudit.D4Levi.extraLabel_cons
