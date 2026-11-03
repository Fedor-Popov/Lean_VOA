import VOA.DeligneAudit.D4LeviOrder

/-! Exact simple-Cartan weights of the six D4 radical colours. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.DeligneSector.Sparse

/-- The contribution of one radical letter to a simple sl4 Cartan label. -/
def letterWeight (i : Fin 3) (j : Fin 6) : ℤ :=
  keyLabel 0 i (wordKey [(j, 0)])

/-- The 18 Cartan brackets in the unrescaled D4 carrier basis. -/
theorem cartan_radical_bracket (i : Fin 3) (j : Fin 6) :
    VOA.DeligneAudit.DeligneSector.D4.br
      (leviColour (VOA.DeligneAudit.A3Sector.simpleH i))
      (radicalColour j) =
        if letterWeight i j = 0 then [] else
          [((radicalColour j).val, letterWeight i j)] := by
  fin_cases i <;> fin_cases j <;>
    decide

/-- Every simple-Cartan bracket is supported on its original radical colour. -/
theorem cartan_radical_support (i : Fin 3) (j : Fin 6) (z : Fin 28)
    (hz : z ≠ radicalColour j) :
    VOA.DeligneAudit.DeligneSector.D4.fD4
      (leviColour (VOA.DeligneAudit.A3Sector.simpleH i))
      (radicalColour j) z = 0 := by
  have hzn : (radicalColour j).val ≠ z.val := by
    intro h
    exact hz (Fin.ext h.symm)
  by_cases hzero : letterWeight i j = 0
  · simp [VOA.DeligneAudit.DeligneSector.D4.fD4, fC, fZ,
      cartan_radical_bracket, sget, hzero]
  · simp [VOA.DeligneAudit.DeligneSector.D4.fD4, fC, fZ,
      cartan_radical_bracket, sget, hzero, hzn]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.cartan_radical_bracket
#print axioms VOA.DeligneAudit.D4Levi.cartan_radical_support
