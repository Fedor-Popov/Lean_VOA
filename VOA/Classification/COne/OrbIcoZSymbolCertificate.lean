import VOA.Classification.COne.OrbIcoZSymbolVector10
import VOA.Classification.COne.OrbIcoZSpecialize

/-! Cached exact bivariate coefficients certify all mixed modes of the actual
level-thirteen singular-vector identity. Each word and vector assembly step
is checked in the Lean kernel in the imported finite certificates. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def rawSymbolRows : RawSym := vectorPartial10

def symbolRows : SymRel := symMap rawSymbolRows

set_option maxHeartbeats 2000000 in
theorem prefixVector10_eq_s13 : prefixVector10 = s13v := by
  decide +kernel

/-- The exact coefficients give genuine Zhu identities at every integer mode. -/
theorem symbolRows_holds (k : ℤ) : evalSym Wi k selfMode symbolRows = 0 := by
  have hp : ∀ m : ℕ, 1 ≤ m → Wi.L (m : ℤ) Xico = 0 := by
    intro m hm
    have h := ((OrbSpan.mem_prim _).mp X_primary).2 (m - 1)
    rwa [show ((m - 1 : ℕ) : ℤ) + 1 = m by omega] at h
  have hs : posV s13v = true := by
    simp only [posV, List.all_eq_true]
    intro p hp
    exact (s13v_spec p hp).2.2
  have he := vectorPartial10_sound Wi k selfMode
  rw [prefixVector10_eq_s13] at he
  unfold symbolRows rawSymbolRows
  rw [← he, ← symVector_sound Wi Xico_grading Xico_grading hp s13v hs,
    s13_zero, PreVertexAlgebra.smul_zero_right, map_zero]

/-- Rational integer specialization preserves the actual null relation. -/
theorem specializedNull_holds (k : ℤ) :
    evalRel Wi selfMode (specialize k rawSymbolRows) = 0 := by
  rw [evalSpecialize]
  exact symbolRows_holds k

end VOA.Classification.COne.OrbIcoZ
