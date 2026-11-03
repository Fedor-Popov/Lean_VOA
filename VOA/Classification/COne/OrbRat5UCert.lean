import VOA.Classification.COne.OrbRat3Eval

/-! # The certified zero mode of the weight-nine generator on `J`

`U₍₈₎ J = -10800 E` in `V₈`, certified by `decide +kernel` against the
evaluator `actU` of `OrbRat3Eval`.  (`U = J₍₋₂₎E − E₍₋₂₎J`, `OrbC2e.weightNine`.)
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false

namespace VOA.Classification.COne.OrbRat5
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e LatMod OrbRat3

/-- `E = e^{β} + e^{-β}` as an executable state. -/
def EcSt : St := [(1, [(1, [])]), (-1, [(1, [])])]

/-- `J` as an executable state. -/
def JcSt : St := [(0, liftR JR)]

/-- Executable description of `U₍₈₎ J`. -/
def UJ : St := [(-2, []), (-1, [(-10800, [])]), (0, []), (1, [(-10800, [])]), (2, [])]

set_option maxHeartbeats 40000 in
-- memory guard (about 4 GB above the import baseline)
theorem cert_UJ : bucket [-2, -1, 0, 1, 2] (actU 8 8 JcSt) = UJ := by decide +kernel

end VOA.Classification.COne.OrbRat5
