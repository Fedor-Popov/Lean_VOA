import VOA.DeligneAudit.D4FusionContactAllMCountResearchInteger

/-! # Short quadratic pieces of the corrected-current wheel

Each polar piece has one lower and one top endpoint multiplier. Each
square piece begins with the positive Cartan-current derivative. This
normal form retains the location of every middle-mode correction.
-/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.D4FusionContact.M2Certificate

noncomputable section

def leviIndex : Fin 3 → Fin 36 := ![14,16,18]

def leviOrbit : List (Fin 3) → IntegerExpr → IntegerExpr
  | [], e => e
  | i::l, e => .deriv (leviIndex i) (leviOrbit l e)

inductive WheelPiece where
  | polar (coefficient : ℤ) (first second : Fin 8) (word : List (Fin 3))
  | square (coefficient : ℤ) (first second : Fin 8) (word : List (Fin 3))

def WheelPiece.expression : WheelPiece → IntegerExpr
  | .polar z i j l => .scale z (.mul (flatten i.castSucc 0)
      (.mul (flatten j.castSucc 1) (leviOrbit l .base)))
  | .square z i j l => .scale z (.mul (flatten i.castSucc 0)
      (.mul (flatten j.castSucc 0) (leviOrbit l (.deriv 3 .base))))

def piecesExpression (l : List WheelPiece) : IntegerExpr :=
  (l.map WheelPiece.expression).foldr IntegerExpr.plus (.scale 0 .base)

end
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch
