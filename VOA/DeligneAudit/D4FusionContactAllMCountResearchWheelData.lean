import VOA.DeligneAudit.D4FusionContactAllMCountResearchPieces

/-! Exact 29-piece endpoint identity, checked as a finite integer word cancellation. -/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.M2Certificate

set_option linter.style.longLine false
set_option maxRecDepth 10000

def wheelPieces : List WheelPiece :=
  [.polar (-16) 7 1 [1, 2],
    .square (-4) 6 7 [0],
    .polar (16) 1 7 [1, 2],
    .square (-1) 0 1 [0, 1, 1, 2, 2],
    .polar (-4) 0 1 [0, 1, 1, 2, 2],
    .polar (-16) 6 7 [0],
    .square (-2) 1 2 [0, 1, 2, 2],
    .square (2) 1 3 [0, 1, 1, 2],
    .polar (-8) 2 6 [0, 0, 2],
    .polar (8) 3 6 [0, 0, 1],
    .polar (16) 5 4 [1, 2],
    .square (-2) 0 5 [0, 1, 1, 2],
    .polar (-4) 0 2 [0, 0, 1, 2, 2],
    .polar (-16) 7 5 [1],
    .square (-4) 2 7 [0, 2],
    .square (-4) 5 6 [0, 1],
    .polar (8) 5 1 [1, 1, 2],
    .polar (16) 4 5 [1, 2],
    .square (2) 0 4 [0, 1, 2, 2],
    .polar (4) 0 3 [0, 0, 1, 1, 2],
    .polar (16) 7 4 [2],
    .square (4) 3 7 [0, 1],
    .square (4) 4 6 [0, 2],
    .polar (-8) 4 1 [1, 2, 2],
    .square (2) 2 4 [0, 2, 2],
    .polar (8) 3 5 [0, 1, 1],
    .polar (-8) 2 4 [0, 2, 2],
    .polar (-16) 4 2 [0, 2, 2],
    .square (2) 3 5 [0, 1, 1]]

def integerWheel := piecesExpression wheelPieces

def wheelTarget : WordRow :=
  [([3,5,10,12],1), ([3,7,8,12],1), ([5,7,8,10],1)]

theorem integerWheel_check : collect (integerWheel.words ++ scaleRow (-32) wheelTarget) = [] := by
  decide +kernel

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch

#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.integerWheel_check
