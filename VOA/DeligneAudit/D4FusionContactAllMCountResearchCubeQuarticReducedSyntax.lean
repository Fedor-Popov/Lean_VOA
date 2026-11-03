import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedRows
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin

/-! Pure syntax for the checked cube and unbounded ordinary jets.
This light module keeps finite integer cancellation apart from D4 tables. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced
open QuarticReducedRows

def rowNext : Fin 3 → Fin 8 → Option (Fin 8) := ![
  ![some 1,none,some 3,none,some 5,none,some 7,none],
  ![some 2,some 3,none,none,some 6,some 7,none,none],
  ![some 4,some 5,some 6,some 7,none,none,none,none]]

def lowerStep (d : Fin 3) (i : Fin 8) : Row (Fin 8) :=
  match rowNext d i with
  | none => []
  | some j => [([j],1)]

def orbitRow (r a b c : ℕ) : Row (Fin 8) :=
  ((deriv (lowerStep 2) : _ → _)^[c])
    (((deriv (lowerStep 1) : _ → _)^[b])
      (((deriv (lowerStep 0) : _ → _)^[a]) [(List.replicate r 0,1)]))

def jetStep (n : ℕ) : Row ℕ := [([n+8],1)]

def jetRow (j r a b c : ℕ) : Row ℕ :=
  ((deriv jetStep : Row ℕ → Row ℕ)^[j])
    (QuarticReducedRows.map Fin.val (orbitRow r a b c))

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced
