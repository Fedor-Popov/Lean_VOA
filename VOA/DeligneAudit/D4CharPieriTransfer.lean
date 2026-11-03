import VOA.DeligneAudit.D4CharGTDual

/-!
# The two-state transfer argument in Lemma E

Pairs are row vectors. `pieriLeftStep`, `pieriRightStep`, and `pieriGauge` are multiplication
by M, K, and G in STEP2 section 4. The only local hypothesis is the displayed relation
`(1-c)X = (1-beta)Y`. The chain theorem holds for every finite length.
This is the algebraic transfer engine, not yet the GT e-Pieri theorem.
-/

namespace VOA.DeligneAudit.D4Char

variable {R : Type*} [CommRing R]

def pieriLeftStep (z c X Y : R) (v : R × R) : R × R :=
  (v.1 * X + v.2 * (c * X + Y), v.1 * z * (1 - c) * X + v.2 * z * Y)

def pieriRightStep (z cp beta X Y : R) (v : R × R) : R × R :=
  ((v.1 + v.2) * X, (v.1 * (1 - cp * beta) + v.2) * z * Y)

def pieriGauge (z c : R) (v : R × R) : R × R :=
  (v.1 * (1 + z * c) + v.2, v.1 * z * (1 - c) + v.2 * z)

/-- Initial row identity `(1,z) M = (X,zY) G`. -/
theorem pieri_initial (z c X Y : R) :
    pieriLeftStep z c X Y (1, z) = pieriGauge z c (X, z * Y) := by
  ext <;> simp only [pieriLeftStep, pieriGauge] <;> ring

/-- The local identity `G_previous M = K G`. -/
theorem pieri_intertwine (z cp c beta X Y : R) (v : R × R)
    (h : (1 - c) * X = (1 - beta) * Y) :
    pieriLeftStep z c X Y (pieriGauge z cp v) =
      pieriGauge z c (pieriRightStep z cp beta X Y v) := by
  apply Prod.ext
  · dsimp [pieriLeftStep, pieriGauge, pieriRightStep]
    linear_combination v.1 * z * cp * h
  · dsimp [pieriLeftStep, pieriGauge, pieriRightStep]
    linear_combination v.1 * z ^ 2 * cp * h

/-- Both row sums of G are `1+z`. -/
theorem pieri_terminal (z c : R) (v : R × R) :
    (pieriGauge z c v).1 + (pieriGauge z c v).2 = (1 + z) * (v.1 + v.2) := by
  dsimp [pieriGauge]
  ring

/-- One edge of the transfer chain, carrying its local algebraic relation. -/
structure PieriEdge (R : Type*) [CommRing R] where
  c : R
  beta : R
  X : R
  Y : R
  balance : (1 - c) * X = (1 - beta) * Y

def pieriLeftRun (z : R) : List (PieriEdge R) → (R × R) → R × R
  | [], v => v
  | e :: es, v => pieriLeftRun z es (pieriLeftStep z e.c e.X e.Y v)

def pieriRightRun (z : R) : R → List (PieriEdge R) → (R × R) → R × R
  | _, [], v => v
  | cp, e :: es, v =>
      pieriRightRun z e.c es (pieriRightStep z cp e.beta e.X e.Y v)

def pieriLast : R → List (PieriEdge R) → R
  | cp, [] => cp
  | _, e :: es => pieriLast e.c es

/-- Telescoping the local intertwining identity, for every chain length. -/
theorem pieri_run_gauge (z cp : R) (es : List (PieriEdge R)) (v : R × R) :
    pieriLeftRun z es (pieriGauge z cp v) =
      pieriGauge z (pieriLast cp es) (pieriRightRun z cp es v) := by
  induction es generalizing cp v with
  | nil => rfl
  | cons e es ih =>
      simp only [pieriLeftRun, pieriRightRun, pieriLast]
      rw [pieri_intertwine z cp e.c e.beta e.X e.Y v e.balance, ih]

/-- The scalar E-step transfer identity, before substituting the Gaussian entries. -/
theorem pieri_transfer_chain (z : R) (e : PieriEdge R) (es : List (PieriEdge R)) :
    (pieriLeftRun z (e :: es) (1, z)).1 +
      (pieriLeftRun z (e :: es) (1, z)).2 =
    (1 + z) * ((pieriRightRun z e.c es (e.X, z * e.Y)).1 +
      (pieriRightRun z e.c es (e.X, z * e.Y)).2) := by
  simp only [pieriLeftRun]
  rw [pieri_initial, pieri_run_gauge, pieri_terminal]

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.pieri_initial
#print axioms VOA.DeligneAudit.D4Char.pieri_intertwine
#print axioms VOA.DeligneAudit.D4Char.pieri_terminal
#print axioms VOA.DeligneAudit.D4Char.pieri_run_gauge
#print axioms VOA.DeligneAudit.D4Char.pieri_transfer_chain
