/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation

/-!
# Light-import copies of the Demazure algorithm (for the E₈ chunked checks)

`DeligneCharacterDemazure` imports all of `Mathlib`, which costs about 5.6 GB of RSS before any work. The
pinned `C_1` chain and the invariance checks therefore use verbatim copies of the computable definitions,
importing only the `ℕ`/`ℤ` notation files.

The copies are:
- from `DeligneCharacterDemazure`: `addTerm`, `normalize`, `pairCoroot`, `shiftAt`, `shiftTheta`,
  `demazureFinTerm`, `demazureZeroTerm`, `demazureFin`, `demazureZero`;
- from `DeligneCharacterDemazureCount`: `aTheta`, `reflFin`, `reflZero`, `memCheck`;
- from `DeligneCharacterExceptional`: `cartanE8`, `thetaE8`.

`DeligneCharacterE8Count` identifies each copy with its original (`*_eq` lemmas: `rfl`, or induction for the
structurally recursive `addTerm`).
-/

namespace VOA.DeligneAudit.DeligneCharacter.E8L

/-- Copy of `Term`. -/
abbrev TermL := (List ℤ × ℤ) × ℤ

/-- Copy of `LPoly`. -/
abbrev LPolyL := List TermL

/-- Copy of `addTerm`. -/
def addTermL : TermL → LPolyL → LPolyL
  | t, [] => [t]
  | t, s :: rest => if t.1 = s.1 then (t.1, t.2 + s.2) :: rest else s :: addTermL t rest

/-- Copy of `normalize`. -/
def normalizeL (f : LPolyL) : LPolyL :=
  (f.foldr addTermL []).filter fun t => t.2 ≠ 0

/-- Copy of `pairCoroot`. -/
def pairCorootL (A : List (List ℤ)) (i : ℕ) (μ : List ℤ) : ℤ :=
  ((A.getD i []).zipWith (· * ·) μ).sum

/-- Copy of `shiftAt`. -/
def shiftAtL (μ : List ℤ) (i : ℕ) (c : ℤ) : List ℤ :=
  μ.mapIdx fun j x => if j = i then x + c else x

/-- Copy of `shiftTheta`. -/
def shiftThetaL (μ θ : List ℤ) (c : ℤ) : List ℤ := List.zipWith (fun x t => x + c * t) μ θ

/-- Copy of `demazureFinTerm`. -/
def demazureFinTermL (A : List (List ℤ)) (i : ℕ) (t : TermL) : LPolyL :=
  let μ := t.1.1
  let n := pairCorootL A i μ
  if 0 ≤ n then
    (List.range (n.toNat + 1)).map fun (k : ℕ) => ((shiftAtL μ i (-(k : ℤ)), t.1.2), t.2)
  else
    (List.range ((-n).toNat - 1)).map fun (k : ℕ) => ((shiftAtL μ i ((k : ℤ) + 1), t.1.2), -t.2)

/-- Copy of `demazureZeroTerm`. -/
def demazureZeroTermL (A : List (List ℤ)) (θ : List ℤ) (t : TermL) : LPolyL :=
  let μ := t.1.1
  let Aθ := (List.range θ.length).map fun i => pairCorootL A i θ
  let n := 1 - (List.zipWith (· * ·) Aθ μ).sum
  if 0 ≤ n then
    (List.range (n.toNat + 1)).map fun (k : ℕ) => ((shiftThetaL μ θ k, t.1.2 - k), t.2)
  else
    (List.range ((-n).toNat - 1)).map fun (k : ℕ) =>
      ((shiftThetaL μ θ (-((k : ℤ) + 1)), t.1.2 + ((k : ℤ) + 1)), -t.2)

/-- Copy of `demazureFin`. -/
def demazureFinL (A : List (List ℤ)) (i : ℕ) (f : LPolyL) : LPolyL :=
  normalizeL (f.flatMap (demazureFinTermL A i))

/-- Copy of `demazureZero`. -/
def demazureZeroL (A : List (List ℤ)) (θ : List ℤ) (f : LPolyL) : LPolyL :=
  normalizeL (f.flatMap (demazureZeroTermL A θ))

/-- Copy of `DemCount.aTheta`. -/
def aThetaL (A : List (List ℤ)) (θ : List ℤ) : List ℤ :=
  (List.range θ.length).map fun i => pairCorootL A i θ

/-- Copy of `DemCount.reflFin`. -/
def reflFinL (A : List (List ℤ)) (i : ℕ) (μ : List ℤ) : List ℤ := shiftAtL μ i (-pairCorootL A i μ)

/-- Copy of `DemCount.reflZero`. -/
def reflZeroL (A : List (List ℤ)) (θ : List ℤ) (μ : List ℤ) : List ℤ :=
  shiftThetaL μ θ (-(List.zipWith (· * ·) (aThetaL A θ) μ).sum)

/-- Copy of `DemCount.memCheck`. -/
def memCheckL (g : List ℤ → List ℤ) (f : LPolyL) : Bool :=
  f.all fun t => decide (((g t.1.1, t.1.2), t.2) ∈ f)

/-- Copy of `cartanE8`. -/
def cartanE8L : List (List ℤ) :=
  [[2, 0, -1, 0, 0, 0, 0, 0], [0, 2, 0, -1, 0, 0, 0, 0], [-1, 0, 2, -1, 0, 0, 0, 0],
   [0, -1, -1, 2, -1, 0, 0, 0], [0, 0, 0, -1, 2, -1, 0, 0], [0, 0, 0, 0, -1, 2, -1, 0],
   [0, 0, 0, 0, 0, -1, 2, -1], [0, 0, 0, 0, 0, 0, -1, 2]]

/-- Copy of `thetaE8`. -/
def thetaE8L : List ℤ := [2, 3, 4, 6, 5, 4, 3, 2]

end VOA.DeligneAudit.DeligneCharacter.E8L
