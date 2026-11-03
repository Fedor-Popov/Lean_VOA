/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateSortedData
import VOA.DeligneAudit.D4FusionRealizationTwoWordTable
import VOA.DeligneAudit.D4FusionRealizationTwoMatrixData

/-! Complete, explicitly indexed numerical obligations for the actual
841-word source and all its low-mode actions. -/
namespace VOA.DeligneAudit.D4Two.Certificate

def columnCheck (c : ℕ) : Bool :=
  (List.range 29).all fun i => (List.range 29).all fun j =>
    coeff (rawColumn c j) i ==
      if i < 28 ∧ j < 28 then -coeff (rawBracket c i) j else 0

def wordMetaCheck (i : ℕ) : Bool :=
  let e := wordNode i
  decide (e.level ≤ 4) && rangeCheck 841 e.vector

def wordStepCheck (i : ℕ) : Bool :=
  let e := wordNode i
  if i = 0 then e.level == 0 && sortedZero (e.vector ++ [(810, -1)])
  else
    let p := wordNode e.parent
    decide (e.parent < i) && decide (e.color < 28) &&
      e.level == p.level + e.mode &&
        sortedZero (e.vector ++ scale (-1)
          (applyColumns (pairColumn 28 (rawColumn e.color) e.color e.mode) p.vector))

def actionSource (i : ℕ) : ℕ := i % 841
def actionColor (i : ℕ) : ℕ := i / 841 % 28
def actionMode (i : ℕ) : ℕ := i / (841 * 28)

def wordCombination (terms : List (ℕ × ℤ)) : SV :=
  terms.flatMap fun p => scale p.2 (wordNode p.1).vector

/-- The case index itself fixes every colour, mode, and source word.
Thus covering the full dense range leaves no omitted action hypothesis. -/
def fullActionCheck (caseAt : ℕ → ActionCase) (i : ℕ) : Bool :=
  let a := caseAt i
  let source := wordNode (actionSource i)
  let c := actionColor i
  let k := actionMode i
  decide (a.denominator ≠ 0) &&
    (a.terms.all fun p => decide (p.1 < 841) &&
      (if source.level + k < 4 then decide ((wordNode p.1).level ≤ source.level + k)
       else true)) &&
    sortedZero (scale a.denominator
      (applyColumns (pairColumn 28 (rawColumn c) c k) source.vector) ++
      scale (-1) (wordCombination a.terms))

end VOA.DeligneAudit.D4Two.Certificate
