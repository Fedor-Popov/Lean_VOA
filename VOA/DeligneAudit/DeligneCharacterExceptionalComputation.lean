/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalParameters

/-! Opaque certification combinators for the actual ordered Demazure algorithm. -/
namespace VOA.DeligneAudit.DeligneCharacter

def exceptionalSeed (theta : List ℤ) : LPoly :=
  [((List.replicate theta.length 0, 0), 1)]

def exceptionalCoeff (m N : ℕ) (values : LPoly) : ℕ :=
  ((values.filter fun (t : Term) => decide (t.1.2 + (m : ℤ) * m = N)).map
    fun (t : Term) => t.2).sum.toNat

theorem exceptional_fold_join (F : ℕ → LPoly → LPoly) (whole pre : List ℕ) (i : ℕ)
    (input middle output : LPoly) (hw : whole = pre ++ [i])
    (hs : F i input = middle) (hr : pre.foldr F middle = output) :
    whole.foldr F input = output := by
  rw [hw, List.foldr_append]
  simp only [List.foldr_cons, List.foldr_nil]
  rw [hs]
  exact hr

theorem exceptional_step_of_fold (A : List (List ℤ)) (theta : List ℤ) (word : List ℕ)
    (input middle output : LPoly) (hz : demazureZero A theta input = middle)
    (hf : word.foldr (demazureFin A) middle = output) :
    demazureStep A theta word input = output := by
  rw [demazureStep, hz]
  exact hf

theorem exceptional_character_one (A : List (List ℤ)) (theta : List ℤ) (word : List ℕ)
    (output : LPoly) (h : demazureStep A theta word (exceptionalSeed theta) = output) :
    demazureChar A theta word 1 = output := by
  change demazureStep A theta word (exceptionalSeed theta) = output
  exact h

theorem exceptional_character_two (A : List (List ℤ)) (theta : List ℤ) (word : List ℕ)
    (middle output : LPoly)
    (h1 : demazureStep A theta word (exceptionalSeed theta) = middle)
    (h2 : demazureStep A theta word middle = output) :
    demazureChar A theta word 2 = output := by
  change demazureStep A theta word (demazureStep A theta word (exceptionalSeed theta)) = output
  rw [h1, h2]

theorem exceptional_alias_coefficient (hilb : ℕ → ℕ → ℕ)
    (A : List (List ℤ)) (theta : List ℤ) (word : List ℕ)
    (hdef : ∀ m N, hilb m N = levelOneDemazureHilb A theta word m N)
    (m N : ℕ) (values : LPoly) (value : ℕ)
    (hchar : demazureChar A theta word m = values)
    (hcoeff : exceptionalCoeff m N values = value) : hilb m N = value := by
  rw [hdef, levelOneDemazureHilb, hchar]
  exact hcoeff

end VOA.DeligneAudit.DeligneCharacter
