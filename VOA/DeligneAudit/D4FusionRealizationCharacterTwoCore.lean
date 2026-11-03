import VOA.DeligneAudit.DeligneCharacterDemazure
import VOA.DeligneAudit.D4FusionRealizationSmallCharacter
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoStates

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

/-! Raw insertion retains zero terms, so chunk assembly preserves exact list order. -/
def rawPush (T : Term → LPoly) (input acc : LPoly) : LPoly :=
  (input.flatMap T).foldr addTerm acc

theorem rawPush_append (T : Term → LPoly) (xs ys acc : LPoly) :
    rawPush T (xs ++ ys) acc = rawPush T xs (rawPush T ys acc) := by
  simp only [rawPush, List.flatMap_append, List.foldr_append]

theorem finish_fin (A : List (List ℤ)) (i : ℕ) (input raw output : LPoly)
    (hp : rawPush (demazureFinTerm A i) input [] = raw)
    (hf : raw.filter (fun t => t.2 ≠ 0) = output) :
    demazureFin A i input = output := by
  change (rawPush (demazureFinTerm A i) input []).filter (fun t => t.2 ≠ 0) = output
  rw [hp, hf]

theorem finish_zero (A : List (List ℤ)) (theta : List ℤ) (input raw output : LPoly)
    (hp : rawPush (demazureZeroTerm A theta) input [] = raw)
    (hf : raw.filter (fun t => t.2 ≠ 0) = output) :
    demazureZero A theta input = output := by
  change (rawPush (demazureZeroTerm A theta) input []).filter (fun t => t.2 ≠ 0) = output
  rw [hp, hf]

def op00 : Term → LPoly := demazureZeroTerm cartan theta

def op01 : Term → LPoly := demazureFinTerm cartan 1

def op02 : Term → LPoly := demazureFinTerm cartan 0

def op03 : Term → LPoly := demazureFinTerm cartan 2

def op04 : Term → LPoly := demazureFinTerm cartan 1

def op05 : Term → LPoly := demazureFinTerm cartan 3

def op06 : Term → LPoly := demazureFinTerm cartan 1

def op07 : Term → LPoly := demazureFinTerm cartan 2

def op08 : Term → LPoly := demazureFinTerm cartan 0

def op09 : Term → LPoly := demazureFinTerm cartan 1

end VOA.DeligneAudit.D4CharacterTwo
