/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.Order.Ring.Int

/-!
# Boolean nilpotency certificates (light import)

The `Bool` checks behind `known_of_certValid` (`DeligneFusionFiniteGNil`), stated for a bare weight
function `wt : Fin n → Fin R → ℤ` and a nonzero-structure-constant predicate `fnz`, so that the
kernel checks of large types (`E₇`, `E₈`) import only this file and the data tables.

* `singleChk wt X a b`: `b` is the only basis vector of weight `wt X + wt a`;
* `topChk wt X a`: no basis vector has weight `wt X + wt a`;
* `pathChk wt fnz X a path`: the `ad X`-string from `a` along `path`;
* `certKnown kn cert`, `certValid wt fnz kn cert`; `certValid_append` splits a certificate.
-/

namespace VOA.DeligneAudit.FiniteG

/-- Equality of weights as a `Bool`. -/
def wEqB {R : ℕ} (u v : Fin R → ℤ) : Bool := (List.finRange R).all fun i => u i == v i

theorem wEqB_iff {R : ℕ} (u v : Fin R → ℤ) : wEqB u v = true ↔ u = v := by
  simp only [wEqB, List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies]
  exact ⟨fun h => funext h, fun h i => h ▸ rfl⟩

variable {n R : ℕ}

/-- `[X, a]` is a multiple of the single basis vector `b` (weights). -/
def singleChk (wt : Fin n → Fin R → ℤ) (X a b : Fin n) : Bool :=
  (List.finRange n).all fun c => c == b || !wEqB (wt c) (wt X + wt a)

/-- `[X, a] = 0` (weights). -/
def topChk (wt : Fin n → Fin R → ℤ) (X a : Fin n) : Bool :=
  (List.finRange n).all fun c => !wEqB (wt c) (wt X + wt a)

/-- The `ad X`-string from `a` along `path`: single basis vectors, nonzero structure constants
(certified by `fnz`), and a stop. -/
def pathChk (wt : Fin n → Fin R → ℤ) (fnz : Fin n → Fin n → Fin n → Bool) (X : Fin n) :
    Fin n → List (Fin n) → Bool
  | a, [] => topChk wt X a
  | a, b :: rest => singleChk wt X a b && fnz X a b && pathChk wt fnz X b rest

/-- A chain step `(X, Y, path)`. -/
abbrev Step (n : ℕ) := Fin n × Fin n × List (Fin n)

/-- The known set after a certificate. -/
def certKnown (kn : Fin n → Bool) : List (Step n) → Fin n → Bool
  | [] => kn
  | (_, Y, p) :: rest => certKnown (fun c => kn c || c == p.getLastD Y) rest

/-- Validity of a certificate from the known set `kn`. -/
def certValid (wt : Fin n → Fin R → ℤ) (fnz : Fin n → Fin n → Fin n → Bool) (kn : Fin n → Bool) :
    List (Step n) → Bool
  | [] => true
  | (X, Y, p) :: rest => kn X && kn Y && !wEqB (wt Y) 0 && pathChk wt fnz X Y p &&
      certValid wt fnz (fun c => kn c || c == p.getLastD Y) rest

theorem certKnown_append :
    ∀ (kn : Fin n → Bool) (l₁ l₂ : List (Step n)),
      certKnown kn (l₁ ++ l₂) = certKnown (certKnown kn l₁) l₂
  | _, [], _ => rfl
  | kn, (_, Y, p) :: l₁, l₂ => certKnown_append (fun c => kn c || c == p.getLastD Y) l₁ l₂

/-- A certificate can be checked in pieces. -/
theorem certValid_append (wt : Fin n → Fin R → ℤ) (fnz : Fin n → Fin n → Fin n → Bool) :
    ∀ (kn : Fin n → Bool) (l₁ l₂ : List (Step n)),
      certValid wt fnz kn (l₁ ++ l₂) =
        (certValid wt fnz kn l₁ && certValid wt fnz (certKnown kn l₁) l₂)
  | _, [], _ => by simp [certValid, certKnown]
  | kn, (X, Y, p) :: l₁, l₂ => by
      simp only [List.cons_append, certValid, certKnown,
        certValid_append wt fnz (fun c => kn c || c == p.getLastD Y) l₁ l₂, Bool.and_assoc]

end VOA.DeligneAudit.FiniteG
