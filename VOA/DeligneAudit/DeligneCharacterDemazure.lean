/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib

/-!
# Computable level-one affine Demazure characters

For a simple Lie algebra with Cartan matrix `A` (as lists), highest root `θ` in
simple-root coordinates, and a reduced word for the reflection `s_θ`, this file computes

  `C_m = q^{m²} (D_{s_θ} D_0)^m e^{Λ₀}`,

the affine Demazure character of `V_{(s_θ s_0)^m}(Λ₀)`, by the affine Demazure character formula
`D_i e^λ = (e^λ - e^{-α_i} e^{s_i λ})/(1 - e^{-α_i})`, applied monomialwise through the
`α_i`-string formula.  Weights are stored in simple-root coordinates, together with the `q`-exponent
(`e^{-δ} ↦ q`… precisely `e^{-α₀} = q^{-1} z^θ`).  The unflavoured Hilbert series is `C_m|_{z = 1}`.

**Inputs used to read the output as `Hilb_q D(1,mθ)`** (not formalized): the affine Demazure
character formula (Kumar 1987, Mathieu 1988), and the identification of Ravinder's module
`D(1,mθ)` with `V_{(s_θ s_0)^m}(Λ₀)`, with the extremal vector in degree `0` (Fourier–Littelmann,
Chari–Venkatesh).  In Lean the function is just the algorithm.  It is written for the simply-laced
case but is also used for `G₂` and `F₄`; `DeligneCharacterExceptional.lean` explains why it is valid
there (`θ` long, the affine node attached to a long root).

Everything is `List`-based and computable, so kernel `decide` can check small cases.
-/

namespace VOA.DeligneAudit.DeligneCharacter

/-- A monomial `z^μ q^e` with integer coefficient. -/
abbrev Term := (List ℤ × ℤ) × ℤ

/-- Laurent polynomials in `z` (root coordinates) and `q`, as unnormalized term lists. -/
abbrev LPoly := List Term

/-- Insert a term, merging equal monomials. -/
def addTerm : Term → LPoly → LPoly
  | t, [] => [t]
  | t, s :: rest => if t.1 = s.1 then (t.1, t.2 + s.2) :: rest else s :: addTerm t rest

/-- Merge equal monomials and drop zero coefficients. -/
def normalize (f : LPoly) : LPoly :=
  (f.foldr addTerm []).filter fun t => t.2 ≠ 0

/-- Pairing `⟨μ, α_i^∨⟩ = ∑_j A_{ij} μ_j` in root coordinates. -/
def pairCoroot (A : List (List ℤ)) (i : ℕ) (μ : List ℤ) : ℤ :=
  ((A.getD i []).zipWith (· * ·) μ).sum

/-- Add `c` times the `i`-th unit vector. -/
def shiftAt (μ : List ℤ) (i : ℕ) (c : ℤ) : List ℤ :=
  μ.mapIdx fun j x => if j = i then x + c else x

/-- `μ + c θ`. -/
def shiftTheta (μ θ : List ℤ) (c : ℤ) : List ℤ := List.zipWith (fun x t => x + c * t) μ θ

/-- The finite Demazure operator `D_i` on one term. -/
def demazureFinTerm (A : List (List ℤ)) (i : ℕ) (t : Term) : LPoly :=
  let μ := t.1.1
  let n := pairCoroot A i μ
  if 0 ≤ n then
    (List.range (n.toNat + 1)).map fun (k : ℕ) => ((shiftAt μ i (-(k : ℤ)), t.1.2), t.2)
  else
    (List.range ((-n).toNat - 1)).map fun (k : ℕ) => ((shiftAt μ i ((k : ℤ) + 1), t.1.2), -t.2)

/-- The affine Demazure operator `D_0` on one term, at level one:
`⟨Λ₀ + μ, α₀^∨⟩ = 1 - (μ, θ)`, `e^{-α₀} = q^{-1} z^θ`. -/
def demazureZeroTerm (A : List (List ℤ)) (θ : List ℤ) (t : Term) : LPoly :=
  let μ := t.1.1
  let Aθ := (List.range θ.length).map fun i => pairCoroot A i θ
  let n := 1 - (List.zipWith (· * ·) Aθ μ).sum
  if 0 ≤ n then
    (List.range (n.toNat + 1)).map fun (k : ℕ) => ((shiftTheta μ θ k, t.1.2 - k), t.2)
  else
    (List.range ((-n).toNat - 1)).map fun (k : ℕ) =>
      ((shiftTheta μ θ (-((k : ℤ) + 1)), t.1.2 + ((k : ℤ) + 1)), -t.2)

def demazureFin (A : List (List ℤ)) (i : ℕ) (f : LPoly) : LPoly :=
  normalize (f.flatMap (demazureFinTerm A i))

def demazureZero (A : List (List ℤ)) (θ : List ℤ) (f : LPoly) : LPoly :=
  normalize (f.flatMap (demazureZeroTerm A θ))

/-- One application of `D_{s_θ} D_0`, with `D_{s_θ}` the composite along `word`. -/
def demazureStep (A : List (List ℤ)) (θ : List ℤ) (word : List ℕ) (f : LPoly) : LPoly :=
  word.foldr (fun i g => demazureFin A i g) (demazureZero A θ f)

/-- `q^{-m²} C_m`: the Demazure character of `V_{(s_θ s_0)^m}(Λ₀)` (before regrading). -/
def demazureChar (A : List (List ℤ)) (θ : List ℤ) (word : List ℕ) (m : ℕ) : LPoly :=
  (demazureStep A θ word)^[m] [((List.replicate θ.length 0, 0), 1)]

/-- **`[q^N] Hilb_q D(1,mθ)`**, the unflavoured level-one Demazure character regraded so that
the extremal vector sits in degree `0`. -/
def levelOneDemazureHilb (A : List (List ℤ)) (θ : List ℤ) (word : List ℕ) (m N : ℕ) : ℕ :=
  (((demazureChar A θ word m).filter fun (t : Term) => decide (t.1.2 + (m : ℤ) * m = N)).map
    fun (t : Term) => t.2).sum.toNat

/-! ## A₂ data (cross-check with the Gelfand–Tsetlin formula) -/

def cartanA2 : List (List ℤ) := [[2, -1], [-1, 2]]
def thetaA2 : List ℤ := [1, 1]
def wordA2 : List ℕ := [0, 1, 0]

/-- `Hilb D(1,θ) = 8 + q` for `A₂` from the Demazure formula. -/
theorem levelOneDemazureHilb_A2_one :
    (List.range 3).map (levelOneDemazureHilb cartanA2 thetaA2 wordA2 1) = [8, 1, 0] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter
