/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AffineSl2BoundaryHarmonicLine
import VOA.Examples.AffineSl2BoundarySingularFamily
import VOA.Examples.AffineSl2WakimotoLiLeading

/-!
# From an affine highest vector to the boundary harmonic symbol

The boundary singular-vector package stores horizontal highest-weight equations on a state.
This file transports those equations through the universal affine `C₂` symbol map.  If the
symbol has a homogeneous polynomial lift of degree `2n+1`, the harmonic-line uniqueness theorem
then forces that lift to be a scalar multiple of `e * Cas^n`.

Consequently the external highest-symbol input separates into two sharply stated facts:

* existence of a homogeneous polynomial lift of the `C₂` class;
* nonvanishing of that class.

Horizontal highest-weight uniqueness is proved here, not taken as an external representation-theoretic input.
-/

namespace VOA.AffineSl2BoundarySingularFamily

open VertexOperatorAlgebra
open AffineVOA AffineVOA.Inst
open AffineSl2BoundaryC2 QuasiLisseSl2 Sl2Pres Sl2Symbol

noncomputable section

/-- The polynomial variable attached to an affine current colour.  Affine colours are ordered
`(e,f,h)`, whereas `SymSl2` is ordered `(e,h,f)`. -/
def currentSymbol : Fin 3 → SymSl2 := ![eSym, fSym, hSym]

/-- Natural conformal weight of a current creation word. -/
def currentWordWeight : List (Fin 3 × ℕ) → ℕ
  | [] => 0
  | an :: l => an.2 + 1 + currentWordWeight l

@[simp] theorem currentWordWeight_nil : currentWordWeight [] = 0 := rfl

@[simp] theorem currentWordWeight_cons (an : Fin 3 × ℕ) (l : List (Fin 3 × ℕ)) :
    currentWordWeight (an :: l) = an.2 + 1 + currentWordWeight l := rfl

/-- The natural word weight is the nonnegative version of the integer grading used by the affine
vacuum module. -/
theorem currentWordWeight_cast (l : List (Fin 3 × ℕ)) :
    (currentWordWeight l : ℤ) = wordDegA l := by
  induction l with
  | nil => rfl
  | cons an l ih =>
      rw [currentWordWeight_cons, wordDegA_cons, Nat.cast_add, Nat.cast_add, ih]
      norm_num

/-- The `C₂` polynomial of a current word.  A positive derivative depth makes the class zero;
depth-zero letters become the corresponding commutative current variables. -/
def currentWordSymbol : List (Fin 3 × ℕ) → SymSl2
  | [] => 1
  | (a, 0) :: l => currentSymbol a * currentWordSymbol l
  | (_, _ + 1) :: _ => 0

/-- Each current variable is homogeneous of polynomial degree one. -/
theorem currentSymbol_isHomogeneous (a : Fin 3) :
    (currentSymbol a).IsHomogeneous 1 := by
  fin_cases a
  · simpa [currentSymbol, eSym] using
      (MvPolynomial.isHomogeneous_X (R := ℂ) (0 : Fin 3))
  · simpa [currentSymbol, fSym] using
      (MvPolynomial.isHomogeneous_X (R := ℂ) (2 : Fin 3))
  · simpa [currentSymbol, hSym] using
      (MvPolynomial.isHomogeneous_X (R := ℂ) (1 : Fin 3))

/-- The word symbol is homogeneous of the conformal weight of the word.  In a positive-depth
sector the symbol is zero, which is homogeneous in every degree. -/
theorem currentWordSymbol_isHomogeneous (l : List (Fin 3 × ℕ)) :
    (currentWordSymbol l).IsHomogeneous (currentWordWeight l) := by
  induction l with
  | nil =>
      simpa [currentWordSymbol, currentWordWeight] using
        (MvPolynomial.isHomogeneous_one (Fin 3) ℂ)
  | cons an l ih =>
      obtain ⟨a, r⟩ := an
      rcases r with _ | r
      · exact (currentSymbol_isHomogeneous a).mul ih
      · simpa [currentWordSymbol, currentWordWeight] using
          (MvPolynomial.isHomogeneous_zero (Fin 3) ℂ
            (r + 1 + 1 + currentWordWeight l))

/-- Evaluating the word symbol gives the `C₂` class of the corresponding affine current word. -/
theorem symbolAlg_currentWordSymbol (k : ℂ) (hk : k + 2 ≠ 0)
    (l : List (Fin 3 × ℕ)) :
    symbolAlg k hk (currentWordSymbol l) =
      mk₂ (affineSl2VOA_closed k hk) (wordStateA k l) := by
  induction l with
  | nil =>
      rw [currentWordSymbol, wordStateA_nil,
        show vacuumA k = (affineSl2VOA_closed k hk).vacuum from rfl,
        map_one, ← A₂_one_eq]
  | cons an l ih =>
      obtain ⟨a, r⟩ := an
      rcases r with _ | r
      · rw [currentWordSymbol, map_mul, wordStateA_cons,
          show (-((0 : ℕ) : ℤ) - 1) = -1 by norm_num,
          Sl2Pres.mk₂_J_neg_one, ih]
        fin_cases a <;>
          simp [currentSymbol, eCl, fCl, hCl, symbolAlg_eSym, symbolAlg_fSym,
            symbolAlg_hSym]
      · rw [currentWordSymbol, map_zero, wordStateA_cons]
        exact ((mk₂_eq_zero_iff _).mpr
          (J_mem_O₂ k hk a (show (-((r + 1 : ℕ) : ℤ) - 1) ≤ -2 by push_cast; omega) _)).symm

/-- Every homogeneous affine state has a homogeneous polynomial lift of its universal `C₂`
class.  This is the grading-sensitive strengthening of bare surjectivity of `symbolAlg`. -/
theorem exists_homogeneous_symbolLift (k : ℂ) (hk : k + 2 ≠ 0)
    (N : ℕ) (s : WakModule k) (hs : s ∈ gradingZA k (N : ℤ)) :
    ∃ p : SymSl2, p.IsHomogeneous N ∧
      symbolAlg k hk p = mk₂ (affineSl2VOA_closed k hk) s := by
  have hsH : s ∈ HSpan k (N : ℤ) := gradingZA_le_hspan k (N : ℤ) hs
  clear hs
  rw [HSpan] at hsH
  induction hsH using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hlN, rfl⟩ := hx
      have hweight : currentWordWeight l = N := by
        exact_mod_cast (currentWordWeight_cast l).trans hlN
      refine ⟨currentWordSymbol l, ?_, symbolAlg_currentWordSymbol k hk l⟩
      simpa [hweight] using currentWordSymbol_isHomogeneous l
  | zero =>
      exact ⟨0, MvPolynomial.isHomogeneous_zero (Fin 3) ℂ N, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨px, hpx, hpxmap⟩ := hx
      obtain ⟨py, hpy, hpymap⟩ := hy
      exact ⟨px + py, hpx.add hpy, by rw [map_add, hpxmap, hpymap, map_add]⟩
  | smul c x _ hx =>
      obtain ⟨p, hp, hpmap⟩ := hx
      refine ⟨c • p, ?_, ?_⟩
      · simpa [Algebra.smul_def] using hp.C_mul c
      · rw [map_smul, hpmap, map_smul]

/-- The conformal-homogeneity field of a boundary candidate supplies the homogeneous lift used
by the harmonic uniqueness theorem. -/
theorem Candidate.exists_homogeneousSymbolLift {k : ℂ} {n : ℕ} (C : Candidate k n) :
    ∃ p : SymSl2, p.IsHomogeneous (2 * n + 1) ∧
      symbolAlg k C.noncritical p =
        mk₂ (affineSl2VOA_closed k C.noncritical) C.vector := by
  simpa [denominator] using
    exists_homogeneous_symbolLift k C.noncritical (2 * n + 1) C.vector C.homogeneous

/-- A polynomial lift of the `C₂` symbol of a boundary candidate automatically satisfies the
classical raising equation. -/
theorem adE_symbolLift_eq_zero {k : ℂ} {n : ℕ} (C : Candidate k n)
    (p : SymSl2)
    (hlift : symbolAlg k C.noncritical p =
      mk₂ (affineSl2VOA_closed k C.noncritical) C.vector) :
    adE p = 0 := by
  apply AffineSl2WakimotoLiLeading.universalSymbolAlg_injective k C.noncritical
  calc
    symbolAlg k C.noncritical (adE p) =
        A₂bracket (affineSl2VOA_closed k C.noncritical)
          (eCl k C.noncritical) (symbolAlg k C.noncritical p) :=
      symbolAlg_adE_compat k C.noncritical p
    _ = 0 := by
      rw [hlift, eCl, A₂bracket_mk, poissonBracket_def,
        smul_currentState_eq_J, C.horizontalRaising, map_zero]
    _ = symbolAlg k C.noncritical 0 := by rw [map_zero]

/-- A polynomial lift of the `C₂` symbol of a boundary candidate automatically has horizontal
Cartan weight two. -/
theorem adH_symbolLift_eq_two_smul {k : ℂ} {n : ℕ} (C : Candidate k n)
    (p : SymSl2)
    (hlift : symbolAlg k C.noncritical p =
      mk₂ (affineSl2VOA_closed k C.noncritical) C.vector) :
    adH p = (2 : ℂ) • p := by
  apply AffineSl2WakimotoLiLeading.universalSymbolAlg_injective k C.noncritical
  rw [symbolAlg_adH_compat, hlift, hCl, A₂bracket_mk, poissonBracket_def,
    smul_currentState_eq_J, C.horizontalCharge, map_smul, map_smul, hlift]

/-- A nonzero homogeneous polynomial lift of a candidate symbol is a nonzero multiple of the
boundary harmonic line. -/
theorem highestSymbol_of_homogeneousLift {k : ℂ} {n : ℕ} (C : Candidate k n)
    (p : SymSl2)
    (hp : p.IsHomogeneous (2 * n + 1))
    (hlift : symbolAlg k C.noncritical p =
      mk₂ (affineSl2VOA_closed k C.noncritical) C.vector)
    (hsymbol_ne : mk₂ (affineSl2VOA_closed k C.noncritical) C.vector ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧
      mk₂ (affineSl2VOA_closed k C.noncritical) C.vector =
        c • symbolAlg k C.noncritical (eSym * casSym ^ n) := by
  obtain ⟨c, hpc⟩ := eq_smul_harmonicLine n p hp
    (adH_symbolLift_eq_two_smul C p hlift)
    (adE_symbolLift_eq_zero C p hlift)
  refine ⟨c, ?_, ?_⟩
  · intro hc
    apply hsymbol_ne
    rw [← hlift, hpc, hc, zero_smul, map_zero]
  · rw [← hlift, hpc, map_smul, harmonicLine]

/-- Nonvanishing of the `C₂` class is enough to obtain the complete nonzero highest-symbol
identity.  Homogeneous lifting, horizontal equivariance, and harmonic-line uniqueness are all
internal. -/
theorem Candidate.exists_highestSymbol_of_symbol_ne_zero {k : ℂ} {n : ℕ}
    (C : Candidate k n)
    (hsymbol_ne : mk₂ (affineSl2VOA_closed k C.noncritical) C.vector ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧
      mk₂ (affineSl2VOA_closed k C.noncritical) C.vector =
        c • symbolAlg k C.noncritical (eSym * casSym ^ n) := by
  obtain ⟨p, hp, hlift⟩ := C.exists_homogeneousSymbolLift
  exact highestSymbol_of_homogeneousLift C p hp hlift hsymbol_ne

/-- The exact boundary `C₂` data package from maximal singular generation and the two remaining
symbol facts: a homogeneous lift and nonvanishing. -/
noncomputable def Candidate.toClassicalDataOfHarmonicLift {k : ℂ} {n : ℕ}
    (C : Candidate k n)
    (p : SymSl2)
    (hp : p.IsHomogeneous (2 * n + 1))
    (hlift : symbolAlg k C.noncritical p =
      mk₂ (affineSl2VOA_closed k C.noncritical) C.vector)
    (hsymbol_ne : mk₂ (affineSl2VOA_closed k C.noncritical) C.vector ≠ 0)
    (hmax : QuotVOA.maxGradedIdeal (affineSl2VOA_closed k C.noncritical) =
      SingVec.idealGen (affineSl2VOA_closed k C.noncritical) C.vector) :
    ClassicalData k n := by
  let hex := highestSymbol_of_homogeneousLift C p hp hlift hsymbol_ne
  let c : ℂ := Classical.choose hex
  have hc : c ≠ 0 := (Classical.choose_spec hex).1
  have hsymbol :
      mk₂ (affineSl2VOA_closed k C.noncritical) C.vector =
        c • symbolAlg k C.noncritical (eSym * casSym ^ n) :=
    (Classical.choose_spec hex).2
  exact
    { toCandidate := C
      symbolCoefficient := c
      symbolCoefficient_ne_zero := hc
      highestSymbol := hsymbol
      maximalGeneration := hmax }

/-- Maximal singular generation plus nonvanishing of the candidate's `C₂` class gives the full
classical data package.  In particular, no separate highest-symbol shape is assumed. -/
noncomputable def Candidate.toClassicalDataOfSymbolNonzero {k : ℂ} {n : ℕ}
    (C : Candidate k n)
    (hsymbol_ne : mk₂ (affineSl2VOA_closed k C.noncritical) C.vector ≠ 0)
    (hmax : QuotVOA.maxGradedIdeal (affineSl2VOA_closed k C.noncritical) =
      SingVec.idealGen (affineSl2VOA_closed k C.noncritical) C.vector) :
    ClassicalData k n := by
  let hex := C.exists_highestSymbol_of_symbol_ne_zero hsymbol_ne
  let c : ℂ := Classical.choose hex
  have hc : c ≠ 0 := (Classical.choose_spec hex).1
  have hsymbol :
      mk₂ (affineSl2VOA_closed k C.noncritical) C.vector =
        c • symbolAlg k C.noncritical (eSym * casSym ^ n) :=
    (Classical.choose_spec hex).2
  exact
    { toCandidate := C
      symbolCoefficient := c
      symbolCoefficient_ne_zero := hc
      highestSymbol := hsymbol
      maximalGeneration := hmax }

/-- The published irreducible singular quotient supplies maximal generation internally.  After
that source theorem, a homogeneous lift and nonvanishing of its `C₂` class are the only remaining
inputs to `ClassicalData`. -/
noncomputable def AdamovicMilasData.toClassicalDataOfHarmonicLift {k : ℂ} {n : ℕ}
    (D : AdamovicMilasData k n)
    (p : SymSl2)
    (hp : p.IsHomogeneous (2 * n + 1))
    (hlift : symbolAlg k D.noncritical p =
      mk₂ (affineSl2VOA_closed k D.noncritical) D.vector)
    (hsymbol_ne : mk₂ (affineSl2VOA_closed k D.noncritical) D.vector ≠ 0) :
    ClassicalData k n :=
  D.toCandidate.toClassicalDataOfHarmonicLift p hp hlift hsymbol_ne D.maximalGeneration

/-- Sharp source-theorem adapter: the Adamović--Milas irreducible singular quotient and the
Arakawa--Jiang--Moreau nonvanishing of the candidate `C₂` class imply the full exact-presentation
package. -/
noncomputable def AdamovicMilasData.toClassicalDataOfSymbolNonzero {k : ℂ} {n : ℕ}
    (D : AdamovicMilasData k n)
    (hsymbol_ne : mk₂ (affineSl2VOA_closed k D.noncritical) D.vector ≠ 0) :
    ClassicalData k n :=
  D.toCandidate.toClassicalDataOfSymbolNonzero hsymbol_ne D.maximalGeneration

end

end VOA.AffineSl2BoundarySingularFamily

section AxiomAudit
namespace VOA.AffineSl2BoundarySingularFamily
end VOA.AffineSl2BoundarySingularFamily
end AxiomAudit
