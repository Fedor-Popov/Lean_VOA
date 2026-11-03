/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Finsupp.Supported
import VOA.Core.LinearFiltration

/-!
# The combinatorial `R`-filtration of the inverse-DS free field `Pi`

Beem--Meneghelli--Rastelli, arXiv:1903.07624, eq. (3.15) and Sections 5--6, assign to a normally
ordered free-field monomial the degree

`number of derivatives of (delta - phi) + lattice charge`.

Derivatives of `(delta + phi)` cost zero.  Thus raw-label concatenation adds degrees,
differentiation does not change degree, and the exponential `exp(m (delta + phi))` has degree `m`.

This file formalizes exactly that monomial bookkeeping.  It deliberately does **not** claim that
the free vector space below already carries the full isotropic-lattice vertex-algebra structure:
the existing lattice VOA in this project is positive definite and must not be silently reused for
`Pi`.  The present layer is nevertheless enough to certify the degree of every term in the
Adamovic generator formulas and to state the later strictness theorem honestly.

The index is `ℤ`, not `ℕ`.  The filtration is nonzero at every integer because lattice charge is
unbounded below.  After fixing charge `q`, however, every monomial has degree at least `q`; this
fixed-charge lower bound is proved below.
-/

namespace VOA
namespace FreeFieldPi

noncomputable section

/-- A basis label for the free-field monomials relevant to the `R`-filtration.

The natural numbers stored in the multisets remember **derivative order minus one**: `0` denotes
the state `d(delta plus-or-minus phi)`, `1` denotes its derivative, and so on.  This avoids
introducing the non-state undifferentiated bosons as basis labels.  The values do not enter the
`R`-degree; only the number of minus oscillators matters. -/
structure Monomial where
  /-- Derivatives of `delta - phi`, each of which costs one unit of `R`-degree. -/
  minusOsc : Multiset ℕ
  /-- Derivatives of `delta + phi`, each of which costs zero units of `R`-degree. -/
  plusOsc : Multiset ℕ
  /-- The exponent `m` in `exp(m (delta + phi))`. -/
  charge : ℤ
  deriving DecidableEq

namespace Monomial

/-- The free-field `R`-degree from BMR eq. (3.15). -/
def rDegree (m : Monomial) : ℤ := m.minusOsc.card + m.charge

/-- The vacuum monomial. -/
def vacuum : Monomial := ⟨0, 0, 0⟩

/-- The pure lattice exponential `exp(q (delta + phi))`. -/
def exponential (q : ℤ) : Monomial := ⟨0, 0, q⟩

/-- Adjoin one derivative of `delta - phi`. -/
def addMinus (derivativeOrderMinusOne : ℕ) (m : Monomial) : Monomial :=
  ⟨derivativeOrderMinusOne ::ₘ m.minusOsc, m.plusOsc, m.charge⟩

/-- Adjoin one derivative of `delta + phi`. -/
def addPlus (derivativeOrderMinusOne : ℕ) (m : Monomial) : Monomial :=
  ⟨m.minusOsc, derivativeOrderMinusOne ::ₘ m.plusOsc, m.charge⟩

/-- Concatenate two raw monomial labels.  This is degree bookkeeping, not an implementation of
the normally ordered product or its Wick contractions. -/
def concat (m n : Monomial) : Monomial :=
  ⟨m.minusOsc + n.minusOsc, m.plusOsc + n.plusOsc, m.charge + n.charge⟩

@[simp] theorem rDegree_vacuum : vacuum.rDegree = 0 := by
  simp [rDegree, vacuum]

@[simp] theorem rDegree_exponential (q : ℤ) : (exponential q).rDegree = q := by
  simp [rDegree, exponential]

@[simp] theorem rDegree_addMinus (a : ℕ) (m : Monomial) :
    (addMinus a m).rDegree = m.rDegree + 1 := by
  simp [rDegree, addMinus]
  omega

@[simp] theorem rDegree_addPlus (a : ℕ) (m : Monomial) :
    (addPlus a m).rDegree = m.rDegree := by
  simp [rDegree, addPlus]

@[simp] theorem rDegree_concat (m n : Monomial) :
    (concat m n).rDegree = m.rDegree + n.rDegree := by
  simp [rDegree, concat]
  omega

end Monomial

/-- The free vector space on the monomial labels.  This is the vector-space shadow of `Pi`, used
only for filtration bookkeeping at this stage. -/
abbrev Space := Monomial →₀ ℂ

/-- The basis vector associated with a monomial label. -/
def basisVector (m : Monomial) : Space := Finsupp.single m 1

/-- The filtration piece spanned by monomials of `R`-degree at most `p`. -/
def rPiece (p : ℤ) : Submodule ℂ Space :=
  Finsupp.supported ℂ ℂ {m | m.rDegree ≤ p}

/-- The `ℤ`-indexed combinatorial `R`-filtration on the free-field basis. -/
def rFiltration : LinearFiltration ℤ ℂ Space where
  piece := rPiece
  mono' := by
    intro p q hp x hx
    rw [rPiece, Finsupp.mem_supported] at hx ⊢
    intro m hm
    exact (hx hm).trans hp

@[simp] theorem rFiltration_piece (p : ℤ) : rFiltration.piece p = rPiece p := rfl

/-- Membership means that every basis label in the finite support has degree at most `p`. -/
theorem mem_rPiece_iff (x : Space) (p : ℤ) :
    x ∈ rPiece p ↔ ∀ m ∈ x.support, m.rDegree ≤ p := by
  rw [rPiece, Finsupp.mem_supported]
  rfl

/-- A basis vector enters the filtration exactly at its monomial degree. -/
@[simp] theorem basisVector_mem_rPiece_iff (m : Monomial) (p : ℤ) :
    basisVector m ∈ rPiece p ↔ m.rDegree ≤ p := by
  rw [mem_rPiece_iff]
  simp [basisVector]

/-- The pure exponential of charge `q` enters exactly at filtration index `q`. -/
@[simp] theorem exponential_mem_rPiece_iff (q p : ℤ) :
    basisVector (Monomial.exponential q) ∈ rPiece p ↔ q ≤ p := by
  simp

/-- The filtration is genuinely unbounded below: every integer-indexed piece is nonzero. -/
theorem rPiece_ne_bot (p : ℤ) : rPiece p ≠ ⊥ := by
  intro hp
  have hmem : basisVector (Monomial.exponential p) ∈ rPiece p := by simp
  rw [hp] at hmem
  simp [basisVector] at hmem

/-- The span of monomials with a fixed lattice charge. -/
def chargeSector (q : ℤ) : Submodule ℂ Space :=
  Finsupp.supported ℂ ℂ {m | m.charge = q}

/-- Although the full filtration is unbounded below, its restriction to charge `q` begins at
degree `q`: below `q`, the filtration piece and the charge sector have zero intersection. -/
theorem rPiece_inf_chargeSector_eq_bot {p q : ℤ} (hpq : p < q) :
    rPiece p ⊓ chargeSector q = ⊥ := by
  ext x
  simp only [Submodule.mem_inf, Submodule.mem_bot]
  constructor
  · rintro ⟨hdegree, hcharge⟩
    rw [rPiece, Finsupp.mem_supported] at hdegree
    rw [chargeSector, Finsupp.mem_supported] at hcharge
    ext m
    by_contra hm
    have hms : m ∈ x.support := Finsupp.mem_support_iff.mpr hm
    have hle : m.rDegree ≤ p := hdegree hms
    have hq : m.charge = q := hcharge hms
    have hlower : q ≤ m.rDegree := by
      rw [← hq]
      simp [Monomial.rDegree]
    omega
  · rintro rfl
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩

end
end FreeFieldPi
end VOA
