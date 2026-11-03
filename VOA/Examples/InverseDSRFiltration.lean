/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.FreeFieldPiRFiltration

/-!
# `R`-degree certificates for the Adamovic inverse-DS formulas

For the boundary levels `k = -4n/(2n+1)`, Adamovic's realization embeds

`L_k(sl2) -> Vir_{2,2n+1} tensor Pi`.

In the notation of Beem--Meneghelli--Rastelli, arXiv:1903.07624, Sections 5--6,

* `e = exp(delta + phi)`;
* `h` is a linear combination of `vPlus = d(delta+phi)` and
  `vMinus = -k/2 d(delta-phi)`; and
* after expanding `d delta` in `vPlus,vMinus`, every term of `f` is one of the raw monomial
  shapes listed below, always multiplied by `exp(-(delta+phi))`.

The Virasoro filtration degree is the number of `T_IR` factors, while the `Pi` degree is formalized
in `FreeFieldPiRFiltration`.  This file proves, by exact integer arithmetic, that every displayed
term in each affine generator has total degree at most one.  It also proves additivity for raw
label concatenation, hence the corresponding bound by affine word length.

This is the finite combinatorial certificate behind the **filtered inclusion**.  It is not yet a
construction of the free-field VOA embedding, and it does not prove **strictness** (the converse
inclusion/no-hidden-cancellation theorem).
-/

namespace VOA
namespace InverseDS

open FreeFieldPi

noncomputable section

/-- A raw monomial in `Vir tensor Pi`, retaining just the information relevant to `R`-degree. -/
structure AmbientMonomial where
  /-- Number of `T_IR` factors. -/
  virLength : ℕ
  /-- Free-field oscillator and lattice-charge label. -/
  pi : FreeFieldPi.Monomial
  deriving DecidableEq

namespace AmbientMonomial

/-- Total tensor-product degree: Virasoro length plus `Pi` degree. -/
def rDegree (m : AmbientMonomial) : ℤ := m.virLength + m.pi.rDegree

/-- Concatenation of raw labels.  This is not yet the normally ordered product. -/
def concat (m n : AmbientMonomial) : AmbientMonomial :=
  ⟨m.virLength + n.virLength, m.pi.concat n.pi⟩

@[simp] theorem rDegree_concat (m n : AmbientMonomial) :
    (concat m n).rDegree = m.rDegree + n.rDegree := by
  simp [rDegree, concat]
  omega

end AmbientMonomial

/-- The free vector space on ambient monomial labels. -/
abbrev AmbientSpace := AmbientMonomial →₀ ℂ

/-- The basis vector attached to an ambient monomial. -/
def ambientBasisVector (m : AmbientMonomial) : AmbientSpace := Finsupp.single m 1

/-- The ambient tensor-product filtration piece. -/
def ambientRPiece (p : ℤ) : Submodule ℂ AmbientSpace :=
  Finsupp.supported ℂ ℂ {m | m.rDegree ≤ p}

/-- The `ℤ`-indexed tensor-product filtration obtained by adding Virasoro length and `Pi` degree. -/
def ambientRFiltration : LinearFiltration ℤ ℂ AmbientSpace where
  piece := ambientRPiece
  mono' := by
    intro p q hp x hx
    rw [ambientRPiece, Finsupp.mem_supported] at hx ⊢
    intro m hm
    exact (hx hm).trans hp

@[simp] theorem ambientRFiltration_piece (p : ℤ) :
    ambientRFiltration.piece p = ambientRPiece p := rfl

/-- An ambient basis vector enters exactly at its total degree. -/
@[simp] theorem ambientBasisVector_mem_rPiece_iff (m : AmbientMonomial) (p : ℤ) :
    ambientBasisVector m ∈ ambientRPiece p ↔ m.rDegree ≤ p := by
  rw [ambientRPiece, Finsupp.mem_supported]
  simp [ambientBasisVector]

/-- Raw-label concatenation sends two filtered basis labels to the piece indexed by the sum.
This is a combinatorial statement, not an implementation of normally ordered multiplication. -/
theorem ambientBasisVector_concat_mem_add_piece {m n : AmbientMonomial} {p q : ℤ}
    (hm : ambientBasisVector m ∈ ambientRPiece p)
    (hn : ambientBasisVector n ∈ ambientRPiece q) :
    ambientBasisVector (m.concat n) ∈ ambientRPiece (p + q) := by
  rw [ambientBasisVector_mem_rPiece_iff] at hm hn ⊢
  rw [AmbientMonomial.rDegree_concat]
  exact add_le_add hm hn

/-- A pure lattice exponential, with no Virasoro factor. -/
def expTerm (q : ℤ) : AmbientMonomial := ⟨0, FreeFieldPi.Monomial.exponential q⟩

/-- One `vPlus` oscillator multiplying a charge-`q` exponential. -/
def plusTerm (q : ℤ) : AmbientMonomial :=
  ⟨0, (FreeFieldPi.Monomial.exponential q).addPlus 0⟩

/-- One `vMinus` oscillator multiplying a charge-`q` exponential. -/
def minusTerm (q : ℤ) : AmbientMonomial :=
  ⟨0, (FreeFieldPi.Monomial.exponential q).addMinus 0⟩

/-- One derivative of `vPlus` multiplying a charge-`q` exponential. -/
def dPlusTerm (q : ℤ) : AmbientMonomial :=
  ⟨0, (FreeFieldPi.Monomial.exponential q).addPlus 1⟩

/-- One derivative of `vMinus` multiplying a charge-`q` exponential. -/
def dMinusTerm (q : ℤ) : AmbientMonomial :=
  ⟨0, (FreeFieldPi.Monomial.exponential q).addMinus 1⟩

/-- Two `vPlus` oscillators multiplying a charge-`q` exponential. -/
def plusPlusTerm (q : ℤ) : AmbientMonomial :=
  ⟨0, ((FreeFieldPi.Monomial.exponential q).addPlus 0).addPlus 0⟩

/-- One `vPlus` and one `vMinus` oscillator multiplying a charge-`q` exponential. -/
def plusMinusTerm (q : ℤ) : AmbientMonomial :=
  ⟨0, ((FreeFieldPi.Monomial.exponential q).addPlus 0).addMinus 0⟩

/-- Two `vMinus` oscillators multiplying a charge-`q` exponential. -/
def minusMinusTerm (q : ℤ) : AmbientMonomial :=
  ⟨0, ((FreeFieldPi.Monomial.exponential q).addMinus 0).addMinus 0⟩

/-- One `T_IR` factor multiplying a charge-`q` exponential. -/
def virTerm (q : ℤ) : AmbientMonomial := ⟨1, FreeFieldPi.Monomial.exponential q⟩

@[simp] theorem rDegree_expTerm (q : ℤ) : (expTerm q).rDegree = q := by
  simp [AmbientMonomial.rDegree, expTerm]

@[simp] theorem rDegree_plusTerm (q : ℤ) : (plusTerm q).rDegree = q := by
  simp [AmbientMonomial.rDegree, plusTerm]

@[simp] theorem rDegree_minusTerm (q : ℤ) : (minusTerm q).rDegree = q + 1 := by
  simp [AmbientMonomial.rDegree, minusTerm]

@[simp] theorem rDegree_dPlusTerm (q : ℤ) : (dPlusTerm q).rDegree = q := by
  simp [AmbientMonomial.rDegree, dPlusTerm]

@[simp] theorem rDegree_dMinusTerm (q : ℤ) : (dMinusTerm q).rDegree = q + 1 := by
  simp [AmbientMonomial.rDegree, dMinusTerm]

@[simp] theorem rDegree_plusPlusTerm (q : ℤ) : (plusPlusTerm q).rDegree = q := by
  simp [AmbientMonomial.rDegree, plusPlusTerm]

@[simp] theorem rDegree_plusMinusTerm (q : ℤ) : (plusMinusTerm q).rDegree = q + 1 := by
  simp [AmbientMonomial.rDegree, plusMinusTerm]

@[simp] theorem rDegree_minusMinusTerm (q : ℤ) : (minusMinusTerm q).rDegree = q + 2 := by
  simp [AmbientMonomial.rDegree, minusMinusTerm]
  omega

@[simp] theorem rDegree_virTerm (q : ℤ) : (virTerm q).rDegree = q + 1 := by
  simp [AmbientMonomial.rDegree, virTerm]
  omega

/-- The possible raw monomial shapes in the three displayed affine generator formulas.

`fDPlus` and `fDMinus` have the same degree as `fPlus` and `fMinus`: changing derivative order
does not change the filtration. -/
inductive AffineGeneratorTerm
  | e
  | hPlus
  | hMinus
  | fVir
  | fPlusPlus
  | fPlusMinus
  | fMinusMinus
  | fDPlus
  | fDMinus
  deriving DecidableEq

/-- Interpret a generator-term shape as an ambient monomial. -/
def AffineGeneratorTerm.monomial : AffineGeneratorTerm → AmbientMonomial
  | .e => expTerm 1
  | .hPlus => plusTerm 0
  | .hMinus => minusTerm 0
  | .fVir => virTerm (-1)
  | .fPlusPlus => plusPlusTerm (-1)
  | .fPlusMinus => plusMinusTerm (-1)
  | .fMinusMinus => minusMinusTerm (-1)
  | .fDPlus => dPlusTerm (-1)
  | .fDMinus => dMinusTerm (-1)

/-- **Generator certificate.** Every term occurring in `e`, `h`, or `f` has total ambient
`R`-degree at most one. -/
theorem affineGeneratorTerm_degree_le_one (t : AffineGeneratorTerm) :
    t.monomial.rDegree ≤ 1 := by
  cases t <;> simp [AffineGeneratorTerm.monomial]

/-- Filtration-piece form of the generator certificate. -/
theorem affineGeneratorTerm_mem_piece_one (t : AffineGeneratorTerm) :
    ambientBasisVector t.monomial ∈ ambientRPiece 1 := by
  rw [ambientBasisVector_mem_rPiece_iff]
  exact affineGeneratorTerm_degree_le_one t

/-- Raw multiplication of chosen generator terms. -/
def affineWordMonomial : List AffineGeneratorTerm → AmbientMonomial
  | [] => ⟨0, FreeFieldPi.Monomial.vacuum⟩
  | t :: ts => t.monomial.concat (affineWordMonomial ts)

/-- Every raw term in the free-field expansion of an affine word has degree at most its word
length.  Passing from this raw statement to fields/modes requires the later free-field VOA layer. -/
theorem affineWordMonomial_degree_le_length (ts : List AffineGeneratorTerm) :
    (affineWordMonomial ts).rDegree ≤ ts.length := by
  induction ts with
  | nil => simp [affineWordMonomial, AmbientMonomial.rDegree]
  | cons t ts ih =>
      rw [affineWordMonomial, AmbientMonomial.rDegree_concat]
      have ht := affineGeneratorTerm_degree_le_one t
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      omega

/-- Filtration-piece form of the affine-word certificate. -/
theorem affineWordMonomial_mem_length_piece (ts : List AffineGeneratorTerm) :
    ambientBasisVector (affineWordMonomial ts) ∈ ambientRPiece (ts.length : ℤ) := by
  rw [ambientBasisVector_mem_rPiece_iff]
  exact affineWordMonomial_degree_le_length ts

/-- The raw terms in the Sugawara identity

`T_Sug = T_IR + 1/2 (vPlus vMinus - d vMinus) + k/2 d vPlus`.
-/
inductive SugawaraTerm
  | vir
  | plusMinus
  | dMinus
  | dPlus
  deriving DecidableEq

def SugawaraTerm.monomial : SugawaraTerm → AmbientMonomial
  | .vir => virTerm 0
  | .plusMinus => plusMinusTerm 0
  | .dMinus => dMinusTerm 0
  | .dPlus => dPlusTerm 0

/-- Every term of the Sugawara vector has ambient degree at most one, as required for agreement
with the corrected affine `R`-filtration. -/
theorem sugawaraTerm_degree_le_one (t : SugawaraTerm) :
    t.monomial.rDegree ≤ 1 := by
  cases t <;> simp [SugawaraTerm.monomial]

/-- A raw term chosen from a corrected affine generator: a current `e,h,f`, or the independent
cost-one Sugawara generator.  This type records only displayed monomial labels. -/
inductive CorrectedGeneratorTerm
  | current (t : AffineGeneratorTerm)
  | sugawara (t : SugawaraTerm)
  deriving DecidableEq

/-- Interpret a corrected-generator term as its raw ambient monomial label. -/
def CorrectedGeneratorTerm.monomial : CorrectedGeneratorTerm → AmbientMonomial
  | .current t => t.monomial
  | .sugawara t => t.monomial

/-- Every raw term of every cost-one corrected affine generator has ambient degree at most one. -/
theorem correctedGeneratorTerm_degree_le_one (t : CorrectedGeneratorTerm) :
    t.monomial.rDegree ≤ 1 := by
  cases t with
  | current t => exact affineGeneratorTerm_degree_le_one t
  | sugawara t => exact sugawaraTerm_degree_le_one t

/-- Concatenate one chosen raw term from each generator in a mixed corrected affine word. -/
def correctedWordMonomial : List CorrectedGeneratorTerm → AmbientMonomial
  | [] => ⟨0, FreeFieldPi.Monomial.vacuum⟩
  | t :: ts => t.monomial.concat (correctedWordMonomial ts)

/-- **Mixed-word certificate.** A raw label obtained by choosing one displayed term from each
current or Sugawara generator in a corrected word has ambient degree at most the word length.

Promoting this statement to the actual filtered inclusion requires the isotropic-lattice VOA,
Wick calculus, and the concrete inverse-DS embedding. -/
theorem correctedWordMonomial_degree_le_length (ts : List CorrectedGeneratorTerm) :
    (correctedWordMonomial ts).rDegree ≤ ts.length := by
  induction ts with
  | nil => simp [correctedWordMonomial, AmbientMonomial.rDegree]
  | cons t ts ih =>
      rw [correctedWordMonomial, AmbientMonomial.rDegree_concat]
      have ht := correctedGeneratorTerm_degree_le_one t
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      omega

/-- Filtration-piece form of the mixed corrected-word certificate. -/
theorem correctedWordMonomial_mem_length_piece (ts : List CorrectedGeneratorTerm) :
    ambientBasisVector (correctedWordMonomial ts) ∈ ambientRPiece (ts.length : ℤ) := by
  rw [ambientBasisVector_mem_rPiece_iff]
  exact correctedWordMonomial_degree_le_length ts

/-- Abstract data needed to compare the corrected affine `R`-filtration with the ambient
free-field filtration.  Constructing this object for the actual VOAs requires the inverse-DS
embedding; no such construction is asserted here. -/
structure FiltrationComparison (Affine Ambient : Type*)
    [AddCommMonoid Affine] [Module ℂ Affine]
    [AddCommMonoid Ambient] [Module ℂ Ambient] where
  /-- Corrected affine filtration, indexed by affine word length. -/
  affineR : LinearFiltration ℕ ℂ Affine
  /-- Ambient `Vir tensor Pi` filtration, which is naturally `ℤ`-indexed. -/
  ambientR : LinearFiltration ℤ ℂ Ambient
  /-- The underlying linear map of the inverse-DS embedding. -/
  iota : Affine →ₗ[ℂ] Ambient
  /-- Injectivity of the inverse-DS embedding. -/
  iota_injective : Function.Injective iota

namespace FiltrationComparison

variable {Affine Ambient : Type*}
variable [AddCommMonoid Affine] [Module ℂ Affine]
variable [AddCommMonoid Ambient] [Module ℂ Ambient]

/-- The easy direction: every affine filtration piece maps into the ambient piece with the same
integer index. -/
def IsFiltered (C : FiltrationComparison Affine Ambient) : Prop :=
  C.affineR.IsFilteredAlong C.ambientR (fun p : ℕ => (p : ℤ)) C.iota

/-- The desired exact comparison: the induced ambient filtration on the affine image is the
corrected affine filtration at nonnegative indices, and the affine image has no negative-degree
part.  The second clause is essential because the ambient filtration is `ℤ`-indexed. -/
def IsStrict (C : FiltrationComparison Affine Ambient) : Prop :=
  C.affineR.IsStrictFilteredAlong C.ambientR (fun p : ℕ => (p : ℤ)) C.iota ∧
    ∀ q : ℤ, q < 0 → LinearMap.range C.iota ⊓ C.ambientR.piece q = ⊥

/-- Strict inverse-DS filtration compatibility implies the easy filtered inclusion. -/
theorem isFiltered_of_isStrict (C : FiltrationComparison Affine Ambient) (h : C.IsStrict) :
    C.IsFiltered :=
  h.1.isFilteredAlong

/-- The no-hidden-cancellation theorem in its exact piecewise form.  This is the formal target for
the inverse-DS filtration project. -/
theorem isStrict_iff_piecewise_comap (C : FiltrationComparison Affine Ambient) :
    C.IsStrict ↔
      (∀ p : ℕ, C.affineR.piece p = (C.ambientR.piece (p : ℤ)).comap C.iota) ∧
      ∀ q : ℤ, q < 0 → LinearMap.range C.iota ⊓ C.ambientR.piece q = ⊥ := by
  rw [IsStrict, LinearFiltration.strictFilteredAlong_iff_comap_eq C.iota_injective]

end FiltrationComparison

end

end InverseDS
end VOA
