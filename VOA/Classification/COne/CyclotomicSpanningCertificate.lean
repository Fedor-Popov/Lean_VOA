/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.CyclotomicSpanningSturm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Dimension and coefficient certificates for cyclotomic spanning

The analytic truncation bound is proved in `CyclotomicSpanningSturm`. This file
separates two remaining inputs: a dimension upper bound D, and D cyclotomic
forms with independent truncated expansions. Their conjunction for some D is
proved equivalent to the original `CyclotomicSpanning24`; no arithmetic
existence theorem is assumed implicitly. A nonzero coefficient minor suffices
for the independence input.

The classical source for existence of cyclotomic families is Diamond--Im,
*Modular forms and modular curves*, section 12.3 (arithmetic forms, base change,
and analytic comparison), as described in `QExpKatzSpanning`:
https://wstein.org/edu/Fall2003/252/references/diamond-im/
Dimension formulas are separate geometric input; see Diamond--Shurman,
*A First Course in Modular Forms*, chapter 3, and Stein, chapter 6:
https://wstein.org/books/modform/modform/dimension_formulas.html

One must not set D equal to the Sturm cutoff without proving that many forms
exist. For example, the classical formulas at N = 24 give dimension 28, whereas
the SL2 norm cutoff in this development is 65. Even the improved PSL2 cutoff
is 33. Those numerical dimension evaluations are not Lean theorems here.

Exact-arithmetic experiment (Python integers and `fractions.Fraction`): form
all nondecreasing quadruples of divisors a of N/4 and multiply the four series
`1 + 2 * sum_{n>=1} q^(a*n*n)`, truncated below the SL2 norm cutoff. Rational
row elimination gives the following ranks:

* N = 24: 35 products, cutoff 65, rank 28; classical dimension 28.
* N = 48: 126 products, cutoff 257, rank 52; classical dimension 92.
* N = 72: 126 products, cutoff 577, rank 72; classical dimension 192.

Thus the diagonal-theta search at level 24 does not extend to all levels by
merely taking four scaled standard theta series. This experiment is not used
by any proof. In particular neither modularity of these candidate products
nor their ranks or the classical dimension values are formalized here.

Still open: supply a matching geometric dimension bound and an arithmetic
family at EVERY positive level divisible by 24, or construct the integral
Cramer frame with a unit leading coefficient from `QExpKatzCramer`. The norm
argument proves vanishing, not bounded denominators. The known
obstructions to single-function Vandermonde frames and to inferring bounded
denominators from integrality of a series remain applicable.
-/

open UpperHalfPlane
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne.SSHecke

/-- A proposed dimension upper bound, independently of arithmetic coefficients. -/
def Gamma1DimensionBound24 (k : ℤ) (D : ℕ → ℕ) : Prop :=
  ∀ N, 0 < N → 24 ∣ N →
    Module.finrank ℂ
      (ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) ≤ D N

/-- D cyclotomic forms independent in the finite space of truncated expansions. -/
def CyclotomicIndependentFamily24 (k : ℤ) (D : ℕ → ℕ) : Prop :=
  ∀ N, 0 < N → 24 ∣ N →
    ∃ ζ : ℂ, IsPrimitiveRoot ζ N ∧
      ∃ f : Fin (D N) →
        ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k,
        (∀ i n, (qExpansion 1 (f i)).coeff n ∈ cyclotomicAway N ζ) ∧
        LinearIndependent ℂ (gamma1CoeffMap N k (integralSturmBound N k) ∘ f)

/-- A finite determinant certificate for the independent-family input.
All coefficients, not just the entries of the minor, must be cyclotomic. -/
def CyclotomicMinorFamily24 (k : ℤ) (D : ℕ → ℕ) : Prop :=
  ∀ N, 0 < N → 24 ∣ N →
    ∃ ζ : ℂ, IsPrimitiveRoot ζ N ∧
      ∃ f : Fin (D N) →
        ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k,
        (∀ i n, (qExpansion 1 (f i)).coeff n ∈ cyclotomicAway N ζ) ∧
        ∃ r : Fin (D N) → Fin (integralSturmBound N k),
          Matrix.det (fun i j => (qExpansion 1 (f i)).coeff (r j)) ≠ 0

/-- The unconditional norm-to-level-one bound supplies a dimension upper bound. -/
theorem gamma1DimensionBound24_sturm (k : ℤ) :
    Gamma1DimensionBound24 k (fun N => integralSturmBound N k) := by
  intro N hN _
  letI : NeZero N := ⟨hN.ne'⟩
  exact finrank_Gamma1_le N k

/-- Independent truncated vectors of sufficient cardinality imply actual spanning. -/
theorem spanning_of_truncated_independent {N : ℕ} [NeZero N] {k : ℤ} {d : ℕ}
    (f : Fin d →
      ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hd : Module.finrank ℂ
      (ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) ≤ d)
    (hi : LinearIndependent ℂ (gamma1CoeffMap N k (integralSturmBound N k) ∘ f)) :
    ∀ F, ∃ c : Fin d → ℂ, F = ∑ i, c i • f i := by
  letI := finiteDimensional_Gamma1 N k
  have hf : LinearIndependent ℂ f := hi.of_comp _
  have hcard : Fintype.card (Fin d) = Module.finrank ℂ
      (ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) := by
    exact le_antisymm hf.fintype_card_le_finrank (by simpa using hd)
  have hspan := hf.span_eq_top_of_card_eq_finrank' hcard
  intro F
  have hmem : F ∈ Submodule.span ℂ (Set.range f) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  exact ⟨c, hc.symm⟩

/-- The two independent inputs discharge the original arithmetic spanning statement. -/
theorem cyclotomicSpanning24_of_dimensionBound_of_independentFamily {k : ℤ} {D : ℕ → ℕ}
    (hd : Gamma1DimensionBound24 k D) (hf : CyclotomicIndependentFamily24 k D) :
    CyclotomicSpanning24 k := by
  intro N hN h24
  letI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨ζ, hζ, f, hc, hi⟩ := hf N hN h24
  exact ⟨ζ, hζ, D N, f, hc, spanning_of_truncated_independent f (hd N hN h24) hi⟩

/-- Selecting any square nonzero minor proves truncated independence. -/
theorem truncated_independent_of_minor {N : ℕ} {k : ℤ} {d B : ℕ}
    (f : Fin d →
      ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
    (r : Fin d → Fin B)
    (hdet : Matrix.det (fun i j => (qExpansion 1 (f i)).coeff (r j)) ≠ 0) :
    LinearIndependent ℂ (gamma1CoeffMap N k B ∘ f) := by
  let R : (Fin B → ℂ) →ₗ[ℂ] (Fin d → ℂ) := LinearMap.funLeft ℂ ℂ r
  exact (Matrix.linearIndependent_rows_of_det_ne_zero hdet).of_comp R

/-- Nonzero minors provide the independent-family input. -/
theorem independentFamily24_of_minorFamily {k : ℤ} {D : ℕ → ℕ}
    (h : CyclotomicMinorFamily24 k D) : CyclotomicIndependentFamily24 k D := by
  intro N hN h24
  obtain ⟨ζ, hζ, f, hc, r, hr⟩ := h N hN h24
  exact ⟨ζ, hζ, f, hc, truncated_independent_of_minor f r hr⟩

/-- A matching dimension upper bound and explicit coefficient minors suffice. -/
theorem cyclotomicSpanning24_of_dimensionBound_of_minors {k : ℤ} {D : ℕ → ℕ}
    (hd : Gamma1DimensionBound24 k D) (hf : CyclotomicMinorFamily24 k D) :
    CyclotomicSpanning24 k :=
  cyclotomicSpanning24_of_dimensionBound_of_independentFamily hd
    (independentFamily24_of_minorFamily hf)

/-- Weight-two arithmetic consequence, with both remaining inputs explicit. -/
theorem qExpPrinciple24Away_two_of_dimensionBound_of_minors {D : ℕ → ℕ}
    (hd : Gamma1DimensionBound24 2 D) (hf : CyclotomicMinorFamily24 2 D) :
    QExpPrinciple24Away 2 :=
  qExpPrinciple24Away_two_of_cyclotomicSpanning
    (cyclotomicSpanning24_of_dimensionBound_of_minors hd hf)

/-- The finite certificates imply the Serre--Stark bounded-coefficient input. -/
theorem boundedCoeff24_of_dimensionBound_of_minors {D : ℕ → ℕ}
    (hd : Gamma1DimensionBound24 2 D) (hf : CyclotomicMinorFamily24 2 D) :
    SerreStarkBoundedCoeff24 :=
  boundedCoeff24_of_qExpPrinciple24Away_two
    (qExpPrinciple24Away_two_of_dimensionBound_of_minors hd hf)

/-- Every finite spanning family contains a cyclotomic basis, with independent truncations. -/
theorem independentFamily24_of_cyclotomicSpanning {k : ℤ} (h : CyclotomicSpanning24 k) :
    CyclotomicIndependentFamily24 k (fun N => Module.finrank ℂ
      (ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)) := by
  classical
  intro N hN h24
  letI : NeZero N := ⟨hN.ne'⟩
  letI := finiteDimensional_Gamma1 N k
  obtain ⟨ζ, hζ, d, f, hc, hs⟩ := h N hN h24
  have hspan : Submodule.span ℂ (Set.range f) = ⊤ := by
    apply top_unique
    intro F _
    obtain ⟨c, hc⟩ := hs F
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨c, hc.symm⟩
  obtain ⟨ι, a, ha, hsp, hi⟩ := exists_linearIndependent' ℂ f
  letI : Finite ι := Finite.of_injective a ha
  letI : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = Module.finrank ℂ
      (ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) := by
    rw [← finrank_span_eq_card hi, hsp, hspan, finrank_top]
  let e := (Fintype.equivFin ι).trans (finCongr hcard)
  let g := (f ∘ a) ∘ e.symm
  have hg : LinearIndependent ℂ g := hi.comp e.symm e.symm.injective
  refine ⟨ζ, hζ, g, fun i n => hc _ n, ?_⟩
  exact hg.map' _ (LinearMap.ker_eq_bot.mpr (gamma1CoeffMap_injective N k))

/-- Lossless separation of geometry (dimension) from arithmetic (independent forms). -/
theorem cyclotomicSpanning24_iff_dimension_and_independentFamily (k : ℤ) :
    CyclotomicSpanning24 k ↔
      ∃ D : ℕ → ℕ, Gamma1DimensionBound24 k D ∧ CyclotomicIndependentFamily24 k D := by
  constructor
  · intro h
    exact ⟨_, fun _ _ _ => le_rfl, independentFamily24_of_cyclotomicSpanning h⟩
  · rintro ⟨D, hd, hf⟩
    exact cyclotomicSpanning24_of_dimensionBound_of_independentFamily hd hf

end VOA.Classification.COne.SSHecke
