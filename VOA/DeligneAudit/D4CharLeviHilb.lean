import VOA.DeligneAudit.DeligneFusionCount
import VOA.DeligneAudit.DeligneCharacterD4Schur
import VOA.DeligneAudit.D4FusionKernelGeneric
import VOA.DeligneAudit.DeligneSectorD4
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The degree-wise D4 Levi character targets

The definitions are natural-valued convolution formulas.
The four entries of a multiplicity vector are `(a, b₊, b₋, c)`.
The named propositions below are targets, not assumed results.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

/-- The GL4 Gelfand--Tsetlin polynomial at four unit variables, coefficient by coefficient. -/
def gl4Hilb (l₁ l₂ l₃ l₄ N : ℕ) : ℕ :=
  ∑ m₁ ∈ Finset.Icc l₂ l₁, ∑ m₂ ∈ Finset.Icc l₃ l₂,
    ∑ m₃ ∈ Finset.Icc l₄ l₃,
      A2.conv
        (A2.conv
          (A2.conv (A2.qbinomCoeff (l₁ - l₂) (l₁ - m₁))
            (A2.qbinomCoeff (l₂ - l₃) (l₂ - m₂)))
          (A2.qbinomCoeff (l₃ - l₄) (l₃ - m₃)))
        (A2.gl3Hilb m₁ m₂ m₃) N

/-- The four-part Gaussian multinomial, in the order of the three Levi mode boxes. -/
def qmultiCoeff (t : Fin 4 → ℕ) : ℕ → ℕ :=
  A2.conv
    (A2.conv (A2.qbinomCoeff (∑ i, t i) (t 3))
      (A2.qbinomCoeff (t 0 + t 1 + t 2) (t 2)))
    (A2.qbinomCoeff (t 0 + t 1) (t 0))

/-- The raw degree-wise Levi sum, with no additional degree shift. -/
def d4LeviHilb (n N : ℕ) : ℕ :=
  ∑ t ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 4)) n,
    A2.conv (qmultiCoeff t)
      (gl4Hilb (2 * t 0 + (t 1 + t 2)) (t 0 + (t 1 + t 2)) (t 0) 0) N

/-- (L4): the exact target type of `d4_hilbInt_eq_levi`, uniformly in both indices. -/
def HilbertIdentity : Prop :=
  ∀ n N : ℕ, DeligneCharacter.D4K.hilbInt n N = (d4LeviHilb n N : ℤ)

/-- (L1): every module satisfying the presented Demazure relations has this graded bound. -/
def GradedLeviBound : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : SectorWeyl.CurrentModule DeligneSector.D4.D4sector.f V) (w : V),
    UnivG.Sat DeligneSector.D4.D4sector.f ρ w
      (UnivG.ravFam DeligneSector.D4.D4sector n 0) →
    ∀ N, Module.finrank ℂ (SectorWeyl.cycDeg ρ w N) ≤ d4LeviHilb n N

/-- (L3), including finite support so the total has an unambiguous finite-sum meaning. -/
def LeviTotalCount : Prop :=
  ∀ n : ℕ, ∃ B : ℕ, (∀ N, B ≤ N → d4LeviHilb n N = 0) ∧
    ∑ N ∈ Finset.range B, d4LeviHilb n N = 29 ^ n

end VOA.DeligneAudit.D4Char
