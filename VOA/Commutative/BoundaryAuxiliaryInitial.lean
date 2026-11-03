/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.InfiniteJetGenerators
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic

/-!
# The boundary affine auxiliary degeneration

Coordinates are `(e,h,f) = (0,1,2)`. We use the actual ordinary coefficient ideals
for `x_i (h^2+4ef)^m` and `x_i (ef)^m`, and the auxiliary weight is one on `e,f`
and zero on `h`, independent of the derivative order.
-/

namespace VOA.BoundaryAuxiliary
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R]

abbrev BasePoly (R : Type*) [CommRing R] := MvPolynomial (Fin 3) R
abbrev JetPoly (R : Type*) [CommRing R] := VOA.InfiniteJet.JetPoly R (Fin 3)

/-- The classical quadratic Casimir in paper coordinate order. -/
def casimir : BasePoly R := MvPolynomial.X 1 ^ 2 + 4 * MvPolynomial.X 0 * MvPolynomial.X 2

/-- The original three algebraic relations. -/
def baseRelation (m : ℕ) (i : Fin 3) : BasePoly R := MvPolynomial.X i * casimir ^ m

/-- The three auxiliary algebraic relations. -/
def auxiliaryRelation (m : ℕ) (i : Fin 3) : BasePoly R :=
  MvPolynomial.X i * (MvPolynomial.X 0 * MvPolynomial.X 2) ^ m

def baseIdeal (m : ℕ) : Ideal (BasePoly R) := Ideal.span (Set.range (baseRelation (R := R) m))
def auxiliaryBaseIdeal (m : ℕ) : Ideal (BasePoly R) :=
  Ideal.span (Set.range (auxiliaryRelation (R := R) m))

/-- The exact coefficient presentation of `B_m = J_infinity A_m`. -/
def sourceIdeal (m : ℕ) : Ideal (JetPoly R) :=
  VOA.InfiniteJet.coefficientIdeal (Set.range (baseRelation (R := R) m))

/-- The exact coefficient presentation of the auxiliary arc algebra `C_m`. -/
def auxiliaryIdeal (m : ℕ) : Ideal (JetPoly R) :=
  VOA.InfiniteJet.coefficientIdeal (Set.range (auxiliaryRelation (R := R) m))

abbrev Source (m : ℕ) := JetPoly R ⧸ sourceIdeal (R := R) m
abbrev Auxiliary (m : ℕ) := JetPoly R ⧸ auxiliaryIdeal (R := R) m

/-- These explicit coefficients give the genuine arc ideal of the original quotient. -/
theorem sourceIdeal_eq_jetIdeal (m : ℕ) :
    sourceIdeal (R := R) m = VOA.InfiniteJet.jetIdeal (baseIdeal (R := R) m) :=
  (VOA.InfiniteJet.jetIdeal_span_eq_coefficientIdeal _).symm

/-- The auxiliary quotient is also a genuine presented arc algebra. -/
theorem auxiliaryIdeal_eq_jetIdeal (m : ℕ) :
    auxiliaryIdeal (R := R) m = VOA.InfiniteJet.jetIdeal (auxiliaryBaseIdeal (R := R) m) :=
  (VOA.InfiniteJet.jetIdeal_span_eq_coefficientIdeal _).symm

/-- Auxiliary degree of a current. -/
def currentWeight (i : Fin 3) : ℕ := if i = 1 then 0 else 1
/-- Auxiliary degree of an ordinary jet coordinate. -/
def auxWeight (v : Fin 3 × ℕ) : ℕ := currentWeight v.1

/-- A series is coefficientwise homogeneous of a fixed auxiliary weight. -/
def SeriesHomogeneous (d : ℕ) (S : PowerSeries (JetPoly R)) : Prop :=
  ∀ n, (PowerSeries.coeff n S).IsWeightedHomogeneous auxWeight d

theorem seriesHomogeneous_current (i : Fin 3) :
    SeriesHomogeneous (R := R) (currentWeight i) (VOA.InfiniteJet.generatorSeries (R := R) i) := by
  intro n
  rw [VOA.InfiniteJet.coeff_generatorSeries]
  exact MvPolynomial.isWeightedHomogeneous_X R auxWeight (i, n)

theorem seriesHomogeneous_C (r : R) :
    SeriesHomogeneous (R := R) 0 (PowerSeries.C (MvPolynomial.C r)) := by
  intro n
  rw [PowerSeries.coeff_C]
  split_ifs
  · exact MvPolynomial.isWeightedHomogeneous_C auxWeight r
  · exact MvPolynomial.isWeightedHomogeneous_zero R auxWeight 0

theorem SeriesHomogeneous.mul {a b : ℕ} {S T : PowerSeries (JetPoly R)}
    (hS : SeriesHomogeneous a S) (hT : SeriesHomogeneous b T) :
    SeriesHomogeneous (a + b) (S * T) := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun ij _ => (hS ij.1).mul (hT ij.2))

theorem SeriesHomogeneous.pow {a : ℕ} {S : PowerSeries (JetPoly R)}
    (hS : SeriesHomogeneous a S) (m : ℕ) : SeriesHomogeneous (m * a) (S ^ m) := by
  induction m with
  | zero =>
      intro n
      simpa using seriesHomogeneous_C (R := R) 1 n
  | succ m ih =>
      simpa only [pow_succ, Nat.succ_mul] using ih.mul hS

/-- Coefficients above a series's homogeneous weight vanish under weighted projection. -/
theorem SeriesHomogeneous.component_ne {a : ℕ} {S : PowerSeries (JetPoly R)}
    (hS : SeriesHomogeneous a S) (d n : ℕ) (hd : d ≠ a) :
    MvPolynomial.weightedHomogeneousComponent auxWeight d (PowerSeries.coeff n S) = 0 :=
  (hS n).weightedHomogeneousComponent_ne d hd

/-- The polynomial top-component ideal, defined from all actual ideal elements and
an auxiliary degree cutoff above which their components vanish. -/
def initialIdeal (I : Ideal (JetPoly R)) : Ideal (JetPoly R) :=
  Ideal.span {p | ∃ g ∈ I, ∃ d : ℕ,
    (∀ k, d < k → MvPolynomial.weightedHomogeneousComponent auxWeight k g = 0) ∧
      MvPolynomial.weightedHomogeneousComponent auxWeight d g = p}

/-- Numeric scalar series have auxiliary degree zero. -/
theorem seriesHomogeneous_natCast (k : ℕ) :
    SeriesHomogeneous (R := R) 0 (k : PowerSeries (JetPoly R)) := by
  simpa only [map_natCast] using seriesHomogeneous_C (R := R) (k : R)

/-- The highest auxiliary-degree branch of the Casimir series. -/
def quadraticBranch : PowerSeries (JetPoly R) :=
  4 * VOA.InfiniteJet.generatorSeries (R := R) 0 * VOA.InfiniteJet.generatorSeries (R := R) 2

theorem seriesHomogeneous_quadraticBranch :
    SeriesHomogeneous (R := R) 2 quadraticBranch := by
  have he : SeriesHomogeneous (R := R) 1 (VOA.InfiniteJet.generatorSeries (R := R) 0) := by
    simpa [currentWeight] using seriesHomogeneous_current (R := R) 0
  have hf : SeriesHomogeneous (R := R) 1 (VOA.InfiniteJet.generatorSeries (R := R) 2) := by
    simpa [currentWeight] using seriesHomogeneous_current (R := R) 2
  exact ((seriesHomogeneous_natCast (R := R) 4).mul he).mul hf

/-- One literal binomial-expansion term of the boundary relation series. -/
def expansionTerm (m : ℕ) (i : Fin 3) (j : ℕ) : PowerSeries (JetPoly R) :=
  VOA.InfiniteJet.generatorSeries (R := R) i * quadraticBranch (R := R) ^ j *
    (VOA.InfiniteJet.generatorSeries (R := R) 1 ^ 2) ^ (m - j) * (m.choose j : PowerSeries (JetPoly R))

theorem seriesHomogeneous_expansionTerm (m : ℕ) (i : Fin 3) (j : ℕ) :
    SeriesHomogeneous (R := R) (currentWeight i + 2 * j) (expansionTerm m i j) := by
  have hh : SeriesHomogeneous (R := R) 0 (VOA.InfiniteJet.generatorSeries (R := R) 1) := by
    simpa [currentWeight] using seriesHomogeneous_current (R := R) 1
  have h := (((seriesHomogeneous_current (R := R) i).mul
    ((seriesHomogeneous_quadraticBranch (R := R)).pow j)).mul ((hh.pow 2).pow (m - j))).mul
      (seriesHomogeneous_natCast (R := R) (m.choose j))
  simpa [expansionTerm, Nat.mul_comm] using h

/-- The binomial expansion is proved for the actual universal generator series. -/
theorem relationSeries_expansion (m : ℕ) (i : Fin 3) :
    MvPolynomial.aeval (VOA.InfiniteJet.generatorSeries (R := R)) (baseRelation (R := R) m i) =
      ∑ j ∈ Finset.range (m + 1), expansionTerm (R := R) m i j := by
  simp only [baseRelation, casimir, map_mul, map_pow, map_add, map_ofNat, MvPolynomial.aeval_X]
  rw [add_comm, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [expansionTerm, quadraticBranch]
  ring

/-- The last binomial term is the auxiliary coefficient series times `4^m`. -/
theorem expansionTerm_last (m : ℕ) (i : Fin 3) :
    expansionTerm (R := R) m i m =
      PowerSeries.C ((4 : JetPoly R) ^ m) *
        MvPolynomial.aeval (VOA.InfiniteJet.generatorSeries (R := R)) (auxiliaryRelation (R := R) m i) := by
  simp only [expansionTerm, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one,
    mul_one, auxiliaryRelation, map_mul, map_pow, MvPolynomial.aeval_X]
  dsimp [quadraticBranch]
  simp only [mul_pow, map_pow, map_ofNat]
  ring

/-- The precise three initial coefficient identities of equation (2.15). -/
theorem relationCoefficient_top (m n : ℕ) (i : Fin 3) :
    MvPolynomial.weightedHomogeneousComponent auxWeight (currentWeight i + 2 * m)
      (VOA.InfiniteJet.relationCoefficient (baseRelation (R := R) m i) n) =
        (4 : JetPoly R) ^ m *
          VOA.InfiniteJet.relationCoefficient (auxiliaryRelation (R := R) m i) n := by
  rw [VOA.InfiniteJet.relationCoefficient, relationSeries_expansion, map_sum, map_sum]
  rw [Finset.sum_eq_single m]
  · rw [(seriesHomogeneous_expansionTerm (R := R) m i m n).weightedHomogeneousComponent_same]
    rw [expansionTerm_last, PowerSeries.coeff_C_mul]
    rfl
  · intro j hj hne
    apply (seriesHomogeneous_expansionTerm m i j).component_ne
    simp only [Finset.mem_range] at hj
    omega
  · simp

/-- The boundary relation coefficients have no components above the stated top degree. -/
theorem relationCoefficient_above_top (m n : ℕ) (i : Fin 3) (d : ℕ)
    (hd : currentWeight i + 2 * m < d) :
    MvPolynomial.weightedHomogeneousComponent auxWeight d
      (VOA.InfiniteJet.relationCoefficient (baseRelation (R := R) m i) n) = 0 := by
  rw [VOA.InfiniteJet.relationCoefficient, relationSeries_expansion, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  apply (seriesHomogeneous_expansionTerm m i j).component_ne
  simp only [Finset.mem_range] at hj
  omega

section Field
variable {K : Type*} [Field K] [CharZero K]

/-- The auxiliary relation ideal lies in the genuine initial ideal. Equality of initial
ideals is neither needed nor assumed. -/
theorem auxiliaryIdeal_le_initialIdeal (m : ℕ) :
    auxiliaryIdeal (R := K) m ≤ initialIdeal (sourceIdeal (R := K) m) := by
  rw [auxiliaryIdeal, VOA.InfiniteJet.coefficientIdeal, Ideal.span_le]
  rintro p ⟨f, ⟨i, rfl⟩, n, rfl⟩
  have hsource : VOA.InfiniteJet.relationCoefficient (baseRelation (R := K) m i) n ∈
      sourceIdeal (R := K) m :=
    VOA.InfiniteJet.relationCoefficient_mem_coefficientIdeal
      (Set.range (baseRelation (R := K) m)) (baseRelation (R := K) m i) ⟨i, rfl⟩ n
  have hi : (4 : JetPoly K) ^ m *
      VOA.InfiniteJet.relationCoefficient (auxiliaryRelation (R := K) m i) n ∈
        initialIdeal (sourceIdeal (R := K) m) := by
    apply Ideal.subset_span
    exact ⟨_, hsource, currentWeight i + 2 * m,
      fun d hd => relationCoefficient_above_top m n i d hd, relationCoefficient_top m n i⟩
  have hz : (4 : K) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hc : MvPolynomial.C (((4 : K) ^ m)⁻¹) * (4 : JetPoly K) ^ m = 1 := by
    rw [show (4 : JetPoly K) ^ m = MvPolynomial.C ((4 : K) ^ m) by
      rw [map_pow]
      congr 1]
    rw [← map_mul]
    simp [hz]
  have hx := (initialIdeal (sourceIdeal (R := K) m)).mul_mem_left
    (MvPolynomial.C (((4 : K) ^ m)⁻¹)) hi
  rw [← mul_assoc, hc, one_mul] at hx
  exact hx

end Field

end
end VOA.BoundaryAuxiliary
