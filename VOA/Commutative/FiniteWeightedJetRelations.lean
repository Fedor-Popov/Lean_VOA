/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.FiniteWeightedJet
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Weighted finite-jet relations

If a relation has weighted degree `D`, its Hasse--Schmidt coefficient of order `n` has jet weight
`D + n` when `x_i^(r)` has weight `baseWeight i + r`.  This file proves that statement and uses
it to show that a jet ideal obtained from a weighted-homogeneous presentation is a homogeneous
ideal.

The presentation is kept explicit as a set of relations.  The finite jet ideal built from all
elements of `Ideal.span S` agrees with the finite jet ideal built only from `S`; this follows from
the Cauchy coefficient formula.  In the stable range the new top coefficients have too high a
weight to create a relation, giving injectivity and hence an equivalence on the quotient submodules
represented by homogeneous polynomials.  No injectivity theorem for the whole quotient is asserted.
-/

namespace VOA.FiniteJet

open scoped BigOperators

universe uσ uR

noncomputable section

section ShiftedSeries

variable {R : Type uR} {σ : Type uσ} [CommSemiring R]

/-- Every coefficient of order `n` in `P` is weighted homogeneous of jet weight `D + n`. -/
def IsWeightShiftedSeries (baseWeight : σ → ℕ) (m D : ℕ)
    (P : Polynomial (JetPoly R σ m)) : Prop :=
  ∀ n, (P.coeff n).IsWeightedHomogeneous (jetWeight baseWeight m) (D + n)

namespace IsWeightShiftedSeries

theorem zero (baseWeight : σ → ℕ) (m D : ℕ) :
    IsWeightShiftedSeries (R := R) baseWeight m D 0 := by
  intro n
  exact MvPolynomial.isWeightedHomogeneous_zero R _ _

theorem constant (baseWeight : σ → ℕ) (m : ℕ) (r : R) :
    IsWeightShiftedSeries (R := R) baseWeight m 0
      (Polynomial.C (MvPolynomial.C r)) := by
  intro n
  cases n with
  | zero => simpa using MvPolynomial.isWeightedHomogeneous_C (jetWeight baseWeight m) r
  | succ n =>
      simp only [Polynomial.coeff_C, Nat.succ_ne_zero, ↓reduceIte]
      exact MvPolynomial.isWeightedHomogeneous_zero R _ _

theorem add {baseWeight : σ → ℕ} {m D : ℕ} {P Q : Polynomial (JetPoly R σ m)}
    (hP : IsWeightShiftedSeries baseWeight m D P)
    (hQ : IsWeightShiftedSeries baseWeight m D Q) :
    IsWeightShiftedSeries baseWeight m D (P + Q) := by
  intro n
  simpa only [Polynomial.coeff_add] using (hP n).add (hQ n)

theorem mul {baseWeight : σ → ℕ} {m D E : ℕ} {P Q : Polynomial (JetPoly R σ m)}
    (hP : IsWeightShiftedSeries baseWeight m D P)
    (hQ : IsWeightShiftedSeries baseWeight m E Q) :
    IsWeightShiftedSeries baseWeight m (D + E) (P * Q) := by
  intro n
  rw [Polynomial.coeff_mul]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro ab hab
  have hab_eq : ab.1 + ab.2 = n := Finset.mem_antidiagonal.mp hab
  have hmul := (hP ab.1).mul (hQ ab.2)
  convert hmul using 1
  omega

theorem pow {baseWeight : σ → ℕ} {m D : ℕ} {P : Polynomial (JetPoly R σ m)}
    (hP : IsWeightShiftedSeries baseWeight m D P) (k : ℕ) :
    IsWeightShiftedSeries baseWeight m (k * D) (P ^ k) := by
  induction k with
  | zero =>
      simpa using constant (R := R) baseWeight m (1 : R)
  | succ k ih =>
      simpa only [pow_succ, Nat.succ_mul] using ih.mul hP

theorem finsetProd (baseWeight : σ → ℕ) (m : ℕ) (s : Finset σ)
    (D : σ → ℕ) (P : σ → Polynomial (JetPoly R σ m))
    (hP : ∀ i ∈ s, IsWeightShiftedSeries baseWeight m (D i) (P i)) :
    IsWeightShiftedSeries baseWeight m (∑ i ∈ s, D i) (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using constant (R := R) baseWeight m (1 : R)
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      exact (hP i (Finset.mem_insert_self i s)).mul
        (ih fun j hj => hP j (Finset.mem_insert_of_mem hj))

theorem jetSeries (baseWeight : σ → ℕ) (m : ℕ) (i : σ) :
    IsWeightShiftedSeries (R := R) baseWeight m (baseWeight i)
      (FiniteJet.jetSeries (R := R) m i) := by
  intro n
  rw [jetSeries_coeff]
  by_cases hn : n ≤ m
  · rw [jetVariable_of_le (R := R) m i n hn]
    simpa only [jetWeight] using
      MvPolynomial.isWeightedHomogeneous_X R (jetWeight baseWeight m)
        (⟨i, ⟨n, Nat.lt_succ_iff.mpr hn⟩⟩ : JetVar σ m)
  · rw [jetVariable, dif_neg hn]
    exact MvPolynomial.isWeightedHomogeneous_zero R _ _

theorem finsuppProd (baseWeight : σ → ℕ) (m : ℕ) (d : σ →₀ ℕ) :
    IsWeightShiftedSeries (R := R) baseWeight m (Finsupp.weight baseWeight d)
      (d.prod fun i k => FiniteJet.jetSeries (R := R) m i ^ k) := by
  classical
  simpa only [Finsupp.prod, Finsupp.weight_apply, nsmul_eq_mul] using
    finsetProd (R := R) baseWeight m d.support (fun i => d i * baseWeight i)
      (fun i => FiniteJet.jetSeries (R := R) m i ^ d i)
      (fun i _ => (jetSeries (R := R) baseWeight m i).pow (d i))

end IsWeightShiftedSeries

theorem relationSeries_monomial (m : ℕ) (d : σ →₀ ℕ) (r : R) :
    relationSeries (R := R) m (MvPolynomial.monomial d r) =
      Polynomial.C (MvPolynomial.C r) *
        d.prod fun i k => FiniteJet.jetSeries (R := R) m i ^ k := by
  simp [relationSeries, jetSubst, MvPolynomial.aeval_monomial]

/-- A weighted-homogeneous relation of degree `D` produces a series whose order-`n` coefficient
has jet weight `D + n`. -/
theorem relationSeries_isWeightShiftedSeries (baseWeight : σ → ℕ) (m D : ℕ)
    {f : MvPolynomial σ R} (hf : f.IsWeightedHomogeneous baseWeight D) :
    IsWeightShiftedSeries (R := R) baseWeight m D (relationSeries (R := R) m f) := by
  induction hf using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
      simpa [relationSeries] using IsWeightShiftedSeries.zero (R := R) baseWeight m D
  | add p q hp hq ihp ihq =>
      simpa [relationSeries] using ihp.add ihq
  | monomial d r hd =>
      rw [relationSeries_monomial]
      have h := (IsWeightShiftedSeries.constant (R := R) baseWeight m r).mul
        (IsWeightShiftedSeries.finsuppProd (R := R) baseWeight m d)
      simpa only [zero_add, hd] using h

/-- The retained coefficient of a weighted-homogeneous relation has the expected shifted jet
weight. -/
theorem relationCoeff_isWeightedHomogeneous (baseWeight : σ → ℕ) (m D n : ℕ)
    {f : MvPolynomial σ R} (hf : f.IsWeightedHomogeneous baseWeight D) :
    (relationCoeff (R := R) m n f).IsWeightedHomogeneous
      (jetWeight baseWeight m) (D + n) := by
  exact relationSeries_isWeightShiftedSeries (R := R) baseWeight m D hf n

end ShiftedSeries

section RelationSets

variable {R : Type uR} {σ : Type uσ} [CommSemiring R]

/-- Retained jet coefficients of an explicit set of defining relations. -/
noncomputable def jetRelationSetOfSet (m : ℕ) (S : Set (MvPolynomial σ R)) :
    Set (JetPoly R σ m) :=
  {g | ∃ f ∈ S, ∃ j : Fin (m + 1), jetCoeff (R := R) m j f = g}

/-- The finite jet ideal generated by an explicit relation set. -/
noncomputable def jetIdealOfSet (m : ℕ) (S : Set (MvPolynomial σ R)) :
    Ideal (JetPoly R σ m) :=
  Ideal.span (jetRelationSetOfSet (R := R) m S)

theorem jetCoeff_mem_jetIdealOfSet (m : ℕ) (S : Set (MvPolynomial σ R))
    (f : MvPolynomial σ R) (hf : f ∈ S) (j : Fin (m + 1)) :
    jetCoeff (R := R) m j f ∈ jetIdealOfSet (R := R) m S := by
  exact Ideal.subset_span ⟨f, hf, j, rfl⟩

/-- Polynomials all of whose retained coefficients lie in `J` form an ideal. -/
noncomputable def coefficientPreimageIdeal (m : ℕ) (J : Ideal (JetPoly R σ m)) :
    Ideal (MvPolynomial σ R) where
  carrier := {f | ∀ n, n ≤ m → relationCoeff (R := R) m n f ∈ J}
  zero_mem' := by simp [relationCoeff, relationSeries]
  add_mem' hf hg n hn := by
    rw [relationCoeff_add]
    exact J.add_mem (hf n hn) (hg n hn)
  smul_mem' a f hf n hn := by
    rw [smul_eq_mul, relationCoeff_mul]
    apply J.sum_mem
    intro ab hab
    have hab_eq : ab.1 + ab.2 = n := Finset.mem_antidiagonal.mp hab
    exact J.mul_mem_left _ (hf ab.2 (by omega))

/-- Passing from a relation set to the ideal it generates does not change the finite jet ideal. -/
theorem jetIdeal_span_eq_jetIdealOfSet (m : ℕ) (S : Set (MvPolynomial σ R)) :
    jetIdeal (R := R) m (Ideal.span S) = jetIdealOfSet (R := R) m S := by
  apply le_antisymm
  · rw [jetIdeal]
    apply Ideal.span_le.mpr
    rintro g ⟨fj, rfl⟩
    change jetCoeff (R := R) m fj.2 fj.1.1 ∈ jetIdealOfSet (R := R) m S
    let J := jetIdealOfSet (R := R) m S
    have hspan : Ideal.span S ≤ coefficientPreimageIdeal (R := R) m J := by
      apply Ideal.span_le.mpr
      intro f hf n hn
      simpa only [jetCoeff_apply] using
        jetCoeff_mem_jetIdealOfSet (R := R) m S f hf ⟨n, Nat.lt_succ_iff.mpr hn⟩
    exact hspan fj.1.2 fj.2 (Nat.lt_succ_iff.mp fj.2.isLt)
  · rw [jetIdealOfSet]
    apply Ideal.span_le.mpr
    rintro g ⟨f, hf, j, rfl⟩
    exact jetCoeff_mem_jetIdeal (R := R) m (Ideal.span S) f (Ideal.subset_span hf) j

/-- The genuinely new coefficient layer introduced when passing from order `m` to `m + 1`. -/
noncomputable def topJetRelationSet (m : ℕ) (S : Set (MvPolynomial σ R)) :
    Set (JetPoly R σ (m + 1)) :=
  {g | ∃ f ∈ S, relationCoeff (R := R) (m + 1) (m + 1) f = g}

noncomputable def topJetIdeal (m : ℕ) (S : Set (MvPolynomial σ R)) :
    Ideal (JetPoly R σ (m + 1)) :=
  Ideal.span (topJetRelationSet (R := R) m S)

/-- At the next order, the relation ideal is generated by the image of the old relation ideal and
the single new top coefficient of each defining relation. -/
theorem jetIdealOfSet_succ_eq (m : ℕ) (S : Set (MvPolynomial σ R)) :
    jetIdealOfSet (R := R) (m + 1) S =
      Ideal.map (jetOrderHom (R := R) m).toRingHom (jetIdealOfSet (R := R) m S) ⊔
        topJetIdeal (R := R) m S := by
  apply le_antisymm
  · rw [jetIdealOfSet]
    apply Ideal.span_le.mpr
    rintro g ⟨f, hf, j, rfl⟩
    by_cases hj : j.val ≤ m
    · apply Submodule.mem_sup_left
      rw [jetCoeff_apply, ← jetOrderHom_relationCoeff (R := R) m f j hj]
      apply Ideal.mem_map_of_mem
      simpa only [jetCoeff_apply] using
        jetCoeff_mem_jetIdealOfSet (R := R) m S f hf
          ⟨j, Nat.lt_succ_iff.mpr hj⟩
    · apply Submodule.mem_sup_right
      have hjtop : j.val = m + 1 := by
        have hjbound : j.val ≤ m + 1 := Nat.le_of_lt_succ j.isLt
        omega
      rw [jetCoeff_apply, hjtop]
      exact Ideal.subset_span ⟨f, hf, rfl⟩
  · apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro g hg
      change jetOrderHom (R := R) m g ∈ jetIdealOfSet (R := R) (m + 1) S
      rw [← jetIdeal_span_eq_jetIdealOfSet] at hg ⊢
      exact jetOrderHom_mem_jetIdeal (R := R) m (Ideal.span S) g hg
    · rw [topJetIdeal]
      apply Ideal.span_le.mpr
      rintro g ⟨f, hf, rfl⟩
      simpa only [jetCoeff_apply] using
        jetCoeff_mem_jetIdealOfSet (R := R) (m + 1) S f hf
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩

end RelationSets

section LowWeightSpan

variable {R : Type uR} {τ : Type*} [CommSemiring R]

/-- Multiplying a homogeneous polynomial of degree `G` cannot create a component of smaller
degree. -/
theorem weightedHomogeneousComponent_mul_eq_zero_of_lt (w : τ → ℕ) (N G : ℕ)
    {g : MvPolynomial τ R} (hg : g.IsWeightedHomogeneous w G) (hNG : N < G)
    (a : MvPolynomial τ R) :
    MvPolynomial.weightedHomogeneousComponent w N (a * g) = 0 := by
  classical
  apply MvPolynomial.weightedHomogeneousComponent_eq_zero'
  intro d hd hweight
  have hcoeff : MvPolynomial.coeff d (a * g) ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  rw [MvPolynomial.coeff_mul] at hcoeff
  obtain ⟨uv, huv, huvcoeff⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff
  have hgcoeff : MvPolynomial.coeff uv.2 g ≠ 0 := right_ne_zero_of_mul huvcoeff
  have hG := hg hgcoeff
  have huv_eq : uv.1 + uv.2 = d := Finset.mem_antidiagonal.mp huv
  have hweights := congrArg (Finsupp.weight w) huv_eq
  simp only [map_add] at hweights
  omega

/-- An ideal generated in degrees strictly above `N` has zero weight-`N` component. -/
theorem weightedHomogeneousComponent_eq_zero_of_mem_span_high (w : τ → ℕ) (N : ℕ)
    (H : Set (MvPolynomial τ R))
    (hH : ∀ g ∈ H, ∃ G, N < G ∧ g.IsWeightedHomogeneous w G)
    {p : MvPolynomial τ R} (hp : p ∈ Ideal.span H) :
    MvPolynomial.weightedHomogeneousComponent w N p = 0 := by
  rw [Ideal.span, Finsupp.span_eq_range_linearCombination] at hp
  rw [LinearMap.mem_range] at hp
  obtain ⟨c, rfl⟩ := hp
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply Finset.sum_eq_zero
  intro g hg
  rw [smul_eq_mul]
  obtain ⟨G, hNG, hhom⟩ := hH g.1 g.2
  exact weightedHomogeneousComponent_mul_eq_zero_of_lt w N G hhom hNG (c g)

end LowWeightSpan

section HomogeneousIdeal

variable {R : Type uR} {σ : Type uσ} [CommSemiring R]

local instance weightedJetGradedAlgebra (baseWeight : σ → ℕ) (m : ℕ) :
    GradedAlgebra (MvPolynomial.weightedHomogeneousSubmodule R (jetWeight baseWeight m)) :=
  MvPolynomial.weightedGradedAlgebra R (jetWeight baseWeight m)

/-- A presentation set is weighted homogeneous when each relation is homogeneous, with its degree
allowed to depend on the relation. -/
def IsWeightedHomogeneousRelationSet (baseWeight : σ → ℕ)
    (S : Set (MvPolynomial σ R)) : Prop :=
  ∀ f ∈ S, ∃ D, f.IsWeightedHomogeneous baseWeight D

/-- A jet ideal generated by an explicit weighted-homogeneous relation set is homogeneous for the
shifted jet grading. -/
theorem jetIdealOfSet_isHomogeneous (baseWeight : σ → ℕ) (m : ℕ)
    (S : Set (MvPolynomial σ R)) (hS : IsWeightedHomogeneousRelationSet baseWeight S) :
    (jetIdealOfSet (R := R) m S).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R (jetWeight baseWeight m)) := by
  unfold jetIdealOfSet
  apply Ideal.homogeneous_span
  intro g hg
  rcases hg with ⟨f, hf, j, rfl⟩
  obtain ⟨D, hD⟩ := hS f hf
  refine ⟨D + j, ?_⟩
  simpa only [jetCoeff_apply] using
    relationCoeff_isWeightedHomogeneous (R := R) baseWeight m D j hD

/-- Therefore the intrinsic finite jet ideal of an ideal generated by homogeneous relations is
homogeneous. -/
theorem jetIdeal_span_isHomogeneous (baseWeight : σ → ℕ) (m : ℕ)
    (S : Set (MvPolynomial σ R)) (hS : IsWeightedHomogeneousRelationSet baseWeight S) :
    (jetIdeal (R := R) m (Ideal.span S)).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R (jetWeight baseWeight m)) := by
  rw [jetIdeal_span_eq_jetIdealOfSet]
  exact jetIdealOfSet_isHomogeneous (R := R) baseWeight m S hS

/-- The image of the old homogeneous jet ideal is homogeneous in the next jet ring. -/
theorem map_jetIdealOfSet_isHomogeneous (baseWeight : σ → ℕ) (m : ℕ)
    (S : Set (MvPolynomial σ R)) (hS : IsWeightedHomogeneousRelationSet baseWeight S) :
    (Ideal.map (jetOrderHom (R := R) m).toRingHom (jetIdealOfSet (R := R) m S)).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R (jetWeight baseWeight (m + 1))) := by
  rw [jetIdealOfSet, Ideal.map_span]
  apply Ideal.homogeneous_span
  intro g hg
  rcases hg with ⟨q, ⟨f, hf, j, rfl⟩, rfl⟩
  obtain ⟨D, hD⟩ := hS f hf
  refine ⟨D + j, ?_⟩
  apply jetOrderHom_isWeightedHomogeneous
  simpa only [jetCoeff_apply] using
    relationCoeff_isWeightedHomogeneous (R := R) baseWeight m D j hD

/-- The new top coefficient layer has no component of weight `N <= m`. -/
theorem topJetIdeal_weightedHomogeneousComponent_eq_zero (baseWeight : σ → ℕ)
    (m N : ℕ) (hlarge : N ≤ m) (S : Set (MvPolynomial σ R))
    (hS : IsWeightedHomogeneousRelationSet baseWeight S)
    {p : JetPoly R σ (m + 1)} (hp : p ∈ topJetIdeal (R := R) m S) :
    MvPolynomial.weightedHomogeneousComponent (jetWeight baseWeight (m + 1)) N p = 0 := by
  apply weightedHomogeneousComponent_eq_zero_of_mem_span_high
    (jetWeight baseWeight (m + 1)) N (topJetRelationSet (R := R) m S)
  · intro g hg
    rcases hg with ⟨f, hf, rfl⟩
    obtain ⟨D, hD⟩ := hS f hf
    refine ⟨D + (m + 1), by omega, ?_⟩
    exact relationCoeff_isWeightedHomogeneous (R := R) baseWeight (m + 1) D (m + 1) hD
  · exact hp

/-- A homogeneous element of stable low weight in the next jet ideal already belongs to the ideal
generated by the image of the old jet ideal. -/
theorem isWeightedHomogeneous_mem_map_jetIdealOfSet_of_mem_succ
    (baseWeight : σ → ℕ) (m N : ℕ) (hlarge : N ≤ m)
    (S : Set (MvPolynomial σ R)) (hS : IsWeightedHomogeneousRelationSet baseWeight S)
    {p : JetPoly R σ (m + 1)}
    (hp : p.IsWeightedHomogeneous (jetWeight baseWeight (m + 1)) N)
    (hpIdeal : p ∈ jetIdealOfSet (R := R) (m + 1) S) :
    p ∈ Ideal.map (jetOrderHom (R := R) m).toRingHom (jetIdealOfSet (R := R) m S) := by
  rw [jetIdealOfSet_succ_eq] at hpIdeal
  rcases Submodule.mem_sup.mp hpIdeal with ⟨a, ha, b, hb, hab⟩
  have hmapHom := map_jetIdealOfSet_isHomogeneous (R := R) baseWeight m S hS
  have haN := hmapHom N ha
  have hdecomp :
      ((DirectSum.decompose
          (MvPolynomial.weightedHomogeneousSubmodule R (jetWeight baseWeight (m + 1))) a N :
          MvPolynomial.weightedHomogeneousSubmodule R (jetWeight baseWeight (m + 1)) N) :
        JetPoly R σ (m + 1)) =
        MvPolynomial.weightedHomogeneousComponent (jetWeight baseWeight (m + 1)) N a := by
    change
      ((MvPolynomial.weightedDecomposition R (jetWeight baseWeight (m + 1))).decompose' a N :
        JetPoly R σ (m + 1)) = _
    exact MvPolynomial.weightedDecomposition.decompose'_apply R
      (jetWeight baseWeight (m + 1)) a N
  rw [hdecomp] at haN
  have hbN := topJetIdeal_weightedHomogeneousComponent_eq_zero (R := R)
    baseWeight m N hlarge S hS hb
  have habN := congrArg
    (MvPolynomial.weightedHomogeneousComponent (jetWeight baseWeight (m + 1)) N) hab
  rw [map_add, hbN, add_zero, hp.weightedHomogeneousComponent_same] at habN
  exact habN ▸ haN

/-- Exact stable low-weight intersection: for a homogeneous polynomial of weight `N <= m`, its
image lies in the next relation ideal exactly when it already lay in the old relation ideal. -/
theorem jetOrderHom_mem_jetIdealOfSet_succ_iff (baseWeight : σ → ℕ) (m N : ℕ)
    (hlarge : N ≤ m) (S : Set (MvPolynomial σ R))
    (hS : IsWeightedHomogeneousRelationSet baseWeight S) {p : JetPoly R σ m}
    (hp : p.IsWeightedHomogeneous (jetWeight baseWeight m) N) :
    jetOrderHom (R := R) m p ∈ jetIdealOfSet (R := R) (m + 1) S ↔
      p ∈ jetIdealOfSet (R := R) m S := by
  constructor
  · intro hmem
    have himage := isWeightedHomogeneous_mem_map_jetIdealOfSet_of_mem_succ
      (R := R) baseWeight m N hlarge S hS
      (jetOrderHom_isWeightedHomogeneous baseWeight m N hp) hmem
    have hmap_le :
        Ideal.map (jetOrderHom (R := R) m).toRingHom (jetIdealOfSet (R := R) m S) ≤
          Ideal.comap
            (MvPolynomial.killCompl (jetVarSucc_injective (σ := σ) m)).toRingHom
            (jetIdealOfSet (R := R) m S) := by
      rw [Ideal.map_le_iff_le_comap]
      intro q hq
      change MvPolynomial.killCompl (jetVarSucc_injective (σ := σ) m)
        (jetOrderHom (R := R) m q) ∈ jetIdealOfSet (R := R) m S
      simpa [jetOrderHom] using hq
    have := hmap_le himage
    change MvPolynomial.killCompl (jetVarSucc_injective (σ := σ) m)
      (jetOrderHom (R := R) m p) ∈ jetIdealOfSet (R := R) m S at this
    simpa [jetOrderHom] using this
  · intro hmem
    rw [jetIdealOfSet_succ_eq]
    exact Submodule.mem_sup_left (Ideal.mem_map_of_mem _ hmem)

end HomogeneousIdeal

section WeightedKernelAssembly

variable {K : Type*} [CommRing K]
variable {τ D : Type*} [AddCommMonoid D]

/-- To prove equality with a candidate ideal, it suffices to put every weighted homogeneous
component of every element of the larger ideal into the candidate.  This is the finite-support
assembly step used after a bidegree-by-bidegree carrier or Hilbert squeeze. -/
theorem ideal_eq_of_le_of_weightedHomogeneousComponents_mem
    (w : τ → D) (I J : Ideal (MvPolynomial τ K))
    (hJI : J ≤ I)
    (hcomponent : ∀ p ∈ I, ∀ d,
      MvPolynomial.weightedHomogeneousComponent w d p ∈ J) :
    I = J := by
  apply le_antisymm
  · intro p hp
    rw [← MvPolynomial.sum_weightedHomogeneousComponent w p]
    rw [finsum_eq_sum _ (MvPolynomial.weightedHomogeneousComponent_finsupp p)]
    exact J.sum_mem fun d _ => hcomponent p hp d
  · exact hJI

/-- Exact polynomial-kernel form of the preceding assembly lemma.  The easy relation
containment and componentwise carrier bound are deliberately kept as separate hypotheses. -/
theorem ringHom_kernel_eq_of_weightedHomogeneousComponents_mem
    {A : Type*} [Semiring A]
    (w : τ → D) (φ : MvPolynomial τ K →+* A)
    (J : Ideal (MvPolynomial τ K))
    (hJ : J ≤ RingHom.ker φ)
    (hcomponent : ∀ p ∈ RingHom.ker φ, ∀ d,
      MvPolynomial.weightedHomogeneousComponent w d p ∈ J) :
    RingHom.ker φ = J :=
  ideal_eq_of_le_of_weightedHomogeneousComponents_mem
    w (RingHom.ker φ) J hJ hcomponent

end WeightedKernelAssembly

section PresentedStabilization

variable {R : Type uR} {σ : Type uσ} [CommRing R]

/-- Homogeneous defining relations prevent new order-`m+1` relations from creating a kernel on
the weight-`N` image when `N <= m`. -/
theorem presentedJetWeightImageOrderHom_injective_of_homogeneousRelations
    (baseWeight : σ → ℕ) (m N : ℕ) (hlarge : N ≤ m)
    (S : Set (MvPolynomial σ R)) (hS : IsWeightedHomogeneousRelationSet baseWeight S) :
    Function.Injective
      (presentedJetWeightImageOrderHom (R := R) baseWeight m N (Ideal.span S)) := by
  intro x y hxy
  rcases x.2 with ⟨p, hp⟩
  rcases y.2 with ⟨q, hq⟩
  change presentedJetMk (R := R) m (Ideal.span S) p.1 = x.1 at hp
  change presentedJetMk (R := R) m (Ideal.span S) q.1 = y.1 at hq
  have htarget := congrArg Subtype.val hxy
  change presentedJetOrderHom (R := R) m (Ideal.span S) x.1 =
    presentedJetOrderHom (R := R) m (Ideal.span S) y.1 at htarget
  rw [← hp, ← hq] at htarget
  have htargetIdeal := Ideal.Quotient.eq.mp htarget
  rw [← map_sub] at htargetIdeal
  rw [jetIdeal_span_eq_jetIdealOfSet] at htargetIdeal
  have hpqHom : (p.1 - q.1).IsWeightedHomogeneous (jetWeight baseWeight m) N :=
    (JetWeightPiece R baseWeight m N).sub_mem p.2 q.2
  have hpqIdeal :=
    (jetOrderHom_mem_jetIdealOfSet_succ_iff (R := R) baseWeight m N hlarge S hS hpqHom).mp
      htargetIdeal
  apply Subtype.ext
  rw [← hp, ← hq]
  apply Ideal.Quotient.eq.mpr
  rw [jetIdeal_span_eq_jetIdealOfSet]
  exact hpqIdeal

/-- For a weighted-homogeneous presentation and positive generator weights, successive presented
weight images are linearly equivalent in the stable range.  This is a statement about the image
of homogeneous representatives; it does not assert injectivity of the whole quotient map. -/
noncomputable def presentedJetWeightImageOrderEquiv_of_homogeneousRelations
    (baseWeight : σ → ℕ) (hpositive : ∀ i, 0 < baseWeight i)
    (m N : ℕ) (hlarge : N ≤ m) (S : Set (MvPolynomial σ R))
    (hS : IsWeightedHomogeneousRelationSet baseWeight S) :
    PresentedJetWeightImage (R := R) baseWeight m N (Ideal.span S) ≃ₗ[R]
      PresentedJetWeightImage (R := R) baseWeight (m + 1) N (Ideal.span S) :=
  LinearEquiv.ofBijective
    (presentedJetWeightImageOrderHom (R := R) baseWeight m N (Ideal.span S))
    ⟨presentedJetWeightImageOrderHom_injective_of_homogeneousRelations
        (R := R) baseWeight m N hlarge S hS,
      presentedJetWeightImageOrderHom_surjective (R := R)
        baseWeight hpositive m N hlarge (Ideal.span S)⟩

end PresentedStabilization

end

end VOA.FiniteJet
