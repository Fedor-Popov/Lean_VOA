/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.RootedMatching
import VOA.Commutative.P3ResidualWindowPreservation

/-!
# The scalar rooted Gordon conductor

For a numerical color profile `rho`, the root slots are `ColoredSlots rho`.  A slot of color
`c` contributes a root factor of multiplicity `c`, and two slots of colors `c_i,c_j` contribute
a collision factor of multiplicity `2 min(c_i,c_j)`.  This is the concrete polynomial
`delta_rho` occurring in the relative rooted-Gordon reconstruction equation.

This file defines that polynomial and proves its nonvanishing and exact homogeneous degree in
the explicit pair-sum form.  Identifying the pair-sum degree with the tail-count quadratic form
is a separate finite combinatorial theorem.
-/

namespace VOA.RootedGordonConductor

open scoped BigOperators

open VOA.CollisionCommonFactors
open VOA.MultispeciesParticlePolynomial
open VOA.RootedMatching

noncomputable section

universe u

variable {K : Type u} [Field K]

noncomputable local instance coloredSlotsFintype {n : ℕ} (rho : Fin n → ℕ) :
    Fintype (ColoredSlots rho) :=
  Fintype.ofFinite _

noncomputable local instance coloredSlotsLinearOrder {n : ℕ} (rho : Fin n → ℕ) :
    LinearOrder (ColoredSlots rho) :=
  LinearOrder.lift' (Fintype.equivFin (ColoredSlots rho))
    (Fintype.equivFin (ColoredSlots rho)).injective

/-- Integer color of a rooted slot. -/
def slotColor {n : ℕ} {rho : Fin n → ℕ} (i : ColoredSlots rho) : ℕ :=
  i.1.1

/-- Root-coordinate part of the scalar Gordon conductor. -/
def rootedGordonRootFactor {n : ℕ} (rho : Fin n → ℕ) :
    MvPolynomial (ColoredSlots rho) K :=
  ∏ i : ColoredSlots rho, MvPolynomial.X i ^ slotColor i

/-- Pair-collision part of the scalar Gordon conductor. -/
def rootedGordonPairFactor {n : ℕ} (rho : Fin n → ℕ) :
    MvPolynomial (ColoredSlots rho) K :=
  ∏ ij : IncreasingPair (ColoredSlots rho),
    collisionFactor (K := K) ij.1.1 ij.1.2 ^
      (2 * min (slotColor ij.1.1) (slotColor ij.1.2))

/-- The scalar rooted Gordon conductor `delta_rho`. -/
def rootedGordonConductor {n : ℕ} (rho : Fin n → ℕ) :
    MvPolynomial (ColoredSlots rho) K :=
  rootedGordonRootFactor (K := K) rho * rootedGordonPairFactor (K := K) rho

/-- The conductor degree before reindexing it as a sum of squared tail counts. -/
def rootedGordonConductorExplicitDegree {n : ℕ} (rho : Fin n → ℕ) : ℕ :=
  (∑ i : ColoredSlots rho, slotColor i) +
    ∑ ij : IncreasingPair (ColoredSlots rho),
      2 * min (slotColor ij.1.1) (slotColor ij.1.2)

theorem rootedGordonRootFactor_isWeightedHomogeneous {n : ℕ} (rho : Fin n → ℕ) :
    (rootedGordonRootFactor (K := K) rho).IsWeightedHomogeneous
      (fun _ : ColoredSlots rho => 1) (∑ i : ColoredSlots rho, slotColor i) := by
  classical
  have h := MvPolynomial.IsWeightedHomogeneous.prod
    (Finset.univ : Finset (ColoredSlots rho))
    (fun i => MvPolynomial.X i ^ slotColor i)
    (fun i => slotColor i) (w := fun _ => 1)
    (fun i _ => by
      convert
        (MvPolynomial.isWeightedHomogeneous_X K (fun _ => 1) i).pow (slotColor i) using 1 <;>
        simp)
  simpa [rootedGordonRootFactor] using h

theorem rootedGordonPairFactor_isWeightedHomogeneous {n : ℕ} (rho : Fin n → ℕ) :
    (rootedGordonPairFactor (K := K) rho).IsWeightedHomogeneous
      (fun _ : ColoredSlots rho => 1)
      (∑ ij : IncreasingPair (ColoredSlots rho),
        2 * min (slotColor ij.1.1) (slotColor ij.1.2)) := by
  classical
  have h := MvPolynomial.IsWeightedHomogeneous.prod
    (Finset.univ : Finset (IncreasingPair (ColoredSlots rho)))
    (fun ij => collisionFactor (K := K) ij.1.1 ij.1.2 ^
      (2 * min (slotColor ij.1.1) (slotColor ij.1.2)))
    (fun ij => 2 * min (slotColor ij.1.1) (slotColor ij.1.2))
    (w := fun _ => 1)
    (fun ij _ => by
      simpa only [nsmul_eq_mul, mul_one] using
        (VOA.P3ResidualWindowPreservation.collisionFactor_isWeightedHomogeneous_one
          (K := K) ij.1.1 ij.1.2).pow
            (2 * min (slotColor ij.1.1) (slotColor ij.1.2)))
  simpa [rootedGordonPairFactor] using h

/-- The scalar rooted Gordon conductor is homogeneous in the explicit pair-sum degree. -/
theorem rootedGordonConductor_isWeightedHomogeneous {n : ℕ} (rho : Fin n → ℕ) :
    (rootedGordonConductor (K := K) rho).IsWeightedHomogeneous
      (fun _ : ColoredSlots rho => 1) (rootedGordonConductorExplicitDegree rho) := by
  rw [rootedGordonConductor, rootedGordonConductorExplicitDegree]
  exact (rootedGordonRootFactor_isWeightedHomogeneous (K := K) rho).mul
    (rootedGordonPairFactor_isWeightedHomogeneous (K := K) rho)

/-- The scalar rooted Gordon conductor is nonzero. -/
theorem rootedGordonConductor_ne_zero {n : ℕ} (rho : Fin n → ℕ) :
    rootedGordonConductor (K := K) rho ≠ 0 := by
  classical
  rw [rootedGordonConductor]
  apply mul_ne_zero
  · rw [rootedGordonRootFactor]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact pow_ne_zero _ (MvPolynomial.X_ne_zero i)
  · rw [rootedGordonPairFactor]
    apply Finset.prod_ne_zero_iff.mpr
    intro ij _
    apply pow_ne_zero
    exact (collisionFactor_prime (K := K) ij.1.1 ij.1.2
      (ne_of_gt ij.2)).ne_zero

end

end VOA.RootedGordonConductor

section AxiomAudit
open VOA.RootedGordonConductor

#print axioms rootedGordonConductor_isWeightedHomogeneous
#print axioms rootedGordonConductor_ne_zero
end AxiomAudit
