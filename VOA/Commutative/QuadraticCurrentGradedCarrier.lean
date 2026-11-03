/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.QuadraticCurrentFunctionalCarrier

/-!
# Graded auxiliary/current carrier comparison

The conductor equivalence shifts derivative degree by its collision degree.
Every fixed-degree carrier is finite dimensional independently of any fusion
theorem. The graded equivalence therefore gives an actual equality of finite
dimensions, the input needed in the auxiliary character computation.
-/

namespace VOA.QuadraticCurrentFunctionalCarrier

open VOA.DeligneAuxiliaryCollision
open VOA.P3ResidualWindowPreservation
open VOA.MvPolynomialFiniteHomogeneous

noncomputable section

variable {K σ ρ : Type*} [Field K] [Fintype σ]

/-- A fixed derivative-degree piece of a tensor-polynomial carrier. -/
def degreePiece {m d : ℕ}
    (C : Submodule K (TensorPolynomial (K := K) (σ := σ) m d)) (r : ℕ) :
    Submodule K C where
  carrier := {p | ∀ t, (p.1 t).IsWeightedHomogeneous (fun _ => 1) r}
  zero_mem' := by
    intro t
    exact (MvPolynomial.weightedHomogeneousSubmodule K (fun _ : Particle m d => 1) r).zero_mem
  add_mem' := by
    intro p q hp hq t
    exact (MvPolynomial.weightedHomogeneousSubmodule K (fun _ => 1) r).add_mem (hp t) (hq t)
  smul_mem' := by
    intro a p hp t
    exact (MvPolynomial.weightedHomogeneousSubmodule K (fun _ => 1) r).smul_mem a (hp t)

/-- The homogeneous tensor coefficients give a finite-dimensional ambient space. -/
def degreePieceCoordinates {m d : ℕ}
    (C : Submodule K (TensorPolynomial (K := K) (σ := σ) m d)) (r : ℕ) :
    degreePiece C r →ₗ[K]
      ((Fin m → σ) → MvPolynomial.weightedHomogeneousSubmodule K
        (fun _ : Particle m d => 1) r) where
  toFun p t := ⟨p.1.1 t, p.property t⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype σ] in
theorem degreePieceCoordinates_injective {m d : ℕ}
    (C : Submodule K (TensorPolynomial (K := K) (σ := σ) m d)) (r : ℕ) :
    Function.Injective (degreePieceCoordinates C r) := by
  intro p q h
  apply Subtype.ext
  apply Subtype.ext
  funext t
  exact congrArg Subtype.val (congrFun h t)

instance degreePiece_finiteDimensional {m d : ℕ}
    (C : Submodule K (TensorPolynomial (K := K) (σ := σ) m d)) (r : ℕ) :
    FiniteDimensional K (degreePiece C r) := by
  letI : FiniteDimensional K
      (MvPolynomial.weightedHomogeneousSubmodule K (fun _ : Particle m d => 1) r) :=
    finiteDimensional_weightedHomogeneousSubmodule (fun _ => 1) (by intros; simp) r
  exact FiniteDimensional.of_injective (degreePieceCoordinates C r)
    (degreePieceCoordinates_injective C r)

/-- Conductor multiplication with its exact homogeneous degree shift. -/
def gradedConductorMap (Q : ρ → σ × σ → K) (m d r : ℕ) :
    degreePiece (currentCarrier Q m d) r →ₗ[K]
      degreePiece (auxiliaryCarrier Q m d) (conductorDegree m d + r) where
  toFun p := ⟨conductorMap Q m d p.1, fun t =>
    (conductor_isWeightedHomogeneous (K := K) m d).mul (p.property t)⟩
  map_add' _ _ := by apply Subtype.ext; exact (conductorMap Q m d).map_add _ _
  map_smul' _ _ := by apply Subtype.ext; exact (conductorMap Q m d).map_smul _ _

/-- The ungraded quotient is homogeneous in the required residual degree. -/
theorem gradedConductorMap_bijective [CharZero K]
    (Q : ρ → σ × σ → K) (m d r : ℕ) :
    Function.Bijective (gradedConductorMap Q m d r) := by
  constructor
  · intro p q h
    apply Subtype.ext
    apply (conductorMap_bijective Q m d).1
    exact congrArg Subtype.val h
  · intro p
    obtain ⟨q, hq⟩ := exists_current_quotient Q m d p.1
    have hdegree : q ∈ degreePiece (currentCarrier Q m d) r := by
      intro t
      exact quotient_weightedHomogeneous_of_factorization (fun _ => 1)
        (conductor (K := K) m d) (p.1.1 t) (q.1 t) (conductorDegree m d) r
        (conductor_ne_zero m d) (conductor_isWeightedHomogeneous m d) (p.property t) (hq t)
    refine ⟨⟨q, hdegree⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext t
    exact (hq t).symm

/-- Exact finite-degree factorization of the Deligne auxiliary functional model. -/
def gradedConductorEquiv [CharZero K] (Q : ρ → σ × σ → K) (m d r : ℕ) :
    degreePiece (currentCarrier Q m d) r ≃ₗ[K]
      degreePiece (auxiliaryCarrier Q m d) (conductorDegree m d + r) :=
  LinearEquiv.ofBijective (gradedConductorMap Q m d r) (gradedConductorMap_bijective Q m d r)

/-- The carrier character shifts by precisely the conductor degree. -/
theorem finrank_auxiliary_eq_current [CharZero K]
    (Q : ρ → σ × σ → K) (m d r : ℕ) :
    Module.finrank K (degreePiece (auxiliaryCarrier Q m d) (conductorDegree m d + r)) =
      Module.finrank K (degreePiece (currentCarrier Q m d) r) :=
  (gradedConductorEquiv Q m d r).finrank_eq.symm

/-- A polynomial multiple of the conductor cannot be homogeneous in a smaller
degree unless it vanishes. This handles the negative residual-degree sectors. -/
theorem conductor_mul_eq_zero_of_degree_lt (m d n : ℕ)
    (q : MvPolynomial (Particle m d) K)
    (hp : (conductor (K := K) m d * q).IsWeightedHomogeneous (fun _ => 1) n)
    (hn : n < conductorDegree m d) : conductor (K := K) m d * q = 0 := by
  by_cases hq : q = 0
  · rw [hq, mul_zero]
  obtain ⟨e, he⟩ := MvPolynomial.exists_coeff_ne_zero hq
  have hcomponent : MvPolynomial.weightedHomogeneousComponent (fun _ => 1)
      (Finsupp.weight (fun _ => 1) e) q ≠ 0 := by
    intro h
    have hcoeff := congrArg (MvPolynomial.coeff e) h
    simp [MvPolynomial.coeff_weightedHomogeneousComponent] at hcoeff
    exact he hcoeff
  have hzero := hp.weightedHomogeneousComponent_ne
    (conductorDegree m d + Finsupp.weight (fun _ => 1) e) (by omega)
  rw [weightedHomogeneousComponent_mul_left (fun _ => 1)
    (conductor_isWeightedHomogeneous m d)] at hzero
  exact False.elim ((mul_ne_zero (conductor_ne_zero m d) hcomponent) hzero)

/-- Every auxiliary degree piece below the conductor degree is zero. -/
theorem auxiliary_degreePiece_eq_zero_of_lt [CharZero K]
    (Q : ρ → σ × σ → K) (m d n : ℕ) (hn : n < conductorDegree m d)
    (p : degreePiece (auxiliaryCarrier Q m d) n) : p = 0 := by
  obtain ⟨q, hq⟩ := exists_current_quotient Q m d p.1
  apply Subtype.ext
  apply Subtype.ext
  funext t
  change p.1.1 t = 0
  rw [hq t]
  apply conductor_mul_eq_zero_of_degree_lt m d n (q.1 t) _ hn
  rw [← hq t]
  exact p.property t

end

end VOA.QuadraticCurrentFunctionalCarrier

section AxiomAudit
#print axioms VOA.QuadraticCurrentFunctionalCarrier.gradedConductorEquiv
#print axioms VOA.QuadraticCurrentFunctionalCarrier.finrank_auxiliary_eq_current
#print axioms VOA.QuadraticCurrentFunctionalCarrier.auxiliary_degreePiece_eq_zero_of_lt
end AxiomAudit
