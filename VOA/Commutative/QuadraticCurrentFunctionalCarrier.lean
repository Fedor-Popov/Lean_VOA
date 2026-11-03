/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.DeligneAuxiliaryCollision

/-!
# Tensor-valued current carriers for arbitrary quadratic relations

Fix a finite basis `σ` of the current space and quadratic equations with
coefficients `Q r (x,y)`. A polynomial has one component for each assignment
of basis vectors to current slots. Simultaneous permutation of slots and roots
expresses commutativity. For every pair of current slots, every quadratic
relation, and every spectator assignment, its projected collision must vanish.

These are literal polynomial kernels, not the image of a proposed fusion module.
The identification with the restricted dual of the presented arc algebra is a
separate step. The auxiliary collision equations below encode `XS = S² = 0`.
-/

namespace VOA.QuadraticCurrentFunctionalCarrier

open VOA.CollisionCommonFactors
open VOA.DeligneAuxiliaryCollision

noncomputable section

variable {K σ ρ : Type*} [Field K] [Fintype σ]

/-- Tensor coefficients in a chosen basis of the current vector space. -/
abbrev TensorPolynomial (m d : ℕ) :=
  (Fin m → σ) → MvPolynomial (Particle m d) K

/-- A particle permutation realizes `g` on the current slots. Its action on
the auxiliary slots can be arbitrary. -/
def ExtendsCurrentPermutation {m d : ℕ}
    (e : Equiv.Perm (Particle m d)) (g : Equiv.Perm (Fin m)) : Prop :=
  ∀ i, e (i.castAdd d) = (g i).castAdd d

/-- A permutation extending a current permutation necessarily preserves the
current and auxiliary populations. -/
theorem preserves_current_of_extends {m d : ℕ}
    (e : Equiv.Perm (Particle m d)) (g : Equiv.Perm (Fin m))
    (he : ExtendsCurrentPermutation e g) :
    ∀ i, (e i).val < m ↔ i.val < m := by
  intro i
  constructor
  · intro hi
    let j : Fin m := ⟨(e i).val, hi⟩
    have hij : e i = j.castAdd d := by ext; rfl
    have hpre : e ((g.symm j).castAdd d) = e i := by
      rw [he, g.apply_symm_apply, hij]
    have hi' := e.injective hpre
    rw [← hi']
    exact (g.symm j).isLt
  · intro hi
    let j : Fin m := ⟨i.val, hi⟩
    have hij : j.castAdd d = i := by ext; rfl
    rw [← hij, he]
    exact (g j).isLt

/-- Simultaneous root/tensor permutation invariance, including all auxiliary
permutations. This is the polynomial form of commutativity. -/
def Symmetric {m d : ℕ} (p : TensorPolynomial (K := K) (σ := σ) m d) : Prop :=
  ∀ (e : Equiv.Perm (Particle m d)) (g : Equiv.Perm (Fin m)),
    ExtendsCurrentPermutation e g → ∀ t,
      MvPolynomial.rename e (p t) = p (t ∘ g.symm)

/-- Insert the two tensor indices tested by a quadratic equation, retaining
every other tensor index as a spectator. -/
def insertPair {m : ℕ} (ij : IncreasingPair (Fin m)) (t : Fin m → σ)
    (xy : σ × σ) : Fin m → σ :=
  Function.update (Function.update t ij.1.1 xy.1) ij.1.2 xy.2

/-- The collision coefficient of one quadratic equation with fixed spectators. -/
def currentReadback {m d : ℕ} (q : σ × σ → K)
    (ij : IncreasingPair (Fin m)) (t : Fin m → σ)
    (p : TensorPolynomial (K := K) (σ := σ) m d) :=
  projectedDiagonal (ij.1.1.castAdd d) (ij.1.2.castAdd d)
    ((Fin.castAdd_injective m d).ne (ne_of_gt ij.2)) q
    (fun xy => p (insertPair ij t xy))

/-- All quadratic equations, with every pair of slots and every spectator. -/
def CurrentEquations {m d : ℕ} (Q : ρ → σ × σ → K)
    (p : TensorPolynomial (K := K) (σ := σ) m d) : Prop :=
  ∀ r ij t, currentReadback (Q r) ij t p = 0

/-- The full polynomial current carrier with auxiliary spectator variables. -/
def currentCarrier (Q : ρ → σ × σ → K) (m d : ℕ) :
    Submodule K (TensorPolynomial (K := K) (σ := σ) m d) where
  carrier := {p | Symmetric p ∧ CurrentEquations Q p}
  zero_mem' := by
    constructor
    · intro e g he t
      simp
    · intro r ij t
      simp [currentReadback, projectedDiagonal]
  add_mem' := by
    intro p q hp hq
    constructor
    · intro e g he t
      simp only [Pi.add_apply, map_add, hp.1 e g he t, hq.1 e g he t]
    · intro r ij t
      have hread : currentReadback (Q r) ij t (p + q) =
          currentReadback (Q r) ij t p + currentReadback (Q r) ij t q := by
        simp [currentReadback, projectedDiagonal, mul_add, Finset.sum_add_distrib]
      rw [hread, hp.2, hq.2, zero_add]
  smul_mem' := by
    intro a p hp
    constructor
    · intro e g he t
      simpa using congrArg (fun f => a • f) (hp.1 e g he t)
    · intro r ij t
      have hread : currentReadback (Q r) ij t (a • p) =
          a • currentReadback (Q r) ij t p := by
        simp [currentReadback, projectedDiagonal, Finset.mul_sum,
          Algebra.smul_def, mul_left_comm]
      rw [hread, hp.2, smul_zero]

/-- Multiplication by the auxiliary conductor preserves and reflects every
current equation. -/
theorem currentEquations_conductor_iff (Q : ρ → σ × σ → K) (m d : ℕ)
    (p : TensorPolynomial (K := K) (σ := σ) m d) :
    CurrentEquations Q (fun t => conductor (K := K) m d * p t) ↔ CurrentEquations Q p := by
  unfold CurrentEquations currentReadback
  apply forall_congr'
  intro r
  apply forall_congr'
  intro ij
  apply forall_congr'
  intro t
  exact projectedDiagonal_conductor_eq_zero_iff m d _ _ _
    ij.1.1.isLt ij.1.2.isLt _ _

omit [Fintype σ] in
/-- The conductor is a scalar invariant, so dividing it out also preserves
simultaneous root/tensor symmetry. -/
theorem symmetric_conductor_iff (m d : ℕ)
    (p : TensorPolynomial (K := K) (σ := σ) m d) :
    Symmetric (fun t => conductor (K := K) m d * p t) ↔ Symmetric p := by
  unfold Symmetric
  apply forall_congr'
  intro e
  apply forall_congr'
  intro g
  apply forall_congr'
  intro he
  apply forall_congr'
  intro t
  rw [map_mul, conductor_rename_invariant m d e (preserves_current_of_extends e g he)]
  exact ⟨fun h => mul_left_cancel₀ (conductor_ne_zero (K := K) m d) h,
    fun h => congrArg (fun f => conductor (K := K) m d * f) h⟩

/-- The literal full current carrier is preserved and reflected by conductor
multiplication; neither freeness nor fusion comparison is assumed. -/
theorem mem_currentCarrier_conductor_iff (Q : ρ → σ × σ → K) (m d : ℕ)
    (p : TensorPolynomial (K := K) (σ := σ) m d) :
    (fun t => conductor (K := K) m d * p t) ∈ currentCarrier Q m d ↔
      p ∈ currentCarrier Q m d := by
  exact and_congr (symmetric_conductor_iff m d p) (currentEquations_conductor_iff Q m d p)

/-- Add the literal mixed and auxiliary diagonal equations to the current
carrier. Symmetry already includes permutations of the auxiliary fields. -/
def auxiliaryCarrier (Q : ρ → σ × σ → K) (m d : ℕ) :
    Submodule K (TensorPolynomial (K := K) (σ := σ) m d) where
  carrier := {p | p ∈ currentCarrier Q m d ∧
    ∀ t (ij : Pair m d), m ≤ ij.1.2.val →
      collisionMap ij.1.2 ij.1.1 (ne_of_lt ij.2) (p t) = 0}
  zero_mem' := ⟨(currentCarrier Q m d).zero_mem, by intros; simp⟩
  add_mem' := by
    intro p q hp hq
    refine ⟨(currentCarrier Q m d).add_mem hp.1 hq.1, ?_⟩
    intro t ij haux
    simp only [Pi.add_apply, map_add, hp.2 t ij haux, hq.2 t ij haux, add_zero]
  smul_mem' := by
    intro a p hp
    refine ⟨(currentCarrier Q m d).smul_mem a hp.1, ?_⟩
    intro t ij haux
    change collisionMap ij.1.2 ij.1.1 _ (a • p t) = 0
    rw [map_smul, hp.2 t ij haux, smul_zero]

omit [Fintype σ] in
/-- The simultaneous tensor symmetry includes scalar exchange symmetry of
any pair of auxiliary variables. -/
theorem auxiliary_swap_invariant {m d : ℕ}
    (p : TensorPolynomial (K := K) (σ := σ) m d) (hp : Symmetric p)
    (ij : Pair m d) (haux : m ≤ ij.1.1.val) (t : Fin m → σ) :
    swapVariables ij.1.2 ij.1.1 (p t) = p t := by
  have he : ExtendsCurrentPermutation (Equiv.swap ij.1.2 ij.1.1) (Equiv.refl (Fin m)) := by
    intro i
    have hi1 : i.castAdd d ≠ ij.1.1 := by
      intro h
      have hv := congrArg Fin.val h
      have hi := i.isLt
      simp only [Fin.val_castAdd] at hv
      omega
    have hi2 : i.castAdd d ≠ ij.1.2 := by
      intro h
      have hv := congrArg Fin.val h
      have hi := i.isLt
      have hij : ij.1.1.val < ij.1.2.val := ij.2
      simp only [Fin.val_castAdd] at hv
      omega
    exact Equiv.swap_apply_of_ne_of_ne hi2 hi1
  simpa [swapVariables] using hp (Equiv.swap ij.1.2 ij.1.1) (Equiv.refl _) he t

/-- The full auxiliary carrier has a unique coordinatewise conductor quotient,
and that quotient lies in the literal current carrier. -/
theorem exists_current_quotient [CharZero K] (Q : ρ → σ × σ → K) (m d : ℕ)
    (p : auxiliaryCarrier Q m d) :
    ∃ q : currentCarrier Q m d, ∀ t,
      p.1 t = conductor (K := K) m d * q.1 t := by
  have hdiv : ∀ t, conductor (K := K) m d ∣ p.1 t := by
    intro t
    exact conductor_dvd_of_collisions m d (p.1 t) (p.property.2 t)
      (fun ij haux => auxiliary_swap_invariant p.1 p.property.1.1 ij haux t)
  choose q hq using hdiv
  have hfac : p.1 = fun t => conductor (K := K) m d * q t := funext hq
  have hcurrent : q ∈ currentCarrier Q m d := by
    apply (mem_currentCarrier_conductor_iff Q m d q).mp
    rw [← hfac]
    exact p.property.1
  exact ⟨⟨q, hcurrent⟩, hq⟩

/-- Multiplication by the universal conductor on the full current carrier. -/
def conductorMap (Q : ρ → σ × σ → K) (m d : ℕ) :
    currentCarrier Q m d →ₗ[K] auxiliaryCarrier Q m d where
  toFun q := ⟨fun t => conductor (K := K) m d * q.1 t,
    (mem_currentCarrier_conductor_iff Q m d q.1).mpr q.property,
    fun t ij haux => collision_vanishes_of_conductor_dvd _ ⟨q.1 t, rfl⟩ ij haux⟩
  map_add' p q := by
    apply Subtype.ext
    funext t
    exact mul_add _ _ _
  map_smul' a q := by
    apply Subtype.ext
    funext t
    change conductor (K := K) m d * (a • q.1 t) =
      a • (conductor (K := K) m d * q.1 t)
    exact mul_smul_comm a _ _

/-- The functional-model factorization is an equality, not only a Hilbert
upper bound: every auxiliary solution is conductor times one current solution. -/
theorem conductorMap_bijective [CharZero K] (Q : ρ → σ × σ → K) (m d : ℕ) :
    Function.Bijective (conductorMap Q m d) := by
  constructor
  · intro p q h
    apply Subtype.ext
    funext t
    apply mul_left_cancel₀ (conductor_ne_zero (K := K) m d)
    exact congrFun (congrArg Subtype.val h) t
  · intro p
    obtain ⟨q, hq⟩ := exists_current_quotient Q m d p
    refine ⟨q, ?_⟩
    apply Subtype.ext
    funext t
    exact (hq t).symm

/-- The universal Deligne auxiliary factorization for arbitrary quadratic
current relations, all particle numbers, and all polynomial degrees at once. -/
def conductorEquiv [CharZero K] (Q : ρ → σ × σ → K) (m d : ℕ) :
    currentCarrier Q m d ≃ₗ[K] auxiliaryCarrier Q m d :=
  LinearEquiv.ofBijective (conductorMap Q m d) (conductorMap_bijective Q m d)

end

end VOA.QuadraticCurrentFunctionalCarrier

section AxiomAudit
#print axioms VOA.QuadraticCurrentFunctionalCarrier.currentEquations_conductor_iff
#print axioms VOA.QuadraticCurrentFunctionalCarrier.mem_currentCarrier_conductor_iff
#print axioms VOA.QuadraticCurrentFunctionalCarrier.conductorEquiv
end AxiomAudit
