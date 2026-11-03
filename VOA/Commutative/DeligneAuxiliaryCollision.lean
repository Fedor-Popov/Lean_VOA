/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.RootedGordonConductorDivisibility

/-!
# The Deligne auxiliary Casimir collision factor

The first `m` particle labels are currents and the remaining `d` labels are
auxiliary Casimir fields. The conductor has order zero at current-current
collisions, order one at mixed collisions, and order two at auxiliary-auxiliary
collisions. The polynomial is the product of these prime powers.

This file proves its divisibility from the literal collision equations and its
nonvanishing after every current-current specialization. The latter is the
cancellation needed to preserve quadratic current relations after division.
No Lie algebra or representation-theoretic hypothesis is used.
-/

namespace VOA.DeligneAuxiliaryCollision

open VOA.CollisionCommonFactors
open VOA.RootedGordonConductorDivisibility

noncomputable section

variable {K : Type*} [Field K]

/-- Ordered particle labels: currents first, auxiliary fields second. -/
abbrev Particle (m d : ℕ) := Fin (m + d)

/-- An unordered pair represented in increasing order. -/
abbrev Pair (m d : ℕ) := IncreasingPair (Particle m d)

/-- Orient every difference from the later to the earlier label. Mixed factors
are therefore auxiliary minus current, as in the paper's `δ_{m,d}`. -/
def factor {m d : ℕ} (ij : Pair m d) : MvPolynomial (Particle m d) K :=
  collisionFactor ij.1.2 ij.1.1

/-- Only collisions involving the auxiliary field contribute a conductor. -/
def order {m d : ℕ} (ij : Pair m d) : ℕ :=
  if ij.1.2.val < m then 0 else if ij.1.1.val < m then 1 else 2

/-- The universal auxiliary conductor, including the cases `m = 0` or `d = 0`. -/
def conductor (m d : ℕ) : MvPolynomial (Particle m d) K :=
  ∏ ij : Pair m d, factor (K := K) ij ^ order ij

/-- The derivative degree, as a finite sum of the literal collision orders. -/
def conductorDegree (m d : ℕ) : ℕ := ∑ ij : Pair m d, order ij

@[simp]
theorem conductor_no_auxiliary (m : ℕ) : conductor (K := K) m 0 = 1 := by
  simp [conductor, order]

/-- The conductor has exactly the degree prescribed by its collision orders. -/
theorem conductor_isWeightedHomogeneous (m d : ℕ) :
    (conductor (K := K) m d).IsWeightedHomogeneous (fun _ => 1) (conductorDegree m d) := by
  apply MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun ij : Pair m d => factor (K := K) ij ^ order ij) order
  intro ij _
  have hfactor : (factor (K := K) ij).IsWeightedHomogeneous (fun _ => 1) 1 := by
    exact (MvPolynomial.weightedHomogeneousSubmodule K (fun _ => 1) 1).sub_mem
      (MvPolynomial.isWeightedHomogeneous_X K (fun _ => 1) ij.1.2)
      (MvPolynomial.isWeightedHomogeneous_X K (fun _ => 1) ij.1.1)
  simpa using hfactor.pow (order ij)

theorem factor_prime {m d : ℕ} (ij : Pair m d) : Prime (factor (K := K) ij) :=
  collisionFactor_prime ij.1.2 ij.1.1 (ne_of_lt ij.2)

/-- Distinct pair factors are nonassociated prime elements. -/
theorem factor_not_dvd {m d : ℕ} (ij kl : Pair m d) (hne : ij ≠ kl) :
    ¬ factor (K := K) ij ∣ factor (K := K) kl := by
  apply collisionFactor_not_dvd_of_unordered_pairs_ne
    (ne_of_lt ij.2) (ne_of_gt kl.2)
  · rintro ⟨hr, hl⟩
    apply hne
    apply Subtype.ext
    exact Prod.ext hl.symm hr.symm
  · rintro ⟨hr, hl⟩
    have hk := kl.2
    rw [hl, hr] at hk
    exact (not_lt_of_ge ij.2.le) hk

theorem conductor_ne_zero (m d : ℕ) : conductor (K := K) m d ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro ij _
  exact pow_ne_zero _ (factor_prime (K := K) ij).ne_zero

private def pairMap {m d : ℕ} (e : Equiv.Perm (Particle m d))
    (ij : Pair m d) : Pair m d := by
  by_cases h : e ij.1.1 < e ij.1.2
  · exact ⟨(e ij.1.1, e ij.1.2), h⟩
  · exact ⟨(e ij.1.2, e ij.1.1),
      lt_of_le_of_ne (le_of_not_gt h) (fun heq =>
        (ne_of_gt ij.2) (e.injective heq))⟩

private def pairEquiv {m d : ℕ} (e : Equiv.Perm (Particle m d)) :
    Pair m d ≃ Pair m d where
  toFun := pairMap e
  invFun := pairMap e.symm
  left_inv ij := by
    rcases ij with ⟨⟨i, j⟩, hij⟩
    apply Subtype.ext
    by_cases h : e i < e j
    · simp [pairMap, h, hij]
    · have hji : ¬j < i := not_lt_of_ge hij.le
      simp [pairMap, h, hji]
  right_inv ij := by
    rcases ij with ⟨⟨i, j⟩, hij⟩
    apply Subtype.ext
    by_cases h : e.symm i < e.symm j
    · simp [pairMap, h, hij]
    · have hji : ¬j < i := not_lt_of_ge hij.le
      simp [pairMap, h, hji]

private theorem rename_factor_pow {m d : ℕ} (e : Equiv.Perm (Particle m d))
    (he : ∀ i, (e i).val < m ↔ i.val < m) (ij : Pair m d) :
    MvPolynomial.rename e (factor (K := K) ij ^ order ij) =
      factor (K := K) (pairEquiv e ij) ^ order (pairEquiv e ij) := by
  have hleft := he ij.1.1
  have hright := he ij.1.2
  have hij : ij.1.1.val < ij.1.2.val := ij.2
  by_cases hr : ij.1.2.val < m
  · have hl : ij.1.1.val < m := by omega
    have hel := hleft.mpr hl
    have her := hright.mpr hr
    by_cases h : e ij.1.1 < e ij.1.2 <;>
      simp [order, hr, factor, pairEquiv, pairMap, h, hel, her]
  · by_cases hl : ij.1.1.val < m
    · have hel := hleft.mpr hl
      have her : ¬(e ij.1.2).val < m := by omega
      have h : e ij.1.1 < e ij.1.2 := by exact_mod_cast (by omega :
        (e ij.1.1).val < (e ij.1.2).val)
      simp [order, hr, hl, factor, pairEquiv, pairMap, h, hel, her, collisionFactor]
    · have hel : ¬(e ij.1.1).val < m := by omega
      have her : ¬(e ij.1.2).val < m := by omega
      by_cases h : e ij.1.1 < e ij.1.2
      · simp [order, hr, hl, factor, pairEquiv, pairMap, h, hel, her, collisionFactor]
      · simp only [order, hr, hl, ↓reduceIte, factor, collisionFactor, map_pow,
          map_sub, MvPolynomial.rename_X, pairEquiv, Equiv.coe_fn_mk, pairMap, h,
          dite_false, hel, her]
        ring

/-- The conductor is invariant under arbitrary permutations that preserve
the current and auxiliary populations, with no restriction on tensor colors. -/
theorem conductor_rename_invariant (m d : ℕ) (e : Equiv.Perm (Particle m d))
    (he : ∀ i, (e i).val < m ↔ i.val < m) :
    MvPolynomial.rename e (conductor (K := K) m d) = conductor (K := K) m d := by
  rw [conductor, map_prod]
  simp_rw [rename_factor_pow e he]
  exact (pairEquiv e).prod_comp (fun ij => factor (K := K) ij ^ order ij)

/-- Literal relations and auxiliary exchange symmetry force the entire
conductor. No current-current vanishing is requested. -/
theorem conductor_dvd_of_collisions [CharZero K] (m d : ℕ)
    (p : MvPolynomial (Particle m d) K)
    (hvanish : ∀ ij : Pair m d, m ≤ ij.1.2.val →
      collisionMap ij.1.2 ij.1.1 (ne_of_lt ij.2) p = 0)
    (hsymm : ∀ ij : Pair m d, m ≤ ij.1.1.val →
      swapVariables ij.1.2 ij.1.1 p = p) :
    conductor (K := K) m d ∣ p := by
  apply prod_pow_dvd_of_pairwise_prime_varying Finset.univ
    (factor (K := K)) order p
  · intro ij _
    exact factor_prime ij
  · intro ij _ kl _ hne
    exact factor_not_dvd ij kl hne
  · intro ij _
    by_cases hr : ij.1.2.val < m
    · simp [order, hr]
    · by_cases hl : ij.1.1.val < m
      · simp only [order, hr, hl, ↓reduceIte, pow_one, factor]
        exact (collisionFactor_dvd_iff _ _ _ _).mpr
          (hvanish ij (Nat.le_of_not_lt hr))
      · simp only [order, hr, hl, ↓reduceIte, factor]
        exact collisionFactor_sq_dvd_of_swap_invariant _ _ _ p
          (hsymm ij (Nat.le_of_not_lt hl)) (hvanish ij (Nat.le_of_not_lt hr))

/-- Every relevant pair condition follows from divisibility by the conductor. -/
theorem collision_vanishes_of_conductor_dvd {m d : ℕ}
    (p : MvPolynomial (Particle m d) K) (hp : conductor (K := K) m d ∣ p)
    (ij : Pair m d) (haux : m ≤ ij.1.2.val) :
    collisionMap ij.1.2 ij.1.1 (ne_of_lt ij.2) p = 0 := by
  apply (collisionFactor_dvd_iff _ _ _ _).mp
  have hpos : 0 < order ij := by
    simp only [order, show ¬ij.1.2.val < m by omega, ↓reduceIte]
    split <;> omega
  have hdvd : factor (K := K) ij ∣ factor (K := K) ij ^ order ij :=
    dvd_pow_self _ (Nat.ne_of_gt hpos)
  exact hdvd.trans ((Finset.dvd_prod_of_mem (fun kl : Pair m d =>
    factor (K := K) kl ^ order kl) (Finset.mem_univ ij)).trans hp)

/-- The conductor stays nonzero when any two current roots coincide. This is
what distinguishes it from a discriminant involving all particles. -/
theorem conductor_currentDiagonal_ne_zero (m d : ℕ)
    (a b : Particle m d) (hba : b ≠ a) (ha : a.val < m) (hb : b.val < m) :
    collisionMap (K := K) a b hba (conductor (K := K) m d) ≠ 0 := by
  rw [conductor, map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro ij _
  rw [map_pow]
  by_cases hr : ij.1.2.val < m
  · simp [order, hr]
  · apply pow_ne_zero
    intro hz
    have hdvd := (collisionFactor_dvd_iff a b hba (factor (K := K) ij)).mpr hz
    apply collisionFactor_not_dvd_of_unordered_pairs_ne hba (ne_of_gt ij.2) ?_ ?_ hdvd
    · rintro ⟨heq, _⟩
      exact hr (heq ▸ ha)
    · rintro ⟨heq, _⟩
      exact hr (heq ▸ hb)

/-- Any quadratic relation readback on a current diagonal can cancel the
specialized auxiliary conductor. The readback is allowed to be tensor-valued
by applying this statement to each component. -/
theorem cancel_currentDiagonal_conductor (m d : ℕ)
    (a b : Particle m d) (hba : b ≠ a) (ha : a.val < m) (hb : b.val < m)
    (q : MvPolynomial {x : Particle m d // x ≠ a} K) :
    collisionMap (K := K) a b hba (conductor (K := K) m d) * q = 0 ↔ q = 0 :=
  mul_eq_zero_iff_left (conductor_currentDiagonal_ne_zero m d a b hba ha hb)

section TensorComponents

variable {T : Type*} [Fintype T]

/-- A tensor projection, written in a basis, followed by a current collision.
Arbitrary coefficients allow all quadratic relation projections and spectators. -/
def projectedDiagonal {m d : ℕ} (a b : Particle m d) (hba : b ≠ a)
    (c : T → K) (p : T → MvPolynomial (Particle m d) K) :
    MvPolynomial {x : Particle m d // x ≠ a} K :=
  ∑ t, MvPolynomial.C (c t) * collisionMap a b hba (p t)

/-- A scalar polynomial factors out of every tensor projection after collision. -/
theorem projectedDiagonal_mul {m d : ℕ} (a b : Particle m d) (hba : b ≠ a)
    (c : T → K) (f : MvPolynomial (Particle m d) K)
    (p : T → MvPolynomial (Particle m d) K) :
    projectedDiagonal a b hba c (fun t => f * p t) =
      collisionMap a b hba f * projectedDiagonal a b hba c p := by
  simp only [projectedDiagonal, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Division by the auxiliary conductor preserves every quadratic current
relation, including linear combinations of tensor components. -/
theorem projectedDiagonal_conductor_eq_zero_iff (m d : ℕ)
    (a b : Particle m d) (hba : b ≠ a) (ha : a.val < m) (hb : b.val < m)
    (c : T → K) (p : T → MvPolynomial (Particle m d) K) :
    projectedDiagonal a b hba c (fun t => conductor (K := K) m d * p t) = 0 ↔
      projectedDiagonal a b hba c p = 0 := by
  rw [projectedDiagonal_mul]
  exact cancel_currentDiagonal_conductor m d a b hba ha hb _

end TensorComponents

end

end VOA.DeligneAuxiliaryCollision

section AxiomAudit
#print axioms VOA.DeligneAuxiliaryCollision.conductor_dvd_of_collisions
#print axioms VOA.DeligneAuxiliaryCollision.conductor_currentDiagonal_ne_zero
#print axioms VOA.DeligneAuxiliaryCollision.conductor_rename_invariant
#print axioms VOA.DeligneAuxiliaryCollision.cancel_currentDiagonal_conductor
end AxiomAudit
