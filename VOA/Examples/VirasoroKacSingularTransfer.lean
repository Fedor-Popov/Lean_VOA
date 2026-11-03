/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroKacVacuumTransfer
import VOA.Examples.VirasoroMinimalFusionArithmetic
import VOA.Examples.VirasoroBoundaryRigidity

/-!
# Minimal-model rigidity from ordinary singular existence

Actual nonzero singular states at the positive Kac labels, on nonreal
parameters, suffice for minimal-model graded rigidity. Degree exhaustion,
continuity, removal of the translation factor and the vacuum simple-root
transfer are all supplied internally. The singular-state premise is a hypothesis here; it is
proved in `VirasoroScreening.screening_nonreal_kac_singular` (`VirasoroScreeningKacRoots.lean`),
and the unconditional rigidity theorem is `VirModule.minimal_graded_rigidity`.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule VirSimple Deform
open scoped Classical

/-- Actual nonzero singular states at all relevant nonreal Kac labels imply
the full ordinary determinant identity at every nonzero parameter, including
collisions. This specializes polynomial identities, not nullspace counts. -/
theorem verma_kac_all_of_nonreal_singular (N : ℕ)
    (hs : ∀ z : ℂ, z.im ≠ 0 → ∀ r s : ℕ, 0 < r → 0 < s → r*s ≤ N →
      ∃ v : sortedSpan (vermaBSACharge z) (fusionKacWeight r s z) (r*s),
        v ≠ 0 ∧ vermaMode (vermaBSACharge z) (fusionKacWeight r s z) 1 v = 0 ∧
          vermaMode (vermaBSACharge z) (fusionKacWeight r s z) 2 v = 0)
    (t : ℂ) (ht : t ≠ 0) (k : ℕ) (hk : k ≤ N) :
    (vermaWeightGramPolynomial (vermaBSACharge t) k).det =
      Polynomial.C (∏ w : VermaPartitions k,vermaDiagonalContraction w.val) *
        kacWeightProduct t k := by
  apply vermaWeightDeterminant_kac_extend k _ t ht
  intro z hz
  apply vermaWeightDeterminant_eq_kac_of_singular _ z k hz
  intro i hi
  have hil := (Finset.mem_filter.mp hi).2
  have hw : fusionKacWeight (i.1.val+1:ℕ) (i.2.val+1:ℕ) z =
      fusionKacWeight ((i.1.val:ℂ)+1) ((i.2.val:ℂ)+1) z := by
    simp only [Nat.cast_add,Nat.cast_one]
  let S : ℂ → Prop := fun h => ∃ v : sortedSpan (vermaBSACharge z) h
      ((i.1.val+1)*(i.2.val+1)), v ≠ 0 ∧
      vermaMode (vermaBSACharge z) h 1 v = 0 ∧
      vermaMode (vermaBSACharge z) h 2 v = 0
  exact Eq.mp (congrArg S hw)
    (hs z hz (i.1.val+1) (i.2.val+1) (by omega) (by omega) (hil.trans hk))

/-- For ordered coprime minimal labels, actual nonreal Kac singular states
through the first vacuum level suffice for rigidity. There is no additional
vacuum character, survival, multiplicity or derivative premise. The singular
existence premise is proved in `VirasoroScreening.screening_nonreal_kac_singular`. -/
theorem minimal_rigidity_of_nonreal_kac_singular (p q : ℕ) (hq : 2 ≤ q)
    (hpq : q < p) (hcop : p.Coprime q)
    (hs : ∀ z : ℂ, z.im ≠ 0 → ∀ r s : ℕ, 0 < r → 0 < s →
      r*s ≤ (p-1)*(q-1) →
      ∃ v : sortedSpan (vermaBSACharge z) (fusionKacWeight r s z) (r*s),
        v ≠ 0 ∧ vermaMode (vermaBSACharge z) (fusionKacWeight r s z) 1 v = 0 ∧
          vermaMode (vermaBSACharge z) (fusionKacWeight r s z) 2 v = 0) :
    IsRigidGraded (virasoroSimple (minimalCentralCharge p q)) := by
  have hpos : 0 < (p-1)*(q-1) := Nat.mul_pos (by omega) (by omega)
  have hn : ((p-1)*(q-1)-1)+1 = (p-1)*(q-1) := by omega
  have hh := graded_rigidity_of_verma_kac p q ((p-1)*(q-1)-1) hq hpq hcop hn
    (fun z hz k hk => verma_kac_all_of_nonreal_singular _ hs z hz k (by omega))
  rw [minimal_fusion_charge q p (by omega) (by omega),minimalCharge_swap] at hh
  exact hh

/-- Symmetry removes the ordering convention on coprime minimal labels.
The only premise is actual ordinary singular existence at nonreal parameters
through the first vacuum level (proved: `VirasoroScreening.screening_nonreal_kac_singular`). No vacuum multiplicity or
first-order deformation assertion is assumed. -/
theorem minimal_graded_rigidity_of_kac_singular (p q : ℕ) (hp : 2 ≤ p)
    (hq : 2 ≤ q) (hcop : p.Coprime q)
    (hs : ∀ z : ℂ, z.im ≠ 0 → ∀ r s : ℕ, 0 < r → 0 < s →
      r*s ≤ (p-1)*(q-1) →
      ∃ v : sortedSpan (vermaBSACharge z) (fusionKacWeight r s z) (r*s),
        v ≠ 0 ∧ vermaMode (vermaBSACharge z) (fusionKacWeight r s z) 1 v = 0 ∧
          vermaMode (vermaBSACharge z) (fusionKacWeight r s z) 2 v = 0) :
    IsRigidGraded (virasoroSimple (minimalCentralCharge p q)) := by
  have hne : p ≠ q := by
    intro he
    subst q
    have hh : p = 1 := by simpa using hcop
    omega
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [minimalCharge_swap]
    apply minimal_rigidity_of_nonreal_kac_singular q p hp hlt hcop.symm
    simpa only [Nat.mul_comm] using hs
  · exact minimal_rigidity_of_nonreal_kac_singular p q hq hgt hcop hs

end VOA.InverseDS.VirasoroVerma
