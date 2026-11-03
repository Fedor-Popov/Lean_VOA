/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSPiExponential

/-!
# The transverse-current gate for the inverse-DS Pi field

The full transverse current consists of the `xi` oscillator modes together with the charge
momentum `xiZeroMode`.  This file proves the zero-mode part of its OPE with the null exponential
exactly and reduces every nonzero mode to the explicit oscillator-dressing identity
`XiDressContraction`.  The attempted direction-free Newton proof is retained below as commented
development, because elaboration of its endomorphism reassembly has not yet passed `lake build`.

Even after this gate is discharged, the existing reconstruction theorem cannot yet be invoked:
one still needs a translation operator covariant on both currents and the exponential, a mutually
local generating family with a proved spanning statement, and then a compatible conformal vector
and grading.  Thus current/exponential locality alone is not sufficient to claim a vertex algebra.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDSPi

open scoped TensorProduct
open Module (End)
open scoped BigOperators

noncomputable section

/-- The transverse oscillator zero mode vanishes on the polynomial Fock factor. -/
@[simp] theorem xiOsc_zero : xiOsc 0 = (0 : End ℂ HyperFock) := by
  rw [xiOsc, directionOsc]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [HeisenbergN.oscN_zero, smul_zero]

/-! ## A direction-free Newton contraction

The following small abstraction is the missing bridge from the positive-lattice proof.  It only
uses the Heisenberg cross commutator; no real coordinates or positivity enter. -/

section Newton

variable {B : Type*} [AddCommGroup B] [Module ℂ B]

/-- Newton coefficients attached to an arbitrary family of creation/annihilation operators. -/
noncomputable def newtonCoeff (A : ℕ → End ℂ B) : ℕ → End ℂ B
  | 0 => LinearMap.id
  | N + 1 => ((N + 1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N + 1),
      (A m).comp (newtonCoeff A (N - m))

noncomputable def newtonCoeffZ (A : ℕ → End ℂ B) (N : ℤ) : End ℂ B :=
  if 0 ≤ N then newtonCoeff A N.toNat else 0

@[simp] theorem newtonCoeff_zero (A : ℕ → End ℂ B) :
    newtonCoeff A 0 = LinearMap.id := by simp [newtonCoeff]

theorem newtonCoeff_succ (A : ℕ → End ℂ B) (N : ℕ) :
    newtonCoeff A (N + 1) = ((N + 1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N + 1),
      (A m).comp (newtonCoeff A (N - m)) := by simp [newtonCoeff]

theorem newtonCoeffZ_neg (A : ℕ → End ℂ B) {N : ℤ} (hN : N < 0) :
    newtonCoeffZ A N = 0 := by rw [newtonCoeffZ, if_neg (by omega)]

theorem newtonCoeffZ_nonneg (A : ℕ → End ℂ B) {N : ℤ} (hN : 0 ≤ N) :
    newtonCoeffZ A N = newtonCoeff A N.toNat := by rw [newtonCoeffZ, if_pos hN]

@[simp] theorem newtonCoeffZ_zero (A : ℕ → End ℂ B) :
    newtonCoeffZ A 0 = LinearMap.id := by rw [newtonCoeffZ_nonneg A le_rfl]; simp

theorem newtonCoeffZ_recursion (A : ℕ → End ℂ B) (N : ℤ) (hN : 1 ≤ N) :
    newtonCoeffZ A N = (N : ℂ)⁻¹ • ∑ m ∈ Finset.range N.toNat,
      (A m).comp (newtonCoeffZ A (N - 1 - m)) := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, N.toNat = K + 1 := ⟨N.toNat - 1, by omega⟩
  have hNK : N = (K : ℤ) + 1 := by omega
  rw [newtonCoeffZ_nonneg A (by omega), hK, newtonCoeff_succ, hNK]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_range] at hm
  congr 2
  rw [newtonCoeffZ_nonneg A (by omega)]
  congr 1
  omega

theorem newtonCoeffZ_sum_reassembly (A : ℕ → End ℂ B) (M : ℤ) (K : ℕ)
    (hK : M.toNat ≤ K) :
    ∑ m ∈ Finset.range K, (A m).comp (newtonCoeffZ A (M - 1 - m))
      = (M : ℂ) • newtonCoeffZ A M := by
  by_cases hM : 1 ≤ M
  · have hsplit : ∑ m ∈ Finset.range K, (A m).comp (newtonCoeffZ A (M - 1 - m))
        = ∑ m ∈ Finset.range M.toNat, (A m).comp (newtonCoeffZ A (M - 1 - m)) := by
      refine (Finset.sum_subset (s₁ := Finset.range M.toNat) (s₂ := Finset.range K)
        (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_).symm
      intro m _ hm
      simp only [Finset.mem_range, not_lt] at hm
      rw [newtonCoeffZ_neg A (by omega), LinearMap.comp_zero]
    rw [hsplit, newtonCoeffZ_recursion A M hM, smul_smul, mul_inv_cancel₀ (by
      simp only [ne_eq]; exact_mod_cast (by omega : M ≠ 0)), one_smul]
  · have hsum0 : ∑ m ∈ Finset.range K,
        (A m).comp (newtonCoeffZ A (M - 1 - m)) = 0 := by
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [newtonCoeffZ_neg A (by omega), LinearMap.comp_zero]
    rw [hsum0]
    rcases lt_or_eq_of_le (by omega : M ≤ 0) with hlt | heq
    · rw [newtonCoeffZ_neg A hlt, smul_zero]
    · rw [heq]; simp

/-- Abstract Newton contraction.  The residue is normalized to one. -/
theorem comp_newtonCoeffZ (X : End ℂ B) (A : ℕ → End ℂ B)
    (k : ℕ) (hk : 1 ≤ k)
    (hmove : ∀ m : ℕ, X.comp (A m) = (A m).comp X
      + (if (m : ℤ) + 1 = (k : ℤ) then (k : ℂ) else 0) • LinearMap.id) :
    ∀ M : ℤ, X.comp (newtonCoeffZ A M)
      = (newtonCoeffZ A M).comp X + newtonCoeffZ A (M - k) := by
  suffices H : ∀ n : ℕ, ∀ M : ℤ, M.toNat ≤ n →
      X.comp (newtonCoeffZ A M)
        = (newtonCoeffZ A M).comp X + newtonCoeffZ A (M - k) by
    exact fun M => H M.toNat M le_rfl
  intro n
  induction n with
  | zero =>
    intro M hM
    by_cases h0 : M = 0
    · subst h0
      rw [newtonCoeffZ_zero, LinearMap.comp_id, LinearMap.id_comp,
        newtonCoeffZ_neg A (show (0 : ℤ) - k < 0 by omega), add_zero]
    · rw [newtonCoeffZ_neg A (by omega : M < 0),
        newtonCoeffZ_neg A (show M - k < 0 by omega),
        LinearMap.comp_zero, LinearMap.zero_comp, add_zero]
  | succ n ih =>
    intro M hM
    by_cases hsmall : M.toNat ≤ n
    · exact ih M hsmall
    · have hM1 : 1 ≤ M := by omega
      have hMne : (M : ℂ) ≠ 0 := by simp only [ne_eq, Int.cast_eq_zero]; omega
      conv_lhs => rw [newtonCoeffZ_recursion A M hM1]
      rw [LinearMap.comp_smul]
      change (M : ℂ)⁻¹ • X.comp (∑ m ∈ Finset.range M.toNat,
        (A m).comp (newtonCoeffZ A (M - 1 - m))) = _
      have hcomp : X.comp (∑ m ∈ Finset.range M.toNat,
          (A m).comp (newtonCoeffZ A (M - 1 - m))) =
          ∑ m ∈ Finset.range M.toNat,
            X.comp ((A m).comp (newtonCoeffZ A (M - 1 - m))) := by
        ext p
        simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
      rw [hcomp]
      have hterm : ∀ m ∈ Finset.range M.toNat,
          X.comp ((A m).comp (newtonCoeffZ A (M - 1 - m)))
            = (A m).comp ((newtonCoeffZ A (M - 1 - m)).comp X)
              + (A m).comp (newtonCoeffZ A ((M - k) - 1 - m))
              + (if (m : ℤ) + 1 = (k : ℤ) then (k : ℂ) else 0)
                • newtonCoeffZ A (M - 1 - m) := by
        intro m _
        rw [← LinearMap.comp_assoc, hmove m, LinearMap.add_comp, LinearMap.comp_assoc,
          ih (M - 1 - m) (by omega)]
        simp only [LinearMap.comp_add, LinearMap.comp_smul, LinearMap.smul_comp,
          LinearMap.id_comp]
        rw [show M - 1 - (m : ℤ) - k = (M - k) - 1 - m from by ring]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hcol1 : (∑ m ∈ Finset.range M.toNat,
            (A m).comp ((newtonCoeffZ A (M - 1 - m)).comp X))
          = (M : ℂ) • ((newtonCoeffZ A M).comp X) := by
        ext p
        have hr := DFunLike.congr_fun
          (newtonCoeffZ_sum_reassembly A M M.toNat le_rfl) (X p)
        simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.smul_apply] using hr
      have hcol2 : (∑ m ∈ Finset.range M.toNat,
            (A m).comp (newtonCoeffZ A ((M - k) - 1 - m)))
          = ((M - k : ℤ) : ℂ) • newtonCoeffZ A (M - k) := by
        rw [newtonCoeffZ_sum_reassembly A (M - k) M.toNat (by omega)]
      have hcol3 : (∑ m ∈ Finset.range M.toNat,
            (if (m : ℤ) + 1 = (k : ℤ) then (k : ℂ) else 0)
              • newtonCoeffZ A (M - 1 - m))
          = (k : ℂ) • newtonCoeffZ A (M - k) := by
        by_cases hkM : k ≤ M.toNat
        · rw [Finset.sum_eq_single (k - 1)]
          · rw [if_pos (by omega), show M - 1 - ((k : ℕ) - 1 : ℕ) = M - k from by
                rw [show ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 from by omega]; ring]
          · intro b _ hb; rw [if_neg (by omega), zero_smul]
          · intro hmem; exact absurd (Finset.mem_range.mpr (by omega)) hmem
        · rw [newtonCoeffZ_neg A (show M - k < 0 by omega), smul_zero]
          refine Finset.sum_eq_zero fun m hm => ?_
          simp only [Finset.mem_range] at hm
          rw [if_neg (by omega), zero_smul]
      rw [hcol1, hcol2, hcol3, inv_smul_eq_iff₀ hMne]
      push_cast
      module

end Newton

def etaCreationAtom (m : ℕ) : End ℂ HyperFock := etaOsc (-((m : ℤ) + 1))
def etaAnnihilationAtom (m : ℕ) : End ℂ HyperFock := -(etaOsc ((m : ℤ) + 1))

theorem etaCreationCoeff_eq_newton (N : ℕ) :
    etaCreationCoeff N = newtonCoeff etaCreationAtom N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 => simp [etaCreationCoeff, newtonCoeff]
      | M + 1 =>
          rw [etaCreationCoeff_succ, newtonCoeff_succ]
          apply congrArg (((M + 1 : ℂ))⁻¹ • ·)
          apply Finset.sum_congr rfl
          intro m hm
          exact congrArg (etaCreationAtom m).comp
            (ih (M - m) (by simp only [Finset.mem_range] at hm; omega))

theorem etaAnnihilationCoeff_eq_newton (N : ℕ) :
    etaAnnihilationCoeff N = newtonCoeff etaAnnihilationAtom N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 => simp [etaAnnihilationCoeff, newtonCoeff]
      | M + 1 =>
          rw [etaAnnihilationCoeff_succ, newtonCoeff_succ]
          apply congrArg (((M + 1 : ℂ))⁻¹ • ·)
          apply Finset.sum_congr rfl
          intro m hm
          exact congrArg (etaAnnihilationAtom m).comp
            (ih (M - m) (by simp only [Finset.mem_range] at hm; omega))

theorem xi_pos_creationAtom_move (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    (xiOsc (k : ℤ)).comp (etaCreationAtom m)
      = (etaCreationAtom m).comp (xiOsc (k : ℤ))
        + (if (m : ℤ) + 1 = (k : ℤ) then (k : ℂ) else 0) • LinearMap.id := by
  have h := etaOsc_xiOsc_comm (-((m : ℤ) + 1)) (k : ℤ)
  change (etaOsc (-((m : ℤ) + 1))).comp (xiOsc k)
      - (xiOsc k).comp (etaOsc (-((m : ℤ) + 1))) = _ at h
  simp only [etaCreationAtom]
  by_cases hc : (m : ℤ) + 1 = (k : ℤ)
  · rw [if_pos hc]
    rw [if_pos (by omega : -((m : ℤ) + 1) + k = 0)] at h
    push_cast at h
    have hcast : (m : ℂ) + 1 = (k : ℂ) := by exact_mod_cast hc
    rw [← hcast]
    have heq := sub_eq_iff_eq_add.mp h
    rw [heq]
    have hneg : (-((m : ℂ) + 1)) • (LinearMap.id : End ℂ HyperFock)
        = -(((m : ℂ) + 1) • (LinearMap.id : End ℂ HyperFock)) := by
      exact neg_smul ((m : ℂ) + 1) (LinearMap.id : End ℂ HyperFock)
    rw [hneg]
    abel
  · rw [if_neg hc]
    rw [if_neg (by omega : ¬ (-((m : ℤ) + 1) + k = 0))] at h
    simp only [zero_smul, add_zero] at h ⊢
    exact (sub_eq_zero.mp h).symm

theorem xi_neg_annihilationAtom_move (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    (xiOsc (-(k : ℤ))).comp (etaAnnihilationAtom m)
      = (etaAnnihilationAtom m).comp (xiOsc (-(k : ℤ)))
        + (if (m : ℤ) + 1 = (k : ℤ) then (k : ℂ) else 0) • LinearMap.id := by
  have h := etaOsc_xiOsc_comm ((m : ℤ) + 1) (-(k : ℤ))
  change (etaOsc ((m : ℤ) + 1)).comp (xiOsc (-k))
      - (xiOsc (-k)).comp (etaOsc ((m : ℤ) + 1)) = _ at h
  simp only [etaAnnihilationAtom, LinearMap.comp_neg, LinearMap.neg_comp]
  by_cases hc : (m : ℤ) + 1 = (k : ℤ)
  · rw [if_pos hc]
    rw [if_pos (by omega : (m : ℤ) + 1 + -k = 0)] at h
    push_cast at h
    have hcast : (m : ℂ) + 1 = (k : ℂ) := by exact_mod_cast hc
    rw [← hcast]
    have heq := sub_eq_iff_eq_add.mp h
    rw [heq]
    abel
  · rw [if_neg hc]
    rw [if_neg (by omega : ¬ ((m : ℤ) + 1 + -k = 0))] at h
    simp only [zero_smul, add_zero] at h ⊢
    have he := (sub_eq_zero.mp h).symm
    simpa only [neg_inj] using congrArg Neg.neg he

theorem xi_pos_comp_etaCreationCoeffZ (k : ℕ) (hk : 1 ≤ k) (M : ℤ) :
    (xiOsc (k : ℤ)).comp (newtonCoeffZ etaCreationAtom M)
      = (newtonCoeffZ etaCreationAtom M).comp (xiOsc (k : ℤ))
        + newtonCoeffZ etaCreationAtom (M - k) :=
  comp_newtonCoeffZ _ _ k hk (xi_pos_creationAtom_move k hk) M

theorem xi_neg_comp_etaAnnihilationCoeffZ (k : ℕ) (hk : 1 ≤ k) (M : ℤ) :
    (xiOsc (-(k : ℤ))).comp (newtonCoeffZ etaAnnihilationAtom M)
      = (newtonCoeffZ etaAnnihilationAtom M).comp (xiOsc (-(k : ℤ)))
        + newtonCoeffZ etaAnnihilationAtom (M - k) :=
  comp_newtonCoeffZ _ _ k hk (xi_neg_annihilationAtom_move k hk) M

theorem newtonCoeffZ_creation_eq_etaEminus (t : ℤ) :
    newtonCoeffZ etaCreationAtom t = etaEminus t := by
  by_cases ht : 0 ≤ t
  · rw [newtonCoeffZ_nonneg _ ht, etaEminus_nonneg ht, etaCreationCoeff_eq_newton]
  · rw [newtonCoeffZ_neg _ (by omega), etaEminus_neg (by omega)]

theorem newtonCoeffZ_annihilation_eq_etaEplus (t : ℤ) :
    newtonCoeffZ etaAnnihilationAtom (-t) = etaEplus t := by
  by_cases ht : t ≤ 0
  · rw [newtonCoeffZ_nonneg _ (by omega), etaEplus_nonpos ht,
      etaAnnihilationCoeff_eq_newton]
  · rw [newtonCoeffZ_neg _ (by omega), etaEplus_pos (by omega)]

theorem xi_pos_comp_etaEminus (k : ℕ) (hk : 1 ≤ k) (t : ℤ) :
    (xiOsc (k : ℤ)).comp (etaEminus t)
      = (etaEminus t).comp (xiOsc (k : ℤ)) + etaEminus (t - k) := by
  rw [← newtonCoeffZ_creation_eq_etaEminus t,
    ← newtonCoeffZ_creation_eq_etaEminus (t - k), xi_pos_comp_etaCreationCoeffZ k hk]

theorem xi_neg_comp_etaEplus (k : ℕ) (hk : 1 ≤ k) (t : ℤ) :
    (xiOsc (-(k : ℤ))).comp (etaEplus t)
      = (etaEplus t).comp (xiOsc (-(k : ℤ))) + etaEplus (t + k) := by
  rw [← newtonCoeffZ_annihilation_eq_etaEplus t,
    ← newtonCoeffZ_annihilation_eq_etaEplus (t + k),
    xi_neg_comp_etaAnnihilationCoeffZ k hk]
  congr 1
  ring

theorem commute_newtonCoeff (X : End ℂ HyperFock) (A : ℕ → End ℂ HyperFock)
    (hA : ∀ m, Commute X (A m)) (N : ℕ) : Commute X (newtonCoeff A N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 => rw [newtonCoeff_zero]; exact Commute.one_right _
      | M + 1 =>
          rw [newtonCoeff_succ]
          refine Commute.smul_right ?_ _
          refine Commute.sum_right _ _ _ (fun m hm => ?_)
          refine Commute.mul_right (hA m) (ih (M - m) ?_)
          simp only [Finset.mem_range] at hm
          omega

theorem xi_neg_commute_creationAtom (k m : ℕ) (hk : 1 ≤ k) :
    Commute (xiOsc (-(k : ℤ))) (etaCreationAtom m) := by
  have h := etaOsc_xiOsc_comm (-((m : ℤ) + 1)) (-(k : ℤ))
  rw [if_neg (by omega : ¬ (-((m : ℤ) + 1) + -k = 0)), zero_smul] at h
  exact (sub_eq_zero.mp h).symm

theorem xi_pos_commute_annihilationAtom (k m : ℕ) (hk : 1 ≤ k) :
    Commute (xiOsc (k : ℤ)) (etaAnnihilationAtom m) := by
  have h := etaOsc_xiOsc_comm ((m : ℤ) + 1) (k : ℤ)
  rw [if_neg (by omega : ¬ ((m : ℤ) + 1 + k = 0)), zero_smul] at h
  have heq := (sub_eq_zero.mp h).symm
  have hc : Commute (xiOsc (k : ℤ)) (etaOsc ((m : ℤ) + 1)) := heq
  exact hc.neg_right

theorem xi_nonpos_comm_etaEminus (r t : ℤ) (hr : r ≤ 0) :
    (xiOsc r).comp (etaEminus t) = (etaEminus t).comp (xiOsc r) := by
  rcases lt_or_eq_of_le hr with hrneg | rfl
  · have hk : 1 ≤ (-r).toNat := by omega
    have hrw : r = -(((-r).toNat : ℕ) : ℤ) := by omega
    by_cases ht : 0 ≤ t
    · rw [etaEminus_nonneg ht, etaCreationCoeff_eq_newton, hrw]
      exact (commute_newtonCoeff _ _ (fun m => xi_neg_commute_creationAtom _ m hk) _).eq
    · rw [etaEminus_neg (by omega)]; simp
  · rw [xiOsc_zero]; simp

theorem xi_nonneg_comm_etaEplus (r t : ℤ) (hr : 0 ≤ r) :
    (xiOsc r).comp (etaEplus t) = (etaEplus t).comp (xiOsc r) := by
  rcases lt_or_eq_of_le hr with hrpos | rfl
  · have hk : 1 ≤ r.toNat := by omega
    have hrw : r = (r.toNat : ℤ) := by omega
    by_cases ht : t ≤ 0
    · rw [etaEplus_nonpos ht, etaAnnihilationCoeff_eq_newton, hrw]
      exact (commute_newtonCoeff _ _ (fun m => xi_pos_commute_annihilationAtom _ m hk) _).eq
    · rw [etaEplus_pos (by omega)]; simp
  · rw [xiOsc_zero]; simp

theorem xiMode_comm_etaEminus (j t : ℤ) :
    (xiOsc (-j - 1)).comp (etaEminus t) - (etaEminus t).comp (xiOsc (-j - 1))
      = if j ≤ -2 then etaEminus (t + j + 1) else 0 := by
  by_cases hj : j ≤ -2
  · rw [if_pos hj]
    have hk : 1 ≤ (-j - 1).toNat := by omega
    have hrw : -j - 1 = ((-j - 1).toNat : ℤ) := by omega
    rw [hrw, xi_pos_comp_etaEminus _ hk]
    rw [show t - ((-j - 1).toNat : ℤ) = t + j + 1 by omega]
    abel
  · rw [if_neg hj, xi_nonpos_comm_etaEminus (-j - 1) t (by omega), sub_self]

theorem xiMode_comm_etaEplus (j t : ℤ) :
    (xiOsc (-j - 1)).comp (etaEplus t) - (etaEplus t).comp (xiOsc (-j - 1))
      = if 0 ≤ j then etaEplus (t + j + 1) else 0 := by
  by_cases hj : 0 ≤ j
  · rw [if_pos hj]
    have hk : 1 ≤ (j + 1).toNat := by omega
    have hrw : -j - 1 = -(((j + 1).toNat : ℕ) : ℤ) := by omega
    rw [hrw, xi_neg_comp_etaEplus _ hk]
    rw [show t + ((j + 1).toNat : ℤ) = t + j + 1 by omega]
    abel
  · rw [if_neg hj, xi_nonneg_comm_etaEplus (-j - 1) t (by omega), sub_self]

theorem oscillator_leibniz (f g h : End ℂ HyperFock) (x : HyperFock) :
    f (g (h x)) - g (h (f x)) = (f * g - g * f) (h x) + g ((f * h - h * f) x) := by
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub]
  abel

/-- The complete oscillator contraction with the normal-ordered null dressing. -/
theorem xiOsc_etaDress_comm (j t : ℤ) (p : HyperFock) :
    xiOsc (-j - 1) (etaDress t p) - etaDress t (xiOsc (-j - 1) p)
      = if j = -1 then 0 else etaDress (t + j + 1) p := by
  have hsupp1 : (Function.support (fun m : ℤ =>
      xiOsc (-j - 1) (etaEminus m (etaEplus (t - m) p)))).Finite := by
    apply Set.Finite.subset (etaDress_marg_support_finite t p)
    intro m hm
    rw [Function.mem_support] at hm ⊢
    intro h
    exact hm (by rw [h, map_zero])
  have hsupp2 : (Function.support (fun m : ℤ =>
      etaEminus m (etaEplus (t - m) (xiOsc (-j - 1) p)))).Finite :=
    etaDress_marg_support_finite t (xiOsc (-j - 1) p)
  rw [etaDress_apply_conv t (xiOsc (-j - 1) p), etaDress_apply_conv t p,
    map_finsum (xiOsc (-j - 1)) (etaDress_marg_support_finite t p),
    ← finsum_sub_distrib hsupp1 hsupp2,
    show (∑ᶠ m : ℤ, (xiOsc (-j - 1) (etaEminus m (etaEplus (t - m) p))
          - etaEminus m (etaEplus (t - m) (xiOsc (-j - 1) p))))
        = ∑ᶠ m : ℤ, (
            ((xiOsc (-j - 1)).comp (etaEminus m) - (etaEminus m).comp (xiOsc (-j - 1)))
                (etaEplus (t - m) p)
          + etaEminus m
              (((xiOsc (-j - 1)).comp (etaEplus (t - m))
                - (etaEplus (t - m)).comp (xiOsc (-j - 1))) p)) from
      finsum_congr fun m => by
        exact oscillator_leibniz (xiOsc (-j - 1)) (etaEminus m) (etaEplus (t - m)) p]
  rcases (show j ≤ -2 ∨ j = -1 ∨ 0 ≤ j from by omega) with hj | hj | hj
  · rw [if_neg (by omega : j ≠ -1),
      show (∑ᶠ m : ℤ, (
            ((xiOsc (-j - 1)).comp (etaEminus m) - (etaEminus m).comp (xiOsc (-j - 1)))
                (etaEplus (t - m) p)
          + etaEminus m (((xiOsc (-j - 1)).comp (etaEplus (t - m))
                - (etaEplus (t - m)).comp (xiOsc (-j - 1))) p)))
          = ∑ᶠ m : ℤ, etaEminus (m + j + 1) (etaEplus (t - m) p) from
        finsum_congr fun m => by
          rw [xiMode_comm_etaEminus, xiMode_comm_etaEplus, if_pos hj,
            if_neg (by omega : ¬ 0 ≤ j), LinearMap.zero_apply, map_zero, add_zero],
      etaDress_apply_conv (t + j + 1) p,
      ← finsum_comp_equiv (Equiv.addRight (j + 1))
        (f := fun m : ℤ => etaEminus m (etaEplus (t + j + 1 - m) p))]
    refine finsum_congr fun m => ?_
    simp only [Equiv.coe_addRight]
    rw [show m + (j + 1) = m + j + 1 from by ring,
      show t + j + 1 - (m + j + 1) = t - m from by ring]
  · subst hj
    rw [if_pos rfl]
    refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
    rw [xiMode_comm_etaEminus, xiMode_comm_etaEplus,
      if_neg (by omega : ¬ (-1 : ℤ) ≤ -2), if_neg (by omega : ¬ (0 : ℤ) ≤ -1)]
    simp
  · rw [if_neg (by omega : j ≠ -1),
      show (∑ᶠ m : ℤ, (
            ((xiOsc (-j - 1)).comp (etaEminus m) - (etaEminus m).comp (xiOsc (-j - 1)))
                (etaEplus (t - m) p)
          + etaEminus m (((xiOsc (-j - 1)).comp (etaEplus (t - m))
                - (etaEplus (t - m)).comp (xiOsc (-j - 1))) p)))
          = ∑ᶠ m : ℤ, etaEminus m (etaEplus (t + j + 1 - m) p) from
        finsum_congr fun m => by
          rw [xiMode_comm_etaEminus, xiMode_comm_etaEplus,
            if_neg (by omega : ¬ j ≤ -2), if_pos hj, LinearMap.zero_apply, zero_add,
            show t - m + j + 1 = t + j + 1 - m from by ring],
      etaDress_apply_conv]

/-- The transverse current: oscillator modes plus charge momentum at current index `-1`. -/
noncomputable def xiCurrentField : FormalDist (End ℂ PiFockCarrier) :=
  fun j => liftHyperOsc (xiOsc (-j - 1)) + (if j = -1 then xiZeroMode else 0)

/-- Action of the transverse current on a pure oscillator/charge state. -/
theorem xiCurrentField_piFockState (j q : ℤ) (p : HyperFock) :
    xiCurrentField j (piFockState p q)
      = piFockState (xiOsc (-j - 1) p) q
        + (if j = -1 then (q : ℂ) • piFockState p q else 0) := by
  rw [xiCurrentField, LinearMap.add_apply, liftHyperOsc_piFockState]
  congr 1
  by_cases hj : j = -1
  · rw [if_pos hj, if_pos hj, xiZeroMode_piFockState]
  · rw [if_neg hj, if_neg hj, LinearMap.zero_apply]

/-- At the exceptional current index, the polynomial oscillator contribution vanishes. -/
theorem xiCurrentField_neg_one_piFockState (q : ℤ) (p : HyperFock) :
    xiCurrentField (-1) (piFockState p q) = (q : ℂ) • piFockState p q := by
  rw [xiCurrentField_piFockState, if_pos rfl]
  norm_num
  rw [piFockState, TensorProduct.zero_tmul]

/-- The zero-mode contribution supplies exactly one unit of charge in the transverse OPE. -/
theorem xiCurrentField_neg_one_comm_exponential_piFockState (t q : ℤ) (p : HyperFock) :
    bracketDist xiCurrentField etaExponentialField (-1) t (piFockState p q)
      = etaExponentialField t (piFockState p q) := by
  rw [bracketDist_apply, LinearMap.sub_apply]
  simp only [Module.End.mul_apply, etaExponentialField_piFockState,
    xiCurrentField_neg_one_piFockState, map_smul]
  push_cast
  module

/-- For a nonzero current index, the full bracket reduces exactly to the oscillator-dressing
commutator; the charge momentum is absent. -/
theorem xiCurrentField_comm_exponential_piFockState_of_ne (j t q : ℤ) (p : HyperFock)
    (hj : j ≠ -1) :
    bracketDist xiCurrentField etaExponentialField j t (piFockState p q)
      = piFockState
          (xiOsc (-j - 1) (etaDress t p) - etaDress t (xiOsc (-j - 1) p))
          (q + 1) := by
  rw [bracketDist_apply, LinearMap.sub_apply]
  simp only [Module.End.mul_apply, etaExponentialField_piFockState,
    xiCurrentField_piFockState, if_neg hj, add_zero]
  rw [piFockState, piFockState, piFockState, TensorProduct.sub_tmul]

/-- The one remaining scalar Fock-space identity for the transverse OPE.

It is a proposition, not an assumed theorem.  A direction-parametric version of the existing
positive-lattice Newton contraction would prove it from `xiOsc_etaOsc_comm`. -/
def XiDressContraction : Prop :=
  ∀ (j t : ℤ) (p : HyperFock), j ≠ -1 →
    xiOsc (-j - 1) (etaDress t p) - etaDress t (xiOsc (-j - 1) p)
      = etaDress (t + j + 1) p

/-- The direction-free Newton calculation discharges the oscillator-dressing gate. -/
theorem xiDressContraction : XiDressContraction := by
  intro j t p hj
  rw [xiOsc_etaDress_comm, if_neg hj]

/-- The contraction gate gives the expected bracket on every pure charge state. -/
theorem xiCurrentField_comm_exponential_piFockState
    (hcontr : XiDressContraction) (j t q : ℤ) (p : HyperFock) :
    bracketDist xiCurrentField etaExponentialField j t (piFockState p q)
      = etaExponentialField (t + j + 1) (piFockState p q) := by
  by_cases hj : j = -1
  · subst hj
    rw [xiCurrentField_neg_one_comm_exponential_piFockState]
    congr 2
    ring
  · rw [xiCurrentField_comm_exponential_piFockState_of_ne j t q p hj,
      hcontr j t p hj, etaExponentialField_piFockState]

/-- Operator-valued coefficient relation for the transverse current, conditional only on the
isolated Fock-space contraction gate. -/
theorem xiCurrentField_comm_exponential (hcontr : XiDressContraction) (j t : ℤ) :
    bracketDist xiCurrentField etaExponentialField j t
      = etaExponentialField (t + j + 1) := by
  refine LinearMap.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add y1 y2 h1 h2 => rw [map_add, map_add, h1, h2]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero, map_zero, map_zero]
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add, map_add, map_add, h1, h2]
      | single q a =>
          rw [(Finsupp.smul_single_one q a).symm]
          erw [TensorProduct.tmul_smul, map_smul, map_smul,
            show p ⊗ₜ[ℂ] etaChargeBasis q = piFockState p q from rfl,
            xiCurrentField_comm_exponential_piFockState hcontr]

/-- The expected transverse-current locality has bound one once the isolated contraction is
discharged. -/
theorem xiCurrentField_local_exponential (hcontr : XiDressContraction) :
    Local xiCurrentField etaExponentialField := by
  refine ⟨1, ?_⟩
  rw [mulBySubPow_one]
  funext s t
  rw [mulBySub_apply, xiCurrentField_comm_exponential hcontr,
    xiCurrentField_comm_exponential hcontr,
    show t + (s - 1) + 1 = (t - 1) + s + 1 from by ring, sub_self]
  rfl

/-- Unconditional coefficient OPE for the transverse current and charge-one exponential. -/
theorem xiCurrentField_comm_exponential_full (j t : ℤ) :
    bracketDist xiCurrentField etaExponentialField j t
      = etaExponentialField (t + j + 1) :=
  xiCurrentField_comm_exponential xiDressContraction j t

/-- The transverse current and null exponential are mutually local with bound one. -/
theorem xiCurrentField_local_exponential_full :
    Local xiCurrentField etaExponentialField :=
  xiCurrentField_local_exponential xiDressContraction

end
end InverseDSPi
end VOA
