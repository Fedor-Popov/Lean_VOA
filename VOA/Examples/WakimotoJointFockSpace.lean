/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2HighestPairingPolynomial
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Data.Finsupp.Weight

/-!
# Finite actual joint spaces of the charged Wakimoto polynomial module

Energy alone permits arbitrarily many gamma zero modes. Fixing ghost charge
as well removes this infinite direction. The positive principal weight
2 energy minus charge bounds every oscillator index and occupation, giving
an explicit finite coefficient model for each joint space.
-/
namespace VOA.Wak.Charged
open MvPolynomial
open scoped BigOperators
noncomputable section

/-- Actual beta, gamma and boson occupation multiplicities. -/
abbrev Occupation := (Fin 3×ℕ)→₀ℕ

/-- Natural energy of one oscillator; gamma at depth zero has energy zero. -/
def oscillatorEnergy (v : Fin 3×ℕ) : ℕ := if v.1=1 then v.2 else v.2+1

/-- Integer ghost charge of one oscillator. -/
def oscillatorCharge (v : Fin 3×ℕ) : ℤ := if v.1=0 then 1 else if v.1=1 then -1 else 0

/-- Positive principal weight of an oscillator, including gamma zero. -/
def oscillatorPrincipal (v : Fin 3×ℕ) : ℕ := if v.1=2 then 2*v.2+2 else 2*v.2+1

/-- Total energy of an actual occupation monomial. -/
def occupationEnergy : Occupation→+ℕ := Finsupp.weight oscillatorEnergy

/-- Total signed ghost charge of an actual occupation monomial. -/
def occupationCharge : Occupation→+ℤ := Finsupp.weight oscillatorCharge

/-- Total positive principal weight of an actual occupation monomial. -/
def occupationPrincipal : Occupation→+ℕ := Finsupp.weight oscillatorPrincipal

/-- Principal weight is exactly twice energy minus ghost charge. -/
theorem occupationPrincipal_eq (d : Occupation) :
    (occupationPrincipal d : ℤ)=2*(occupationEnergy d : ℤ)-occupationCharge d := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => rw [map_add,map_add,map_add,Nat.cast_add,Nat.cast_add,hd,he]; ring
  | single v n =>
      simp only [occupationPrincipal,occupationEnergy,occupationCharge,Finsupp.weight_single]
      rcases v with ⟨a,j⟩
      rcases fin3_cases a with rfl|rfl|rfl <;>
        norm_num [oscillatorPrincipal,oscillatorEnergy,oscillatorCharge,nsmul_eq_mul,Fin.ext_iff] <;> ring

/-- Every oscillator has positive principal weight and its depth is smaller
than that weight. -/
theorem oscillatorPrincipal_bounds (v : Fin 3×ℕ) :
    0<oscillatorPrincipal v ∧ v.2<oscillatorPrincipal v := by
  unfold oscillatorPrincipal
  split_ifs <;> omega

/-- Occupations with a fixed positive grading label. -/
abbrev PrincipalIndex (N : ℕ) := {d : Occupation // occupationPrincipal d=N}

/-- Every multiplicity in a fixed principal occupation is bounded by N. -/
theorem principalIndex_bound (N : ℕ) (d : PrincipalIndex N) (v : Fin 3×ℕ) : d.val v≤N := by
  calc
    d.val v≤occupationPrincipal d.val :=
      Finsupp.le_weight oscillatorPrincipal (by have := (oscillatorPrincipal_bounds v).1; omega) d.val
    _=N := d.property

/-- An occupied variable has depth at most N. Thus no unbounded gamma-zero
or high-mode direction remains at a fixed principal weight. -/
theorem principalIndex_support (N : ℕ) (d : PrincipalIndex N) (v : Fin 3×ℕ)
    (hv : d.val v≠0) : v.2≤N := by
  have h := Finsupp.le_weight_of_ne_zero' oscillatorPrincipal hv
  change oscillatorPrincipal v≤occupationPrincipal d.val at h
  rw [d.property] at h
  have := (oscillatorPrincipal_bounds v).2
  omega

/-- Fixed-principal-weight occupations embed in a finite box of finite
multiplicities. This is an actual finiteness proof, not a character premise. -/
instance principalIndex_finite (N : ℕ) : Finite (PrincipalIndex N) := by
  let f : PrincipalIndex N → ((Fin 3×Fin (N+1))→Fin (N+1)) :=
    fun d v => ⟨d.val (v.1,v.2.val),Nat.lt_succ_of_le (principalIndex_bound N d _)⟩
  apply Finite.of_injective f
  intro d e hde
  apply Subtype.ext
  ext v
  by_cases hv : v.2<N+1
  · have h := congrArg (fun F => (F (v.1,⟨v.2,hv⟩)).val) hde
    exact h
  · have hd : d.val v=0 := by by_contra hz; have := principalIndex_support N d v hz; omega
    have he : e.val v=0 := by by_contra hz; have := principalIndex_support N e v hz; omega
    rw [hd,he]

/-- Actual monomial indices of fixed energy and signed ghost charge. -/
abbrev JointIndex (n : ℕ) (c : ℤ) :=
  {d : Occupation // occupationEnergy d=n ∧ occupationCharge d=c}

/-- Each joint occupation has its forced principal label 2n-c. -/
theorem jointIndex_principal (n : ℕ) (c : ℤ) (d : JointIndex n c) :
    occupationPrincipal d.val=(2*(n : ℤ)-c).toNat := by
  have h := occupationPrincipal_eq d.val
  rw [d.property.1,d.property.2] at h
  omega

/-- Every joint occupation set is finite, including joint spaces with
negative ghost charge or energy zero. -/
instance jointIndex_finite (n : ℕ) (c : ℤ) : Finite (JointIndex n c) := by
  let f : JointIndex n c → PrincipalIndex (2*(n : ℤ)-c).toNat :=
    fun d => ⟨d.val,jointIndex_principal n c d⟩
  apply Finite.of_injective f
  intro d e he
  exact Subtype.ext (congrArg (fun x : PrincipalIndex (2*(n : ℤ)-c).toNat => x.val) he)

/-- A finite indexing instance for actual joint monomial coefficients. -/
def jointIndexFintype (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := Fintype.ofFinite _

/-- The actual polynomial subspace supported exactly at the given joint
energy and charge. Its ambient carrier is the existing Wakimoto Fock space. -/
def jointFockSpace (n : ℕ) (c : ℤ) : Submodule ℂ WakFock :=
  Finsupp.supported ℂ ℂ {d : Occupation | occupationEnergy d=n ∧ occupationCharge d=c}

/-- Joint polynomials are exactly finite coefficient vectors on the actual
joint monomial index set, with no quotient or faithfulness assumption. -/
def jointFockCoefficientEquiv (n : ℕ) (c : ℤ) :
    jointFockSpace n c ≃ₗ[ℂ] (JointIndex n c→₀ℂ) :=
  Finsupp.supportedEquivFinsupp _

/-- The actual joint polynomial subspace is finite-dimensional. -/
instance jointFockSpace_finiteDimensional (n : ℕ) (c : ℤ) :
    FiniteDimensional ℂ (jointFockSpace n c) := by
  letI := jointIndexFintype n c
  exact (jointFockCoefficientEquiv n c).symm.finiteDimensional

/-- Its dimension is exactly the number of actual joint occupation
monomials; later word matrices must use an equinumerous index set. -/
theorem jointFockSpace_finrank (n : ℕ) (c : ℤ) :
    Module.finrank ℂ (jointFockSpace n c)=Nat.card (JointIndex n c) := by
  letI := jointIndexFintype n c
  rw [(jointFockCoefficientEquiv n c).finrank_eq,Module.finrank_finsupp_self,Nat.card_eq_fintype_card]

end
end VOA.Wak.Charged
