/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2KacVacuumCoefficient

/-!
# The simple admissible zero of the reduced affine vacuum product

At energy q(p-1) and positive charge p-1, the remaining zero label has
exactly one descendant: the empty word. All other nonhorizontal factors
are nonzero. Its slope is q, so the derivative is nonzero as well.
-/
namespace VOA.Wak.Charged
open Polynomial AffineVOA.HighestModule
noncomputable section
open scoped Classical
local instance admissibleRootFintype (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := jointIndexFintype n c

/-- The first vacuum block has positive principal bound, so its horizontal
factor is present and the proved coefficient identity applies. -/
theorem admissible_principal_positive (p q : ℕ) (hp : 2≤p) (hq : 0<q) :
    0<2*((q*(p-1) : ℕ) : ℤ)-((p : ℤ)-1) := by
  have hcast : ((p-1 : ℕ) : ℤ)=(p : ℤ)-1 := by omega
  push_cast
  rw [hcast]
  have hq' : (1 : ℤ)≤q := by omega
  have hp' : (2 : ℤ)≤p := by omega
  nlinarith

/-- The first admissible real root lies in the actual finite Kac index
set, with its energy and both principal cutoffs checked explicitly. -/
theorem admissible_first_label_mem (p q : ℕ) (hp : 2≤p) (hq : 0<q) :
    ((0,q-1),p-2)∈affineKacLabels (q*(p-1)) ((p : ℤ)-1) := by
  have hr : p-2+1=p-1 := by omega
  have hm : q-1+1=q := by omega
  have hb : (p-2 : ℕ)<(2*((q*(p-1) : ℕ) : ℤ)-((p : ℤ)-1)).toNat ∧
      (q-1 : ℕ)<(2*((q*(p-1) : ℕ) : ℤ)-((p : ℤ)-1)).toNat+1 := by
    have hc : ((p-1 : ℕ) : ℤ)=(p : ℤ)-1 := by omega
    have he : (2*((q*(p-1) : ℕ) : ℤ)-((p : ℤ)-1))=
        (2*(q : ℤ)-1)*((p : ℤ)-1) := by push_cast; rw [hc]; ring
    rw [he]
    have hp' : (2 : ℤ)≤p := by omega
    have hq' : (1 : ℤ)≤q := by omega
    have hbp : (p : ℤ)-1≤(2*(q : ℤ)-1)*((p : ℤ)-1) := by nlinarith
    have hbq : (q : ℤ)-1≤(2*(q : ℤ)-1)*((p : ℤ)-1) := by nlinarith
    omega
  simp only [Nat.cast_mul] at hb
  simp [affineKacLabels,realRootModes,jointModeBox,oscillatorEnergy,hr,hm,Nat.mul_comm]
  omega

/-- Its descendant multiplicity is exactly one, not merely bounded below. -/
theorem admissible_first_multiplicity (p q : ℕ) (hp : 2≤p) (hq : 0<q) :
    affineKacMultiplicity (q*(p-1)) ((p : ℤ)-1) ((0,q-1),p-2)=1 := by
  have hr : p-2+1=p-1 := by omega
  have hm : q-1+1=q := by omega
  have hc : ((p-1 : ℕ) : ℤ)=(p : ℤ)-1 := by omega
  simpa [affineKacMultiplicity,oscillatorEnergy,oscillatorCharge,hr,hm,hc,
    Nat.mul_comm] using jointIndex_zero_zero_card

/-- The central polynomial belonging to one Kac root factor, before its
actual descendant multiplicity is applied. -/
def affineRootPolynomial (i : (Fin 3×ℕ)×ℕ) : ℂ[X] :=
  -(Polynomial.C (realRootSlope i.1 : ℂ)*(X+Polynomial.C 2)+
    Polynomial.C (realRootOffset i.1 i.2 : ℂ))

/-- Its value is minus the actual Kac highest weight at shifted level. -/
theorem affineRootPolynomial_eval (k : ℂ) (i : (Fin 3×ℕ)×ℕ) :
    (affineRootPolynomial i).eval k= -realRootWeight (k+2) i := by
  simp [affineRootPolynomial,realRootWeight]

/-- The first real-root factor is linear with slope minus q and vanishes
at the admissible central level p/q-2. -/
theorem admissible_first_root_polynomial (p q : ℕ) (hp : 2≤p) (hq : 0<q) :
    affineRootPolynomial ((0,q-1),p-2)=
      Polynomial.C (-(q : ℂ))*(X-Polynomial.C ((p : ℂ)/q-2)) := by
  have hqC : (q : ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hpc : ((p-2 : ℕ) : ℂ)=(p : ℂ)-2 := by exact_mod_cast (Nat.cast_sub hp : ((p-2 : ℕ) : ℤ)=(p : ℤ)-2)
  have hqc : ((q-1 : ℕ) : ℂ)=(q : ℂ)-1 := by exact_mod_cast (Nat.cast_sub (by omega : 1≤q) : ((q-1 : ℕ) : ℤ)=(q : ℤ)-1)
  apply Polynomial.funext
  intro k
  simp [affineRootPolynomial,realRootSlope,realRootOffset,hpc,hqc]
  field_simp
  ring

/-- Remove the unique admissible factor as well as the horizontal one.
The remaining polynomial has nonzero value at the admissible level. -/
def admissibleVacuumRemainder (p q : ℕ) : ℂ[X] :=
  ∏ i∈((affineKacLabels (q*(p-1)) ((p : ℤ)-1)).erase ((1,0),0)).erase ((0,q-1),p-2),
    (affineRootPolynomial i)^affineKacMultiplicity (q*(p-1)) ((p : ℤ)-1) i

/-- The reduced actual Kac product splits off exactly one linear factor
at the first admissible level, rather than a higher power. -/
theorem affineVacuumProduct_admissible_factor (p q : ℕ) (hp : 2≤p) (hq : 0<q) :
    affineVacuumProduct (q*(p-1)) ((p : ℤ)-1)=
      (Polynomial.C (-(q : ℂ))*(X-Polynomial.C ((p : ℂ)/q-2)))*admissibleVacuumRemainder p q := by
  classical
  have hm : ((0,q-1),p-2)∈(affineKacLabels (q*(p-1)) ((p : ℤ)-1)).erase ((1,0),0) :=
    Finset.mem_erase.mpr ⟨by simp,admissible_first_label_mem p q hp hq⟩
  have he := Finset.mul_prod_erase ((affineKacLabels (q*(p-1)) ((p : ℤ)-1)).erase ((1,0),0))
    (fun i => (affineRootPolynomial i)^affineKacMultiplicity (q*(p-1)) ((p : ℤ)-1) i) hm
  dsimp only at he
  rw [admissible_first_multiplicity p q hp hq,pow_one,admissible_first_root_polynomial p q hp hq] at he
  exact he.symm

/-- Every remaining factor has a nonzero value, by the proved complete
classification of weight-zero Kac labels at this energy. -/
theorem admissibleVacuumRemainder_ne_zero (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (hcop : p.Coprime q) :
    (admissibleVacuumRemainder p q).eval ((p : ℂ)/q-2)≠0 := by
  classical
  simp only [admissibleVacuumRemainder,eval_prod,eval_pow,affineRootPolynomial_eval,
    sub_add_cancel]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  obtain ⟨hne,hii⟩ := Finset.mem_erase.mp hi
  obtain ⟨hnh,hii⟩ := Finset.mem_erase.mp hii
  apply pow_ne_zero
  apply neg_ne_zero.mpr
  intro hz
  rcases admissible_zero_labels p q hp hq hcop i hii hz with hh|hh
  · exact hnh hh
  · exact hne hh

/-- The reduced ordinary product has a zero and nonzero derivative at
every admissible parameter. This is an unconditional finite factor calculation. -/
theorem affineVacuumProduct_admissible_simple (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (hcop : p.Coprime q) :
    (affineVacuumProduct (q*(p-1)) ((p : ℤ)-1)).eval ((p : ℂ)/q-2)=0 ∧
    (affineVacuumProduct (q*(p-1)) ((p : ℤ)-1)).derivative.eval ((p : ℂ)/q-2)≠0 := by
  rw [affineVacuumProduct_admissible_factor p q hp hq]
  constructor
  · simp
  · have hqC : -(q : ℂ)≠0 := neg_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt hq))
    simpa only [derivative_mul,derivative_C,derivative_sub,derivative_X,
      sub_zero,zero_mul,mul_one,zero_add,eval_add,eval_mul,eval_sub,eval_X,eval_C,
      sub_self,mul_zero,zero_add,add_zero] using
      mul_ne_zero hqC (admissibleVacuumRemainder_ne_zero p q hp hq hcop)

/-- The actual shifted Verma denominator is nonzero at every admissible
parameter in the first vacuum block, using the full proved Kac identity. -/
theorem affineMinusTwoPolynomial_admissible_ne_zero (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (hcop : p.Coprime q) :
    (affineMinusTwoPolynomial (q*(p-1)) (p : ℤ)).eval ((p : ℂ)/q-2)≠0 := by
  have ht : (p : ℂ)/q≠0 := div_ne_zero
    (by exact_mod_cast (show p≠0 by omega)) (by exact_mod_cast (Nat.ne_of_gt hq))
  have hk : (p : ℂ)/q-2+2≠0 := by simpa only [sub_add_cancel] using ht
  rw [affineMinusTwoPolynomial_eval,weightDeterminant_eq_affineKacProduct_all,
    eval_mul,eval_C]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => derivativeMultiplier_ne_zero _ hk _ _))
    (affineKacProduct_admissible_minus_two p q hp hq hcop)

/-- The genuine Chevalley vacuum determinant has a simple root at the
first admissible level and charge. The proof uses the actual coefficient
identity, not a vacuum-character assumption or a formal proposed product. -/
theorem vacuumChevalleyDeterminant_admissible_simple (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (hcop : p.Coprime q) :
    (vacuumChevalleyPolynomial (q*(p-1)) ((p : ℤ)-1)).det.eval ((p : ℂ)/q-2)=0 ∧
    (vacuumChevalleyPolynomial (q*(p-1)) ((p : ℤ)-1)).det.derivative.eval ((p : ℂ)/q-2)≠0 := by
  classical
  let k : ℂ := (p : ℂ)/q-2
  let n := q*(p-1)
  let c : ℤ := (p : ℤ)-1
  have hc : c+1=(p : ℤ) := by dsimp [c]; ring
  have hid := affine_vacuum_polynomial_identity n c (admissible_principal_positive p q hp hq)
  obtain ⟨hz,hd⟩ := affineVacuumProduct_admissible_simple p q hp hq hcop
  have hden := affineMinusTwoPolynomial_admissible_ne_zero p q hp hq hcop
  have hscale := vacuumDeterminantScale_ne_zero n c
  have hk : k+2≠0 := by
    dsimp [k]
    rw [sub_add_cancel]
    exact div_ne_zero (by exact_mod_cast (show p≠0 by omega)) (by exact_mod_cast (Nat.ne_of_gt hq))
  have hlead := affineLeadingPolynomial_eval_ne_zero k hk n c
  have he := congrArg (Polynomial.eval k) hid
  simp only [eval_mul,eval_C] at he
  have hv : (vacuumChevalleyPolynomial n c).det.eval k=0 := by
    rw [show (affineVacuumProduct n c).eval k=0 from hz,mul_zero,hc] at he
    exact (mul_eq_zero.mp he).resolve_right hden
  refine ⟨hv,?_⟩
  intro hvd
  have hdid := congrArg (fun P : ℂ[X] => P.derivative.eval k) hid
  simp only [derivative_mul,derivative_C,eval_add,eval_mul,eval_zero,eval_C] at hdid
  rw [show (vacuumChevalleyPolynomial n c).det.derivative.eval k=0 from hvd,hv,
    show (affineVacuumProduct n c).eval k=0 from hz] at hdid
  have hnon : vacuumDeterminantScale n c*(affineLeadingPolynomial n c).eval k*
      (affineVacuumProduct n c).derivative.eval k≠0 := mul_ne_zero (mul_ne_zero hscale hlead) hd
  apply hnon
  linear_combination -hdid

end
end VOA.Wak.Charged
