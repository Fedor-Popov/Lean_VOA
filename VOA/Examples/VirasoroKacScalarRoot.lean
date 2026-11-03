/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroKacVacuumCoefficient
import VOA.Examples.VirasoroKacLabelSeparation
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Simple zeros of the reduced ordinary Kac product

These statements concern the explicit finite product, independently of
whether it has been identified with an actual determinant. One vanishing
factor at the terminal label has multiplicity one. Its nonzero derivative
cannot be cancelled by the other nonzero factors.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule
open scoped Classical
set_option maxHeartbeats 1200000

/-- There is exactly one level-zero Verma partition: the empty word. -/
theorem vermaPartitions_card_zero : Fintype.card (VermaPartitions 0) = 1 := by
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨[],sortedWord_nil,rfl⟩, ?_⟩
  intro w
  apply Subtype.ext
  exact (verma_energy_zero_iff w.val).mp w.property.2

/-- The rational Kac weight is differentiable at every nonzero parameter,
with its ordinary rational derivative displayed explicitly. -/
theorem fusionKacWeight_hasDerivAt (r s t : ℂ) (ht : t ≠ 0) :
    HasDerivAt (fusionKacWeight r s)
      ((r^2-1)/4 - (s^2-1)/(4*t^2)) t := by
  have he := (((((hasDerivAt_id t).const_mul r).sub_const s).pow 2).sub
    (((hasDerivAt_id t).sub_const 1).pow 2)).div
      ((hasDerivAt_id t).const_mul 4) (mul_ne_zero (by norm_num) ht)
  convert he using 1 <;> dsimp [fusionKacWeight] <;> field_simp <;> ring

/-- Every finite subproduct of the scalar Kac factors is differentiable
away from parameter zero, even where one of its factors vanishes. -/
theorem kacScalarSubproduct_differentiable (n : ℕ)
    (S : Finset (Fin (n+1) × Fin (n+1))) (t : ℂ) (ht : t ≠ 0) :
    DifferentiableAt ℂ (fun z => ∏ i ∈ S,
      (-fusionKacWeight (i.1.val+1) (i.2.val+1) z) ^
        Fintype.card (VermaPartitions (n+1-(i.1.val+1)*(i.2.val+1)))) t := by
  apply DifferentiableAt.fun_finset_prod
  intro i hi
  exact ((fusionKacWeight_hasDerivAt _ _ t ht).differentiableAt.neg).pow _

/-- A terminal zero label is a simple zero of the reduced scalar product,
provided all its other labels are nonzero and its own derivative is nonzero.
The terminal exponent is proved to be one from the actual partition count. -/
theorem kacVacuumScalar_simple_of_label (n : ℕ) (t : ℂ) (ht : t ≠ 0)
    (a : Fin (n+1) × Fin (n+1))
    (ha : a ∈ (kacLabels (n+1)).erase (0,0))
    (hlevel : (a.1.val+1)*(a.2.val+1) = n+1)
    (hz : fusionKacWeight (a.1.val+1) (a.2.val+1) t = 0)
    (hd : _root_.deriv (fusionKacWeight (a.1.val+1) (a.2.val+1)) t ≠ 0)
    (hothers : ∀ i ∈ (kacLabels (n+1)).erase (0,0), i ≠ a →
      fusionKacWeight (i.1.val+1) (i.2.val+1) t ≠ 0) :
    kacVacuumScalar t n = 0 ∧ _root_.deriv (fun z => kacVacuumScalar z n) t ≠ 0 := by
  let S := ((kacLabels (n+1)).erase (0,0)).erase a
  let g := fun z => ∏ i ∈ S,
    (-fusionKacWeight (i.1.val+1) (i.2.val+1) z) ^
      Fintype.card (VermaPartitions (n+1-(i.1.val+1)*(i.2.val+1)))
  have he (z : ℂ) : kacVacuumScalar z n =
      -fusionKacWeight (a.1.val+1) (a.2.val+1) z * g z := by
    have hh := Finset.mul_prod_erase ((kacLabels (n+1)).erase (0,0))
      (fun i => (-fusionKacWeight (i.1.val+1) (i.2.val+1) z) ^
        Fintype.card (VermaPartitions (n+1-(i.1.val+1)*(i.2.val+1)))) ha
    simpa only [hlevel,Nat.sub_self,vermaPartitions_card_zero,pow_one] using hh.symm
  have hg : g t ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (neg_ne_zero.mpr (hothers i
      (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1))
  have hgd := kacScalarSubproduct_differentiable n S t ht
  have hfd := (fusionKacWeight_hasDerivAt (a.1.val+1) (a.2.val+1) t ht).differentiableAt
  have hh := hfd.hasDerivAt.neg.mul hgd.hasDerivAt
  have hf : (fun z => kacVacuumScalar z n) =
      (fun z => -fusionKacWeight (a.1.val+1) (a.2.val+1) z * g z) := funext he
  constructor
  · rw [he,hz,neg_zero,zero_mul]
  · rw [hf]
    change _root_.deriv (-fusionKacWeight (a.1.val+1) (a.2.val+1) * g) t ≠ 0
    rw [hh.deriv]
    simpa only [Pi.neg_apply,hz,neg_zero,zero_mul,add_zero,g] using mul_ne_zero (neg_ne_zero.mpr hd) hg

/-- The arithmetic minimal-model weight agrees exactly with the rational
fusion weight at t=p/q. This fixes the label orientation for later roots. -/
theorem fusionKacWeight_minimal (p q r s : ℕ) (hp : 0 < p) (hq : 0 < q) :
    fusionKacWeight r s ((p:ℂ)/q) =
      (VirMinimalArithmetic.minimalKacWeight p q r s : ℂ) := by
  have hp0 : (p:ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  have hq0 : (q:ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  unfold fusionKacWeight VirMinimalArithmetic.minimalKacWeight
  push_cast
  field_simp
  <;> ring

/-- At the first vacuum label the Kac weight crosses zero with nonzero
velocity. Coprimality is not needed for this derivative, only p>q>=2. -/
theorem fusionKacWeight_minimal_derivative (p q : ℕ) (hq : 2 ≤ q) (hpq : q < p) :
    _root_.deriv (fusionKacWeight (q-1:ℕ) (p-1:ℕ)) ((p:ℂ)/q) ≠ 0 := by
  have hp : 0 < p := by omega
  have hp0 : (p:ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  have hq0 : (q:ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  rw [(fusionKacWeight_hasDerivAt _ _ _ (div_ne_zero hp0 hq0)).deriv]
  have he : ((((q-1:ℕ):ℂ)^2-1)/4 - (((p-1:ℕ):ℂ)^2-1)/(4*((p:ℂ)/q)^2)) =
      (q:ℂ)*((q:ℂ)-(p:ℂ))/(2*(p:ℂ)) := by
    rw [Nat.cast_sub (by omega : 1 ≤ q),Nat.cast_sub (by omega : 1 ≤ p)]
    push_cast
    field_simp
    <;> ring
  rw [he]
  apply div_ne_zero
  · apply mul_ne_zero hq0
    exact sub_ne_zero.mpr (by exact_mod_cast Nat.ne_of_lt hpq)
  · exact mul_ne_zero (by norm_num) hp0

/-- For every ordered coprime minimal-model pair, the explicit reduced Kac
scalar has a simple zero at the first vacuum level. This is an unconditional
fact about the proposed finite product; equality with actual determinants
is not proved in this file (the root input is supplied by `VirasoroScreeningKacRoots.lean`). -/
theorem kacVacuumScalar_minimal_simple (p q n : ℕ) (hq : 2 ≤ q)
    (hpq : q < p) (hcop : p.Coprime q) (hn : n+1 = (p-1)*(q-1)) :
    kacVacuumScalar ((p:ℂ)/q) n = 0 ∧
      _root_.deriv (fun z => kacVacuumScalar z n) ((p:ℂ)/q) ≠ 0 := by
  have hp : 2 ≤ p := by omega
  have hp0 : (p:ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hq0 : (q:ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hp1 : 1 ≤ p-1 := by omega
  have hq1 : 1 ≤ q-1 := by omega
  have hp2 : p-2+1 = p-1 := by omega
  have hq2 : q-2+1 = q-1 := by omega
  have hpl : p-2 < n+1 := by nlinarith
  have hql : q-2 < n+1 := by nlinarith
  let a : Fin (n+1) × Fin (n+1) := (⟨q-2,hql⟩,⟨p-2,hpl⟩)
  have ha1 : a.1.val+1 = q-1 := by dsimp [a]; omega
  have ha2 : a.2.val+1 = p-1 := by dsimp [a]; omega
  have hlev : (a.1.val+1)*(a.2.val+1) = n+1 := by rw [ha1,ha2,hn,Nat.mul_comm]
  have hane : a ≠ (0,0) := by
    intro hh
    have hh' := congrArg (fun i : Fin (n+1) × Fin (n+1) => i.2.val) hh
    dsimp [a] at hh'
    omega
  have ham : a ∈ (kacLabels (n+1)).erase (0,0) := by
    exact Finset.mem_erase.mpr ⟨hane,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlev.le⟩⟩
  have ha1c : (a.1.val:ℂ)+1 = ((q-1:ℕ):ℂ) := by exact_mod_cast ha1
  have ha2c : (a.2.val:ℂ)+1 = ((p-1:ℕ):ℂ) := by exact_mod_cast ha2
  apply kacVacuumScalar_simple_of_label n _ (div_ne_zero hp0 hq0) a ham hlev
  · rw [ha1c,ha2c,fusionKacWeight_minimal p q _ _ (by omega) (by omega),
      VirMinimalArithmetic.minimalKacWeight_minimal_label hp hq]
    norm_num
  · rw [ha1c,ha2c]
    exact fusionKacWeight_minimal_derivative p q hq hpq
  · intro i hi hia hz
    have hz' : VirMinimalArithmetic.minimalKacWeight p q (i.1.val+1) (i.2.val+1) = 0 := by
      rw [← Rat.cast_inj (α := ℂ)]
      simpa only [Rat.cast_zero, ← fusionKacWeight_minimal p q _ _ (by omega) (by omega),
        Nat.cast_add,Nat.cast_one] using hz
    have hil := (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).2
    have hil' := hil.trans_eq hn
    rcases VirMinimalArithmetic.minimalKacWeight_zero_first_labels hp hq
      (by omega) (by omega) hcop hz' hil' with hh | hh
    · apply (Finset.mem_erase.mp hi).1
      apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_zero] <;> omega
    · apply hia
      apply Prod.ext <;> apply Fin.ext <;> omega

end VOA.InverseDS.VirasoroVerma
