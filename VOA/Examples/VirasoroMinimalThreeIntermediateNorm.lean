/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFusionThreeStateRecursion

/-!
# Actual intermediate norms for the q=3 vacuum family

The preterminal Ward equations determine every positive-mode action on the
actual intermediate vacuum coefficients. Combining them with the full
state recurrence gives a scalar recursion for their canonical norms.
This does not identify a terminal residual with the singular norm derivative.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule

/-- The incoming and field weights coincide at the q=3 vacuum parameters. -/
theorem minimalThree_incoming_eq_field (p : ℕ) (hp : 2≤p) :
    fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))=
      vermaBSAWeight 3 ((3:ℂ)/(p:ℂ)) := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
  have hs : ((p-1:ℕ):ℂ)=(p:ℂ)-1 := by exact_mod_cast Int.ofNat_sub (by omega : 1≤p)
  unfold fusionKacWeight vermaBSAWeight
  rw [hs]
  norm_num
  field_simp
  ring

/-- The actual preterminal vacuum coefficient at the minimal-model charge. -/
noncomputable def minimalThreeVacuumCoefficient (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (r : ℕ) : VirUniv (vermaBSACharge ((3:ℂ)/(p:ℂ))) :=
  vacuumProjection _ ((minimalThreeChargeKernel p hp hcop (vermaBSACharge ((3:ℂ)/(p:ℂ)))).val r)

/-- The intermediate family starts with the genuine vacuum. -/
@[simp] theorem minimalThreeVacuumCoefficient_zero (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    minimalThreeVacuumCoefficient p hp hcop 0=vacVec (vermaBSACharge ((3:ℂ)/(p:ℂ))) := by
  simp [minimalThreeVacuumCoefficient,minimalThreeChargeKernel_zero]

/-- The first Ward identity on every preterminal coefficient. Equal
incoming and field weights reduce its multiplier to the output index. -/
theorem minimalThreeVacuumCoefficient_L1 (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (r : ℕ) (hr : r+1<(p-1)*2) :
    Lop (vermaBSACharge ((3:ℂ)/(p:ℂ))) 1 (minimalThreeVacuumCoefficient p hp hcop (r+1))=
      (r:ℂ) • minimalThreeVacuumCoefficient p hp hcop r := by
  have hh := nonresonant_first_below_at_charge (vermaBSACharge ((3:ℂ)/(p:ℂ))) 0
    (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ)) 3 ((p-1)*2)
    (minimal_three_parameter_ne_zero p (by omega)) (by omega)
    (minimalThreeChargeKernel p hp hcop _) (minimalThreeChargeKernel_below p hp hcop _)
    (fun j hj hjN => minimalThree_diagonal_interior p j hp hcop hj hjN) r (by omega)
  change vermaMode _ 0 1 _-(0-fusionKacWeight _ _ _+vermaBSAWeight 3 _+(r:ℂ)) • _=0 at hh
  rw [minimalThree_incoming_eq_field p hp] at hh
  simp only [zero_sub,neg_add_cancel_left] at hh
  rw [sub_eq_zero] at hh
  unfold minimalThreeVacuumCoefficient
  rw [← vacuumProjection_mode,hh,map_smul]
  module

/-- The second Ward identity on every preterminal coefficient. The first
input defect is zero, leaving the ordinary primary covariance multiplier. -/
theorem minimalThreeVacuumCoefficient_L2 (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (r : ℕ) (hr : r+2<(p-1)*2) :
    Lop (vermaBSACharge ((3:ℂ)/(p:ℂ))) 2 (minimalThreeVacuumCoefficient p hp hcop (r+2))=
      (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+(r:ℂ)) • minimalThreeVacuumCoefficient p hp hcop r := by
  have hP := nonresonant_first_below_at_charge (vermaBSACharge ((3:ℂ)/(p:ℂ))) 0
    (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ)) 3 ((p-1)*2)
    (minimal_three_parameter_ne_zero p (by omega)) (by omega)
    (minimalThreeChargeKernel p hp hcop _) (minimalThreeChargeKernel_below p hp hcop _)
    (fun j hj hjN => minimalThree_diagonal_interior p j hp hcop hj hjN) r (by omega)
  have hQ := nonresonant_second_below 0
    (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ)) 3 ((p-1)*2)
    (minimal_three_parameter_ne_zero p (by omega)) (by omega)
    (minimalThreeChargeKernel p hp hcop _) (minimalThreeChargeKernel_below p hp hcop _)
    (fun j hj hjN => minimalThree_diagonal_interior p j hp hcop hj hjN) r (by omega)
  change vermaMode _ 0 2 _-(0-fusionKacWeight _ _ _+2*vermaBSAWeight 3 _+(r:ℂ)) • _-
    (3:ℂ) • (wardP1Map _ 0 _ _ (minimalThreeChargeKernel p hp hcop _)).val r=0 at hQ
  rw [hP,smul_zero,sub_zero,minimalThree_incoming_eq_field p hp] at hQ
  have he : 0-vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+2*vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+(r:ℂ)=
      vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+(r:ℂ) := by ring
  rw [he,sub_eq_zero] at hQ
  unfold minimalThreeVacuumCoefficient
  rw [← vacuumProjection_mode,hQ,map_smul]

/-- All higher positive Ward actions follow from the L1/L2 commutator.
Only actual preterminal coefficients occur in the induction. -/
theorem minimalThreeVacuumCoefficient_higher (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (m r : ℕ) (hr : r+m+2<(p-1)*2) :
    Lop (vermaBSACharge ((3:ℂ)/(p:ℂ))) ((m:ℤ)+2)
      (minimalThreeVacuumCoefficient p hp hcop (r+m+2))=
      (((m:ℂ)+1)*vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+(r:ℂ)) •
        minimalThreeVacuumCoefficient p hp hcop r := by
  induction m generalizing r with
  | zero => simpa using minimalThreeVacuumCoefficient_L2 p hp hcop r hr
  | succ m ih =>
    have hA := ih (r+1) (by omega)
    have hB := ih r (by omega)
    have h1 := minimalThreeVacuumCoefficient_L1 p hp hcop (r+m+2) (by omega)
    have h2 := minimalThreeVacuumCoefficient_L1 p hp hcop r (by omega)
    have hh := LeeYang.Lop_apply_comm (vermaBSACharge ((3:ℂ)/(p:ℂ))) 1 ((m:ℤ)+2)
      (minimalThreeVacuumCoefficient p hp hcop (r+(m+1)+2))
    rw [show r+(m+1)+2=(r+1)+m+2 by omega,hA,map_smul,h2] at hh
    rw [show (r+1)+m+2=(r+m+2)+1 by omega,h1,map_smul,hB] at hh
    have hz : ¬ (1:ℤ)+((m:ℤ)+2)=0 := by omega
    simp only [if_neg hz,zero_smul,add_zero] at hh
    have hn : (1:ℂ)-((m:ℤ)+2)≠0 := by
      push_cast
      have hm := Nat.cast_add_one_ne_zero (R:=ℂ) m
      intro he; apply hm; linear_combination -he
    push_cast at hh
    apply smul_right_injective _ hn
    convert (show ((1:ℂ)-((m:ℤ)+2)) •
        Lop (vermaBSACharge ((3:ℂ)/(p:ℂ))) (1+((m:ℤ)+2))
          (minimalThreeVacuumCoefficient p hp hcop ((r+m+2)+1)) = _ from
      eq_sub_of_add_eq' hh.symm) using 1
    · congr 2 <;> push_cast <;> ring
    · push_cast at hh ⊢
      simp only [smul_smul,← sub_smul]
      congr 1
      ring

/-- A positive mode lowering coefficient r to j has the usual primary
multiplier j+(r-j-1)a, proved for the actual constructed coefficients. -/
theorem minimalThreeVacuumCoefficient_positive_to (p : ℕ) (hp : 2≤p)
    (hcop : Nat.Coprime p 3) (r j : ℕ) (hj : j<r) (hr : r<(p-1)*2) :
    Lop (vermaBSACharge ((3:ℂ)/(p:ℂ))) ((r:ℤ)-(j:ℤ))
      (minimalThreeVacuumCoefficient p hp hcop r)=
      ((j:ℂ)+((r:ℂ)-(j:ℂ)-1)*vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) •
        minimalThreeVacuumCoefficient p hp hcop j := by
  by_cases he : r=j+1
  · subst r
    simpa using minimalThreeVacuumCoefficient_L1 p hp hcop j hr
  · have hk : r=j+(r-j-2)+2 := by omega
    have hh := minimalThreeVacuumCoefficient_higher p hp hcop (r-j-2) j (by omega)
    rw [← hk] at hh
    have hz : ((r-j-2:ℕ):ℤ)+2=(r:ℤ)-(j:ℤ) := by omega
    have hc : ((r-j-2:ℕ):ℂ)+1=(r:ℂ)-(j:ℂ)-1 := by
      have hi : ((r-j-2:ℕ):ℤ)+1=(r:ℤ)-(j:ℤ)-1 := by omega
      exact_mod_cast hi
    rw [hz,hc] at hh
    simpa only [add_comm] using hh

/-- Pair the full preterminal state equation with its own coefficient.
Adjointness and the proved positive Ward action give a scalar recurrence
for ACTUAL canonical norms, not a guessed formal conformal block. -/
theorem minimalThree_actual_norm_recursion (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (r : ℕ) (hr : r<(p-1)*2) :
    threeStateDiagonal 0 (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
      (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) r *
      (VirGram4.canB (vermaBSACharge ((3:ℂ)/(p:ℂ)))).form
        (minimalThreeVacuumCoefficient p hp hcop r) (minimalThreeVacuumCoefficient p hp hcop r)+
    ∑ j : Fin r, threeStateCoefficient 0 (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
      (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) r j *
      ((j:ℂ)+((r:ℂ)-(j:ℂ)-1)*vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) *
      (VirGram4.canB (vermaBSACharge ((3:ℂ)/(p:ℂ)))).form
        (minimalThreeVacuumCoefficient p hp hcop j) (minimalThreeVacuumCoefficient p hp hcop j)=0 := by
  have hh := minimalThreeChargeKernel_below p hp hcop (vermaBSACharge ((3:ℂ)/(p:ℂ))) r hr
  rw [wardSourceAt_three_state_recursion,minimalThree_incoming_eq_field p hp] at hh
  have he := congrArg (fun v => (VirGram4.canB (vermaBSACharge ((3:ℂ)/(p:ℂ)))).form
    (vacuumProjection _ v) (minimalThreeVacuumCoefficient p hp hcop r)) hh
  simp only [map_add,map_smul,map_sum,LinearMap.add_apply,LinearMap.sum_apply,
    LinearMap.smul_apply,map_zero,LinearMap.zero_apply,smul_eq_mul,vacuumProjection_mode] at he
  change _+∑ j : Fin r, threeStateCoefficient _ _ _ _ r j *
    (VirGram4.canB _).form (Lop _ ((j:ℤ)-(r:ℤ)) (minimalThreeVacuumCoefficient p hp hcop j))
      (minimalThreeVacuumCoefficient p hp hcop r)=0 at he
  have hs (j : Fin r) :
      (VirGram4.canB (vermaBSACharge ((3:ℂ)/(p:ℂ)))).form
        (Lop _ ((j:ℤ)-(r:ℤ)) (minimalThreeVacuumCoefficient p hp hcop j))
        (minimalThreeVacuumCoefficient p hp hcop r)=
      ((j:ℂ)+((r:ℂ)-(j:ℂ)-1)*vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) *
      (VirGram4.canB _).form (minimalThreeVacuumCoefficient p hp hcop j)
        (minimalThreeVacuumCoefficient p hp hcop j) := by
    rw [VirGram4.canB_adj,neg_sub,
      minimalThreeVacuumCoefficient_positive_to p hp hcop r j j.isLt hr,map_smul,smul_eq_mul]
  simp only [hs] at he
  simpa only [mul_assoc] using he

/-- The cubic diagonal is invertible at each positive preterminal index.
This uses the established actual fusion nonresonance, not a new assumption. -/
theorem minimalThree_state_diagonal_ne_zero (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (r : ℕ) (hr0 : 0<r) (hr : r<(p-1)*2) :
    threeStateDiagonal 0 (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
      (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) r≠0 := by
  rw [threeStateDiagonal_eq]
  have hh := minimalThree_diagonal_interior p r hp hcop hr0 hr
  rw [minimalThree_incoming_eq_field p hp] at hh
  exact hh

/-- Compute intermediate norms by the ordinary scalar Ward recurrence.
Only preterminal values are identified with actual state norms below. -/
noncomputable def minimalThreeNormCoefficient (p : ℕ) : ℕ → ℂ
  | 0 => 1
  | r+1 => -((∑ j : Fin (r+1),
      threeStateCoefficient 0 (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
        (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) (r+1) j *
        ((j:ℂ)+(((r+1:ℕ):ℂ)-(j:ℂ)-1)*vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) *
        minimalThreeNormCoefficient p j)) /
      threeStateDiagonal 0 (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
        (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) (r+1)
termination_by r => r

/-- Every scalar preterminal coefficient equals the ACTUAL canonical
norm of the corresponding constructed vacuum coefficient. -/
theorem minimalThreeNormCoefficient_eq_norm (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (r : ℕ) (hr : r<(p-1)*2) :
    minimalThreeNormCoefficient p r =
      (VirGram4.canB (vermaBSACharge ((3:ℂ)/(p:ℂ)))).form
        (minimalThreeVacuumCoefficient p hp hcop r) (minimalThreeVacuumCoefficient p hp hcop r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [minimalThreeNormCoefficient,VirGram4.canB_vac]
    | succ r =>
      rw [minimalThreeNormCoefficient]
      have hi (j : Fin (r+1)) := ih j j.isLt (by omega)
      simp only [hi]
      apply (div_eq_iff (minimalThree_state_diagonal_ne_zero p hp hcop (r+1) (by omega) hr)).mpr
      have hh := minimalThree_actual_norm_recursion p hp hcop (r+1) hr
      linear_combination -hh

end VOA.InverseDS.VirasoroVerma
