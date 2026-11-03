/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFusionThreeSpecialization
import VOA.Examples.VirasoroMinimalChargeArithmetic

/-!
# Nonresonance at the (p,3) vacuum parameters

At A=p-1 and t=3/p the (A,2) highest weight is zero. Coprimality with three
excludes every interior fusion resonance. Thus the ordinary vector formula
can in principle be constructed directly at these vacuum parameters rather
than recovered only as a limit. This module proves the arithmetic inputs;
it does not assert survival of a Verma state in the vacuum quotient or a
nonzero norm derivative.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- A minimal-model label coprime to three cannot be divisible by three. -/
theorem minimal_three_not_dvd (p : ℕ) (hcop : Nat.Coprime p 3) : ¬3∣p := by
  intro hd
  have he := Nat.eq_one_of_dvd_coprimes hcop hd (dvd_refl 3)
  omega

/-- The rational parameter 3/p is nonzero at positive p. -/
theorem minimal_three_parameter_ne_zero (p : ℕ) (hp : 0<p) : (3:ℂ)/(p:ℂ)≠0 :=
  div_ne_zero (by norm_num) (by exact_mod_cast (Nat.ne_of_gt hp))

/-- The (p-1,2) curve is a vacuum curve at t=3/p. This is the charge
specialization relevant to M(p,3), at relative level 2(p-1). -/
theorem fusionThree_minimal_weight_zero (p : ℕ) (hp : 2≤p) :
    fusionKacWeight ((p-1:ℕ):ℂ) 2 ((3:ℂ)/(p:ℂ))=0 := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
  have hs : ((p-1:ℕ):ℂ)=(p:ℂ)-1 := by exact_mod_cast Int.ofNat_sub (by omega : 1≤p)
  unfold fusionKacWeight
  rw [hs]
  field_simp
  ring

/-- The rational curve's central charge is precisely the package's
minimal-model central charge with labels p and three. -/
theorem fusionThree_minimal_charge (p : ℕ) (hp : 2≤p) :
    vermaBSACharge ((3:ℂ)/(p:ℂ))=minimalCentralCharge p 3 := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
  unfold vermaBSACharge minimalCentralCharge
  push_cast
  field_simp
  ring

/-- Coprimality excludes the middle resonance; the two endpoint factors
can vanish only at the initial or terminal coefficient. All interior
coefficients are therefore nonresonant even at this rational parameter. -/
theorem fusionThree_minimal_nonresonant (p r i : ℕ) (hp : 2≤p)
    (hcop : Nat.Coprime p 3) (hr : 0<r) (hrN : r<(p-1)*2) (hi : i<3) :
    ((i:ℂ)*((p-1:ℕ):ℂ)-(r:ℂ))*((3:ℂ)/(p:ℂ))≠(i:ℂ)*(2-(i:ℂ)) := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
  intro he
  have hh : (3:ℂ)*((i:ℂ)*((p-1:ℕ):ℂ)-(r:ℂ))=(i:ℂ)*(2-(i:ℂ))*(p:ℂ) := by
    field_simp at he
    linear_combination he
  interval_cases i
  · have hz : (r:ℂ)=0 := by linear_combination -hh/3
    have hz' : r=0 := by exact_mod_cast hz
    omega
  · have hn : 3*(p-1)=p+3*r := by
      exact_mod_cast (show (3:ℂ)*((p-1:ℕ):ℂ)=(p:ℂ)+3*(r:ℂ) by
        norm_num at hh
        linear_combination hh)
    have hm := congrArg (fun n : ℕ => n%3) hn
    simp at hm
    exact minimal_three_not_dvd p hcop (Nat.dvd_of_mod_eq_zero hm.symm)
  · have hn : r=2*(p-1) := by
      exact_mod_cast (show (r:ℂ)=2*((p-1:ℕ):ℂ) by
        norm_num at hh
        linear_combination -hh)
    omega

/-- Every actual source diagonal before the terminal level is invertible
at a coprime M(p,3) vacuum parameter. This is the concrete ordinary input
needed for direct triangular construction there. -/
theorem wardBSASourceDiagonal_minimal_three (p r : ℕ) (hp : 2≤p)
    (hcop : Nat.Coprime p 3) (hr : 0<r) (hrN : r<(p-1)*2) :
    wardBSASourceDiagonal (fusionKacWeight ((p-1:ℕ):ℂ) ((3:ℂ)-1) ((3:ℂ)/(p:ℂ)))
      (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ)) 3 r 3
      (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+3)≠0 := by
  have ht := minimal_three_parameter_ne_zero p (by omega)
  apply wardBSASourceDiagonal_ne_zero_of_avoid_roots _ _ _ _
    (fusionLabelGauge ((p-1:ℕ):ℂ) ((3:ℂ)/(p:ℂ))) 3 r (by omega) ht
    (fusionLabelGauge_quadratic _ _ ht)
  intro i hi he
  have hh := (fusionLabel_root_iff ((p-1:ℕ):ℂ) ((3:ℂ)/(p:ℂ)) 3 i r ht).mp he
  norm_num only [Nat.cast_ofNat,show (3:ℂ)-1=2 by norm_num] at hh
  exact fusionThree_minimal_nonresonant p r i hp hcop hr hrN hi hh

/-- The proposed even-level vacuum subdiagonal has no arithmetic zero
at coprime M(p,3) parameters. Identifying it with a vacuum coordinate is
still a separate operator theorem, not supplied by this calculation. -/
theorem fusionThree_vacuum_factor_ne_zero (p j : ℕ) (hp : 2≤p)
    (hcop : Nat.Coprime p 3) : (4:ℂ)-6*(j:ℂ)/(p:ℂ)≠0 := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
  intro hz
  have he : (2:ℂ)*(p:ℂ)=3*(j:ℂ) := by
    field_simp at hz
    linear_combination hz/2
  have hn : 2*p=3*j := by exact_mod_cast he
  have hd : 3∣2*p := hn ▸ dvd_mul_right 3 j
  have hc : Nat.Coprime 3 2 := by decide
  have hpdiv : 3∣p := hc.dvd_of_dvd_mul_left hd
  exact minimal_three_not_dvd p hcop hpdiv

/-- Direct triangular coefficient solutions exist at the rational M(p,3)
vacuum parameters, with the genuine highest vector at coefficient zero.
No limiting vector or nonreal-parameter assumption is used here. Positive
Ward equations and vacuum survival for this direct construction remain
separate obligations. -/
theorem exists_fusion_minimal_three_partial_kernel (p : ℕ) (hp : 2≤p)
    (hcop : Nat.Coprime p 3) :
    ∃ f : wardSequenceSpace (vermaBSACharge ((3:ℂ)/(p:ℂ)))
      (fusionKacWeight ((p-1:ℕ):ℂ) ((3:ℂ)-1) ((3:ℂ)/(p:ℂ))),
      f.val 0=highestVector (vermaBSACharge ((3:ℂ)/(p:ℂ)))
        (fusionKacWeight ((p-1:ℕ):ℂ) ((3:ℂ)-1) ((3:ℂ)/(p:ℂ))) ∧
      ∀ r<(p-1)*2,
        (wardSourceAt (vermaBSACharge ((3:ℂ)/(p:ℂ)))
          (fusionKacWeight ((p-1:ℕ):ℂ) ((3:ℂ)-1) ((3:ℂ)/(p:ℂ)))
          (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
          (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) 3 f).val r=0 := by
  have ht := minimal_three_parameter_ne_zero p (by omega)
  refine exists_ward_partial_kernel (vermaBSACharge ((3:ℂ)/(p:ℂ)))
    (fusionKacWeight ((p-1:ℕ):ℂ) ((3:ℂ)-1) ((3:ℂ)/(p:ℂ)))
    (wardSourceAt (vermaBSACharge ((3:ℂ)/(p:ℂ)))
      (fusionKacWeight ((p-1:ℕ):ℂ) ((3:ℂ)-1) ((3:ℂ)/(p:ℂ)))
      (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
      (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) 3)
    (fun r => wardBSASourceDiagonal (fusionKacWeight ((p-1:ℕ):ℂ) ((3:ℂ)-1) ((3:ℂ)/(p:ℂ)))
      (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ)) 3 r 3
        (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+3)) ((p-1)*2) ?_ ?_ ?_ ?_ (fusionLeadingState _ _)
  · exact fun r f hf => wardSourceAt_diagonal _ _ _ _ _ _ r f hf
  · exact fun r f hf => wardSourceAt_below _ _ _ _ _ _ r f hf
  · simpa using wardBSASourceDiagonal_label_initial (p-1) 3 ((3:ℂ)/(p:ℂ)) (by omega) ht
  · exact fun r hr hrN => wardBSASourceDiagonal_minimal_three p r hp hcop hr hrN

end VOA.InverseDS.VirasoroVerma
