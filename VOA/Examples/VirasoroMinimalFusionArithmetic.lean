/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFusionThreeMinimalArithmetic
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# Fusion nonresonance at prime-power minimal-model labels

At t=q/p the intermediate resonance condition becomes
p*i*(i+1)=q*(i+r). Coprimality therefore forces q to divide i*(i+1).
If q is a prime power, consecutive integers force an endpoint index,
which cannot occur at a strictly intermediate level. This establishes
actual scalar invertibility, not nonvanishing of a terminal vector.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- The general minimal-model parameter q/p is nonzero for positive labels. -/
theorem minimal_fusion_parameter_ne_zero (p q : ℕ) (hp : 0<p) (hq : 0<q) :
    (q:ℂ)/(p:ℂ)≠0 :=
  div_ne_zero (by exact_mod_cast Nat.ne_of_gt hq) (by exact_mod_cast Nat.ne_of_gt hp)

/-- The general outgoing Kac weight is zero at the vacuum specialization.
This identifies the actual highest-weight module in which fusion is performed. -/
theorem minimal_fusion_weight_zero (p q : ℕ) (hp : 1≤p) (hq : 0<q) :
    fusionKacWeight ((p-1:ℕ):ℂ) ((q:ℂ)-1) ((q:ℂ)/(p:ℂ))=0 := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
  have hq0 : (q:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hq
  have hs : ((p-1:ℕ):ℂ)=(p:ℂ)-1 := by exact_mod_cast Int.ofNat_sub hp
  unfold fusionKacWeight
  rw [hs]
  field_simp
  ring

/-- The rational fusion charge is exactly the package's minimal-model charge. -/
theorem minimal_fusion_charge (p q : ℕ) (hp : 0<p) (hq : 0<q) :
    vermaBSACharge ((q:ℂ)/(p:ℂ))=minimalCentralCharge p q := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hp
  have hq0 : (q:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hq
  unfold vermaBSACharge minimalCentralCharge
  push_cast
  field_simp
  ring

/-- Clearing the nonzero denominator turns every rational resonance into
an exact equation of natural numbers, with no subtraction underflow. -/
theorem minimal_fusion_resonance_iff (p q i r : ℕ) (hp : 1≤p) :
    (((i:ℂ)*((p-1:ℕ):ℂ)-(r:ℂ))*((q:ℂ)/(p:ℂ))=
      (i:ℂ)*((q:ℂ)-1-(i:ℂ))) ↔ p*i*(i+1)=q*(i+r) := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
  have hs : ((p-1:ℕ):ℂ)=(p:ℂ)-1 := by exact_mod_cast Int.ofNat_sub hp
  rw [hs]
  constructor
  · intro he
    have hc : (p:ℂ)*(i:ℂ)*((i:ℂ)+1)=(q:ℂ)*((i:ℂ)+(r:ℂ)) := by
      field_simp at he
      linear_combination he
    exact_mod_cast hc
  · intro he
    have hc : (p:ℂ)*(i:ℂ)*((i:ℂ)+1)=(q:ℂ)*((i:ℂ)+(r:ℂ)) := by exact_mod_cast he
    field_simp
    linear_combination hc

/-- At every rational minimal-model parameter the actual diagonal vanishes
exactly when the finite integer resonance equation has a solution. This
classification also exposes additional interior zeros for composite labels. -/
theorem minimal_fusion_diagonal_zero_iff (p q r : ℕ) (hp : 1≤p) (hq : 2≤q) :
    wardBSASourceDiagonal (fusionKacWeight ((p-1:ℕ):ℂ) ((q:ℂ)-1) ((q:ℂ)/(p:ℂ)))
      (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((q:ℂ)/(p:ℂ))) ((q:ℂ)/(p:ℂ)) q r q
      (vermaBSAWeight q ((q:ℂ)/(p:ℂ))+(q:ℂ))=0 ↔
      ∃ i : ℕ, i<q ∧ p*i*(i+1)=q*(i+r) := by
  rw [wardBSASourceDiagonal_label_zero_iff (p-1) q r _ hq
    (minimal_fusion_parameter_ne_zero p q (by omega) (by omega))]
  simp only [minimal_fusion_resonance_iff p q _ r hp]

/-- An actual interior resonance occurs at level three for labels (5,6),
well before their singular level twenty. Coprimality alone therefore does
not justify the direct coefficient divisions in this label orientation. -/
theorem minimal_fusion_five_six_interior_zero :
    wardBSASourceDiagonal (fusionKacWeight (4:ℂ) ((6:ℂ)-1) ((6:ℂ)/5))
      (fusionKacWeight (4:ℂ) 0 ((6:ℂ)/5)) ((6:ℂ)/5) 6 3 6
      (vermaBSAWeight 6 ((6:ℂ)/5)+6)=0 := by
  apply (minimal_fusion_diagonal_zero_iff 5 6 3 (by omega) (by omega)).mpr
  exact ⟨2,by omega,by norm_num⟩

/-- Coprime labels force the second label to divide the product of two
consecutive resonance indices. This is the precise arithmetic restriction;
for labels with several prime factors it need not force an endpoint. -/
theorem minimal_fusion_resonance_dvd (p q i r : ℕ) (hp : 1≤p)
    (hcop : Nat.Coprime p q)
    (he : ((i:ℂ)*((p-1:ℕ):ℂ)-(r:ℂ))*((q:ℂ)/(p:ℂ))=
      (i:ℂ)*((q:ℂ)-1-(i:ℂ))) : q∣i*(i+1) := by
  have hh := (minimal_fusion_resonance_iff p q i r hp).mp he
  have hd : q∣p*(i*(i+1)) := by rw [← mul_assoc,hh]; exact dvd_mul_right _ _
  exact hcop.symm.dvd_of_dvd_mul_left hd

/-- At a prime-power second label every strictly interior fusion factor
is nonzero. Consecutive indices cannot share the label's prime factors,
so a resonance would have to be initial or terminal. -/
theorem minimal_fusion_nonresonant_prime_power (p q i r : ℕ)
    (hp : 2≤p) (hq : 2≤q) (hcop : Nat.Coprime p q) (hpow : IsPrimePow q)
    (hi : i<q) (hr : 0<r) (hrN : r<(p-1)*(q-1)) :
    ((i:ℂ)*((p-1:ℕ):ℂ)-(r:ℂ))*((q:ℂ)/(p:ℂ))≠
      (i:ℂ)*((q:ℂ)-1-(i:ℂ)) := by
  intro he
  have hh := (minimal_fusion_resonance_iff p q i r (by omega)).mp he
  have hd := minimal_fusion_resonance_dvd p q i r (by omega) hcop he
  have hic : Nat.Coprime i (i+1) := by simp
  rcases hic.isPrimePow_dvd_mul hpow |>.mp hd with hl | hl
  · have hz : i=0 := Nat.eq_zero_of_dvd_of_lt hl hi
    subst i
    simp only [mul_zero,zero_add,zero_mul] at hh
    have hqr := Nat.mul_pos (by omega : 0<q) hr
    omega
  · have hle := Nat.le_of_dvd (by omega : 0 < i + 1) hl
    have hiq : i+1=q := by omega
    have heq : p*i=i+r := by
      rw [hiq,mul_comm q (i+r)] at hh
      exact Nat.eq_of_mul_eq_mul_right (by omega : 0<q) hh
    have hs : i=q-1 := by omega
    have hpr : r=(p-1)*(q-1) := by
      rw [hs] at heq
      have he' : p=(p-1)+1 := by omega
      rw [he',Nat.add_mul,one_mul] at heq
      omega
    omega

/-- Every actual source diagonal before the first singular level is
invertible at coprime minimal-model parameters whose second label is a
prime power. No statement about terminal survival is included. -/
theorem minimal_fusion_diagonal_prime_power (p q r : ℕ)
    (hp : 2≤p) (hq : 2≤q) (hcop : Nat.Coprime p q) (hpow : IsPrimePow q)
    (hr : 0<r) (hrN : r<(p-1)*(q-1)) :
    wardBSASourceDiagonal (fusionKacWeight ((p-1:ℕ):ℂ) ((q:ℂ)-1) ((q:ℂ)/(p:ℂ)))
      (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((q:ℂ)/(p:ℂ))) ((q:ℂ)/(p:ℂ)) q r q
      (vermaBSAWeight q ((q:ℂ)/(p:ℂ))+(q:ℂ))≠0 := by
  have ht := minimal_fusion_parameter_ne_zero p q (by omega) (by omega)
  apply wardBSASourceDiagonal_ne_zero_of_avoid_roots _ _ _ _
    (fusionLabelGauge ((p-1:ℕ):ℂ) ((q:ℂ)/(p:ℂ))) q r (by omega) ht
    (fusionLabelGauge_quadratic _ _ ht)
  intro i hi he
  have hh := (fusionLabel_root_iff ((p-1:ℕ):ℂ) ((q:ℂ)/(p:ℂ)) q i r ht).mp he
  exact minimal_fusion_nonresonant_prime_power p q i r hp hq hcop hpow hi hr hrN hh

end VOA.InverseDS.VirasoroVerma
