/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroThreeMovingSpecialization

/-!
# The actual moving-source norm identity

Away from the terminal resonance the next state exists and its Ward
identities determine its norm. Multiplication by the diagonal gives the
norm of the undivided source. At a terminal zero the source is singular,
so both sides vanish by the canonical radical. Thus the identity remains
valid without dividing by the terminal diagonal.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule VirDeformModes.NormalOrdering

/-- The actual moving coefficient after vacuum projection on its charge curve. -/
noncomputable def threeMovingVacuum (t : ℂ) (r : ℕ) : VirUniv (vermaBSACharge t) :=
  vacuumProjection _ (threeMovingState (vermaBSACharge t) t r)

section Ward
variable (t : ℂ) (ht : t≠0) (R : ℕ)
  (hd : ∀ r, 0<r → r<R → threeMovingDiagonal t r≠0)
include ht hd

/-- Ordinary nonresonance gives the first positive Ward equation for the
explicit moving states, not merely a chosen hypothetical primary sequence. -/
theorem threeMovingVacuum_L1 (r : ℕ) (hr : r+1<R) :
    Lop (vermaBSACharge t) 1 (threeMovingVacuum t (r+1))=(r:ℂ) • threeMovingVacuum t r := by
  have hh := nonresonant_first_below 0 (vermaBSAWeight 3 t) t 3 R ht (by omega)
    (threeMovingSequence (vermaBSACharge t) t) (threeMovingSequence_below t ht R hd)
    (fun j hj hjR => by simpa only [threeMovingDiagonal,threeStateDiagonal_eq,Nat.cast_ofNat] using hd j hj hjR) r (by omega)
  change vermaMode _ 0 1 _-(0-vermaBSAWeight 3 t+vermaBSAWeight 3 t+(r:ℂ)) • _=0 at hh
  have he : 0-vermaBSAWeight 3 t+vermaBSAWeight 3 t+(r:ℂ)=(r:ℂ) := by ring
  rw [he,sub_eq_zero] at hh
  simp only [threeMovingSequence] at hh
  unfold threeMovingVacuum
  rw [← vacuumProjection_mode,hh,map_smul]

/-- The second positive Ward equation includes and discharges its first
defect correction through the actual coefficient recursion. -/
theorem threeMovingVacuum_L2 (r : ℕ) (hr : r+2<R) :
    Lop (vermaBSACharge t) 2 (threeMovingVacuum t (r+2))=
      (vermaBSAWeight 3 t+(r:ℂ)) • threeMovingVacuum t r := by
  have hP := nonresonant_first_below 0 (vermaBSAWeight 3 t) t 3 R ht (by omega)
    (threeMovingSequence (vermaBSACharge t) t) (threeMovingSequence_below t ht R hd)
    (fun j hj hjR => by simpa only [threeMovingDiagonal,threeStateDiagonal_eq,Nat.cast_ofNat] using hd j hj hjR) r (by omega)
  have hQ := nonresonant_second_below 0 (vermaBSAWeight 3 t) t 3 R ht (by omega)
    (threeMovingSequence (vermaBSACharge t) t) (threeMovingSequence_below t ht R hd)
    (fun j hj hjR => by simpa only [threeMovingDiagonal,threeStateDiagonal_eq,Nat.cast_ofNat] using hd j hj hjR) r (by omega)
  change vermaMode _ 0 2 _-(0-vermaBSAWeight 3 t+2*vermaBSAWeight 3 t+(r:ℂ)) • _-
    (3:ℂ) • (wardP1Map _ 0 _ _ (threeMovingSequence _ t)).val r=0 at hQ
  rw [hP,smul_zero,sub_zero] at hQ
  have he : 0-vermaBSAWeight 3 t+2*vermaBSAWeight 3 t+(r:ℂ)=vermaBSAWeight 3 t+(r:ℂ) := by ring
  rw [he,sub_eq_zero] at hQ
  simp only [threeMovingSequence] at hQ
  unfold threeMovingVacuum
  rw [← vacuumProjection_mode,hQ,map_smul]

/-- All positive modes follow by the actual L1/L2 commutator. -/
theorem threeMovingVacuum_higher (m r : ℕ) (hr : r+m+2<R) :
    Lop (vermaBSACharge t) ((m:ℤ)+2) (threeMovingVacuum t (r+m+2))=
      (((m:ℂ)+1)*vermaBSAWeight 3 t+(r:ℂ)) • threeMovingVacuum t r := by
  induction m generalizing r with
  | zero => simpa using threeMovingVacuum_L2 t ht R hd r hr
  | succ m ih =>
    have hA := ih (r+1) (by omega)
    have hB := ih r (by omega)
    have h1 := threeMovingVacuum_L1 t ht R hd (r+m+2) (by omega)
    have h2 := threeMovingVacuum_L1 t ht R hd r (by omega)
    have hh := LeeYang.Lop_apply_comm (vermaBSACharge t) 1 ((m:ℤ)+2)
      (threeMovingVacuum t (r+(m+1)+2))
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
        Lop (vermaBSACharge t) (1+((m:ℤ)+2)) (threeMovingVacuum t ((r+m+2)+1)) = _ from
      eq_sub_of_add_eq' hh.symm) using 1
    · congr 2 <;> push_cast <;> ring
    · push_cast at hh ⊢
      simp only [smul_smul,← sub_smul]
      congr 1
      ring

/-- A positive mode between any two preterminal coefficients has its
ordinary primary multiplier, on the concrete moving family. -/
theorem threeMovingVacuum_positive_to (r j : ℕ) (hj : j<r) (hr : r<R) :
    Lop (vermaBSACharge t) ((r:ℤ)-(j:ℤ)) (threeMovingVacuum t r)=
      ((j:ℂ)+((r:ℂ)-(j:ℂ)-1)*vermaBSAWeight 3 t) • threeMovingVacuum t j := by
  by_cases he : r=j+1
  · subst r
    simpa using threeMovingVacuum_L1 t ht R hd j hr
  · have hk : r=j+(r-j-2)+2 := by omega
    have hh := threeMovingVacuum_higher t ht R hd (r-j-2) j (by omega)
    rw [← hk] at hh
    have hz : ((r-j-2:ℕ):ℤ)+2=(r:ℤ)-(j:ℤ) := by omega
    have hc : ((r-j-2:ℕ):ℂ)+1=(r:ℂ)-(j:ℂ)-1 := by
      have hi : ((r-j-2:ℕ):ℤ)+1=(r:ℤ)-(j:ℤ)-1 := by omega
      exact_mod_cast hi
    rw [hz,hc] at hh
    simpa only [add_comm] using hh
end Ward

/-- The actual norm-weighted Ward sum; every term involves an earlier
coefficient and has no terminal denominator. -/
noncomputable def threeMovingNormSum (t : ℂ) (r : ℕ) : ℂ :=
  ∑ j : Fin r, threeMovingCoefficient t r j*
    ((j:ℂ)+((r:ℂ)-(j:ℂ)-1)*vermaBSAWeight 3 t)*
    (VirGram4.canB (vermaBSACharge t)).form (threeMovingVacuum t j) (threeMovingVacuum t j)

/-- Adjointness turns the actual triangular coefficient equation into
its canonical norm recurrence at every nonresonant output index. -/
theorem threeMoving_norm_equation (t : ℂ) (ht : t≠0) (r : ℕ) (hr : 0<r)
    (hd : ∀ j, 0<j → j≤r → threeMovingDiagonal t j≠0) :
    threeMovingDiagonal t r*(VirGram4.canB (vermaBSACharge t)).form
      (threeMovingVacuum t r) (threeMovingVacuum t r)+threeMovingNormSum t r=0 := by
  have hh := threeMovingState_equation (vermaBSACharge t) t r hr (hd r hr le_rfl)
  have he := congrArg (fun v => (VirGram4.canB (vermaBSACharge t)).form
    (vacuumProjection _ v) (threeMovingVacuum t r)) hh
  simp only [threeMovingSource,map_add,map_smul,map_sum,LinearMap.add_apply,
    LinearMap.sum_apply,LinearMap.smul_apply,map_zero,LinearMap.zero_apply,
    smul_eq_mul,vacuumProjection_mode] at he
  have hs (j : Fin r) : (VirGram4.canB (vermaBSACharge t)).form
      (Lop _ ((j:ℤ)-(r:ℤ)) (threeMovingVacuum t j)) (threeMovingVacuum t r)=
      ((j:ℂ)+((r:ℂ)-(j:ℂ)-1)*vermaBSAWeight 3 t)*
      (VirGram4.canB _).form (threeMovingVacuum t j) (threeMovingVacuum t j) := by
    rw [VirGram4.canB_adj,neg_sub,threeMovingVacuum_positive_to t ht (r+1)
      (fun k hk hkr => hd k hk (by omega)) r j j.isLt (by omega),map_smul,smul_eq_mul]
  change _+∑ j : Fin r, threeMovingCoefficient t r j*
    (VirGram4.canB _).form (Lop _ ((j:ℤ)-(r:ℤ)) (threeMovingVacuum t j))
      (threeMovingVacuum t r)=0 at he
  simp only [hs] at he
  simpa only [threeMovingNormSum,mul_assoc] using he

/-- Off resonance, multiplying the actual norm recurrence by its diagonal
gives the norm of the undivided source, without guessing a norm product. -/
theorem threeMoving_source_norm_nonresonant (t : ℂ) (ht : t≠0) (r : ℕ) (hr : 0<r)
    (hd : ∀ j, 0<j → j≤r → threeMovingDiagonal t j≠0) :
    (VirGram4.canB (vermaBSACharge t)).form
      (vacuumProjection _ (threeMovingSource (vermaBSACharge t) t r))
      (vacuumProjection _ (threeMovingSource (vermaBSACharge t) t r))=
      -threeMovingDiagonal t r*threeMovingNormSum t r := by
  have he := threeMovingState_equation (vermaBSACharge t) t r hr (hd r hr le_rfl)
  have hs : threeMovingSource (vermaBSACharge t) t r=
      -threeMovingDiagonal t r • threeMovingState (vermaBSACharge t) t r := by
    simpa only [neg_smul] using (eq_neg_of_add_eq_zero_right he)
  rw [hs]
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  have hh := threeMoving_norm_equation t ht r hr hd
  change _*( _*(VirGram4.canB _).form (threeMovingVacuum t r) (threeMovingVacuum t r))=_
  linear_combination threeMovingDiagonal t r*hh


/-- At a terminal diagonal zero, the undivided source is in the actual
canonical radical. Thus its norm vanishes, with no limiting argument. -/
theorem threeMoving_source_norm_resonant (t : ℂ) (ht : t≠0) (r : ℕ) (hr : 2≤r)
    (hd : ∀ j, 0<j → j<r → threeMovingDiagonal t j≠0)
    (hz : threeMovingDiagonal t r=0) :
    (VirGram4.canB (vermaBSACharge t)).form
      (vacuumProjection _ (threeMovingSource (vermaBSACharge t) t r))
      (vacuumProjection _ (threeMovingSource (vermaBSACharge t) t r))=0 := by
  have hz' : wardBSASourceDiagonal 0 (vermaBSAWeight 3 t) t 3 r 3 (vermaBSAWeight 3 t+3)=0 := by
    simpa only [threeMovingDiagonal,threeStateDiagonal_eq,Nat.cast_ofNat] using hz
  have hd' (j : ℕ) (hj : 0<j) (hjr : j<r) :
      wardBSASourceDiagonal 0 (vermaBSAWeight 3 t) t 3 j 3 (vermaBSAWeight 3 t+3)≠0 := by
    simpa only [threeMovingDiagonal,threeStateDiagonal_eq,Nat.cast_ofNat] using hd j hj hjr
  have he : (wardSourceAt (vermaBSACharge t) 0 (vermaBSAWeight 3 t) t (vermaBSAWeight 3 t) 3
      (threeMovingSequence (vermaBSACharge t) t)).val r=threeMovingSource (vermaBSACharge t) t r := by
    rw [wardSourceAt_three_state_recursion]
    change threeMovingDiagonal t r • _+_= _
    rw [hz,zero_smul,zero_add]
    rfl
  have h1 := nonresonant_terminal_L1 0 (vermaBSAWeight 3 t) t 3 r ht (by omega)
    (threeMovingSequence (vermaBSACharge t) t) (threeMovingSequence_below t ht r hd) hd' (by omega) hz'
  have h2 := nonresonant_terminal_L2 0 (vermaBSAWeight 3 t) t 3 r ht (by omega)
    (threeMovingSequence (vermaBSACharge t) t) (threeMovingSequence_below t ht r hd) hd' hr hz'
  rw [he] at h1 h2
  apply canB_singular_right_zero _ (n:=r) (by omega) _
    (vacuumProjection_level _ r _ (threeMovingSource_level _ t r))
  · rw [← vacuumProjection_mode,h1,map_zero]
  · rw [← vacuumProjection_mode,h2,map_zero]

/-- The genuine moving norm identity holds even at a terminal resonance,
provided only earlier diagonals are nonzero. This is the ordinary norm
identity needed for the derivative comparison. -/
theorem threeMoving_source_norm (t : ℂ) (ht : t≠0) (r : ℕ) (hr : 2≤r)
    (hd : ∀ j, 0<j → j<r → threeMovingDiagonal t j≠0) :
    (VirGram4.canB (vermaBSACharge t)).form
      (vacuumProjection _ (threeMovingSource (vermaBSACharge t) t r))
      (vacuumProjection _ (threeMovingSource (vermaBSACharge t) t r))=
      -threeMovingDiagonal t r*threeMovingNormSum t r := by
  by_cases hz : threeMovingDiagonal t r=0
  · rw [threeMoving_source_norm_resonant t ht r hr hd hz,hz,neg_zero,zero_mul]
  · exact threeMoving_source_norm_nonresonant t ht r (by omega)
      (fun j hj hjr => by rcases lt_or_eq_of_le hjr with h | rfl; exact hd j hj h; exact hz)

/-- At the minimal parameter the actual norm-weighted sum is precisely
the proved nonzero normalized residual times t squared over four. -/
theorem threeMovingNormSum_at_minimal (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    threeMovingNormSum ((3:ℂ)/(p:ℂ)) ((p-1)*2)=
      (((3:ℂ)/(p:ℂ))^2/4)*minimalThreeNormResidual p := by
  have ht := minimal_three_parameter_ne_zero p (by omega)
  have hc : (((3:ℂ)/(p:ℂ))^2/4)*(vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+1)=
      ((3:ℂ)/(p:ℂ))/2 := by
    unfold vermaBSAWeight
    norm_num
    field_simp
    ring
  unfold threeMovingNormSum threeMovingCoefficient minimalThreeNormResidual
  rw [← mul_assoc,hc,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [threeStateCoefficient_ward_factor _ ht]
  unfold threeMovingVacuum
  rw [threeMovingState_at_minimal p hp hcop _ j j.isLt]
  change _*(VirGram4.canB _).form (minimalThreeVacuumCoefficient p hp hcop j)
    (minimalThreeVacuumCoefficient p hp hcop j)=_
  rw [← minimalThreeNormCoefficient_eq_norm p hp hcop j j.isLt]
  ring

end VOA.InverseDS.VirasoroVerma
