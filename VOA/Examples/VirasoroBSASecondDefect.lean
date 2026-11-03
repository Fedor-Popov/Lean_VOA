/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroBSAFirstDefect

/-!
# Transporting the second positive defect

The first defect contributes a finite error operator. Its recursion and
signs are derived from the actual commutators, not a primary assumption.
-/
namespace VOA.BSAWardDefect
open VOA.InverseDS.VirasoroVerma VOA.VirModule
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The error multiplying the first positive seed defect in the second
Ward equation. Only finite negative-word operators enter this recursion. -/
noncomputable def secondError {c h : ℂ} (A : System V c h) (t : ℂ) (N : ℕ) :
    ℕ → Module.End ℂ V
  | 0 => 0
  | r+1 => (-t/(((r:ℂ)+1)*((N:ℂ)-((r:ℂ)+1)))) •
      ((∑ j : Fin (r+1), A.mode ((j:ℤ)-((r:ℤ)+1))*secondError A t N j)+
        (3:ℂ) • op A t N r)
termination_by r => r

/-- The undivided second-defect error at a positive source level. -/
noncomputable def secondSourceError {c h : ℂ} (A : System V c h) (t : ℂ) (N r : ℕ) :
    Module.End ℂ V :=
  (∑ j : Fin r, A.mode ((j:ℤ)-(r:ℤ))*secondError A t N j)+(3:ℂ) • op A t N (r-1)

/-- The error recursion has the same intermediate denominator as the state. -/
theorem secondError_eq_source {c h : ℂ} (A : System V c h) (t : ℂ) (N r : ℕ) (hr : 0<r) :
    secondError A t N r=(-t/((r:ℂ)*((N:ℂ)-(r:ℂ)))) • secondSourceError A t N r := by
  cases r with
  | zero => omega
  | succ r => simp only [secondError,secondSourceError,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]

/-- At level one the commutator [L2,L-1]=3L1 produces the entire error. -/
theorem secondError_one {c h : ℂ} (A : System V c h) (t : ℂ) (N : ℕ) :
    secondError A t N 1=(-t/((N:ℂ)-1)) • ((3:ℂ) • LinearMap.id) := by
  simp [secondError,op]

/-- The second Ward equation at the first intermediate state, with both
seed defects retained explicitly. -/
theorem state_L2_one {c h : ℂ} (A : System V c h) (t : ℂ) (N : ℕ) :
    A.mode 2 (transportState A t N 1)=
      op A t N 1 (A.mode 2 A.seed)+secondError A t N 1 (A.mode 1 A.seed) := by
  rw [state_one,op_one,secondError_one,map_smul,A.comm 2 (-1) A.seed]
  norm_num

/-- Telescoping the second Ward equation leaves the source of the second
defect and an explicit negative-word operator applied to the first defect. -/
theorem source_L2_step {c h : ℂ} (A : System V c h) (t : ℂ) (N r : ℕ) (a b : ℂ)
    (h1 : A.mode 1 (transportState A t N (r+1)) =
      op A t N (r+1) (A.mode 1 A.seed)+((r:ℂ)+a) • transportState A t N r)
    (h2 : ∀ j : Fin r, A.mode 2 (transportState A t N (j+2)) =
      op A t N (j+2) (A.mode 2 A.seed)+secondError A t N (j+2) (A.mode 1 A.seed)+
      ((j:ℂ)+b) • transportState A t N j) :
    A.mode 2 (transportSource A t N (r+2)) =
      sourceOp A t N (r+2) (A.mode 2 A.seed)+
      secondSourceError A t N (r+2) (A.mode 1 A.seed)+
      ((r:ℂ)+4+b) • transportSource A t N r + (7*(r:ℂ)+4*h+3*a+c/2) • transportState A t N r := by
  classical
  have hcomm (j : Fin (r+2)) :
      A.mode 2 (A.mode ((j:ℤ)-((r:ℤ)+2)) (transportState A t N j)) =
        A.mode ((j:ℤ)-((r:ℤ)+2)) (A.mode 2 (transportState A t N j)) +
          ((r:ℂ)+4-(j:ℂ)) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j) +
          (if j.val=r then c/2 else 0) • transportState A t N j := by
    have hh := A.comm 2 ((j:ℤ)-((r:ℤ)+2)) (transportState A t N j)
    have he : (2:ℤ)+((j:ℤ)-((r:ℤ)+2)) = (j:ℤ)-(r:ℤ) := by ring
    rw [he] at hh
    have hi : ((j:ℤ)-(r:ℤ)=0) ↔ j.val=r := by omega
    simp only [hi] at hh
    split_ifs at hh ⊢ <;> try simp only [zero_smul] at hh ⊢
    all_goals convert hh using 1 <;> push_cast <;> ring
  have hA : (∑ j : Fin (r+2), A.mode ((j:ℤ)-((r:ℤ)+2)) (A.mode 2 (transportState A t N j))) =
      sourceOp A t N (r+2) (A.mode 2 A.seed)+
      (∑ j : Fin (r+2), A.mode ((j:ℤ)-((r:ℤ)+2)) (secondError A t N j (A.mode 1 A.seed)))+
      ∑ j : Fin r, ((j:ℂ)+b) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j) := by
    simp only [sourceOp,LinearMap.sum_apply,Module.End.mul_apply,Nat.cast_add,Nat.cast_ofNat]
    rw [← Finset.sum_add_distrib]
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.cast_zero,transportState_zero,op,secondError,
      LinearMap.id_apply,LinearMap.zero_apply,map_zero,add_zero]
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Fin.val_succ,Nat.cast_zero,Nat.zero_add,state_L2_one,map_add]
    have hh : (∑ j : Fin r,
        A.mode (((j.val+1+1:ℕ):ℤ)-((r:ℤ)+2))
          (A.mode 2 (transportState A t N (j.val+1+1)))) =
        (∑ j : Fin r,
          (A.mode (((j.val+1+1:ℕ):ℤ)-((r:ℤ)+2)) (op A t N (j.val+1+1) (A.mode 2 A.seed))+
          A.mode (((j.val+1+1:ℕ):ℤ)-((r:ℤ)+2)) (secondError A t N (j.val+1+1) (A.mode 1 A.seed))))+
        ∑ j : Fin r, ((j:ℂ)+b) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [show j.val+1+1=j.val+2 by omega,h2 j,map_add,map_add,map_smul]
      congr 2
      push_cast
      ring
    rw [hh]
    simp only [show op A t N 0=LinearMap.id by rw [op],
      show secondError A t N 0=0 by rw [secondError],
      LinearMap.id_apply,LinearMap.zero_apply,map_zero,add_zero]
    module
  have hB : (∑ j : Fin (r+2), ((r:ℂ)+4-(j:ℂ)) •
      A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j)) =
      (∑ j : Fin r, ((r:ℂ)+4-(j:ℂ)) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j)) +
        (3:ℂ) • op A t N (r+1) (A.mode 1 A.seed)+
        (7*(r:ℂ)+4*h+3*a) • transportState A t N r := by
    rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,Nat.cast_add,Nat.cast_one,sub_self,
      show (r:ℤ)+1-(r:ℤ)=1 by ring,h1,transportState_L0 A t N r,smul_smul]
    push_cast
    module
  have hC : (∑ j : Fin (r+2), (if j.val=r then c/2 else 0) • transportState A t N j) =
      (c/2) • transportState A t N r := by
    rw [Finset.sum_eq_single (⟨r,by omega⟩ : Fin (r+2))]
    · simp
    · intro j hj hjr
      have he : j.val ≠ r := fun he => hjr (Fin.ext he)
      simp [he]
    · simp
  have hs : (∑ j : Fin r, ((j:ℂ)+b) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j))+
      (∑ j : Fin r, ((r:ℂ)+4-(j:ℂ)) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j)) =
      ((r:ℂ)+4+b) • transportSource A t N r := by
    rw [← Finset.sum_add_distrib]
    simp only [transportSource,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← add_smul]
    congr 1
    ring
  simp only [transportSource,Nat.cast_add,Nat.cast_ofNat,map_sum,hcomm,Finset.sum_add_distrib]
  rw [hA,hB,hC]
  have hE : secondSourceError A t N (r+2) (A.mode 1 A.seed)=
      (∑ j : Fin (r+2), A.mode ((j:ℤ)-((r:ℤ)+2)) (secondError A t N j (A.mode 1 A.seed)))+
      (3:ℂ) • op A t N (r+1) (A.mode 1 A.seed) := by
    simp [secondSourceError,Module.End.mul_apply]
  rw [hE]
  have hsA := eq_sub_iff_add_eq.mpr hs
  simp only [transportSource] at hsA
  rw [hsA]
  module
/-- All intermediate second Ward equations retain both positive seed
images, with the recursively constructed error multiplying the first. -/
theorem state_L2 (t : ℂ) (N r : ℕ)
    (A : System V (vermaBSACharge t) (vermaBSAWeight N t)) (ht : t≠0) (hr : r+2<N) :
    A.mode 2 (transportState A t N (r+2))=
      op A t N (r+2) (A.mode 2 A.seed)+secondError A t N (r+2) (A.mode 1 A.seed)+
      ((r:ℂ)+vermaBSAOffset2 N t) • transportState A t N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    have hs := source_L2_step A t N r (vermaBSAOffset1 N t) (vermaBSAOffset2 N t)
      (state_L1 t N r A ht (by omega)) (fun j => ih j j.isLt (by omega))
    rw [transportState_eq_source A t N (r+2) (by omega),map_smul,hs,
      op_eq_source A t N (r+2) (by omega),secondError_eq_source A t N (r+2) (by omega)]
    simp only [LinearMap.smul_apply,smul_add,smul_smul,add_assoc]
    congr 1
    congr 1
    have hd' := bsa_denominator_ne_zero N (r+2) (by omega) hr
    by_cases hz : r=0
    · subst r
      simp only [transportSource,Fin.sum_univ_zero,smul_zero,zero_add,smul_smul,
        Nat.cast_zero,Nat.cast_ofNat]
      congr 1
      unfold vermaBSACharge vermaBSAWeight vermaBSAOffset1 vermaBSAOffset2
      norm_num at hd' ⊢
      field_simp [ht,hd']
      <;> ring
    · rw [transportState_eq_source A t N r (by omega)]
      simp only [smul_smul,← add_smul]
      congr 1
      have hd := bsa_denominator_ne_zero N r (by omega) (by omega)
      unfold vermaBSACharge vermaBSAWeight vermaBSAOffset1 vermaBSAOffset2
      push_cast at hd' ⊢
      field_simp [ht,hd,hd',(mul_ne_zero_iff.mp hd).1,(mul_ne_zero_iff.mp hd).2,
        (mul_ne_zero_iff.mp hd').1,(mul_ne_zero_iff.mp hd').2]
      <;> ring

/-- The terminal second Ward identity, with the entire first-defect error
retained. No primary equation is assumed of the input. -/
theorem source_L2_terminal (t : ℂ) (N : ℕ)
    (A : System V (vermaBSACharge t) (vermaBSAWeight N t)) (ht : t≠0) (hN : 3≤N) :
    A.mode 2 (transportSource A t N N)=
      sourceOp A t N N (A.mode 2 A.seed)+secondSourceError A t N N (A.mode 1 A.seed) := by
  obtain ⟨r,hr⟩ : ∃ r : ℕ, N=r+2 := ⟨N-2,by omega⟩
  subst N
  rw [source_L2_step A t (r+2) r (vermaBSAOffset1 (r+2) t)
      (vermaBSAOffset2 (r+2) t)
      (state_L1 t (r+2) r A ht (by omega))
      (fun j => state_L2 t (r+2) j A ht (by omega)),
    transportState_eq_source A t (r+2) r (by omega),smul_smul,add_assoc,add_assoc,← add_smul]
  have hd : (r:ℂ)≠0 := by exact_mod_cast (show r≠0 by omega)
  have he : ((r:ℂ)+4+vermaBSAOffset2 (r+2) t)+
      (7*(r:ℂ)+4*vermaBSAWeight (r+2) t+3*vermaBSAOffset1 (r+2) t+vermaBSACharge t/2)*
      (-t/((r:ℂ)*(((r+2:ℕ):ℂ)-(r:ℂ))))=0 := by
    unfold vermaBSAOffset1 vermaBSAOffset2 vermaBSAWeight vermaBSACharge
    push_cast
    field_simp
    <;> ring
  rw [he,zero_smul,add_zero]
end VOA.BSAWardDefect


namespace VOA.InverseDS.VirasoroVerma

/-- The second-defect correction as an actual endomorphism on field-weight
indexed Verma sequences. Its definition does not choose a seed. -/
noncomputable def wardSecondError (c h b t : ℂ) (N : ℕ) :
    ℕ → Module.End ℂ (ℂ → wardSequenceSpace c h)
  | 0 => 0
  | r+1 => (-t/(((r:ℂ)+1)*((N:ℂ)-((r:ℂ)+1)))) •
      ((∑ j : Fin (r+1), wardTransportMode c h b ((j:ℤ)-((r:ℤ)+1))*wardSecondError c h b t N j)+
        (3:ℂ) • wardBSAOperator c h b t N r)
termination_by r => r

/-- The undivided actual error multiplying the first primary defect. -/
noncomputable def wardSecondSourceError (c h b t : ℂ) (N r : ℕ) :
    Module.End ℂ (ℂ → wardSequenceSpace c h) :=
  (∑ j : Fin r, wardTransportMode c h b ((j:ℤ)-(r:ℤ))*wardSecondError c h b t N j)+
    (3:ℂ) • wardBSAOperator c h b t N (r-1)

/-- The abstract error recursion agrees with the actual endomorphism,
independently of which weight-compatible seed packages the commutators. -/
theorem wardDefectSystem_secondError (c h b a t : ℂ) (N r : ℕ)
    (f : ℂ → wardSequenceSpace c h) (h0 : wardWeight c h f=a • f) :
    BSAWardDefect.secondError (wardDefectSystem c h b a f h0) t N r=
      wardSecondError c h b t N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [BSAWardDefect.secondError,wardSecondError]
    | succ r =>
      simp only [BSAWardDefect.secondError,wardSecondError,wardDefectSystem_op]
      congr 2
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j (by omega)]
      rfl

/-- The source-error identification discharges all abstract-system data. -/
theorem wardDefectSystem_secondSourceError (c h b a t : ℂ) (N r : ℕ)
    (f : ℂ → wardSequenceSpace c h) (h0 : wardWeight c h f=a • f) :
    BSAWardDefect.secondSourceError (wardDefectSystem c h b a f h0) t N r=
      wardSecondSourceError c h b t N r := by
  simp only [BSAWardDefect.secondSourceError,wardSecondSourceError,
    wardDefectSystem_secondError,wardDefectSystem_op]
  rfl

/-- The actual second Ward identity retains the first-defect error. It
requires only the seed weight, not either primary covariance equation. -/
theorem wardBSASourceOperator_L2_defect (h b t : ℂ) (N : ℕ)
    (ht : t≠0) (hN : 3≤N) (f : ℂ → wardSequenceSpace (vermaBSACharge t) h)
    (h0 : wardWeight (vermaBSACharge t) h f=vermaBSAWeight N t • f) :
    wardQ (vermaBSACharge t) h b (wardBSASourceOperator (vermaBSACharge t) h b t N N f)=
      wardBSASourceOperator (vermaBSACharge t) h b t N N (wardQ (vermaBSACharge t) h b f)+
      wardSecondSourceError (vermaBSACharge t) h b t N N (wardP (vermaBSACharge t) h b f) := by
  have hh := BSAWardDefect.source_L2_terminal t N
    (wardDefectSystem (vermaBSACharge t) h b (vermaBSAWeight N t) f h0) ht hN
  rw [wardDefectSystem_source,wardDefectSystem_sourceOp,wardDefectSystem_secondSourceError] at hh
  exact hh

/-- Every error operator preserves an initial segment of zero coefficients.
Its extra term is another negative-word operator and has the same property. -/
theorem wardSecondError_below (c h b t : ℂ) (N n : ℕ)
    (f : ℂ → wardSequenceSpace c h) (r : ℕ) (hf : WardBelow f r) :
    WardBelow (wardSecondError c h b t N n f) r := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => intro a j hj; simp [wardSecondError]
    | succ n =>
      intro a j hj
      simp only [wardSecondError,LinearMap.smul_apply,LinearMap.add_apply,
        LinearMap.sum_apply,Module.End.mul_apply,Pi.smul_apply,Pi.add_apply,
        Submodule.coe_smul,Submodule.coe_add,Submodule.coe_sum,Finset.sum_apply]
      have he (i : Fin (n+1)) :
          (wardTransportMode c h b ((i:ℤ)-((n:ℤ)+1))
            (wardSecondError c h b t N i f) a).val j=0 :=
        wardTransportMode_below c h b _ (by omega) _ r (ih i (by omega)) a j hj
      have ho := wardBSAOperator_below c h b t N n f r hf a j hj
      simp only [he,ho,Finset.sum_const_zero,smul_zero,add_zero]

/-- The undivided terminal error also preserves earlier coefficient zeros. -/
theorem wardSecondSourceError_below (c h b t : ℂ) (N n : ℕ)
    (f : ℂ → wardSequenceSpace c h) (r : ℕ) (hf : WardBelow f r) :
    WardBelow (wardSecondSourceError c h b t N n f) r := by
  intro a j hj
  simp only [wardSecondSourceError,LinearMap.add_apply,LinearMap.sum_apply,
    LinearMap.smul_apply,Module.End.mul_apply,Pi.smul_apply,Pi.add_apply,
    Submodule.coe_smul,Submodule.coe_add,Submodule.coe_sum,Finset.sum_apply]
  have he (i : Fin n) :
      (wardTransportMode c h b ((i:ℤ)-(n:ℤ))
        (wardSecondError c h b t N i f) a).val j=0 :=
    wardTransportMode_below c h b _ (by omega) _ r (wardSecondError_below c h b t N i f r hf) a j hj
  have ho := wardBSAOperator_below c h b t N (n-1) f r hf a j hj
  simp only [he,ho,Finset.sum_const_zero,smul_zero,add_zero]
end VOA.InverseDS.VirasoroVerma
