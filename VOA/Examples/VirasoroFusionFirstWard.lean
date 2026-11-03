/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFusionKernel
import VOA.Examples.VirasoroBSAFirstDefect

/-!
# The first Ward equation for the constructed terminal state

Intertwining transports the actual primary defect. Scalar invertibility
forces that defect to vanish below resonance; the terminal scalar zero
then kills L1 of the terminal source. L2 and nonvanishing remain separate.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- The first positive operator lowers the supported field weight and
applies the actual first primary defect to its level sequence. -/
theorem wardFieldLift_first (c h b a : ℂ) (f : wardSequenceSpace c h) :
    wardP c h b (wardFieldLift c h a f)=
      wardFieldLift c h (a-1) (wardP1Map c h b a f) := by
  classical
  funext w
  change wardP1Map c h b (w-(-1)) (if w-(-1)=a then f else 0)=
    if w=a-1 then wardP1Map c h b a f else 0
  by_cases hw : w=a-1
  · subst w
    simp
  · have hw' : w-(-1)≠a := by intro he; apply hw; linear_combination he
    simp only [if_neg hw',map_zero,if_neg hw]

/-- The evaluated source transports the first covariance defect exactly,
including the shift by minus one of the input field weight. -/
theorem wardSourceAt_first_defect (c h b t : ℂ) (N : ℕ) (ht : t≠0) (hN : 2≤N)
    (f : wardSequenceSpace c h) :
    wardP1Map c h b (vermaBSAWeight N t+(N:ℂ))
      (wardSourceAt c h b t (vermaBSAWeight N t) N f)=
    wardSourceAt c h b t (vermaBSAWeight N t-1) N
      (wardP1Map c h b (vermaBSAWeight N t) f) := by
  have hh := wardBSASourceOperator_L1_defect c h b t N ht hN
    (wardFieldLift c h (vermaBSAWeight N t) f)
    (wardFieldLift_weight c h (vermaBSAWeight N t) f)
  rw [wardFieldLift_first] at hh
  have he := congrArg (fun F : ℂ → wardSequenceSpace c h =>
    F (vermaBSAWeight N t+(N:ℂ)-1)) hh
  have ha : vermaBSAWeight N t+(N:ℂ)-1=(vermaBSAWeight N t-1)+(N:ℂ) := by ring
  change wardP1Map c h b ((vermaBSAWeight N t+(N:ℂ)-1)-(-1))
    (wardBSASourceOperator c h b t N N (wardFieldLift c h (vermaBSAWeight N t) f)
      ((vermaBSAWeight N t+(N:ℂ)-1)-(-1)))=
    wardBSASourceOperator c h b t N N
      (wardFieldLift c h (vermaBSAWeight N t-1) (wardP1Map c h b (vermaBSAWeight N t) f))
      (vermaBSAWeight N t+(N:ℂ)-1) at he
  simp only [sub_neg_eq_add,sub_add_cancel] at he
  rw [ha] at he
  exact he

/-- Lowering the field weight by one shifts the diagonal's coefficient
index by one. This follows from the actual normalized scalar formula. -/
theorem wardSourceDiagonal_shift_one (h b t a : ℂ) (N r : ℕ) :
    wardBSASourceDiagonal h b t N r N ((a-1)+(N:ℂ))=
      wardBSASourceDiagonal h b t N (r+1) N (a+(N:ℂ)) := by
  rw [wardBSASourceDiagonal_normalized,wardBSASourceDiagonal_normalized]
  have he : h+(r:ℂ)-(a-1)=h+((r+1:ℕ):ℂ)-a := by push_cast; ring
  rw [he]

/-- Invertible diagonal coefficients force a sequence to vanish wherever
its triangular image vanishes, including coefficient zero. -/
theorem ward_zero_of_source_zero (c h : ℂ)
    (T : Module.End ℂ (wardSequenceSpace c h)) (d : ℕ → ℂ) (R : ℕ)
    (hdiag : ∀ (r : ℕ) (f : wardSequenceSpace c h),
      (∀ j<r, f.val j=0) → (T f).val r=d r • f.val r)
    (hd : ∀ r<R, d r≠0) (f : wardSequenceSpace c h)
    (hf : ∀ r<R, (T f).val r=0) : ∀ r<R, f.val r=0 := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    have hh := hdiag r f (fun j hj => ih j hj (by omega))
    rw [hf r hr] at hh
    exact (smul_eq_zero.mp hh.symm).resolve_left (hd r hr)

/-- The constructed input satisfies its first primary equation below the
last preterminal index. This is derived from its source equation. -/
theorem fusionKernelSequence_first_below (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N) :
    ∀ r<A*(N-1)-1,
      (wardP1Map (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
        (fusionKacWeight (A:ℂ) 0 t) (vermaBSAWeight N t)
        (fusionKernelSequence A N t him hN)).val r=0 := by
  have ht : t≠0 := by intro hz; apply him; simp [hz]
  apply ward_zero_of_source_zero _ _
    (wardSourceAt (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
      (fusionKacWeight (A:ℂ) 0 t) t (vermaBSAWeight N t-1) N)
    (fun r => wardBSASourceDiagonal (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
      (fusionKacWeight (A:ℂ) 0 t) t N r N ((vermaBSAWeight N t-1)+(N:ℂ)))
  · exact fun r f hf => wardSourceAt_diagonal _ _ _ _ _ _ r f hf
  · intro r hr
    rw [wardSourceDiagonal_shift_one]
    exact wardBSASourceDiagonal_nonreal_intermediate A N (r+1) t him (by omega) (by omega) (by omega)
  · intro r hr
    rw [← wardSourceAt_first_defect _ _ _ t N ht hN]
    change vermaMode _ _ 1 _-(_ : ℂ) • _=0
    rw [fusionKernelSequence_source_below A N t him hN (r+1) (by omega),
      fusionKernelSequence_source_below A N t him hN r (by omega),map_zero,smul_zero,sub_zero]

/-- The constructed terminal state is killed by the actual L1 operator.
No primary-seed assumption or terminal nonvanishing assumption is used. -/
theorem fusionTerminalState_L1 (A N : ℕ) (t : ℂ) (him : t.im≠0)
    (hA : 0<A) (hN : 2≤N) :
    vermaMode (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t) 1
      (fusionTerminalState A N t him hN).val=0 := by
  have ht : t≠0 := by intro hz; apply him; simp [hz]
  have hR : 0<A*(N-1) := Nat.mul_pos hA (by omega)
  have hh := wardSourceAt_first_defect (vermaBSACharge t)
    (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t) (fusionKacWeight (A:ℂ) 0 t)
    t N ht hN (fusionKernelSequence A N t him hN)
  have he := congrArg (fun f : wardSequenceSpace (vermaBSACharge t)
    (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t) => f.val (A*(N-1)-1)) hh
  dsimp only at he
  rw [wardSourceAt_diagonal _ _ _ _ _ _ _ _
    (fusionKernelSequence_first_below A N t him hN),wardSourceDiagonal_shift_one,
    show A*(N-1)-1+1=A*(N-1) by omega,
    wardBSASourceDiagonal_label_terminal A N t hN ht,zero_smul] at he
  change vermaMode _ _ 1 _-(_ : ℂ) • _=0 at he
  rw [fusionKernelSequence_source_below A N t him hN (A*(N-1)-1) (by omega),
    smul_zero,sub_zero] at he
  simpa only [fusionTerminalState,show A*(N-1)-1+1=A*(N-1) by omega] using he
end VOA.InverseDS.VirasoroVerma
