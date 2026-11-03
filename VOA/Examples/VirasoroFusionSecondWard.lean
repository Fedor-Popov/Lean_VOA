/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFusionFirstWard
import VOA.Examples.VirasoroBSASecondDefect

/-!
# The second Ward equation for the actual fusion terminal state

The first-defect error vanishes before resonance. The second diagonal
shift then proves the actual L2 equation. Nonvanishing remains separate.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- The second positive operator lowers supported field weight by two and
applies the actual second primary defect to the level sequence. -/
theorem wardFieldLift_second (c h b a : ℂ) (f : wardSequenceSpace c h) :
    wardQ c h b (wardFieldLift c h a f)=
      wardFieldLift c h (a-2) (wardP2Map c h b a f) := by
  classical
  funext w
  change wardP2Map c h b (w-(-2)) (if w-(-2)=a then f else 0)=
    if w=a-2 then wardP2Map c h b a f else 0
  by_cases hw : w=a-2
  · subst w; simp
  · have hw' : w-(-2)≠a := by intro he; apply hw; linear_combination he
    simp only [if_neg hw',map_zero,if_neg hw]

/-- The evaluated correction to the second source Ward equation. It is an
actual level sequence, obtained by transporting the first input defect. -/
noncomputable def wardSourceErrorAt (c h b t a : ℂ) (N : ℕ) (f : wardSequenceSpace c h) :
    wardSequenceSpace c h :=
  wardSecondSourceError c h b t N N
    (wardFieldLift c h (a-1) (wardP1Map c h b a f)) (a+(N:ℂ)-2)

/-- The evaluated second Ward equation includes the explicitly constructed
error, with both field shifts and all operator identifications discharged. -/
theorem wardSourceAt_second_defect (h b t : ℂ) (N : ℕ) (ht : t≠0) (hN : 3≤N)
    (f : wardSequenceSpace (vermaBSACharge t) h) :
    wardP2Map (vermaBSACharge t) h b (vermaBSAWeight N t+(N:ℂ))
      (wardSourceAt (vermaBSACharge t) h b t (vermaBSAWeight N t) N f)=
    wardSourceAt (vermaBSACharge t) h b t (vermaBSAWeight N t-2) N
      (wardP2Map (vermaBSACharge t) h b (vermaBSAWeight N t) f)+
    wardSourceErrorAt (vermaBSACharge t) h b t (vermaBSAWeight N t) N f := by
  have hh := wardBSASourceOperator_L2_defect h b t N ht hN
    (wardFieldLift (vermaBSACharge t) h (vermaBSAWeight N t) f)
    (wardFieldLift_weight (vermaBSACharge t) h (vermaBSAWeight N t) f)
  rw [wardFieldLift_first,wardFieldLift_second] at hh
  have he := congrArg (fun F : ℂ → wardSequenceSpace (vermaBSACharge t) h =>
    F (vermaBSAWeight N t+(N:ℂ)-2)) hh
  change wardP2Map (vermaBSACharge t) h b ((vermaBSAWeight N t+(N:ℂ)-2)-(-2))
    (wardBSASourceOperator (vermaBSACharge t) h b t N N
      (wardFieldLift (vermaBSACharge t) h (vermaBSAWeight N t) f)
      ((vermaBSAWeight N t+(N:ℂ)-2)-(-2)))=
    wardBSASourceOperator (vermaBSACharge t) h b t N N
      (wardFieldLift (vermaBSACharge t) h (vermaBSAWeight N t-2)
        (wardP2Map (vermaBSACharge t) h b (vermaBSAWeight N t) f))
      (vermaBSAWeight N t+(N:ℂ)-2)+
    wardSourceErrorAt (vermaBSACharge t) h b t (vermaBSAWeight N t) N f at he
  simp only [sub_neg_eq_add,sub_add_cancel] at he
  have ha : vermaBSAWeight N t+(N:ℂ)-2=(vermaBSAWeight N t-2)+(N:ℂ) := by ring
  rw [ha] at he
  exact he

/-- Lowering field weight by two shifts the actual diagonal index by two. -/
theorem wardSourceDiagonal_shift_two (h b t a : ℂ) (N r : ℕ) :
    wardBSASourceDiagonal h b t N r N ((a-2)+(N:ℂ))=
      wardBSASourceDiagonal h b t N (r+2) N (a+(N:ℂ)) := by
  rw [wardBSASourceDiagonal_normalized,wardBSASourceDiagonal_normalized]
  have he : h+(r:ℂ)-(a-2)=h+((r+2:ℕ):ℂ)-a := by push_cast; ring
  rw [he]

/-- The first input defect vanishes far enough to kill the entire error
at every coefficient used in the second terminal Ward argument. -/
theorem fusionKernelSequence_error_below (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N) :
    ∀ r<A*(N-1)-1,
      (wardSourceErrorAt (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
        (fusionKacWeight (A:ℂ) 0 t) t (vermaBSAWeight N t) N
        (fusionKernelSequence A N t him hN)).val r=0 := by
  intro r hr
  exact wardSecondSourceError_below _ _ _ _ N N _ (A*(N-1)-1)
    (wardFieldLift_below _ _ _ _ _ (fusionKernelSequence_first_below A N t him hN)) _ r hr

/-- The constructed input satisfies the second primary defect equation
below R-2. This is forced by the actual source equation and first-defect bound. -/
theorem fusionKernelSequence_second_below (A N : ℕ) (t : ℂ) (him : t.im≠0)
    (hN : 3≤N) : ∀ r<A*(N-1)-2,
      (wardP2Map (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
        (fusionKacWeight (A:ℂ) 0 t) (vermaBSAWeight N t)
        (fusionKernelSequence A N t him (by omega))).val r=0 := by
  have ht : t≠0 := by intro hz; apply him; simp [hz]
  apply ward_zero_of_source_zero _ _
    (wardSourceAt (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
      (fusionKacWeight (A:ℂ) 0 t) t (vermaBSAWeight N t-2) N)
    (fun r => wardBSASourceDiagonal (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
      (fusionKacWeight (A:ℂ) 0 t) t N r N ((vermaBSAWeight N t-2)+(N:ℂ)))
  · exact fun r f hf => wardSourceAt_diagonal _ _ _ _ _ _ r f hf
  · intro r hr
    rw [wardSourceDiagonal_shift_two]
    exact wardBSASourceDiagonal_nonreal_intermediate A N (r+2) t him (by omega) (by omega) (by omega)
  · intro r hr
    have hh := wardSourceAt_second_defect (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
      (fusionKacWeight (A:ℂ) 0 t) t N ht hN (fusionKernelSequence A N t him (by omega))
    have he := congrArg (fun f : wardSequenceSpace (vermaBSACharge t)
      (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t) => f.val r) hh
    dsimp only at he
    simp only [Submodule.coe_add,Pi.add_apply] at he
    change vermaMode _ _ 2 _-(_ : ℂ) • _-(3:ℂ) • (vermaMode _ _ 1 _-(_ : ℂ) • _)=_ at he
    rw [fusionKernelSequence_source_below A N t him (by omega) (r+2) (by omega),
      fusionKernelSequence_source_below A N t him (by omega) (r+1) (by omega),
      fusionKernelSequence_source_below A N t him (by omega) r (by omega),
      fusionKernelSequence_error_below A N t him (by omega) r (by omega)] at he
    simpa only [map_zero,smul_zero,sub_zero,add_zero] using he.symm

/-- The ACTUAL terminal state is killed by L2, with no primary-seed or
terminal nonvanishing assumption. Together with L1 this gives singularity. -/
theorem fusionTerminalState_L2 (A N : ℕ) (t : ℂ) (him : t.im≠0)
    (hA : 0<A) (hN : 3≤N) :
    vermaMode (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t) 2
      (fusionTerminalState A N t him (by omega)).val=0 := by
  have ht : t≠0 := by intro hz; apply him; simp [hz]
  have hR : 2≤A*(N-1) := by
    have hh := Nat.mul_le_mul hA (show 2≤N-1 by omega)
    simpa using hh
  have hh := wardSourceAt_second_defect (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
    (fusionKacWeight (A:ℂ) 0 t) t N ht hN (fusionKernelSequence A N t him (by omega))
  have he := congrArg (fun f : wardSequenceSpace (vermaBSACharge t)
    (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t) => f.val (A*(N-1)-2)) hh
  dsimp only at he
  simp only [Submodule.coe_add,Pi.add_apply] at he
  rw [wardSourceAt_diagonal _ _ _ _ _ _ _ _
    (fusionKernelSequence_second_below A N t him hN),wardSourceDiagonal_shift_two,
    show A*(N-1)-2+2=A*(N-1) by omega,
    wardBSASourceDiagonal_label_terminal A N t (by omega) ht,zero_smul] at he
  change vermaMode _ _ 2 _-(_ : ℂ) • _-(3:ℂ) • (vermaMode _ _ 1 _-(_ : ℂ) • _)=_ at he
  rw [fusionKernelSequence_source_below A N t him (by omega) (A*(N-1)-2) (by omega),
    fusionKernelSequence_source_below A N t him (by omega) (A*(N-1)-2+1) (by omega),
    fusionKernelSequence_error_below A N t him (by omega) (A*(N-1)-2) (by omega)] at he
  simpa only [fusionTerminalState,show A*(N-1)-2+2=A*(N-1) by omega,
    smul_zero,map_zero,sub_zero,add_zero] using he
/-- Every positive Virasoro mode kills the constructed terminal state.
The state is allowed to be zero; nonvanishing is not part of this theorem. -/
theorem fusionTerminalState_positive (A N : ℕ) (t : ℂ) (him : t.im≠0)
    (hA : 0<A) (hN : 3≤N) :
    ∀ m : ℤ, 0<m →
      vermaMode (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t) m
        (fusionTerminalState A N t him (by omega)).val=0 :=
  verma_positive_zero_of_one_two _ _ _
    (fusionTerminalState_L1 A N t him hA (by omega)) (fusionTerminalState_L2 A N t him hA hN)

/-- The actual terminal vector has the expected outgoing highest weight
plus its relative level A(N-1), independently of whether it is zero. -/
theorem fusionTerminalState_weight (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N) :
    vermaMode (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t) 0
      (fusionTerminalState A N t him hN).val=
      (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t+((A*(N-1):ℕ):ℂ)) •
        (fusionTerminalState A N t him hN).val :=
  (verma_mem_level_iff_eigen _ _ _ _).mp (fusionTerminalState A N t him hN).property
end VOA.InverseDS.VirasoroVerma
