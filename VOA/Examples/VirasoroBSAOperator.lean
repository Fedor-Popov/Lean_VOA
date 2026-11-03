/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroDescendantBSATransport

/-!
# The actual finite BSA operator without a primary-seed assumption

The recursive expression is an endomorphism before choosing any seed.
Evaluation on a primary seed agrees with the proved transport construction.
Every stage is triangular in the coefficient index. Solving its kernel
equation and proving a nonzero terminal fusion state remain open.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- The finite intermediate BSA expression as an actual endomorphism. No
seed, covariance equation or nonzero denominator assumption enters its definition. -/
noncomputable def wardBSAOperator (c h b t : ℂ) (N : ℕ) :
    ℕ → Module.End ℂ (ℂ → wardSequenceSpace c h)
  | 0 => LinearMap.id
  | r+1 => (-t/(((r:ℂ)+1)*((N:ℂ)-((r:ℂ)+1)))) •
      ∑ j : Fin (r+1), wardTransportMode c h b ((j:ℤ)-((r:ℤ)+1)) * wardBSAOperator c h b t N j
termination_by r => r

/-- The undivided source endomorphism, including its terminal value at N.
The terminal zero denominator is never used to define this source. -/
noncomputable def wardBSASourceOperator (c h b t : ℂ) (N r : ℕ) :
    Module.End ℂ (ℂ → wardSequenceSpace c h) :=
  ∑ j : Fin r, wardTransportMode c h b ((j:ℤ)-(r:ℤ)) * wardBSAOperator c h b t N j

/-- Acting on a primary seed gives exactly the already proved intermediate
transport recursion. This is equality of actual states, not formal words. -/
theorem wardBSAOperator_apply (c h b a t : ℂ) (N r : ℕ)
    (f : ℂ → wardSequenceSpace c h)
    (h0 : wardWeight c h f=a • f) (h1 : wardP c h b f=0) (h2 : wardQ c h b f=0) :
    wardBSAOperator c h b t N r f=
      BSAWardTransport.transportState (wardTransportSystem c h b a f h0 h1 h2) t N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [wardBSAOperator,BSAWardTransport.transportState_zero,wardTransportSystem]
    | succ r =>
      rw [wardBSAOperator,BSAWardTransport.transportState]
      simp only [LinearMap.smul_apply,LinearMap.sum_apply,Module.End.mul_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j (by omega)]
      rfl

/-- Evaluating the undivided source agrees with the corresponding transported
source; this includes the terminal singular expression. -/
theorem wardBSASourceOperator_apply (c h b a t : ℂ) (N r : ℕ)
    (f : ℂ → wardSequenceSpace c h)
    (h0 : wardWeight c h f=a • f) (h1 : wardP c h b f=0) (h2 : wardQ c h b f=0) :
    wardBSASourceOperator c h b t N r f=
      BSAWardTransport.transportSource (wardTransportSystem c h b a f h0 h1 h2) t N r := by
  simp only [wardBSASourceOperator,BSAWardTransport.transportSource,LinearMap.sum_apply,
    Module.End.mul_apply,wardBSAOperator_apply c h b a t N _ f h0 h1 h2]
  rfl

/-- Every negative indexed transport mode preserves initial coefficient zeros. -/
theorem wardTransportMode_below (c h b : ℂ) (m : ℤ) (hm : m<0)
    (f : ℂ → wardSequenceSpace c h) (r : ℕ) (hf : WardBelow f r) :
    WardBelow (wardTransportMode c h b m f) r := by
  obtain ⟨k,rfl⟩ := Int.eq_negSucc_of_lt_zero hm
  cases k with
  | zero => exact wardA_below c h b f r hf
  | succ k => exact wardNegative_below c h b k f r hf

/-- Every intermediate BSA endomorphism is triangular, with no primary
condition on the input sequence. -/
theorem wardBSAOperator_below (c h b t : ℂ) (N n : ℕ)
    (f : ℂ → wardSequenceSpace c h) (r : ℕ) (hf : WardBelow f r) :
    WardBelow (wardBSAOperator c h b t N n f) r := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [wardBSAOperator] using hf
    | succ n =>
      intro a j hj
      simp only [wardBSAOperator,LinearMap.smul_apply,LinearMap.sum_apply,Module.End.mul_apply,
        Pi.smul_apply,Submodule.coe_smul,Submodule.coe_sum,Finset.sum_apply]
      have hh (i : Fin (n+1)) :
          (wardTransportMode c h b ((i:ℤ)-((n:ℤ)+1))
            (wardBSAOperator c h b t N i f) a).val j=0 :=
        wardTransportMode_below c h b _ (by omega) _ r (ih i (by omega)) a j hj
      simp only [hh,Finset.sum_const_zero,smul_zero]

/-- The undivided terminal operator also preserves earlier coefficient zeros.
This supplies a genuine triangular kernel equation for later construction. -/
theorem wardBSASourceOperator_below (c h b t : ℂ) (N n : ℕ)
    (f : ℂ → wardSequenceSpace c h) (r : ℕ) (hf : WardBelow f r) :
    WardBelow (wardBSASourceOperator c h b t N n f) r := by
  intro a j hj
  simp only [wardBSASourceOperator,LinearMap.sum_apply,Module.End.mul_apply,
    Submodule.coe_sum,Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  exact wardTransportMode_below c h b _ (by omega) _ r
    (wardBSAOperator_below c h b t N i f r hf) a j hj
/-- The assumption-free source endomorphism sends a primary seed on the
(1,N) curve to a vector satisfying both positive Ward equations. Seed
existence and nonzero output are still not asserted. -/
theorem wardBSASourceOperator_positive (h b t : ℂ) (N : ℕ) (ht : t≠0) (hN : 3≤N)
    (f : ℂ → wardSequenceSpace (vermaBSACharge t) h)
    (h0 : wardWeight (vermaBSACharge t) h f=vermaBSAWeight N t • f)
    (h1 : wardP (vermaBSACharge t) h b f=0) (h2 : wardQ (vermaBSACharge t) h b f=0) :
    wardP (vermaBSACharge t) h b (wardBSASourceOperator (vermaBSACharge t) h b t N N f)=0 ∧
    wardQ (vermaBSACharge t) h b (wardBSASourceOperator (vermaBSACharge t) h b t N N f)=0 := by
  rw [wardBSASourceOperator_apply _ h b (vermaBSAWeight N t) t N N f h0 h1 h2]
  exact wardBSATerminal_positive h b t N ht hN f h0 h1 h2

/-- The same actual source endomorphism shifts a primary seed's field
weight by N; zero output is allowed in this equality. -/
theorem wardBSASourceOperator_weight (h b t : ℂ) (N : ℕ)
    (f : ℂ → wardSequenceSpace (vermaBSACharge t) h)
    (h0 : wardWeight (vermaBSACharge t) h f=vermaBSAWeight N t • f)
    (h1 : wardP (vermaBSACharge t) h b f=0) (h2 : wardQ (vermaBSACharge t) h b f=0) :
    wardWeight (vermaBSACharge t) h (wardBSASourceOperator (vermaBSACharge t) h b t N N f)=
      (vermaBSAWeight N t+(N:ℂ)) • wardBSASourceOperator (vermaBSACharge t) h b t N N f := by
  rw [wardBSASourceOperator_apply _ h b (vermaBSAWeight N t) t N N f h0 h1 h2]
  exact wardBSATerminal_weight h b t N f h0 h1 h2

end VOA.InverseDS.VirasoroVerma
