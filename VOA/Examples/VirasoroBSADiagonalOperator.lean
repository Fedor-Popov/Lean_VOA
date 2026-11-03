/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroBSAOperator

/-!
# The scalar diagonal of the full BSA source

The scalar recursion is identified with the actual endomorphism on the
first coefficient that may be nonzero. Later modules VirasoroFusionProduct
and VirasoroFusionLabelRoots prove the finite product, exact zeros and
nonreal intermediate nonvanishing; this module supplies their operator bridge.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- The scalar diagonal of a single negative descendant of positive index k. -/
noncomputable def wardCreationDiagonal (h b a : ℂ) (r k : ℕ) : ℂ :=
  (-1:ℂ)^k*((k:ℂ)*b+a-(k:ℂ)-h-(r:ℂ))

/-- The integer-indexed mode has the same diagonal at every negative index,
including the separately constructed first negative operator. -/
theorem wardTransportMode_diagonal (c h b : ℂ) (k : ℕ) (hk : 0<k)
    (f : ℂ → wardSequenceSpace c h) (r : ℕ) (hf : WardBelow f r) (a : ℂ) :
    (wardTransportMode c h b (-(k:ℤ)) f a).val r=
      wardCreationDiagonal h b a r k • (f (a-(k:ℂ))).val r := by
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero =>
      change ((wardA c h b) f a).val r=_
      rw [wardA_apply]
      norm_num [wardCreationDiagonal]
      module
    | succ k =>
      have hi : -((k+1+1:ℕ):ℤ)=Int.negSucc (k+1) := by omega
      rw [hi]
      change ((wardNegative c h b k) f a).val r=_
      rw [wardNegative_diagonal c h b k f r hf a]
      simp only [wardCreationDiagonal,Nat.cast_add,Nat.cast_one,pow_succ]
      have he : a-((k:ℂ)+2)=a-((k:ℂ)+1+1) := by ring
      rw [he]
      congr 1
      ring

/-- The scalar recursion for the intermediate BSA endomorphism. The output
field weight changes in each factor exactly as it does in composition. -/
noncomputable def wardBSADiagonal (h b t : ℂ) (N r : ℕ) : ℕ → ℂ → ℂ
  | 0, _ => 1
  | n+1, a => (-t/(((n:ℂ)+1)*((N:ℂ)-((n:ℂ)+1)))) *
      ∑ j : Fin (n+1), wardCreationDiagonal h b a r (n+1-j) *
        wardBSADiagonal h b t N r j (a-((n+1-j:ℕ):ℂ))
termination_by n => n

/-- The undivided scalar source, in particular at the terminal index N.
The later VirasoroFusionProduct module classifies its terminal zeros. -/
noncomputable def wardBSASourceDiagonal (h b t : ℂ) (N r n : ℕ) (a : ℂ) : ℂ :=
  ∑ j : Fin n, wardCreationDiagonal h b a r (n-j) *
    wardBSADiagonal h b t N r j (a-((n-j:ℕ):ℂ))

/-- Each intermediate endomorphism's first surviving coefficient is exactly
its recursively defined scalar times the input at the shifted field weight. -/
theorem wardBSAOperator_diagonal (c h b t : ℂ) (N n : ℕ)
    (f : ℂ → wardSequenceSpace c h) (r : ℕ) (hf : WardBelow f r) (a : ℂ) :
    (wardBSAOperator c h b t N n f a).val r=
      wardBSADiagonal h b t N r n a • (f (a-(n:ℂ))).val r := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    cases n with
    | zero => simp [wardBSAOperator,wardBSADiagonal]
    | succ n =>
      simp only [wardBSAOperator,wardBSADiagonal,LinearMap.smul_apply,LinearMap.sum_apply,
        Module.End.mul_apply,Pi.smul_apply,Submodule.coe_smul,Submodule.coe_sum,
        Finset.sum_apply,mul_smul,Finset.sum_smul]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hi : (j:ℤ)-((n:ℤ)+1)=-((n+1-j:ℕ):ℤ) := by omega
      rw [hi,wardTransportMode_diagonal c h b (n+1-j) (by omega) _ r
        (wardBSAOperator_below c h b t N j f r hf)]
      rw [ih j (by omega),smul_smul]
      have he : a-((n+1-j:ℕ):ℂ)-(j:ℂ)=a-((n+1:ℕ):ℂ) := by
        have hj' : ((n+1-j:ℕ):ℂ)+(j:ℂ)=((n+1:ℕ):ℂ) := by
          exact_mod_cast (Nat.sub_add_cancel (by omega : j.val≤n+1))
        linear_combination -hj'
      rw [he,smul_smul]

/-- The actual full source diagonal is the explicit finite scalar recursion,
without a primary-seed or nonvanishing assumption. -/
theorem wardBSASourceOperator_diagonal (c h b t : ℂ) (N n : ℕ)
    (f : ℂ → wardSequenceSpace c h) (r : ℕ) (hf : WardBelow f r) (a : ℂ) :
    (wardBSASourceOperator c h b t N n f a).val r=
      wardBSASourceDiagonal h b t N r n a • (f (a-(n:ℂ))).val r := by
  simp only [wardBSASourceOperator,wardBSASourceDiagonal,LinearMap.sum_apply,
    Module.End.mul_apply,Submodule.coe_sum,Finset.sum_apply,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j hj
  have hi : (j:ℤ)-(n:ℤ)=-((n-j:ℕ):ℤ) := by omega
  rw [hi,wardTransportMode_diagonal c h b (n-j) (by omega) _ r
    (wardBSAOperator_below c h b t N j f r hf),
    wardBSAOperator_diagonal c h b t N j f r hf,smul_smul]
  have he : a-((n-j:ℕ):ℂ)-(j:ℂ)=a-(n:ℂ) := by
    have hj' : ((n-j:ℕ):ℂ)+(j:ℂ)=(n:ℂ) := by
      exact_mod_cast (Nat.sub_add_cancel (by omega : j.val≤n))
    linear_combination -hj'
  rw [he]
end VOA.InverseDS.VirasoroVerma
