/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFusionProduct

/-!
# Solving the actual triangular source equation before resonance

A correction supported at a single coefficient cancels its source whenever
the diagonal is nonzero. Earlier equations stay solved. This constructs
actual Verma states, but does not yet prove that the terminal source is
singular or nonzero.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- A level sequence supported at just r, with a prescribed actual level-r
state. Membership is checked in the Verma module, not in a formal word space. -/
noncomputable def wardSingle (c h : ℂ) (r : ℕ) (v : sortedSpan c h r) :
    wardSequenceSpace c h := by
  classical
  refine ⟨fun j => if j=r then v.val else 0,?_⟩
  intro j
  by_cases hj : j=r
  · subst j; simpa using v.property
  · simp only [if_neg hj]; exact (sortedSpan c h j).zero_mem

/-- The single coefficient has exactly its prescribed value. -/
@[simp] theorem wardSingle_same (c h : ℂ) (r : ℕ) (v : sortedSpan c h r) :
    (wardSingle c h r v).val r=v.val := by simp [wardSingle]

/-- Every other coefficient of a single correction is zero. -/
theorem wardSingle_other (c h : ℂ) (r : ℕ) (v : sortedSpan c h r)
    (j : ℕ) (hj : j≠r) : (wardSingle c h r v).val j=0 := by simp [wardSingle,hj]

/-- Place one actual level sequence at field weight a. This enforces the
weight equation without assuming either positive primary equation. -/
noncomputable def wardFieldLift (c h a : ℂ) :
    wardSequenceSpace c h →ₗ[ℂ] (ℂ → wardSequenceSpace c h) := by
  classical
  exact {
    toFun := fun f w => if w=a then f else 0
    map_add' := by intro f g; ext w; by_cases hw : w=a <;> simp [hw]
    map_smul' := by intro z f; ext w; by_cases hw : w=a <;> simp [hw] }

/-- The field lift is an actual eigenvector of the field-weight operator. -/
theorem wardFieldLift_weight (c h a : ℂ) (f : wardSequenceSpace c h) :
    wardWeight c h (wardFieldLift c h a f)=a • wardFieldLift c h a f := by
  classical
  ext w
  by_cases hw : w=a
  · subst w; simp [wardWeight,wardFieldLift]
  · simp [wardWeight,wardFieldLift,hw]

/-- Evaluate the actual source at output field weight a+N after lifting
an input sequence at a. This is a linear operator on actual level sequences. -/
noncomputable def wardSourceAt (c h b t a : ℂ) (N : ℕ) :
    Module.End ℂ (wardSequenceSpace c h) where
  toFun f := wardBSASourceOperator c h b t N N (wardFieldLift c h a f) (a+(N:ℂ))
  map_add' f g := by simp
  map_smul' z f := by simp

/-- The field lift preserves any given initial segment of zeros. -/
theorem wardFieldLift_below (c h a : ℂ) (f : wardSequenceSpace c h) (r : ℕ)
    (hf : ∀ j<r, f.val j=0) : WardBelow (wardFieldLift c h a f) r := by
  classical
  intro w j hj
  change (if w=a then f else 0).val j=0
  split_ifs <;> simp [hf j hj]

/-- The evaluated actual source is triangular in the coefficient index. -/
theorem wardSourceAt_below (c h b t a : ℂ) (N r : ℕ) (f : wardSequenceSpace c h)
    (hf : ∀ j<r, f.val j=0) : ∀ j<r, (wardSourceAt c h b t a N f).val j=0 := by
  intro j hj
  exact wardBSASourceOperator_below c h b t N N _ r
    (wardFieldLift_below c h a f r hf) (a+(N:ℂ)) j hj

/-- The source's first surviving coefficient is exactly the proved fusion
scalar times the input coefficient, with all field shifts discharged. -/
theorem wardSourceAt_diagonal (c h b t a : ℂ) (N r : ℕ) (f : wardSequenceSpace c h)
    (hf : ∀ j<r, f.val j=0) :
    (wardSourceAt c h b t a N f).val r=
      wardBSASourceDiagonal h b t N r N (a+(N:ℂ)) • f.val r := by
  have hh := wardBSASourceOperator_diagonal c h b t N N
    (wardFieldLift c h a f) r (wardFieldLift_below c h a f r hf) (a+(N:ℂ))
  simpa [wardSourceAt,wardFieldLift] using hh

/-- Single-coefficient elimination for any actual level-sequence operator
with a triangular scalar diagonal. It constructs states, not assumed kernels. -/
theorem exists_ward_partial_kernel (c h : ℂ)
    (T : Module.End ℂ (wardSequenceSpace c h)) (d : ℕ → ℂ) (R : ℕ)
    (hdiag : ∀ (r : ℕ) (f : wardSequenceSpace c h),
      (∀ j<r, f.val j=0) → (T f).val r=d r • f.val r)
    (hbelow : ∀ (r : ℕ) (f : wardSequenceSpace c h),
      (∀ j<r, f.val j=0) → ∀ j<r, (T f).val j=0)
    (hd0 : d 0=0) (hd : ∀ r, 0<r → r<R → d r≠0)
    (v : sortedSpan c h 0) :
    ∃ f : wardSequenceSpace c h, f.val 0=v.val ∧ ∀ r<R, (T f).val r=0 := by
  have step : ∀ n, n≤R → ∃ f : wardSequenceSpace c h,
      f.val 0=v.val ∧ ∀ r<n, (T f).val r=0 := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨wardSingle c h 0 v,wardSingle_same _ _ _ _,by omega⟩
    | succ n ih =>
      intro hn
      by_cases hn0 : n=0
      · subst n
        refine ⟨wardSingle c h 0 v,wardSingle_same _ _ _ _,?_⟩
        intro r hr
        have hr0 : r=0 := by omega
        subst r
        rw [hdiag 0 _ (by omega),hd0,zero_smul]
      · obtain ⟨f,hf0,hf⟩ := ih (by omega)
        let w : sortedSpan c h n := ⟨-(d n)⁻¹ • (T f).val n,
          (sortedSpan c h n).smul_mem _ ((T f).property n)⟩
        let g := wardSingle c h n w
        have hg : ∀ j<n, g.val j=0 := fun j hj => wardSingle_other c h n w j (by omega)
        refine ⟨f+g,?_,?_⟩
        · change f.val 0+g.val 0=v.val
          rw [hf0,hg 0 (by omega),add_zero]
        · intro r hr
          change (T (f+g)).val r=0
          rw [map_add]
          change (T f).val r+(T g).val r=0
          by_cases hrn : r<n
          · rw [hf r hrn,hbelow n g hg r hrn,add_zero]
          · have he : r=n := by omega
            subst r
            rw [hdiag n g hg]
            dsimp only [g]
            rw [wardSingle_same]
            change (T f).val n+d n • (-(d n)⁻¹ • (T f).val n)=0
            rw [smul_smul,mul_neg,mul_inv_cancel₀ (hd n (by omega) (by omega)),neg_one_smul,add_neg_cancel]
  exact step R le_rfl

/-- On the intended generic label curves there exists an actual sequence
with any prescribed leading state whose source vanishes below A(N-1).
This is an unconditional construction for nonreal t, not a primary-seed axiom. -/
theorem exists_fusion_partial_kernel (A N : ℕ) (t : ℂ) (him : t.im≠0)
    (hN : 2≤N) (v : sortedSpan (vermaBSACharge t)
      (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t) 0) :
    ∃ f : wardSequenceSpace (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t),
      f.val 0=v.val ∧ ∀ r<A*(N-1),
        (wardSourceAt (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
          (fusionKacWeight (A:ℂ) 0 t) t (vermaBSAWeight N t) N f).val r=0 := by
  have ht : t≠0 := by intro hz; apply him; simp [hz]
  apply exists_ward_partial_kernel _ _ _
    (fun r => wardBSASourceDiagonal (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
      (fusionKacWeight (A:ℂ) 0 t) t N r N (vermaBSAWeight N t+(N:ℂ)))
  · exact fun r f hf => wardSourceAt_diagonal _ _ _ _ _ _ r f hf
  · exact fun r f hf => wardSourceAt_below _ _ _ _ _ _ r f hf
  · exact wardBSASourceDiagonal_label_initial A N t hN ht
  · exact fun r hr hrN => wardBSASourceDiagonal_nonreal_intermediate A N r t him (by omega) hr hrN
/-- A triangular equation with invertible interior diagonals determines
all preterminal coefficients uniquely once its leading coefficient is fixed. -/
theorem ward_partial_kernel_unique (c h : ℂ)
    (T : Module.End ℂ (wardSequenceSpace c h)) (d : ℕ → ℂ) (R : ℕ)
    (hdiag : ∀ (r : ℕ) (f : wardSequenceSpace c h),
      (∀ j<r, f.val j=0) → (T f).val r=d r • f.val r)
    (hd : ∀ r, 0<r → r<R → d r≠0)
    (f g : wardSequenceSpace c h) (h0 : f.val 0=g.val 0)
    (hf : ∀ r<R, (T f).val r=0) (hg : ∀ r<R, (T g).val r=0) :
    ∀ r<R, f.val r=g.val r := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    by_cases hz : r=0
    · simpa [hz] using h0
    · have hb : ∀ j<r, (f-g).val j=0 := by
        intro j hj
        change f.val j-g.val j=0
        exact sub_eq_zero.mpr (ih j hj (by omega))
      have hh := hdiag r (f-g) hb
      rw [map_sub] at hh
      change (T f).val r-(T g).val r=d r • (f.val r-g.val r) at hh
      rw [hf r hr,hg r hr,sub_self] at hh
      exact sub_eq_zero.mp ((smul_eq_zero.mp hh.symm).resolve_left (hd r (by omega) hr))

/-- A zero terminal diagonal makes the terminal source independent of the
unspecified terminal coefficient and all later coefficients. -/
theorem ward_partial_kernel_terminal_unique (c h : ℂ)
    (T : Module.End ℂ (wardSequenceSpace c h)) (d : ℕ → ℂ) (R : ℕ)
    (hdiag : ∀ (r : ℕ) (f : wardSequenceSpace c h),
      (∀ j<r, f.val j=0) → (T f).val r=d r • f.val r)
    (hd : ∀ r, 0<r → r<R → d r≠0) (hR : d R=0)
    (f g : wardSequenceSpace c h) (h0 : f.val 0=g.val 0)
    (hf : ∀ r<R, (T f).val r=0) (hg : ∀ r<R, (T g).val r=0) :
    (T f).val R=(T g).val R := by
  have hh := hdiag R (f-g) (by
    intro j hj
    change f.val j-g.val j=0
    exact sub_eq_zero.mpr (ward_partial_kernel_unique c h T d R hdiag hd f g h0 hf hg j hj))
  rw [hR,zero_smul,map_sub] at hh
  exact sub_eq_zero.mp hh

/-- The nonzero actual highest vector as a member of level zero. -/
noncomputable def fusionLeadingState (c h : ℂ) : sortedSpan c h 0 :=
  ⟨highestVector c h,by simpa [energyHW] using negWord_mem_sortedSpan c h []⟩

/-- Fix an actual solution of the preterminal equations, normalized by the
highest vector. Existence comes from the explicit single-coefficient elimination. -/
noncomputable def fusionKernelSequence (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N) :
    wardSequenceSpace (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t) :=
  Classical.choose (exists_fusion_partial_kernel A N t him hN (fusionLeadingState _ _))

/-- The constructed sequence starts with the genuine Verma highest vector. -/
theorem fusionKernelSequence_initial (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N) :
    (fusionKernelSequence A N t him hN).val 0=
      highestVector (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t) :=
  (Classical.choose_spec (exists_fusion_partial_kernel A N t him hN
    (fusionLeadingState _ _))).1

/-- All source coefficients strictly before the terminal resonance vanish. -/
theorem fusionKernelSequence_source_below (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N) :
    ∀ r<A*(N-1),
      (wardSourceAt (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
        (fusionKacWeight (A:ℂ) 0 t) t (vermaBSAWeight N t) N
        (fusionKernelSequence A N t him hN)).val r=0 :=
  (Classical.choose_spec (exists_fusion_partial_kernel A N t him hN
    (fusionLeadingState _ _))).2

/-- The constructed INPUT sequence is nonzero because its leading vector
is nonzero. This does not assert that its terminal SOURCE is nonzero. -/
theorem fusionKernelSequence_ne_zero (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N) :
    fusionKernelSequence A N t him hN≠0 := by
  intro hz
  have hh := fusionKernelSequence_initial A N t him hN
  rw [hz] at hh
  exact highestVector_ne_zero _ _ hh.symm

/-- The actual terminal source, at level A(N-1). Singularity and nonvanishing
are separate obligations; neither is built into this definition. -/
noncomputable def fusionTerminalState (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N) :
    sortedSpan (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t) (A*(N-1)) :=
  ⟨(wardSourceAt (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
      (fusionKacWeight (A:ℂ) 0 t) t (vermaBSAWeight N t) N
      (fusionKernelSequence A N t him hN)).val (A*(N-1)),
    (wardSourceAt _ _ _ _ _ _ (fusionKernelSequence A N t him hN)).property _⟩

/-- Any normalized solution of the preterminal equations gives exactly
the same terminal source. Thus the chosen tail has no mathematical effect. -/
theorem fusionTerminalState_eq_of_solution (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N)
    (f : wardSequenceSpace (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t))
    (hf0 : f.val 0=highestVector (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t))
    (hf : ∀ r<A*(N-1),
      (wardSourceAt (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
        (fusionKacWeight (A:ℂ) 0 t) t (vermaBSAWeight N t) N f).val r=0) :
    (fusionTerminalState A N t him hN).val=
      (wardSourceAt (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
        (fusionKacWeight (A:ℂ) 0 t) t (vermaBSAWeight N t) N f).val (A*(N-1)) := by
  have ht : t≠0 := by intro hz; apply him; simp [hz]
  apply ward_partial_kernel_terminal_unique _ _ _
    (fun r => wardBSASourceDiagonal (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
      (fusionKacWeight (A:ℂ) 0 t) t N r N (vermaBSAWeight N t+(N:ℂ)))
  · exact fun r f hf => wardSourceAt_diagonal _ _ _ _ _ _ r f hf
  · exact fun r hr hrN => wardBSASourceDiagonal_nonreal_intermediate A N r t him (by omega) hr hrN
  · exact wardBSASourceDiagonal_label_terminal A N t hN ht
  · exact (fusionKernelSequence_initial A N t him hN).trans hf0.symm
  · exact fusionKernelSequence_source_below A N t him hN
  · exact hf
end VOA.InverseDS.VirasoroVerma
