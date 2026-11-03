/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVacuumFusionSource
import VOA.Examples.VirasoroFusionNonresonantWard
import VOA.Examples.VirasoroFusionThreeMinimalArithmetic
import VOA.Examples.VirasoroSingularGram
import VOA.Core.DeformationLiftedModes

/-!
# Vacuum survival of the q=3 fusion source

At the actual rational vacuum parameters, the scalar off-diagonal is half
of 4-6j/p. Coprimality makes it nonzero. The source equations therefore
force nonzero even coefficients and a nonzero terminal vacuum projection.
This is an ordinary singular-state construction, not a norm derivative
or rigidity theorem.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule

/-- The operator-derived off-diagonal at even index 2j is the expected
nonzero arithmetic factor, with the one-half normalization of our Fock test. -/
theorem minimalThree_survival_factor (p j : ℕ) (hp : 2≤p) :
    (((3:ℂ)/(p:ℂ))/2)*(fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))+
      vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+2-((2*j:ℕ):ℂ))=
      (1/2:ℂ)*(4-6*(j:ℂ)/(p:ℂ)) := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
  have hs : ((p-1:ℕ):ℂ)=(p:ℂ)-1 := by exact_mod_cast Int.ofNat_sub (by omega : 1≤p)
  unfold fusionKacWeight vermaBSAWeight
  rw [hs]
  push_cast
  field_simp
  ring

/-- The even-step coefficient in the ACTUAL scalar source never vanishes
at coprime q=3 vacuum parameters. -/
theorem minimalThree_survival_factor_ne_zero (p j : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    (((3:ℂ)/(p:ℂ))/2)*(fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))+
      vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+2-((2*j:ℕ):ℂ))≠0 := by
  rw [minimalThree_survival_factor p j hp]
  exact mul_ne_zero (by norm_num) (fusionThree_vacuum_factor_ne_zero p j hp hcop)

/-- A direct preterminal coefficient solution exists already in the
highest-weight-zero Verma module at the rational vacuum parameters. -/
theorem exists_minimalThree_vacuum_kernel (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    ∃ f : wardSequenceSpace (vermaBSACharge ((3:ℂ)/(p:ℂ))) 0,
      f.val 0=highestVector (vermaBSACharge ((3:ℂ)/(p:ℂ))) 0 ∧
      ∀ r<(p-1)*2,
        (wardSourceAt (vermaBSACharge ((3:ℂ)/(p:ℂ))) 0
          (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
          (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) 3 f).val r=0 := by
  have hh := exists_fusion_minimal_three_partial_kernel p hp hcop
  have hw : fusionKacWeight ((p-1:ℕ):ℂ) ((3:ℂ)-1) ((3:ℂ)/(p:ℂ))=0 := by
    convert fusionThree_minimal_weight_zero p hp using 1 <;> norm_num
  rw [hw] at hh
  exact hh

/-- All even preterminal coefficients have nonzero ACTUAL vacuum tests.
The induction uses the actual zero source and its proved two-step formula. -/
theorem minimalThree_kernel_survival (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (f : wardSequenceSpace (vermaBSACharge ((3:ℂ)/(p:ℂ))) 0)
    (h0 : f.val 0=highestVector (vermaBSACharge ((3:ℂ)/(p:ℂ))) 0)
    (hf : ∀ r<(p-1)*2,
      (wardSourceAt (vermaBSACharge ((3:ℂ)/(p:ℂ))) 0
        (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
        (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) 3 f).val r=0)
    (j : ℕ) (hj : j<p-1) :
    vermaVacuumSurvival (vermaBSACharge ((3:ℂ)/(p:ℂ))) (f.val (2*j))≠0 := by
  induction j with
  | zero => simp [h0]
  | succ j ih =>
    have hh := vermaVacuumSurvival_sourceAt_three (vermaBSACharge ((3:ℂ)/(p:ℂ)))
      (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
      (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) f (2*j)
    rw [hf (2*j+2) (by omega),map_zero] at hh
    intro hz
    rw [show 2*j+2=2*(j+1) by omega,hz,mul_zero,zero_add] at hh
    exact mul_ne_zero (minimalThree_survival_factor_ne_zero p (j+1) hp hcop)
      (ih (by omega)) hh.symm

/-- The terminal source of any normalized preterminal solution has a
nonzero vacuum projection. The terminal diagonal is zero, leaving the
proved nonzero even-step term. -/
theorem minimalThree_terminal_survival (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (f : wardSequenceSpace (vermaBSACharge ((3:ℂ)/(p:ℂ))) 0)
    (h0 : f.val 0=highestVector (vermaBSACharge ((3:ℂ)/(p:ℂ))) 0)
    (hf : ∀ r<(p-1)*2,
      (wardSourceAt (vermaBSACharge ((3:ℂ)/(p:ℂ))) 0
        (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
        (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) 3 f).val r=0) :
    vacuumProjection (vermaBSACharge ((3:ℂ)/(p:ℂ)))
      ((wardSourceAt (vermaBSACharge ((3:ℂ)/(p:ℂ))) 0
        (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
        (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) 3 f).val ((p-1)*2))≠0 := by
  apply vacuumProjection_ne_zero_of_survival
  have hh := vermaVacuumSurvival_sourceAt_three (vermaBSACharge ((3:ℂ)/(p:ℂ)))
    (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
    (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) f (2*(p-2))
  have hd := wardBSASourceDiagonal_label_terminal (p-1) 3 ((3:ℂ)/(p:ℂ))
    (by omega) (minimal_three_parameter_ne_zero p (by omega))
  norm_num only [show (3:ℂ)-1=2 by norm_num,show (3:ℕ)-1=2 by omega] at hd
  rw [fusionThree_minimal_weight_zero p hp] at hd
  have he : 2*(p-2)+2=(p-1)*2 := by omega
  rw [he,hd,zero_mul,zero_add] at hh
  rw [hh]
  have hk := minimalThree_survival_factor_ne_zero p (p-1) hp hcop
  rw [show 2*(p-1)=(p-1)*2 by omega] at hk
  exact mul_ne_zero hk (minimalThree_kernel_survival p hp hcop f h0 hf (p-2) (by omega))

/-- The actual Verma-to-vacuum projection preserves conformal level.
This follows from its zero-mode intertwining and the complete vacuum grading. -/
theorem vacuumProjection_level (c : ℂ) (n : ℕ) (v : Verma c 0)
    (hv : v∈sortedSpan c 0 n) : vacuumProjection c v∈gradingVir c (n:ℤ) := by
  change vacuumProjection c v∈(virasoroVOA c).grading (n:ℤ)
  rw [Deform.grading_eq_L_zero_eigenspace,Module.End.mem_eigenspace_iff,
    virasoroVOA_L_eq_Lop,← vacuumProjection_mode]
  rw [(verma_mem_level_iff_eigen c 0 n v).mp hv,map_smul]
  simp

/-- Every coprime M(p,3) parameter has an ACTUAL nonzero singular state
in the universal vacuum module at its first candidate singular level.
The construction proves vacuum survival, not just Verma nonvanishing. -/
theorem minimalThree_nonzero_vacuum_singular (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    ∃ v : VirUniv (vermaBSACharge ((3:ℂ)/(p:ℂ))),
      v∈gradingVir (vermaBSACharge ((3:ℂ)/(p:ℂ))) (((p-1)*2:ℕ):ℤ) ∧
      v≠0 ∧ Lop (vermaBSACharge ((3:ℂ)/(p:ℂ))) 1 v=0 ∧
      Lop (vermaBSACharge ((3:ℂ)/(p:ℂ))) 2 v=0 := by
  obtain ⟨f,h0,hf⟩ := exists_minimalThree_vacuum_kernel p hp hcop
  let t : ℂ := 3/(p:ℂ)
  let b : ℂ := fusionKacWeight ((p-1:ℕ):ℂ) 0 t
  let S := wardSourceAt (vermaBSACharge t) 0 b t (vermaBSAWeight 3 t) 3 f
  have ht : t≠0 := minimal_three_parameter_ne_zero p (by omega)
  have hw : fusionKacWeight ((p-1:ℕ):ℂ) ((3:ℂ)-1) t=0 := by
    convert fusionThree_minimal_weight_zero p hp using 1 <;> norm_num [t]
  have hd : ∀ r, 0<r → r<(p-1)*2 →
      wardBSASourceDiagonal 0 b t 3 r 3 (vermaBSAWeight 3 t+3)≠0 := by
    intro r hr hrN
    have hh := wardBSASourceDiagonal_minimal_three p r hp hcop hr hrN
    rw [hw] at hh
    exact hh
  have hz : wardBSASourceDiagonal 0 b t 3 ((p-1)*2) 3 (vermaBSAWeight 3 t+3)=0 := by
    have hh := wardBSASourceDiagonal_label_terminal (p-1) 3 t (by omega) ht
    simp only [Nat.cast_ofNat] at hh
    rw [hw] at hh
    exact hh
  have h1 := nonresonant_terminal_L1 0 b t 3 ((p-1)*2) ht (by omega) f hf hd (by omega) hz
  have h2 := nonresonant_terminal_L2 0 b t 3 ((p-1)*2) ht (by omega) f hf hd (by omega) hz
  refine ⟨vacuumProjection (vermaBSACharge t) (S.val ((p-1)*2)),
    vacuumProjection_level _ _ _ (S.property _),
    minimalThree_terminal_survival p hp hcop f h0 hf,?_,?_⟩
  · rw [← vacuumProjection_mode,h1,map_zero]
  · rw [← vacuumProjection_mode,h2,map_zero]

/-- The actual partition Gram determinant has a root at EVERY coprime
M(p,3) charge and level 2(p-1). No simple-root or derivative claim is made. -/
theorem partitionDeterminant_minimal_three_root (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    ((VirDeformModes.NormalOrdering.partitionGramPolynomial ((p-1)*2)).det).eval
      (minimalCentralCharge p 3 : ℂ)=0 := by
  obtain ⟨v,hv,hn,h1,h2⟩ := minimalThree_nonzero_vacuum_singular p hp hcop
  have hh := VirDeformModes.NormalOrdering.partitionDeterminant_eval_zero_of_singular
    (vermaBSACharge ((3:ℂ)/(p:ℂ))) (n:=(p-1)*2) (by omega) ⟨v,hv⟩
    (by intro hz; exact hn (congrArg Subtype.val hz)) h1 h2
  rw [fusionThree_minimal_charge p hp] at hh
  exact hh

end VOA.InverseDS.VirasoroVerma
