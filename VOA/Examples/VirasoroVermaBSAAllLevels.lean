/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaBSANonvanishing
import VOA.Examples.VirasoroVacuumExactSequence

/-!
# The two boundary levels of the generic BSA singular family

The existing uniform telescopes cover levels at least three. Translation
settles level one, and the undivided L2 telescope at index zero settles level
two. Thus the actual nonzero (1,N) singular family includes every positive
N and every nonzero parameter. No vacuum survival is claimed.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule

/-- At level two the undivided L2 telescope has no earlier source. Its
remaining highest-weight and central coefficients cancel on the BSA curve. -/
theorem vermaBSASource_two_L2 (t : ℂ) (ht : t≠0) :
    vermaMode (vermaBSACharge t) (vermaBSAWeight 2 t) 2
      (vermaBSASource (vermaBSACharge t) (vermaBSAWeight 2 t) t 2 2)=0 := by
  have hh := vermaBSASource_L2_step (vermaBSACharge t) (vermaBSAWeight 2 t) t 2 0
    (vermaBSAOffset1 2 t) 0 (vermaBSAState_L1 _ t 2 0 ht (by omega))
    (fun j => Fin.elim0 j)
  have hc : 4*vermaBSAWeight 2 t+3*vermaBSAOffset1 2 t+vermaBSACharge t/2=0 := by
    unfold vermaBSAWeight vermaBSAOffset1 vermaBSACharge
    norm_num
    field_simp
    <;> ring
  simpa [vermaBSASource, hc] using hh

/-- The actual terminal BSA source satisfies both positive generator
relations at every positive level, including the translation boundary. -/
theorem vermaBSASource_one_two_all (t : ℂ) (N : ℕ) (ht : t≠0) (hN : 0<N) :
    vermaMode (vermaBSACharge t) (vermaBSAWeight N t) 1
      (vermaBSASource (vermaBSACharge t) (vermaBSAWeight N t) t N N)=0 ∧
    vermaMode (vermaBSACharge t) (vermaBSAWeight N t) 2
      (vermaBSASource (vermaBSACharge t) (vermaBSAWeight N t) t N N)=0 := by
  by_cases h1 : N=1
  · subst N
    have hw : vermaBSAWeight 1 t=0 := by simp [vermaBSAWeight]
    rw [hw]
    simpa [vermaBSASource] using
      And.intro ((translation_highest (vermaBSACharge t)).pos_annihilate 1 (by norm_num))
        ((translation_highest (vermaBSACharge t)).pos_annihilate 2 (by norm_num))
  · refine ⟨vermaBSASource_L1_terminal _ t N ht (by omega), ?_⟩
    by_cases h2 : N=2
    · subst N; exact vermaBSASource_two_L2 t ht
    · exact vermaBSASource_L2_terminal t N ht (by omega)

/-- At every positive level and every nonzero complex parameter the actual
BSA source is a nonzero highest-weight state, with the displayed relative
level. The two small levels need no separate existence assumption. -/
theorem vermaBSA_nonzero_highest_all (t : ℂ) (N : ℕ) (ht : t≠0) (hN : 0<N) :
    ∃ v : Verma (vermaBSACharge t) (vermaBSAWeight N t),
      v≠0 ∧ v∈sortedSpan (vermaBSACharge t) (vermaBSAWeight N t) N ∧
      IsHighestWeightVector (vermaRep (vermaBSACharge t) (vermaBSAWeight N t)) v
        (vermaBSACharge t) (vermaBSAWeight N t+N) := by
  have hh := vermaBSASource_one_two_all t N ht hN
  refine ⟨vermaBSASource _ _ t N N, vermaBSASource_ne_zero _ _ t N ht hN,
    vermaBSASource_mem_level _ _ t N N, rfl,
    verma_positive_zero_of_one_two _ _ _ hh.1 hh.2, ?_⟩
  exact vermaBSASource_L0 _ _ t N N (fun j => vermaBSAState_L0 _ _ t N j)

end VOA.InverseDS.VirasoroVerma
