/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFusionThreeNonvanishing
import VOA.Examples.VirasoroWardClosedKernel

/-!
# Nonzero (A,2) Verma singular states at every nonzero parameter

Nonreal parameters already have actual nonzero fusion output. The Ward
matrix depends continuously on charge and weight. Compactness of the
normalized finite-dimensional coefficient sphere supplies a nonzero kernel
at every nonzero parameter, including rational ones where a chosen vector
formula might have poles. This does not prove survival in the vacuum
quotient or a nonzero derivative of its canonical norm.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- Every positive first label has a genuine nonzero singular Verma state
on the (A,2) curve at every nonzero complex parameter. The proof specializes
the equations and normalized coordinates, not a potentially singular formula. -/
theorem fusionThree_highest_all_parameters (A : ℕ) (hA : 0<A)
    (t : ℂ) (ht : t≠0) :
    ∃ v : Verma (vermaBSACharge t) (fusionKacWeight (A:ℂ) (((3:ℕ):ℂ)-1) t),
      v≠0 ∧ v∈sortedSpan (vermaBSACharge t)
        (fusionKacWeight (A:ℂ) (((3:ℕ):ℂ)-1) t) (A*(3-1)) ∧
      IsHighestWeightVector (vermaRep (vermaBSACharge t)
        (fusionKacWeight (A:ℂ) (((3:ℕ):ℂ)-1) t)) v (vermaBSACharge t)
          (fusionKacWeight (A:ℂ) (((3:ℕ):ℂ)-1) t+((A*(3-1):ℕ):ℂ)) := by
  apply verma_highest_of_nonreal vermaBSACharge
    (fun z => fusionKacWeight (A:ℂ) (((3:ℕ):ℂ)-1) z) (A*(3-1)) t
  · unfold vermaBSACharge
    fun_prop (disch := assumption)
  · unfold fusionKacWeight
    fun_prop (disch := exact mul_ne_zero (by norm_num) ht)
  · intro z hz
    refine ⟨fusionTerminalState A 3 z hz (by omega),
      fusionTerminalState_three_ne_zero A z hz hA,?_,?_⟩
    · exact fusionTerminalState_positive A 3 z hz hA (by omega) 1 (by omega)
    · exact fusionTerminalState_positive A 3 z hz hA (by omega) 2 (by omega)

end VOA.InverseDS.VirasoroVerma
