/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Filtered.GeneratorCurrentLiSpanning

/-!
# The sl₂ instance of the generic current Li-spanning theorem

A consistency check of `GeneratorCurrentLiSpanning`: the bespoke sl₂ result
`AffineVOA.CurrentLi.liFiltration_eq_currentWordPiece` is recovered from the generic Lie-current
theorem, using only the sl₂ commutator `current_comm`, vacuum annihilation and word spanning.
The A₂ instance is `DeligneAudit.A2.universal_genWordsSpan`.
-/

namespace VOA
namespace AffineVOA
namespace CurrentLi

open VOA.AffineVOA.Inst

noncomputable section

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- Li's filtration of the universal noncritical affine `sl₂` VOA is spanned by current words,
from the generic Lie-current theorem. -/
theorem sl2_genWordsSpan :
    GeneratorWordsSpanLiFiltration (affineSl2VOA_closed k hk) (currentState k) (fun _ => 1) := by
  apply generatorWordsSpanLiFiltration_of_tracked
  · exact generatorModeTracked_of_current_comm (J k) fabc
      (fun a b m => (m : ℂ) * k * kappa a b) (smul_currentState_eq_J k hk)
      (fun a b m p => by rw [current_comm]; rfl)
      (fun a m hm => J_vacuum_nonneg k a hm)
  · rw [show genWordState (affineSl2VOA_closed k hk) (currentState k) (fun _ => 1) =
        wordStateA k from funext fun w => (wordStateA_eq_generatorWord k hk w).symm]
    exact wordStateA_span k

/-- The generic theorem reproduces the bespoke sl₂ description of Li's filtration. -/
theorem sl2_liFiltration_eq_genWordPiece (p : ℕ) :
    liFiltration (affineSl2VOA_closed k hk) p =
      genWordPiece (affineSl2VOA_closed k hk) (currentState k) (fun _ => 1) p :=
  liFiltration_eq_genWordPiece _ _ _ (fun a => currentState_mem_grading k hk a)
    (sl2_genWordsSpan k hk) p

end

end CurrentLi
end AffineVOA
end VOA
