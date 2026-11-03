import VOA.DeligneAudit.D4FusionRealizationTwoWordTable
import Mathlib.Data.Fintype.Card

/-! Exact finite count of the certified word labels at level at most 1. -/
namespace VOA.DeligneAudit.D4Two.Certificate

theorem word_level_count_1 :
    Fintype.card {i : Fin 841 // (wordNode i).level ≤ 1} = 678 := by
  decide +kernel

end VOA.DeligneAudit.D4Two.Certificate
