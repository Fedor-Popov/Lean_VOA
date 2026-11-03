import VOA.DeligneAudit.D4FusionRealizationTwoWordTable
import Mathlib.Data.Fintype.Card

/-! Exact finite count of the certified word labels at level at most 4. -/
namespace VOA.DeligneAudit.D4Two.Certificate

theorem word_level_count_4 :
    Fintype.card {i : Fin 841 // (wordNode i).level ≤ 4} = 841 := by
  decide +kernel

end VOA.DeligneAudit.D4Two.Certificate
