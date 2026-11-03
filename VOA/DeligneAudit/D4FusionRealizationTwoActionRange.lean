import Mathlib.Data.List.Range

namespace VOA.DeligneAudit.D4Two.Certificate

theorem action_range_join (P : ℕ → Bool) (lo mid hi : ℕ)
    (hlm : lo ≤ mid) (hmh : mid ≤ hi)
    (hleft : (List.range' lo (mid - lo)).all P = true)
    (hright : (List.range' mid (hi - mid)).all P = true) :
    (List.range' lo (hi - lo)).all P = true := by
  apply List.all_eq_true.mpr
  intro i hiMem
  obtain ⟨hil, hih⟩ := List.mem_range'_1.mp hiMem
  by_cases hmid : i < mid
  · exact List.all_eq_true.mp hleft i (List.mem_range'_1.mpr ⟨hil, by omega⟩)
  · exact List.all_eq_true.mp hright i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

end VOA.DeligneAudit.D4Two.Certificate
