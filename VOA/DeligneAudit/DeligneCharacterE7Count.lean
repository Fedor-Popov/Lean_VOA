/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterE7Inv4

/-!
# `E₇`: the `q = 1` Demazure count `∑ coeff C_m = 134^m`

* `C_1 = demazureChar … 1` is pinned to a literal letter by letter (`e7_s0`, …, one small
  `decide +kernel` per Demazure operator, in the files `DeligneCharacterE7Chain*`), giving `e7_char_one`;
* its invariance at `q = 1` under `s_θ` and the simple reflections is checked by the permutation
  criterion `inv_of_memChecks` (`memCheck` per letter);
* `DemCount.demazureChar_total` gives `C_m(1) = C_1(1)^m = 134^m`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.DemCount

open VOA.DeligneAudit.DeligneCharacter

theorem e7_char_one : demazureChar cartanE7 thetaE7 wordE7 1 = e7P33 := by
  rw [demazureChar_one]; exact e7_c33

theorem e7_good : Good 7 e7P33 := by
  have h := (toR1_demazureChar (r := 7) cartanE7 thetaE7 rfl wordE7 1).2
  rwa [e7_char_one] at h


theorem e7_memFin (i : ℕ) (hi : i ∈ wordE7) : memCheck (reflFin cartanE7 i) e7P33 = true := by
  have : i < 7 := by revert i; decide
  interval_cases i
  · exact e7_mem0
  · exact e7_mem1
  · exact e7_mem2
  · exact e7_mem3
  · exact e7_mem4
  · exact e7_mem5
  · exact e7_mem6

theorem e7_total_one : (e7P33.map (·.2)).sum = 134 := by
  decide +kernel

/-- **`E₇`: the total multiplicity of `D(1, mθ)` is `134^m`.** -/
theorem e7_demazure_total (m : ℕ) :
    ((demazureChar cartanE7 thetaE7 wordE7 m).map (·.2)).sum = 134 ^ m := by
  have hinv := inv_of_memChecks cartanE7 thetaE7 rfl wordE7 _ e7_good e7_nodup
    (by decide) (by decide) e7_memθ e7_memFin
  rw [← e7_char_one] at hinv
  rw [demazureChar_total (r := 7) cartanE7 thetaE7 rfl wordE7
    (alpha_ne_zero_of cartanE7 thetaE7 wordE7 (by decide) ⟨⟨0, by omega⟩, by decide⟩) hinv m,
    e7_char_one, e7_total_one]

end VOA.DeligneAudit.DeligneCharacter.DemCount

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.DemCount.e7_demazure_total
end AxiomAudit
