/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterE6Inv1

/-!
# `E₆`: the `q = 1` Demazure count `∑ coeff C_m = 79^m`

* `C_1 = demazureChar … 1` is pinned to a literal letter by letter (`e6_s0`, …, one small
  `decide +kernel` per Demazure operator, in the files `DeligneCharacterE6Chain*`), giving `e6_char_one`;
* its invariance at `q = 1` under `s_θ` and the simple reflections is checked by the permutation
  criterion `inv_of_memChecks` (`memCheck` per letter);
* `DemCount.demazureChar_total` gives `C_m(1) = C_1(1)^m = 79^m`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.DemCount

open VOA.DeligneAudit.DeligneCharacter

theorem e6_char_one : demazureChar cartanE6 thetaE6 wordE6 1 = e6P21 := by
  rw [demazureChar_one]; exact e6_c21

theorem e6_good : Good 6 e6P21 := by
  have h := (toR1_demazureChar (r := 6) cartanE6 thetaE6 rfl wordE6 1).2
  rwa [e6_char_one] at h


theorem e6_memFin (i : ℕ) (hi : i ∈ wordE6) : memCheck (reflFin cartanE6 i) e6P21 = true := by
  have : i < 6 := by revert i; decide
  interval_cases i
  · exact e6_mem0
  · exact e6_mem1
  · exact e6_mem2
  · exact e6_mem3
  · exact e6_mem4
  · exact e6_mem5

theorem e6_total_one : (e6P21.map (·.2)).sum = 79 := by
  decide +kernel

/-- **`E₆`: the total multiplicity of `D(1, mθ)` is `79^m`.** -/
theorem e6_demazure_total (m : ℕ) :
    ((demazureChar cartanE6 thetaE6 wordE6 m).map (·.2)).sum = 79 ^ m := by
  have hinv := inv_of_memChecks cartanE6 thetaE6 rfl wordE6 _ e6_good e6_nodup
    (by decide) (by decide) e6_memθ e6_memFin
  rw [← e6_char_one] at hinv
  rw [demazureChar_total (r := 6) cartanE6 thetaE6 rfl wordE6
    (alpha_ne_zero_of cartanE6 thetaE6 wordE6 (by decide) ⟨⟨0, by omega⟩, by decide⟩) hinv m,
    e6_char_one, e6_total_one]

end VOA.DeligneAudit.DeligneCharacter.DemCount

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.DemCount.e6_demazure_total
end AxiomAudit
