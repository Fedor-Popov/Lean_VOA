/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4FusionCountChain3

/-!
# `F₄`: the `q = 1` Demazure count `∑ coeff C_m = 53^m`

`C_1 = demazureChar … 1` is pinned letter by letter (`F4FusionCountChain0..3`), its invariance under
`s_θ` and the simple reflections is checked by `inv_of_memChecks`, and
`DemCount.demazureChar_total` gives `C_m(1) = C_1(1)^m = 53^m`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.DemCount

open VOA.DeligneAudit.DeligneCharacter

theorem f4_nodup : f4P15.Nodup := by decide +kernel

theorem f4_memθ : memCheck (reflZero cartanF4 thetaF4) f4P15 = true := by decide +kernel

theorem f4_mem0 : memCheck (reflFin cartanF4 0) f4P15 = true := by decide +kernel

theorem f4_mem1 : memCheck (reflFin cartanF4 1) f4P15 = true := by decide +kernel

theorem f4_mem2 : memCheck (reflFin cartanF4 2) f4P15 = true := by decide +kernel

theorem f4_mem3 : memCheck (reflFin cartanF4 3) f4P15 = true := by decide +kernel

theorem f4_char_one : demazureChar cartanF4 thetaF4 wordF4 1 = f4P15 := by
  rw [demazureChar_one]; exact f4_c15

theorem f4_good : Good 4 f4P15 := by
  have h := (toR1_demazureChar (r := 4) cartanF4 thetaF4 rfl wordF4 1).2
  rwa [f4_char_one] at h

theorem f4_memFin (i : ℕ) (hi : i ∈ wordF4) : memCheck (reflFin cartanF4 i) f4P15 = true := by
  have : i < 4 := by revert i; decide
  interval_cases i
  · exact f4_mem0
  · exact f4_mem1
  · exact f4_mem2
  · exact f4_mem3

theorem f4_total_one : (f4P15.map (·.2)).sum = 53 := by
  decide +kernel

/-- **`F₄`: the total multiplicity of `D(1, mθ)` is `53^m`.** -/
theorem f4_demazure_total (m : ℕ) :
    ((demazureChar cartanF4 thetaF4 wordF4 m).map (·.2)).sum = 53 ^ m := by
  have hinv := inv_of_memChecks cartanF4 thetaF4 rfl wordF4 _ f4_good f4_nodup
    (by decide) (by decide) f4_memθ f4_memFin
  rw [← f4_char_one] at hinv
  rw [demazureChar_total (r := 4) cartanF4 thetaF4 rfl wordF4
    (alpha_ne_zero_of cartanF4 thetaF4 wordF4 (by decide) ⟨⟨0, by omega⟩, by decide⟩) hinv m,
    f4_char_one, f4_total_one]

end VOA.DeligneAudit.DeligneCharacter.DemCount

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.DemCount.f4_demazure_total
end AxiomAudit
