import VOA.DeligneAudit.D4FusionContactCurrentSL2
import VOA.DeligneAudit.D4FusionContactNilpotence
import VOA.DeligneAudit.D4FusionContactKnown

/-!
# Actual all-m highest-root nilpotence and all-mode center words

The existing E-calculus expresses a word of center currents of length n
through raising-current words applied to zero-mode powers of exponent
at least n. Sharp highest-root nilpotence therefore kills all such words
once n exceeds 2m. No finite-dimensionality premise is used.
-/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule contactF V} {w : V} {m : ℕ}

theorem current_center_pow_of_known (h : HighestRel R w m)
    (hknown : ∃ N, (currentCenter R 0 ^ N) w = 0) :
    (currentCenter R 0 ^ (2 * m + 1)) w = 0 := by
  obtain ⟨N, hN⟩ := hknown
  have hEF : ∀ v : V, currentHighestE R 0 (currentCenter R 0 v) -
      currentCenter R 0 (currentHighestE R 0 v) = currentHighestH R 0 v := by
    intro v
    exact congrArg (fun T : Module.End ℂ V => T v) (current_highest_EF R 0 0)
  have hHF : ∀ v : V, currentHighestH R 0 (currentCenter R 0 v) -
      currentCenter R 0 (currentHighestH R 0 v) = (-2 : ℂ) • currentCenter R 0 v := by
    intro v
    exact congrArg (fun T : Module.End ℂ V => T v) (current_highest_HF R 0 0)
  have hk : (currentCenter R 0)^[N] w = 0 := by
    simpa only [Module.End.pow_apply] using hN
  have hs := (VOA.DeligneAudit.CLFilt.hw_pow
    (currentHighestE R 0) (currentCenter R 0) (currentHighestH R 0)
    hEF hHF (current_highest_E_kills h 0) (current_highest_H_zero h) N hk).2
    (by positivity : 0 ≤ ((2 * m : ℕ) : ℤ))
  simpa only [Int.toNat_natCast, Module.End.pow_apply] using hs

/-- All center-current words beyond the sharp source weight vanish,
using the actual sl₂ current structure and the existing E-calculus. -/
theorem current_center_word_zero_of_pow (h : HighestRel R w m)
    (hpow : (currentCenter R 0 ^ (2 * m + 1)) w = 0)
    (l : List ℕ) (hl : 2 * m + 1 ≤ l.length) : ECalc.Fw (currentCenter R) l w = 0 := by
  have hv := ECalc.fword_mem_EW (current_highest_EF R) (current_highest_HF R)
    (current_highest_HE R) (current_center_comm R)
    (current_highest_E_kills h) (current_highest_H_pos h) l
  have hbot : ECalc.EW (currentHighestE R) (currentCenter R) w l.length l.sum ≤ ⊥ := by
    rw [ECalc.EW, Submodule.span_le]
    rintro _ ⟨q, _, _, rfl⟩
    have hpow' : (currentCenter R 0 ^ (l.length + q.length)) w = 0 := by
      obtain ⟨a, ha⟩ : ∃ a, l.length + q.length = a + (2 * m + 1) :=
        ⟨l.length + q.length - (2 * m + 1), by omega⟩
      rw [ha, pow_add, Module.End.mul_apply, hpow, map_zero]
    rw [hpow', map_zero]
    exact Submodule.zero_mem _
  exact hbot hv

variable {R : CurrentModule D4sector.f V}

theorem localWeyl_current_center_pow (h : LocalWeylRelG D4sector R w m) :
    (currentCenter R 0 ^ (2 * m + 1)) w = 0 :=
  current_center_pow_of_known (highestRel_of_localWeyl h) (localWeyl_center_local_nil h)

theorem localWeyl_current_center_word_zero (h : LocalWeylRelG D4sector R w m)
    (l : List ℕ) (hl : 2 * m + 1 ≤ l.length) : ECalc.Fw (currentCenter R) l w = 0 :=
  current_center_word_zero_of_pow (highestRel_of_localWeyl h)
    (localWeyl_current_center_pow h) l hl

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_current_center_pow
#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_current_center_word_zero
