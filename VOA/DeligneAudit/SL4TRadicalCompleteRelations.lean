import VOA.DeligneAudit.SL4TRadicalConversionRelations
import VOA.DeligneAudit.SL4TRadicalModeEvaluation

/-! Complete-function source relations and unsupported zero-mode vectors. -/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviConversion

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- The all-zero radical word at a fixed count triple. -/
def radicalZeroModeVector (d : Fin 3 → ℕ) : V :=
  (ρ.op (F 0) 0 ^ d 0 * ρ.op (F 1) 0 ^ d 1 * ρ.op (F 2) 0 ^ d 2) w

/-- The complete-function source in one alphabet, with the other modes zero. -/
def radicalCompleteSource (d : Fin 3 → ℕ) (j : Fin 3) (s : ℕ) : V :=
  if j = 0 then
    (PowerSeries.coeff s (fCurrent (fun t => ρ.op (F 0) t) ^ d 0) *
      ρ.op (F 1) 0 ^ d 1 * ρ.op (F 2) 0 ^ d 2) w
  else if j = 1 then
    (ρ.op (F 0) 0 ^ d 0 *
      PowerSeries.coeff s (fCurrent (fun t => ρ.op (F 1) t) ^ d 1) *
        ρ.op (F 2) 0 ^ d 2) w
  else
    (ρ.op (F 1) 0 ^ d 1 *
      PowerSeries.coeff s (fCurrent (fun t => ρ.op (F 2) t) ^ d 2) *
        ρ.op (F 0) 0 ^ d 0) w

/-- Garland on the first simple root with arbitrary zero-mode radical spectators. -/
theorem radicalCompleteSource_first_zero (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (s : ℕ) (hd : 1 ≤ d 0) (hs : a + 1 ≤ d 0 + s) :
    radicalCompleteSource ρ w d 0 s = 0 := by
  let R := ρ.op (F 1) 0 ^ d 1 * ρ.op (F 2) 0 ^ d 2
  have hc (t : ℕ) : R * ρ.op (F 0) t = ρ.op (F 0) t * R :=
    ((show Commute (ρ.op (F 1) 0) (ρ.op (F 0) t) from
      a3_conversion_radical_comm ρ 1 0 0 t).pow_left (d 1)).mul_left
      ((show Commute (ρ.op (F 2) 0) (ρ.op (F 0) t) from
        a3_conversion_radical_comm ρ 2 0 0 t).pow_left (d 2))
  have hk := a3_simple_conversion_kill ρ w a b c h 0 (d 0) s hd hs
  have he := spectator_comm_coeff (fun t => ρ.op (F 0) t) R hc (d 0) s
  change (PowerSeries.coeff s (fCurrent (fun t => ρ.op (F 0) t) ^ d 0) *
    ρ.op (F 1) 0 ^ d 1 * ρ.op (F 2) 0 ^ d 2) w = 0
  rw [mul_assoc, ← he, Module.End.mul_apply]
  change R (PowerSeries.coeff s
    (fCurrent (fun t => ρ.op (simpleF 0) t) ^ d 0) • w) = 0
  rw [hk, map_zero]

/-- All three complete-function source relations vanish modulo earlier radical counts. -/
theorem radicalCompleteSource_mem_higher (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (j : Fin 3) (s : ℕ) (hd : 1 ≤ d j)
    (hs : weightABC a b c j + 1 ≤ d j + s) :
    radicalCompleteSource ρ w d j s ∈ higherRadicalCountClosure ρ w d := by
  fin_cases j
  · change radicalCompleteSource ρ w d 0 s ∈ higherRadicalCountClosure ρ w d
    rw [radicalCompleteSource_first_zero ρ w a b c h d s hd hs]
    exact Submodule.zero_mem _
  · have he : radicalConversionCounts 0 (d 1) (List.replicate (d 0) 0) []
        (List.replicate (d 2) 0) = d := by
      funext i
      fin_cases i <;> simp [radicalConversionCounts]
    have hm := radicalConversion_zero_modes ρ w a b c h 0 (d 0) (d 1) s hd hs
      [] (List.replicate (d 2) 0)
    rw [he] at hm
    simpa [boxTarget, aWord, a3ConvA, a3ConvB, a3ConvSpectator,
      radicalCompleteSource, Module.End.mul_apply] using hm
  · have he : radicalConversionCounts 1 (d 2) (List.replicate (d 1) 0) []
        (List.replicate (d 0) 0) = d := by
      funext i
      fin_cases i <;> simp [radicalConversionCounts]
    have hm := radicalConversion_zero_modes ρ w a b c h 1 (d 1) (d 2) s hd hs
      [] (List.replicate (d 0) 0)
    rw [he] at hm
    simpa [boxTarget, aWord, a3ConvA, a3ConvB, a3ConvSpectator,
      radicalCompleteSource, Module.End.mul_apply] using hm

/-- The constant complete-function coefficient is the all-zero radical vector. -/
theorem radicalCompleteSource_zero (d : Fin 3 → ℕ) (j : Fin 3) :
    radicalCompleteSource ρ w d j 0 = radicalZeroModeVector ρ w d := by
  have hc : ∀ i : Fin 3, PowerSeries.coeff 0
      (fCurrent (fun t => ρ.op (F i) t) ^ d i) = ρ.op (F i) 0 ^ d i := by
    intro i
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
    rfl
  unfold radicalCompleteSource
  split_ifs
  · rw [hc]
    rfl
  · rw [hc]
    rfl
  · rw [hc]
    unfold radicalZeroModeVector
    have h₁ : Commute (ρ.op (F 1) 0 ^ d 1) (ρ.op (F 0) 0 ^ d 0) :=
      ((show Commute (ρ.op (F 1) 0) (ρ.op (F 0) 0) from
        a3_conversion_radical_comm ρ 1 0 0 0).pow_left _).pow_right _
    have h₂ : Commute (ρ.op (F 2) 0 ^ d 2) (ρ.op (F 0) 0 ^ d 0) :=
      ((show Commute (ρ.op (F 2) 0) (ρ.op (F 0) 0) from
        a3_conversion_radical_comm ρ 2 0 0 0).pow_left _).pow_right _
    rw [(h₁.mul_left h₂).eq, mul_assoc]

/-- Unsupported count triples already kill the all-zero multiplicity vector. -/
theorem radicalZeroModeVector_mem_higher_of_unsupported (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (hd : a < d 0 ∨ b < d 1 ∨ c < d 2) :
    radicalZeroModeVector ρ w d ∈ higherRadicalCountClosure ρ w d := by
  rcases hd with hd | hd | hd
  · rw [← radicalCompleteSource_zero ρ w d 0]
    exact radicalCompleteSource_mem_higher ρ w a b c h d 0 0
      (by omega) (by simpa [weightABC] using hd)
  · rw [← radicalCompleteSource_zero ρ w d 1]
    exact radicalCompleteSource_mem_higher ρ w a b c h d 1 0
      (by omega) (by simpa [weightABC] using hd)
  · rw [← radicalCompleteSource_zero ρ w d 2]
    exact radicalCompleteSource_mem_higher ρ w a b c h d 2 0
      (by omega) (by simpa [weightABC] using hd)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.radicalCompleteSource_first_zero
#print axioms VOA.DeligneAudit.SL4T.radicalCompleteSource_mem_higher
#print axioms VOA.DeligneAudit.SL4T.radicalCompleteSource_zero
#print axioms VOA.DeligneAudit.SL4T.radicalZeroModeVector_mem_higher_of_unsupported
