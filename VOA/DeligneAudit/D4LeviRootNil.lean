import VOA.DeligneAudit.D4LeviIntegrability

/-! Lemma I for all twelve negative root colours of the presented D4 module. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- Exponent mθ(hβ)+1 for the negative root colour c = fβ. -/
def rootExponent (m : ℕ) (c : Fin 28) : ℕ :=
  if c = 27 then 2 * m + 1 else
  if c = 16 ∨ c = 17 ∨ c = 19 then 1 else m + 1

/-- The two-step chain proves sharp powers for all six radical letters and
all six Levi lowering roots; the highest root uses the established D4 theta lemma. -/
theorem source_root_nil
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (c : Fin 28) (hc : 16 ≤ c.val) :
    ((ρ.op c 0) ^ rootExponent m c) w = 0 := by
  have hs : Sat D4sector.f ρ w (ravSpec D4sector m (2 * m)) := by
    simpa [ravFam] using h
  have hsimple (i : Fin 28) (hi : i = 16 ∨ i = 17 ∨ i = 19) :
      ρ.op i 0 w = 0 := by
    have hlow : D4sector.lowering i := by
      change 16 ≤ i.val ∧ i.val < 20
      rcases hi with rfl | rfl | rfl <;> decide
    have hnil := rs_lowering hs hlow
    have hexp : D4sector.lowExp i = 0 := by
      rcases hi with rfl | rfl | rfl <;> decide
    simpa [hexp, Function.iterate_one] using hnil
  have h16 := hsimple 16 (Or.inl rfl)
  have h17 := hsimple 17 (Or.inr (Or.inl rfl))
  have h19 := hsimple 19 (Or.inr (Or.inr rfl))
  have h18 : ((ρ.op (18 : Fin 28) 0) ^ (m + 1)) w = 0 := by
    have hnil := rs_lowering hs
      (by change 16 ≤ 18 ∧ 18 < 20; decide : D4sector.lowering (18 : Fin 28))
    simpa [D4sector, lowExpD4, Module.End.pow_apply] using hnil
  have h22 : ((ρ.op (22 : Fin 28) 0) ^ (m + 1)) w = 0 :=
    step_nil ρ 0 w (m + 1) (by simpa [stepA] using h19)
      (by simpa [stepB] using h18)
  have h21 : ((ρ.op (21 : Fin 28) 0) ^ (m + 1)) w = 0 :=
    step_nil ρ 1 w (m + 1) (by simpa [stepA] using h17)
      (by simpa [stepB] using h18)
  have h20 : ((ρ.op (20 : Fin 28) 0) ^ (m + 1)) w = 0 :=
    step_nil ρ 2 w (m + 1) (by simpa [stepA] using h16)
      (by simpa [stepB] using h18)
  have h23 : ((ρ.op (23 : Fin 28) 0) ^ (m + 1)) w = 0 :=
    step_nil ρ 3 w (m + 1) (by simpa [stepA] using h16)
      (by simpa [stepB] using h21)
  have h24 : ((ρ.op (24 : Fin 28) 0) ^ (m + 1)) w = 0 :=
    step_nil ρ 4 w (m + 1) (by simpa [stepA] using h16)
      (by simpa [stepB] using h22)
  have h25 : ((ρ.op (25 : Fin 28) 0) ^ (m + 1)) w = 0 :=
    step_nil ρ 5 w (m + 1) (by simpa [stepA] using h17)
      (by simpa [stepB] using h22)
  have h26 : ((ρ.op (26 : Fin 28) 0) ^ (m + 1)) w = 0 :=
    step_nil ρ 6 w (m + 1) (by simpa [stepA] using h19)
      (by simpa [stepB] using h23)
  have h27 : ((ρ.op (27 : Fin 28) 0) ^ (2 * m + 1)) w = 0 := by
    have ht := d4_thetaNil m V ρ w
      (fun e he => rs_raising hs he 0)
      (fun h hh => rs_cartan_zero hs hh)
      (fun h hh => rs_cartanN_zero hs hh)
      (fun i hi => rs_lowering hs hi)
    simpa [D4sector] using ht
  fin_cases c <;> simp [rootExponent, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27] at hc ⊢

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.source_root_nil
