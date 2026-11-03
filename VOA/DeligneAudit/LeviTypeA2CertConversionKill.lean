import VOA.DeligneAudit.LeviTypeA2CertOrderedStepRank
import VOA.DeligneAudit.LeviConversionBoxTopMain

/-! The simple node-two current supplies the vanishing input to box conversion. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

theorem a2_node2_conversion_kill (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (r s : ℕ)
    (hr : 1 ≤ r) (hrs : q + 1 ≤ r + s) :
    PowerSeries.coeff s
      (VOA.DeligneAudit.LeviConversion.fCurrent (fun t => ρ.op 4 t) ^ r) • w = 0 := by
  let E : ℕ → Module.End ℂ V := fun t => ρ.op 1 t
  let H : ℕ → Module.End ℂ V := fun t => ρ.op 7 t
  let F : ℕ → Module.End ℂ V := fun t => ρ.op 4 t
  have hS : VOA.DeligneAudit.CVsl2.SL2 E H F := a2_node2_sl2 ρ
  have hEF : ∀ k, E 1 * F k - F k * E 1 = H (k + 1) := by
    intro k
    simpa [E, H, F, Nat.add_comm] using hS.hEF 1 k
  have hHF : ∀ m k, H (m + 1) * F k - F k * H (m + 1) =
      (-2 : ℂ) • F (m + 1 + k) := by
    intro m k
    exact hS.hHF (m + 1) k
  have hN : (F 0 ^ (q + 1)) w = 0 := by
    simpa [F, Module.End.pow_apply] using h.lowering_second
  have hkill := VOA.DeligneAudit.Garland.garland hEF hHF hS.hFF
    (h.raising 1 (by decide) 1)
    (fun m => h.cartan_pos 7 (by decide) (m + 1) (by omega))
    r hr hN s hrs
  simpa [VOA.DeligneAudit.LeviConversion.fCurrent,
    VOA.DeligneAudit.Garland.Fs, F] using hkill

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_node2_conversion_kill
