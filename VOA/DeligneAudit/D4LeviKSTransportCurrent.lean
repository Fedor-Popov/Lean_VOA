import VOA.DeligneAudit.D4LeviKSTransportGarland

/-! The first transported Garland coefficient as an explicit current polynomial. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- The current whose coefficient at `s` is the shifted radical mode `b (r+s)`. -/
noncomputable def transportCurrent (b : ℕ → Module.End ℂ V) (r : ℕ) :
    PowerSeries (Module.End ℂ V) := PowerSeries.mk (fun s => b (r + s))

/-- Sum of all placements of one transported letter among `k` current factors. -/
noncomputable def oneTransportPower (F B : PowerSeries (Module.End ℂ V)) :
    ℕ → PowerSeries (Module.End ℂ V)
  | 0 => 0
  | k + 1 => oneTransportPower F B k * F + F ^ k * B

private theorem current_comm (f b : ℕ → Module.End ℂ V)
    (hfb : ∀ r s, eTransportOp ρ r * f s - f s * eTransportOp ρ r =
      b (r + s)) (r : ℕ) :
    PowerSeries.C (eTransportOp ρ r) * fCurrent f -
      fCurrent f * PowerSeries.C (eTransportOp ρ r) =
        transportCurrent b r := by
  apply PowerSeries.ext
  intro s
  simp only [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
    fCurrent, transportCurrent, PowerSeries.coeff_mk]
  exact hfb r s

/-- The first adjoint transport of a Garland power is the placement polynomial. -/
theorem oneTransportPower_eq_comm (f b : ℕ → Module.End ℂ V)
    (hfb : ∀ r s, eTransportOp ρ r * f s - f s * eTransportOp ρ r =
      b (r + s)) (r k : ℕ) :
    oneTransportPower (fCurrent f) (transportCurrent b r) k =
      PowerSeries.C (eTransportOp ρ r) * fCurrent f ^ k -
        fCurrent f ^ k * PowerSeries.C (eTransportOp ρ r) := by
  induction k with
  | zero => simp [oneTransportPower]
  | succ k ih =>
      have hc := current_comm ρ f b hfb r
      simp only [oneTransportPower, pow_succ]
      rw [ih, ← hc]
      noncomm_ring

/-- A single f₂ transport is the exact mixed X Garland relation. -/
theorem fTwo_one_transport_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k s r : ℕ) (hk : 1 ≤ k) (hks : m + 1 ≤ k + s) :
    (PowerSeries.coeff s
      (oneTransportPower (fCurrent (fOp ρ))
        (transportCurrent (xOp ρ) r) k)) w = 0 := by
  rw [oneTransportPower_eq_comm ρ (fOp ρ) (xOp ρ)
    (eTransport_fTwo_comm ρ) r k]
  have hg : (PowerSeries.coeff s (fCurrent (fOp ρ) ^ k)) w = 0 := by
    simpa [fOp] using fTwo_garland_zero ρ w m h k s hk hks
  simp only [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
    LinearMap.sub_apply, Module.End.mul_apply,
    eTransport_source_zero ρ w m h r, map_zero]
  rw [hg]
  simp

/-- A single f₂₃₄ transport is the exact mixed Y Garland relation. -/
theorem fTop_one_transport_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k s r : ℕ) (hk : 1 ≤ k) (hks : m + 1 ≤ k + s) :
    (PowerSeries.coeff s
      (oneTransportPower (fCurrent (fTopOp ρ))
        (transportCurrent (yOp ρ) r) k)) w = 0 := by
  rw [oneTransportPower_eq_comm ρ (fTopOp ρ) (yOp ρ)
    (eTransport_fTop_comm ρ) r k]
  simp only [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
    LinearMap.sub_apply, Module.End.mul_apply,
    fTop_garland_zero ρ w m h k s hk hks,
    eTransport_source_zero ρ w m h r, map_zero, sub_self]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.oneTransportPower_eq_comm
#print axioms VOA.DeligneAudit.D4Levi.fTwo_one_transport_zero
#print axioms VOA.DeligneAudit.D4Levi.fTop_one_transport_zero
