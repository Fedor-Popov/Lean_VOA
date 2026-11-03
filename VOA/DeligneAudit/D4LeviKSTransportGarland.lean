import VOA.DeligneAudit.D4LeviKSTransportWords

/-! Exact iterated transport of the two Levi Garland relations at the D4 source. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- Nested adjoint transport by a list of E modes. -/
noncomputable def iteratedETransport : List ℕ → Module.End ℂ V → Module.End ℂ V
  | [], G => G
  | r :: rs, G =>
      eTransportOp ρ r * iteratedETransport rs G -
        iteratedETransport rs G * eTransportOp ρ r

/-- A relation on the source remains an exact relation after any E transport. -/
theorem iteratedETransport_source_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (G : Module.End ℂ V) (hG : G w = 0) (rs : List ℕ) :
    iteratedETransport ρ rs G w = 0 := by
  induction rs with
  | nil => simpa [iteratedETransport] using hG
  | cons r rs ih =>
      simp only [iteratedETransport, LinearMap.sub_apply, Module.End.mul_apply,
        ih, map_zero, eTransport_source_zero ρ w m h r, sub_self]

/-- Every admissible f₂ Garland coefficient vanishes after arbitrary E transport. -/
theorem fTwo_garland_transport_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k s : ℕ) (hk : 1 ≤ k) (hks : m + 1 ≤ k + s) (rs : List ℕ) :
    iteratedETransport ρ rs
      (PowerSeries.coeff s (fCurrent (fOp ρ) ^ k)) w = 0 := by
  apply iteratedETransport_source_zero ρ w m h
  exact fTwo_garland_zero ρ w m h k s hk hks

/-- The corresponding exact transport of the f₂₃₄ Garland relation. -/
theorem fTop_garland_transport_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k s : ℕ) (hk : 1 ≤ k) (hks : m + 1 ≤ k + s) (rs : List ℕ) :
    iteratedETransport ρ rs
      (PowerSeries.coeff s (fCurrent (fTopOp ρ) ^ k)) w = 0 := by
  apply iteratedETransport_source_zero ρ w m h
  exact fTop_garland_zero ρ w m h k s hk hks

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.iteratedETransport_source_zero
#print axioms VOA.DeligneAudit.D4Levi.fTwo_garland_transport_zero
#print axioms VOA.DeligneAudit.D4Levi.fTop_garland_transport_zero
