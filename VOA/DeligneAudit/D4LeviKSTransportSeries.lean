import VOA.DeligneAudit.D4LeviKSTransportPower

/-! Full replacement of Garland powers by shifted radical currents. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V)

private theorem current_comm_of_coeff_comm (f b : ℕ → Module.End ℂ V)
    (h : ∀ i j, f i * b j = b j * f i) (r : ℕ) :
    fCurrent f * transportCurrent b r = transportCurrent b r * fCurrent f := by
  apply PowerSeries.ext
  intro s
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  simp only [fCurrent, transportCurrent, PowerSeries.coeff_mk]
  rw [← Finset.Nat.sum_antidiagonal_swap]
  apply Finset.sum_congr rfl
  intro p hp
  exact h p.2 (r + p.1)

private theorem current_e_comm (f b : ℕ → Module.End ℂ V)
    (h : ∀ r s, eTransportOp ρ r * f s - f s * eTransportOp ρ r =
      b (r + s)) (r : ℕ) :
    PowerSeries.C (eTransportOp ρ r) * fCurrent f -
      fCurrent f * PowerSeries.C (eTransportOp ρ r) = transportCurrent b r := by
  apply PowerSeries.ext
  intro s
  simp only [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
    fCurrent, transportCurrent, PowerSeries.coeff_mk]
  exact h r s

private theorem current_e_radical_comm (b : ℕ → Module.End ℂ V)
    (h : ∀ r s, eTransportOp ρ r * b s = b s * eTransportOp ρ r)
    (r q : ℕ) :
    PowerSeries.C (eTransportOp ρ r) * transportCurrent b q =
      transportCurrent b q * PowerSeries.C (eTransportOp ρ r) := by
  apply PowerSeries.ext
  intro s
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
    transportCurrent, PowerSeries.coeff_mk]
  exact h r (q + s)

private theorem iteratedAdjoint_coeff (rs : List ℕ)
    (F : PowerSeries (Module.End ℂ V)) (s : ℕ) :
    PowerSeries.coeff s
      (iteratedAdjoint (fun r => PowerSeries.C (eTransportOp ρ r)) rs F) =
        iteratedETransport ρ rs (PowerSeries.coeff s F) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [iteratedAdjoint, iteratedETransport, map_sub,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, ih]

/-- Partial transport leaves `n` Levi factors and replaces the others. -/
theorem garland_partial_transport (f b : ℕ → Module.End ℂ V)
    (hfb : ∀ r s, eTransportOp ρ r * f s - f s * eTransportOp ρ r =
      b (r + s))
    (hbb : ∀ r s, eTransportOp ρ r * b s = b s * eTransportOp ρ r)
    (hfbComm : ∀ r s, f r * b s = b s * f r)
    (rs : List ℕ) (n s : ℕ) :
    iteratedETransport ρ rs
      (PowerSeries.coeff s (fCurrent f ^ (n + rs.length))) =
        (n + rs.length).descFactorial rs.length •
          PowerSeries.coeff s
            (fCurrent f ^ n * (rs.map (transportCurrent b)).prod) := by
  let E : ℕ → PowerSeries (Module.End ℂ V) :=
    fun r => PowerSeries.C (eTransportOp ρ r)
  let F := fCurrent f
  let B : ℕ → PowerSeries (Module.End ℂ V) := transportCurrent b
  have hpower := iteratedAdjoint_power E B F
    (current_e_comm ρ f b hfb)
    (current_e_radical_comm ρ b hbb)
    (current_comm_of_coeff_comm f b hfbComm)
    rs n
  calc
    iteratedETransport ρ rs (PowerSeries.coeff s (F ^ (n + rs.length))) =
        PowerSeries.coeff s
          (iteratedAdjoint E rs (F ^ (n + rs.length))) := by
            exact (iteratedAdjoint_coeff ρ rs (F ^ (n + rs.length)) s).symm
    _ = PowerSeries.coeff s
          ((n + rs.length).descFactorial rs.length •
            (F ^ n * (rs.map B).prod)) := by rw [hpower]
    _ = (n + rs.length).descFactorial rs.length •
          PowerSeries.coeff s (F ^ n * (rs.map B).prod) := by
            simp only [map_nsmul]

/-- Partial f₂ transport gives the mixed f₂/X current polynomial. -/
theorem fTwo_garland_partial_transport (rs : List ℕ) (n s : ℕ) :
    iteratedETransport ρ rs
      (PowerSeries.coeff s (fCurrent (fOp ρ) ^ (n + rs.length))) =
        (n + rs.length).descFactorial rs.length •
          PowerSeries.coeff s
            (fCurrent (fOp ρ) ^ n *
              (rs.map (transportCurrent (xOp ρ))).prod) :=
  garland_partial_transport ρ (fOp ρ) (xOp ρ)
    (eTransport_fTwo_comm ρ)
    (fun r q => eTransport_radical_comm ρ 1 r q)
    (fOp_xOp_comm ρ) rs n s

/-- Partial f₂₃₄ transport gives the mixed f₂₃₄/Y current polynomial. -/
theorem fTop_garland_partial_transport (rs : List ℕ) (n s : ℕ) :
    iteratedETransport ρ rs
      (PowerSeries.coeff s (fCurrent (fTopOp ρ) ^ (n + rs.length))) =
        (n + rs.length).descFactorial rs.length •
          PowerSeries.coeff s
            (fCurrent (fTopOp ρ) ^ n *
              (rs.map (transportCurrent (yOp ρ))).prod) :=
  garland_partial_transport ρ (fTopOp ρ) (yOp ρ)
    (eTransport_fTop_comm ρ)
    (fun r q => eTransport_radical_comm ρ 4 r q)
    (fTop_y_comm ρ) rs n s

/-- K transports of a degree-K Garland power leave only radical currents. -/
theorem garland_full_transport (f b : ℕ → Module.End ℂ V)
    (hfb : ∀ r s, eTransportOp ρ r * f s - f s * eTransportOp ρ r =
      b (r + s))
    (hbb : ∀ r s, eTransportOp ρ r * b s = b s * eTransportOp ρ r)
    (hfbComm : ∀ r s, f r * b s = b s * f r)
    (rs : List ℕ) (s : ℕ) :
    iteratedETransport ρ rs
      (PowerSeries.coeff s (fCurrent f ^ rs.length)) =
        rs.length.factorial •
          PowerSeries.coeff s (rs.map (transportCurrent b)).prod := by
  let E : ℕ → PowerSeries (Module.End ℂ V) :=
    fun r => PowerSeries.C (eTransportOp ρ r)
  let F := fCurrent f
  let B : ℕ → PowerSeries (Module.End ℂ V) := transportCurrent b
  have hpower := iteratedAdjoint_power E B F
    (current_e_comm ρ f b hfb)
    (current_e_radical_comm ρ b hbb)
    (current_comm_of_coeff_comm f b hfbComm)
    rs 0
  simp only [zero_add, pow_zero, one_mul, Nat.descFactorial_self] at hpower
  calc
    iteratedETransport ρ rs (PowerSeries.coeff s (F ^ rs.length)) =
        PowerSeries.coeff s (iteratedAdjoint E rs (F ^ rs.length)) := by
          exact (iteratedAdjoint_coeff ρ rs (F ^ rs.length) s).symm
    _ = PowerSeries.coeff s (rs.length.factorial • (rs.map B).prod) := by rw [hpower]
    _ = rs.length.factorial • PowerSeries.coeff s (rs.map B).prod := by
          simp only [map_nsmul]

/-- The f₂ transport has the closed X-current form at every length. -/
theorem fTwo_garland_full_transport (rs : List ℕ) (s : ℕ) :
    iteratedETransport ρ rs
      (PowerSeries.coeff s (fCurrent (fOp ρ) ^ rs.length)) =
        rs.length.factorial •
          PowerSeries.coeff s (rs.map (transportCurrent (xOp ρ))).prod :=
  garland_full_transport ρ (fOp ρ) (xOp ρ)
    (eTransport_fTwo_comm ρ)
    (fun r q => eTransport_radical_comm ρ 1 r q)
    (fOp_xOp_comm ρ) rs s

/-- The f₂₃₄ transport has the closed Y-current form at every length. -/
theorem fTop_garland_full_transport (rs : List ℕ) (s : ℕ) :
    iteratedETransport ρ rs
      (PowerSeries.coeff s (fCurrent (fTopOp ρ) ^ rs.length)) =
        rs.length.factorial •
          PowerSeries.coeff s (rs.map (transportCurrent (yOp ρ))).prod :=
  garland_full_transport ρ (fTopOp ρ) (yOp ρ)
    (eTransport_fTop_comm ρ)
    (fun r q => eTransport_radical_comm ρ 4 r q)
    (fTop_y_comm ρ) rs s

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.garland_full_transport
#print axioms VOA.DeligneAudit.D4Levi.garland_partial_transport
#print axioms VOA.DeligneAudit.D4Levi.fTwo_garland_partial_transport
#print axioms VOA.DeligneAudit.D4Levi.fTop_garland_partial_transport
#print axioms VOA.DeligneAudit.D4Levi.fTwo_garland_full_transport
#print axioms VOA.DeligneAudit.D4Levi.fTop_garland_full_transport
