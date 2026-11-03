import VOA.DeligneAudit.D4LeviKSTransportCurrent

/-! The first full-replacement case: two transports of a two-letter Levi word. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V)

/-- Two adjoint transports replace both factors, in the two possible orders. -/
theorem twoTransport_pair (f b : ℕ → Module.End ℂ V)
    (hfb : ∀ r s, eTransportOp ρ r * f s - f s * eTransportOp ρ r =
      b (r + s))
    (hbb : ∀ r s, eTransportOp ρ r * b s = b s * eTransportOp ρ r)
    (r q s t : ℕ) :
    iteratedETransport ρ [r, q] (f s * f t) =
      b (r + s) * b (q + t) + b (q + s) * b (r + t) := by
  have hq :
      iteratedETransport ρ [q] (f s * f t) =
        b (q + s) * f t + f s * b (q + t) := by
    simp only [iteratedETransport]
    rw [show eTransportOp ρ q * (f s * f t) -
        (f s * f t) * eTransportOp ρ q =
          (eTransportOp ρ q * f s - f s * eTransportOp ρ q) * f t +
          f s * (eTransportOp ρ q * f t - f t * eTransportOp ρ q) by
            noncomm_ring]
    rw [hfb, hfb]
  change eTransportOp ρ r * iteratedETransport ρ [q] (f s * f t) -
    iteratedETransport ρ [q] (f s * f t) * eTransportOp ρ r = _
  rw [hq]
  have hs := hfb r s
  have ht := hfb r t
  have hbs := hbb r (q + s)
  have hbt := hbb r (q + t)
  calc
    eTransportOp ρ r * (b (q + s) * f t + f s * b (q + t)) -
        (b (q + s) * f t + f s * b (q + t)) * eTransportOp ρ r =
      (eTransportOp ρ r * b (q + s) -
          b (q + s) * eTransportOp ρ r) * f t +
        b (q + s) * (eTransportOp ρ r * f t -
          f t * eTransportOp ρ r) +
        (eTransportOp ρ r * f s - f s * eTransportOp ρ r) * b (q + t) +
        f s * (eTransportOp ρ r * b (q + t) -
          b (q + t) * eTransportOp ρ r) := by noncomm_ring
    _ = b (r + s) * b (q + t) + b (q + s) * b (r + t) := by
      rw [sub_eq_zero.mpr hbs, sub_eq_zero.mpr hbt, hs, ht]
      simp [add_comm]

/-- The f₂ two-letter word has a complete X replacement after two E modes. -/
theorem twoTransport_fTwo_pair (r q s t : ℕ) :
    iteratedETransport ρ [r, q] (fOp ρ s * fOp ρ t) =
      xOp ρ (r + s) * xOp ρ (q + t) +
        xOp ρ (q + s) * xOp ρ (r + t) :=
  twoTransport_pair ρ (fOp ρ) (xOp ρ)
    (eTransport_fTwo_comm ρ)
    (fun r s => eTransport_radical_comm ρ 1 r s) r q s t

/-- The f₂₃₄ two-letter word has a complete Y replacement after two E modes. -/
theorem twoTransport_fTop_pair (r q s t : ℕ) :
    iteratedETransport ρ [r, q] (fTopOp ρ s * fTopOp ρ t) =
      yOp ρ (r + s) * yOp ρ (q + t) +
        yOp ρ (q + s) * yOp ρ (r + t) :=
  twoTransport_pair ρ (fTopOp ρ) (yOp ρ)
    (eTransport_fTop_comm ρ)
    (fun r s => eTransport_radical_comm ρ 4 r s) r q s t

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.twoTransport_pair
#print axioms VOA.DeligneAudit.D4Levi.twoTransport_fTwo_pair
#print axioms VOA.DeligneAudit.D4Levi.twoTransport_fTop_pair
