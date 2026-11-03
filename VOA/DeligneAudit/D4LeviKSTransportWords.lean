import VOA.DeligneAudit.D4LeviKSTransport

/-! Exact Leibniz expansion for transport of ordered Levi-current words. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V)

/-- A Levi-current word with one factor replaced by its transported radical current. -/
noncomputable def transportedWord (f b : ℕ → Module.End ℂ V)
    (r : ℕ) : List ℕ → Module.End ℂ V
  | [] => 0
  | s :: ss => b (r + s) * (ss.map f).prod + f s * transportedWord f b r ss

/-- The adjoint action of E obeys the product Leibniz rule on every ordered word. -/
theorem eTransport_word_comm (f b : ℕ → Module.End ℂ V)
    (hfb : ∀ r s, eTransportOp ρ r * f s - f s * eTransportOp ρ r =
      b (r + s)) (r : ℕ) (ls : List ℕ) :
    eTransportOp ρ r * (ls.map f).prod -
      (ls.map f).prod * eTransportOp ρ r = transportedWord f b r ls := by
  induction ls with
  | nil => simp [transportedWord]
  | cons s ss ih =>
      simp only [List.map_cons, List.prod_cons, transportedWord]
      calc
        eTransportOp ρ r * (f s * (ss.map f).prod) -
            (f s * (ss.map f).prod) * eTransportOp ρ r =
          (eTransportOp ρ r * f s - f s * eTransportOp ρ r) *
            (ss.map f).prod +
          f s * (eTransportOp ρ r * (ss.map f).prod -
            (ss.map f).prod * eTransportOp ρ r) := by noncomm_ring
        _ = b (r + s) * (ss.map f).prod +
              f s * transportedWord f b r ss := by rw [hfb, ih]

/-- The f₂ word transports by replacing precisely one f₂ mode with X. -/
theorem eTransport_fTwo_word (r : ℕ) (ls : List ℕ) :
    eTransportOp ρ r * (ls.map (fOp ρ)).prod -
      (ls.map (fOp ρ)).prod * eTransportOp ρ r =
        transportedWord (fOp ρ) (xOp ρ) r ls :=
  eTransport_word_comm ρ (fOp ρ) (xOp ρ)
    (eTransport_fTwo_comm ρ) r ls

/-- The f₂₃₄ word transports by replacing precisely one factor with Y. -/
theorem eTransport_fTop_word (r : ℕ) (ls : List ℕ) :
    eTransportOp ρ r * (ls.map (fTopOp ρ)).prod -
      (ls.map (fTopOp ρ)).prod * eTransportOp ρ r =
        transportedWord (fTopOp ρ) (yOp ρ) r ls :=
  eTransport_word_comm ρ (fTopOp ρ) (yOp ρ)
    (eTransport_fTop_comm ρ) r ls

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.eTransport_word_comm
#print axioms VOA.DeligneAudit.D4Levi.eTransport_fTwo_word
#print axioms VOA.DeligneAudit.D4Levi.eTransport_fTop_word
