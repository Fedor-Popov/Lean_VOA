import VOA.DeligneAudit.D4LeviKSRyGraded

/-! The node-one radical current transports both Levi Garland roots. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

noncomputable def eTransportOp (r : ℕ) : Module.End ℂ V :=
  -ρ.op (19 : Fin 28) r

/-- The signed E current kills the source at every mode. -/
theorem eTransport_source_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (r : ℕ) :
    eTransportOp ρ r w = 0 := by
  have he := radicalWord_zero_of_E ρ w m h [(0, r)] (by simp)
  simpa [eTransportOp, radicalWord, wordOp, radicalColour] using
    congrArg Neg.neg he

/-- E transports the f₂ current into the X current. -/
theorem eTransport_fTwo_comm (r s : ℕ) :
    eTransportOp ρ r * fOp ρ s - fOp ρ s * eTransportOp ρ r =
      xOp ρ (r + s) := by
  have hc : fOp ρ s * ρ.op (19 : Fin 28) r -
      ρ.op (19 : Fin 28) r * fOp ρ s = xOp ρ (r + s) := by
    ext v
    have h := ρ.comm (18 : Fin 28) (19 : Fin 28) s r v
    change ρ.op (18 : Fin 28) s (ρ.op (19 : Fin 28) r v) -
      ρ.op (19 : Fin 28) r (ρ.op (18 : Fin 28) s v) = _ at h
    change ρ.op (18 : Fin 28) s (ρ.op (19 : Fin 28) r v) -
      ρ.op (19 : Fin 28) r (ρ.op (18 : Fin 28) s v) = _
    rw [h]
    change (∑ c : Fin 28,
      fD4 (lowerColour 2) (radicalColour 0) c • ρ.op c (s + r) v) = _
    have hcoef (c : Fin 28) :
        fD4 (lowerColour 2) (radicalColour 0) c =
          if c = radicalColour 1 then (1 : ℂ) else 0 := by
      simpa [lowerAction] using lower_coefficient 2 0 c
    change (∑ c : Fin 28,
      fD4 (lowerColour 2) (radicalColour 0) c • ρ.op c (s + r) v) =
        ρ.op (radicalColour 1) (r + s) v
    simp only [hcoef, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Nat.add_comm]
  simpa [eTransportOp, fOp, xOp, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc] using hc

/-- E transports the signed f₂₃₄ current into the Y current. -/
theorem eTransport_fTop_comm (r s : ℕ) :
    eTransportOp ρ r * fTopOp ρ s -
      fTopOp ρ s * eTransportOp ρ r = yOp ρ (r + s) := by
  have hc : ρ.op (23 : Fin 28) s * ρ.op (19 : Fin 28) r -
      ρ.op (19 : Fin 28) r * ρ.op (23 : Fin 28) s =
        -yOp ρ (r + s) := by
    ext v
    have h := ρ.comm (23 : Fin 28) (19 : Fin 28) s r v
    change ρ.op (23 : Fin 28) s (ρ.op (19 : Fin 28) r v) -
      ρ.op (19 : Fin 28) r (ρ.op (23 : Fin 28) s v) = _ at h
    change ρ.op (23 : Fin 28) s (ρ.op (19 : Fin 28) r v) -
      ρ.op (19 : Fin 28) r (ρ.op (23 : Fin 28) s v) = _
    rw [h]
    change (∑ c : Fin 28,
      fD4 (lowerColour 5) (radicalColour 0) c • ρ.op c (s + r) v) = _
    have hcoef (c : Fin 28) :
        fD4 (lowerColour 5) (radicalColour 0) c =
          if c = radicalColour 4 then (-1 : ℂ) else 0 := by
      simpa [lowerAction] using lower_coefficient 5 0 c
    change (∑ c : Fin 28,
      fD4 (lowerColour 5) (radicalColour 0) c • ρ.op c (s + r) v) =
        -ρ.op (radicalColour 4) (r + s) v
    simp only [hcoef, ite_smul, neg_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Nat.add_comm]
  have hs : ρ.op (19 : Fin 28) r * ρ.op (23 : Fin 28) s -
      ρ.op (23 : Fin 28) s * ρ.op (19 : Fin 28) r =
        yOp ρ (r + s) := by
    rw [← neg_sub, hc]
    simp
  simpa [eTransportOp, fTopOp] using hs

/-- Transport is square-zero on every radical current, since the radical is abelian. -/
theorem eTransport_radical_comm (j : Fin 6) (r s : ℕ) :
    eTransportOp ρ r * ρ.op (radicalColour j) s =
      ρ.op (radicalColour j) s * eTransportOp ρ r := by
  ext v
  have hc := radical_ops_comm ρ 0 j r s v
  change ρ.op (19 : Fin 28) r (ρ.op (radicalColour j) s v) =
    ρ.op (radicalColour j) s (ρ.op (19 : Fin 28) r v) at hc
  simpa [eTransportOp] using congrArg Neg.neg hc

theorem eTransport_fTwo_second (r q s : ℕ) :
    eTransportOp ρ r *
      (eTransportOp ρ q * fOp ρ s - fOp ρ s * eTransportOp ρ q) -
      (eTransportOp ρ q * fOp ρ s - fOp ρ s * eTransportOp ρ q) *
        eTransportOp ρ r = 0 := by
  rw [eTransport_fTwo_comm]
  exact sub_eq_zero.mpr (eTransport_radical_comm ρ 1 r (q + s))

theorem eTransport_fTop_second (r q s : ℕ) :
    eTransportOp ρ r *
      (eTransportOp ρ q * fTopOp ρ s - fTopOp ρ s * eTransportOp ρ q) -
      (eTransportOp ρ q * fTopOp ρ s - fTopOp ρ s * eTransportOp ρ q) *
        eTransportOp ρ r = 0 := by
  rw [eTransport_fTop_comm]
  exact sub_eq_zero.mpr (eTransport_radical_comm ρ 4 r (q + s))

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.eTransport_source_zero
#print axioms VOA.DeligneAudit.D4Levi.eTransport_fTwo_comm
#print axioms VOA.DeligneAudit.D4Levi.eTransport_fTop_comm
#print axioms VOA.DeligneAudit.D4Levi.eTransport_radical_comm
#print axioms VOA.DeligneAudit.D4Levi.eTransport_fTwo_second
#print axioms VOA.DeligneAudit.D4Levi.eTransport_fTop_second
