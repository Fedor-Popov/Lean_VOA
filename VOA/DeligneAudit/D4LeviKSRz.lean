import VOA.DeligneAudit.D4LeviKSSource
import VOA.DeligneAudit.D4LeviSource
import VOA.DeligneAudit.LeviTypeA3ConversionKill
import VOA.DeligneAudit.LeviConversionTop

/-! The concrete f₂ conversion of Y currents into Z currents. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

private noncomputable def fTwo (r : ℕ) : Module.End ℂ V :=
  ρ.op (18 : Fin 28) r
private noncomputable def yCurrent (r : ℕ) : Module.End ℂ V :=
  ρ.op (26 : Fin 28) r
private noncomputable def zCurrent (r : ℕ) : Module.End ℂ V :=
  ρ.op (27 : Fin 28) r

/-- In the actual D4 colours, the f₂ current converts Y into Z. -/
theorem fTwo_y_comm (r s : ℕ) :
    fTwo ρ r * yCurrent ρ s - yCurrent ρ s * fTwo ρ r =
      zCurrent ρ (r + s) := by
  ext v
  have hc := ρ.comm (18 : Fin 28) (26 : Fin 28) r s v
  change ρ.op (18 : Fin 28) r (ρ.op (26 : Fin 28) s v) -
    ρ.op (26 : Fin 28) s (ρ.op (18 : Fin 28) r v) = _
  rw [hc]
  change (∑ c : Fin 28,
    fD4 (lowerColour 2) (radicalColour 4) c • ρ.op c (r + s) v) = _
  have hcoef (c : Fin 28) :
      fD4 (lowerColour 2) (radicalColour 4) c =
        if c = radicalColour 5 then (1 : ℂ) else 0 := by
    simpa [lowerAction] using lower_coefficient 2 4 c
  change (∑ c : Fin 28,
    fD4 (lowerColour 2) (radicalColour 4) c • ρ.op c (r + s) v) =
      ρ.op (radicalColour 5) (r + s) v
  simp only [hcoef, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The converted Z current commutes with f₂. -/
theorem fTwo_z_comm (r s : ℕ) :
    fTwo ρ r * zCurrent ρ s = zCurrent ρ s * fTwo ρ r := by
  apply sub_eq_zero.mp
  ext v
  have hc := ρ.comm (18 : Fin 28) (27 : Fin 28) r s v
  change ρ.op (18 : Fin 28) r (ρ.op (27 : Fin 28) s v) -
    ρ.op (27 : Fin 28) s (ρ.op (18 : Fin 28) r v) = 0
  rw [hc]
  change (∑ c : Fin 28,
    fD4 (lowerColour 2) (radicalColour 5) c • ρ.op c (r + s) v) = 0
  simp [lower_coefficient, lowerAction]

/-- The f₂ Garland coefficient vanishes at the D4 source above weight m. -/
theorem fTwo_garland_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k s : ℕ) (hk : 1 ≤ k) (hks : m + 1 ≤ k + s) :
    (PowerSeries.coeff s (fCurrent (fTwo ρ) ^ k)) w = 0 := by
  have hh := VOA.DeligneAudit.A3Sector.a3_simple_conversion_kill
    (leviCurrent ρ) w 0 m 0 (source_localWeyl ρ w m h)
    1 k s hk (by simpa [VOA.DeligneAudit.A3Sector.weightABC] using hks)
  simpa [fTwo, leviCurrent, leviColour, leviSign,
    VOA.DeligneAudit.A3Sector.simpleF] using hh

/-- Exact f₂ Wick identity, before absorption of the lower contraction terms. -/
theorem rz_wick_identity
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k s : ℕ) (xs : List ℕ) (hk : 1 ≤ k)
    (hks : m + 1 ≤ k + s) :
    (((-1 : Module.End ℂ V) ^ k * (k.factorial : Module.End ℂ V)) *
      topSum (yCurrent ρ) (zCurrent ρ) k s xs) w =
      -(lowerSum (fTwo ρ) (yCurrent ρ) (zCurrent ρ) k s xs w) := by
  have h := lemmaC (fTwo ρ) (yCurrent ρ) (zCurrent ρ)
    (fTwo_y_comm ρ) (fTwo_z_comm ρ)
    (fun i j => by
      ext v
      simpa [yCurrent, zCurrent] using radical_ops_comm ρ 4 5 i j v)
    k s xs 1 w (by intro i; simp)
    (fTwo_garland_zero ρ w m h k s hk hks)
  simpa only [one_mul, Module.End.one_apply, Module.End.mul_apply,
    LinearMap.neg_apply] using h

/-- The same exact conversion with any spectator commuting with f₂. -/
theorem rz_wick_identity_spectator
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k s : ℕ) (xs : List ℕ) (R : Module.End ℂ V)
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hR : ∀ r, R * fTwo ρ r = fTwo ρ r * R) :
    (((-1 : Module.End ℂ V) ^ k * (k.factorial : Module.End ℂ V)) *
      topSum (yCurrent ρ) (zCurrent ρ) k s xs) (R w) =
      -(lowerSum (fTwo ρ) (yCurrent ρ) (zCurrent ρ) k s xs (R w)) := by
  have hh := lemmaC (fTwo ρ) (yCurrent ρ) (zCurrent ρ)
    (fTwo_y_comm ρ) (fTwo_z_comm ρ)
    (fun i j => by
      ext v
      simpa [yCurrent, zCurrent] using radical_ops_comm ρ 4 5 i j v)
    k s xs R w hR (fTwo_garland_zero ρ w m h k s hk hks)
  simpa only [Module.End.mul_apply, LinearMap.neg_apply] using hh

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.fTwo_y_comm
#print axioms VOA.DeligneAudit.D4Levi.fTwo_z_comm
#print axioms VOA.DeligneAudit.D4Levi.fTwo_garland_zero
#print axioms VOA.DeligneAudit.D4Levi.rz_wick_identity
#print axioms VOA.DeligneAudit.D4Levi.rz_wick_identity_spectator
