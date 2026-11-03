import VOA.DeligneAudit.D4LeviKSRyGarland

/-! The exact highest-Levi-root Wick identity before higher-key absorption. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- The signed highest Levi lowering current converts X to Z. -/
theorem fTop_x_comm (r s : ℕ) :
    fTopOp ρ r * xOp ρ s - xOp ρ s * fTopOp ρ r =
      zOp ρ (r + s) := by
  have hc : ρ.op (23 : Fin 28) r * xOp ρ s -
      xOp ρ s * ρ.op (23 : Fin 28) r = -zOp ρ (r + s) := by
    ext v
    have h := ρ.comm (23 : Fin 28) (22 : Fin 28) r s v
    change ρ.op (23 : Fin 28) r (ρ.op (22 : Fin 28) s v) -
      ρ.op (22 : Fin 28) s (ρ.op (23 : Fin 28) r v) = _ at h
    change ρ.op (23 : Fin 28) r (ρ.op (22 : Fin 28) s v) -
      ρ.op (22 : Fin 28) s (ρ.op (23 : Fin 28) r v) = _
    rw [h]
    change (∑ c : Fin 28,
      fD4 (lowerColour 5) (radicalColour 1) c • ρ.op c (r + s) v) = _
    have hcoef (c : Fin 28) :
        fD4 (lowerColour 5) (radicalColour 1) c =
          if c = radicalColour 5 then (-1 : ℂ) else 0 := by
      simpa [lowerAction] using lower_coefficient 5 1 c
    change (∑ c : Fin 28,
      fD4 (lowerColour 5) (radicalColour 1) c • ρ.op c (r + s) v) =
        -ρ.op (radicalColour 5) (r + s) v
    simp only [hcoef, ite_smul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, neg_smul, one_smul, zero_smul]
  calc
    fTopOp ρ r * xOp ρ s - xOp ρ s * fTopOp ρ r =
        -(ρ.op (23 : Fin 28) r * xOp ρ s -
          xOp ρ s * ρ.op (23 : Fin 28) r) := by
            simp [fTopOp]
            abel
    _ = zOp ρ (r + s) := by rw [hc]; simp

/-- The full-contraction colour Z commutes with the signed current. -/
theorem fTop_z_comm (r s : ℕ) :
    fTopOp ρ r * zOp ρ s = zOp ρ s * fTopOp ρ r := by
  have hc : ρ.op (23 : Fin 28) r * zOp ρ s -
      zOp ρ s * ρ.op (23 : Fin 28) r = 0 := by
    ext v
    have h := ρ.comm (23 : Fin 28) (27 : Fin 28) r s v
    change ρ.op (23 : Fin 28) r (ρ.op (27 : Fin 28) s v) -
      ρ.op (27 : Fin 28) s (ρ.op (23 : Fin 28) r v) = _ at h
    change ρ.op (23 : Fin 28) r (ρ.op (27 : Fin 28) s v) -
      ρ.op (27 : Fin 28) s (ρ.op (23 : Fin 28) r v) = 0
    rw [h]
    change (∑ c : Fin 28,
      fD4 (lowerColour 5) (radicalColour 5) c • ρ.op c (r + s) v) = 0
    simp [lower_coefficient, lowerAction]
  apply sub_eq_zero.mp
  calc
    fTopOp ρ r * zOp ρ s - zOp ρ s * fTopOp ρ r =
        -(ρ.op (23 : Fin 28) r * zOp ρ s -
          zOp ρ s * ρ.op (23 : Fin 28) r) := by
            simp [fTopOp]
            abel
    _ = 0 := by rw [hc]; simp

/-- Exact Wick conversion on an arbitrary spectator commuting with f₂₃₄. -/
theorem ry_wick_identity_spectator
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k s : ℕ) (xs : List ℕ) (R : Module.End ℂ V)
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hR : ∀ r, R * fTopOp ρ r = fTopOp ρ r * R) :
    (((-1 : Module.End ℂ V) ^ k * (k.factorial : Module.End ℂ V)) *
      topSum (xOp ρ) (zOp ρ) k s xs) (R w) =
      -(lowerSum (fTopOp ρ) (xOp ρ) (zOp ρ) k s xs (R w)) := by
  have hh := lemmaC (fTopOp ρ) (xOp ρ) (zOp ρ)
    (fTop_x_comm ρ) (fTop_z_comm ρ)
    (fun i j => by
      ext v
      simpa [xOp, zOp] using radical_ops_comm ρ 1 5 i j v)
    k s xs R w hR (fTop_garland_zero ρ w m h k s hk hks)
  simpa only [Module.End.mul_apply, LinearMap.neg_apply] using hh

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.fTop_x_comm
#print axioms VOA.DeligneAudit.D4Levi.fTop_z_comm
#print axioms VOA.DeligneAudit.D4Levi.ry_wick_identity_spectator
