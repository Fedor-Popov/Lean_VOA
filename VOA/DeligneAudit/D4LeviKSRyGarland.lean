import VOA.DeligneAudit.D4LeviKSRzGraded
import VOA.DeligneAudit.LeviTypeA3HighestLength

/-! The highest Levi-root Garland relation and its X-to-Z Wick conversion. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

noncomputable def fTopOp (r : ℕ) : Module.End ℂ V := -ρ.op (23 : Fin 28) r

private theorem a3_op_comm_end (σ : CurrentModule
    VOA.DeligneAudit.A3Sector.bracketTable V) (x y : Fin 15) (r s : ℕ) :
    σ.op x r * σ.op y s - σ.op y s * σ.op x r =
      ∑ e, VOA.DeligneAudit.A3Sector.bracketTable x y e • σ.op e (r + s) := by
  ext v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.smul_apply]
  exact σ.comm x y r s v

/-- The highest root of the Levi has Garland weight `m` at the D4 source. -/
theorem fTop_garland_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k s : ℕ) (hk : 1 ≤ k) (hks : m + 1 ≤ k + s) :
    (PowerSeries.coeff s (fCurrent (fTopOp ρ) ^ k)) w = 0 := by
  let σ := leviCurrent ρ
  let F : ℕ → Module.End ℂ V := fun t => σ.op
    (VOA.DeligneAudit.A3Sector.F 2) t
  let H : ℕ → Module.End ℂ V := fun t =>
    σ.op 12 t + σ.op 13 t + σ.op 14 t
  let E : Module.End ℂ V := σ.op 2 1
  have hFF : ∀ r t, F r * F t = F t * F r := by
    intro r t
    simpa [F, VOA.DeligneAudit.A3Sector.radicalOp] using
      VOA.DeligneAudit.A3Sector.radicalOp_comm σ 2 r 2 t
  have hEF : ∀ t, E * F t - F t * E = H (t + 1) := by
    intro t
    rw [a3_op_comm_end]
    simp [H, VOA.DeligneAudit.A3Sector.F, Fin.sum_univ_succ,
      VOA.DeligneAudit.A3Sector.a3_highest_ef_table, Nat.add_comm, add_assoc]
  have hHF : ∀ r t, H (r + 1) * F t - F t * H (r + 1) =
      (-2 : ℂ) • F (r + 1 + t) := by
    intro r t
    calc
      _ = (σ.op 12 (r + 1) * F t - F t * σ.op 12 (r + 1)) +
          (σ.op 13 (r + 1) * F t - F t * σ.op 13 (r + 1)) +
          (σ.op 14 (r + 1) * F t - F t * σ.op 14 (r + 1)) := by
            dsimp [H]
            noncomm_ring
      _ = (-2 : ℂ) • F (r + 1 + t) := by
        rw [a3_op_comm_end, a3_op_comm_end, a3_op_comm_end]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        simp_rw [← add_smul]
        simp [F, VOA.DeligneAudit.A3Sector.F,
          VOA.DeligneAudit.A3Sector.a3_highest_hf_table]
  have hE : E w = 0 :=
    (source_localWeyl ρ w m h).raising 2 (by decide) 1
  have hH : ∀ r, H (r + 1) w = 0 := by
    intro r
    change σ.op 12 (r + 1) w + σ.op 13 (r + 1) w +
      σ.op 14 (r + 1) w = 0
    rw [show σ.op 12 (r + 1) w = 0 by
      simpa [VOA.DeligneAudit.A3Sector.simpleH] using
        (source_localWeyl ρ w m h).cartan_pos 0 (r + 1) (by omega)]
    rw [show σ.op 13 (r + 1) w = 0 by
      simpa [VOA.DeligneAudit.A3Sector.simpleH] using
        (source_localWeyl ρ w m h).cartan_pos 1 (r + 1) (by omega)]
    rw [show σ.op 14 (r + 1) w = 0 by
      simpa [VOA.DeligneAudit.A3Sector.simpleH] using
        (source_localWeyl ρ w m h).cartan_pos 2 (r + 1) (by omega)]
    simp
  have hN : (F 0 ^ (m + 1)) w = 0 := by
    simpa [F, σ, VOA.DeligneAudit.A3Sector.weightABC,
      Module.End.pow_apply] using
      VOA.DeligneAudit.A3Sector.a3_highest_nilpotence σ w 0 m 0
        (source_localWeyl ρ w m h)
  have hg := VOA.DeligneAudit.Garland.garland hEF hHF hFF hE hH
    k hk hN s hks
  simpa [F, σ, fTopOp, fCurrent, VOA.DeligneAudit.Garland.Fs,
    VOA.DeligneAudit.A3Sector.F, leviCurrent, leviColour, leviSign] using hg

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.fTop_garland_zero
