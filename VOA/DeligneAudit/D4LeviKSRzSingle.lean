import VOA.DeligneAudit.D4LeviKSRz
import VOA.DeligneAudit.D4LeviHigherPrefix

/-! The one-contraction Rz relation in the higher-key orbit. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- The positive-mode f₂ current kills the source at modes at least m. -/
theorem fTwo_source_mode_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (s : ℕ) (hs : m ≤ s) : ρ.op (18 : Fin 28) s w = 0 := by
  have hh := VOA.DeligneAudit.A3Sector.a3_simple_conversion_kill
    (leviCurrent ρ) w 0 m 0 (source_localWeyl ρ w m h)
    1 1 s (by omega) (by simpa [VOA.DeligneAudit.A3Sector.weightABC] using
      (show m < 1 + s by omega))
  simpa [VOA.DeligneAudit.LeviConversion.fCurrent, leviCurrent,
    leviColour, leviSign, VOA.DeligneAudit.A3Sector.simpleF] using hh

private def oneZKey (d : ℕ) : RadicalKey := ⟨0, 0, 0, 0, 0, 1, d⟩
private def oneYKey (d : ℕ) : RadicalKey := ⟨0, 0, 0, 0, 1, 0, d⟩

/-- The first Rz contraction is generated from the higher Y key by f₂. -/
theorem rz_single_z_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r s : ℕ) (hs : m ≤ s) :
    ρ.op (27 : Fin 28) (r + s) w ∈
      higherOrbit ρ w m (oneZKey (r + s)) := by
  let N := higherOrbit ρ w m (oneZKey (r + s))
  have hless : keyLess m (oneZKey (r + s)) (oneYKey r) := by
    left
    simp [keyHeight, oneZKey, oneYKey]
  have hy : ρ.op (26 : Fin 28) r w ∈ N := by
    have hmem : radicalWord ρ w [(4, r)] ∈
        keyLayer ρ w (oneYKey r) := by
      simpa [oneYKey, wordKey] using radicalWord_mem_key ρ w [(4, r)]
    have horbit := keyLayer_le_orbit ρ w (oneYKey r) hmem
    have hh := keyOrbit_le_higher ρ w m (oneZKey (r + s))
      (oneYKey r) hless horbit
    simpa [N, radicalWord, wordOp, radicalColour] using hh
  have hf : ρ.op (18 : Fin 28) s (ρ.op (26 : Fin 28) r w) ∈ N := by
    exact higherOrbit_full_levi_inv ρ w m (oneZKey (r + s))
      (18 : Fin 28) ⟨10, rfl⟩ s hy
  have hcomm := congrArg (fun T : Module.End ℂ V => T w)
    (fTwo_y_comm ρ s r)
  change (ρ.op (18 : Fin 28) s * ρ.op (26 : Fin 28) r -
      ρ.op (26 : Fin 28) r * ρ.op (18 : Fin 28) s) w =
        ρ.op (27 : Fin 28) (s + r) w at hcomm
  have hbr : ρ.op (18 : Fin 28) s (ρ.op (26 : Fin 28) r w) -
      ρ.op (26 : Fin 28) r (ρ.op (18 : Fin 28) s w) =
        ρ.op (27 : Fin 28) (r + s) w := by
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, Nat.add_comm] using hcomm
  rw [fTwo_source_mode_zero ρ w m h s hs, map_zero, sub_zero] at hbr
  exact hbr ▸ hf

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.fTwo_source_mode_zero
#print axioms VOA.DeligneAudit.D4Levi.rz_single_z_higher
