import VOA.DeligneAudit.LeviTypeA2CertKeyNil

/-! Local nilpotence of the node-two zero-mode lowering on the cyclic module. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.FiniteG
open VOA.DeligneAudit.DeligneSector

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- Every vector in the cyclic module is killed by a power of `f₂(0)`. -/
theorem a2_cyc_lowering_locally_nilpotent (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) {v : V}
    (hv : v ∈ VOA.DeligneAudit.UnivG.cycSubG ρ w) :
    ∃ N : ℕ, (ρ.op 4 0 ^ N) v = 0 := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, rfl⟩ := hz
      have hw : (ρ.op 4 0 ^ (q + 1)) w = 0 := by
        simpa [Module.End.pow_apply] using h.lowering_second
      have hwt : A2sector.wt (4 : Fin 8) ≠ 0 := by decide
      refine ⟨q + 1 + adK A2sector * l.length, ?_⟩
      exact pow_kill_word (S := A2sector) ρ
        (⟨4, by decide⟩ : Fin A2sector.n) hwt hw l
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨Nx, hx⟩ := hx
      obtain ⟨Ny, hy⟩ := hy
      refine ⟨max Nx Ny, ?_⟩
      rw [map_add, pow_kill_mono _ hx (le_max_left Nx Ny),
        pow_kill_mono _ hy (le_max_right Nx Ny), add_zero]
  | smul c x _ hx =>
      obtain ⟨N, hx⟩ := hx
      exact ⟨N, by rw [map_smul, hx, smul_zero]⟩

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_cyc_lowering_locally_nilpotent
