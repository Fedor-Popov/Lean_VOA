import VOA.DeligneAudit.LeviTypeA2CertCycNil
import VOA.DeligneAudit.LeviTypeA2CertKeyWeight
import VOA.DeligneAudit.DeligneFusionCLFilt

/-! Zero-mode local Weyl relations on a radical key modulo a Levi-stable submodule. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- The highest-weight power for a key vector in any quotient killing higher keys
and stable under the node-two `sl₂` zero modes. Negative weights vanish there. -/
theorem a2_key_lowering_sharp_mod (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k : A2RadicalKey)
    (N : Submodule ℂ V)
    (hHigher : a2HigherKeySpan ρ w q k ≤ N)
    (hE : N ≤ N.comap (ρ.op 1 0))
    (hF : N ≤ N.comap (ρ.op 4 0))
    (hH : N ≤ N.comap (ρ.op 7 0))
    {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    (a2KeyHeight q k < 0 → v ∈ N) ∧
      (0 ≤ a2KeyHeight q k →
        (ρ.op 4 0 ^ ((a2KeyHeight q k).toNat + 1)) v ∈ N) := by
  let E : Module.End ℂ (V ⧸ N) := N.mapQ N (ρ.op 1 0) hE
  let F : Module.End ℂ (V ⧸ N) := N.mapQ N (ρ.op 4 0) hF
  let H : Module.End ℂ (V ⧸ N) := N.mapQ N (ρ.op 7 0) hH
  have hEF : ∀ x, E (F x) - F (E x) = H x := by
    intro x
    obtain ⟨u, rfl⟩ := N.mkQ_surjective x
    simp only [E, F, H, Submodule.mkQ_apply, Submodule.mapQ_apply,
      ← Submodule.Quotient.mk_sub]
    congr 1
    rw [ρ.comm 1 4 0 0 u]
    simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
  have hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x := by
    intro x
    obtain ⟨u, rfl⟩ := N.mkQ_surjective x
    simp only [H, F, Submodule.mkQ_apply, Submodule.mapQ_apply,
      ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_smul]
    congr 1
    rw [ρ.comm 7 4 0 0 u]
    simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
  have hE0 : E (N.mkQ v) = 0 := by
    simp only [E, Submodule.mkQ_apply, Submodule.mapQ_apply]
    exact (Submodule.Quotient.mk_eq_zero N).mpr
      (hHigher (a2_raising_mem_higher ρ w p q h 0 k hv))
  have hH0 : H (N.mkQ v) = (a2KeyHeight q k : ℂ) • N.mkQ v := by
    simp only [H, Submodule.mkQ_apply, Submodule.mapQ_apply]
    rw [a2_node2_weight_key ρ w q k h.cartan_second hv]
    rw [← Submodule.Quotient.mk_smul]
    simp [a2KeyHeight]
  have hiter : ∀ j (u : V), F^[j] (N.mkQ u) = N.mkQ ((ρ.op 4 0)^[j] u) := by
    intro j
    induction j with
    | zero => intro u; rfl
    | succ j ih =>
        intro u
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        rfl
  let K := q + 1 + VOA.DeligneAudit.FiniteG.adK
    VOA.DeligneAudit.DeligneSector.A2sector * (k.d₁ + k.d₂)
  have hnil : F^[K] (N.mkQ v) = 0 := by
    rw [hiter, ← Module.End.pow_apply]
    rw [a2_key_lowering_nilpotent ρ w p q h k hv]
    exact map_zero _
  obtain ⟨hneg, hpos⟩ := VOA.DeligneAudit.CLFilt.hw_pow E F H
    hEF hHF hE0 hH0 K hnil
  constructor
  · intro hk
    exact (Submodule.Quotient.mk_eq_zero N).mp (hneg hk)
  · intro hk
    have hp := hpos hk
    rw [hiter, ← Module.End.pow_apply] at hp
    exact (Submodule.Quotient.mk_eq_zero N).mp hp

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_key_lowering_sharp_mod
