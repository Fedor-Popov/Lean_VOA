import VOA.DeligneAudit.LeviTypeA3OrbitClosure

/-! Rank and vanishing of one key's full Levi orbit modulo higher keys. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_key_levi_orbit_rank (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (k : A3RadicalKey) {v : V} (hv : v ∈ a3KeyLayer ρ w k)
    (hp : 0 ≤ a3KeyLabelInt b c 0 k)
    (hq : 0 ≤ a3KeyLabelInt b c 1 k) :
    let N := a3HigherLeviClosure ρ w b c k
    let C := a3LeviClosure ρ (ℂ ∙ v)
    FiniteDimensional ℂ (C.map N.mkQ) ∧
      Module.finrank ℂ (C.map N.mkQ) ≤
        3 ^ (a3KeyLabelInt b c 0 k).toNat *
          3 ^ (a3KeyLabelInt b c 1 k).toNat := by
  let N := a3HigherLeviClosure ρ w b c k
  have hN : ∀ x r, N ≤ N.comap (ρ.op (a3LeviColour x) r) :=
    fun x r => a3HigherLeviClosure_inv ρ w b c k x r
  dsimp only
  rw [a3_levi_closure_map_eq_cyclic ρ N hN v]
  exact a3_key_cyclic_rank ρ w a b c h k hv hp hq

theorem a3_key_negative_levi_orbit_zero (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 2) (k : A3RadicalKey)
    {v : V} (hv : v ∈ a3KeyLayer ρ w k)
    (hi : a3KeyLabelInt b c i k < 0) :
    let N := a3HigherLeviClosure ρ w b c k
    (a3LeviClosure ρ (ℂ ∙ v)).map N.mkQ = ⊥ := by
  let N := a3HigherLeviClosure ρ w b c k
  have hvN : v ∈ N := (Submodule.Quotient.mk_eq_zero N).mp
    (a3_key_negative_zero ρ w a b c h i k hv hi)
  have hSN : ℂ ∙ v ≤ N := by
    rw [Submodule.span_le]
    intro x hx
    have hxeq : x = v := Set.mem_singleton_iff.mp hx
    subst x
    exact hvN
  have hCN := a3LeviClosure_le_of_inv ρ (ℂ ∙ v) N hSN
    (fun x r => a3HigherLeviClosure_inv ρ w b c k x r)
  apply eq_bot_iff.mpr
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
  change N.mkQ x = 0
  exact (Submodule.Quotient.mk_eq_zero N).mpr (hCN hx)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_key_levi_orbit_rank
#print axioms VOA.DeligneAudit.A3Sector.a3_key_negative_levi_orbit_zero
