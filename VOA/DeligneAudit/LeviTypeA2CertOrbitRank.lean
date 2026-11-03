import VOA.DeligneAudit.LeviTypeA2CertOrbitClosure

/-! Rank bounds for one key vector's full Levi orbit modulo higher keys. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.CVsl2

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- The full Levi orbit of one key vector has quotient rank at most
`2 ^ height` when its node-two height is nonnegative. -/
theorem a2_key_levi_orbit_rank (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k : A2RadicalKey)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k)
    (hk : 0 ≤ a2KeyHeight q k) :
    let N := a2LeviClosure ρ (a2HigherKeySpan ρ w q k)
    let C := a2LeviClosure ρ (ℂ ∙ v)
    FiniteDimensional ℂ (C.map N.mkQ) ∧
      Module.finrank ℂ (C.map N.mkQ) ≤
        2 ^ (a2KeyHeight q k).toNat := by
  let N := a2LeviClosure ρ (a2HigherKeySpan ρ w q k)
  let F : ℕ → Module.End ℂ (V ⧸ N) := fun r =>
    N.mapQ N (ρ.op 4 r) (a2_key_higher_levi_stable ρ w q k r 4
      (Or.inr (Or.inl rfl)))
  let C := a2LeviClosure ρ (ℂ ∙ v)
  have hP := a2_key_fspan_bound ρ w p q h k hv hk
  have hle : C.map N.mkQ ≤ Fspan F (N.mkQ v) := by
    apply Submodule.map_le_iff_le_comap.mpr
    exact a2_key_levi_orbit_le_fspan ρ w p q h k hv
  letI : FiniteDimensional ℂ (Fspan F (N.mkQ v)) := hP.1
  haveI : FiniteDimensional ℂ (C.map N.mkQ) :=
    Submodule.finiteDimensional_of_le hle
  exact ⟨inferInstance, (Submodule.finrank_mono hle).trans hP.2⟩

/-- A negative-height key vector has zero Levi orbit modulo higher keys. -/
theorem a2_key_negative_levi_orbit_zero (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k : A2RadicalKey)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k)
    (hk : a2KeyHeight q k < 0) :
    let N := a2LeviClosure ρ (a2HigherKeySpan ρ w q k)
    (a2LeviClosure ρ (ℂ ∙ v)).map N.mkQ = ⊥ := by
  let N := a2LeviClosure ρ (a2HigherKeySpan ρ w q k)
  have hvN : v ∈ N := (Submodule.Quotient.mk_eq_zero N).mp
    (a2_key_negative_zero ρ w p q h k hv hk)
  have hSN : ℂ ∙ v ≤ N := by
    rw [Submodule.span_le]
    intro x hx
    have hxeq : x = v := Set.mem_singleton_iff.mp hx
    subst x
    exact hvN
  have hCN := a2LeviClosure_le_of_inv ρ (ℂ ∙ v) N hSN
    (fun a r ha => a2LeviClosure_inv ρ _ a r ha)
  apply eq_bot_iff.mpr
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
  change N.mkQ x = 0
  exact (Submodule.Quotient.mk_eq_zero N).mpr (hCN hx)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_key_levi_orbit_rank
#print axioms VOA.DeligneAudit.A3Sector.a2_key_negative_levi_orbit_zero
