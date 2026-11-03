import VOA.DeligneAudit.LeviTypeA2CertClosureMinimal

/-! The Levi orbit of a key vector is its bounded node-two lowering orbit. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.CVsl2

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- Modulo higher keys, every Levi descendant of one key vector lies in
its `f₂[t]` orbit. -/
theorem a2_key_levi_orbit_le_fspan (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k : A2RadicalKey)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    let N := a2LeviClosure ρ (a2HigherKeySpan ρ w q k)
    let F : ℕ → Module.End ℂ (V ⧸ N) := fun r =>
      N.mapQ N (ρ.op 4 r) (a2_key_higher_levi_stable ρ w q k r 4
        (Or.inr (Or.inl rfl)))
    a2LeviClosure ρ (ℂ ∙ v) ≤ (Fspan F (N.mkQ v)).comap N.mkQ := by
  let N := a2LeviClosure ρ (a2HigherKeySpan ρ w q k)
  let E : ℕ → Module.End ℂ (V ⧸ N) := fun r =>
    N.mapQ N (ρ.op 1 r) (a2_key_higher_levi_stable ρ w q k r 1
      (Or.inl rfl))
  let H : ℕ → Module.End ℂ (V ⧸ N) := fun r =>
    N.mapQ N (ρ.op 7 r) (a2_key_higher_levi_stable ρ w q k r 7
      (Or.inr (Or.inr rfl)))
  let F : ℕ → Module.End ℂ (V ⧸ N) := fun r =>
    N.mapQ N (ρ.op 4 r) (a2_key_higher_levi_stable ρ w q k r 4
      (Or.inr (Or.inl rfl)))
  let K : ℕ → Module.End ℂ (V ⧸ N) := fun r =>
    N.mapQ N (ρ.op 6 r)
      (a2LeviClosure_inv ρ _ 6 r (Or.inr (Or.inr (Or.inl rfl))))
  let P := Fspan F (N.mkQ v)
  let T := P.comap N.mkQ
  have hRel := a2_key_local_weyl_levi_quotient ρ w p q h k hv
  have hE : ∀ r, E r (N.mkQ v) = 0 := by
    intro r
    exact (Submodule.Quotient.mk_eq_zero N).mpr (hRel.1 r)
  have hH : ∀ r, 0 < r → H r (N.mkQ v) = 0 := by
    intro r hr
    exact (Submodule.Quotient.mk_eq_zero N).mpr (hRel.2.1 r hr)
  have hH0 : H 0 (N.mkQ v) = (a2KeyHeight q k : ℂ) • N.mkQ v := by
    change N.mkQ (ρ.op 7 0 v) = _
    rw [hRel.2.2.1, map_smul]
  have hS : SL2 E H F :=
    SL2_quot (a2_node2_sl2 ρ) N
      (fun r => a2_key_higher_levi_stable ρ w q k r 1 (Or.inl rfl))
      (fun r => a2_key_higher_levi_stable ρ w q k r 7
        (Or.inr (Or.inr rfl)))
      (fun r => a2_key_higher_levi_stable ρ w q k r 4
        (Or.inr (Or.inl rfl)))
  have hEH := Fspan_stable hS.hEF hS.hHF hE hH hH0
  have hK := a2_key_fspan_other_stable ρ w p q h k hv
  have hST : ℂ ∙ v ≤ T := by
    rw [Submodule.span_le]
    intro x hx
    have hxeq : x = v := Set.mem_singleton_iff.mp hx
    subst x
    exact self_mem (F := F) (N.mkQ v)
  have hT : ∀ (a : Fin 8) (r : ℕ), a2Levi a →
      T ≤ T.comap (ρ.op a r) := by
    intro a r ha x hx
    rcases ha with rfl | rfl | rfl | rfl
    · exact hEH.1 r hx
    · exact Fspan_F (N.mkQ v) r hx
    · exact hK r hx
    · exact hEH.2 r hx
  exact a2LeviClosure_le_of_inv ρ (ℂ ∙ v) T hST hT

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_key_levi_orbit_le_fspan
