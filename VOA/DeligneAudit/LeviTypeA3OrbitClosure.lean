import VOA.DeligneAudit.LeviTypeA3KeyOrbit

/-! The Levi closure of one vector maps to its cyclic quotient module. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V)

private theorem a3_word_quot (N : Submodule ℂ V)
    (hN : ∀ a r, N ≤ N.comap (ρ.op (a3LeviColour a) r))
    (l : List (Fin 8 × ℕ)) (v : V) :
    wordOp (a3LeviQuotCurrent ρ N hN) l (N.mkQ v) =
      N.mkQ (wordOp ρ (l.map fun x => (a3LeviColour x.1, x.2)) v) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      rcases x with ⟨a, r⟩
      change (a3LeviQuotCurrent ρ N hN).op a r
        (wordOp (a3LeviQuotCurrent ρ N hN) l (N.mkQ v)) = _
      rw [ih]
      rfl

theorem a3_levi_closure_map_eq_cyclic (N : Submodule ℂ V)
    (hN : ∀ a r, N ≤ N.comap (ρ.op (a3LeviColour a) r)) (v : V) :
    (a3LeviClosure ρ (ℂ ∙ v)).map N.mkQ =
      VOA.DeligneAudit.UnivG.cycSubG (a3LeviQuotCurrent ρ N hN) (N.mkQ v) := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply a3LeviClosure_le_of_inv ρ
    · rw [Submodule.span_le]
      intro x hx
      have hx' : x = v := Set.mem_singleton_iff.mp hx
      subst x
      exact VOA.DeligneAudit.UnivG.wordOp_mem_cycSubG
        (a3LeviQuotCurrent ρ N hN) (N.mkQ v) []
    · intro a r x hx
      change (a3LeviQuotCurrent ρ N hN).op a r (N.mkQ x) ∈
        VOA.DeligneAudit.UnivG.cycSubG (a3LeviQuotCurrent ρ N hN) (N.mkQ v)
      exact VOA.DeligneAudit.UnivG.cycSubG_inv
        (a3LeviQuotCurrent ρ N hN) (N.mkQ v) a r hx
  · rw [VOA.DeligneAudit.UnivG.cycSubG, Submodule.span_le]
    rintro z ⟨l, rfl⟩
    change wordOp (a3LeviQuotCurrent ρ N hN) l (N.mkQ v) ∈ _
    rw [a3_word_quot ρ N hN]
    exact Submodule.mem_map.mpr
      ⟨wordOp ρ (l.map fun x => (a3LeviColour x.1, x.2)) v,
        Submodule.subset_span ⟨l, v, Submodule.mem_span_singleton_self v, rfl⟩, rfl⟩

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_levi_closure_map_eq_cyclic
