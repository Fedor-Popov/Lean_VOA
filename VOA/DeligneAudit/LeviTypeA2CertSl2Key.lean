import VOA.DeligneAudit.LeviTypeA2CertSl2Quot

/-! The `2 ^ height` bound for each radical key in its canonical quotient. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.CVsl2

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- The canonical higher-key closure is stable under every node-two current. -/
theorem a2_key_higher_levi_stable (q : ℕ) (k : A2RadicalKey)
    (r : ℕ) (a : Fin 8) (ha : a = 1 ∨ a = 4 ∨ a = 7) :
    a2LeviClosure ρ (a2HigherKeySpan ρ w q k) ≤
      (a2LeviClosure ρ (a2HigherKeySpan ρ w q k)).comap (ρ.op a r) := by
  rcases ha with rfl | rfl | rfl
  · exact a2LeviClosure_inv ρ _ 1 r (Or.inl rfl)
  · exact a2LeviClosure_inv ρ _ 4 r (Or.inr (Or.inl rfl))
  · exact a2LeviClosure_inv ρ _ 7 r (Or.inr (Or.inr (Or.inr rfl)))

/-- A key of nonnegative node-two height generates at most `2 ^ height`
lowering-current descendants in the quotient by higher keys. -/
theorem a2_key_fspan_bound (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k : A2RadicalKey)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k)
    (hk : 0 ≤ a2KeyHeight q k) :
    let N := a2LeviClosure ρ (a2HigherKeySpan ρ w q k)
    let F : ℕ → Module.End ℂ (V ⧸ N) := fun r =>
      N.mapQ N (ρ.op 4 r) (a2_key_higher_levi_stable ρ w q k r 4
        (Or.inr (Or.inl rfl)))
    FiniteDimensional ℂ (Fspan F (N.mkQ v)) ∧
      Module.finrank ℂ (Fspan F (N.mkQ v)) ≤
        2 ^ (a2KeyHeight q k).toNat := by
  exact a2_key_fspan_bound_mod ρ q k _
    (a2_key_higher_levi_stable ρ w q k)
    (a2_key_local_weyl_levi_quotient ρ w p q h k hv) hk

/-- A key of negative node-two height vanishes in the same quotient. -/
theorem a2_key_negative_zero (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k : A2RadicalKey)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k)
    (hk : a2KeyHeight q k < 0) :
    (a2LeviClosure ρ (a2HigherKeySpan ρ w q k)).mkQ v = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((a2_key_local_weyl_levi_quotient ρ w p q h k hv).2.2.2.1 hk)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_key_higher_levi_stable
#print axioms VOA.DeligneAudit.A3Sector.a2_key_fspan_bound
#print axioms VOA.DeligneAudit.A3Sector.a2_key_negative_zero
