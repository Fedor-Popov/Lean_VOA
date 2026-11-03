import VOA.DeligneAudit.LeviTypeA2CertSl2Current

/-! The local Weyl bound inside a Levi-stable quotient. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.CVsl2

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V)

/-- A nonnegative key vector generates at most `2 ^ height` lowering-current
descendants after quotienting by a Levi-stable subspace. -/
theorem a2_key_fspan_bound_mod (q : ℕ) (k : A2RadicalKey)
    (N : Submodule ℂ V)
    (hStable : ∀ r, ∀ a : Fin 8, a = 1 ∨ a = 4 ∨ a = 7 →
      N ≤ N.comap (ρ.op a r))
    {v : V} (hRel : A2KeyLocalWeylRelModulo ρ q k N v)
    (hk : 0 ≤ a2KeyHeight q k) :
    let F : ℕ → Module.End ℂ (V ⧸ N) := fun r =>
      N.mapQ N (ρ.op 4 r) (hStable r 4 (Or.inr (Or.inl rfl)))
    FiniteDimensional ℂ (Fspan F (N.mkQ v)) ∧
      Module.finrank ℂ (Fspan F (N.mkQ v)) ≤
        2 ^ (a2KeyHeight q k).toNat := by
  let E : ℕ → Module.End ℂ (V ⧸ N) := fun r =>
    N.mapQ N (ρ.op 1 r) (hStable r 1 (Or.inl rfl))
  let H : ℕ → Module.End ℂ (V ⧸ N) := fun r =>
    N.mapQ N (ρ.op 7 r) (hStable r 7 (Or.inr (Or.inr rfl)))
  let F : ℕ → Module.End ℂ (V ⧸ N) := fun r =>
    N.mapQ N (ρ.op 4 r) (hStable r 4 (Or.inr (Or.inl rfl)))
  have hS : SL2 E H F :=
    SL2_quot (a2_node2_sl2 ρ) N
      (fun r => hStable r 1 (Or.inl rfl))
      (fun r => hStable r 7 (Or.inr (Or.inr rfl)))
      (fun r => hStable r 4 (Or.inr (Or.inl rfl)))
  have hE : ∀ r, E r (N.mkQ v) = 0 := by
    intro r
    exact (Submodule.Quotient.mk_eq_zero N).mpr (hRel.1 r)
  have hH : ∀ r, 0 < r → H r (N.mkQ v) = 0 := by
    intro r hr
    exact (Submodule.Quotient.mk_eq_zero N).mpr (hRel.2.1 r hr)
  have hH0 : ∃ c : ℂ, H 0 (N.mkQ v) = c • N.mkQ v := by
    refine ⟨(a2KeyHeight q k : ℂ), ?_⟩
    change N.mkQ (ρ.op 7 0 v) = _
    rw [hRel.2.2.1, map_smul]
  have hpow : ∀ n : ℕ,
      (F 0 ^ n) (N.mkQ v) = N.mkQ ((ρ.op 4 0 ^ n) v) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, ih]
        change N.mkQ (ρ.op 4 0 ((ρ.op 4 0 ^ n) v)) = _
        rw [pow_succ', Module.End.mul_apply]
  have hF0 : (F 0 ^ ((a2KeyHeight q k).toNat + 1)) (N.mkQ v) = 0 := by
    rw [hpow]
    exact (Submodule.Quotient.mk_eq_zero N).mpr (hRel.2.2.2.2 hk)
  exact local_weyl_fspan_bound hS hE hH hH0 _ hF0

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_key_fspan_bound_mod
