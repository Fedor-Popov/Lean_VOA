import VOA.DeligneAudit.LeviTypeA2CertSl2Other

/-! The bounded lowering orbit is stable under the second Levi Cartan current. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.CVsl2

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- In the higher-key quotient, the `f₂` orbit of one key vector is
stable under every `h₁` current mode. -/
theorem a2_key_fspan_other_stable (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k : A2RadicalKey)
    {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    let N := a2LeviClosure ρ (a2HigherKeySpan ρ w q k)
    let F : ℕ → Module.End ℂ (V ⧸ N) := fun r =>
      N.mapQ N (ρ.op 4 r) (a2_key_higher_levi_stable ρ w q k r 4
        (Or.inr (Or.inl rfl)))
    let K : ℕ → Module.End ℂ (V ⧸ N) := fun r =>
      N.mapQ N (ρ.op 6 r)
        (a2LeviClosure_inv ρ _ 6 r (Or.inr (Or.inr (Or.inl rfl))))
    ∀ s, Fspan F (N.mkQ v) ≤ (Fspan F (N.mkQ v)).comap (K s) := by
  let N := a2LeviClosure ρ (a2HigherKeySpan ρ w q k)
  let F : ℕ → Module.End ℂ (V ⧸ N) := fun r =>
    N.mapQ N (ρ.op 4 r) (a2_key_higher_levi_stable ρ w q k r 4
      (Or.inr (Or.inl rfl)))
  let K : ℕ → Module.End ℂ (V ⧸ N) := fun r =>
    N.mapQ N (ρ.op 6 r)
      (a2LeviClosure_inv ρ _ 6 r (Or.inr (Or.inr (Or.inl rfl))))
  have hKF : ∀ s r, K s * F r - F r * K s = F (s + r) := by
    intro s r
    apply LinearMap.ext
    intro z
    obtain ⟨u, rfl⟩ := N.mkQ_surjective z
    simp only [K, F, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.sub_apply, Module.End.mul_apply,
      ← Submodule.Quotient.mk_sub]
    exact congrArg N.mkQ (congrArg (fun T : Module.End ℂ V => T u)
      (a2_other_f2_comm ρ s r))
  have hK0 : ∃ c : ℂ, K 0 (N.mkQ v) = c • N.mkQ v := by
    refine ⟨(p : ℂ) - 2 * (k.d₁ : ℂ) - (k.d₂ : ℂ), ?_⟩
    change N.mkQ (ρ.op 6 0 v) = _
    rw [a2_other_cartan_weight_key ρ w p k h.cartan_first hv,
      map_smul]
  have hKp : ∀ s, 0 < s → K s (N.mkQ v) = 0 := by
    intro s hs
    exact (Submodule.Quotient.mk_eq_zero N).mpr
      ((a2LeviClosure_contains ρ _)
        (a2_other_cartan_pos_mem_higher ρ w p q h s hs k hv))
  exact fspan_other_cartan_stable F K hKF (N.mkQ v) hK0 hKp

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_key_fspan_other_stable
