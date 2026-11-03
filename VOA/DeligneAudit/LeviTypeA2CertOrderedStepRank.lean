import VOA.DeligneAudit.LeviTypeA2CertStepQuotRank

/-! Each ordered key step has the node-two orbit rank bound. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

noncomputable def a2KeyOrbitLength (q : ℕ) (k : A2RadicalKey) : ℕ :=
  if a2KeyHeight q k < 0 then 0 else 2 ^ (a2KeyHeight q k).toNat

theorem a2OrderedStep_rank (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (i : ℕ) (hi : i < (a2KeyBox p q).card) :
    let k := a2KeyEnum p q ⟨i, hi⟩
    let F := a2KeyPrefix ρ w (a2KeyEnum p q) i
    let S := a2KeyLayer ρ w k
    let T := a2KeyPrefix ρ w (a2KeyEnum p q) (i + 1)
    FiniteDimensional ℂ (T ⧸ F.comap T.subtype) ∧
      Module.finrank ℂ (T ⧸ F.comap T.subtype) ≤
        a2KeyOrbitLength q k * Module.finrank ℂ (S ⧸ F.comap S.subtype) := by
  let k := a2KeyEnum p q ⟨i, hi⟩
  let F := a2KeyPrefix ρ w (a2KeyEnum p q) i
  let S := a2KeyLayer ρ w k
  let T := a2KeyPrefix ρ w (a2KeyEnum p q) (i + 1)
  let m := Module.finrank ℂ (S ⧸ F.comap S.subtype)
  let L := a2KeyOrbitLength q k
  obtain ⟨v, hv⟩ := a2OrderedPrefix_step_orbits ρ w p q h i hi
  have hF : F = a2LeviClosure ρ (a2HigherKeySpan ρ w q k) :=
    a2OrderedPrefix_eq_higher ρ w p q h i hi
  have hfinite (j : Fin m) :
      FiniteDimensional ℂ ((a2LeviClosure ρ (ℂ ∙ (v j : V))).map F.mkQ) := by
    rw [hF]
    by_cases hk : a2KeyHeight q k < 0
    · rw [a2_key_negative_levi_orbit_zero ρ w p q h k (v j).property hk]
      infer_instance
    · exact (a2_key_levi_orbit_rank ρ w p q h k (v j).property
        (by omega)).1
  have hrank (j : Fin m) :
      Module.finrank ℂ ((a2LeviClosure ρ (ℂ ∙ (v j : V))).map F.mkQ) ≤ L := by
    rw [hF]
    by_cases hk : a2KeyHeight q k < 0
    · rw [a2_key_negative_levi_orbit_zero ρ w p q h k (v j).property hk]
      simp [L, a2KeyOrbitLength, hk]
    · simpa [L, a2KeyOrbitLength, hk] using
        (a2_key_levi_orbit_rank ρ w p q h k (v j).property (by omega)).2
  exact a2_step_quot_rank_of_orbits F T m L
    (fun j => a2LeviClosure ρ (ℂ ∙ (v j : V))) hv hfinite hrank

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2OrderedStep_rank
