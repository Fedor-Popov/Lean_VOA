import VOA.DeligneAudit.LeviTypeA3StepQuotRank

/-! The ordered key step has the sl₃ Levi orbit rank bound. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

noncomputable def a3KeyOrbitLength (b c : ℕ) (k : A3RadicalKey) : ℕ :=
  if a3KeyLabelInt b c 0 k < 0 ∨ a3KeyLabelInt b c 1 k < 0 then 0
  else 3 ^ (a3KeyLabelInt b c 0 k).toNat *
    3 ^ (a3KeyLabelInt b c 1 k).toNat

theorem a3OrderedStep_rank (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : ℕ) (hi : i < (a3KeyBox a b c).card) :
    let k := a3KeyEnum a b c ⟨i, hi⟩
    let F := a3KeyPrefix ρ w (a3KeyEnum a b c) i
    let S := a3KeyLayer ρ w k
    let T := a3KeyPrefix ρ w (a3KeyEnum a b c) (i + 1)
    FiniteDimensional ℂ (T ⧸ F.comap T.subtype) ∧
      Module.finrank ℂ (T ⧸ F.comap T.subtype) ≤
        a3KeyOrbitLength b c k * Module.finrank ℂ (S ⧸ F.comap S.subtype) := by
  let k := a3KeyEnum a b c ⟨i, hi⟩
  let F := a3KeyPrefix ρ w (a3KeyEnum a b c) i
  let S := a3KeyLayer ρ w k
  let T := a3KeyPrefix ρ w (a3KeyEnum a b c) (i + 1)
  let m := Module.finrank ℂ (S ⧸ F.comap S.subtype)
  let L := a3KeyOrbitLength b c k
  obtain ⟨v, hv⟩ := a3KeyPrefix_step_orbits ρ w hi
    (a3KeyEnum a b c) a b c h
  have hF : F = a3HigherLeviClosure ρ w b c k :=
    a3OrderedPrefix_eq_higher ρ w a b c h i hi
  have hfinite (j : Fin m) :
      FiniteDimensional ℂ ((a3LeviClosure ρ (ℂ ∙ (v j : V))).map F.mkQ) := by
    rw [hF]
    by_cases hp : a3KeyLabelInt b c 0 k < 0
    · rw [a3_key_negative_levi_orbit_zero ρ w a b c h 0 k (v j).property hp]
      infer_instance
    · by_cases hq : a3KeyLabelInt b c 1 k < 0
      · rw [a3_key_negative_levi_orbit_zero ρ w a b c h 1 k (v j).property hq]
        infer_instance
      · exact (a3_key_levi_orbit_rank ρ w a b c h k (v j).property
          (by omega) (by omega)).1
  have hrank (j : Fin m) :
      Module.finrank ℂ ((a3LeviClosure ρ (ℂ ∙ (v j : V))).map F.mkQ) ≤ L := by
    rw [hF]
    by_cases hp : a3KeyLabelInt b c 0 k < 0
    · rw [a3_key_negative_levi_orbit_zero ρ w a b c h 0 k (v j).property hp]
      simp [L, a3KeyOrbitLength, hp]
    · by_cases hq : a3KeyLabelInt b c 1 k < 0
      · rw [a3_key_negative_levi_orbit_zero ρ w a b c h 1 k (v j).property hq]
        simp [L, a3KeyOrbitLength, hq]
      · simpa [L, a3KeyOrbitLength, hp, hq] using
          (a3_key_levi_orbit_rank ρ w a b c h k (v j).property
            (by omega) (by omega)).2
  exact a3_step_quot_rank_of_orbits F T m L
    (fun j => a3LeviClosure ρ (ℂ ∙ (v j : V))) hv hfinite hrank

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3OrderedStep_rank
