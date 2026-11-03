import VOA.DeligneAudit.LeviTypeA2CertGradedFinal
import VOA.DeligneAudit.LeviTypeA2CertStepRank

/-! Public all-weight A₂ theorem and a rank certificate for every generator. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviKeyFiltration

noncomputable section

/-- The unconditional all-weight `sl₃` local Weyl rank bound. -/
theorem typeA2Bound : TypeA2Bound := by
  intro p q V _ _ ρ w h
  exact a2_all_weight_rank ρ w p q h

/-- A rank-field certificate follows from the proved cyclic rank bound.
The graded key filtration is the proof of `typeA2Bound`; this certificate
uses the equivalent one-step finite filtration. -/
theorem allA2LeviRankCertificates : AllA2LeviRankCertificates := by
  intro p q V _ _ ρ w h
  let C := VOA.DeligneAudit.UnivG.cycSubG ρ w
  have hrank := a2_all_weight_rank ρ w p q h
  letI : FiniteDimensional ℂ C := hrank.1
  let F : ℕ → Submodule ℂ C := fun i => if i = 0 then ⊥ else ⊤
  let S : ℕ → Submodule ℂ C := fun _ => ⊤
  let L : ℕ → ℕ := fun _ => 1
  let g : ℕ → ℕ := fun _ => 3 ^ p * 3 ^ q
  refine ⟨{
    n := 1
    F := F
    S := S
    L := L
    g := g
    zero := by simp [F]
    top := by simp [F]
    mono := ?_
    step_finite := ?_
    step_rank := ?_
    multiplicity := ?_
    count := ?_
  }⟩
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simp [F]
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    infer_instance
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    change Module.finrank ℂ (StepQuot F 0) ≤
      L 0 * Module.finrank ℂ (KeyQuot F S 0)
    simp [F, S, L, StepQuot, KeyQuot]
    exact le_rfl
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    have hq : Module.finrank ℂ (KeyQuot F S 0) ≤
        Module.finrank ℂ C := by
      have htop : FiniteDimensional ℂ (⊤ : Submodule ℂ C) := inferInstance
      have hle := Submodule.finrank_quotient_le
        (s := (F 0).comap (S 0).subtype)
      simpa [F, S, KeyQuot] using hle
    exact hq.trans hrank.2
  · simp [L, g, VOA.DeligneAudit.LeviTypeA.a2LeviCount_eq]

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.typeA2Bound
#print axioms VOA.DeligneAudit.A3Sector.allA2LeviRankCertificates
