import VOA.DeligneAudit.LeviTypeA2CertStepQuotRank

/-! Projection of a finite key step, keeping the original higher-key quotient. -/

namespace VOA.DeligneAudit.D4Char

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def quotientToImageEquiv (F S : Submodule ℂ V) :
    (S ⧸ F.comap S.subtype) ≃ₗ[ℂ] S.map F.mkQ := by
  let f : S →ₗ[ℂ] V ⧸ F := F.mkQ.comp S.subtype
  have hker : LinearMap.ker f = F.comap S.subtype := by
    simp [f, LinearMap.ker_comp]
  have hrange : LinearMap.range f = S.map F.mkQ := by
    simp [f, LinearMap.range_comp, Submodule.range_subtype]
  rw [← hrange]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans f.quotKerEquivRange

/-- On a homogeneous subspace, quotienting by the homogeneous prefix or the full prefix agrees. -/
theorem projectedPrefix_comap (p : Module.End ℂ V) (hp : ∀ v, p (p v) = p v)
    (F S : Submodule ℂ V) (hF : F.map p ≤ F) (hS : S ≤ LinearMap.range p) :
    (F.map p).comap S.subtype = F.comap S.subtype := by
  ext v
  constructor
  · intro hv
    exact hF hv
  · intro hv
    obtain ⟨u, hu⟩ := hS v.property
    have he : p (v : V) = v := by rw [← hu]; exact hp u
    exact ⟨v, hv, he⟩

def projectedQuotientImageEquiv (p : Module.End ℂ V) (hp : ∀ v, p (p v) = p v)
    (F S : Submodule ℂ V) (hF : F.map p ≤ F) (hS : S ≤ LinearMap.range p) :
    S.map (F.map p).mkQ ≃ₗ[ℂ] S.map F.mkQ :=
  (quotientToImageEquiv (F.map p) S).symm.trans
    ((Submodule.quotEquivOfEq _ _ (projectedPrefix_comap p hp F S hF hS)).trans
      (quotientToImageEquiv F S))

/-- Graded orbit ranks in the original quotient bound the projected filtration step. -/
theorem projected_step_rank (p : Module.End ℂ V) (hp : ∀ v, p (p v) = p v)
    (F T : Submodule ℂ V) (hF : F.map p ≤ F) (m L : ℕ)
    (O : Fin m → Submodule ℂ V) (hT : T = F ⊔ ⨆ j, O j)
    (hfinite : ∀ j, FiniteDimensional ℂ (((O j).map p).map F.mkQ))
    (hrank : ∀ j, Module.finrank ℂ (((O j).map p).map F.mkQ) ≤ L) :
    FiniteDimensional ℂ ((T.map p) ⧸ (F.map p).comap (T.map p).subtype) ∧
      Module.finrank ℂ ((T.map p) ⧸ (F.map p).comap (T.map p).subtype) ≤ L * m := by
  have hmap : T.map p = F.map p ⊔ ⨆ j, (O j).map p := by
    rw [hT, Submodule.map_sup, Submodule.map_iSup]
  have hrange (j : Fin m) : (O j).map p ≤ LinearMap.range p := by
    rintro x ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  let e (j : Fin m) := projectedQuotientImageEquiv p hp F ((O j).map p) hF (hrange j)
  apply A3Sector.a2_step_quot_rank_of_orbits (F.map p) (T.map p) m L
    (fun j => (O j).map p) hmap
  · intro j
    haveI := hfinite j
    exact FiniteDimensional.of_injective (e j).toLinearMap (e j).injective
  · intro j
    exact (e j).finrank_eq.trans_le (hrank j)

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.quotientToImageEquiv
#print axioms VOA.DeligneAudit.D4Char.projectedPrefix_comap
#print axioms VOA.DeligneAudit.D4Char.projectedQuotientImageEquiv
#print axioms VOA.DeligneAudit.D4Char.projected_step_rank
