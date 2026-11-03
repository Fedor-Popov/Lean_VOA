import VOA.DeligneAudit.LeviTypeA2CertHigherPrefix
import VOA.DeligneAudit.LeviTypeA2CertStepRank

/-! A quotient rank bound from finitely many bounded orbit images. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviKeyFiltration

noncomputable section

theorem a2_step_quot_rank_of_orbits
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (F T : Submodule ℂ V) (m L : ℕ)
    (O : Fin m → Submodule ℂ V)
    (hT : T = F ⊔ ⨆ j, O j)
    (hfinite : ∀ j, FiniteDimensional ℂ ((O j).map F.mkQ))
    (hrank : ∀ j, Module.finrank ℂ ((O j).map F.mkQ) ≤ L) :
    FiniteDimensional ℂ (T ⧸ F.comap T.subtype) ∧
      Module.finrank ℂ (T ⧸ F.comap T.subtype) ≤ L * m := by
  let P : Fin m → Submodule ℂ (V ⧸ F) := fun j => (O j).map F.mkQ
  have haux (s : Finset (Fin m)) :
      FiniteDimensional ℂ (s.sup P : Submodule ℂ (V ⧸ F)) ∧
        Module.finrank ℂ (s.sup P : Submodule ℂ (V ⧸ F)) ≤ ∑ j ∈ s, L := by
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨by simpa using
          (inferInstance : FiniteDimensional ℂ (⊥ : Submodule ℂ (V ⧸ F))), by simp⟩
    | @insert j s hj ih =>
        haveI : FiniteDimensional ℂ (P j) := hfinite j
        haveI : FiniteDimensional ℂ (s.sup P : Submodule ℂ (V ⧸ F)) := ih.1
        rw [Finset.sup_insert, Finset.sum_insert hj]
        exact ⟨inferInstance,
          (Submodule.finrank_add_le_finrank_add_finrank (P j) (s.sup P)).trans
            (Nat.add_le_add (hrank j) ih.2)⟩
  have hmap : T.map F.mkQ = Finset.univ.sup P := by
    rw [hT, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq,
      Submodule.map_iSup, Finset.sup_eq_iSup]
    simp [P]
  have h := haux Finset.univ
  rw [← hmap] at h
  let f : T →ₗ[ℂ] V ⧸ F := F.mkQ.comp T.subtype
  have hker : LinearMap.ker f = F.comap T.subtype := by
    simp [f, LinearMap.ker_comp]
  have hrange : LinearMap.range f = T.map F.mkQ := by
    simp [f, LinearMap.range_comp, Submodule.range_subtype]
  let e : (T ⧸ F.comap T.subtype) ≃ₗ[ℂ] LinearMap.range f :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans f.quotKerEquivRange
  haveI : FiniteDimensional ℂ (LinearMap.range f) := by
    rw [hrange]
    exact h.1
  haveI : FiniteDimensional ℂ (T ⧸ F.comap T.subtype) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  refine ⟨inferInstance, ?_⟩
  calc
    Module.finrank ℂ (T ⧸ F.comap T.subtype) =
        Module.finrank ℂ (LinearMap.range f) := e.finrank_eq
    _ = Module.finrank ℂ (T.map F.mkQ) := by rw [hrange]
    _ ≤ m * L := by
      simpa only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] using h.2
    _ = L * m := Nat.mul_comm _ _

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_step_quot_rank_of_orbits
