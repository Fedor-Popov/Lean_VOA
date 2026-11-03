import VOA.DeligneAudit.LeviTypeA2CertPrefix
import VOA.DeligneAudit.LeviKeyFiltration

/-! A finite key quotient basis lifts to generators modulo preceding stages. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviKeyFiltration

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- A basis of `S/(S ∩ F)` gives exactly `finrank` lifts in `S` whose
ambient span, together with `F`, contains `S`. -/
theorem a2_keyQuot_basis_lifts (F S : Submodule ℂ V)
    [FiniteDimensional ℂ S] :
    ∃ v : Fin (Module.finrank ℂ (S ⧸ F.comap S.subtype)) → S,
      S ≤ F ⊔ Submodule.span ℂ (Set.range fun j => (v j : V)) := by
  let P : Submodule ℂ S := F.comap S.subtype
  let Q := S ⧸ P
  let b : Module.Basis (Fin (Module.finrank ℂ Q)) ℂ Q := Module.finBasis ℂ Q
  let v : Fin (Module.finrank ℂ Q) → S := fun j =>
    Classical.choose (P.mkQ_surjective (b j))
  have hv (j : Fin (Module.finrank ℂ Q)) :
      P.mkQ (v j) = b j :=
    Classical.choose_spec (P.mkQ_surjective (b j))
  refine ⟨v, ?_⟩
  intro x hx
  let y : S := ⟨x, hx⟩
  let z : S := ∑ j, b.repr (P.mkQ y) j • v j
  have hz : (z : V) ∈ Submodule.span ℂ (Set.range fun j => (v j : V)) := by
    change S.subtype z ∈ _
    simp only [z, map_sum, map_smul]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨j, rfl⟩)
  have hq : P.mkQ z = P.mkQ y := by
    change P.mkQ (∑ j, b.repr (P.mkQ y) j • v j) = _
    simp only [map_sum, map_smul, hv]
    exact b.sum_repr _
  have hdiff : (y - z : S) ∈ P := by
    apply (Submodule.Quotient.mk_eq_zero P).mp
    change P.mkQ (y - z) = 0
    rw [map_sub, hq, sub_self]
  have hyz : (y : V) = ((y - z : S) : V) + (z : V) := by
    simp
  change (y : V) ∈ F ⊔ Submodule.span ℂ (Set.range fun j => (v j : V))
  rw [hyz]
  exact Submodule.mem_sup.mpr ⟨_, hdiff, _, hz, rfl⟩

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_keyQuot_basis_lifts
