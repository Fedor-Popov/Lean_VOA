import VOA.DeligneAudit.LeviTypeA2CertGradedBoxFinite
import VOA.DeligneAudit.LeviTypeA2CertHigherPrefix

/-! Rank of a key quotient from its finite box generating set. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl

noncomputable section

private theorem quotient_finrank_le_finset
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (F S : Submodule ℂ V) (E : Finset V)
    (hS : S ≤ Submodule.span ℂ (E : Set V) ⊔ F) :
    Module.finrank ℂ (S ⧸ F.comap S.subtype) ≤ E.card := by
  classical
  let f : S →ₗ[ℂ] V ⧸ F := F.mkQ.comp S.subtype
  have hker : LinearMap.ker f = F.comap S.subtype := by
    simp [f, LinearMap.ker_comp]
  have hrange : LinearMap.range f = S.map F.mkQ := by
    simp [f, LinearMap.range_comp, Submodule.range_subtype]
  let e : (S ⧸ F.comap S.subtype) ≃ₗ[ℂ] LinearMap.range f :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans f.quotKerEquivRange
  have hspan : S.map F.mkQ ≤
      Submodule.span ℂ ((E.image F.mkQ : Finset (V ⧸ F)) : Set (V ⧸ F)) := by
    calc
      S.map F.mkQ ≤ (Submodule.span ℂ (E : Set V) ⊔ F).map F.mkQ :=
        Submodule.map_mono hS
      _ = Submodule.span ℂ (F.mkQ '' (E : Set V)) := by
        rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq,
          Submodule.map_span]
      _ = _ := by rw [Finset.coe_image]
  haveI : FiniteDimensional ℂ
      (Submodule.span ℂ ((E.image F.mkQ : Finset (V ⧸ F)) : Set (V ⧸ F))) :=
    FiniteDimensional.span_of_finite _ (Finset.finite_toSet _)
  have hle := Submodule.finrank_mono hspan
  have hcard := finrank_span_finset_le_card
    (R := ℂ) (s := E.image F.mkQ)
  calc
    Module.finrank ℂ (S ⧸ F.comap S.subtype) =
        Module.finrank ℂ (LinearMap.range f) := e.finrank_eq
    _ = Module.finrank ℂ (S.map F.mkQ) := by rw [hrange]
    _ ≤ Module.finrank ℂ
        (Submodule.span ℂ ((E.image F.mkQ : Finset (V ⧸ F)) : Set (V ⧸ F))) := hle
    _ ≤ (E.image F.mkQ).card := hcard
    _ ≤ E.card := Finset.card_image_le

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- A radical key quotient has rank at most its fixed-degree box pairs. -/
theorem a2_key_quot_finrank_le_boxPairs (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k : A2RadicalKey)
    (ha : k.d₁ ≤ p) (hb : k.d₂ ≤ q) :
    let F := a2LeviClosure ρ (a2HigherKeySpan ρ w q k)
    let S := a2KeyLayer ρ w k
    Module.finrank ℂ (S ⧸ F.comap S.subtype) ≤
      (a2TwoBoxKeyPairs p q k.d₁ k.d₂ k.degree).card := by
  let F := a2LeviClosure ρ (a2HigherKeySpan ρ w q k)
  let S := a2KeyLayer ρ w k
  let E := a2TwoBoxKeyVectors ρ w p q k.d₁ k.d₂ k.degree
  have hS : S ≤ Submodule.span ℂ (E : Set V) ⊔ F :=
    (a2KeyLayer_le_two_boxes ρ w p q h k).trans
      (sup_le_sup_right (a2TwoBoxKeySpan_le_finite ρ w p q
        k.d₁ k.d₂ k.degree ha hb) _)
  exact (quotient_finrank_le_finset F S E hS).trans
    (a2TwoBoxKeyVectors_card_le ρ w p q k.d₁ k.d₂ k.degree)

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_key_quot_finrank_le_boxPairs
