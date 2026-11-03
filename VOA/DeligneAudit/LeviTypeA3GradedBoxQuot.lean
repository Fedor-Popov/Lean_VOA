import VOA.DeligneAudit.LeviTypeA3GradedConditionalFinal

/-! Finite three-box vectors control a key quotient once KS supplies the span. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviConversion

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- The vector represented by one triple of radical mode monomials. -/
def a3ThreeBoxValue
    (fg : ((ℕ →₀ ℕ) × (ℕ →₀ ℕ)) × (ℕ →₀ ℕ)) : V :=
  (aWord (fun i => ρ.op (F 0) i) (VOA.DeligneAudit.CLAssembly.lst fg.1.1) *
    ((VOA.DeligneAudit.CLAssembly.lst fg.1.2).map
      (fun i => ρ.op (F 1) i)).prod *
    ((VOA.DeligneAudit.CLAssembly.lst fg.2).map
      (fun i => ρ.op (F 2) i)).prod) w

/-- The finite vector set attached to one radical key. -/
def a3ThreeBoxKeyVectors (a b c d₁ d₂ d₃ degree : ℕ) : Finset V := by
  classical
  exact (a3ThreeBoxKeyTriples a b c d₁ d₂ d₃ degree).image
    (a3ThreeBoxValue ρ w)

theorem a3ThreeBoxKeyVectors_card_le (a b c d₁ d₂ d₃ degree : ℕ) :
    (a3ThreeBoxKeyVectors ρ w a b c d₁ d₂ d₃ degree).card ≤
      (a3ThreeBoxKeyTriples a b c d₁ d₂ d₃ degree).card := by
  classical
  exact Finset.card_image_le

/-- A finite span modulo a submodule has quotient rank at most the size of
the chosen generating set. -/
theorem a3_quotient_finrank_le_finset
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
  have hcard := finrank_span_finset_le_card (R := ℂ) (s := E.image F.mkQ)
  calc
    Module.finrank ℂ (S ⧸ F.comap S.subtype) =
        Module.finrank ℂ (LinearMap.range f) := e.finrank_eq
    _ = Module.finrank ℂ (S.map F.mkQ) := by rw [hrange]
    _ ≤ Module.finrank ℂ
        (Submodule.span ℂ ((E.image F.mkQ : Finset (V ⧸ F)) : Set (V ⧸ F))) := hle
    _ ≤ (E.image F.mkQ).card := hcard
    _ ≤ E.card := Finset.card_image_le

/-- The fixed-key span inclusion yields the precise three-box rank bound. -/
theorem a3_key_quot_finrank_le_triples_of_span
    (a b c : ℕ) (k : A3RadicalKey)
    (F : Submodule ℂ V)
    (hspan : a3KeyLayer ρ w k ≤
      Submodule.span ℂ
        (a3ThreeBoxKeyVectors ρ w a b c k.d₁ k.d₂ k.d₃ k.degree : Set V) ⊔ F) :
    Module.finrank ℂ
      (a3KeyLayer ρ w k ⧸ F.comap (a3KeyLayer ρ w k).subtype) ≤
      (a3ThreeBoxKeyTriples a b c k.d₁ k.d₂ k.d₃ k.degree).card := by
  exact (a3_quotient_finrank_le_finset F (a3KeyLayer ρ w k)
    (a3ThreeBoxKeyVectors ρ w a b c k.d₁ k.d₂ k.d₃ k.degree) hspan).trans
      (a3ThreeBoxKeyVectors_card_le ρ w a b c k.d₁ k.d₂ k.d₃ k.degree)

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3ThreeBoxKeyVectors_card_le
#print axioms VOA.DeligneAudit.A3Sector.a3_quotient_finrank_le_finset
#print axioms VOA.DeligneAudit.A3Sector.a3_key_quot_finrank_le_triples_of_span
