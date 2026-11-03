import VOA.DeligneAudit.LeviTypeA3GradedPairOneStep
import VOA.DeligneAudit.LeviTypeA3GradedResidual
import VOA.DeligneAudit.LeviTypeA3HigherPrefix

/-! The finite three-box target for the fixed-key induction. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.LeviConversion

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- The finite target for the two adjacent-pair reductions at one key. -/
def a3ThreeBoxTarget (a b c : ℕ) (k : A3RadicalKey) : Submodule ℂ V :=
  Submodule.span ℂ
    (a3ThreeBoxKeyVectors ρ w a b c k.d₁ k.d₂ k.d₃ k.degree : Set V) ⊔
    a3HigherLeviClosure ρ w b c k

theorem a3_mode_set_degree (m d : ℕ) (f : ℕ →₀ ℕ)
    (hf : f ∈ a2BoxModeSet m d) : Finsupp.degree f = d := by
  rw [a2BoxModeSet, Finset.mem_finsuppAntidiag'] at hf
  simpa [Finsupp.degree_apply] using hf.1

theorem a3_three_box_triple_data (a b c : ℕ) (k : A3RadicalKey)
    (fg : ((ℕ →₀ ℕ) × (ℕ →₀ ℕ)) × (ℕ →₀ ℕ))
    (hfg : fg ∈ a3ThreeBoxKeyTriples a b c k.d₁ k.d₂ k.d₃ k.degree) :
    Finsupp.degree fg.1.1 = k.d₁ ∧
    Finsupp.degree fg.1.2 = k.d₂ ∧
    Finsupp.degree fg.2 = k.d₃ ∧
    a3BoxDegree fg = k.degree := by
  simp only [a3ThreeBoxKeyTriples, Finset.mem_filter, a3ThreeBoxModeSet,
    Finset.mem_product] at hfg
  rcases hfg with ⟨⟨⟨hf, hg⟩, hh⟩, hd⟩
  exact ⟨a3_mode_set_degree a k.d₁ fg.1.1 hf,
    a3_mode_set_degree b k.d₂ fg.1.2 hg,
    a3_mode_set_degree c k.d₃ fg.2 hh, hd⟩

/-- Every finite three-box vector is a word in the stated radical key. -/
theorem a3ThreeBoxKeyVectors_le_layer (a b c : ℕ) (k : A3RadicalKey) :
    (a3ThreeBoxKeyVectors ρ w a b c k.d₁ k.d₂ k.d₃ k.degree : Set V) ⊆
      a3KeyLayer ρ w k := by
  classical
  intro v hv
  obtain ⟨fg, hfg, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hfdeg, hgdeg, hhdeg, hd⟩ :=
    a3_three_box_triple_data a b c k fg hfg
  have hlen₁ : (VOA.DeligneAudit.CLAssembly.lst fg.1.1).length = k.d₁ := by
    simpa [a2_lst_length, Finsupp.weight_apply, om, Finsupp.degree_apply,
      Finsupp.sum, Prod.fst_sum] using hfdeg
  have hlen₂ : (VOA.DeligneAudit.CLAssembly.lst fg.1.2).length = k.d₂ := by
    simpa [a2_lst_length, Finsupp.weight_apply, om, Finsupp.degree_apply,
      Finsupp.sum, Prod.fst_sum] using hgdeg
  have hlen₃ : (VOA.DeligneAudit.CLAssembly.lst fg.2).length = k.d₃ := by
    simpa [a2_lst_length, Finsupp.weight_apply, om, Finsupp.degree_apply,
      Finsupp.sum, Prod.fst_sum] using hhdeg
  have hsum : (VOA.DeligneAudit.CLAssembly.lst fg.1.1).sum +
      (VOA.DeligneAudit.CLAssembly.lst fg.1.2).sum +
      (VOA.DeligneAudit.CLAssembly.lst fg.2).sum = k.degree := by
    simpa [a3BoxDegree, a2_lst_sum] using hd
  have hw := a3_three_mode_mem_key ρ w
    (VOA.DeligneAudit.CLAssembly.lst fg.1.1)
    (VOA.DeligneAudit.CLAssembly.lst fg.1.2)
    (VOA.DeligneAudit.CLAssembly.lst fg.2)
  simpa only [a3ThreeBoxKeyVectors, a3ThreeBoxValue,
    hlen₁, hlen₂, hlen₃, hsum] using hw

theorem a3ThreeBoxTarget_le_layer_sup (a b c : ℕ) (k : A3RadicalKey) :
    a3ThreeBoxTarget ρ w a b c k ≤
      a3KeyLayer ρ w k ⊔ a3HigherLeviClosure ρ w b c k := by
  unfold a3ThreeBoxTarget
  exact sup_le (Submodule.span_le.mpr
    (fun _ hv => (show a3KeyLayer ρ w k ≤ _ from le_sup_left)
      (a3ThreeBoxKeyVectors_le_layer ρ w a b c k hv)))
    le_sup_right

theorem a3_key_rank_of_target (a b c : ℕ) (k : A3RadicalKey)
    (hspan : a3KeyLayer ρ w k ≤ a3ThreeBoxTarget ρ w a b c k) :
    Module.finrank ℂ
      (a3KeyLayer ρ w k ⧸
        (a3HigherLeviClosure ρ w b c k).comap (a3KeyLayer ρ w k).subtype) ≤
      (a3ThreeBoxKeyTriples a b c k.d₁ k.d₂ k.d₃ k.degree).card := by
  exact a3_key_quot_finrank_le_triples_of_span ρ w a b c k
    (a3HigherLeviClosure ρ w b c k) hspan

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_three_box_triple_data
#print axioms VOA.DeligneAudit.A3Sector.a3ThreeBoxKeyVectors_le_layer
#print axioms VOA.DeligneAudit.A3Sector.a3ThreeBoxTarget_le_layer_sup
#print axioms VOA.DeligneAudit.A3Sector.a3_key_rank_of_target
#print axioms VOA.DeligneAudit.A3Sector.a3_mode_set_degree
