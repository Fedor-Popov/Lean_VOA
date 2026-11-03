import VOA.DeligneAudit.LeviTypeA2CertGradedAggregate

/-! Keys with more than `q` second-colour letters have zero key quotient. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.Sl2Weyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

private theorem a2_box_degree_le (m : ℕ) (f : ℕ →₀ ℕ)
    (hf : BoxP m f) : Finsupp.degree f ≤ m := by
  by_cases hzero : f = 0
  · subst f
    simp
  · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hzero
    have h := hf i hi
    have hle := Finsupp.le_degree i f
    omega

/-- The second-colour box has no words longer than its weight. -/
theorem a2TwoBoxKeySpan_bot_of_second_gt (p q a b d : ℕ)
    (hb : q < b) : a2TwoBoxKeySpan ρ w p q a b d = ⊥ := by
  apply eq_bot_iff.mpr
  unfold a2TwoBoxKeySpan
  rw [iSup_le_iff]
  intro d₁
  rw [iSup_le_iff]
  intro d₂
  rw [iSup_le_iff]
  intro _
  rw [a2TwoBoxSpan, Submodule.span_le]
  intro v hv
  obtain ⟨f, g, _, hg, _, hgw, _⟩ := hv
  have hgb : Finsupp.degree g = b := by
    rw [← VOA.DeligneAudit.CLAssembly.length_lst]
    rw [a2_lst_length]
    simpa [hgw]
  have hq := a2_box_degree_le q g hg
  omega

/-- Above the second-colour box, a key layer already lies in its
higher-key Levi closure. -/
theorem a2KeyLayer_le_higher_of_second_gt (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k : A2RadicalKey)
    (hk : q < k.d₂) :
    a2KeyLayer ρ w k ≤
      a2LeviClosure ρ (a2HigherKeySpan ρ w q k) := by
  have hboxes := a2KeyLayer_le_two_boxes ρ w p q h k
  rw [a2TwoBoxKeySpan_bot_of_second_gt ρ w p q
    k.d₁ k.d₂ k.degree hk, bot_sup_eq] at hboxes
  exact hboxes

/-- The multiplicity of a key beyond the second-colour box is zero. -/
theorem a2_key_quot_finrank_zero_of_second_gt (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k : A2RadicalKey)
    (hk : q < k.d₂) :
    let F := a2LeviClosure ρ (a2HigherKeySpan ρ w q k)
    let S := a2KeyLayer ρ w k
    Module.finrank ℂ (S ⧸ F.comap S.subtype) = 0 := by
  let F := a2LeviClosure ρ (a2HigherKeySpan ρ w q k)
  let S := a2KeyLayer ρ w k
  have hS : S ≤ F := a2KeyLayer_le_higher_of_second_gt ρ w p q h k hk
  have htop : F.comap S.subtype = ⊤ := by
    rw [eq_top_iff]
    intro v _
    exact hS v.property
  change Module.finrank ℂ (S ⧸ F.comap S.subtype) = 0
  rw [htop]
  exact Module.finrank_zero_of_subsingleton

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2TwoBoxKeySpan_bot_of_second_gt
#print axioms VOA.DeligneAudit.A3Sector.a2KeyLayer_le_higher_of_second_gt
#print axioms VOA.DeligneAudit.A3Sector.a2_key_quot_finrank_zero_of_second_gt
