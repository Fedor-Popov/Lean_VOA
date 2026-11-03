import VOA.DeligneAudit.D4FusionToroidalPresentedTwoLayerShift

/-! The exact Garland family in the multiplicity-two presentation. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

theorem two_JprimeSyntax_iff (z : FreeT 28) :
    z ∈ JprimeSyntax 2 ↔
      (∃ t ∈ (ravFam D4sector 2 0).tails,
        z = swT (symbolLetters 2 t)) ∨
      (∃ N, 1 ≤ N ∧ z = psymSyntax D4sector.c₀ 1 N) := by
  constructor
  · rintro (h | ⟨j, N, hj, hjm, hN, hz⟩)
    · exact Or.inl h
    · have hj' : j = 1 := by omega
      subst j
      exact Or.inr ⟨N, by omega, hz⟩
  · rintro (h | ⟨N, hN, hz⟩)
    · exact Or.inl h
    · exact Or.inr ⟨1, N, by omega, by omega, by omega, hz⟩

theorem two_garland_one_syntax (N : ℕ) (hN : 1 ≤ N) :
    psymSyntax D4sector.c₀ 1 N ∈ JprimeSyntaxE 2 := by
  exact Or.inl ((two_JprimeSyntax_iff _).mpr
    (Or.inr ⟨N, hN, rfl⟩))

theorem evalT_rhoPTE_two (z : FreeT 28) :
    evalT (ρPTE 2) (pTE 2) z =
      (JT D4sector.f 2 (JprimeSyntaxE 2)).mkQ z := by
  have hmap : evalT (ρPTE 2) (pTE 2) =
      (JT D4sector.f 2 (JprimeSyntaxE 2)).mkQ := by
    apply Finsupp.lhom_ext'
    intro l
    apply LinearMap.ext_ring
    change evalT (ρPTE 2) (pTE 2) (swT l) =
      (JT D4sector.f 2 (JprimeSyntaxE 2)).mkQ (swT l)
    rw [evalT_swT]
    exact wordOpT_rhoPT D4sector.f 2 (JprimeSyntaxE 2) l
  exact LinearMap.congr_fun hmap z

theorem two_garland_one_zero (N : ℕ) (hN : 1 ≤ N) :
    Psym (ρPTE 2) D4sector.c₀ 1 N (pTE 2) = 0 := by
  rw [← evalT_psymSyntax, evalT_rhoPTE_two]
  exact mk_syntax D4sector.f 2 (JprimeSyntaxE 2)
    (psymSyntax D4sector.c₀ 1 N) (two_garland_one_syntax N hN)

theorem two_garland_quadratic_relation :
    prefixT [(D4sector.c₀, 1, 0)]
      (psymSyntax D4sector.c₀ 1 1) ∈
        JT D4sector.f 2 (JprimeSyntaxE 2) := by
  apply Submodule.subset_span
  exact ⟨[(D4sector.c₀, 1, 0)],
    Or.inr (Or.inr ⟨psymSyntax D4sector.c₀ 1 1,
      two_garland_one_syntax 1 (by omega), rfl⟩)⟩

theorem two_garland_quadratic_zero :
    ((JT D4sector.f 2 (JprimeSyntaxE 2)).mkQ
      (prefixT [(D4sector.c₀, 1, 0)]
        (psymSyntax D4sector.c₀ 1 1)) : PTE 2) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr two_garland_quadratic_relation

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_JprimeSyntax_iff
#print axioms VOA.DeligneAudit.Toroidal.two_garland_one_syntax
#print axioms VOA.DeligneAudit.Toroidal.evalT_rhoPTE_two
#print axioms VOA.DeligneAudit.Toroidal.two_garland_one_zero
#print axioms VOA.DeligneAudit.Toroidal.two_garland_quadratic_relation
#print axioms VOA.DeligneAudit.Toroidal.two_garland_quadratic_zero
