import VOA.DeligneAudit.LeviTypeA2CertOrbitRank
import VOA.DeligneAudit.LeviTypeA2Step

/-! Finite orbit spanning gives the rank estimate for a Levi filtration step. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviKeyFiltration

noncomputable section

/-- If a quotient is spanned by `m` Levi orbits of rank at most `L`, its
rank is at most `L * m`. The index `m` will be the key-quotient rank. -/
theorem a2_step_rank_of_orbit_spanning
    {Q : Type} [AddCommGroup Q] [Module ℂ Q] (m L : ℕ)
    (O : Fin m → Submodule ℂ Q)
    (hspan : Finset.univ.sup O = ⊤)
    (hfinite : ∀ j, FiniteDimensional ℂ (O j))
    (hrank : ∀ j, Module.finrank ℂ (O j) ≤ L) :
    FiniteDimensional ℂ Q ∧ Module.finrank ℂ Q ≤ L * m := by
  have haux (s : Finset (Fin m)) :
      FiniteDimensional ℂ (s.sup O : Submodule ℂ Q) ∧
        Module.finrank ℂ (s.sup O : Submodule ℂ Q) ≤ ∑ j ∈ s, L := by
    induction s using Finset.induction_on with
    | empty =>
        constructor
        · simpa only [Finset.sup_empty] using
            (inferInstance : FiniteDimensional ℂ (⊥ : Submodule ℂ Q))
        · simp
    | @insert j s hj ih =>
        haveI : FiniteDimensional ℂ (O j) := hfinite j
        haveI : FiniteDimensional ℂ (s.sup O : Submodule ℂ Q) := ih.1
        rw [Finset.sup_insert, Finset.sum_insert hj]
        exact ⟨inferInstance,
          (Submodule.finrank_add_le_finrank_add_finrank (O j) (s.sup O)).trans
            (Nat.add_le_add (hrank j) ih.2)⟩
  have h := haux Finset.univ
  rw [hspan] at h
  letI : FiniteDimensional ℂ (⊤ : Submodule ℂ Q) := h.1
  have hQ : FiniteDimensional ℂ Q := by
    exact Module.Finite.of_surjective (⊤ : Submodule ℂ Q).subtype
      (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  refine ⟨hQ, ?_⟩
  calc
    Module.finrank ℂ Q ≤ m * L := by
      simpa only [finrank_top, Finset.sum_const, Finset.card_fin,
        nsmul_eq_mul] using h.2
    _ = L * m := Nat.mul_comm _ _

/-- Exact step formulation: one orbit for each member of a key-quotient basis
gives the rank-field certificate's local estimate. -/
theorem a2_step_rank_from_key_orbits
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (F S : ℕ → Submodule ℂ M) (i L : ℕ)
    (O : Fin (Module.finrank ℂ (KeyQuot F S i)) →
      Submodule ℂ (StepQuot F i))
    (hspan : Finset.univ.sup O = ⊤)
    (hfinite : ∀ j, FiniteDimensional ℂ (O j))
    (hrank : ∀ j, Module.finrank ℂ (O j) ≤ L) :
    FiniteDimensional ℂ (StepQuot F i) ∧
      Module.finrank ℂ (StepQuot F i) ≤
        L * Module.finrank ℂ (KeyQuot F S i) :=
  a2_step_rank_of_orbit_spanning _ _ O hspan hfinite hrank

/-- A rank-field version of the all-weight certificate. The step inequality
can be obtained from `a2_step_rank_of_orbit_spanning`. -/
structure A2LeviRankCertificate {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : SectorWeyl.CurrentModule VOA.AffineSl3.bracketTable V)
    (w : V) (p q : ℕ) where
  n : ℕ
  F : ℕ → Submodule ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w)
  S : ℕ → Submodule ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w)
  L : ℕ → ℕ
  g : ℕ → ℕ
  zero : F 0 = ⊥
  top : F n = ⊤
  mono : ∀ i < n, F i ≤ F (i + 1)
  step_finite : ∀ i < n, FiniteDimensional ℂ (StepQuot F i)
  step_rank : ∀ i < n,
    Module.finrank ℂ (StepQuot F i) ≤
      L i * Module.finrank ℂ (KeyQuot F S i)
  multiplicity : ∀ i < n, Module.finrank ℂ (KeyQuot F S i) ≤ g i
  count : (∑ i ∈ Finset.range n, L i * g i) ≤
    VOA.DeligneAudit.LeviTypeA.a2LeviCount p q

/-- The exact open existence proposition for rank-field certificates. -/
def AllA2LeviRankCertificates : Prop :=
  ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : SectorWeyl.CurrentModule VOA.AffineSl3.bracketTable V) (w : V),
    A2LocalWeylRel ρ w p q → Nonempty (A2LeviRankCertificate ρ w p q)

/-- Rank-field certificates imply the all-weight `sl₃` bound. -/
theorem typeA2Bound_of_rank_certificates
    (hc : AllA2LeviRankCertificates) : TypeA2Bound := by
  intro p q V _ _ ρ w h
  obtain ⟨n, F, S, L, g, hz, ht, hm, hfd, hrank, hKS, hcount⟩ :=
    hc p q V ρ w h
  letI : FiniteDimensional ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) :=
    finite_of_finite_steps n F hz ht hm hfd
  refine ⟨inferInstance, ?_⟩
  calc
    Module.finrank ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) ≤
        ∑ i ∈ Finset.range n,
          L i * Module.finrank ℂ (KeyQuot F S i) :=
      key_filtered_weyl_bound n F S L hz ht hm hrank
    _ ≤ ∑ i ∈ Finset.range n, L i * g i := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left _ (hKS i (Finset.mem_range.mp hi))
    _ ≤ 3 ^ p * 3 ^ q := hcount.trans_eq
      (VOA.DeligneAudit.LeviTypeA.a2LeviCount_eq p q)

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_step_rank_of_orbit_spanning
#print axioms VOA.DeligneAudit.A3Sector.a2_step_rank_from_key_orbits
#print axioms VOA.DeligneAudit.A3Sector.typeA2Bound_of_rank_certificates
