import VOA.DeligneAudit.LeviTypeA2Cutoff
import VOA.DeligneAudit.LeviTypeA2Count
import VOA.DeligneAudit.LeviTypeAStep
import VOA.DeligneAudit.LeviTypeAStepSl2

/-! The exact remaining key-filtration certificate for the all-weight `sl₃` bound. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviKeyFiltration

noncomputable section

/-- Data still needed to instantiate the Levi step on the cyclic `sl₃` module.
`stage` is PBW/Levi generation; `surj` is the local Weyl quotient at a key;
`multiplicity` is (KS), and `count` maps the keys to the binomial budget. -/
structure A2LeviCertificate {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : SectorWeyl.CurrentModule VOA.AffineSl3.bracketTable V)
    (w : V) (p q : ℕ) where
  n : ℕ
  F : ℕ → Submodule ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w)
  S : ℕ → Submodule ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w)
  closure : Submodule ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) →
    Submodule ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w)
  L : ℕ → ℕ
  g : ℕ → ℕ
  zero : F 0 = ⊥
  top : F n = ⊤
  stage : ∀ i < n, F (i + 1) = F i ⊔ closure (S i)
  key_finite : ∀ i < n, FiniteDimensional ℂ (S i)
  surj : ∀ i < n,
    ∃ φ : (Fin (L i) → KeyQuot F S i) →ₗ[ℂ] StepQuot F i,
      Function.Surjective φ
  multiplicity : ∀ i < n, Module.finrank ℂ (KeyQuot F S i) ≤ g i
  count : (∑ i ∈ Finset.range n, L i * g i) ≤
    VOA.DeligneAudit.LeviTypeA.a2LeviCount p q

/-- The specific unproved proposition needed by the conditional theorem. -/
def AllA2LeviCertificates : Prop :=
  ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : SectorWeyl.CurrentModule VOA.AffineSl3.bracketTable V) (w : V),
    A2LocalWeylRel ρ w p q → Nonempty (A2LeviCertificate ρ w p q)

/-- Certificates for every local Weyl generator give the exact all-weight
`sl₃` theorem. The certificate construction remains open. -/
theorem typeA2Bound_of_certificates
    (hc : AllA2LeviCertificates) : TypeA2Bound := by
  intro p q V _ _ ρ w h
  obtain ⟨n, F, S, C, L, g, hz, ht, hs, hf, hsurj, hKS, hcount⟩ :=
    hc p q V ρ w h
  obtain ⟨hfd, hrank⟩ :=
    VOA.DeligneAudit.LeviTypeA.levi_step_bound n F S C L g
      hz ht hs hf hsurj hKS
  exact ⟨hfd, hrank.trans (hcount.trans_eq
    (VOA.DeligneAudit.LeviTypeA.a2LeviCount_eq p q))⟩

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.typeA2Bound_of_certificates
