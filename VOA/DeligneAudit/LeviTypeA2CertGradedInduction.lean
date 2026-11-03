import VOA.DeligneAudit.LeviTypeA2CertGradedOneStep

/-! Strong induction removes the lower-mode remainder at a fixed key. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.Sl2Weyl VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- All products of two box monomials at the specified radical key. -/
def a2TwoBoxKeySpan (p q a b d : ℕ) : Submodule ℂ V :=
  ⨆ d₁ : ℕ, ⨆ d₂ : ℕ, ⨆ (_ : d₁ + d₂ = d),
    a2TwoBoxSpan ρ w p q a b d₁ d₂

theorem a2TwoBoxSpan_le_key (p q a b d d₁ d₂ : ℕ)
    (hd : d₁ + d₂ = d) :
    a2TwoBoxSpan ρ w p q a b d₁ d₂ ≤
      a2TwoBoxKeySpan ρ w p q a b d := by
  unfold a2TwoBoxKeySpan
  exact le_iSup_of_le d₁ (le_iSup_of_le d₂ (le_iSup_of_le hd le_rfl))

/-- Every radical monomial at a fixed key lies in the two-colour box
span modulo the Levi closure of strictly higher keys. -/
theorem a2_radical_word_two_boxes (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (xs ys : List ℕ) :
    (aWord (fun i => ρ.op 3 i) xs *
      (ys.map fun i => ρ.op 5 i).prod) w ∈
      a2TwoBoxKeySpan ρ w p q xs.length ys.length (xs.sum + ys.sum) ⊔
      a2LeviClosure ρ
        (a2HigherKeySpan ρ w q
          ⟨xs.length, ys.length, xs.sum + ys.sum⟩) := by
  suffices hσ : ∀ σ : ℕ, ∀ xs ys : List ℕ, xs.sum = σ →
      (aWord (fun i => ρ.op 3 i) xs *
        (ys.map fun i => ρ.op 5 i).prod) w ∈
        a2TwoBoxKeySpan ρ w p q xs.length ys.length (xs.sum + ys.sum) ⊔
        a2LeviClosure ρ
          (a2HigherKeySpan ρ w q
            ⟨xs.length, ys.length, xs.sum + ys.sum⟩) by
    exact hσ xs.sum xs ys rfl
  intro σ
  induction σ using Nat.strong_induction_on with
  | h σ ih =>
      intro xs ys hsum
      let C := a2TwoBoxKeySpan ρ w p q xs.length ys.length
        (xs.sum + ys.sum) ⊔
        a2LeviClosure ρ
          (a2HigherKeySpan ρ w q
            ⟨xs.length, ys.length, xs.sum + ys.sum⟩)
      have hstep := a2_boxes_one_step ρ w p q h xs ys.length ys.sum
        (a2_mono_hom ys)
      have hstep' :
          (aWord (fun i => ρ.op 3 i) xs *
            (ys.map fun i => ρ.op 5 i).prod) w ∈
          a2TwoBoxSpan ρ w p q xs.length ys.length xs.sum ys.sum ⊔
            (a2ModeLowerSpan ρ w xs.length ys.length
              (xs.sum + ys.sum) xs.sum ⊔
              a2LeviClosure ρ
                (a2HigherKeySpan ρ w q
                  ⟨xs.length, ys.length, xs.sum + ys.sum⟩)) := by
        simpa only [VOA.DeligneAudit.CLAssembly.evAlg_mono] using hstep
      have hbox : a2TwoBoxSpan ρ w p q xs.length ys.length xs.sum ys.sum ≤ C :=
        (a2TwoBoxSpan_le_key ρ w p q xs.length ys.length
          (xs.sum + ys.sum) xs.sum ys.sum rfl).trans le_sup_left
      have hlower : a2ModeLowerSpan ρ w xs.length ys.length
          (xs.sum + ys.sum) xs.sum ≤ C := by
        rw [a2ModeLowerSpan, Submodule.span_le]
        intro v hv
        obtain ⟨zs, bs, hza, hbs, hd, hsmall, rfl⟩ := hv
        have hz := ih zs.sum (by omega) zs bs rfl
        simpa only [C, hza, hbs, hd] using hz
      have hhigher : a2LeviClosure ρ
          (a2HigherKeySpan ρ w q
            ⟨xs.length, ys.length, xs.sum + ys.sum⟩) ≤ C := le_sup_right
      exact (sup_le hbox (sup_le hlower hhigher)) hstep'

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2TwoBoxSpan_le_key
#print axioms VOA.DeligneAudit.A3Sector.a2_radical_word_two_boxes
