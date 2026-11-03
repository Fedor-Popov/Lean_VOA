import VOA.DeligneAudit.LeviTypeA2CertGradedF2Box
import VOA.DeligneAudit.LeviTypeA2CertFirstBoxGraded

/-! Apply the exact first-colour box to fixed-key F₂ box terms. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.Sl2Weyl VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- Products of both sl₂ box monomials with specified individual degrees. -/
def a2TwoBoxSpan (p q a b d₁ d₂ : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ (f g : ℕ →₀ ℕ),
    BoxP p f ∧ BoxP q g ∧
      Finsupp.weight om f = (a, d₁) ∧
        Finsupp.weight om g = (b, d₂) ∧
          v = (Sl2Weyl.evAlg (fun i => ρ.op 3 i)
            (VOA.DeligneAudit.A2.CVRoots.sl2_first ρ).hFF
            (MvPolynomial.monomial f 1) *
            Sl2Weyl.evAlg (fun i => ρ.op 5 i) (by
              intro i j
              apply sub_eq_zero.mp
              simp [op_comm_end, Fin.sum_univ_eight,
                VOA.AffineSl3.bracketTable])
              (MvPolynomial.monomial g 1)) w}

theorem a2_mono_hom (xs : List ℕ) :
    (VOA.DeligneAudit.CLAssembly.mono xs).IsWeightedHomogeneous om
      (xs.length, xs.sum) := by
  induction xs with
  | nil =>
      simpa [VOA.DeligneAudit.CLAssembly.mono] using
        MvPolynomial.isWeightedHomogeneous_one ℂ om
  | cons s xs ih =>
      have hz : (z s).IsWeightedHomogeneous om (1, s) :=
        MvPolynomial.isWeightedHomogeneous_X ℂ om s
      have hm := hz.mul ih
      simpa [VOA.DeligneAudit.CLAssembly.mono, Nat.add_comm] using hm

/-- The F₁ box acts exactly on an F₂ box word. -/
theorem a2_f2_boxSpan_le_twoBox (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (xs : List ℕ) (b d₂ : ℕ) :
    a2F2BoxSpan ρ w xs q b d₂ ≤
      a2TwoBoxSpan ρ w p q xs.length b xs.sum d₂ := by
  rw [a2F2BoxSpan, Submodule.span_le]
  intro v hv
  obtain ⟨g, hg, hgw, rfl⟩ := hv
  let ys := VOA.DeligneAudit.CLAssembly.lst g
  let F₁ : ℕ → Module.End ℂ V := fun i => ρ.op 3 i
  let F₂ : ℕ → Module.End ℂ V := fun i => ρ.op 5 i
  let h₂ : ∀ i j, F₂ i * F₂ j = F₂ j * F₂ i := by
    intro i j
    apply sub_eq_zero.mp
    simp [F₂, op_comm_end, Fin.sum_univ_eight,
      VOA.AffineSl3.bracketTable]
  have hword : Sl2Weyl.evAlg F₂ h₂ (MvPolynomial.monomial g 1) =
      (ys.map F₂).prod := a2_evAlg_monomial_word F₂ h₂ g
  have hbox := a2_first_box_graded_with_spectators ρ w p q h ys
    (a2_mono_hom xs)
  have hinput : (aWord F₁ xs *
      Sl2Weyl.evAlg F₂ h₂ (MvPolynomial.monomial g 1)) w ∈
      Submodule.span ℂ {v | ∃ f, BoxP p f ∧
        Finsupp.weight om f = (xs.length, xs.sum) ∧
        v = Sl2Weyl.evAlg F₁
          (VOA.DeligneAudit.A2.CVRoots.sl2_first ρ).hFF
          (MvPolynomial.monomial f 1) ((ys.map F₂).prod w)} := by
    rw [hword]
    simpa [F₁, F₂, aWord, Module.End.mul_apply,
      VOA.DeligneAudit.CLAssembly.evAlg_mono] using hbox
  have hle : Submodule.span ℂ {v | ∃ f, BoxP p f ∧
        Finsupp.weight om f = (xs.length, xs.sum) ∧
        v = Sl2Weyl.evAlg F₁
          (VOA.DeligneAudit.A2.CVRoots.sl2_first ρ).hFF
          (MvPolynomial.monomial f 1) ((ys.map F₂).prod w)} ≤
      a2TwoBoxSpan ρ w p q xs.length b xs.sum d₂ := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨f, hf, hfw, rfl⟩ := hz
    apply Submodule.subset_span
    refine ⟨f, g, hf, hg, hfw, hgw, ?_⟩
    rw [hword]
    rfl
  exact hle hinput

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_f2_boxSpan_le_twoBox
#print axioms VOA.DeligneAudit.A3Sector.a2_mono_hom
