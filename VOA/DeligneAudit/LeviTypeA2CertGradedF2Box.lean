import VOA.DeligneAudit.LeviTypeA2CertGradedModeSpan

/-! The full second-colour box reduction at one fixed key. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.Sl2Weyl VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- Fixed-key F₂ box monomials with a first-colour word on the left. -/
def a2F2BoxSpan (xs : List ℕ) (q b d₂ : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ f : ℕ →₀ ℕ,
    BoxP q f ∧ Finsupp.weight om f = (b, d₂) ∧
      v = (aWord (fun i => ρ.op 3 i) xs *
        Sl2Weyl.evAlg (fun i => ρ.op 5 i) (by
          intro i j
          apply sub_eq_zero.mp
          simp [op_comm_end, Fin.sum_univ_eight,
            VOA.AffineSl3.bracketTable])
          (MvPolynomial.monomial f 1)) w}

/-- F₂ box reduction preserves its radical key. The Garland defects
reduce the first-colour mode sum or enter the higher-key Levi closure. -/
theorem a2_f2_box_fixed_key (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (xs : List ℕ) (b d₂ : ℕ) {P : R}
    (hP : P.IsWeightedHomogeneous om (b, d₂)) :
    let F : ℕ → Module.End ℂ V := fun i => ρ.op 5 i
    let hFF : ∀ i j, F i * F j = F j * F i := by
      intro i j
      apply sub_eq_zero.mp
      simp [F, op_comm_end, Fin.sum_univ_eight,
        VOA.AffineSl3.bracketTable]
    (aWord (fun i => ρ.op 3 i) xs * Sl2Weyl.evAlg F hFF P) w ∈
      a2F2BoxSpan ρ w xs q b d₂ ⊔
        (a2ModeLowerSpan ρ w xs.length b (xs.sum + d₂) xs.sum ⊔
          a2LeviClosure ρ
            (a2HigherKeySpan ρ w q ⟨xs.length, b, xs.sum + d₂⟩)) := by
  let F : ℕ → Module.End ℂ V := fun i => ρ.op 5 i
  let hFF : ∀ i j, F i * F j = F j * F i := by
    intro i j
    apply sub_eq_zero.mp
    simp [F, op_comm_end, Fin.sum_univ_eight,
      VOA.AffineSl3.bracketTable]
  let T : Module.End ℂ V := aWord (fun i => ρ.op 3 i) xs
  let B := a2F2BoxSpan ρ w xs q b d₂
  let N := a2ModeLowerSpan ρ w xs.length b (xs.sum + d₂) xs.sum ⊔
    a2LeviClosure ρ
      (a2HigherKeySpan ρ w q ⟨xs.length, b, xs.sum + d₂⟩)
  have hmapB : ∀ v ∈ Submodule.span ℂ
      {z | ∃ f, BoxP q f ∧ Finsupp.weight om f = (b, d₂) ∧
        z = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) w},
      T v ∈ B := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨f, hf, hw, rfl⟩ := hv
        exact Submodule.subset_span ⟨f, hf, hw, rfl⟩
    | zero => simp
    | add v z _ _ hv hz =>
        rw [map_add]
        exact B.add_mem hv hz
    | smul c v _ hv =>
        rw [map_smul]
        exact B.smul_mem c hv
  have hmapD : ∀ v ∈ a2GradedDefect F hFF w q (b, d₂), T v ∈ N := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨f, r, s, hr, hrs, hw, rfl⟩ := hv
        exact a2_f2_defect_reduces_mode ρ w p q h xs f r s b d₂
          hr hrs hw
    | zero => simp
    | add v z _ _ hv hz =>
        rw [map_add]
        exact N.add_mem hv hz
    | smul c v _ hv =>
        rw [map_smul]
        exact N.smul_mem c hv
  obtain ⟨vB, hvB, vD, hvD, hsum⟩ := Submodule.mem_sup.mp
    (a2_span_box_graded_explicit_eval F hFF w q hP)
  change T (Sl2Weyl.evAlg F hFF P w) ∈ B ⊔ N
  rw [← hsum, map_add]
  exact Submodule.add_mem_sup (hmapB vB hvB) (hmapD vD hvD)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_f2_box_fixed_key
