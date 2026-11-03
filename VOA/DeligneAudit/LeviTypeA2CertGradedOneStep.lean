import VOA.DeligneAudit.LeviTypeA2CertGradedTwoBox

/-! One fixed-key reduction with both colour boxes. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.Sl2Weyl VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- Both boxes at one key, modulo smaller first-colour mode sum
and Levi closure of strictly higher radical keys. -/
theorem a2_boxes_one_step (p q : ℕ)
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
      a2TwoBoxSpan ρ w p q xs.length b xs.sum d₂ ⊔
        (a2ModeLowerSpan ρ w xs.length b (xs.sum + d₂) xs.sum ⊔
          a2LeviClosure ρ
            (a2HigherKeySpan ρ w q ⟨xs.length, b, xs.sum + d₂⟩)) := by
  have hstep := a2_f2_box_fixed_key ρ w p q h xs b d₂ hP
  exact (sup_le_sup_right (a2_f2_boxSpan_le_twoBox ρ w p q h xs b d₂) _) hstep

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_boxes_one_step
