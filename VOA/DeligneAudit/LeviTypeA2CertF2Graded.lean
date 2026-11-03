import VOA.DeligneAudit.LeviTypeA2CertGradedConversion
import VOA.DeligneAudit.LeviTypeA2CertF2Defect

/-! The second-colour box conversion at one fixed radical key. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- The F₂ defect preserves the two radical counts and the total mode degree.
Only the first-colour mode sum decreases; all other Wick terms lie in the
Levi closure of strictly higher keys. -/
theorem a2_f2_box_conversion_graded (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k s : ℕ)
    (hk : 1 ≤ k) (hks : q + 1 ≤ k + s)
    (xs ys : List ℕ) :
    boxTarget (fun i => ρ.op 3 i) (fun i => ρ.op 5 i)
      k s xs ys 1 w ∈
      gradedLowerModeSpan (fun i => ρ.op 3 i) (fun i => ρ.op 5 i)
        xs ys k (xs.sum + ys.sum + s) 1 w ⊔
      a2LeviClosure ρ
        (a2HigherKeySpan ρ w q
          ⟨xs.length, ys.length + k, xs.sum + ys.sum + s⟩) := by
  apply box_conversion_graded (fun i => ρ.op 4 i)
    (fun i => ρ.op 3 i) (fun i => ρ.op 5 i)
    ?_ ?_ ?_ ?_ k s xs ys 1 w
    ?_ (a2_node2_conversion_kill ρ w p q h k s hk hks) ?_ _ ?_
  · intro i j
    rw [op_comm_end]
    simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
  · intro i j
    apply sub_eq_zero.mp
    rw [op_comm_end]
    simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
  · intro i j
    apply sub_eq_zero.mp
    rw [op_comm_end]
    simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
  · intro i j
    apply sub_eq_zero.mp
    rw [op_comm_end]
    simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
  · intro i
    simp
  · intro c v
    simp
  · intro t ht hlt
    exact a2_f2_lower_wick_higher ρ w q k s xs ys
      (xs.sum + ys.sum + s) t ht hlt

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_f2_box_conversion_graded
