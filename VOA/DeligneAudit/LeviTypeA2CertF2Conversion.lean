import VOA.DeligneAudit.LeviTypeA2CertConversionKill

/-! Apply the universal box conversion to the three A₂ current families. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- The node-two lowering current converts a first radical current into a
compound radical current. The uncontracted Wick terms are the only remaining
input to the F₂ box conversion. -/
theorem a2_f2_box_conversion (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k s : ℕ)
    (hk : 1 ≤ k) (hks : q + 1 ≤ k + s)
    (xs ys : List ℕ) (N : Submodule ℂ V)
    (hHigher : ∀ t ∈ choices (xs ++ List.replicate k 0), t.2.length < k →
      conversionTerm (fun i => ρ.op 4 i) (fun i => ρ.op 3 i)
        (fun i => ρ.op 5 i) k s t •
        (((ys.map fun i => ρ.op 5 i).prod * 1) • w) ∈ N) :
    boxTarget (fun i => ρ.op 3 i) (fun i => ρ.op 5 i)
      k s xs ys 1 w ∈
      lowerModeSpan (fun i => ρ.op 3 i) (fun i => ρ.op 5 i)
        xs 1 w ⊔ N := by
  apply box_conversion (fun i => ρ.op 4 i) (fun i => ρ.op 3 i)
    (fun i => ρ.op 5 i) ?_ ?_ ?_ ?_ k s xs ys 1 w
    ?_ (a2_node2_conversion_kill ρ w p q h k s hk hks) ?_ N hHigher
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

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_f2_box_conversion
