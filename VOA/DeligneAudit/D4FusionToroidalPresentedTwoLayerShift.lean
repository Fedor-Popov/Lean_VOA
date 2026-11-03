import VOA.DeligneAudit.D4FusionToroidalPresentedTwoAssembly

/-! The toroidal action raises the u-degree filtration by its own u-degree. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

theorem twoN_op_shift (j : ℕ) (c : Fin 28) (i s : ℕ) :
    twoN j ≤ (twoN (j + i)).comap ((ρPTE 2).op c i s) := by
  rw [twoN, Submodule.span_le]
  rintro v ⟨l, hl, rfl⟩
  change wordOpT (ρPTE 2) ((c, i, s) :: l) (pTE 2) ∈ twoN (j + i)
  exact twoN_word (j + i) _ (by simp only [twoUDeg]; omega)

theorem twoN2inN1_subtype (v : twoN 1) :
    v ∈ twoN2inN1 ↔ (v : PTE 2) ∈ twoN 2 := Iff.rfl

theorem twoN2inN1_op (c : Fin 28) (i s : ℕ) (v : twoN 1)
    (hv : v ∈ twoN2inN1) :
    (ρPTE 2).op c i s (v : PTE 2) ∈ twoN 2 := by
  exact twoN_op 2 c i s (twoN2inN1_subtype v |>.mp hv)

theorem twoN_positive_op (c : Fin 28) (i s : ℕ) (v : twoN 1) :
    (ρPTE 2).op c i s (v : PTE 2) ∈ twoN 1 := by
  exact twoN_op 1 c i s v.property

theorem twoN_positive_degree_one (c : Fin 28) (s : ℕ) (v : twoN 1) :
    (ρPTE 2).op c 1 s (v : PTE 2) ∈ twoN 2 := by
  exact twoN_op_shift 1 c 1 s v.property

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.twoN_op_shift
#print axioms VOA.DeligneAudit.Toroidal.twoN2inN1_subtype
#print axioms VOA.DeligneAudit.Toroidal.twoN2inN1_op
#print axioms VOA.DeligneAudit.Toroidal.twoN_positive_op
#print axioms VOA.DeligneAudit.Toroidal.twoN_positive_degree_one
