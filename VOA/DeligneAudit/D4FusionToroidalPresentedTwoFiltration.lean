import VOA.DeligneAudit.D4FusionToroidalPresentedEigCore
import VOA.DeligneAudit.D4FusionContactTwo

/-! The decreasing filtration by total toroidal u-degree at multiplicity two. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

def twoUDeg : List (TLtr 28) → ℕ
  | [] => 0
  | x :: l => x.2.1 + twoUDeg l

def twoN (j : ℕ) : Submodule ℂ (PTE 2) :=
  Submodule.span ℂ {v | ∃ l, j ≤ twoUDeg l ∧
    v = wordOpT (ρPTE 2) l (pTE 2)}

theorem twoN_word (j : ℕ) (l : List (TLtr 28)) (hl : j ≤ twoUDeg l) :
    wordOpT (ρPTE 2) l (pTE 2) ∈ twoN j :=
  Submodule.subset_span ⟨l, hl, rfl⟩

theorem twoN_mono {j k : ℕ} (h : j ≤ k) : twoN k ≤ twoN j := by
  apply Submodule.span_mono
  rintro v ⟨l, hl, rfl⟩
  exact ⟨l, h.trans hl, rfl⟩

theorem twoN_zero : twoN 0 = ⊤ := by
  calc
    twoN 0 = Submodule.span ℂ (Set.range fun l : List (TLtr 28) =>
        wordOpT (ρPTE 2) l (pTE 2)) := by
      apply congrArg (Submodule.span ℂ)
      ext v
      constructor
      · rintro ⟨l, _, rfl⟩
        exact ⟨l, rfl⟩
      · rintro ⟨l, rfl⟩
        exact ⟨l, Nat.zero_le _, rfl⟩
    _ = ⊤ := PTE_cyclic 2

theorem twoN_op (j : ℕ) (c : Fin 28) (i s : ℕ) :
    twoN j ≤ (twoN j).comap ((ρPTE 2).op c i s) := by
  rw [twoN, Submodule.span_le]
  rintro v ⟨l, hl, rfl⟩
  change (ρPTE 2).op c i s (wordOpT (ρPTE 2) l (pTE 2)) ∈ twoN j
  change wordOpT (ρPTE 2) ((c, i, s) :: l) (pTE 2) ∈ twoN j
  exact twoN_word j _ (by simp only [twoUDeg]; omega)

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.twoN_word
#print axioms VOA.DeligneAudit.Toroidal.twoN_mono
#print axioms VOA.DeligneAudit.Toroidal.twoN_zero
#print axioms VOA.DeligneAudit.Toroidal.twoN_op
