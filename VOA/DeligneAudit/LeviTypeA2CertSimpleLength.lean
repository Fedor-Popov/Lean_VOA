import VOA.DeligneAudit.LeviTypeA2CertBoxLength

/-! Length cutoff for the simple radical colour. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- Any product of more than `p` first-colour modes kills `w`. -/
theorem a2_simple_word_length_zero (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (l : List ℕ) (hl : p < l.length) :
    (l.map fun s => ρ.op 3 s).prod w = 0 := by
  let F : ℕ → Module.End ℂ V := fun s => ρ.op 3 s
  let H : ℕ → Module.End ℂ V := fun s => ρ.op 6 s
  let E : Module.End ℂ V := ρ.op 0 1
  have hFF : ∀ i j, F i * F j = F j * F i := by
    intro i j
    apply sub_eq_zero.mp
    simp [F, op_comm_end, Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
  have hEF : ∀ k, E * F k - F k * E = H (k + 1) := by
    intro k
    rw [op_comm_end]
    simp [H, Fin.sum_univ_eight, VOA.AffineSl3.bracketTable,
      Nat.add_comm]
  have hHF : ∀ m k,
      H (m + 1) * F k - F k * H (m + 1) =
        (-2 : ℂ) • F (m + 1 + k) := by
    intro m k
    rw [op_comm_end]
    simp [F, Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
  have hE : E w = 0 := h.raising 0 (by decide) 1
  have hH : ∀ m, H (m + 1) w = 0 := by
    intro m
    exact h.cartan_pos 6 (by decide) _ (by omega)
  have hN : (F 0 ^ (p + 1)) w = 0 := by
    simpa [F, Module.End.pow_apply] using h.lowering_first
  have hk : ∀ r s, 1 ≤ r → p + 1 ≤ r + s →
      (PowerSeries.coeff s (Garland.Fs F ^ r)) w = 0 := by
    intro r s hr hrs
    exact Garland.garland hEF hHF hFF hE hH r hr hN s hrs
  exact sl2_box_word_length_zero F hFF w p hk l hl

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_simple_word_length_zero
