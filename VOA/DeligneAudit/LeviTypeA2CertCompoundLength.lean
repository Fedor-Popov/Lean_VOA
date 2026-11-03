import VOA.DeligneAudit.LeviTypeA2CertSimpleCount

/-! Compound-root box length, conditional on sharp zero-mode nilpotence. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- The exact missing zero-mode input for the compound-root sl₂ box. -/
def A2CompoundNilpotence (p q : ℕ) : Prop :=
  (ρ.op 5 0 ^ (p + q + 1)) w = 0

/-- The compound-root analogue of the first-colour word cutoff. -/
theorem a2_compound_word_length_zero (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (hN : A2CompoundNilpotence ρ w p q)
    (l : List ℕ) (hl : p + q < l.length) :
    (l.map fun s => ρ.op 5 s).prod w = 0 := by
  let F : ℕ → Module.End ℂ V := fun s => ρ.op 5 s
  let H : ℕ → Module.End ℂ V := fun s => ρ.op 6 s + ρ.op 7 s
  let E : Module.End ℂ V := ρ.op 2 1
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
    calc
      _ = (ρ.op 6 (m + 1) * F k - F k * ρ.op 6 (m + 1)) +
            (ρ.op 7 (m + 1) * F k - F k * ρ.op 7 (m + 1)) := by
              simp only [H, add_mul, mul_add, sub_eq_add_neg, neg_add_rev]
              abel
      _ = (-2 : ℂ) • F (m + 1 + k) := by
        rw [op_comm_end, op_comm_end]
        simp [F, Fin.sum_univ_eight, VOA.AffineSl3.bracketTable,
          two_smul]
  have hE : E w = 0 := h.raising 2 (by decide) 1
  have hH : ∀ m, H (m + 1) w = 0 := by
    intro m
    have h6 := h.cartan_pos 6 (by decide) (m + 1) (by omega)
    have h7 := h.cartan_pos 7 (by decide) (m + 1) (by omega)
    simp [H, h6, h7]
  have hN' : (F 0 ^ (p + q + 1)) w = 0 := hN
  have hk : ∀ r s, 1 ≤ r → p + q + 1 ≤ r + s →
      (PowerSeries.coeff s (Garland.Fs F ^ r)) w = 0 := by
    intro r s hr hrs
    exact Garland.garland hEF hHF hFF hE hH r hr hN' s hrs
  exact sl2_box_word_length_zero F hFF w (p + q) hk l hl

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_compound_word_length_zero
