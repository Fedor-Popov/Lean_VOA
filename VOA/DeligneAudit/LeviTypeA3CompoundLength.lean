import VOA.DeligneAudit.LeviTypeA3HighestNil

/-! Garland box length for the first compound radical colour. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

private theorem op_comm_end (x y : Fin 15) (r s : ℕ) :
    ρ.op x r * ρ.op y s - ρ.op y s * ρ.op x r =
      ∑ e, bracketTable x y e • ρ.op e (r + s) := by
  ext v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.smul_apply]
  exact ρ.comm x y r s v

/-- More than `a+b` modes of `E₂₀` kill the generator. -/
theorem a3_compound_word_length_zero (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (l : List ℕ) (hl : a + b < l.length) :
    (l.map fun s => ρ.op (F 1) s).prod w = 0 := by
  let G : ℕ → Module.End ℂ V := fun s => ρ.op (F 1) s
  let H : ℕ → Module.End ℂ V := fun s => ρ.op 12 s + ρ.op 13 s
  let E : Module.End ℂ V := ρ.op 1 1
  have hFF : ∀ r s, G r * G s = G s * G r := by
    intro r s
    simpa [G, radicalOp] using radicalOp_comm ρ 1 r 1 s
  have hEF : ∀ k, E * G k - G k * E = H (k + 1) := by
    intro k
    rw [op_comm_end]
    simp [E, G, H, F, Fin.sum_univ_succ, a3_compound_ef_table,
      Nat.add_comm, add_assoc]
  have hHF : ∀ m k, H (m + 1) * G k - G k * H (m + 1) =
      (-2 : ℂ) • G (m + 1 + k) := by
    intro m k
    calc
      _ = (ρ.op 12 (m + 1) * G k - G k * ρ.op 12 (m + 1)) +
          (ρ.op 13 (m + 1) * G k - G k * ρ.op 13 (m + 1)) := by
            dsimp [H]
            noncomm_ring
      _ = (-2 : ℂ) • G (m + 1 + k) := by
        rw [op_comm_end, op_comm_end]
        rw [← Finset.sum_add_distrib]
        simp_rw [← add_smul]
        simp [G, F, a3_compound_hf_table]
  have hE : E w = 0 := h.raising 1 (by decide) 1
  have hH : ∀ m, H (m + 1) w = 0 := by
    intro m
    change ρ.op 12 (m + 1) w + ρ.op 13 (m + 1) w = 0
    rw [show ρ.op 12 (m + 1) w = 0 by
      simpa [simpleH] using h.cartan_pos 0 (m + 1) (by omega)]
    rw [show ρ.op 13 (m + 1) w = 0 by
      simpa [simpleH] using h.cartan_pos 1 (m + 1) (by omega)]
    simp
  have hN : (G 0 ^ (a + b + 1)) w = 0 := by
    simpa [G, Module.End.pow_apply] using
      a3_compound_one_nilpotence ρ w a b c h
  have hk : ∀ r s, 1 ≤ r → a + b + 1 ≤ r + s →
      (PowerSeries.coeff s (VOA.DeligneAudit.Garland.Fs G ^ r)) w = 0 := by
    intro r s hr hrs
    exact VOA.DeligneAudit.Garland.garland hEF hHF hFF hE hH
      r hr hN s hrs
  exact a3_box_word_length_zero G hFF w (a + b) hk l hl

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_compound_word_length_zero
