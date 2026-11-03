import VOA.DeligneAudit.D4LeviOrder
import VOA.DeligneAudit.D4FusionContactTruncation

/-! The source fusion relations give mode cutoffs for every negative root. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4FusionContact

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- The exceptional highest-root current starts at mode `2m`; the other
negative roots start at mode `m`. -/
def rootModeBound (m : ℕ) (c : Fin 28) : ℕ :=
  if c = 27 then 2 * m else m

theorem source_root_mode_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (c : Fin 28) (hc : 16 ≤ c.val) (r : ℕ)
    (hr : rootModeBound m c ≤ r) : ρ.op c r w = 0 := by
  have hs : Sat D4sector.f ρ w (ravSpec D4sector m (2 * m)) := by
    simpa [ravFam] using h
  obtain ⟨i, rfl⟩ := negativeIndex_covers c hc
  have hf : ρ.op (negativeIndex i) (rootModeBound m (negativeIndex i)) w = 0 := by
    have hfusion : D4sector.fusion (negativeIndex i) :=
      negativeIndex_range i
    have hbase := rs_fusion hs hfusion
    simpa [rootModeBound, D4sector] using hbase
  obtain ⟨k, rfl⟩ : ∃ k, r = rootModeBound m (negativeIndex i) + k :=
    ⟨r - rootModeBound m (negativeIndex i), by omega⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hf
  have hc := ρ.comm (negativeCartan i) (negativeIndex i) k
    (rootModeBound m (negativeIndex i)) w
  have hcart : D4sector.cartan (negativeCartan i) :=
    negativeCartan_lt_four i
  rw [hf, map_zero, rs_cartan_pos hs hcart k hk, map_zero, sub_zero] at hc
  have hsum : (∑ z : Fin 28,
      D4sector.f (negativeCartan i) (negativeIndex i) z •
        ρ.op z (k + rootModeBound m (negativeIndex i)) w) =
      (negativeWeight i : ℂ) •
        ρ.op (negativeIndex i) (rootModeBound m (negativeIndex i) + k) w := by
    change (∑ z : Fin 28,
      contactF (negativeCartan i) (negativeIndex i) z •
        ρ.op z (k + rootModeBound m (negativeIndex i)) w) = _
    simp only [negative_cartan_table, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true,
      add_comm k (rootModeBound m (negativeIndex i))]
  have hc' := hc.trans hsum
  exact (smul_eq_zero.mp hc'.symm).resolve_left (negativeWeight_ne_zero i)

theorem source_radical_mode_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (j : Fin 6) (r : ℕ)
    (hr : rootModeBound m (radicalColour j) ≤ r) :
    ρ.op (radicalColour j) r w = 0 :=
  source_root_mode_zero ρ w m h (radicalColour j)
    (by fin_cases j <;> decide) r hr

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.source_root_mode_zero
#print axioms VOA.DeligneAudit.D4Levi.source_radical_mode_zero
