import VOA.DeligneAudit.D4LeviKSRzWordBridge

/-! Unconditional general Rz orbit generators in the target kernel. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rzTargetGenerator_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b k l s : ℕ) (α : Fin b ⊕ Fin a → ℕ)
    (β : Fin l → ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      pairFinalKey a b (k + l)
        (((Finset.univ.toList : List (Fin b ⊕ Fin a)).map α).sum +
          ((Finset.univ.toList : List (Fin l)).map β).sum + s)) :
    rzTargetGenerator a b k l s α β ∈
      (pairTargetQuotientEvaluation ρ w m i a b (k + l)
        (pairKernelPrefix_of_sat ρ w m i a b (k + l)
          (((Finset.univ.toList : List (Fin b ⊕ Fin a)).map α).sum +
            ((Finset.univ.toList : List (Fin l)).map β).sum + s)
          h hi hkey)).ker := by
  classical
  let xs := (Finset.univ.toList : List (Fin b ⊕ Fin a)).map α
  let zs := (Finset.univ.toList : List (Fin l)).map β
  have hx : xs.length = a + b := by
    simp [xs, Fintype.card_sum, Nat.add_comm]
  have hz : zs.length = l := by simp [zs]
  apply rzTargetGenerator_mem_ker_of_word_bridge ρ w m i a b k l s
    α β xs zs h hk hks hx hz hi hkey
  simpa only [xs, zs, List.map_map, Function.comp_def] using
    rzRawSourceGenerator_word_bridge ρ w a b k l s α β

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rzTargetGenerator_mem_ker
