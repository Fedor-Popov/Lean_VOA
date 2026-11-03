/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# Kernel checks on the `E₈` weights (chunked, light imports)
-/

namespace VOA.DeligneAudit.E8Lie

theorem wt_inj_ok0 : ∀ a b : Fin 248, 0 ≤ a.val → a.val < 31 → 8 ≤ a.val → 8 ≤ b.val →
    wt a = wt b → a = b := by
  decide +kernel

theorem wt_inj_ok1 : ∀ a b : Fin 248, 31 ≤ a.val → a.val < 62 → 8 ≤ a.val → 8 ≤ b.val →
    wt a = wt b → a = b := by
  decide +kernel

theorem wt_inj_ok2 : ∀ a b : Fin 248, 62 ≤ a.val → a.val < 93 → 8 ≤ a.val → 8 ≤ b.val →
    wt a = wt b → a = b := by
  decide +kernel

theorem wt_inj_ok3 : ∀ a b : Fin 248, 93 ≤ a.val → a.val < 124 → 8 ≤ a.val → 8 ≤ b.val →
    wt a = wt b → a = b := by
  decide +kernel

theorem wt_inj_ok4 : ∀ a b : Fin 248, 124 ≤ a.val → a.val < 155 → 8 ≤ a.val → 8 ≤ b.val →
    wt a = wt b → a = b := by
  decide +kernel

theorem wt_inj_ok5 : ∀ a b : Fin 248, 155 ≤ a.val → a.val < 186 → 8 ≤ a.val → 8 ≤ b.val →
    wt a = wt b → a = b := by
  decide +kernel

theorem wt_inj_ok6 : ∀ a b : Fin 248, 186 ≤ a.val → a.val < 217 → 8 ≤ a.val → 8 ≤ b.val →
    wt a = wt b → a = b := by
  decide +kernel

theorem wt_inj_ok7 : ∀ a b : Fin 248, 217 ≤ a.val → a.val < 248 → 8 ≤ a.val → 8 ≤ b.val →
    wt a = wt b → a = b := by
  decide +kernel

theorem wt_inj : ∀ a b : Fin 248, 8 ≤ a.val → 8 ≤ b.val → wt a = wt b → a = b := by
  intro a b
  have ha := a.isLt
  by_cases h0 : a.val < 31; · exact wt_inj_ok0 a b (by omega) h0
  by_cases h1 : a.val < 62; · exact wt_inj_ok1 a b (by omega) h1
  by_cases h2 : a.val < 93; · exact wt_inj_ok2 a b (by omega) h2
  by_cases h3 : a.val < 124; · exact wt_inj_ok3 a b (by omega) h3
  by_cases h4 : a.val < 155; · exact wt_inj_ok4 a b (by omega) h4
  by_cases h5 : a.val < 186; · exact wt_inj_ok5 a b (by omega) h5
  by_cases h6 : a.val < 217; · exact wt_inj_ok6 a b (by omega) h6
  exact wt_inj_ok7 a b (by omega) (by omega)

theorem card_rootIdx : (Finset.univ.filter fun a : Fin 248 => 8 ≤ a.val).card = 240 := by
  decide +kernel

end VOA.DeligneAudit.E8Lie
