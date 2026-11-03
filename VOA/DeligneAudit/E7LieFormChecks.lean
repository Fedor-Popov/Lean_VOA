/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieForm

/-!
# Kernel checks for the `E₇` cert form (chunked)
-/

namespace VOA.DeligneAudit.E7Lie

theorem simple_ok : ∀ i, simpleOK i = true := by decide +kernel

theorem root_ok : ∀ a : Fin 133, 7 ≤ a.val → rootOK a = true := by decide +kernel

theorem formPair_ok0 : ∀ a : Fin 133, 0 ≤ a.val → a.val < 19 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok0 : ∀ a : Fin 133, 0 ≤ a.val → a.val < 19 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok1 : ∀ a : Fin 133, 19 ≤ a.val → a.val < 38 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok1 : ∀ a : Fin 133, 19 ≤ a.val → a.val < 38 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok2 : ∀ a : Fin 133, 38 ≤ a.val → a.val < 57 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok2 : ∀ a : Fin 133, 38 ≤ a.val → a.val < 57 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok3 : ∀ a : Fin 133, 57 ≤ a.val → a.val < 76 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok3 : ∀ a : Fin 133, 57 ≤ a.val → a.val < 76 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok4 : ∀ a : Fin 133, 76 ≤ a.val → a.val < 95 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok4 : ∀ a : Fin 133, 76 ≤ a.val → a.val < 95 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok5 : ∀ a : Fin 133, 95 ≤ a.val → a.val < 114 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok5 : ∀ a : Fin 133, 95 ≤ a.val → a.val < 114 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok6 : ∀ a : Fin 133, 114 ≤ a.val → a.val < 133 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok6 : ∀ a : Fin 133, 114 ≤ a.val → a.val < 133 → pairRowOK a = true := by
  decide +kernel

theorem formPair_all (a c : Fin 133) : formPairOK a c = true := by
  have ha := a.isLt
  by_cases h0 : a.val < 19; · exact formPair_ok0 a (by omega) h0 c
  by_cases h1 : a.val < 38; · exact formPair_ok1 a (by omega) h1 c
  by_cases h2 : a.val < 57; · exact formPair_ok2 a (by omega) h2 c
  by_cases h3 : a.val < 76; · exact formPair_ok3 a (by omega) h3 c
  by_cases h4 : a.val < 95; · exact formPair_ok4 a (by omega) h4 c
  by_cases h5 : a.val < 114; · exact formPair_ok5 a (by omega) h5 c
  exact formPair_ok6 a (by omega) (by omega) c

theorem pairRow_all (a : Fin 133) : pairRowOK a = true := by
  have ha := a.isLt
  by_cases h0 : a.val < 19; · exact pairRow_ok0 a (by omega) h0
  by_cases h1 : a.val < 38; · exact pairRow_ok1 a (by omega) h1
  by_cases h2 : a.val < 57; · exact pairRow_ok2 a (by omega) h2
  by_cases h3 : a.val < 76; · exact pairRow_ok3 a (by omega) h3
  by_cases h4 : a.val < 95; · exact pairRow_ok4 a (by omega) h4
  by_cases h5 : a.val < 114; · exact pairRow_ok5 a (by omega) h5
  exact pairRow_ok6 a (by omega) (by omega)

end VOA.DeligneAudit.E7Lie
