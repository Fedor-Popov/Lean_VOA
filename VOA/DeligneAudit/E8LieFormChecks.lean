/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieForm

/-!
# Kernel checks for the `E₈` cert form (chunked)
-/

namespace VOA.DeligneAudit.E8Lie

theorem simple_ok : ∀ i, simpleOK i = true := by decide +kernel

theorem root_ok : ∀ a : Fin 248, 8 ≤ a.val → rootOK a = true := by decide +kernel

theorem formPair_ok0 : ∀ a : Fin 248, 0 ≤ a.val → a.val < 19 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok0 : ∀ a : Fin 248, 0 ≤ a.val → a.val < 19 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok1 : ∀ a : Fin 248, 19 ≤ a.val → a.val < 38 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok1 : ∀ a : Fin 248, 19 ≤ a.val → a.val < 38 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok2 : ∀ a : Fin 248, 38 ≤ a.val → a.val < 57 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok2 : ∀ a : Fin 248, 38 ≤ a.val → a.val < 57 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok3 : ∀ a : Fin 248, 57 ≤ a.val → a.val < 76 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok3 : ∀ a : Fin 248, 57 ≤ a.val → a.val < 76 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok4 : ∀ a : Fin 248, 76 ≤ a.val → a.val < 95 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok4 : ∀ a : Fin 248, 76 ≤ a.val → a.val < 95 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok5 : ∀ a : Fin 248, 95 ≤ a.val → a.val < 114 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok5 : ∀ a : Fin 248, 95 ≤ a.val → a.val < 114 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok6 : ∀ a : Fin 248, 114 ≤ a.val → a.val < 133 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok6 : ∀ a : Fin 248, 114 ≤ a.val → a.val < 133 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok7 : ∀ a : Fin 248, 133 ≤ a.val → a.val < 152 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok7 : ∀ a : Fin 248, 133 ≤ a.val → a.val < 152 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok8 : ∀ a : Fin 248, 152 ≤ a.val → a.val < 171 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok8 : ∀ a : Fin 248, 152 ≤ a.val → a.val < 171 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok9 : ∀ a : Fin 248, 171 ≤ a.val → a.val < 190 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok9 : ∀ a : Fin 248, 171 ≤ a.val → a.val < 190 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok10 : ∀ a : Fin 248, 190 ≤ a.val → a.val < 209 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok10 : ∀ a : Fin 248, 190 ≤ a.val → a.val < 209 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok11 : ∀ a : Fin 248, 209 ≤ a.val → a.val < 228 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok11 : ∀ a : Fin 248, 209 ≤ a.val → a.val < 228 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok12 : ∀ a : Fin 248, 228 ≤ a.val → a.val < 247 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok12 : ∀ a : Fin 248, 228 ≤ a.val → a.val < 247 → pairRowOK a = true := by
  decide +kernel

theorem formPair_ok13 : ∀ a : Fin 248, 247 ≤ a.val → a.val < 248 → ∀ c, formPairOK a c = true := by
  decide +kernel

theorem pairRow_ok13 : ∀ a : Fin 248, 247 ≤ a.val → a.val < 248 → pairRowOK a = true := by
  decide +kernel

theorem formPair_all (a c : Fin 248) : formPairOK a c = true := by
  have ha := a.isLt
  by_cases h0 : a.val < 19; · exact formPair_ok0 a (by omega) h0 c
  by_cases h1 : a.val < 38; · exact formPair_ok1 a (by omega) h1 c
  by_cases h2 : a.val < 57; · exact formPair_ok2 a (by omega) h2 c
  by_cases h3 : a.val < 76; · exact formPair_ok3 a (by omega) h3 c
  by_cases h4 : a.val < 95; · exact formPair_ok4 a (by omega) h4 c
  by_cases h5 : a.val < 114; · exact formPair_ok5 a (by omega) h5 c
  by_cases h6 : a.val < 133; · exact formPair_ok6 a (by omega) h6 c
  by_cases h7 : a.val < 152; · exact formPair_ok7 a (by omega) h7 c
  by_cases h8 : a.val < 171; · exact formPair_ok8 a (by omega) h8 c
  by_cases h9 : a.val < 190; · exact formPair_ok9 a (by omega) h9 c
  by_cases h10 : a.val < 209; · exact formPair_ok10 a (by omega) h10 c
  by_cases h11 : a.val < 228; · exact formPair_ok11 a (by omega) h11 c
  by_cases h12 : a.val < 247; · exact formPair_ok12 a (by omega) h12 c
  exact formPair_ok13 a (by omega) (by omega) c

theorem pairRow_all (a : Fin 248) : pairRowOK a = true := by
  have ha := a.isLt
  by_cases h0 : a.val < 19; · exact pairRow_ok0 a (by omega) h0
  by_cases h1 : a.val < 38; · exact pairRow_ok1 a (by omega) h1
  by_cases h2 : a.val < 57; · exact pairRow_ok2 a (by omega) h2
  by_cases h3 : a.val < 76; · exact pairRow_ok3 a (by omega) h3
  by_cases h4 : a.val < 95; · exact pairRow_ok4 a (by omega) h4
  by_cases h5 : a.val < 114; · exact pairRow_ok5 a (by omega) h5
  by_cases h6 : a.val < 133; · exact pairRow_ok6 a (by omega) h6
  by_cases h7 : a.val < 152; · exact pairRow_ok7 a (by omega) h7
  by_cases h8 : a.val < 171; · exact pairRow_ok8 a (by omega) h8
  by_cases h9 : a.val < 190; · exact pairRow_ok9 a (by omega) h9
  by_cases h10 : a.val < 209; · exact pairRow_ok10 a (by omega) h10
  by_cases h11 : a.val < 228; · exact pairRow_ok11 a (by omega) h11
  by_cases h12 : a.val < 247; · exact pairRow_ok12 a (by omega) h12
  exact pairRow_ok13 a (by omega) (by omega)

end VOA.DeligneAudit.E8Lie
