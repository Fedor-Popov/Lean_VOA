/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6LieDataCasAt000
import VOA.AffineGeneral.E6LieDataCasAt001
import VOA.AffineGeneral.E6LieDataCasAt002
import VOA.AffineGeneral.E6LieDataCasAt003
import VOA.AffineGeneral.E6LieDataCasAt004
import VOA.AffineGeneral.E6LieDataCasAt005
import VOA.AffineGeneral.E6LieDataCasAt006
import VOA.AffineGeneral.E6LieDataCasAt007
import VOA.AffineGeneral.E6LieDataCasAt008
import VOA.AffineGeneral.E6LieDataCasAt009
import VOA.AffineGeneral.E6LieDataCasAt010
import VOA.AffineGeneral.E6LieDataCasAt011
import VOA.AffineGeneral.E6LieDataCasAt012

set_option linter.style.longLine false

/-!
# E₆ Lie data: the Casimir at `0 ≤ x < 13`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6_cas0 : ∀ x : Fin 78, 0 ≤ x.val → x.val < 13 → casOK e6T 78 e6dl e6D 3 24 x = true := by
  suffices h : ∀ x : ℕ, 0 ≤ x → x < 13 → casOK e6T 78 e6dl e6D 3 24 x = true by
    exact fun x hxlo hxhi => h x.val hxlo hxhi
  intro x hxlo hxhi
  interval_cases x
  · exact e6_cas_at_000
  · exact e6_cas_at_001
  · exact e6_cas_at_002
  · exact e6_cas_at_003
  · exact e6_cas_at_004
  · exact e6_cas_at_005
  · exact e6_cas_at_006
  · exact e6_cas_at_007
  · exact e6_cas_at_008
  · exact e6_cas_at_009
  · exact e6_cas_at_010
  · exact e6_cas_at_011
  · exact e6_cas_at_012

end VOA.AffineGeneral.SCLie

#print axioms VOA.AffineGeneral.SCLie.e6_cas0
