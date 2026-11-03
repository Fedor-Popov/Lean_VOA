/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6LieDataCasAt052
import VOA.AffineGeneral.E6LieDataCasAt053
import VOA.AffineGeneral.E6LieDataCasAt054
import VOA.AffineGeneral.E6LieDataCasAt055
import VOA.AffineGeneral.E6LieDataCasAt056
import VOA.AffineGeneral.E6LieDataCasAt057
import VOA.AffineGeneral.E6LieDataCasAt058
import VOA.AffineGeneral.E6LieDataCasAt059
import VOA.AffineGeneral.E6LieDataCasAt060
import VOA.AffineGeneral.E6LieDataCasAt061
import VOA.AffineGeneral.E6LieDataCasAt062
import VOA.AffineGeneral.E6LieDataCasAt063
import VOA.AffineGeneral.E6LieDataCasAt064

set_option linter.style.longLine false

/-!
# E₆ Lie data: the Casimir at `52 ≤ x < 65`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6_cas4 : ∀ x : Fin 78, 52 ≤ x.val → x.val < 65 → casOK e6T 78 e6dl e6D 3 24 x = true := by
  suffices h : ∀ x : ℕ, 52 ≤ x → x < 65 → casOK e6T 78 e6dl e6D 3 24 x = true by
    exact fun x hxlo hxhi => h x.val hxlo hxhi
  intro x hxlo hxhi
  interval_cases x
  · exact e6_cas_at_052
  · exact e6_cas_at_053
  · exact e6_cas_at_054
  · exact e6_cas_at_055
  · exact e6_cas_at_056
  · exact e6_cas_at_057
  · exact e6_cas_at_058
  · exact e6_cas_at_059
  · exact e6_cas_at_060
  · exact e6_cas_at_061
  · exact e6_cas_at_062
  · exact e6_cas_at_063
  · exact e6_cas_at_064

end VOA.AffineGeneral.SCLie

#print axioms VOA.AffineGeneral.SCLie.e6_cas4
