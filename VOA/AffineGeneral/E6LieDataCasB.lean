/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6LieDataCasAt013
import VOA.AffineGeneral.E6LieDataCasAt014
import VOA.AffineGeneral.E6LieDataCasAt015
import VOA.AffineGeneral.E6LieDataCasAt016
import VOA.AffineGeneral.E6LieDataCasAt017
import VOA.AffineGeneral.E6LieDataCasAt018
import VOA.AffineGeneral.E6LieDataCasAt019
import VOA.AffineGeneral.E6LieDataCasAt020
import VOA.AffineGeneral.E6LieDataCasAt021
import VOA.AffineGeneral.E6LieDataCasAt022
import VOA.AffineGeneral.E6LieDataCasAt023
import VOA.AffineGeneral.E6LieDataCasAt024
import VOA.AffineGeneral.E6LieDataCasAt025

set_option linter.style.longLine false

/-!
# E₆ Lie data: the Casimir at `13 ≤ x < 26`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6_cas1 : ∀ x : Fin 78, 13 ≤ x.val → x.val < 26 → casOK e6T 78 e6dl e6D 3 24 x = true := by
  suffices h : ∀ x : ℕ, 13 ≤ x → x < 26 → casOK e6T 78 e6dl e6D 3 24 x = true by
    exact fun x hxlo hxhi => h x.val hxlo hxhi
  intro x hxlo hxhi
  interval_cases x
  · exact e6_cas_at_013
  · exact e6_cas_at_014
  · exact e6_cas_at_015
  · exact e6_cas_at_016
  · exact e6_cas_at_017
  · exact e6_cas_at_018
  · exact e6_cas_at_019
  · exact e6_cas_at_020
  · exact e6_cas_at_021
  · exact e6_cas_at_022
  · exact e6_cas_at_023
  · exact e6_cas_at_024
  · exact e6_cas_at_025

end VOA.AffineGeneral.SCLie

#print axioms VOA.AffineGeneral.SCLie.e6_cas1
