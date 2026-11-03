/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6LieDataCasAt065
import VOA.AffineGeneral.E6LieDataCasAt066
import VOA.AffineGeneral.E6LieDataCasAt067
import VOA.AffineGeneral.E6LieDataCasAt068
import VOA.AffineGeneral.E6LieDataCasAt069
import VOA.AffineGeneral.E6LieDataCasAt070
import VOA.AffineGeneral.E6LieDataCasAt071
import VOA.AffineGeneral.E6LieDataCasAt072
import VOA.AffineGeneral.E6LieDataCasAt073
import VOA.AffineGeneral.E6LieDataCasAt074
import VOA.AffineGeneral.E6LieDataCasAt075
import VOA.AffineGeneral.E6LieDataCasAt076
import VOA.AffineGeneral.E6LieDataCasAt077

set_option linter.style.longLine false

/-!
# E₆ Lie data: the Casimir at `65 ≤ x < 78`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6_cas5 : ∀ x : Fin 78, 65 ≤ x.val → x.val < 78 → casOK e6T 78 e6dl e6D 3 24 x = true := by
  suffices h : ∀ x : ℕ, 65 ≤ x → x < 78 → casOK e6T 78 e6dl e6D 3 24 x = true by
    exact fun x hxlo hxhi => h x.val hxlo hxhi
  intro x hxlo hxhi
  interval_cases x
  · exact e6_cas_at_065
  · exact e6_cas_at_066
  · exact e6_cas_at_067
  · exact e6_cas_at_068
  · exact e6_cas_at_069
  · exact e6_cas_at_070
  · exact e6_cas_at_071
  · exact e6_cas_at_072
  · exact e6_cas_at_073
  · exact e6_cas_at_074
  · exact e6_cas_at_075
  · exact e6_cas_at_076
  · exact e6_cas_at_077

end VOA.AffineGeneral.SCLie

#print axioms VOA.AffineGeneral.SCLie.e6_cas5
