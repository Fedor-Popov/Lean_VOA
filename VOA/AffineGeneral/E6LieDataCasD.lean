/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6LieDataCasAt039
import VOA.AffineGeneral.E6LieDataCasAt040
import VOA.AffineGeneral.E6LieDataCasAt041
import VOA.AffineGeneral.E6LieDataCasAt042
import VOA.AffineGeneral.E6LieDataCasAt043
import VOA.AffineGeneral.E6LieDataCasAt044
import VOA.AffineGeneral.E6LieDataCasAt045
import VOA.AffineGeneral.E6LieDataCasAt046
import VOA.AffineGeneral.E6LieDataCasAt047
import VOA.AffineGeneral.E6LieDataCasAt048
import VOA.AffineGeneral.E6LieDataCasAt049
import VOA.AffineGeneral.E6LieDataCasAt050
import VOA.AffineGeneral.E6LieDataCasAt051

set_option linter.style.longLine false

/-!
# E₆ Lie data: the Casimir at `39 ≤ x < 52`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6_cas3 : ∀ x : Fin 78, 39 ≤ x.val → x.val < 52 → casOK e6T 78 e6dl e6D 3 24 x = true := by
  suffices h : ∀ x : ℕ, 39 ≤ x → x < 52 → casOK e6T 78 e6dl e6D 3 24 x = true by
    exact fun x hxlo hxhi => h x.val hxlo hxhi
  intro x hxlo hxhi
  interval_cases x
  · exact e6_cas_at_039
  · exact e6_cas_at_040
  · exact e6_cas_at_041
  · exact e6_cas_at_042
  · exact e6_cas_at_043
  · exact e6_cas_at_044
  · exact e6_cas_at_045
  · exact e6_cas_at_046
  · exact e6_cas_at_047
  · exact e6_cas_at_048
  · exact e6_cas_at_049
  · exact e6_cas_at_050
  · exact e6_cas_at_051

end VOA.AffineGeneral.SCLie

#print axioms VOA.AffineGeneral.SCLie.e6_cas3
