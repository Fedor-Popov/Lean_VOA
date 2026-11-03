/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6LieDataCasAt026
import VOA.AffineGeneral.E6LieDataCasAt027
import VOA.AffineGeneral.E6LieDataCasAt028
import VOA.AffineGeneral.E6LieDataCasAt029
import VOA.AffineGeneral.E6LieDataCasAt030
import VOA.AffineGeneral.E6LieDataCasAt031
import VOA.AffineGeneral.E6LieDataCasAt032
import VOA.AffineGeneral.E6LieDataCasAt033
import VOA.AffineGeneral.E6LieDataCasAt034
import VOA.AffineGeneral.E6LieDataCasAt035
import VOA.AffineGeneral.E6LieDataCasAt036
import VOA.AffineGeneral.E6LieDataCasAt037
import VOA.AffineGeneral.E6LieDataCasAt038

set_option linter.style.longLine false

/-!
# E₆ Lie data: the Casimir at `26 ≤ x < 39`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6_cas2 : ∀ x : Fin 78, 26 ≤ x.val → x.val < 39 → casOK e6T 78 e6dl e6D 3 24 x = true := by
  suffices h : ∀ x : ℕ, 26 ≤ x → x < 39 → casOK e6T 78 e6dl e6D 3 24 x = true by
    exact fun x hxlo hxhi => h x.val hxlo hxhi
  intro x hxlo hxhi
  interval_cases x
  · exact e6_cas_at_026
  · exact e6_cas_at_027
  · exact e6_cas_at_028
  · exact e6_cas_at_029
  · exact e6_cas_at_030
  · exact e6_cas_at_031
  · exact e6_cas_at_032
  · exact e6_cas_at_033
  · exact e6_cas_at_034
  · exact e6_cas_at_035
  · exact e6_cas_at_036
  · exact e6_cas_at_037
  · exact e6_cas_at_038

end VOA.AffineGeneral.SCLie

#print axioms VOA.AffineGeneral.SCLie.e6_cas2
