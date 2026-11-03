/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6LieDataPairAssembly
import VOA.AffineGeneral.E6LieDataPairRow000
import VOA.AffineGeneral.E6LieDataPairRow001
import VOA.AffineGeneral.E6LieDataPairRow002
import VOA.AffineGeneral.E6LieDataPairRow003
import VOA.AffineGeneral.E6LieDataPairRow004
import VOA.AffineGeneral.E6LieDataPairRow005
import VOA.AffineGeneral.E6LieDataPairRow006
import VOA.AffineGeneral.E6LieDataPairRow007
import VOA.AffineGeneral.E6LieDataPairRow008
import VOA.AffineGeneral.E6LieDataPairRow009
import VOA.AffineGeneral.E6LieDataPairRow010
import VOA.AffineGeneral.E6LieDataPairRow011
import VOA.AffineGeneral.E6LieDataPairRow012
import VOA.AffineGeneral.E6LieDataPairRow013
import VOA.AffineGeneral.E6LieDataPairRow014
import VOA.AffineGeneral.E6LieDataPairRow015
import VOA.AffineGeneral.E6LieDataPairRow016
import VOA.AffineGeneral.E6LieDataPairRow017
import VOA.AffineGeneral.E6LieDataPairRow018
import VOA.AffineGeneral.E6LieDataPairRow019
import VOA.AffineGeneral.E6LieDataPairRow020
import VOA.AffineGeneral.E6LieDataPairRow021
import VOA.AffineGeneral.E6LieDataPairRow022
import VOA.AffineGeneral.E6LieDataPairRow023
import VOA.AffineGeneral.E6LieDataPairRow024
import VOA.AffineGeneral.E6LieDataPairRow025

set_option linter.style.longLine false

/-!
# E₆ Lie data: dual pairing, `0 ≤ j < 26`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6_pair0 : pairChunk 78 e6Gm e6dl e6D 0 26 = true := by
  apply e6_pairChunk_of_rows
  intro j hlo hhi
  interval_cases j
  · exact e6_pair_row_000
  · exact e6_pair_row_001
  · exact e6_pair_row_002
  · exact e6_pair_row_003
  · exact e6_pair_row_004
  · exact e6_pair_row_005
  · exact e6_pair_row_006
  · exact e6_pair_row_007
  · exact e6_pair_row_008
  · exact e6_pair_row_009
  · exact e6_pair_row_010
  · exact e6_pair_row_011
  · exact e6_pair_row_012
  · exact e6_pair_row_013
  · exact e6_pair_row_014
  · exact e6_pair_row_015
  · exact e6_pair_row_016
  · exact e6_pair_row_017
  · exact e6_pair_row_018
  · exact e6_pair_row_019
  · exact e6_pair_row_020
  · exact e6_pair_row_021
  · exact e6_pair_row_022
  · exact e6_pair_row_023
  · exact e6_pair_row_024
  · exact e6_pair_row_025

end VOA.AffineGeneral.SCLie

#print axioms VOA.AffineGeneral.SCLie.e6_pair0
