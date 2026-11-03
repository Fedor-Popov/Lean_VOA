/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6LieDataPairAssembly
import VOA.AffineGeneral.E6LieDataPairRow052
import VOA.AffineGeneral.E6LieDataPairRow053
import VOA.AffineGeneral.E6LieDataPairRow054
import VOA.AffineGeneral.E6LieDataPairRow055
import VOA.AffineGeneral.E6LieDataPairRow056
import VOA.AffineGeneral.E6LieDataPairRow057
import VOA.AffineGeneral.E6LieDataPairRow058
import VOA.AffineGeneral.E6LieDataPairRow059
import VOA.AffineGeneral.E6LieDataPairRow060
import VOA.AffineGeneral.E6LieDataPairRow061
import VOA.AffineGeneral.E6LieDataPairRow062
import VOA.AffineGeneral.E6LieDataPairRow063
import VOA.AffineGeneral.E6LieDataPairRow064
import VOA.AffineGeneral.E6LieDataPairRow065
import VOA.AffineGeneral.E6LieDataPairRow066
import VOA.AffineGeneral.E6LieDataPairRow067
import VOA.AffineGeneral.E6LieDataPairRow068
import VOA.AffineGeneral.E6LieDataPairRow069
import VOA.AffineGeneral.E6LieDataPairRow070
import VOA.AffineGeneral.E6LieDataPairRow071
import VOA.AffineGeneral.E6LieDataPairRow072
import VOA.AffineGeneral.E6LieDataPairRow073
import VOA.AffineGeneral.E6LieDataPairRow074
import VOA.AffineGeneral.E6LieDataPairRow075
import VOA.AffineGeneral.E6LieDataPairRow076
import VOA.AffineGeneral.E6LieDataPairRow077

set_option linter.style.longLine false

/-!
# E₆ Lie data: dual pairing, `52 ≤ j < 78`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6_pair2 : pairChunk 78 e6Gm e6dl e6D 52 78 = true := by
  apply e6_pairChunk_of_rows
  intro j hlo hhi
  interval_cases j
  · exact e6_pair_row_052
  · exact e6_pair_row_053
  · exact e6_pair_row_054
  · exact e6_pair_row_055
  · exact e6_pair_row_056
  · exact e6_pair_row_057
  · exact e6_pair_row_058
  · exact e6_pair_row_059
  · exact e6_pair_row_060
  · exact e6_pair_row_061
  · exact e6_pair_row_062
  · exact e6_pair_row_063
  · exact e6_pair_row_064
  · exact e6_pair_row_065
  · exact e6_pair_row_066
  · exact e6_pair_row_067
  · exact e6_pair_row_068
  · exact e6_pair_row_069
  · exact e6_pair_row_070
  · exact e6_pair_row_071
  · exact e6_pair_row_072
  · exact e6_pair_row_073
  · exact e6_pair_row_074
  · exact e6_pair_row_075
  · exact e6_pair_row_076
  · exact e6_pair_row_077

end VOA.AffineGeneral.SCLie

#print axioms VOA.AffineGeneral.SCLie.e6_pair2
