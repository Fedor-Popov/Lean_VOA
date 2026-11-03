/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6LieDataPairAssembly
import VOA.AffineGeneral.E6LieDataPairRow026
import VOA.AffineGeneral.E6LieDataPairRow027
import VOA.AffineGeneral.E6LieDataPairRow028
import VOA.AffineGeneral.E6LieDataPairRow029
import VOA.AffineGeneral.E6LieDataPairRow030
import VOA.AffineGeneral.E6LieDataPairRow031
import VOA.AffineGeneral.E6LieDataPairRow032
import VOA.AffineGeneral.E6LieDataPairRow033
import VOA.AffineGeneral.E6LieDataPairRow034
import VOA.AffineGeneral.E6LieDataPairRow035
import VOA.AffineGeneral.E6LieDataPairRow036
import VOA.AffineGeneral.E6LieDataPairRow037
import VOA.AffineGeneral.E6LieDataPairRow038
import VOA.AffineGeneral.E6LieDataPairRow039
import VOA.AffineGeneral.E6LieDataPairRow040
import VOA.AffineGeneral.E6LieDataPairRow041
import VOA.AffineGeneral.E6LieDataPairRow042
import VOA.AffineGeneral.E6LieDataPairRow043
import VOA.AffineGeneral.E6LieDataPairRow044
import VOA.AffineGeneral.E6LieDataPairRow045
import VOA.AffineGeneral.E6LieDataPairRow046
import VOA.AffineGeneral.E6LieDataPairRow047
import VOA.AffineGeneral.E6LieDataPairRow048
import VOA.AffineGeneral.E6LieDataPairRow049
import VOA.AffineGeneral.E6LieDataPairRow050
import VOA.AffineGeneral.E6LieDataPairRow051

set_option linter.style.longLine false

/-!
# E₆ Lie data: dual pairing, `26 ≤ j < 52`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6_pair1 : pairChunk 78 e6Gm e6dl e6D 26 52 = true := by
  apply e6_pairChunk_of_rows
  intro j hlo hhi
  interval_cases j
  · exact e6_pair_row_026
  · exact e6_pair_row_027
  · exact e6_pair_row_028
  · exact e6_pair_row_029
  · exact e6_pair_row_030
  · exact e6_pair_row_031
  · exact e6_pair_row_032
  · exact e6_pair_row_033
  · exact e6_pair_row_034
  · exact e6_pair_row_035
  · exact e6_pair_row_036
  · exact e6_pair_row_037
  · exact e6_pair_row_038
  · exact e6_pair_row_039
  · exact e6_pair_row_040
  · exact e6_pair_row_041
  · exact e6_pair_row_042
  · exact e6_pair_row_043
  · exact e6_pair_row_044
  · exact e6_pair_row_045
  · exact e6_pair_row_046
  · exact e6_pair_row_047
  · exact e6_pair_row_048
  · exact e6_pair_row_049
  · exact e6_pair_row_050
  · exact e6_pair_row_051

end VOA.AffineGeneral.SCLie

#print axioms VOA.AffineGeneral.SCLie.e6_pair1
