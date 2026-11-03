/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6LieDataTab

/-! A fixed-column dual-pairing certificate. -/
set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6_pair_row_076 :
    (decide (e6D 76 ≠ 0) && inRange 78 (e6dl 76) &&
      (List.range 78).all (fun i => formV e6Gm [(i, 1)] (e6dl 76) ==
        if i = 76 then e6D 76 else 0)) = true := by
  decide +kernel

end VOA.AffineGeneral.SCLie
