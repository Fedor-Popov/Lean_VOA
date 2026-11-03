/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6LieDataTab

/-! A fixed-column dual-pairing certificate. -/
set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6_pair_row_027 :
    (decide (e6D 27 ≠ 0) && inRange 78 (e6dl 27) &&
      (List.range 78).all (fun i => formV e6Gm [(i, 1)] (e6dl 27) ==
        if i = 27 then e6D 27 else 0)) = true := by
  decide +kernel

end VOA.AffineGeneral.SCLie
