/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6LieDataTab

/-!
# E₆ Lie data: `κ`-skewness of the Chevalley generators [11, 10, 9, 8, 7, 6]
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6_skewOK2_11 : skewOK2 e6T 78 e6Gc 11 = true := by decide +kernel

theorem e6_skewOK2_10 : skewOK2 e6T 78 e6Gc 10 = true := by decide +kernel

theorem e6_skewOK2_9 : skewOK2 e6T 78 e6Gc 9 = true := by decide +kernel

theorem e6_skewOK2_8 : skewOK2 e6T 78 e6Gc 8 = true := by decide +kernel

theorem e6_skewOK2_7 : skewOK2 e6T 78 e6Gc 7 = true := by decide +kernel

theorem e6_skewOK2_6 : skewOK2 e6T 78 e6Gc 6 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
