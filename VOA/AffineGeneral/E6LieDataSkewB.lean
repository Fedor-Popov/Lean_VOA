/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6LieDataTab

/-!
# E₆ Lie data: `κ`-skewness of the Chevalley generators [47, 46, 45, 44, 43, 42]
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6_skewOK2_47 : skewOK2 e6T 78 e6Gc 47 = true := by decide +kernel

theorem e6_skewOK2_46 : skewOK2 e6T 78 e6Gc 46 = true := by decide +kernel

theorem e6_skewOK2_45 : skewOK2 e6T 78 e6Gc 45 = true := by decide +kernel

theorem e6_skewOK2_44 : skewOK2 e6T 78 e6Gc 44 = true := by decide +kernel

theorem e6_skewOK2_43 : skewOK2 e6T 78 e6Gc 43 = true := by decide +kernel

theorem e6_skewOK2_42 : skewOK2 e6T 78 e6Gc 42 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
