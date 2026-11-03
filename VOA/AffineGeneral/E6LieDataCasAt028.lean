/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6LieDataTab

/-! The Casimir certificate at one fixed basis vector. -/
set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6_cas_at_028 : casOK e6T 78 e6dl e6D 3 24 28 = true := by
  decide +kernel

end VOA.AffineGeneral.SCLie
