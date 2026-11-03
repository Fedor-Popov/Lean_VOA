/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4LieTab
import VOA.DeligneAudit.G2LieSingQ

/-!
# `F₄` singular vector: integer data

`f4scZ`, `f4fZ`: the integer structure constants and form of `F4Table`/`f4Gm`.
`f4svTerms`: the terms of the weight-two singular vector `-X₈² + 4X₁₉X₃₀ + 4X₂₁X₃₄ +
4X₂₅X₄₂` — the highest-weight vector of `I₂ⁿˢ = V(2ω₄)` (324-dimensional) in the
positive-system convention of the generator (`gen_sc_sector.py f4`, `relRaw[0]`).
-/

namespace VOA.DeligneAudit.F4Lie

open VOA.AffineGeneral VOA.AffineGeneral.SCLie

def f4scZ (a b c : Fin 52) : ℤ := coef (entry f4T a b) c

def f4fZ (a b : Fin 52) : ℤ := formV f4Gm [((a : ℕ), 1)] [((b : ℕ), 1)]

def f4svTerms : List (ℤ × Fin 52 × Fin 52) := [(-1, 8, 8), (4, 19, 30), (4, 21, 34), (4, 25, 42)]

end VOA.DeligneAudit.F4Lie
