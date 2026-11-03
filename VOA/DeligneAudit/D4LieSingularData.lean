/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LieTable

/-! Small integer data for the three D4 singular-vector checks. -/
namespace VOA.DeligneAudit.D4Lie

/-- First factors of the three highest-weight vectors (`singular_cert/cert_D4.json`). -/
def ta : Fin 3 → Fin 3 → Fin 28 := ![![4, 8, 11], ![5, 9, 11], ![7, 10, 12]]
/-- Second factors. -/
def tb : Fin 3 → Fin 3 → Fin 28 := ![![15, 14, 12], ![15, 14, 13], ![15, 14, 13]]
/-- Coefficients. -/
def cz : Fin 3 → Fin 3 → ℤ := ![![-1, 1, -1], ![-1, 1, -1], ![1, 1, -1]]

/-- The integer `J(1)` coefficients. -/
def oneZ (r : Fin 3) (c e : Fin 28) : ℤ :=
  ∑ i, cz r i * (-2 * Gz c (tb r i) * (if ta r i = e then 1 else 0) +
    -2 * Gz c (ta r i) * (if tb r i = e then 1 else 0) +
    ((sL c (ta r i)).map fun t => t.2 * sZ t.1 (tb r i) e).sum)

/-- The integer `J(2)` coefficients. -/
def twoZ (r : Fin 3) (c : Fin 28) : ℤ :=
  ∑ i, cz r i * ((sL c (ta r i)).map fun t => t.2 * (-2 * Gz t.1 (tb r i))).sum


end VOA.DeligneAudit.D4Lie
