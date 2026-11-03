/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCarrierDemazure
import VOA.DeligneAudit.A2Carrier

/-!
# The D₄ type data for the carrier chain

Basis: the 28 vectors of `Notes/deligne/audit_2026_10_25/casimir_cert/cert_D4.json` (indices `0..3`
Cartan `H_i`, then root vectors; the same basis as `singular_cert/cert_D4.json`).

* `relTable`: 105 weight vectors spanning `I₂ⁿˢ = 35_v ⊕ 35_s ⊕ 35_c ⊂ Sym² so₈`.  They were generated
  (exact rational arithmetic, by a script not included in this release) by applying the lowering operators
  `F_i` to the three highest-weight symbols of the singular vectors of `singular_cert/cert_D4.json`
  (equal to `hw` of `casimir_cert/cert_D4.json`), keeping an independent subset; the span was
  checked to be `g`-stable and of dimension 105.  Lean does not re-check this provenance.
* `casEntries`: the Casimir `Q` of `casimir_cert/cert_D4.json`.
* **Lean-checked**: U3, `X_a · Q ∈ (I₂ⁿˢ)` for all 28 currents (`u3_a`), by explicit certificates
  `X_a Q = Σ ℓ · x_c · r_b` (found by exact elimination, verified by `ring`).
-/

namespace VOA.DeligneAudit.DeligneCarrier.D4

open MvPolynomial VOA.QuadraticJetCoefficientPairing

set_option linter.style.longLine false

noncomputable section

/-- Relation 0. -/
def P0 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 15) + (1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 14) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 12)

/-- Relation 1. -/
def P1 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 15) + (1 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 14) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 13)

/-- Relation 2. -/
def P2 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 15) + (1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 14) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 13)

/-- Relation 3. -/
def P3 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 15) + (1 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 14) + (1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 13) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 12) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 11)

/-- Relation 4. -/
def P4 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 15) + (1 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 14) + (1 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 12) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 13) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 11)

/-- Relation 5. -/
def P5 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 15) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 14) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 11) + (1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 13) + (1 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 12)

/-- Relation 6. -/
def P6 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 18) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 14) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 14) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 13) + (1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 12) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 11)

/-- Relation 7. -/
def P7 : MvPolynomial (Fin 28) ℂ :=
  (2 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 16) + (2 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 13) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 10)

/-- Relation 8. -/
def P8 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 18) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 14) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 14) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 12) + (1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 13) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 11)

/-- Relation 9. -/
def P9 : MvPolynomial (Fin 28) ℂ :=
  (2 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 17) + (2 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 12) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 10)

/-- Relation 10. -/
def P10 : MvPolynomial (Fin 28) ℂ :=
  (-2 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 19) + (2 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 11) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 9)

/-- Relation 11. -/
def P11 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 18) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 14) + (1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 14) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 11) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 13) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 12)

/-- Relation 12. -/
def P12 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 22) + (1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 11) + (1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 19) + (1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 11) + (1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 9) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 8) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 11)

/-- Relation 13. -/
def P13 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 21) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 12) + (1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 17) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 12) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 10) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 12) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 8)

/-- Relation 14. -/
def P14 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 20) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 16) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 13) + (1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 10) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 9)

/-- Relation 15. -/
def P15 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 22) + (1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 11) + (1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 19) + (1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 11) + (1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 8) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 9) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 11)

/-- Relation 16. -/
def P16 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 21) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 17) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 12) + (1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 10) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 8)

/-- Relation 17. -/
def P17 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 20) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 13) + (1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 16) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 13) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 10) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 13) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 9)

/-- Relation 18. -/
def P18 : MvPolynomial (Fin 28) ℂ :=
  (2 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 19) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 22) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 11) + (2 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 9) + (2 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 8)

/-- Relation 19. -/
def P19 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 21) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 12) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 17) + (1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 12) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 8) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 10) + (1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 12)

/-- Relation 20. -/
def P20 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 20) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 13) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 16) + (1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 13) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 9) + (1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 13) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 10)

/-- Relation 21. -/
def P21 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 25) + (1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 8) + (1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 19) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 17) + (1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 8) + (1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 6) + (1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 8) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 8)

/-- Relation 22. -/
def P22 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 24) + (1 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 16) + (1 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 19) + (1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 9) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 6) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 9)

/-- Relation 23. -/
def P23 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 23) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 16) + (1 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 17) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 10) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 10) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 7)

/-- Relation 24. -/
def P24 : MvPolynomial (Fin 28) ℂ :=
  (2 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 20) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 18) + (2 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 7)

/-- Relation 25. -/
def P25 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 25) + (1 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 17) + (1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 19) + (1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 8) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 6) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 8)

/-- Relation 26. -/
def P26 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 24) + (1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 9) + (1 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 19) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 16) + (1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 9) + (1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 6) + (1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 9) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 9)

/-- Relation 27. -/
def P27 : MvPolynomial (Fin 28) ℂ :=
  (2 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 21) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 18) + (2 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 7)

/-- Relation 28. -/
def P28 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 23) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 17) + (1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 16) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 10) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 10) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 7)

/-- Relation 29. -/
def P29 : MvPolynomial (Fin 28) ℂ :=
  (4 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 22) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 18) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 5)

/-- Relation 30. -/
def P30 : MvPolynomial (Fin 28) ℂ :=
  (2 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 19) + (2 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 25) + (2 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 17) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 8) + (2 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 6) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 8)

/-- Relation 31. -/
def P31 : MvPolynomial (Fin 28) ℂ :=
  (2 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 19) + (2 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 24) + (2 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 16) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 9) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 9) + (2 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 6)

/-- Relation 32. -/
def P32 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 23) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 10) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 17) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 16) + (1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 10) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 7) + (1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 10) + (1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 10)

/-- Relation 33. -/
def P33 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 25) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 18) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 4) + (1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 22) + (1 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 21) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 4) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 4) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 4)

/-- Relation 34. -/
def P34 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 26) + (1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 16) + (1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 19) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 17) + (1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 6) + (1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 6) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 6)

/-- Relation 35. -/
def P35 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 24) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 20) + (1 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 22) + (1 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 18) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 5)

/-- Relation 36. -/
def P36 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 23) + (1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 20) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 21) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 18) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 7)

/-- Relation 37. -/
def P37 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 25) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 21) + (1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 22) + (1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 18) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 4)

/-- Relation 38. -/
def P38 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 26) + (1 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 17) + (1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 19) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 16) + (1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 6) + (1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 6) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 6)

/-- Relation 39. -/
def P39 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 24) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 18) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 5) + (1 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 22) + (1 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 20) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 5) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 5) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 5)

/-- Relation 40. -/
def P40 : MvPolynomial (Fin 28) ℂ :=
  (2 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 21) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 23) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 18) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 20) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 7)

/-- Relation 41. -/
def P41 : MvPolynomial (Fin 28) ℂ :=
  (4 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 22) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 25) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 18) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 21) + (4 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 4)

/-- Relation 42. -/
def P42 : MvPolynomial (Fin 28) ℂ :=
  (4 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 22) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 24) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 18) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 20) + (4 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 5)

/-- Relation 43. -/
def P43 : MvPolynomial (Fin 28) ℂ :=
  (2 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 19) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 26) + (2 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 17) + (2 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 16) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 6) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 6) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 6)

/-- Relation 44. -/
def P44 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 23) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 18) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 7) + (1 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 21) + (1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 20) + (2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 7) + (1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 7) + (1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 7)

/-- Relation 45. -/
def P45 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 25) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 26) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 18) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 20) + (1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 3) + (1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 22) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 24) + (1 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 21) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 23) + (2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 3) + (1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 3) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 3)

/-- Relation 46. -/
def P46 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 26) + (1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 27) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 16) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 20) + (1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 19) + (1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 22) + (1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 17) + (1 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 21) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 1) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 2) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 1)

/-- Relation 47. -/
def P47 : MvPolynomial (Fin 28) ℂ :=
  (-2 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 24) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 22) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 19)

/-- Relation 48. -/
def P48 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 24) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 26) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 20) + (1 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 23) + (1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 22) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 25) + (1 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 18) + (1 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 21) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 2)

/-- Relation 49. -/
def P49 : MvPolynomial (Fin 28) ℂ :=
  (-2 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 23) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 21) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 17)

/-- Relation 50. -/
def P50 : MvPolynomial (Fin 28) ℂ :=
  (-2 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 25) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 22) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 19)

/-- Relation 51. -/
def P51 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 25) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 26) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 21) + (1 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 23) + (1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 22) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 24) + (1 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 18) + (1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 20) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 3)

/-- Relation 52. -/
def P52 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 26) + (1 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 27) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 17) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 21) + (1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 19) + (1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 22) + (1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 16) + (1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 20) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 1) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 3) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 1)

/-- Relation 53. -/
def P53 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 24) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 26) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 18) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 21) + (1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 2) + (1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 22) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 25) + (1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 20) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 23) + (2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 2) + (1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 3) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 2)

/-- Relation 54. -/
def P54 : MvPolynomial (Fin 28) ℂ :=
  (-4 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 23) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 20) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 16)

/-- Relation 55. -/
def P55 : MvPolynomial (Fin 28) ℂ :=
  (-8 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 25) + (-8 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 21) + (8 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 17)

/-- Relation 56. -/
def P56 : MvPolynomial (Fin 28) ℂ :=
  (4 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 22) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 24) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 25) + (4 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 26) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 18) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 20) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 21) + (4 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 23) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 3)

/-- Relation 57. -/
def P57 : MvPolynomial (Fin 28) ℂ :=
  (-8 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 24) + (-8 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 20) + (8 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 16)

/-- Relation 58. -/
def P58 : MvPolynomial (Fin 28) ℂ :=
  (2 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 19) + (2 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 22) + (2 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 26) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 27) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 17) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 21) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 16) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 20) + (2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 1) + (2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 3) + (2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 2)

/-- Relation 59. -/
def P59 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 23) + (1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 26) + (1 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 18) + (1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 22) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 0) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 21) + (1 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 25) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 20) + (1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 24) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 1) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 3) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 2)

/-- Relation 60. -/
def P60 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 27) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 18) + (1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 20) + (1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 22) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 21) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 18) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 18)

/-- Relation 61. -/
def P61 : MvPolynomial (Fin 28) ℂ :=
  (-2 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 26) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 20) + (2 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 16) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 24) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 23) + (4 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 16) + (2 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 16) + (2 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 16)

/-- Relation 62. -/
def P62 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 26) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 24) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 22) + (1 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 25) + (1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 19)

/-- Relation 63. -/
def P63 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 26) + (1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 23) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 25) + (1 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 21) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 17)

/-- Relation 64. -/
def P64 : MvPolynomial (Fin 28) ℂ :=
  (-2 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 25) + (2 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 26) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 22) + (2 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 24) + (2 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 19)

/-- Relation 65. -/
def P65 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 27) + (1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 21) + (1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 22) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 18) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 20) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 18) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 18)

/-- Relation 66. -/
def P66 : MvPolynomial (Fin 28) ℂ :=
  (-2 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 26) + (2 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 23) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 24) + (2 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 20) + (2 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 16)

/-- Relation 67. -/
def P67 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 26) + (1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 17) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 21) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 25) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 23) + (2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 17) + (1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 17) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 17)

/-- Relation 68. -/
def P68 : MvPolynomial (Fin 28) ℂ :=
  (-8 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 25) + (8 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 26) + (-8 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 21) + (8 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 23) + (-8 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 17)

/-- Relation 69. -/
def P69 : MvPolynomial (Fin 28) ℂ :=
  (4 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 22) + (4 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 27) + (4 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 18) + (4 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 20) + (4 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 21) + (4 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 18) + (4 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 18)

/-- Relation 70. -/
def P70 : MvPolynomial (Fin 28) ℂ :=
  (-8 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 24) + (8 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 26) + (-8 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 20) + (8 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 23) + (-8 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 16)

/-- Relation 71. -/
def P71 : MvPolynomial (Fin 28) ℂ :=
  (-2 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 19) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 22) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 26) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 25) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 24) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 19) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 19) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 19)

/-- Relation 72. -/
def P72 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 27) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 18 * X 19) + (1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 22) + (1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 24) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 25) + (1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 22)

/-- Relation 73. -/
def P73 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 27) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 17 * X 18) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 21) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 23) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 25) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 21)

/-- Relation 74. -/
def P74 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 27) + (1 : MvPolynomial (Fin 28) ℂ) * (X 16 * X 18) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 20) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 20) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 24) + (1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 23) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 20) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 20)

/-- Relation 75. -/
def P75 : MvPolynomial (Fin 28) ℂ :=
  (2 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 26) + (2 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 25) + (2 : MvPolynomial (Fin 28) ℂ) * (X 17 * X 19)

/-- Relation 76. -/
def P76 : MvPolynomial (Fin 28) ℂ :=
  (2 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 25) + (2 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 27) + (2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 22) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 24) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 18 * X 19) + (2 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 22)

/-- Relation 77. -/
def P77 : MvPolynomial (Fin 28) ℂ :=
  (4 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 26) + (4 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 24) + (4 : MvPolynomial (Fin 28) ℂ) * (X 16 * X 19)

/-- Relation 78. -/
def P78 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 27) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 21) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 25) + (1 : MvPolynomial (Fin 28) ℂ) * (X 17 * X 18) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 21) + (1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 23) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 21) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 21)

/-- Relation 79. -/
def P79 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 27) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 23) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 24) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 16 * X 18) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 20) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 20)

/-- Relation 80. -/
def P80 : MvPolynomial (Fin 28) ℂ :=
  (-8 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 25) + (8 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 27) + (8 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 21) + (-8 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 23) + (8 : MvPolynomial (Fin 28) ℂ) * (X 17 * X 18) + (8 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 21)

/-- Relation 81. -/
def P81 : MvPolynomial (Fin 28) ℂ :=
  (16 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 26) + (16 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 23) + (-16 : MvPolynomial (Fin 28) ℂ) * (X 16 * X 17)

/-- Relation 82. -/
def P82 : MvPolynomial (Fin 28) ℂ :=
  (-4 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 22) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 27) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 18 * X 19) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 22) + (4 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 24) + (4 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 25) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 22) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 22)

/-- Relation 83. -/
def P83 : MvPolynomial (Fin 28) ℂ :=
  (-4 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 24) + (4 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 27) + (4 : MvPolynomial (Fin 28) ℂ) * (X 16 * X 18) + (4 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 20) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 23) + (4 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 20)

/-- Relation 84. -/
def P84 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 27) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 19 * X 21) + (1 : MvPolynomial (Fin 28) ℂ) * (X 17 * X 22) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 25) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 26)

/-- Relation 85. -/
def P85 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 27) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 19 * X 20) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 16 * X 22) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 24) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 24) + (1 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 26) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 24)

/-- Relation 86. -/
def P86 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 27) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 17 * X 20) + (1 : MvPolynomial (Fin 28) ℂ) * (X 16 * X 21) + (1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 23) + (1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 23) + (1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 26) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 23)

/-- Relation 87. -/
def P87 : MvPolynomial (Fin 28) ℂ :=
  (-2 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 25) + (2 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 27) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 17 * X 22) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 25) + (2 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 26) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 19 * X 21) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 25)

/-- Relation 88. -/
def P88 : MvPolynomial (Fin 28) ℂ :=
  (-2 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 26) + (2 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 27) + (2 : MvPolynomial (Fin 28) ℂ) * (X 16 * X 22) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 24) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 19 * X 20)

/-- Relation 89. -/
def P89 : MvPolynomial (Fin 28) ℂ :=
  (-1 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 27) + (1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 23) + (1 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 26) + (1 : MvPolynomial (Fin 28) ℂ) * (X 17 * X 20) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 16 * X 21) + (1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 23) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 23)

/-- Relation 90. -/
def P90 : MvPolynomial (Fin 28) ℂ :=
  (8 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 25) + (-8 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 27) + (-8 : MvPolynomial (Fin 28) ℂ) * (X 19 * X 21) + (8 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 25) + (-8 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 26) + (-8 : MvPolynomial (Fin 28) ℂ) * (X 17 * X 22) + (8 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 25)

/-- Relation 91. -/
def P91 : MvPolynomial (Fin 28) ℂ :=
  (8 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 26) + (8 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 27) + (8 : MvPolynomial (Fin 28) ℂ) * (X 16 * X 21) + (-8 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 23) + (8 : MvPolynomial (Fin 28) ℂ) * (X 17 * X 20)

/-- Relation 92. -/
def P92 : MvPolynomial (Fin 28) ℂ :=
  (4 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 24) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 27) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 19 * X 20) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 16 * X 22) + (4 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 24) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 26) + (4 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 24)

/-- Relation 93. -/
def P93 : MvPolynomial (Fin 28) ℂ :=
  (-2 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 27) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 21 * X 22) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 18 * X 25)

/-- Relation 94. -/
def P94 : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 27) + (1 : MvPolynomial (Fin 28) ℂ) * (X 19 * X 23) + (-1 : MvPolynomial (Fin 28) ℂ) * (X 17 * X 24) + (1 : MvPolynomial (Fin 28) ℂ) * (X 16 * X 25) + (1 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 26) + (1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 26)

/-- Relation 95. -/
def P95 : MvPolynomial (Fin 28) ℂ :=
  (2 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 26) + (2 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 27) + (2 : MvPolynomial (Fin 28) ℂ) * (X 17 * X 24) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 16 * X 25) + (2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 26) + (2 : MvPolynomial (Fin 28) ℂ) * (X 19 * X 23)

/-- Relation 96. -/
def P96 : MvPolynomial (Fin 28) ℂ :=
  (-4 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 27) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 20 * X 22) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 18 * X 24)

/-- Relation 97. -/
def P97 : MvPolynomial (Fin 28) ℂ :=
  (-8 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 26) + (-8 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 27) + (8 : MvPolynomial (Fin 28) ℂ) * (X 19 * X 23) + (8 : MvPolynomial (Fin 28) ℂ) * (X 16 * X 25) + (-8 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 26) + (8 : MvPolynomial (Fin 28) ℂ) * (X 17 * X 24)

/-- Relation 98. -/
def P98 : MvPolynomial (Fin 28) ℂ :=
  (16 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 27) + (-16 : MvPolynomial (Fin 28) ℂ) * (X 20 * X 21) + (-16 : MvPolynomial (Fin 28) ℂ) * (X 18 * X 23)

/-- Relation 99. -/
def P99 : MvPolynomial (Fin 28) ℂ :=
  (2 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 27) + (2 : MvPolynomial (Fin 28) ℂ) * (X 22 * X 23) + (2 : MvPolynomial (Fin 28) ℂ) * (X 21 * X 24) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 20 * X 25) + (2 : MvPolynomial (Fin 28) ℂ) * (X 18 * X 26)

/-- Relation 100. -/
def P100 : MvPolynomial (Fin 28) ℂ :=
  (2 : MvPolynomial (Fin 28) ℂ) * (X 18 * X 26) + (2 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 27) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 21 * X 24) + (2 : MvPolynomial (Fin 28) ℂ) * (X 20 * X 25) + (2 : MvPolynomial (Fin 28) ℂ) * (X 22 * X 23)

/-- Relation 101. -/
def P101 : MvPolynomial (Fin 28) ℂ :=
  (-8 : MvPolynomial (Fin 28) ℂ) * (X 18 * X 26) + (-8 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 27) + (8 : MvPolynomial (Fin 28) ℂ) * (X 22 * X 23) + (-8 : MvPolynomial (Fin 28) ℂ) * (X 20 * X 25) + (-8 : MvPolynomial (Fin 28) ℂ) * (X 21 * X 24)

/-- Relation 102. -/
def P102 : MvPolynomial (Fin 28) ℂ :=
  (4 : MvPolynomial (Fin 28) ℂ) * (X 16 * X 27) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 23 * X 24) + (4 : MvPolynomial (Fin 28) ℂ) * (X 20 * X 26)

/-- Relation 103. -/
def P103 : MvPolynomial (Fin 28) ℂ :=
  (4 : MvPolynomial (Fin 28) ℂ) * (X 21 * X 26) + (4 : MvPolynomial (Fin 28) ℂ) * (X 17 * X 27) + (-4 : MvPolynomial (Fin 28) ℂ) * (X 23 * X 25)

/-- Relation 104. -/
def P104 : MvPolynomial (Fin 28) ℂ :=
  (16 : MvPolynomial (Fin 28) ℂ) * (X 22 * X 26) + (-16 : MvPolynomial (Fin 28) ℂ) * (X 19 * X 27) + (-16 : MvPolynomial (Fin 28) ℂ) * (X 24 * X 25)

/-- The Casimir. -/
def Qd : MvPolynomial (Fin 28) ℂ :=
  (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 0) + (2 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 1) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 2) + (1 : MvPolynomial (Fin 28) ℂ) * (X 0 * X 3) + (2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 1) + (2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 2) + (2 : MvPolynomial (Fin 28) ℂ) * (X 1 * X 3) + (1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 2) + (1 : MvPolynomial (Fin 28) ℂ) * (X 2 * X 3) + (1 : MvPolynomial (Fin 28) ℂ) * (X 3 * X 3) + (2 : MvPolynomial (Fin 28) ℂ) * (X 4 * X 16) + (2 : MvPolynomial (Fin 28) ℂ) * (X 5 * X 17) + (2 : MvPolynomial (Fin 28) ℂ) * (X 6 * X 18) + (2 : MvPolynomial (Fin 28) ℂ) * (X 7 * X 19) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 8 * X 20) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 9 * X 21) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 10 * X 22) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 11 * X 23) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 12 * X 24) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 13 * X 25) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 14 * X 26) + (-2 : MvPolynomial (Fin 28) ℂ) * (X 15 * X 27)

/-- The relations of `I₂ⁿˢ` as coefficient lists. -/
def relTable : Fin 105 → List (Fin 28 × Fin 28 × ℂ) := ![
  [(4, 15, (-1 : ℂ)), (8, 14, (1 : ℂ)), (11, 12, (-1 : ℂ))],
  [(5, 15, (-1 : ℂ)), (9, 14, (1 : ℂ)), (11, 13, (-1 : ℂ))],
  [(7, 15, (1 : ℂ)), (10, 14, (1 : ℂ)), (12, 13, (-1 : ℂ))],
  [(3, 15, (1 : ℂ)), (6, 14, (1 : ℂ)), (8, 13, (1 : ℂ)), (9, 12, (-1 : ℂ)), (10, 11, (-1 : ℂ))],
  [(2, 15, (1 : ℂ)), (6, 14, (1 : ℂ)), (9, 12, (1 : ℂ)), (8, 13, (-1 : ℂ)), (10, 11, (-1 : ℂ))],
  [(0, 15, (-1 : ℂ)), (6, 14, (-1 : ℂ)), (10, 11, (-1 : ℂ)), (8, 13, (1 : ℂ)), (9, 12, (1 : ℂ))],
  [(15, 18, (-1 : ℂ)), (3, 14, (-1 : ℂ)), (1, 14, (-1 : ℂ)), (4, 13, (-1 : ℂ)), (5, 12, (1 : ℂ)), (7, 11, (-1 : ℂ))],
  [(15, 16, (2 : ℂ)), (6, 13, (2 : ℂ)), (9, 10, (-2 : ℂ))],
  [(15, 18, (-1 : ℂ)), (2, 14, (-1 : ℂ)), (1, 14, (-1 : ℂ)), (5, 12, (-1 : ℂ)), (4, 13, (1 : ℂ)), (7, 11, (-1 : ℂ))],
  [(15, 17, (2 : ℂ)), (6, 12, (2 : ℂ)), (8, 10, (-2 : ℂ))],
  [(15, 19, (-2 : ℂ)), (6, 11, (2 : ℂ)), (8, 9, (-2 : ℂ))],
  [(15, 18, (1 : ℂ)), (0, 14, (1 : ℂ)), (1, 14, (1 : ℂ)), (7, 11, (-1 : ℂ)), (4, 13, (-1 : ℂ)), (5, 12, (-1 : ℂ))],
  [(15, 22, (1 : ℂ)), (3, 11, (1 : ℂ)), (14, 19, (1 : ℂ)), (1, 11, (1 : ℂ)), (4, 9, (1 : ℂ)), (5, 8, (-1 : ℂ)), (0, 11, (1 : ℂ))],
  [(15, 21, (-1 : ℂ)), (3, 12, (-1 : ℂ)), (14, 17, (1 : ℂ)), (1, 12, (-1 : ℂ)), (4, 10, (-1 : ℂ)), (2, 12, (-1 : ℂ)), (7, 8, (-1 : ℂ))],
  [(15, 20, (-1 : ℂ)), (14, 16, (-1 : ℂ)), (1, 13, (-1 : ℂ)), (5, 10, (1 : ℂ)), (7, 9, (-1 : ℂ))],
  [(15, 22, (1 : ℂ)), (2, 11, (1 : ℂ)), (14, 19, (1 : ℂ)), (1, 11, (1 : ℂ)), (5, 8, (1 : ℂ)), (4, 9, (-1 : ℂ)), (0, 11, (1 : ℂ))],
  [(15, 21, (-1 : ℂ)), (14, 17, (-1 : ℂ)), (1, 12, (-1 : ℂ)), (4, 10, (1 : ℂ)), (7, 8, (-1 : ℂ))],
  [(15, 20, (-1 : ℂ)), (2, 13, (-1 : ℂ)), (14, 16, (1 : ℂ)), (1, 13, (-1 : ℂ)), (5, 10, (-1 : ℂ)), (3, 13, (-1 : ℂ)), (7, 9, (-1 : ℂ))],
  [(14, 19, (2 : ℂ)), (15, 22, (-2 : ℂ)), (1, 11, (-2 : ℂ)), (4, 9, (2 : ℂ)), (5, 8, (2 : ℂ))],
  [(15, 21, (1 : ℂ)), (0, 12, (1 : ℂ)), (14, 17, (-1 : ℂ)), (1, 12, (1 : ℂ)), (7, 8, (-1 : ℂ)), (4, 10, (-1 : ℂ)), (2, 12, (1 : ℂ))],
  [(15, 20, (1 : ℂ)), (0, 13, (1 : ℂ)), (14, 16, (-1 : ℂ)), (1, 13, (1 : ℂ)), (7, 9, (-1 : ℂ)), (3, 13, (1 : ℂ)), (5, 10, (-1 : ℂ))],
  [(15, 25, (-1 : ℂ)), (3, 8, (1 : ℂ)), (12, 19, (1 : ℂ)), (11, 17, (-1 : ℂ)), (1, 8, (1 : ℂ)), (4, 6, (1 : ℂ)), (2, 8, (1 : ℂ)), (0, 8, (1 : ℂ))],
  [(15, 24, (-1 : ℂ)), (11, 16, (1 : ℂ)), (13, 19, (1 : ℂ)), (1, 9, (1 : ℂ)), (5, 6, (-1 : ℂ)), (0, 9, (1 : ℂ))],
  [(15, 23, (1 : ℂ)), (12, 16, (-1 : ℂ)), (13, 17, (1 : ℂ)), (1, 10, (-1 : ℂ)), (2, 10, (-1 : ℂ)), (6, 7, (-1 : ℂ))],
  [(14, 20, (2 : ℂ)), (13, 18, (-2 : ℂ)), (5, 7, (2 : ℂ))],
  [(15, 25, (-1 : ℂ)), (11, 17, (1 : ℂ)), (12, 19, (1 : ℂ)), (1, 8, (1 : ℂ)), (4, 6, (-1 : ℂ)), (0, 8, (1 : ℂ))],
  [(15, 24, (-1 : ℂ)), (2, 9, (1 : ℂ)), (13, 19, (1 : ℂ)), (11, 16, (-1 : ℂ)), (1, 9, (1 : ℂ)), (5, 6, (1 : ℂ)), (3, 9, (1 : ℂ)), (0, 9, (1 : ℂ))],
  [(14, 21, (2 : ℂ)), (12, 18, (-2 : ℂ)), (4, 7, (2 : ℂ))],
  [(15, 23, (1 : ℂ)), (13, 17, (-1 : ℂ)), (12, 16, (1 : ℂ)), (1, 10, (-1 : ℂ)), (3, 10, (-1 : ℂ)), (6, 7, (-1 : ℂ))],
  [(14, 22, (4 : ℂ)), (11, 18, (-4 : ℂ)), (4, 5, (-4 : ℂ))],
  [(12, 19, (2 : ℂ)), (15, 25, (2 : ℂ)), (11, 17, (2 : ℂ)), (1, 8, (-2 : ℂ)), (4, 6, (2 : ℂ)), (2, 8, (-2 : ℂ))],
  [(13, 19, (2 : ℂ)), (15, 24, (2 : ℂ)), (11, 16, (2 : ℂ)), (1, 9, (-2 : ℂ)), (3, 9, (-2 : ℂ)), (5, 6, (2 : ℂ))],
  [(15, 23, (-1 : ℂ)), (0, 10, (1 : ℂ)), (13, 17, (-1 : ℂ)), (12, 16, (-1 : ℂ)), (1, 10, (1 : ℂ)), (6, 7, (-1 : ℂ)), (3, 10, (1 : ℂ)), (2, 10, (1 : ℂ))],
  [(14, 25, (1 : ℂ)), (8, 18, (-1 : ℂ)), (3, 4, (-1 : ℂ)), (12, 22, (1 : ℂ)), (11, 21, (1 : ℂ)), (1, 4, (-2 : ℂ)), (2, 4, (-1 : ℂ)), (0, 4, (-1 : ℂ))],
  [(15, 26, (1 : ℂ)), (8, 16, (1 : ℂ)), (10, 19, (1 : ℂ)), (9, 17, (-1 : ℂ)), (1, 6, (1 : ℂ)), (2, 6, (1 : ℂ)), (0, 6, (1 : ℂ))],
  [(14, 24, (1 : ℂ)), (11, 20, (-1 : ℂ)), (13, 22, (1 : ℂ)), (9, 18, (1 : ℂ)), (0, 5, (-1 : ℂ))],
  [(14, 23, (-1 : ℂ)), (12, 20, (1 : ℂ)), (13, 21, (-1 : ℂ)), (10, 18, (-1 : ℂ)), (2, 7, (-1 : ℂ))],
  [(14, 25, (1 : ℂ)), (11, 21, (-1 : ℂ)), (12, 22, (1 : ℂ)), (8, 18, (1 : ℂ)), (0, 4, (-1 : ℂ))],
  [(15, 26, (1 : ℂ)), (9, 17, (1 : ℂ)), (10, 19, (1 : ℂ)), (8, 16, (-1 : ℂ)), (1, 6, (1 : ℂ)), (3, 6, (1 : ℂ)), (0, 6, (1 : ℂ))],
  [(14, 24, (1 : ℂ)), (9, 18, (-1 : ℂ)), (2, 5, (-1 : ℂ)), (13, 22, (1 : ℂ)), (11, 20, (1 : ℂ)), (1, 5, (-2 : ℂ)), (3, 5, (-1 : ℂ)), (0, 5, (-1 : ℂ))],
  [(13, 21, (2 : ℂ)), (14, 23, (-2 : ℂ)), (10, 18, (-2 : ℂ)), (12, 20, (-2 : ℂ)), (3, 7, (-2 : ℂ))],
  [(12, 22, (4 : ℂ)), (14, 25, (-4 : ℂ)), (8, 18, (-4 : ℂ)), (11, 21, (-4 : ℂ)), (2, 4, (4 : ℂ))],
  [(13, 22, (4 : ℂ)), (14, 24, (-4 : ℂ)), (9, 18, (-4 : ℂ)), (11, 20, (-4 : ℂ)), (3, 5, (4 : ℂ))],
  [(10, 19, (2 : ℂ)), (15, 26, (-2 : ℂ)), (9, 17, (2 : ℂ)), (8, 16, (2 : ℂ)), (1, 6, (-2 : ℂ)), (3, 6, (-2 : ℂ)), (2, 6, (-2 : ℂ))],
  [(14, 23, (1 : ℂ)), (10, 18, (-1 : ℂ)), (0, 7, (1 : ℂ)), (13, 21, (1 : ℂ)), (12, 20, (1 : ℂ)), (1, 7, (2 : ℂ)), (3, 7, (1 : ℂ)), (2, 7, (1 : ℂ))],
  [(13, 25, (1 : ℂ)), (14, 26, (-1 : ℂ)), (6, 18, (-1 : ℂ)), (8, 20, (-1 : ℂ)), (3, 3, (1 : ℂ)), (10, 22, (1 : ℂ)), (12, 24, (-1 : ℂ)), (9, 21, (1 : ℂ)), (11, 23, (-1 : ℂ)), (1, 3, (2 : ℂ)), (2, 3, (1 : ℂ)), (0, 3, (1 : ℂ))],
  [(14, 26, (-1 : ℂ)), (15, 27, (1 : ℂ)), (4, 16, (-1 : ℂ)), (8, 20, (-1 : ℂ)), (7, 19, (1 : ℂ)), (10, 22, (1 : ℂ)), (5, 17, (1 : ℂ)), (9, 21, (1 : ℂ)), (1, 1, (-1 : ℂ)), (1, 2, (-1 : ℂ)), (0, 1, (-1 : ℂ))],
  [(11, 24, (-2 : ℂ)), (9, 22, (-2 : ℂ)), (5, 19, (-2 : ℂ))],
  [(12, 24, (1 : ℂ)), (14, 26, (-1 : ℂ)), (8, 20, (-1 : ℂ)), (11, 23, (1 : ℂ)), (10, 22, (1 : ℂ)), (13, 25, (-1 : ℂ)), (6, 18, (1 : ℂ)), (9, 21, (1 : ℂ)), (0, 2, (1 : ℂ))],
  [(12, 23, (-2 : ℂ)), (10, 21, (-2 : ℂ)), (7, 17, (-2 : ℂ))],
  [(11, 25, (-2 : ℂ)), (8, 22, (-2 : ℂ)), (4, 19, (-2 : ℂ))],
  [(13, 25, (1 : ℂ)), (14, 26, (-1 : ℂ)), (9, 21, (-1 : ℂ)), (11, 23, (1 : ℂ)), (10, 22, (1 : ℂ)), (12, 24, (-1 : ℂ)), (6, 18, (1 : ℂ)), (8, 20, (1 : ℂ)), (0, 3, (1 : ℂ))],
  [(14, 26, (-1 : ℂ)), (15, 27, (1 : ℂ)), (5, 17, (-1 : ℂ)), (9, 21, (-1 : ℂ)), (7, 19, (1 : ℂ)), (10, 22, (1 : ℂ)), (4, 16, (1 : ℂ)), (8, 20, (1 : ℂ)), (1, 1, (-1 : ℂ)), (1, 3, (-1 : ℂ)), (0, 1, (-1 : ℂ))],
  [(12, 24, (1 : ℂ)), (14, 26, (-1 : ℂ)), (6, 18, (-1 : ℂ)), (9, 21, (-1 : ℂ)), (2, 2, (1 : ℂ)), (10, 22, (1 : ℂ)), (13, 25, (-1 : ℂ)), (8, 20, (1 : ℂ)), (11, 23, (-1 : ℂ)), (1, 2, (2 : ℂ)), (2, 3, (1 : ℂ)), (0, 2, (1 : ℂ))],
  [(13, 23, (-4 : ℂ)), (10, 20, (-4 : ℂ)), (7, 16, (-4 : ℂ))],
  [(12, 25, (-8 : ℂ)), (8, 21, (-8 : ℂ)), (4, 17, (8 : ℂ))],
  [(10, 22, (4 : ℂ)), (12, 24, (-4 : ℂ)), (13, 25, (-4 : ℂ)), (14, 26, (4 : ℂ)), (6, 18, (-4 : ℂ)), (8, 20, (-4 : ℂ)), (9, 21, (-4 : ℂ)), (11, 23, (4 : ℂ)), (2, 3, (-4 : ℂ))],
  [(13, 24, (-8 : ℂ)), (9, 20, (-8 : ℂ)), (5, 16, (8 : ℂ))],
  [(7, 19, (2 : ℂ)), (10, 22, (2 : ℂ)), (14, 26, (2 : ℂ)), (15, 27, (-2 : ℂ)), (5, 17, (-2 : ℂ)), (9, 21, (-2 : ℂ)), (4, 16, (-2 : ℂ)), (8, 20, (-2 : ℂ)), (1, 1, (2 : ℂ)), (1, 3, (2 : ℂ)), (1, 2, (2 : ℂ))],
  [(11, 23, (-1 : ℂ)), (14, 26, (1 : ℂ)), (6, 18, (1 : ℂ)), (10, 22, (1 : ℂ)), (0, 0, (-1 : ℂ)), (9, 21, (-1 : ℂ)), (13, 25, (1 : ℂ)), (8, 20, (-1 : ℂ)), (12, 24, (1 : ℂ)), (0, 1, (-2 : ℂ)), (0, 3, (-1 : ℂ)), (0, 2, (-1 : ℂ))],
  [(14, 27, (-1 : ℂ)), (1, 18, (-1 : ℂ)), (4, 20, (1 : ℂ)), (7, 22, (1 : ℂ)), (5, 21, (-1 : ℂ)), (2, 18, (-1 : ℂ)), (0, 18, (-1 : ℂ))],
  [(13, 26, (-2 : ℂ)), (6, 20, (-2 : ℂ)), (3, 16, (2 : ℂ)), (10, 24, (-2 : ℂ)), (9, 23, (-2 : ℂ)), (1, 16, (4 : ℂ)), (2, 16, (2 : ℂ)), (0, 16, (2 : ℂ))],
  [(11, 26, (1 : ℂ)), (8, 24, (-1 : ℂ)), (6, 22, (-1 : ℂ)), (9, 25, (1 : ℂ)), (2, 19, (1 : ℂ))],
  [(12, 26, (-1 : ℂ)), (8, 23, (1 : ℂ)), (10, 25, (-1 : ℂ)), (6, 21, (1 : ℂ)), (0, 17, (1 : ℂ))],
  [(9, 25, (-2 : ℂ)), (11, 26, (2 : ℂ)), (6, 22, (-2 : ℂ)), (8, 24, (2 : ℂ)), (3, 19, (2 : ℂ))],
  [(14, 27, (-1 : ℂ)), (5, 21, (1 : ℂ)), (7, 22, (1 : ℂ)), (1, 18, (-1 : ℂ)), (4, 20, (-1 : ℂ)), (3, 18, (-1 : ℂ)), (0, 18, (-1 : ℂ))],
  [(13, 26, (-2 : ℂ)), (9, 23, (2 : ℂ)), (10, 24, (-2 : ℂ)), (6, 20, (2 : ℂ)), (0, 16, (2 : ℂ))],
  [(12, 26, (-1 : ℂ)), (2, 17, (1 : ℂ)), (6, 21, (-1 : ℂ)), (10, 25, (-1 : ℂ)), (8, 23, (-1 : ℂ)), (1, 17, (2 : ℂ)), (3, 17, (1 : ℂ)), (0, 17, (1 : ℂ))],
  [(10, 25, (-8 : ℂ)), (12, 26, (8 : ℂ)), (6, 21, (-8 : ℂ)), (8, 23, (8 : ℂ)), (3, 17, (-8 : ℂ))],
  [(7, 22, (4 : ℂ)), (14, 27, (4 : ℂ)), (1, 18, (4 : ℂ)), (4, 20, (4 : ℂ)), (5, 21, (4 : ℂ)), (3, 18, (4 : ℂ)), (2, 18, (4 : ℂ))],
  [(10, 24, (-8 : ℂ)), (13, 26, (8 : ℂ)), (6, 20, (-8 : ℂ)), (9, 23, (8 : ℂ)), (2, 16, (-8 : ℂ))],
  [(0, 19, (-2 : ℂ)), (6, 22, (-2 : ℂ)), (11, 26, (-2 : ℂ)), (9, 25, (-2 : ℂ)), (8, 24, (-2 : ℂ)), (1, 19, (-4 : ℂ)), (3, 19, (-2 : ℂ)), (2, 19, (-2 : ℂ))],
  [(11, 27, (1 : ℂ)), (18, 19, (-1 : ℂ)), (1, 22, (1 : ℂ)), (4, 24, (1 : ℂ)), (5, 25, (-1 : ℂ)), (2, 22, (1 : ℂ))],
  [(12, 27, (-1 : ℂ)), (17, 18, (-1 : ℂ)), (1, 21, (-1 : ℂ)), (4, 23, (-1 : ℂ)), (7, 25, (-1 : ℂ)), (0, 21, (-1 : ℂ))],
  [(13, 27, (-1 : ℂ)), (16, 18, (1 : ℂ)), (1, 20, (-1 : ℂ)), (3, 20, (-1 : ℂ)), (7, 24, (-1 : ℂ)), (5, 23, (1 : ℂ)), (2, 20, (-1 : ℂ)), (0, 20, (-1 : ℂ))],
  [(8, 26, (2 : ℂ)), (6, 25, (2 : ℂ)), (17, 19, (2 : ℂ))],
  [(5, 25, (2 : ℂ)), (11, 27, (2 : ℂ)), (1, 22, (2 : ℂ)), (4, 24, (-2 : ℂ)), (18, 19, (-2 : ℂ)), (3, 22, (2 : ℂ))],
  [(9, 26, (4 : ℂ)), (6, 24, (4 : ℂ)), (16, 19, (4 : ℂ))],
  [(12, 27, (-1 : ℂ)), (2, 21, (-1 : ℂ)), (7, 25, (-1 : ℂ)), (17, 18, (1 : ℂ)), (1, 21, (-1 : ℂ)), (4, 23, (1 : ℂ)), (3, 21, (-1 : ℂ)), (0, 21, (-1 : ℂ))],
  [(13, 27, (-1 : ℂ)), (5, 23, (-1 : ℂ)), (7, 24, (-1 : ℂ)), (16, 18, (-1 : ℂ)), (1, 20, (-1 : ℂ)), (0, 20, (-1 : ℂ))],
  [(7, 25, (-8 : ℂ)), (12, 27, (8 : ℂ)), (1, 21, (8 : ℂ)), (4, 23, (-8 : ℂ)), (17, 18, (8 : ℂ)), (3, 21, (8 : ℂ))],
  [(10, 26, (16 : ℂ)), (6, 23, (16 : ℂ)), (16, 17, (-16 : ℂ))],
  [(0, 22, (-4 : ℂ)), (11, 27, (-4 : ℂ)), (18, 19, (-4 : ℂ)), (1, 22, (-4 : ℂ)), (4, 24, (4 : ℂ)), (5, 25, (4 : ℂ)), (3, 22, (-4 : ℂ)), (2, 22, (-4 : ℂ))],
  [(7, 24, (-4 : ℂ)), (13, 27, (4 : ℂ)), (16, 18, (4 : ℂ)), (1, 20, (4 : ℂ)), (5, 23, (-4 : ℂ)), (2, 20, (4 : ℂ))],
  [(8, 27, (1 : ℂ)), (19, 21, (-1 : ℂ)), (17, 22, (1 : ℂ)), (1, 25, (-1 : ℂ)), (4, 26, (-1 : ℂ))],
  [(9, 27, (1 : ℂ)), (19, 20, (-1 : ℂ)), (16, 22, (-1 : ℂ)), (1, 24, (-1 : ℂ)), (3, 24, (-1 : ℂ)), (5, 26, (1 : ℂ)), (2, 24, (-1 : ℂ))],
  [(10, 27, (-1 : ℂ)), (17, 20, (-1 : ℂ)), (16, 21, (1 : ℂ)), (1, 23, (1 : ℂ)), (3, 23, (1 : ℂ)), (7, 26, (1 : ℂ)), (0, 23, (1 : ℂ))],
  [(2, 25, (-2 : ℂ)), (8, 27, (2 : ℂ)), (17, 22, (-2 : ℂ)), (1, 25, (-2 : ℂ)), (4, 26, (2 : ℂ)), (19, 21, (-2 : ℂ)), (3, 25, (-2 : ℂ))],
  [(5, 26, (-2 : ℂ)), (9, 27, (2 : ℂ)), (16, 22, (2 : ℂ)), (1, 24, (-2 : ℂ)), (19, 20, (-2 : ℂ))],
  [(10, 27, (-1 : ℂ)), (2, 23, (1 : ℂ)), (7, 26, (1 : ℂ)), (17, 20, (1 : ℂ)), (16, 21, (-1 : ℂ)), (1, 23, (1 : ℂ)), (0, 23, (1 : ℂ))],
  [(0, 25, (8 : ℂ)), (8, 27, (-8 : ℂ)), (19, 21, (-8 : ℂ)), (1, 25, (8 : ℂ)), (4, 26, (-8 : ℂ)), (17, 22, (-8 : ℂ)), (3, 25, (8 : ℂ))],
  [(7, 26, (8 : ℂ)), (10, 27, (8 : ℂ)), (16, 21, (8 : ℂ)), (1, 23, (-8 : ℂ)), (17, 20, (8 : ℂ))],
  [(0, 24, (4 : ℂ)), (9, 27, (-4 : ℂ)), (19, 20, (-4 : ℂ)), (16, 22, (-4 : ℂ)), (1, 24, (4 : ℂ)), (5, 26, (-4 : ℂ)), (2, 24, (4 : ℂ))],
  [(4, 27, (-2 : ℂ)), (21, 22, (-2 : ℂ)), (18, 25, (-2 : ℂ))],
  [(6, 27, (1 : ℂ)), (19, 23, (1 : ℂ)), (17, 24, (-1 : ℂ)), (16, 25, (1 : ℂ)), (1, 26, (1 : ℂ)), (3, 26, (1 : ℂ))],
  [(2, 26, (2 : ℂ)), (6, 27, (2 : ℂ)), (17, 24, (2 : ℂ)), (16, 25, (-2 : ℂ)), (1, 26, (2 : ℂ)), (19, 23, (2 : ℂ))],
  [(5, 27, (-4 : ℂ)), (20, 22, (-4 : ℂ)), (18, 24, (-4 : ℂ))],
  [(0, 26, (-8 : ℂ)), (6, 27, (-8 : ℂ)), (19, 23, (8 : ℂ)), (16, 25, (8 : ℂ)), (1, 26, (-8 : ℂ)), (17, 24, (8 : ℂ))],
  [(7, 27, (16 : ℂ)), (20, 21, (-16 : ℂ)), (18, 23, (-16 : ℂ))],
  [(3, 27, (2 : ℂ)), (22, 23, (2 : ℂ)), (21, 24, (2 : ℂ)), (20, 25, (-2 : ℂ)), (18, 26, (2 : ℂ))],
  [(18, 26, (2 : ℂ)), (2, 27, (2 : ℂ)), (21, 24, (-2 : ℂ)), (20, 25, (2 : ℂ)), (22, 23, (2 : ℂ))],
  [(18, 26, (-8 : ℂ)), (0, 27, (-8 : ℂ)), (22, 23, (8 : ℂ)), (20, 25, (-8 : ℂ)), (21, 24, (-8 : ℂ))],
  [(16, 27, (4 : ℂ)), (23, 24, (-4 : ℂ)), (20, 26, (4 : ℂ))],
  [(21, 26, (4 : ℂ)), (17, 27, (4 : ℂ)), (23, 25, (-4 : ℂ))],
  [(22, 26, (16 : ℂ)), (19, 27, (-16 : ℂ)), (24, 25, (-16 : ℂ))]]

/-- The Casimir as a coefficient list. -/
def casEntries : List (Fin 28 × Fin 28 × ℂ) :=
  [(0, 0, (1 : ℂ)), (0, 1, (2 : ℂ)), (0, 2, (1 : ℂ)), (0, 3, (1 : ℂ)), (1, 1, (2 : ℂ)), (1, 2, (2 : ℂ)), (1, 3, (2 : ℂ)), (2, 2, (1 : ℂ)), (2, 3, (1 : ℂ)), (3, 3, (1 : ℂ)), (4, 16, (2 : ℂ)), (5, 17, (2 : ℂ)), (6, 18, (2 : ℂ)), (7, 19, (2 : ℂ)), (8, 20, (-2 : ℂ)), (9, 21, (-2 : ℂ)), (10, 22, (-2 : ℂ)), (11, 23, (-2 : ℂ)), (12, 24, (-2 : ℂ)), (13, 25, (-2 : ℂ)), (14, 26, (-2 : ℂ)), (15, 27, (-2 : ℂ))]

/-- The relation matrices. -/
def rel (r : Fin 105) : Fin 28 × Fin 28 → ℂ := A2.entryMatrix (relTable r)

/-- The Casimir matrix. -/
def cas : Fin 28 × Fin 28 → ℂ := A2.entryMatrix casEntries

theorem cas_eq : quadraticRelation cas = Qd := by
  rw [cas, A2.quadraticRelation_entryMatrix]
  simp [casEntries, Qd, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring

theorem mem_of_natCast_mul (L : ℕ) (hL : L ≠ 0) {f : MvPolynomial (Fin 28) ℂ}
    (h : (L : MvPolynomial (Fin 28) ℂ) * f ∈ quadraticIdeal rel) : f ∈ quadraticIdeal rel := by
  have hf : f = MvPolynomial.C ((L : ℂ)⁻¹) * ((L : MvPolynomial (Fin 28) ℂ) * f) := by
    rw [← mul_assoc, ← map_natCast MvPolynomial.C L, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hL), map_one, one_mul]
  rw [hf]
  exact Ideal.mul_mem_left _ _ h

theorem P0_mem : P0 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 0) = P0 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P0, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨0, rfl⟩

theorem P1_mem : P1 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 1) = P1 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P1, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨1, rfl⟩

theorem P2_mem : P2 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 2) = P2 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P2, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨2, rfl⟩

theorem P3_mem : P3 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 3) = P3 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P3, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨3, rfl⟩

theorem P4_mem : P4 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 4) = P4 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P4, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨4, rfl⟩

theorem P5_mem : P5 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 5) = P5 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P5, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨5, rfl⟩

theorem P6_mem : P6 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 6) = P6 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P6, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨6, rfl⟩

theorem P7_mem : P7 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 7) = P7 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P7, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨7, rfl⟩

theorem P8_mem : P8 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 8) = P8 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P8, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨8, rfl⟩

theorem P9_mem : P9 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 9) = P9 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P9, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨9, rfl⟩

theorem P10_mem : P10 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 10) = P10 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P10, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨10, rfl⟩

theorem P11_mem : P11 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 11) = P11 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P11, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨11, rfl⟩

theorem P12_mem : P12 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 12) = P12 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P12, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨12, rfl⟩

theorem P13_mem : P13 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 13) = P13 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P13, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨13, rfl⟩

theorem P14_mem : P14 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 14) = P14 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P14, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨14, rfl⟩

theorem P15_mem : P15 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 15) = P15 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P15, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨15, rfl⟩

theorem P16_mem : P16 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 16) = P16 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P16, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨16, rfl⟩

theorem P17_mem : P17 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 17) = P17 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P17, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨17, rfl⟩

theorem P18_mem : P18 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 18) = P18 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P18, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨18, rfl⟩

theorem P19_mem : P19 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 19) = P19 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P19, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨19, rfl⟩

theorem P20_mem : P20 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 20) = P20 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P20, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨20, rfl⟩

theorem P21_mem : P21 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 21) = P21 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P21, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨21, rfl⟩

theorem P22_mem : P22 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 22) = P22 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P22, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨22, rfl⟩

theorem P23_mem : P23 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 23) = P23 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P23, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨23, rfl⟩

theorem P24_mem : P24 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 24) = P24 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P24, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨24, rfl⟩

theorem P25_mem : P25 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 25) = P25 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P25, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨25, rfl⟩

theorem P26_mem : P26 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 26) = P26 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P26, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨26, rfl⟩

theorem P27_mem : P27 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 27) = P27 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P27, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨27, rfl⟩

theorem P28_mem : P28 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 28) = P28 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P28, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨28, rfl⟩

theorem P29_mem : P29 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 29) = P29 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P29, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨29, rfl⟩

theorem P30_mem : P30 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 30) = P30 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P30, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨30, rfl⟩

theorem P31_mem : P31 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 31) = P31 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P31, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨31, rfl⟩

theorem P32_mem : P32 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 32) = P32 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P32, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨32, rfl⟩

theorem P33_mem : P33 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 33) = P33 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P33, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨33, rfl⟩

theorem P34_mem : P34 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 34) = P34 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P34, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨34, rfl⟩

theorem P35_mem : P35 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 35) = P35 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P35, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨35, rfl⟩

theorem P36_mem : P36 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 36) = P36 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P36, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨36, rfl⟩

theorem P37_mem : P37 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 37) = P37 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P37, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨37, rfl⟩

theorem P38_mem : P38 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 38) = P38 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P38, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨38, rfl⟩

theorem P39_mem : P39 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 39) = P39 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P39, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨39, rfl⟩

theorem P40_mem : P40 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 40) = P40 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P40, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨40, rfl⟩

theorem P41_mem : P41 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 41) = P41 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P41, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨41, rfl⟩

theorem P42_mem : P42 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 42) = P42 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P42, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨42, rfl⟩

theorem P43_mem : P43 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 43) = P43 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P43, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨43, rfl⟩

theorem P44_mem : P44 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 44) = P44 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P44, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨44, rfl⟩

theorem P45_mem : P45 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 45) = P45 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P45, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨45, rfl⟩

theorem P46_mem : P46 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 46) = P46 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P46, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨46, rfl⟩

theorem P47_mem : P47 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 47) = P47 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P47, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨47, rfl⟩

theorem P48_mem : P48 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 48) = P48 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P48, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨48, rfl⟩

theorem P49_mem : P49 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 49) = P49 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P49, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨49, rfl⟩

theorem P50_mem : P50 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 50) = P50 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P50, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨50, rfl⟩

theorem P51_mem : P51 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 51) = P51 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P51, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨51, rfl⟩

theorem P52_mem : P52 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 52) = P52 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P52, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨52, rfl⟩

theorem P53_mem : P53 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 53) = P53 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P53, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨53, rfl⟩

theorem P54_mem : P54 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 54) = P54 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P54, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨54, rfl⟩

theorem P55_mem : P55 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 55) = P55 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P55, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨55, rfl⟩

theorem P56_mem : P56 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 56) = P56 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P56, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨56, rfl⟩

theorem P57_mem : P57 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 57) = P57 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P57, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨57, rfl⟩

theorem P58_mem : P58 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 58) = P58 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P58, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨58, rfl⟩

theorem P59_mem : P59 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 59) = P59 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P59, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨59, rfl⟩

theorem P60_mem : P60 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 60) = P60 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P60, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨60, rfl⟩

theorem P61_mem : P61 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 61) = P61 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P61, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨61, rfl⟩

theorem P62_mem : P62 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 62) = P62 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P62, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨62, rfl⟩

theorem P63_mem : P63 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 63) = P63 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P63, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨63, rfl⟩

theorem P64_mem : P64 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 64) = P64 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P64, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨64, rfl⟩

theorem P65_mem : P65 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 65) = P65 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P65, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨65, rfl⟩

theorem P66_mem : P66 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 66) = P66 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P66, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨66, rfl⟩

theorem P67_mem : P67 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 67) = P67 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P67, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨67, rfl⟩

theorem P68_mem : P68 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 68) = P68 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P68, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨68, rfl⟩

theorem P69_mem : P69 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 69) = P69 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P69, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨69, rfl⟩

theorem P70_mem : P70 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 70) = P70 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P70, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨70, rfl⟩

theorem P71_mem : P71 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 71) = P71 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P71, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨71, rfl⟩

theorem P72_mem : P72 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 72) = P72 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P72, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨72, rfl⟩

theorem P73_mem : P73 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 73) = P73 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P73, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨73, rfl⟩

theorem P74_mem : P74 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 74) = P74 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P74, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨74, rfl⟩

theorem P75_mem : P75 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 75) = P75 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P75, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨75, rfl⟩

theorem P76_mem : P76 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 76) = P76 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P76, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨76, rfl⟩

theorem P77_mem : P77 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 77) = P77 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P77, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨77, rfl⟩

theorem P78_mem : P78 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 78) = P78 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P78, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨78, rfl⟩

theorem P79_mem : P79 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 79) = P79 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P79, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨79, rfl⟩

theorem P80_mem : P80 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 80) = P80 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P80, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨80, rfl⟩

theorem P81_mem : P81 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 81) = P81 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P81, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨81, rfl⟩

theorem P82_mem : P82 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 82) = P82 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P82, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨82, rfl⟩

theorem P83_mem : P83 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 83) = P83 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P83, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨83, rfl⟩

theorem P84_mem : P84 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 84) = P84 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P84, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨84, rfl⟩

theorem P85_mem : P85 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 85) = P85 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P85, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨85, rfl⟩

theorem P86_mem : P86 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 86) = P86 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P86, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨86, rfl⟩

theorem P87_mem : P87 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 87) = P87 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P87, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨87, rfl⟩

theorem P88_mem : P88 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 88) = P88 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P88, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨88, rfl⟩

theorem P89_mem : P89 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 89) = P89 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P89, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨89, rfl⟩

theorem P90_mem : P90 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 90) = P90 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P90, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨90, rfl⟩

theorem P91_mem : P91 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 91) = P91 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P91, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨91, rfl⟩

theorem P92_mem : P92 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 92) = P92 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P92, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨92, rfl⟩

theorem P93_mem : P93 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 93) = P93 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P93, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨93, rfl⟩

theorem P94_mem : P94 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 94) = P94 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P94, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨94, rfl⟩

theorem P95_mem : P95 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 95) = P95 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P95, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨95, rfl⟩

theorem P96_mem : P96 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 96) = P96 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P96, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨96, rfl⟩

theorem P97_mem : P97 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 97) = P97 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P97, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨97, rfl⟩

theorem P98_mem : P98 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 98) = P98 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P98, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨98, rfl⟩

theorem P99_mem : P99 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 99) = P99 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P99, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨99, rfl⟩

theorem P100_mem : P100 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 100) = P100 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P100, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨100, rfl⟩

theorem P101_mem : P101 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 101) = P101 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P101, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨101, rfl⟩

theorem P102_mem : P102 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 102) = P102 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P102, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨102, rfl⟩

theorem P103_mem : P103 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 103) = P103 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P103, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨103, rfl⟩

theorem P104_mem : P104 ∈ quadraticIdeal rel := by
  have h : quadraticRelation (rel 104) = P104 := by
    rw [rel, A2.quadraticRelation_entryMatrix]
    simp [relTable, P104, smul_eq_C_mul, map_neg, map_ofNat, map_one] <;> ring
  rw [← h]
  exact Ideal.subset_span ⟨104, rfl⟩

set_option maxRecDepth 100000 in
theorem u3_0 : X 0 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 0 * Qd) = (-8 : MvPolynomial (Fin 28) ℂ) * X 26 * P8 + (8 : MvPolynomial (Fin 28) ℂ) * X 26 * P11 + (32 : MvPolynomial (Fin 28) ℂ) * X 23 * P12 + (32 : MvPolynomial (Fin 28) ℂ) * X 24 * P13 + (40 : MvPolynomial (Fin 28) ℂ) * X 23 * P15 + (-8 : MvPolynomial (Fin 28) ℂ) * X 24 * P16 + (24 : MvPolynomial (Fin 28) ℂ) * X 25 * P17 + (-4 : MvPolynomial (Fin 28) ℂ) * X 23 * P18 + (-24 : MvPolynomial (Fin 28) ℂ) * X 24 * P19 + (-24 : MvPolynomial (Fin 28) ℂ) * X 25 * P20 + (-32 : MvPolynomial (Fin 28) ℂ) * X 20 * P21 + (-24 : MvPolynomial (Fin 28) ℂ) * X 20 * P25 + (-24 : MvPolynomial (Fin 28) ℂ) * X 21 * P26 + (-40 : MvPolynomial (Fin 28) ℂ) * X 22 * P28 + (-4 : MvPolynomial (Fin 28) ℂ) * X 20 * P30 + (12 : MvPolynomial (Fin 28) ℂ) * X 21 * P31 + (40 : MvPolynomial (Fin 28) ℂ) * X 22 * P32 + (16 : MvPolynomial (Fin 28) ℂ) * X 16 * P33 + (32 : MvPolynomial (Fin 28) ℂ) * X 18 * P34 + (-32 : MvPolynomial (Fin 28) ℂ) * X 17 * P35 + (64 : MvPolynomial (Fin 28) ℂ) * X 19 * P36 + (24 : MvPolynomial (Fin 28) ℂ) * X 18 * P38 + (16 : MvPolynomial (Fin 28) ℂ) * X 19 * P40 + (16 : MvPolynomial (Fin 28) ℂ) * X 16 * P41 + (8 : MvPolynomial (Fin 28) ℂ) * X 17 * P42 + (36 : MvPolynomial (Fin 28) ℂ) * X 18 * P43 + (32 : MvPolynomial (Fin 28) ℂ) * X 19 * P44 + (20 : MvPolynomial (Fin 28) ℂ) * X 0 * P45 + (16 : MvPolynomial (Fin 28) ℂ) * X 1 * P45 + (-16 : MvPolynomial (Fin 28) ℂ) * X 2 * P45 + (-24 : MvPolynomial (Fin 28) ℂ) * X 0 * P46 + (-32 : MvPolynomial (Fin 28) ℂ) * X 1 * P46 + (16 : MvPolynomial (Fin 28) ℂ) * X 2 * P46 + (-16 : MvPolynomial (Fin 28) ℂ) * X 3 * P46 + (-12 : MvPolynomial (Fin 28) ℂ) * X 0 * P48 + (-8 : MvPolynomial (Fin 28) ℂ) * X 2 * P48 + (-20 : MvPolynomial (Fin 28) ℂ) * X 0 * P51 + (-16 : MvPolynomial (Fin 28) ℂ) * X 1 * P51 + (-8 : MvPolynomial (Fin 28) ℂ) * X 2 * P51 + (-16 : MvPolynomial (Fin 28) ℂ) * X 3 * P51 + (8 : MvPolynomial (Fin 28) ℂ) * X 0 * P52 + (16 : MvPolynomial (Fin 28) ℂ) * X 3 * P52 + (12 : MvPolynomial (Fin 28) ℂ) * X 0 * P53 + (-24 : MvPolynomial (Fin 28) ℂ) * X 3 * P53 + (-5 : MvPolynomial (Fin 28) ℂ) * X 0 * P56 + (-8 : MvPolynomial (Fin 28) ℂ) * X 1 * P56 + (-10 : MvPolynomial (Fin 28) ℂ) * X 2 * P56 + (-10 : MvPolynomial (Fin 28) ℂ) * X 3 * P56 + (-4 : MvPolynomial (Fin 28) ℂ) * X 0 * P58 + (-16 : MvPolynomial (Fin 28) ℂ) * X 1 * P58 + (8 : MvPolynomial (Fin 28) ℂ) * X 2 * P58 + (-4 : MvPolynomial (Fin 28) ℂ) * X 0 * P59 + (16 : MvPolynomial (Fin 28) ℂ) * X 1 * P59 + (-8 : MvPolynomial (Fin 28) ℂ) * X 4 * P61 := by
    simp only [Qd, P8, P11, P12, P13, P15, P16, P17, P18, P19, P20, P21, P25, P26, P28, P30, P31, P32, P33, P34, P35, P36, P38, P40, P41, P42, P43, P44, P45, P46, P48, P51, P52, P53, P56, P58, P59, P61]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P8_mem) (Ideal.mul_mem_left _ _ P11_mem)) (Ideal.mul_mem_left _ _ P12_mem)) (Ideal.mul_mem_left _ _ P13_mem)) (Ideal.mul_mem_left _ _ P15_mem)) (Ideal.mul_mem_left _ _ P16_mem)) (Ideal.mul_mem_left _ _ P17_mem)) (Ideal.mul_mem_left _ _ P18_mem)) (Ideal.mul_mem_left _ _ P19_mem)) (Ideal.mul_mem_left _ _ P20_mem)) (Ideal.mul_mem_left _ _ P21_mem)) (Ideal.mul_mem_left _ _ P25_mem)) (Ideal.mul_mem_left _ _ P26_mem)) (Ideal.mul_mem_left _ _ P28_mem)) (Ideal.mul_mem_left _ _ P30_mem)) (Ideal.mul_mem_left _ _ P31_mem)) (Ideal.mul_mem_left _ _ P32_mem)) (Ideal.mul_mem_left _ _ P33_mem)) (Ideal.mul_mem_left _ _ P34_mem)) (Ideal.mul_mem_left _ _ P35_mem)) (Ideal.mul_mem_left _ _ P36_mem)) (Ideal.mul_mem_left _ _ P38_mem)) (Ideal.mul_mem_left _ _ P40_mem)) (Ideal.mul_mem_left _ _ P41_mem)) (Ideal.mul_mem_left _ _ P42_mem)) (Ideal.mul_mem_left _ _ P43_mem)) (Ideal.mul_mem_left _ _ P44_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P58_mem)) (Ideal.mul_mem_left _ _ P58_mem)) (Ideal.mul_mem_left _ _ P58_mem)) (Ideal.mul_mem_left _ _ P59_mem)) (Ideal.mul_mem_left _ _ P59_mem)) (Ideal.mul_mem_left _ _ P61_mem))

set_option maxRecDepth 100000 in
theorem u3_1 : X 1 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 1 * Qd) = (16 : MvPolynomial (Fin 28) ℂ) * X 26 * P8 + (-16 : MvPolynomial (Fin 28) ℂ) * X 26 * P11 + (-16 : MvPolynomial (Fin 28) ℂ) * X 23 * P12 + (-32 : MvPolynomial (Fin 28) ℂ) * X 24 * P13 + (-32 : MvPolynomial (Fin 28) ℂ) * X 23 * P15 + (16 : MvPolynomial (Fin 28) ℂ) * X 24 * P16 + (-16 : MvPolynomial (Fin 28) ℂ) * X 25 * P17 + (8 : MvPolynomial (Fin 28) ℂ) * X 23 * P18 + (16 : MvPolynomial (Fin 28) ℂ) * X 24 * P19 + (16 : MvPolynomial (Fin 28) ℂ) * X 25 * P20 + (32 : MvPolynomial (Fin 28) ℂ) * X 20 * P21 + (16 : MvPolynomial (Fin 28) ℂ) * X 21 * P26 + (32 : MvPolynomial (Fin 28) ℂ) * X 22 * P28 + (-8 : MvPolynomial (Fin 28) ℂ) * X 21 * P31 + (-32 : MvPolynomial (Fin 28) ℂ) * X 22 * P32 + (-16 : MvPolynomial (Fin 28) ℂ) * X 16 * P33 + (-16 : MvPolynomial (Fin 28) ℂ) * X 18 * P34 + (16 : MvPolynomial (Fin 28) ℂ) * X 17 * P35 + (-32 : MvPolynomial (Fin 28) ℂ) * X 19 * P36 + (16 : MvPolynomial (Fin 28) ℂ) * X 17 * P39 + (-8 : MvPolynomial (Fin 28) ℂ) * X 19 * P40 + (-12 : MvPolynomial (Fin 28) ℂ) * X 16 * P41 + (-8 : MvPolynomial (Fin 28) ℂ) * X 17 * P42 + (-24 : MvPolynomial (Fin 28) ℂ) * X 18 * P43 + (-16 : MvPolynomial (Fin 28) ℂ) * X 19 * P44 + (-16 : MvPolynomial (Fin 28) ℂ) * X 0 * P45 + (-20 : MvPolynomial (Fin 28) ℂ) * X 1 * P45 + (8 : MvPolynomial (Fin 28) ℂ) * X 2 * P45 + (24 : MvPolynomial (Fin 28) ℂ) * X 0 * P46 + (40 : MvPolynomial (Fin 28) ℂ) * X 1 * P46 + (24 : MvPolynomial (Fin 28) ℂ) * X 3 * P46 + (-12 : MvPolynomial (Fin 28) ℂ) * X 1 * P48 + (-8 : MvPolynomial (Fin 28) ℂ) * X 3 * P48 + (16 : MvPolynomial (Fin 28) ℂ) * X 0 * P51 + (20 : MvPolynomial (Fin 28) ℂ) * X 1 * P51 + (8 : MvPolynomial (Fin 28) ℂ) * X 2 * P51 + (16 : MvPolynomial (Fin 28) ℂ) * X 3 * P51 + (-16 : MvPolynomial (Fin 28) ℂ) * X 0 * P52 + (-24 : MvPolynomial (Fin 28) ℂ) * X 1 * P52 + (-8 : MvPolynomial (Fin 28) ℂ) * X 2 * P52 + (-24 : MvPolynomial (Fin 28) ℂ) * X 3 * P52 + (12 : MvPolynomial (Fin 28) ℂ) * X 1 * P53 + (24 : MvPolynomial (Fin 28) ℂ) * X 3 * P53 + (4 : MvPolynomial (Fin 28) ℂ) * X 0 * P56 + (7 : MvPolynomial (Fin 28) ℂ) * X 1 * P56 + (8 : MvPolynomial (Fin 28) ℂ) * X 2 * P56 + (8 : MvPolynomial (Fin 28) ℂ) * X 3 * P56 + (4 : MvPolynomial (Fin 28) ℂ) * X 0 * P58 + (12 : MvPolynomial (Fin 28) ℂ) * X 1 * P58 + (-4 : MvPolynomial (Fin 28) ℂ) * X 2 * P58 + (-12 : MvPolynomial (Fin 28) ℂ) * X 1 * P59 + (16 : MvPolynomial (Fin 28) ℂ) * X 4 * P61 := by
    simp only [Qd, P8, P11, P12, P13, P15, P16, P17, P18, P19, P20, P21, P26, P28, P31, P32, P33, P34, P35, P36, P39, P40, P41, P42, P43, P44, P45, P46, P48, P51, P52, P53, P56, P58, P59, P61]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P8_mem) (Ideal.mul_mem_left _ _ P11_mem)) (Ideal.mul_mem_left _ _ P12_mem)) (Ideal.mul_mem_left _ _ P13_mem)) (Ideal.mul_mem_left _ _ P15_mem)) (Ideal.mul_mem_left _ _ P16_mem)) (Ideal.mul_mem_left _ _ P17_mem)) (Ideal.mul_mem_left _ _ P18_mem)) (Ideal.mul_mem_left _ _ P19_mem)) (Ideal.mul_mem_left _ _ P20_mem)) (Ideal.mul_mem_left _ _ P21_mem)) (Ideal.mul_mem_left _ _ P26_mem)) (Ideal.mul_mem_left _ _ P28_mem)) (Ideal.mul_mem_left _ _ P31_mem)) (Ideal.mul_mem_left _ _ P32_mem)) (Ideal.mul_mem_left _ _ P33_mem)) (Ideal.mul_mem_left _ _ P34_mem)) (Ideal.mul_mem_left _ _ P35_mem)) (Ideal.mul_mem_left _ _ P36_mem)) (Ideal.mul_mem_left _ _ P39_mem)) (Ideal.mul_mem_left _ _ P40_mem)) (Ideal.mul_mem_left _ _ P41_mem)) (Ideal.mul_mem_left _ _ P42_mem)) (Ideal.mul_mem_left _ _ P43_mem)) (Ideal.mul_mem_left _ _ P44_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P58_mem)) (Ideal.mul_mem_left _ _ P58_mem)) (Ideal.mul_mem_left _ _ P58_mem)) (Ideal.mul_mem_left _ _ P59_mem)) (Ideal.mul_mem_left _ _ P61_mem))

set_option maxRecDepth 100000 in
theorem u3_2 : X 2 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 2 * Qd) = (-8 : MvPolynomial (Fin 28) ℂ) * X 26 * P8 + (8 : MvPolynomial (Fin 28) ℂ) * X 26 * P11 + (-8 : MvPolynomial (Fin 28) ℂ) * X 23 * P12 + (16 : MvPolynomial (Fin 28) ℂ) * X 24 * P13 + (-8 : MvPolynomial (Fin 28) ℂ) * X 24 * P16 + (-4 : MvPolynomial (Fin 28) ℂ) * X 23 * P18 + (-8 : MvPolynomial (Fin 28) ℂ) * X 24 * P19 + (-8 : MvPolynomial (Fin 28) ℂ) * X 20 * P21 + (-8 : MvPolynomial (Fin 28) ℂ) * X 21 * P22 + (16 : MvPolynomial (Fin 28) ℂ) * X 22 * P23 + (16 : MvPolynomial (Fin 28) ℂ) * X 20 * P25 + (-8 : MvPolynomial (Fin 28) ℂ) * X 21 * P26 + (-16 : MvPolynomial (Fin 28) ℂ) * X 22 * P28 + (4 : MvPolynomial (Fin 28) ℂ) * X 20 * P30 + (16 : MvPolynomial (Fin 28) ℂ) * X 16 * P33 + (8 : MvPolynomial (Fin 28) ℂ) * X 18 * P34 + (-16 : MvPolynomial (Fin 28) ℂ) * X 19 * P36 + (-24 : MvPolynomial (Fin 28) ℂ) * X 18 * P38 + (-32 : MvPolynomial (Fin 28) ℂ) * X 17 * P39 + (4 : MvPolynomial (Fin 28) ℂ) * X 16 * P41 + (8 : MvPolynomial (Fin 28) ℂ) * X 0 * P45 + (16 : MvPolynomial (Fin 28) ℂ) * X 1 * P45 + (8 : MvPolynomial (Fin 28) ℂ) * X 2 * P45 + (-16 : MvPolynomial (Fin 28) ℂ) * X 0 * P46 + (-32 : MvPolynomial (Fin 28) ℂ) * X 1 * P46 + (-16 : MvPolynomial (Fin 28) ℂ) * X 2 * P46 + (-16 : MvPolynomial (Fin 28) ℂ) * X 3 * P46 + (16 : MvPolynomial (Fin 28) ℂ) * X 0 * P48 + (24 : MvPolynomial (Fin 28) ℂ) * X 1 * P48 + (12 : MvPolynomial (Fin 28) ℂ) * X 2 * P48 + (12 : MvPolynomial (Fin 28) ℂ) * X 3 * P48 + (-8 : MvPolynomial (Fin 28) ℂ) * X 0 * P51 + (-16 : MvPolynomial (Fin 28) ℂ) * X 1 * P51 + (-4 : MvPolynomial (Fin 28) ℂ) * X 2 * P51 + (-8 : MvPolynomial (Fin 28) ℂ) * X 3 * P51 + (16 : MvPolynomial (Fin 28) ℂ) * X 0 * P52 + (32 : MvPolynomial (Fin 28) ℂ) * X 1 * P52 + (8 : MvPolynomial (Fin 28) ℂ) * X 2 * P52 + (16 : MvPolynomial (Fin 28) ℂ) * X 3 * P52 + (-12 : MvPolynomial (Fin 28) ℂ) * X 0 * P53 + (-16 : MvPolynomial (Fin 28) ℂ) * X 1 * P53 + (4 : MvPolynomial (Fin 28) ℂ) * X 2 * P53 + (-12 : MvPolynomial (Fin 28) ℂ) * X 3 * P53 + (-1 : MvPolynomial (Fin 28) ℂ) * X 0 * P56 + (-2 : MvPolynomial (Fin 28) ℂ) * X 1 * P56 + (-1 : MvPolynomial (Fin 28) ℂ) * X 2 * P56 + (-2 : MvPolynomial (Fin 28) ℂ) * X 3 * P56 + (-8 : MvPolynomial (Fin 28) ℂ) * X 4 * P61 := by
    simp only [Qd, P8, P11, P12, P13, P16, P18, P19, P21, P22, P23, P25, P26, P28, P30, P33, P34, P36, P38, P39, P41, P45, P46, P48, P51, P52, P53, P56, P61]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P8_mem) (Ideal.mul_mem_left _ _ P11_mem)) (Ideal.mul_mem_left _ _ P12_mem)) (Ideal.mul_mem_left _ _ P13_mem)) (Ideal.mul_mem_left _ _ P16_mem)) (Ideal.mul_mem_left _ _ P18_mem)) (Ideal.mul_mem_left _ _ P19_mem)) (Ideal.mul_mem_left _ _ P21_mem)) (Ideal.mul_mem_left _ _ P22_mem)) (Ideal.mul_mem_left _ _ P23_mem)) (Ideal.mul_mem_left _ _ P25_mem)) (Ideal.mul_mem_left _ _ P26_mem)) (Ideal.mul_mem_left _ _ P28_mem)) (Ideal.mul_mem_left _ _ P30_mem)) (Ideal.mul_mem_left _ _ P33_mem)) (Ideal.mul_mem_left _ _ P34_mem)) (Ideal.mul_mem_left _ _ P36_mem)) (Ideal.mul_mem_left _ _ P38_mem)) (Ideal.mul_mem_left _ _ P39_mem)) (Ideal.mul_mem_left _ _ P41_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P61_mem))

set_option maxRecDepth 100000 in
theorem u3_3 : X 3 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 3 * Qd) = (-8 : MvPolynomial (Fin 28) ℂ) * X 26 * P8 + (8 : MvPolynomial (Fin 28) ℂ) * X 26 * P11 + (-8 : MvPolynomial (Fin 28) ℂ) * X 23 * P12 + (8 : MvPolynomial (Fin 28) ℂ) * X 24 * P13 + (-8 : MvPolynomial (Fin 28) ℂ) * X 24 * P16 + (8 : MvPolynomial (Fin 28) ℂ) * X 25 * P17 + (-4 : MvPolynomial (Fin 28) ℂ) * X 23 * P18 + (-8 : MvPolynomial (Fin 28) ℂ) * X 25 * P20 + (-16 : MvPolynomial (Fin 28) ℂ) * X 20 * P21 + (8 : MvPolynomial (Fin 28) ℂ) * X 21 * P22 + (-8 : MvPolynomial (Fin 28) ℂ) * X 22 * P23 + (8 : MvPolynomial (Fin 28) ℂ) * X 22 * P28 + (4 : MvPolynomial (Fin 28) ℂ) * X 21 * P31 + (-16 : MvPolynomial (Fin 28) ℂ) * X 16 * P33 + (-16 : MvPolynomial (Fin 28) ℂ) * X 18 * P34 + (-8 : MvPolynomial (Fin 28) ℂ) * X 19 * P40 + (4 : MvPolynomial (Fin 28) ℂ) * X 17 * P42 + (-4 : MvPolynomial (Fin 28) ℂ) * X 0 * P45 + (-4 : MvPolynomial (Fin 28) ℂ) * X 2 * P45 + (4 : MvPolynomial (Fin 28) ℂ) * X 3 * P45 + (-8 : MvPolynomial (Fin 28) ℂ) * X 3 * P46 + (4 : MvPolynomial (Fin 28) ℂ) * X 3 * P48 + (8 : MvPolynomial (Fin 28) ℂ) * X 0 * P51 + (8 : MvPolynomial (Fin 28) ℂ) * X 1 * P51 + (4 : MvPolynomial (Fin 28) ℂ) * X 2 * P51 + (4 : MvPolynomial (Fin 28) ℂ) * X 3 * P51 + (-1 : MvPolynomial (Fin 28) ℂ) * X 0 * P56 + (-2 : MvPolynomial (Fin 28) ℂ) * X 1 * P56 + (-2 : MvPolynomial (Fin 28) ℂ) * X 2 * P56 + (-1 : MvPolynomial (Fin 28) ℂ) * X 3 * P56 + (-8 : MvPolynomial (Fin 28) ℂ) * X 4 * P61 := by
    simp only [Qd, P8, P11, P12, P13, P16, P17, P18, P20, P21, P22, P23, P28, P31, P33, P34, P40, P42, P45, P46, P48, P51, P56, P61]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P8_mem) (Ideal.mul_mem_left _ _ P11_mem)) (Ideal.mul_mem_left _ _ P12_mem)) (Ideal.mul_mem_left _ _ P13_mem)) (Ideal.mul_mem_left _ _ P16_mem)) (Ideal.mul_mem_left _ _ P17_mem)) (Ideal.mul_mem_left _ _ P18_mem)) (Ideal.mul_mem_left _ _ P20_mem)) (Ideal.mul_mem_left _ _ P21_mem)) (Ideal.mul_mem_left _ _ P22_mem)) (Ideal.mul_mem_left _ _ P23_mem)) (Ideal.mul_mem_left _ _ P28_mem)) (Ideal.mul_mem_left _ _ P31_mem)) (Ideal.mul_mem_left _ _ P33_mem)) (Ideal.mul_mem_left _ _ P34_mem)) (Ideal.mul_mem_left _ _ P40_mem)) (Ideal.mul_mem_left _ _ P42_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P61_mem))

set_option maxRecDepth 100000 in
theorem u3_4 : X 4 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 4 * Qd) = (-8 : MvPolynomial (Fin 28) ℂ) * X 25 * P8 + (8 : MvPolynomial (Fin 28) ℂ) * X 25 * P11 + (-8 : MvPolynomial (Fin 28) ℂ) * X 21 * P12 + (8 : MvPolynomial (Fin 28) ℂ) * X 22 * P13 + (-8 : MvPolynomial (Fin 28) ℂ) * X 22 * P16 + (-4 : MvPolynomial (Fin 28) ℂ) * X 21 * P18 + (16 : MvPolynomial (Fin 28) ℂ) * X 18 * P21 + (8 : MvPolynomial (Fin 28) ℂ) * X 19 * P27 + (-4 : MvPolynomial (Fin 28) ℂ) * X 17 * P29 + (4 : MvPolynomial (Fin 28) ℂ) * X 0 * P33 + (4 : MvPolynomial (Fin 28) ℂ) * X 2 * P33 + (8 : MvPolynomial (Fin 28) ℂ) * X 3 * P33 + (-8 : MvPolynomial (Fin 28) ℂ) * X 0 * P37 + (-8 : MvPolynomial (Fin 28) ℂ) * X 1 * P37 + (-4 : MvPolynomial (Fin 28) ℂ) * X 2 * P37 + (-4 : MvPolynomial (Fin 28) ℂ) * X 3 * P37 + (1 : MvPolynomial (Fin 28) ℂ) * X 0 * P41 + (2 : MvPolynomial (Fin 28) ℂ) * X 1 * P41 + (2 : MvPolynomial (Fin 28) ℂ) * X 2 * P41 + (1 : MvPolynomial (Fin 28) ℂ) * X 3 * P41 + (12 : MvPolynomial (Fin 28) ℂ) * X 4 * P45 + (-8 : MvPolynomial (Fin 28) ℂ) * X 4 * P46 + (4 : MvPolynomial (Fin 28) ℂ) * X 4 * P48 := by
    simp only [Qd, P8, P11, P12, P13, P16, P18, P21, P27, P29, P33, P37, P41, P45, P46, P48]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P8_mem) (Ideal.mul_mem_left _ _ P11_mem)) (Ideal.mul_mem_left _ _ P12_mem)) (Ideal.mul_mem_left _ _ P13_mem)) (Ideal.mul_mem_left _ _ P16_mem)) (Ideal.mul_mem_left _ _ P18_mem)) (Ideal.mul_mem_left _ _ P21_mem)) (Ideal.mul_mem_left _ _ P27_mem)) (Ideal.mul_mem_left _ _ P29_mem)) (Ideal.mul_mem_left _ _ P33_mem)) (Ideal.mul_mem_left _ _ P33_mem)) (Ideal.mul_mem_left _ _ P33_mem)) (Ideal.mul_mem_left _ _ P37_mem)) (Ideal.mul_mem_left _ _ P37_mem)) (Ideal.mul_mem_left _ _ P37_mem)) (Ideal.mul_mem_left _ _ P37_mem)) (Ideal.mul_mem_left _ _ P41_mem)) (Ideal.mul_mem_left _ _ P41_mem)) (Ideal.mul_mem_left _ _ P41_mem)) (Ideal.mul_mem_left _ _ P41_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem))

set_option maxRecDepth 100000 in
theorem u3_5 : X 5 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 5 * Qd) = (-8 : MvPolynomial (Fin 28) ℂ) * X 24 * P6 + (8 : MvPolynomial (Fin 28) ℂ) * X 24 * P11 + (-8 : MvPolynomial (Fin 28) ℂ) * X 22 * P14 + (-8 : MvPolynomial (Fin 28) ℂ) * X 20 * P15 + (8 : MvPolynomial (Fin 28) ℂ) * X 22 * P17 + (-4 : MvPolynomial (Fin 28) ℂ) * X 20 * P18 + (8 : MvPolynomial (Fin 28) ℂ) * X 19 * P24 + (16 : MvPolynomial (Fin 28) ℂ) * X 18 * P26 + (-4 : MvPolynomial (Fin 28) ℂ) * X 16 * P29 + (-8 : MvPolynomial (Fin 28) ℂ) * X 0 * P35 + (-8 : MvPolynomial (Fin 28) ℂ) * X 1 * P35 + (-4 : MvPolynomial (Fin 28) ℂ) * X 2 * P35 + (-4 : MvPolynomial (Fin 28) ℂ) * X 3 * P35 + (4 : MvPolynomial (Fin 28) ℂ) * X 0 * P39 + (8 : MvPolynomial (Fin 28) ℂ) * X 2 * P39 + (4 : MvPolynomial (Fin 28) ℂ) * X 3 * P39 + (1 : MvPolynomial (Fin 28) ℂ) * X 0 * P42 + (2 : MvPolynomial (Fin 28) ℂ) * X 1 * P42 + (1 : MvPolynomial (Fin 28) ℂ) * X 2 * P42 + (2 : MvPolynomial (Fin 28) ℂ) * X 3 * P42 + (4 : MvPolynomial (Fin 28) ℂ) * X 5 * P51 + (-8 : MvPolynomial (Fin 28) ℂ) * X 5 * P52 + (12 : MvPolynomial (Fin 28) ℂ) * X 5 * P53 := by
    simp only [Qd, P6, P11, P14, P15, P17, P18, P24, P26, P29, P35, P39, P42, P51, P52, P53]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P6_mem) (Ideal.mul_mem_left _ _ P11_mem)) (Ideal.mul_mem_left _ _ P14_mem)) (Ideal.mul_mem_left _ _ P15_mem)) (Ideal.mul_mem_left _ _ P17_mem)) (Ideal.mul_mem_left _ _ P18_mem)) (Ideal.mul_mem_left _ _ P24_mem)) (Ideal.mul_mem_left _ _ P26_mem)) (Ideal.mul_mem_left _ _ P29_mem)) (Ideal.mul_mem_left _ _ P35_mem)) (Ideal.mul_mem_left _ _ P35_mem)) (Ideal.mul_mem_left _ _ P35_mem)) (Ideal.mul_mem_left _ _ P35_mem)) (Ideal.mul_mem_left _ _ P39_mem)) (Ideal.mul_mem_left _ _ P39_mem)) (Ideal.mul_mem_left _ _ P39_mem)) (Ideal.mul_mem_left _ _ P42_mem)) (Ideal.mul_mem_left _ _ P42_mem)) (Ideal.mul_mem_left _ _ P42_mem)) (Ideal.mul_mem_left _ _ P42_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P53_mem))

set_option maxRecDepth 100000 in
theorem u3_6 : X 6 * Qd ∈ quadraticIdeal rel := by
  have h : ((2 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 6 * Qd) = (-4 : MvPolynomial (Fin 28) ℂ) * X 26 * P4 + (4 : MvPolynomial (Fin 28) ℂ) * X 26 * P5 + (-4 : MvPolynomial (Fin 28) ℂ) * X 24 * P9 + (-4 : MvPolynomial (Fin 28) ℂ) * X 23 * P10 + (-8 : MvPolynomial (Fin 28) ℂ) * X 19 * P23 + (-4 : MvPolynomial (Fin 28) ℂ) * X 16 * P25 + (-2 : MvPolynomial (Fin 28) ℂ) * X 16 * P30 + (4 : MvPolynomial (Fin 28) ℂ) * X 17 * P31 + (-8 : MvPolynomial (Fin 28) ℂ) * X 1 * P34 + (-4 : MvPolynomial (Fin 28) ℂ) * X 2 * P34 + (-4 : MvPolynomial (Fin 28) ℂ) * X 3 * P34 + (2 : MvPolynomial (Fin 28) ℂ) * X 0 * P38 + (4 : MvPolynomial (Fin 28) ℂ) * X 1 * P38 + (2 : MvPolynomial (Fin 28) ℂ) * X 2 * P38 + (4 : MvPolynomial (Fin 28) ℂ) * X 3 * P38 + (-1 : MvPolynomial (Fin 28) ℂ) * X 0 * P43 + (-2 : MvPolynomial (Fin 28) ℂ) * X 1 * P43 + (-3 : MvPolynomial (Fin 28) ℂ) * X 2 * P43 + (-2 : MvPolynomial (Fin 28) ℂ) * X 6 * P45 + (-4 : MvPolynomial (Fin 28) ℂ) * X 6 * P46 + (2 : MvPolynomial (Fin 28) ℂ) * X 6 * P48 + (4 : MvPolynomial (Fin 28) ℂ) * X 8 * P61 := by
    simp only [Qd, P4, P5, P9, P10, P23, P25, P30, P31, P34, P38, P43, P45, P46, P48, P61]
    ring
  apply mem_of_natCast_mul 2 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P4_mem) (Ideal.mul_mem_left _ _ P5_mem)) (Ideal.mul_mem_left _ _ P9_mem)) (Ideal.mul_mem_left _ _ P10_mem)) (Ideal.mul_mem_left _ _ P23_mem)) (Ideal.mul_mem_left _ _ P25_mem)) (Ideal.mul_mem_left _ _ P30_mem)) (Ideal.mul_mem_left _ _ P31_mem)) (Ideal.mul_mem_left _ _ P34_mem)) (Ideal.mul_mem_left _ _ P34_mem)) (Ideal.mul_mem_left _ _ P34_mem)) (Ideal.mul_mem_left _ _ P38_mem)) (Ideal.mul_mem_left _ _ P38_mem)) (Ideal.mul_mem_left _ _ P38_mem)) (Ideal.mul_mem_left _ _ P38_mem)) (Ideal.mul_mem_left _ _ P43_mem)) (Ideal.mul_mem_left _ _ P43_mem)) (Ideal.mul_mem_left _ _ P43_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P61_mem))

set_option maxRecDepth 100000 in
theorem u3_7 : X 7 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 7 * Qd) = (8 : MvPolynomial (Fin 28) ℂ) * X 23 * P6 + (8 : MvPolynomial (Fin 28) ℂ) * X 23 * P8 + (8 : MvPolynomial (Fin 28) ℂ) * X 21 * P14 + (8 : MvPolynomial (Fin 28) ℂ) * X 20 * P16 + (8 : MvPolynomial (Fin 28) ℂ) * X 20 * P19 + (8 : MvPolynomial (Fin 28) ℂ) * X 21 * P20 + (8 : MvPolynomial (Fin 28) ℂ) * X 17 * P24 + (8 : MvPolynomial (Fin 28) ℂ) * X 16 * P27 + (-16 : MvPolynomial (Fin 28) ℂ) * X 18 * P32 + (-4 : MvPolynomial (Fin 28) ℂ) * X 0 * P36 + (-8 : MvPolynomial (Fin 28) ℂ) * X 1 * P36 + (-8 : MvPolynomial (Fin 28) ℂ) * X 2 * P36 + (-4 : MvPolynomial (Fin 28) ℂ) * X 3 * P36 + (-2 : MvPolynomial (Fin 28) ℂ) * X 0 * P40 + (-4 : MvPolynomial (Fin 28) ℂ) * X 1 * P40 + (-2 : MvPolynomial (Fin 28) ℂ) * X 2 * P40 + (-4 : MvPolynomial (Fin 28) ℂ) * X 3 * P40 + (-8 : MvPolynomial (Fin 28) ℂ) * X 0 * P44 + (-4 : MvPolynomial (Fin 28) ℂ) * X 2 * P44 + (-4 : MvPolynomial (Fin 28) ℂ) * X 3 * P44 + (-1 : MvPolynomial (Fin 28) ℂ) * X 7 * P56 + (4 : MvPolynomial (Fin 28) ℂ) * X 7 * P58 + (-12 : MvPolynomial (Fin 28) ℂ) * X 7 * P59 := by
    simp only [Qd, P6, P8, P14, P16, P19, P20, P24, P27, P32, P36, P40, P44, P56, P58, P59]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P6_mem) (Ideal.mul_mem_left _ _ P8_mem)) (Ideal.mul_mem_left _ _ P14_mem)) (Ideal.mul_mem_left _ _ P16_mem)) (Ideal.mul_mem_left _ _ P19_mem)) (Ideal.mul_mem_left _ _ P20_mem)) (Ideal.mul_mem_left _ _ P24_mem)) (Ideal.mul_mem_left _ _ P27_mem)) (Ideal.mul_mem_left _ _ P32_mem)) (Ideal.mul_mem_left _ _ P36_mem)) (Ideal.mul_mem_left _ _ P36_mem)) (Ideal.mul_mem_left _ _ P36_mem)) (Ideal.mul_mem_left _ _ P36_mem)) (Ideal.mul_mem_left _ _ P40_mem)) (Ideal.mul_mem_left _ _ P40_mem)) (Ideal.mul_mem_left _ _ P40_mem)) (Ideal.mul_mem_left _ _ P40_mem)) (Ideal.mul_mem_left _ _ P44_mem)) (Ideal.mul_mem_left _ _ P44_mem)) (Ideal.mul_mem_left _ _ P44_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P58_mem)) (Ideal.mul_mem_left _ _ P59_mem))

set_option maxRecDepth 100000 in
theorem u3_8 : X 8 * Qd ∈ quadraticIdeal rel := by
  have h : ((2 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 8 * Qd) = (4 : MvPolynomial (Fin 28) ℂ) * X 25 * P4 + (-4 : MvPolynomial (Fin 28) ℂ) * X 25 * P5 + (4 : MvPolynomial (Fin 28) ℂ) * X 22 * P9 + (4 : MvPolynomial (Fin 28) ℂ) * X 21 * P10 + (-4 : MvPolynomial (Fin 28) ℂ) * X 17 * P12 + (-4 : MvPolynomial (Fin 28) ℂ) * X 19 * P13 + (-4 : MvPolynomial (Fin 28) ℂ) * X 19 * P16 + (2 : MvPolynomial (Fin 28) ℂ) * X 17 * P18 + (-2 : MvPolynomial (Fin 28) ℂ) * X 0 * P21 + (-8 : MvPolynomial (Fin 28) ℂ) * X 1 * P21 + (-2 : MvPolynomial (Fin 28) ℂ) * X 2 * P21 + (-4 : MvPolynomial (Fin 28) ℂ) * X 3 * P21 + (4 : MvPolynomial (Fin 28) ℂ) * X 0 * P25 + (4 : MvPolynomial (Fin 28) ℂ) * X 1 * P25 + (2 : MvPolynomial (Fin 28) ℂ) * X 2 * P25 + (2 : MvPolynomial (Fin 28) ℂ) * X 3 * P25 + (-1 : MvPolynomial (Fin 28) ℂ) * X 0 * P30 + (-2 : MvPolynomial (Fin 28) ℂ) * X 1 * P30 + (-2 : MvPolynomial (Fin 28) ℂ) * X 2 * P30 + (-1 : MvPolynomial (Fin 28) ℂ) * X 3 * P30 + (-8 : MvPolynomial (Fin 28) ℂ) * X 6 * P33 + (6 : MvPolynomial (Fin 28) ℂ) * X 8 * P45 + (-4 : MvPolynomial (Fin 28) ℂ) * X 8 * P46 + (2 : MvPolynomial (Fin 28) ℂ) * X 8 * P48 := by
    simp only [Qd, P4, P5, P9, P10, P12, P13, P16, P18, P21, P25, P30, P33, P45, P46, P48]
    ring
  apply mem_of_natCast_mul 2 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P4_mem) (Ideal.mul_mem_left _ _ P5_mem)) (Ideal.mul_mem_left _ _ P9_mem)) (Ideal.mul_mem_left _ _ P10_mem)) (Ideal.mul_mem_left _ _ P12_mem)) (Ideal.mul_mem_left _ _ P13_mem)) (Ideal.mul_mem_left _ _ P16_mem)) (Ideal.mul_mem_left _ _ P18_mem)) (Ideal.mul_mem_left _ _ P21_mem)) (Ideal.mul_mem_left _ _ P21_mem)) (Ideal.mul_mem_left _ _ P21_mem)) (Ideal.mul_mem_left _ _ P21_mem)) (Ideal.mul_mem_left _ _ P25_mem)) (Ideal.mul_mem_left _ _ P25_mem)) (Ideal.mul_mem_left _ _ P25_mem)) (Ideal.mul_mem_left _ _ P25_mem)) (Ideal.mul_mem_left _ _ P30_mem)) (Ideal.mul_mem_left _ _ P30_mem)) (Ideal.mul_mem_left _ _ P30_mem)) (Ideal.mul_mem_left _ _ P30_mem)) (Ideal.mul_mem_left _ _ P33_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem))

set_option maxRecDepth 100000 in
theorem u3_9 : X 9 * Qd ∈ quadraticIdeal rel := by
  have h : ((2 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 9 * Qd) = (4 : MvPolynomial (Fin 28) ℂ) * X 24 * P3 + (-4 : MvPolynomial (Fin 28) ℂ) * X 24 * P5 + (4 : MvPolynomial (Fin 28) ℂ) * X 22 * P7 + (4 : MvPolynomial (Fin 28) ℂ) * X 20 * P10 + (-12 : MvPolynomial (Fin 28) ℂ) * X 16 * P12 + (-4 : MvPolynomial (Fin 28) ℂ) * X 19 * P14 + (8 : MvPolynomial (Fin 28) ℂ) * X 16 * P15 + (-4 : MvPolynomial (Fin 28) ℂ) * X 19 * P17 + (2 : MvPolynomial (Fin 28) ℂ) * X 16 * P18 + (4 : MvPolynomial (Fin 28) ℂ) * X 0 * P22 + (4 : MvPolynomial (Fin 28) ℂ) * X 1 * P22 + (-4 : MvPolynomial (Fin 28) ℂ) * X 2 * P22 + (8 : MvPolynomial (Fin 28) ℂ) * X 3 * P22 + (-2 : MvPolynomial (Fin 28) ℂ) * X 0 * P26 + (-8 : MvPolynomial (Fin 28) ℂ) * X 1 * P26 + (2 : MvPolynomial (Fin 28) ℂ) * X 2 * P26 + (-8 : MvPolynomial (Fin 28) ℂ) * X 3 * P26 + (-1 : MvPolynomial (Fin 28) ℂ) * X 0 * P31 + (-2 : MvPolynomial (Fin 28) ℂ) * X 1 * P31 + (-1 : MvPolynomial (Fin 28) ℂ) * X 2 * P31 + (-2 : MvPolynomial (Fin 28) ℂ) * X 3 * P31 + (-12 : MvPolynomial (Fin 28) ℂ) * X 5 * P34 + (12 : MvPolynomial (Fin 28) ℂ) * X 5 * P38 + (-8 : MvPolynomial (Fin 28) ℂ) * X 6 * P39 + (6 : MvPolynomial (Fin 28) ℂ) * X 9 * P45 + (-12 : MvPolynomial (Fin 28) ℂ) * X 9 * P46 + (6 : MvPolynomial (Fin 28) ℂ) * X 9 * P48 + (-4 : MvPolynomial (Fin 28) ℂ) * X 9 * P51 + (8 : MvPolynomial (Fin 28) ℂ) * X 9 * P52 := by
    simp only [Qd, P3, P5, P7, P10, P12, P14, P15, P17, P18, P22, P26, P31, P34, P38, P39, P45, P46, P48, P51, P52]
    ring
  apply mem_of_natCast_mul 2 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P3_mem) (Ideal.mul_mem_left _ _ P5_mem)) (Ideal.mul_mem_left _ _ P7_mem)) (Ideal.mul_mem_left _ _ P10_mem)) (Ideal.mul_mem_left _ _ P12_mem)) (Ideal.mul_mem_left _ _ P14_mem)) (Ideal.mul_mem_left _ _ P15_mem)) (Ideal.mul_mem_left _ _ P17_mem)) (Ideal.mul_mem_left _ _ P18_mem)) (Ideal.mul_mem_left _ _ P22_mem)) (Ideal.mul_mem_left _ _ P22_mem)) (Ideal.mul_mem_left _ _ P22_mem)) (Ideal.mul_mem_left _ _ P22_mem)) (Ideal.mul_mem_left _ _ P26_mem)) (Ideal.mul_mem_left _ _ P26_mem)) (Ideal.mul_mem_left _ _ P26_mem)) (Ideal.mul_mem_left _ _ P26_mem)) (Ideal.mul_mem_left _ _ P31_mem)) (Ideal.mul_mem_left _ _ P31_mem)) (Ideal.mul_mem_left _ _ P31_mem)) (Ideal.mul_mem_left _ _ P31_mem)) (Ideal.mul_mem_left _ _ P34_mem)) (Ideal.mul_mem_left _ _ P38_mem)) (Ideal.mul_mem_left _ _ P39_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P52_mem))

set_option maxRecDepth 100000 in
theorem u3_10 : X 10 * Qd ∈ quadraticIdeal rel := by
  have h : ((2 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 10 * Qd) = (4 : MvPolynomial (Fin 28) ℂ) * X 23 * P3 + (4 : MvPolynomial (Fin 28) ℂ) * X 23 * P4 + (4 : MvPolynomial (Fin 28) ℂ) * X 21 * P7 + (4 : MvPolynomial (Fin 28) ℂ) * X 20 * P9 + (12 : MvPolynomial (Fin 28) ℂ) * X 16 * P13 + (4 : MvPolynomial (Fin 28) ℂ) * X 17 * P14 + (4 : MvPolynomial (Fin 28) ℂ) * X 16 * P16 + (8 : MvPolynomial (Fin 28) ℂ) * X 16 * P19 + (-4 : MvPolynomial (Fin 28) ℂ) * X 17 * P20 + (4 : MvPolynomial (Fin 28) ℂ) * X 0 * P23 + (-4 : MvPolynomial (Fin 28) ℂ) * X 1 * P23 + (-4 : MvPolynomial (Fin 28) ℂ) * X 2 * P23 + (-8 : MvPolynomial (Fin 28) ℂ) * X 3 * P23 + (-2 : MvPolynomial (Fin 28) ℂ) * X 0 * P28 + (-4 : MvPolynomial (Fin 28) ℂ) * X 1 * P28 + (-2 : MvPolynomial (Fin 28) ℂ) * X 2 * P28 + (-4 : MvPolynomial (Fin 28) ℂ) * X 3 * P28 + (2 : MvPolynomial (Fin 28) ℂ) * X 0 * P32 + (-8 : MvPolynomial (Fin 28) ℂ) * X 1 * P32 + (-2 : MvPolynomial (Fin 28) ℂ) * X 2 * P32 + (-8 : MvPolynomial (Fin 28) ℂ) * X 3 * P32 + (12 : MvPolynomial (Fin 28) ℂ) * X 7 * P34 + (6 : MvPolynomial (Fin 28) ℂ) * X 7 * P43 + (-8 : MvPolynomial (Fin 28) ℂ) * X 6 * P44 + (6 : MvPolynomial (Fin 28) ℂ) * X 10 * P45 + (-12 : MvPolynomial (Fin 28) ℂ) * X 10 * P46 + (6 : MvPolynomial (Fin 28) ℂ) * X 10 * P48 + (1 : MvPolynomial (Fin 28) ℂ) * X 10 * P56 + (-4 : MvPolynomial (Fin 28) ℂ) * X 10 * P58 := by
    simp only [Qd, P3, P4, P7, P9, P13, P14, P16, P19, P20, P23, P28, P32, P34, P43, P44, P45, P46, P48, P56, P58]
    ring
  apply mem_of_natCast_mul 2 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P3_mem) (Ideal.mul_mem_left _ _ P4_mem)) (Ideal.mul_mem_left _ _ P7_mem)) (Ideal.mul_mem_left _ _ P9_mem)) (Ideal.mul_mem_left _ _ P13_mem)) (Ideal.mul_mem_left _ _ P14_mem)) (Ideal.mul_mem_left _ _ P16_mem)) (Ideal.mul_mem_left _ _ P19_mem)) (Ideal.mul_mem_left _ _ P20_mem)) (Ideal.mul_mem_left _ _ P23_mem)) (Ideal.mul_mem_left _ _ P23_mem)) (Ideal.mul_mem_left _ _ P23_mem)) (Ideal.mul_mem_left _ _ P23_mem)) (Ideal.mul_mem_left _ _ P28_mem)) (Ideal.mul_mem_left _ _ P28_mem)) (Ideal.mul_mem_left _ _ P28_mem)) (Ideal.mul_mem_left _ _ P28_mem)) (Ideal.mul_mem_left _ _ P32_mem)) (Ideal.mul_mem_left _ _ P32_mem)) (Ideal.mul_mem_left _ _ P32_mem)) (Ideal.mul_mem_left _ _ P32_mem)) (Ideal.mul_mem_left _ _ P34_mem)) (Ideal.mul_mem_left _ _ P43_mem)) (Ideal.mul_mem_left _ _ P44_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P58_mem))

set_option maxRecDepth 100000 in
theorem u3_11 : X 11 * Qd ∈ quadraticIdeal rel := by
  have h : ((2 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 11 * Qd) = (8 : MvPolynomial (Fin 28) ℂ) * X 25 * P1 + (4 : MvPolynomial (Fin 28) ℂ) * X 22 * P4 + (4 : MvPolynomial (Fin 28) ℂ) * X 22 * P5 + (-4 : MvPolynomial (Fin 28) ℂ) * X 19 * P6 + (-4 : MvPolynomial (Fin 28) ℂ) * X 19 * P8 + (4 : MvPolynomial (Fin 28) ℂ) * X 18 * P10 + (-2 : MvPolynomial (Fin 28) ℂ) * X 0 * P12 + (-8 : MvPolynomial (Fin 28) ℂ) * X 1 * P12 + (-6 : MvPolynomial (Fin 28) ℂ) * X 2 * P12 + (-4 : MvPolynomial (Fin 28) ℂ) * X 3 * P12 + (4 : MvPolynomial (Fin 28) ℂ) * X 0 * P15 + (4 : MvPolynomial (Fin 28) ℂ) * X 1 * P15 + (2 : MvPolynomial (Fin 28) ℂ) * X 2 * P15 + (2 : MvPolynomial (Fin 28) ℂ) * X 3 * P15 + (-1 : MvPolynomial (Fin 28) ℂ) * X 0 * P18 + (-2 : MvPolynomial (Fin 28) ℂ) * X 1 * P18 + (-1 : MvPolynomial (Fin 28) ℂ) * X 3 * P18 + (-4 : MvPolynomial (Fin 28) ℂ) * X 5 * P21 + (2 : MvPolynomial (Fin 28) ℂ) * X 5 * P30 + (-8 : MvPolynomial (Fin 28) ℂ) * X 9 * P33 + (6 : MvPolynomial (Fin 28) ℂ) * X 11 * P45 + (-4 : MvPolynomial (Fin 28) ℂ) * X 11 * P46 + (2 : MvPolynomial (Fin 28) ℂ) * X 11 * P48 := by
    simp only [Qd, P1, P4, P5, P6, P8, P10, P12, P15, P18, P21, P30, P33, P45, P46, P48]
    ring
  apply mem_of_natCast_mul 2 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P1_mem) (Ideal.mul_mem_left _ _ P4_mem)) (Ideal.mul_mem_left _ _ P5_mem)) (Ideal.mul_mem_left _ _ P6_mem)) (Ideal.mul_mem_left _ _ P8_mem)) (Ideal.mul_mem_left _ _ P10_mem)) (Ideal.mul_mem_left _ _ P12_mem)) (Ideal.mul_mem_left _ _ P12_mem)) (Ideal.mul_mem_left _ _ P12_mem)) (Ideal.mul_mem_left _ _ P12_mem)) (Ideal.mul_mem_left _ _ P15_mem)) (Ideal.mul_mem_left _ _ P15_mem)) (Ideal.mul_mem_left _ _ P15_mem)) (Ideal.mul_mem_left _ _ P15_mem)) (Ideal.mul_mem_left _ _ P18_mem)) (Ideal.mul_mem_left _ _ P18_mem)) (Ideal.mul_mem_left _ _ P18_mem)) (Ideal.mul_mem_left _ _ P21_mem)) (Ideal.mul_mem_left _ _ P30_mem)) (Ideal.mul_mem_left _ _ P33_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem))

set_option maxRecDepth 100000 in
theorem u3_12 : X 12 * Qd ∈ quadraticIdeal rel := by
  have h : ((1 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 12 * Qd) = (4 : MvPolynomial (Fin 28) ℂ) * X 25 * P2 + (-2 : MvPolynomial (Fin 28) ℂ) * X 21 * P4 + (-2 : MvPolynomial (Fin 28) ℂ) * X 21 * P5 + (2 : MvPolynomial (Fin 28) ℂ) * X 17 * P6 + (2 : MvPolynomial (Fin 28) ℂ) * X 18 * P9 + (-2 : MvPolynomial (Fin 28) ℂ) * X 17 * P11 + (3 : MvPolynomial (Fin 28) ℂ) * X 0 * P13 + (4 : MvPolynomial (Fin 28) ℂ) * X 1 * P13 + (1 : MvPolynomial (Fin 28) ℂ) * X 2 * P13 + (2 : MvPolynomial (Fin 28) ℂ) * X 3 * P13 + (-2 : MvPolynomial (Fin 28) ℂ) * X 1 * P16 + (-1 : MvPolynomial (Fin 28) ℂ) * X 2 * P16 + (-1 : MvPolynomial (Fin 28) ℂ) * X 3 * P16 + (1 : MvPolynomial (Fin 28) ℂ) * X 0 * P19 + (2 : MvPolynomial (Fin 28) ℂ) * X 1 * P19 + (2 : MvPolynomial (Fin 28) ℂ) * X 2 * P19 + (1 : MvPolynomial (Fin 28) ℂ) * X 3 * P19 + (2 : MvPolynomial (Fin 28) ℂ) * X 7 * P21 + (2 : MvPolynomial (Fin 28) ℂ) * X 7 * P25 + (-4 : MvPolynomial (Fin 28) ℂ) * X 10 * P33 + (3 : MvPolynomial (Fin 28) ℂ) * X 12 * P45 + (-2 : MvPolynomial (Fin 28) ℂ) * X 12 * P46 + (1 : MvPolynomial (Fin 28) ℂ) * X 12 * P48 := by
    simp only [Qd, P2, P4, P5, P6, P9, P11, P13, P16, P19, P21, P25, P33, P45, P46, P48]
    ring
  apply mem_of_natCast_mul 1 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P2_mem) (Ideal.mul_mem_left _ _ P4_mem)) (Ideal.mul_mem_left _ _ P5_mem)) (Ideal.mul_mem_left _ _ P6_mem)) (Ideal.mul_mem_left _ _ P9_mem)) (Ideal.mul_mem_left _ _ P11_mem)) (Ideal.mul_mem_left _ _ P13_mem)) (Ideal.mul_mem_left _ _ P13_mem)) (Ideal.mul_mem_left _ _ P13_mem)) (Ideal.mul_mem_left _ _ P13_mem)) (Ideal.mul_mem_left _ _ P16_mem)) (Ideal.mul_mem_left _ _ P16_mem)) (Ideal.mul_mem_left _ _ P16_mem)) (Ideal.mul_mem_left _ _ P19_mem)) (Ideal.mul_mem_left _ _ P19_mem)) (Ideal.mul_mem_left _ _ P19_mem)) (Ideal.mul_mem_left _ _ P19_mem)) (Ideal.mul_mem_left _ _ P21_mem)) (Ideal.mul_mem_left _ _ P25_mem)) (Ideal.mul_mem_left _ _ P33_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem))

set_option maxRecDepth 100000 in
theorem u3_13 : X 13 * Qd ∈ quadraticIdeal rel := by
  have h : ((1 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 13 * Qd) = (4 : MvPolynomial (Fin 28) ℂ) * X 23 * P1 + (4 : MvPolynomial (Fin 28) ℂ) * X 24 * P2 + (4 : MvPolynomial (Fin 28) ℂ) * X 20 * P3 + (2 : MvPolynomial (Fin 28) ℂ) * X 20 * P4 + (-2 : MvPolynomial (Fin 28) ℂ) * X 20 * P5 + (-4 : MvPolynomial (Fin 28) ℂ) * X 16 * P6 + (-4 : MvPolynomial (Fin 28) ℂ) * X 18 * P7 + (-6 : MvPolynomial (Fin 28) ℂ) * X 16 * P8 + (-2 : MvPolynomial (Fin 28) ℂ) * X 16 * P11 + (4 : MvPolynomial (Fin 28) ℂ) * X 1 * P14 + (4 : MvPolynomial (Fin 28) ℂ) * X 2 * P14 + (4 : MvPolynomial (Fin 28) ℂ) * X 3 * P14 + (3 : MvPolynomial (Fin 28) ℂ) * X 0 * P17 + (-2 : MvPolynomial (Fin 28) ℂ) * X 1 * P17 + (-1 : MvPolynomial (Fin 28) ℂ) * X 2 * P17 + (2 : MvPolynomial (Fin 28) ℂ) * X 3 * P17 + (1 : MvPolynomial (Fin 28) ℂ) * X 0 * P20 + (2 : MvPolynomial (Fin 28) ℂ) * X 1 * P20 + (1 : MvPolynomial (Fin 28) ℂ) * X 2 * P20 + (2 : MvPolynomial (Fin 28) ℂ) * X 3 * P20 + (-4 : MvPolynomial (Fin 28) ℂ) * X 7 * P22 + (4 : MvPolynomial (Fin 28) ℂ) * X 5 * P23 + (-4 : MvPolynomial (Fin 28) ℂ) * X 6 * P24 + (8 : MvPolynomial (Fin 28) ℂ) * X 7 * P26 + (-4 : MvPolynomial (Fin 28) ℂ) * X 10 * P35 + (4 : MvPolynomial (Fin 28) ℂ) * X 9 * P36 + (1 : MvPolynomial (Fin 28) ℂ) * X 13 * P45 + (-2 : MvPolynomial (Fin 28) ℂ) * X 13 * P46 + (3 : MvPolynomial (Fin 28) ℂ) * X 13 * P48 := by
    simp only [Qd, P1, P2, P3, P4, P5, P6, P7, P8, P11, P14, P17, P20, P22, P23, P24, P26, P35, P36, P45, P46, P48]
    ring
  apply mem_of_natCast_mul 1 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P1_mem) (Ideal.mul_mem_left _ _ P2_mem)) (Ideal.mul_mem_left _ _ P3_mem)) (Ideal.mul_mem_left _ _ P4_mem)) (Ideal.mul_mem_left _ _ P5_mem)) (Ideal.mul_mem_left _ _ P6_mem)) (Ideal.mul_mem_left _ _ P7_mem)) (Ideal.mul_mem_left _ _ P8_mem)) (Ideal.mul_mem_left _ _ P11_mem)) (Ideal.mul_mem_left _ _ P14_mem)) (Ideal.mul_mem_left _ _ P14_mem)) (Ideal.mul_mem_left _ _ P14_mem)) (Ideal.mul_mem_left _ _ P17_mem)) (Ideal.mul_mem_left _ _ P17_mem)) (Ideal.mul_mem_left _ _ P17_mem)) (Ideal.mul_mem_left _ _ P17_mem)) (Ideal.mul_mem_left _ _ P20_mem)) (Ideal.mul_mem_left _ _ P20_mem)) (Ideal.mul_mem_left _ _ P20_mem)) (Ideal.mul_mem_left _ _ P20_mem)) (Ideal.mul_mem_left _ _ P22_mem)) (Ideal.mul_mem_left _ _ P23_mem)) (Ideal.mul_mem_left _ _ P24_mem)) (Ideal.mul_mem_left _ _ P26_mem)) (Ideal.mul_mem_left _ _ P35_mem)) (Ideal.mul_mem_left _ _ P36_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem))

set_option maxRecDepth 100000 in
theorem u3_14 : X 14 * Qd ∈ quadraticIdeal rel := by
  have h : ((1 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 14 * Qd) = (-4 : MvPolynomial (Fin 28) ℂ) * X 20 * P0 + (-4 : MvPolynomial (Fin 28) ℂ) * X 21 * P1 + (-4 : MvPolynomial (Fin 28) ℂ) * X 22 * P2 + (2 : MvPolynomial (Fin 28) ℂ) * X 18 * P3 + (2 : MvPolynomial (Fin 28) ℂ) * X 18 * P4 + (-2 : MvPolynomial (Fin 28) ℂ) * X 18 * P5 + (4 : MvPolynomial (Fin 28) ℂ) * X 0 * P6 + (4 : MvPolynomial (Fin 28) ℂ) * X 1 * P6 + (3 : MvPolynomial (Fin 28) ℂ) * X 2 * P6 + (3 : MvPolynomial (Fin 28) ℂ) * X 3 * P6 + (-1 : MvPolynomial (Fin 28) ℂ) * X 0 * P8 + (-2 : MvPolynomial (Fin 28) ℂ) * X 1 * P8 + (-1 : MvPolynomial (Fin 28) ℂ) * X 2 * P8 + (1 : MvPolynomial (Fin 28) ℂ) * X 0 * P11 + (2 : MvPolynomial (Fin 28) ℂ) * X 1 * P11 + (1 : MvPolynomial (Fin 28) ℂ) * X 3 * P11 + (4 : MvPolynomial (Fin 28) ℂ) * X 7 * P12 + (2 : MvPolynomial (Fin 28) ℂ) * X 5 * P13 + (2 : MvPolynomial (Fin 28) ℂ) * X 4 * P14 + (2 : MvPolynomial (Fin 28) ℂ) * X 4 * P17 + (-2 : MvPolynomial (Fin 28) ℂ) * X 5 * P19 + (2 : MvPolynomial (Fin 28) ℂ) * X 8 * P24 + (-6 : MvPolynomial (Fin 28) ℂ) * X 13 * P33 + (2 : MvPolynomial (Fin 28) ℂ) * X 12 * P35 + (-2 : MvPolynomial (Fin 28) ℂ) * X 11 * P36 + (4 : MvPolynomial (Fin 28) ℂ) * X 14 * P45 + (-2 : MvPolynomial (Fin 28) ℂ) * X 14 * P46 := by
    simp only [Qd, P0, P1, P2, P3, P4, P5, P6, P8, P11, P12, P13, P14, P17, P19, P24, P33, P35, P36, P45, P46]
    ring
  apply mem_of_natCast_mul 1 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P0_mem) (Ideal.mul_mem_left _ _ P1_mem)) (Ideal.mul_mem_left _ _ P2_mem)) (Ideal.mul_mem_left _ _ P3_mem)) (Ideal.mul_mem_left _ _ P4_mem)) (Ideal.mul_mem_left _ _ P5_mem)) (Ideal.mul_mem_left _ _ P6_mem)) (Ideal.mul_mem_left _ _ P6_mem)) (Ideal.mul_mem_left _ _ P6_mem)) (Ideal.mul_mem_left _ _ P6_mem)) (Ideal.mul_mem_left _ _ P8_mem)) (Ideal.mul_mem_left _ _ P8_mem)) (Ideal.mul_mem_left _ _ P8_mem)) (Ideal.mul_mem_left _ _ P11_mem)) (Ideal.mul_mem_left _ _ P11_mem)) (Ideal.mul_mem_left _ _ P11_mem)) (Ideal.mul_mem_left _ _ P12_mem)) (Ideal.mul_mem_left _ _ P13_mem)) (Ideal.mul_mem_left _ _ P14_mem)) (Ideal.mul_mem_left _ _ P17_mem)) (Ideal.mul_mem_left _ _ P19_mem)) (Ideal.mul_mem_left _ _ P24_mem)) (Ideal.mul_mem_left _ _ P33_mem)) (Ideal.mul_mem_left _ _ P35_mem)) (Ideal.mul_mem_left _ _ P36_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem))

set_option maxRecDepth 100000 in
theorem u3_15 : X 15 * Qd ∈ quadraticIdeal rel := by
  have h : ((1 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 15 * Qd) = (4 : MvPolynomial (Fin 28) ℂ) * X 16 * P0 + (-4 : MvPolynomial (Fin 28) ℂ) * X 17 * P1 + (4 : MvPolynomial (Fin 28) ℂ) * X 19 * P2 + (2 : MvPolynomial (Fin 28) ℂ) * X 1 * P3 + (1 : MvPolynomial (Fin 28) ℂ) * X 2 * P3 + (1 : MvPolynomial (Fin 28) ℂ) * X 3 * P3 + (1 : MvPolynomial (Fin 28) ℂ) * X 0 * P4 + (1 : MvPolynomial (Fin 28) ℂ) * X 2 * P4 + (-1 : MvPolynomial (Fin 28) ℂ) * X 0 * P5 + (-1 : MvPolynomial (Fin 28) ℂ) * X 3 * P5 + (2 : MvPolynomial (Fin 28) ℂ) * X 6 * P6 + (2 : MvPolynomial (Fin 28) ℂ) * X 4 * P7 + (-2 : MvPolynomial (Fin 28) ℂ) * X 6 * P8 + (2 : MvPolynomial (Fin 28) ℂ) * X 6 * P11 + (-2 : MvPolynomial (Fin 28) ℂ) * X 9 * P13 + (2 : MvPolynomial (Fin 28) ℂ) * X 8 * P14 + (2 : MvPolynomial (Fin 28) ℂ) * X 8 * P17 + (-2 : MvPolynomial (Fin 28) ℂ) * X 9 * P19 + (2 : MvPolynomial (Fin 28) ℂ) * X 13 * P21 + (2 : MvPolynomial (Fin 28) ℂ) * X 12 * P22 + (-2 : MvPolynomial (Fin 28) ℂ) * X 11 * P23 + (-4 : MvPolynomial (Fin 28) ℂ) * X 14 * P34 + (-2 : MvPolynomial (Fin 28) ℂ) * X 15 * P46 := by
    simp only [Qd, P0, P1, P2, P3, P4, P5, P6, P7, P8, P11, P13, P14, P17, P19, P21, P22, P23, P34, P46]
    ring
  apply mem_of_natCast_mul 1 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P0_mem) (Ideal.mul_mem_left _ _ P1_mem)) (Ideal.mul_mem_left _ _ P2_mem)) (Ideal.mul_mem_left _ _ P3_mem)) (Ideal.mul_mem_left _ _ P3_mem)) (Ideal.mul_mem_left _ _ P3_mem)) (Ideal.mul_mem_left _ _ P4_mem)) (Ideal.mul_mem_left _ _ P4_mem)) (Ideal.mul_mem_left _ _ P5_mem)) (Ideal.mul_mem_left _ _ P5_mem)) (Ideal.mul_mem_left _ _ P6_mem)) (Ideal.mul_mem_left _ _ P7_mem)) (Ideal.mul_mem_left _ _ P8_mem)) (Ideal.mul_mem_left _ _ P11_mem)) (Ideal.mul_mem_left _ _ P13_mem)) (Ideal.mul_mem_left _ _ P14_mem)) (Ideal.mul_mem_left _ _ P17_mem)) (Ideal.mul_mem_left _ _ P19_mem)) (Ideal.mul_mem_left _ _ P21_mem)) (Ideal.mul_mem_left _ _ P22_mem)) (Ideal.mul_mem_left _ _ P23_mem)) (Ideal.mul_mem_left _ _ P34_mem)) (Ideal.mul_mem_left _ _ P46_mem))

set_option maxRecDepth 100000 in
theorem u3_16 : X 16 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 16 * Qd) = (-4 : MvPolynomial (Fin 28) ℂ) * X 26 * P17 + (4 : MvPolynomial (Fin 28) ℂ) * X 26 * P20 + (-16 : MvPolynomial (Fin 28) ℂ) * X 23 * P22 + (-4 : MvPolynomial (Fin 28) ℂ) * X 23 * P26 + (-4 : MvPolynomial (Fin 28) ℂ) * X 24 * P28 + (-6 : MvPolynomial (Fin 28) ℂ) * X 23 * P31 + (4 : MvPolynomial (Fin 28) ℂ) * X 24 * P32 + (-16 : MvPolynomial (Fin 28) ℂ) * X 20 * P34 + (-4 : MvPolynomial (Fin 28) ℂ) * X 20 * P38 + (-6 : MvPolynomial (Fin 28) ℂ) * X 20 * P43 + (-4 : MvPolynomial (Fin 28) ℂ) * X 16 * P45 + (-8 : MvPolynomial (Fin 28) ℂ) * X 16 * P46 + (4 : MvPolynomial (Fin 28) ℂ) * X 16 * P48 + (8 : MvPolynomial (Fin 28) ℂ) * X 16 * P51 + (-8 : MvPolynomial (Fin 28) ℂ) * X 16 * P52 + (4 : MvPolynomial (Fin 28) ℂ) * X 16 * P53 + (-8 : MvPolynomial (Fin 28) ℂ) * X 19 * P54 + (1 : MvPolynomial (Fin 28) ℂ) * X 16 * P56 + (-4 : MvPolynomial (Fin 28) ℂ) * X 16 * P58 + (-4 : MvPolynomial (Fin 28) ℂ) * X 0 * P61 + (4 : MvPolynomial (Fin 28) ℂ) * X 3 * P61 + (6 : MvPolynomial (Fin 28) ℂ) * X 0 * P66 + (4 : MvPolynomial (Fin 28) ℂ) * X 1 * P66 + (2 : MvPolynomial (Fin 28) ℂ) * X 2 * P66 := by
    simp only [Qd, P17, P20, P22, P26, P28, P31, P32, P34, P38, P43, P45, P46, P48, P51, P52, P53, P54, P56, P58, P61, P66]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P17_mem) (Ideal.mul_mem_left _ _ P20_mem)) (Ideal.mul_mem_left _ _ P22_mem)) (Ideal.mul_mem_left _ _ P26_mem)) (Ideal.mul_mem_left _ _ P28_mem)) (Ideal.mul_mem_left _ _ P31_mem)) (Ideal.mul_mem_left _ _ P32_mem)) (Ideal.mul_mem_left _ _ P34_mem)) (Ideal.mul_mem_left _ _ P38_mem)) (Ideal.mul_mem_left _ _ P43_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P54_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P58_mem)) (Ideal.mul_mem_left _ _ P61_mem)) (Ideal.mul_mem_left _ _ P61_mem)) (Ideal.mul_mem_left _ _ P66_mem)) (Ideal.mul_mem_left _ _ P66_mem)) (Ideal.mul_mem_left _ _ P66_mem))

set_option maxRecDepth 100000 in
theorem u3_17 : X 17 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 17 * Qd) = (-16 : MvPolynomial (Fin 28) ℂ) * X 23 * P25 + (-8 : MvPolynomial (Fin 28) ℂ) * X 23 * P30 + (-16 : MvPolynomial (Fin 28) ℂ) * X 21 * P38 + (-8 : MvPolynomial (Fin 28) ℂ) * X 21 * P43 + (4 : MvPolynomial (Fin 28) ℂ) * X 17 * P45 + (-8 : MvPolynomial (Fin 28) ℂ) * X 17 * P46 + (12 : MvPolynomial (Fin 28) ℂ) * X 17 * P48 + (-16 : MvPolynomial (Fin 28) ℂ) * X 19 * P49 + (4 : MvPolynomial (Fin 28) ℂ) * X 17 * P51 + (-8 : MvPolynomial (Fin 28) ℂ) * X 17 * P52 + (-4 : MvPolynomial (Fin 28) ℂ) * X 17 * P53 + (1 : MvPolynomial (Fin 28) ℂ) * X 17 * P56 + (-4 : MvPolynomial (Fin 28) ℂ) * X 17 * P58 + (-4 : MvPolynomial (Fin 28) ℂ) * X 17 * P59 + (8 : MvPolynomial (Fin 28) ℂ) * X 0 * P63 + (-8 : MvPolynomial (Fin 28) ℂ) * X 2 * P63 + (-8 : MvPolynomial (Fin 28) ℂ) * X 0 * P67 + (8 : MvPolynomial (Fin 28) ℂ) * X 2 * P67 := by
    simp only [Qd, P25, P30, P38, P43, P45, P46, P48, P49, P51, P52, P53, P56, P58, P59, P63, P67]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P25_mem) (Ideal.mul_mem_left _ _ P30_mem)) (Ideal.mul_mem_left _ _ P38_mem)) (Ideal.mul_mem_left _ _ P43_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P49_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P58_mem)) (Ideal.mul_mem_left _ _ P59_mem)) (Ideal.mul_mem_left _ _ P63_mem)) (Ideal.mul_mem_left _ _ P63_mem)) (Ideal.mul_mem_left _ _ P67_mem)) (Ideal.mul_mem_left _ _ P67_mem))

set_option maxRecDepth 100000 in
theorem u3_18 : X 18 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 18 * Qd) = (8 : MvPolynomial (Fin 28) ℂ) * X 27 * P8 + (-8 : MvPolynomial (Fin 28) ℂ) * X 27 * P11 + (8 : MvPolynomial (Fin 28) ℂ) * X 24 * P27 + (4 : MvPolynomial (Fin 28) ℂ) * X 23 * P29 + (-16 : MvPolynomial (Fin 28) ℂ) * X 20 * P33 + (-16 : MvPolynomial (Fin 28) ℂ) * X 21 * P35 + (16 : MvPolynomial (Fin 28) ℂ) * X 22 * P36 + (8 : MvPolynomial (Fin 28) ℂ) * X 20 * P37 + (-8 : MvPolynomial (Fin 28) ℂ) * X 21 * P39 + (12 : MvPolynomial (Fin 28) ℂ) * X 22 * P40 + (-2 : MvPolynomial (Fin 28) ℂ) * X 20 * P41 + (-2 : MvPolynomial (Fin 28) ℂ) * X 21 * P42 + (24 : MvPolynomial (Fin 28) ℂ) * X 22 * P44 + (4 : MvPolynomial (Fin 28) ℂ) * X 18 * P45 + (8 : MvPolynomial (Fin 28) ℂ) * X 18 * P46 + (12 : MvPolynomial (Fin 28) ℂ) * X 18 * P48 + (4 : MvPolynomial (Fin 28) ℂ) * X 18 * P51 + (4 : MvPolynomial (Fin 28) ℂ) * X 18 * P53 + (3 : MvPolynomial (Fin 28) ℂ) * X 18 * P56 + (12 : MvPolynomial (Fin 28) ℂ) * X 18 * P59 + (-16 : MvPolynomial (Fin 28) ℂ) * X 1 * P60 + (-16 : MvPolynomial (Fin 28) ℂ) * X 0 * P65 + (-16 : MvPolynomial (Fin 28) ℂ) * X 1 * P65 + (-8 : MvPolynomial (Fin 28) ℂ) * X 2 * P65 + (-2 : MvPolynomial (Fin 28) ℂ) * X 0 * P69 + (-4 : MvPolynomial (Fin 28) ℂ) * X 1 * P69 + (16 : MvPolynomial (Fin 28) ℂ) * X 4 * P74 := by
    simp only [Qd, P8, P11, P27, P29, P33, P35, P36, P37, P39, P40, P41, P42, P44, P45, P46, P48, P51, P53, P56, P59, P60, P65, P69, P74]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P8_mem) (Ideal.mul_mem_left _ _ P11_mem)) (Ideal.mul_mem_left _ _ P27_mem)) (Ideal.mul_mem_left _ _ P29_mem)) (Ideal.mul_mem_left _ _ P33_mem)) (Ideal.mul_mem_left _ _ P35_mem)) (Ideal.mul_mem_left _ _ P36_mem)) (Ideal.mul_mem_left _ _ P37_mem)) (Ideal.mul_mem_left _ _ P39_mem)) (Ideal.mul_mem_left _ _ P40_mem)) (Ideal.mul_mem_left _ _ P41_mem)) (Ideal.mul_mem_left _ _ P42_mem)) (Ideal.mul_mem_left _ _ P44_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P59_mem)) (Ideal.mul_mem_left _ _ P60_mem)) (Ideal.mul_mem_left _ _ P65_mem)) (Ideal.mul_mem_left _ _ P65_mem)) (Ideal.mul_mem_left _ _ P65_mem)) (Ideal.mul_mem_left _ _ P69_mem)) (Ideal.mul_mem_left _ _ P69_mem)) (Ideal.mul_mem_left _ _ P74_mem))

set_option maxRecDepth 100000 in
theorem u3_19 : X 19 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 19 * Qd) = (-16 : MvPolynomial (Fin 28) ℂ) * X 24 * P25 + (-8 : MvPolynomial (Fin 28) ℂ) * X 24 * P30 + (-16 : MvPolynomial (Fin 28) ℂ) * X 22 * P38 + (-8 : MvPolynomial (Fin 28) ℂ) * X 22 * P43 + (4 : MvPolynomial (Fin 28) ℂ) * X 19 * P45 + (-8 : MvPolynomial (Fin 28) ℂ) * X 19 * P46 + (-16 : MvPolynomial (Fin 28) ℂ) * X 17 * P47 + (12 : MvPolynomial (Fin 28) ℂ) * X 19 * P48 + (-4 : MvPolynomial (Fin 28) ℂ) * X 19 * P51 + (8 : MvPolynomial (Fin 28) ℂ) * X 19 * P52 + (4 : MvPolynomial (Fin 28) ℂ) * X 19 * P53 + (-1 : MvPolynomial (Fin 28) ℂ) * X 19 * P56 + (4 : MvPolynomial (Fin 28) ℂ) * X 19 * P58 + (4 : MvPolynomial (Fin 28) ℂ) * X 19 * P59 + (-8 : MvPolynomial (Fin 28) ℂ) * X 0 * P62 + (8 : MvPolynomial (Fin 28) ℂ) * X 2 * P62 + (-4 : MvPolynomial (Fin 28) ℂ) * X 0 * P71 + (4 : MvPolynomial (Fin 28) ℂ) * X 2 * P71 := by
    simp only [Qd, P25, P30, P38, P43, P45, P46, P47, P48, P51, P52, P53, P56, P58, P59, P62, P71]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P25_mem) (Ideal.mul_mem_left _ _ P30_mem)) (Ideal.mul_mem_left _ _ P38_mem)) (Ideal.mul_mem_left _ _ P43_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P47_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P58_mem)) (Ideal.mul_mem_left _ _ P59_mem)) (Ideal.mul_mem_left _ _ P62_mem)) (Ideal.mul_mem_left _ _ P62_mem)) (Ideal.mul_mem_left _ _ P71_mem)) (Ideal.mul_mem_left _ _ P71_mem))

set_option maxRecDepth 100000 in
theorem u3_20 : X 20 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 20 * Qd) = (8 : MvPolynomial (Fin 28) ℂ) * X 27 * P17 + (-8 : MvPolynomial (Fin 28) ℂ) * X 27 * P20 + (32 : MvPolynomial (Fin 28) ℂ) * X 23 * P35 + (-8 : MvPolynomial (Fin 28) ℂ) * X 23 * P39 + (4 : MvPolynomial (Fin 28) ℂ) * X 24 * P40 + (2 : MvPolynomial (Fin 28) ℂ) * X 23 * P42 + (-8 : MvPolynomial (Fin 28) ℂ) * X 24 * P44 + (-12 : MvPolynomial (Fin 28) ℂ) * X 20 * P45 + (8 : MvPolynomial (Fin 28) ℂ) * X 20 * P46 + (12 : MvPolynomial (Fin 28) ℂ) * X 20 * P48 + (12 : MvPolynomial (Fin 28) ℂ) * X 20 * P51 + (-4 : MvPolynomial (Fin 28) ℂ) * X 20 * P53 + (8 : MvPolynomial (Fin 28) ℂ) * X 22 * P54 + (1 : MvPolynomial (Fin 28) ℂ) * X 20 * P56 + (4 : MvPolynomial (Fin 28) ℂ) * X 20 * P59 + (16 : MvPolynomial (Fin 28) ℂ) * X 16 * P60 + (8 : MvPolynomial (Fin 28) ℂ) * X 18 * P61 + (8 : MvPolynomial (Fin 28) ℂ) * X 16 * P65 + (-8 : MvPolynomial (Fin 28) ℂ) * X 18 * P66 + (2 : MvPolynomial (Fin 28) ℂ) * X 16 * P69 + (8 : MvPolynomial (Fin 28) ℂ) * X 0 * P74 + (-16 : MvPolynomial (Fin 28) ℂ) * X 1 * P74 + (-8 : MvPolynomial (Fin 28) ℂ) * X 2 * P74 + (-16 : MvPolynomial (Fin 28) ℂ) * X 3 * P74 + (-16 : MvPolynomial (Fin 28) ℂ) * X 0 * P79 := by
    simp only [Qd, P17, P20, P35, P39, P40, P42, P44, P45, P46, P48, P51, P53, P54, P56, P59, P60, P61, P65, P66, P69, P74, P79]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P17_mem) (Ideal.mul_mem_left _ _ P20_mem)) (Ideal.mul_mem_left _ _ P35_mem)) (Ideal.mul_mem_left _ _ P39_mem)) (Ideal.mul_mem_left _ _ P40_mem)) (Ideal.mul_mem_left _ _ P42_mem)) (Ideal.mul_mem_left _ _ P44_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P54_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P59_mem)) (Ideal.mul_mem_left _ _ P60_mem)) (Ideal.mul_mem_left _ _ P61_mem)) (Ideal.mul_mem_left _ _ P65_mem)) (Ideal.mul_mem_left _ _ P66_mem)) (Ideal.mul_mem_left _ _ P69_mem)) (Ideal.mul_mem_left _ _ P74_mem)) (Ideal.mul_mem_left _ _ P74_mem)) (Ideal.mul_mem_left _ _ P74_mem)) (Ideal.mul_mem_left _ _ P74_mem)) (Ideal.mul_mem_left _ _ P79_mem))

set_option maxRecDepth 100000 in
theorem u3_21 : X 21 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 21 * Qd) = (16 : MvPolynomial (Fin 28) ℂ) * X 23 * P37 + (4 : MvPolynomial (Fin 28) ℂ) * X 23 * P41 + (4 : MvPolynomial (Fin 28) ℂ) * X 21 * P45 + (-8 : MvPolynomial (Fin 28) ℂ) * X 21 * P46 + (12 : MvPolynomial (Fin 28) ℂ) * X 21 * P48 + (16 : MvPolynomial (Fin 28) ℂ) * X 22 * P49 + (4 : MvPolynomial (Fin 28) ℂ) * X 21 * P51 + (8 : MvPolynomial (Fin 28) ℂ) * X 21 * P52 + (-4 : MvPolynomial (Fin 28) ℂ) * X 21 * P53 + (1 : MvPolynomial (Fin 28) ℂ) * X 21 * P56 + (4 : MvPolynomial (Fin 28) ℂ) * X 21 * P58 + (-4 : MvPolynomial (Fin 28) ℂ) * X 21 * P59 + (16 : MvPolynomial (Fin 28) ℂ) * X 17 * P65 + (4 : MvPolynomial (Fin 28) ℂ) * X 17 * P69 + (-8 : MvPolynomial (Fin 28) ℂ) * X 0 * P73 + (8 : MvPolynomial (Fin 28) ℂ) * X 2 * P73 + (8 : MvPolynomial (Fin 28) ℂ) * X 0 * P78 + (-8 : MvPolynomial (Fin 28) ℂ) * X 2 * P78 := by
    simp only [Qd, P37, P41, P45, P46, P48, P49, P51, P52, P53, P56, P58, P59, P65, P69, P73, P78]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P37_mem) (Ideal.mul_mem_left _ _ P41_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P49_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P58_mem)) (Ideal.mul_mem_left _ _ P59_mem)) (Ideal.mul_mem_left _ _ P65_mem)) (Ideal.mul_mem_left _ _ P69_mem)) (Ideal.mul_mem_left _ _ P73_mem)) (Ideal.mul_mem_left _ _ P73_mem)) (Ideal.mul_mem_left _ _ P78_mem)) (Ideal.mul_mem_left _ _ P78_mem))

set_option maxRecDepth 100000 in
theorem u3_22 : X 22 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 22 * Qd) = (16 : MvPolynomial (Fin 28) ℂ) * X 25 * P35 + (-32 : MvPolynomial (Fin 28) ℂ) * X 24 * P37 + (-16 : MvPolynomial (Fin 28) ℂ) * X 25 * P39 + (-4 : MvPolynomial (Fin 28) ℂ) * X 24 * P41 + (-4 : MvPolynomial (Fin 28) ℂ) * X 25 * P42 + (4 : MvPolynomial (Fin 28) ℂ) * X 22 * P45 + (-8 : MvPolynomial (Fin 28) ℂ) * X 22 * P46 + (24 : MvPolynomial (Fin 28) ℂ) * X 21 * P47 + (20 : MvPolynomial (Fin 28) ℂ) * X 22 * P48 + (-8 : MvPolynomial (Fin 28) ℂ) * X 20 * P50 + (-4 : MvPolynomial (Fin 28) ℂ) * X 22 * P51 + (-8 : MvPolynomial (Fin 28) ℂ) * X 22 * P52 + (-4 : MvPolynomial (Fin 28) ℂ) * X 22 * P53 + (-3 : MvPolynomial (Fin 28) ℂ) * X 22 * P56 + (-4 : MvPolynomial (Fin 28) ℂ) * X 22 * P58 + (12 : MvPolynomial (Fin 28) ℂ) * X 22 * P59 + (-8 : MvPolynomial (Fin 28) ℂ) * X 19 * P60 + (-8 : MvPolynomial (Fin 28) ℂ) * X 18 * P62 + (12 : MvPolynomial (Fin 28) ℂ) * X 18 * P64 + (24 : MvPolynomial (Fin 28) ℂ) * X 19 * P65 + (4 : MvPolynomial (Fin 28) ℂ) * X 19 * P69 + (8 : MvPolynomial (Fin 28) ℂ) * X 18 * P71 + (-16 : MvPolynomial (Fin 28) ℂ) * X 0 * P72 + (8 : MvPolynomial (Fin 28) ℂ) * X 2 * P72 + (-8 : MvPolynomial (Fin 28) ℂ) * X 1 * P76 + (-4 : MvPolynomial (Fin 28) ℂ) * X 2 * P76 + (-4 : MvPolynomial (Fin 28) ℂ) * X 0 * P82 + (-4 : MvPolynomial (Fin 28) ℂ) * X 1 * P82 := by
    simp only [Qd, P35, P37, P39, P41, P42, P45, P46, P47, P48, P50, P51, P52, P53, P56, P58, P59, P60, P62, P64, P65, P69, P71, P72, P76, P82]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P35_mem) (Ideal.mul_mem_left _ _ P37_mem)) (Ideal.mul_mem_left _ _ P39_mem)) (Ideal.mul_mem_left _ _ P41_mem)) (Ideal.mul_mem_left _ _ P42_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P47_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P50_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P58_mem)) (Ideal.mul_mem_left _ _ P59_mem)) (Ideal.mul_mem_left _ _ P60_mem)) (Ideal.mul_mem_left _ _ P62_mem)) (Ideal.mul_mem_left _ _ P64_mem)) (Ideal.mul_mem_left _ _ P65_mem)) (Ideal.mul_mem_left _ _ P69_mem)) (Ideal.mul_mem_left _ _ P71_mem)) (Ideal.mul_mem_left _ _ P72_mem)) (Ideal.mul_mem_left _ _ P72_mem)) (Ideal.mul_mem_left _ _ P76_mem)) (Ideal.mul_mem_left _ _ P76_mem)) (Ideal.mul_mem_left _ _ P82_mem)) (Ideal.mul_mem_left _ _ P82_mem))

set_option maxRecDepth 100000 in
theorem u3_23 : X 23 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 23 * Qd) = (16 : MvPolynomial (Fin 28) ℂ) * X 27 * P23 + (-8 : MvPolynomial (Fin 28) ℂ) * X 27 * P28 + (-8 : MvPolynomial (Fin 28) ℂ) * X 27 * P32 + (-16 : MvPolynomial (Fin 28) ℂ) * X 26 * P36 + (4 : MvPolynomial (Fin 28) ℂ) * X 26 * P40 + (8 : MvPolynomial (Fin 28) ℂ) * X 26 * P44 + (4 : MvPolynomial (Fin 28) ℂ) * X 23 * P45 + (-8 : MvPolynomial (Fin 28) ℂ) * X 23 * P46 + (12 : MvPolynomial (Fin 28) ℂ) * X 23 * P48 + (16 : MvPolynomial (Fin 28) ℂ) * X 24 * P49 + (-4 : MvPolynomial (Fin 28) ℂ) * X 23 * P51 + (4 : MvPolynomial (Fin 28) ℂ) * X 23 * P53 + (-5 : MvPolynomial (Fin 28) ℂ) * X 23 * P56 + (8 : MvPolynomial (Fin 28) ℂ) * X 23 * P58 + (-12 : MvPolynomial (Fin 28) ℂ) * X 23 * P59 + (-16 : MvPolynomial (Fin 28) ℂ) * X 20 * P63 + (8 : MvPolynomial (Fin 28) ℂ) * X 20 * P67 + (1 : MvPolynomial (Fin 28) ℂ) * X 20 * P68 + (-4 : MvPolynomial (Fin 28) ℂ) * X 21 * P70 + (-16 : MvPolynomial (Fin 28) ℂ) * X 16 * P73 + (8 : MvPolynomial (Fin 28) ℂ) * X 16 * P78 + (1 : MvPolynomial (Fin 28) ℂ) * X 16 * P80 + (-8 : MvPolynomial (Fin 28) ℂ) * X 17 * P83 + (-8 : MvPolynomial (Fin 28) ℂ) * X 0 * P86 + (-16 : MvPolynomial (Fin 28) ℂ) * X 1 * P86 + (-24 : MvPolynomial (Fin 28) ℂ) * X 2 * P86 := by
    simp only [Qd, P23, P28, P32, P36, P40, P44, P45, P46, P48, P49, P51, P53, P56, P58, P59, P63, P67, P68, P70, P73, P78, P80, P83, P86]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P23_mem) (Ideal.mul_mem_left _ _ P28_mem)) (Ideal.mul_mem_left _ _ P32_mem)) (Ideal.mul_mem_left _ _ P36_mem)) (Ideal.mul_mem_left _ _ P40_mem)) (Ideal.mul_mem_left _ _ P44_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P49_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P58_mem)) (Ideal.mul_mem_left _ _ P59_mem)) (Ideal.mul_mem_left _ _ P63_mem)) (Ideal.mul_mem_left _ _ P67_mem)) (Ideal.mul_mem_left _ _ P68_mem)) (Ideal.mul_mem_left _ _ P70_mem)) (Ideal.mul_mem_left _ _ P73_mem)) (Ideal.mul_mem_left _ _ P78_mem)) (Ideal.mul_mem_left _ _ P80_mem)) (Ideal.mul_mem_left _ _ P83_mem)) (Ideal.mul_mem_left _ _ P86_mem)) (Ideal.mul_mem_left _ _ P86_mem)) (Ideal.mul_mem_left _ _ P86_mem))

set_option maxRecDepth 100000 in
theorem u3_24 : X 24 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 24 * Qd) = (-16 : MvPolynomial (Fin 28) ℂ) * X 27 * P22 + (-8 : MvPolynomial (Fin 28) ℂ) * X 27 * P26 + (-4 : MvPolynomial (Fin 28) ℂ) * X 27 * P31 + (16 : MvPolynomial (Fin 28) ℂ) * X 26 * P35 + (8 : MvPolynomial (Fin 28) ℂ) * X 26 * P39 + (2 : MvPolynomial (Fin 28) ℂ) * X 26 * P42 + (4 : MvPolynomial (Fin 28) ℂ) * X 24 * P45 + (-8 : MvPolynomial (Fin 28) ℂ) * X 24 * P46 + (16 : MvPolynomial (Fin 28) ℂ) * X 23 * P47 + (12 : MvPolynomial (Fin 28) ℂ) * X 24 * P48 + (20 : MvPolynomial (Fin 28) ℂ) * X 24 * P51 + (-16 : MvPolynomial (Fin 28) ℂ) * X 24 * P52 + (12 : MvPolynomial (Fin 28) ℂ) * X 24 * P53 + (1 : MvPolynomial (Fin 28) ℂ) * X 24 * P56 + (-4 : MvPolynomial (Fin 28) ℂ) * X 24 * P59 + (16 : MvPolynomial (Fin 28) ℂ) * X 20 * P62 + (4 : MvPolynomial (Fin 28) ℂ) * X 20 * P64 + (16 : MvPolynomial (Fin 28) ℂ) * X 22 * P66 + (4 : MvPolynomial (Fin 28) ℂ) * X 20 * P71 + (16 : MvPolynomial (Fin 28) ℂ) * X 16 * P72 + (4 : MvPolynomial (Fin 28) ℂ) * X 16 * P76 + (-32 : MvPolynomial (Fin 28) ℂ) * X 19 * P79 + (2 : MvPolynomial (Fin 28) ℂ) * X 16 * P82 + (24 : MvPolynomial (Fin 28) ℂ) * X 0 * P85 + (16 : MvPolynomial (Fin 28) ℂ) * X 1 * P85 + (8 : MvPolynomial (Fin 28) ℂ) * X 2 * P85 := by
    simp only [Qd, P22, P26, P31, P35, P39, P42, P45, P46, P47, P48, P51, P52, P53, P56, P59, P62, P64, P66, P71, P72, P76, P79, P82, P85]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P22_mem) (Ideal.mul_mem_left _ _ P26_mem)) (Ideal.mul_mem_left _ _ P31_mem)) (Ideal.mul_mem_left _ _ P35_mem)) (Ideal.mul_mem_left _ _ P39_mem)) (Ideal.mul_mem_left _ _ P42_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P47_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P59_mem)) (Ideal.mul_mem_left _ _ P62_mem)) (Ideal.mul_mem_left _ _ P64_mem)) (Ideal.mul_mem_left _ _ P66_mem)) (Ideal.mul_mem_left _ _ P71_mem)) (Ideal.mul_mem_left _ _ P72_mem)) (Ideal.mul_mem_left _ _ P76_mem)) (Ideal.mul_mem_left _ _ P79_mem)) (Ideal.mul_mem_left _ _ P82_mem)) (Ideal.mul_mem_left _ _ P85_mem)) (Ideal.mul_mem_left _ _ P85_mem)) (Ideal.mul_mem_left _ _ P85_mem))

set_option maxRecDepth 100000 in
theorem u3_25 : X 25 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 25 * Qd) = (-8 : MvPolynomial (Fin 28) ℂ) * X 27 * P25 + (-4 : MvPolynomial (Fin 28) ℂ) * X 27 * P30 + (-8 : MvPolynomial (Fin 28) ℂ) * X 26 * P37 + (2 : MvPolynomial (Fin 28) ℂ) * X 26 * P41 + (4 : MvPolynomial (Fin 28) ℂ) * X 25 * P45 + (-8 : MvPolynomial (Fin 28) ℂ) * X 25 * P46 + (4 : MvPolynomial (Fin 28) ℂ) * X 25 * P48 + (8 : MvPolynomial (Fin 28) ℂ) * X 23 * P50 + (-4 : MvPolynomial (Fin 28) ℂ) * X 25 * P51 + (-4 : MvPolynomial (Fin 28) ℂ) * X 25 * P53 + (1 : MvPolynomial (Fin 28) ℂ) * X 25 * P56 + (-4 : MvPolynomial (Fin 28) ℂ) * X 25 * P59 + (8 : MvPolynomial (Fin 28) ℂ) * X 22 * P63 + (4 : MvPolynomial (Fin 28) ℂ) * X 21 * P64 + (-8 : MvPolynomial (Fin 28) ℂ) * X 22 * P67 + (4 : MvPolynomial (Fin 28) ℂ) * X 21 * P71 + (8 : MvPolynomial (Fin 28) ℂ) * X 17 * P72 + (-16 : MvPolynomial (Fin 28) ℂ) * X 19 * P73 + (8 : MvPolynomial (Fin 28) ℂ) * X 18 * P75 + (8 : MvPolynomial (Fin 28) ℂ) * X 17 * P76 + (2 : MvPolynomial (Fin 28) ℂ) * X 17 * P82 + (8 : MvPolynomial (Fin 28) ℂ) * X 0 * P84 + (-4 : MvPolynomial (Fin 28) ℂ) * X 2 * P87 := by
    simp only [Qd, P25, P30, P37, P41, P45, P46, P48, P50, P51, P53, P56, P59, P63, P64, P67, P71, P72, P73, P75, P76, P82, P84, P87]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P25_mem) (Ideal.mul_mem_left _ _ P30_mem)) (Ideal.mul_mem_left _ _ P37_mem)) (Ideal.mul_mem_left _ _ P41_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P50_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P59_mem)) (Ideal.mul_mem_left _ _ P63_mem)) (Ideal.mul_mem_left _ _ P64_mem)) (Ideal.mul_mem_left _ _ P67_mem)) (Ideal.mul_mem_left _ _ P71_mem)) (Ideal.mul_mem_left _ _ P72_mem)) (Ideal.mul_mem_left _ _ P73_mem)) (Ideal.mul_mem_left _ _ P75_mem)) (Ideal.mul_mem_left _ _ P76_mem)) (Ideal.mul_mem_left _ _ P82_mem)) (Ideal.mul_mem_left _ _ P84_mem)) (Ideal.mul_mem_left _ _ P87_mem))

set_option maxRecDepth 100000 in
theorem u3_26 : X 26 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 26 * Qd) = (16 : MvPolynomial (Fin 28) ℂ) * X 27 * P34 + (16 : MvPolynomial (Fin 28) ℂ) * X 27 * P38 + (8 : MvPolynomial (Fin 28) ℂ) * X 27 * P43 + (4 : MvPolynomial (Fin 28) ℂ) * X 26 * P45 + (-8 : MvPolynomial (Fin 28) ℂ) * X 26 * P46 + (-4 : MvPolynomial (Fin 28) ℂ) * X 26 * P48 + (28 : MvPolynomial (Fin 28) ℂ) * X 26 * P51 + (-24 : MvPolynomial (Fin 28) ℂ) * X 26 * P52 + (4 : MvPolynomial (Fin 28) ℂ) * X 26 * P53 + (1 : MvPolynomial (Fin 28) ℂ) * X 26 * P56 + (-4 : MvPolynomial (Fin 28) ℂ) * X 26 * P58 + (-4 : MvPolynomial (Fin 28) ℂ) * X 26 * P59 + (-16 : MvPolynomial (Fin 28) ℂ) * X 23 * P62 + (-16 : MvPolynomial (Fin 28) ℂ) * X 24 * P63 + (16 : MvPolynomial (Fin 28) ℂ) * X 25 * P66 + (-16 : MvPolynomial (Fin 28) ℂ) * X 24 * P67 + (8 : MvPolynomial (Fin 28) ℂ) * X 23 * P71 + (-16 : MvPolynomial (Fin 28) ℂ) * X 20 * P75 + (-16 : MvPolynomial (Fin 28) ℂ) * X 16 * P84 + (-16 : MvPolynomial (Fin 28) ℂ) * X 17 * P85 + (16 : MvPolynomial (Fin 28) ℂ) * X 19 * P86 + (32 : MvPolynomial (Fin 28) ℂ) * X 19 * P89 + (-32 : MvPolynomial (Fin 28) ℂ) * X 0 * P94 + (-16 : MvPolynomial (Fin 28) ℂ) * X 1 * P94 := by
    simp only [Qd, P34, P38, P43, P45, P46, P48, P51, P52, P53, P56, P58, P59, P62, P63, P66, P67, P71, P75, P84, P85, P86, P89, P94]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P34_mem) (Ideal.mul_mem_left _ _ P38_mem)) (Ideal.mul_mem_left _ _ P43_mem)) (Ideal.mul_mem_left _ _ P45_mem)) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P58_mem)) (Ideal.mul_mem_left _ _ P59_mem)) (Ideal.mul_mem_left _ _ P62_mem)) (Ideal.mul_mem_left _ _ P63_mem)) (Ideal.mul_mem_left _ _ P66_mem)) (Ideal.mul_mem_left _ _ P67_mem)) (Ideal.mul_mem_left _ _ P71_mem)) (Ideal.mul_mem_left _ _ P75_mem)) (Ideal.mul_mem_left _ _ P84_mem)) (Ideal.mul_mem_left _ _ P85_mem)) (Ideal.mul_mem_left _ _ P86_mem)) (Ideal.mul_mem_left _ _ P89_mem)) (Ideal.mul_mem_left _ _ P94_mem)) (Ideal.mul_mem_left _ _ P94_mem))

set_option maxRecDepth 100000 in
theorem u3_27 : X 27 * Qd ∈ quadraticIdeal rel := by
  have h : ((4 : ℕ) : MvPolynomial (Fin 28) ℂ) * (X 27 * Qd) = (4 : MvPolynomial (Fin 28) ℂ) * X 27 * P45 + (8 : MvPolynomial (Fin 28) ℂ) * X 27 * P46 + (-4 : MvPolynomial (Fin 28) ℂ) * X 27 * P48 + (-4 : MvPolynomial (Fin 28) ℂ) * X 27 * P51 + (-8 : MvPolynomial (Fin 28) ℂ) * X 27 * P52 + (4 : MvPolynomial (Fin 28) ℂ) * X 27 * P53 + (1 : MvPolynomial (Fin 28) ℂ) * X 27 * P56 + (4 : MvPolynomial (Fin 28) ℂ) * X 27 * P58 + (-4 : MvPolynomial (Fin 28) ℂ) * X 27 * P59 + (-16 : MvPolynomial (Fin 28) ℂ) * X 26 * P60 + (16 : MvPolynomial (Fin 28) ℂ) * X 26 * P65 + (-4 : MvPolynomial (Fin 28) ℂ) * X 26 * P69 + (-16 : MvPolynomial (Fin 28) ℂ) * X 23 * P72 + (-16 : MvPolynomial (Fin 28) ℂ) * X 24 * P73 + (-32 : MvPolynomial (Fin 28) ℂ) * X 25 * P74 + (16 : MvPolynomial (Fin 28) ℂ) * X 23 * P76 + (16 : MvPolynomial (Fin 28) ℂ) * X 24 * P78 + (32 : MvPolynomial (Fin 28) ℂ) * X 25 * P79 + (4 : MvPolynomial (Fin 28) ℂ) * X 23 * P82 + (-16 : MvPolynomial (Fin 28) ℂ) * X 20 * P84 + (-16 : MvPolynomial (Fin 28) ℂ) * X 21 * P85 + (-16 : MvPolynomial (Fin 28) ℂ) * X 22 * P86 + (16 : MvPolynomial (Fin 28) ℂ) * X 20 * P87 + (32 : MvPolynomial (Fin 28) ℂ) * X 22 * P89 + (-16 : MvPolynomial (Fin 28) ℂ) * X 16 * P93 + (32 : MvPolynomial (Fin 28) ℂ) * X 18 * P94 + (-8 : MvPolynomial (Fin 28) ℂ) * X 1 * P99 := by
    simp only [Qd, P45, P46, P48, P51, P52, P53, P56, P58, P59, P60, P65, P69, P72, P73, P74, P76, P78, P79, P82, P84, P85, P86, P87, P89, P93, P94, P99]
    ring
  apply mem_of_natCast_mul 4 (by norm_num)
  rw [h]
  exact (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ P45_mem) (Ideal.mul_mem_left _ _ P46_mem)) (Ideal.mul_mem_left _ _ P48_mem)) (Ideal.mul_mem_left _ _ P51_mem)) (Ideal.mul_mem_left _ _ P52_mem)) (Ideal.mul_mem_left _ _ P53_mem)) (Ideal.mul_mem_left _ _ P56_mem)) (Ideal.mul_mem_left _ _ P58_mem)) (Ideal.mul_mem_left _ _ P59_mem)) (Ideal.mul_mem_left _ _ P60_mem)) (Ideal.mul_mem_left _ _ P65_mem)) (Ideal.mul_mem_left _ _ P69_mem)) (Ideal.mul_mem_left _ _ P72_mem)) (Ideal.mul_mem_left _ _ P73_mem)) (Ideal.mul_mem_left _ _ P74_mem)) (Ideal.mul_mem_left _ _ P76_mem)) (Ideal.mul_mem_left _ _ P78_mem)) (Ideal.mul_mem_left _ _ P79_mem)) (Ideal.mul_mem_left _ _ P82_mem)) (Ideal.mul_mem_left _ _ P84_mem)) (Ideal.mul_mem_left _ _ P85_mem)) (Ideal.mul_mem_left _ _ P86_mem)) (Ideal.mul_mem_left _ _ P87_mem)) (Ideal.mul_mem_left _ _ P89_mem)) (Ideal.mul_mem_left _ _ P93_mem)) (Ideal.mul_mem_left _ _ P94_mem)) (Ideal.mul_mem_left _ _ P99_mem))

/-- **The D₄ type data**, with U3 checked in Lean. -/
def D4data : DeligneCarrierData where
  n := 28
  ρ := Fin 105
  rel := rel
  cas := cas
  u3 a := by
    rw [cas_eq]
    fin_cases a
    · exact u3_0
    · exact u3_1
    · exact u3_2
    · exact u3_3
    · exact u3_4
    · exact u3_5
    · exact u3_6
    · exact u3_7
    · exact u3_8
    · exact u3_9
    · exact u3_10
    · exact u3_11
    · exact u3_12
    · exact u3_13
    · exact u3_14
    · exact u3_15
    · exact u3_16
    · exact u3_17
    · exact u3_18
    · exact u3_19
    · exact u3_20
    · exact u3_21
    · exact u3_22
    · exact u3_23
    · exact u3_24
    · exact u3_25
    · exact u3_26
    · exact u3_27

end

end VOA.DeligneAudit.DeligneCarrier.D4

section AxiomAudit
open VOA.DeligneAudit.DeligneCarrier.D4
#print axioms D4data
end AxiomAudit
