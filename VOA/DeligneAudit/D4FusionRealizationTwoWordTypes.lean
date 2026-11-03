/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoIntegerData

/-! Literal-data types for actual word steps and full action certificates. -/
namespace VOA.DeligneAudit.D4Two.Certificate

structure WordNode where
  level : ℕ
  parent : ℕ
  color : ℕ
  mode : ℕ
  vector : SV
  deriving Inhabited

/-- The index of a case determines the source word, mode and colour.
Each pair is a target-word index followed by its integer coefficient. -/
structure ActionCase where
  denominator : ℤ
  terms : List (ℕ × ℤ)
  deriving Inhabited

end VOA.DeligneAudit.D4Two.Certificate
