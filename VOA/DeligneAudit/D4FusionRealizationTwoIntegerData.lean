/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Data.Int.Basic

/-! The literal two-site certificate data need only integer and list types. -/
namespace VOA.DeligneAudit.D4Two.Certificate

abbrev SV := List (ℕ × ℤ)

/-- Metadata for actual current words. A noninitial parent precedes its child. -/
structure Entry where
  level : ℕ
  parent : ℕ
  color : ℕ
  mode : ℕ
  vector : SV
  dual : SV
  denominator : ℤ
  weight : ℤ
  deriving Inhabited

end VOA.DeligneAudit.D4Two.Certificate
