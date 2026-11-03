/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.LatticeC2
import VOA.Classification.COne.LatticeRational2

/-!
# `V_{2m}` is strongly rational

The rank-one lattice VOA `V_{2m}` (`√(2m) ℤ`, `m ≥ 1`) is strongly rational: simple, self-dual,
`C₂`-cofinite (`V2m_stronglyFinite`, `LatticeSimple.lean` + `LatticeC2.lean`) and admissibly
rational (`V2m_admissiblyRational`, `LatticeRational2.lean`). Unconditional; `#print axioms` is
`[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA.Classification.COne

/-- **`V_{2m}` is strongly rational** (Dong 1993; Dong–Li–Mason), for every `m ≥ 1`. -/
theorem V2m_stronglyRational (m : ℕ) (hm : 1 ≤ m) : StronglyRational (V2m m hm) :=
  { V2m_stronglyFinite m hm with rational := V2m_admissiblyRational hm }

end VOA.Classification.COne
