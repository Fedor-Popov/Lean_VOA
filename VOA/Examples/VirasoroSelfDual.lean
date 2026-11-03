/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroSimple
import VOA.Examples.LeeYangRigidity
import VOA.Modules.StronglyRational

/-!
# `L(c,0)` is self-dual for **every** central charge — a nontrivial witness

`Modules/StronglyRational.lean` replaces the vacuous `Contragredient.SelfContragredient` with
`VertexOperatorAlgebra.SelfDual` (McRae, arXiv:2108.01898v3, §2.2, clause (2): the existence of a
nondegenerate invariant bilinear form).  `Examples/TrivialStronglyRational.lean` witnesses the
whole `StronglyRational` bundle, but only at `trivialVOA = ℂ𝟙`, where every conjunct is true for
degenerate reasons.  A sceptic could reasonably ask whether `SelfDual` has any *nontrivial* models
in this repository.

It does — an infinite family.  For **every** `c ∈ ℂ`, the simple Virasoro VOA `L(c,0)`
(`VirSimple.virasoroSimple c`, `Examples/VirasoroSimple.lean`) is self-dual:

* it is **simple** for every `c` — `VirSimple.virasoroSimple_isSimple`;
* its vacuum survives the quotient — `VirSimple.virasoroSimple_vacuum_ne_zero`;
* it is of **strong CFT type**, `L₁𝒱₁ = 0`, *vacuously*, because `𝒱₁ = 0`: the creation monomials
  `L₋ₙ₁₋₂⋯L₋ₙᵣ₋₂|0⟩` have energy `≥ 2` unless the word is empty
  (`VirModule.gradingVir_one`), and the quotient grading is the image of the universal one
  (`VirSimple.virasoroSimple_grading`);
* so `selfDual_of_L_one_grading_one_eq_zero` builds the canonical FHL form and simplicity makes it
  nondegenerate.

⚠ **This is a witness for `SelfDual` only, not for `StronglyFinite`.**  The missing conjunct is
`C₂`-cofiniteness, which for `L(c,0)` holds exactly at the minimal-model central charges
`c = 1 − 6(p−q)²/(pq)` and is not available in this repository for any `c`.  Claiming
`StronglyFinite (virasoroSimple c)` would be false for generic `c` and unproved for special `c`,
so it is not claimed.

⚠ Note also that `SelfDual` here is genuinely doing work even though `𝒱₁ = 0`: the *content* is the
nondegeneracy of the canonical form, which comes from simplicity
(`invariantForm_nondegenerate_FHL`, H. Li, J. Pure Appl. Algebra **96** (1994) 279–297).  For the
**universal** VOA `V(c,0)` at a degenerate `c` the same form exists but is **degenerate** — its
radical is the maximal proper ideal (`LiRadical.leftRadical_eq_maxGradedIdeal`), which is nonzero
exactly when `V(c,0) ≠ L(c,0)`.  So the family below separates the two.

## Status
`sorry`-free, `admit`-free, `native_decide`-free, no new axioms, `VOA.pbw`-free.
-/

namespace VOA

namespace VirSimple

variable (c : ℂ)

/-- `L(c,0)₁ = 0`: the weight-one space of the simple Virasoro VOA vanishes, because it is the
image of `V(c,0)₁ = 0` under the quotient map. -/
theorem virasoroSimple_grading_one : (virasoroSimple c).grading 1 = ⊥ := by
  have h : (VirModule.virasoroVOA c).grading 1 = ⊥ := VirModule.gradingVir_one c
  rw [virasoroSimple_grading, h, Submodule.map_bot]

/-- **`L(c,0)` is of strong CFT type** (Dong–Mason, arXiv:math/0201318v1, §2, eq. (2.2)):
`L₁𝒱₁ = 0`, here vacuously since `𝒱₁ = 0`. -/
theorem virasoroSimple_qp :
    ∀ v, v ∈ (virasoroSimple c).grading 1 → (virasoroSimple c).L 1 v = 0 := by
  intro v hv
  rw [virasoroSimple_grading_one c, Submodule.mem_bot] at hv
  rw [hv, map_zero]

/-- **`L(c,0)` is self-dual, for every central charge `c`.**

A nontrivial family of models for `VertexOperatorAlgebra.SelfDual` — the predicate that replaces
the vacuous `SelfContragredient`.  By `selfDual_iff` this is exactly the statement that `L(c,0)` is
of strong CFT type, which Dong–Mason §2 identify with `L(c,0)′ ≅ L(c,0)`. -/
theorem virasoroSimple_selfDual : (virasoroSimple c).SelfDual :=
  VertexOperatorAlgebra.selfDual_of_L_one_grading_one_eq_zero
    (virasoroSimple_vacuum_ne_zero c) (virasoroSimple_qp c) (virasoroSimple_isSimple c)

end VirSimple

end VOA
