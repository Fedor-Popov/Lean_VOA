/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2BelowCriticalCompact
import VOA.Examples.AffineSl2BelowCriticalNondegenerate

/-!
# Below-critical graded unitarity of `V^k(sl₂)` for the ordinary current-PBW flag

The assembled energy induction of the below-critical, no-wall graded-unitarity argument:

* weight `E < 0` is empty;
* at weight `E ≥ 0`, if every lower weight has the graded-unitary layer signs **at every real
  level `k < -2`**, then the prefix no-wall lemma (`layerNondegenerate_of_lower`) together with
  the below-critical nondegeneracy of the full vacuum form (`universalForm_separating_of_lt`)
  makes every flag step at weight `E` nondegenerate at every `k < -2`;
* the layer signs at weight `E` are then transported along the connected interval
  `(-∞, -2)` from a large-negative-level anchor.

## What is proved and what is assumed

`universal_gradedUnitary_belowCritical` is `#print axioms`-clean but, *as stated in this file*,
**conditional** on three named inputs (all three are proved downstream for the compact family; see
the end of this docstring):

1. a family `R` of real structures with `IsCompactRealStructure (R k hk)` (the compact
   conjugation; such a family, `compactRealFamily`, is constructed in
   `AffineSl2BelowCriticalRealStructure`, which also states the specialised theorem
   `universal_gradedUnitary_belowCritical_compact` without this hypothesis);
2. `LayerSignAnchor R` — at each fixed weight, the layer signs hold for all sufficiently
   negative real `k` (the large-`λ` Wick asymptotics of the source note);
3. `LayerSignRigidity R` — at each fixed weight, if every flag step is nondegenerate at every
   real `k < -2`, the layer signs cannot change along `(-∞, -2)` (the continuity / constant
   inertia step of the source note).

Everything else in the induction — the ordinary flag, its mode properties, the Hermitian
Sugawara identity, the prefix no-wall lemma, and the nondegeneracy of the full vacuum form for
every real `k < -2` — is proved, in `AffineSl2BelowCriticalFlag`,
`AffineSl2BelowCriticalNoWall`, `AffineSl2BelowCriticalCompact` and
`AffineSl2BelowCriticalNondegenerate`.

All three inputs are discharged downstream for the constructed compact family:
`compactRealFamily_isCompact` (`AffineSl2BelowCriticalRealStructure`),
`layerSignRigidity_compact` (`AffineSl2BelowCriticalRigidity`) and `layerSignAnchor_compact`
(`AffineSl2BelowCriticalAnchor`), which also states the hypothesis-free theorem
`universal_gradedUnitary_belowCritical_unconditional`.  This file keeps the induction abstract
in the family `R` so that the three analytic inputs stay visible as separate statements.
-/

namespace VOA

namespace AffineSl2BelowCritical

open AffineVOA AffineVOA.Inst AffineSl2GeneralRigidity

noncomputable section

/-- A family of real structures on the universal algebras at real levels below critical. -/
abbrev RealFamily : Type :=
  ∀ (x : ℝ) (hx : x < -2), RealStructure (universal (x : ℂ) (noncritical_of_lt hx))

/-- The graded-unitary layer-sign clause (vi) at weight `E` and real level `x < -2`. -/
def LayerSigns (R : RealFamily) (x : ℝ) (hx : x < -2) (E : ℤ) : Prop :=
  LayerPositive (ordinaryFlag (x : ℂ) (noncritical_of_lt hx)) E
    (LiRadical.gradedForm (universalForm (x : ℂ) (noncritical_of_lt hx)) E)
    (gradedSesq (universalForm (x : ℂ) (noncritical_of_lt hx)) (R x hx) E)

/-- Clause (iv) at weight `E` and real level `x < -2`. -/
def LayerNondeg (x : ℝ) (hx : x < -2) (E : ℤ) : Prop :=
  LayerNondegenerate (ordinaryFlag (x : ℂ) (noncritical_of_lt hx)) E
    (LiRadical.gradedForm (universalForm (x : ℂ) (noncritical_of_lt hx)) E)

/-- **Named input (anchor)**, proved for the compact family by `layerSignAnchor_compact`
(`AffineSl2BelowCriticalAnchor`).  At each fixed weight the graded-unitary layer signs hold for
every sufficiently negative real level.  (Source: the large-`λ` limit, in which the length-`r`
block of the rescaled Gram matrix tends to `(-1)^r` times the positive Wick metric and the
cross-length blocks vanish.) -/
def LayerSignAnchor (R : RealFamily) : Prop :=
  ∀ E : ℤ, ∃ K : ℝ, ∀ (x : ℝ) (hx : x < -2), x < K → LayerSigns R x hx E

/-- **Named input (rigidity)**, proved for the compact family by `layerSignRigidity_compact`
(`AffineSl2BelowCriticalRigidity`).  At each fixed weight, if every flag step is nondegenerate
at every real level `x < -2`, then the layer signs at one such level imply them at every such
level.  (Source: the Gram entries are polynomial in the level in a fixed flag-adapted PBW basis,
and a continuous family of nondegenerate Hermitian forms on the connected interval
`(-∞, -2)` has constant inertia.) -/
def LayerSignRigidity (R : RealFamily) : Prop :=
  ∀ E : ℤ, (∀ (x : ℝ) (hx : x < -2), LayerNondeg x hx E) →
    ∀ (x₀ : ℝ) (hx₀ : x₀ < -2) (x₁ : ℝ) (hx₁ : x₁ < -2),
      LayerSigns R x₀ hx₀ E → LayerSigns R x₁ hx₁ E

/-- Negative weights carry the layer signs vacuously. -/
theorem layerSigns_of_neg (R : RealFamily) (x : ℝ) (hx : x < -2) {E : ℤ} (hE : E < 0) :
    LayerSigns R x hx E := by
  intro p u _ hu
  exfalso
  apply hu
  have h0 : ∀ y : WakModule (x : ℂ),
      y ∈ (universal (x : ℂ) (noncritical_of_lt hx)).grading E → y = 0 := fun y hy => by
    rw [(universal (x : ℂ) (noncritical_of_lt hx)).positivity E hE] at hy
    exact (Submodule.mem_bot ℂ).mp hy
  exact Subtype.ext (h0 _ u.2)

/-- **One step of the energy induction.**  Lower-weight layer signs at every level give
nondegeneracy of every flag step at weight `E` at every level (no-wall lemma + full
nondegeneracy below critical), and then the layer signs at weight `E` (anchor + rigidity). -/
theorem step (R : RealFamily) (hR : ∀ x hx, IsCompactRealStructure (R x hx))
    (hanchor : LayerSignAnchor R) (hrigid : LayerSignRigidity R) (E : ℤ)
    (hlow : ∀ m : ℕ, 0 < m → ∀ (x : ℝ) (hx : x < -2), LayerSigns R x hx (E - m)) :
    (∀ (x : ℝ) (hx : x < -2), LayerNondeg x hx E) ∧
      ∀ (x : ℝ) (hx : x < -2), LayerSigns R x hx E := by
  have hnd : ∀ (x : ℝ) (hx : x < -2), LayerNondeg x hx E := fun x hx =>
    layerNondegenerate_of_lower (hR x hx) E (universalForm_separating_of_lt hx E)
      (fun m hm => hlow m hm x hx)
  refine ⟨hnd, fun x hx => ?_⟩
  obtain ⟨K, hK⟩ := hanchor E
  have hx₀ : min K (-2) - 1 < -2 := by
    have := min_le_right K (-2); linarith
  have hx₀K : min K (-2) - 1 < K := by
    have := min_le_left K (-2); linarith
  exact hrigid E hnd _ hx₀ x hx (hK _ hx₀ hx₀K)

/-- The layer signs at every weight, by strong induction on the weight. -/
theorem layerSigns_all (R : RealFamily) (hR : ∀ x hx, IsCompactRealStructure (R x hx))
    (hanchor : LayerSignAnchor R) (hrigid : LayerSignRigidity R) :
    ∀ (n : ℕ) (E : ℤ), E < n → ∀ (x : ℝ) (hx : x < -2), LayerSigns R x hx E := by
  intro n
  induction n with
  | zero =>
      intro E hE x hx
      exact layerSigns_of_neg R x hx (by exact_mod_cast hE)
  | succ n ih =>
      intro E hE
      by_cases hEn : E < n
      · exact ih E hEn
      · have hEeq : E = n := by push_cast at hE; omega
        exact (step R hR hanchor hrigid E (fun m hm => ih (E - m) (by omega))).2

/-- **Below-critical graded unitarity of the universal affine `sl₂` vacuum VOA for the
ordinary current-PBW flag** — conditional on the three named inputs of the file docstring.

For every real `k < -2`, `V^k(sl₂)` with its normalized canonical invariant form, a compact
real structure and the ordinary current-length flag is graded-unitary (ABLR clauses (iv) and
(vi) at every weight; clause (v) is then `layerDecomposition`).

⚠ `#print axioms`-clean but **conditional on** `hR`, `hanchor`, `hrigid`.  Not unconditional. -/
theorem universal_gradedUnitary_belowCritical (R : RealFamily)
    (hR : ∀ x hx, IsCompactRealStructure (R x hx))
    (hanchor : LayerSignAnchor R) (hrigid : LayerSignRigidity R)
    (k : ℝ) (hk : k < -2) :
    GradedUnitary (universalForm (k : ℂ) (noncritical_of_lt hk)) (R k hk)
      (ordinaryFlag (k : ℂ) (noncritical_of_lt hk)) := by
  intro E
  have hlow : ∀ m : ℕ, 0 < m → ∀ (x : ℝ) (hx : x < -2), LayerSigns R x hx (E - m) :=
    fun m _ x hx => layerSigns_all R hR hanchor hrigid (E.toNat + 1) (E - m) (by omega) x hx
  exact ⟨(step R hR hanchor hrigid E hlow).1 k hk,
    layerSigns_all R hR hanchor hrigid (E.toNat + 1) E (by omega) k hk⟩

end

end AffineSl2BelowCritical

end VOA
