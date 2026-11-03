/-
Copyright (c) 2026 Leonardo Rastelli, Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.DeformationGraded

/-!
# Localising the first-order Jacobi identity: the cocycle condition as a finite linear system

`Core.DeformationGraded` reduced the *coboundary* side of first-order deformation theory to finite
linear algebra, but left the *cocycle* side global: `gradedCocyclesAt W a b c` is defined as the
**image** of `gradedCocycles W` — a submodule of the infinite-dimensional `Cochain 𝒱` cut out by
`JacobiAx`, an identity of `finsum`s over `ℤ` quantified over all of `𝒱³` — under the component
map.  There was no local characterisation of the cocycle condition at a tridegree anywhere.

This file supplies one.  For a **graded** cochain the first-order Jacobi identity is *equivalent*
to a family of explicit **finite** linear equations on the graded components
(`jacobiAx_iff_localJacobiAt`), and together with the localised vacuum and creation axioms this
exhibits `gradedCocycles W` as an intersection of kernels of linear maps into
finite-dimensional spaces (`gradedCocycles_eq_iInf`).

## The identity, and which components enter it

Written with `cmode f` for the deformed products `u¹₍ₙ₎v`, `JacobiAx W f` is

`∑ᶠ i, (-1)ⁱ C(ℓ,i)·( f_u^{(ℓ+m-i)}(v₍ₙ₊ᵢ₎x) + u₍ℓ₊ₘ₋ᵢ₎(f_v^{(n+i)}x)`
`                    − (-1)^ℓ·[ f_v^{(ℓ+n-i)}(u₍ₘ₊ᵢ₎x) + v₍ℓ₊ₙ₋ᵢ₎(f_u^{(m+i)}x) ] )`
`  = ∑ᶠ i, C(m,i)·( (f_u^{(ℓ+i)}v)₍ₘ₊ₙ₋ᵢ₎x + f_{(u₍ℓ₊ᵢ₎v)}^{(m+n-i)}x )`.

Fix `u ∈ 𝒱ₐ`, `v ∈ 𝒱_b`, `x ∈ 𝒱_d`.  Each of the six occurrences of `f` is then a *determinate*
graded component (`cmode_eq_gradedComponent`: the tridegree of `cmode f y k z` is
`(grade y, grade z, grade y + grade z − k − 1)`).  Writing `e := jacTarget a b d ℓ m n
= a+b+d−ℓ−m−n−2`, the six families are

| term | component of `f` at tridegree | mode |
|---|---|---|
| `f_u^{(ℓ+m-i)}(v₍ₙ₊ᵢ₎x)` | `(a, b+d−n−i−1, e)` | `ℓ+m−i` |
| `u₍ℓ₊ₘ₋ᵢ₎(f_v^{(n+i)}x)` | `(b, d, b+d−n−i−1)` | `n+i` |
| `f_v^{(ℓ+n-i)}(u₍ₘ₊ᵢ₎x)` | `(b, a+d−m−i−1, e)` | `ℓ+n−i` |
| `v₍ℓ₊ₙ₋ᵢ₎(f_u^{(m+i)}x)` | `(a, d, a+d−m−i−1)` | `m+i` |
| `(f_u^{(ℓ+i)}v)₍ₘ₊ₙ₋ᵢ₎x` | `(a, b, a+b−ℓ−i−1)` | `ℓ+i` |
| `f_{(u₍ℓ₊ᵢ₎v)}^{(m+n-i)}x` | `(a+b−ℓ−i−1, d, e)` | `m+n−i` |

The **target grade `e` does not depend on `i`** (`jac1L_mem_grading`, `jac1R_mem_grading`): the
identity is grade-homogeneous, as it must be.

## The crux: the sum **is** finite once the three grades are fixed

Both `finsum`s are cut off from **both** sides, and both cut-offs are explicit:

* **below**, for every cochain: `cbz ℓ i = 0` for `i < 0`, so only `i ≥ 0` contributes
  (`jac1L_eq_zero_of_neg`, `jac1R_eq_zero_of_neg`);
* **above**, for a *graded* cochain and homogeneous inputs: every summand factors through a
  product whose target grade falls linearly in `i`, and `𝒱ₖ = 0` for `k < 0` (VOA4).  Hence
  `jac1L … i = 0` for `i > jacBoundL a b d m n = max (b+d−n−1) (a+d−m−1)`, and
  `jac1R … i = 0` for `i > jacBoundR a b ℓ = a+b−ℓ−1`
  (`jac1L_eq_zero_of_gt`, `jac1R_eq_zero_of_gt`).

So `∑ᶠ` becomes `∑ i ∈ Finset.Icc 0 N` with `N` an explicit function of the grades
(`jacTotL_eq_finsetSum`, `jacTotR_eq_finsetSum`).  This is strictly stronger than the
pre-existing `jacLHS_support_finite`/`jacRHS_support_finite`, which produce an *existential* bound
`N` out of the truncation axiom and therefore cannot be written down as a system.

## The coupling: what "finite" does and does not mean here

* **Each equation is finite.**  At fixed `(a,b,d,ℓ,m,n)` the equation involves the finitely many
  components listed in the table above — at most `4·(jacBoundL a b d m n + 1)` from the four left
  families and `2·(jacBoundR a b ℓ + 1)` from the two right families — each of them an element of
  a finite-dimensional block `GradedCochain W · · ·`.
* **⚠ One tridegree is not self-contained.**  The equation at `(a,b,d,ℓ,m,n)` couples the six
  families above, which run over *different* tridegrees.  So the cocycle condition is **not** a
  kernel condition on the single block `GradedCochain W a b c`; it is a kernel condition on the
  total family.  That is why `gradedCocyclesAt W a b c` is presented here as the
  `gradedComponent`-image of an explicit kernel (`gradedCocyclesAt_eq_map_iInf`), not as a kernel.
* **⚠ For fixed input grades there are still infinitely many equations.**  Three explicit cones
  are automatic (`localJacobiAt_of_outside_cone`): `a,b,d < 0`; `ℓ+m+n > a+b+d−2` (negative target
  grade); and `ℓ > a+b−1 ∧ n > b+d−1 ∧ m > a+d−1` (both ranges empty).  What remains is still
  infinite, because `ℓ` is bounded above but **not below**: as `ℓ → −∞` the target grade
  `e = a+b+d−ℓ−m−n−2 → +∞` and the equation constrains components at ever deeper tridegrees.
  This is the exact analogue, on the cocycle side, of the "not bounded below" warning in
  `Core.DeformationGraded`.

  ⚠ **What would remove this last infinity** is the classical reduction of the Borcherds identity
  to finitely many of its specialisations (commutator formula plus associativity/iterate formula,
  the content of `Core.Reconstruction`/`Core.WeakAssoc` in the undeformed setting).  Linearising
  that reduction would cut the `ℓ`-family down to a bounded window and make the whole system
  finite per tridegree.  It is **not** done here and is the natural next task.

## Main results

* `smul_eq_zero_of_grading_lt` — VOA4 positivity in product form.
* `jacBoundL`, `jacBoundR`, `jacTarget` — the explicit index bounds and target grade.
* `jac1L_eq_zero_of_gt`, `jac1R_eq_zero_of_gt`, `jacTotL_eq_finsetSum`,
  `jacTotR_eq_finsetSum` — **the crux**: the `finsum`s are explicit `Finset.sum`s.
* `LocalJacobiAt` — the local (finite) first-order Jacobi equation.
* `jacobiAx_iff_localJacobiAt` — **the localisation**, both directions.
* `eq_of_homogeneous₃` — the trilinear companion of `eq_of_homogeneous`.
* `VacuumAxLocal`, `CreationAxLocal`, `vacuum_iff_local`, `creationAx_iff_local` — the other
  two axioms localised; `creationAxLocal_of_neg` shows only `0 ≤ c ≤ a` carries information.
* `mem_cocycles_iff_local`, `mem_gradedCocycles_iff_local` — all four axioms as local data
  (truncation is free by `truncated_of_graded`).
* `jac1L_mem_grading`, `jac1R_mem_grading`, `jacDefect_mem_grading` — grade-homogeneity.
* `localJacobiDefect` — the local system as a linear map into a finite-dimensional space of
  trilinear maps; `mem_ker_localJacobiDefect` — its kernel is `LocalJacobiAt`.
* `gradedCocycles_eq_iInf` — `gradedCocycles` is an intersection of explicit kernels.
* `gradedCocyclesAt_eq_map_iInf` — `gradedCocyclesAt` as the image of that kernel.
* `localJacobiAt_of_outside_cone` — where the system is automatically satisfied.
* `cmode_eq_gradedComponent` — every occurrence of `f` is a graded component.
* `mem_gradedCocyclesAt_of_local`, `deformationSpaceAt_ne_zero_of_local`,
  `not_isRigid_of_local` — the payoff: **solve the finite system, compare with the computable
  coboundary block, and a mismatch disproves `IsRigid`.**
* `localJacobiAt_of_isCoboundary` — consistency: every field redefinition solves the system.
* `gradedCocyclesAt_eq_top_of_coboundaries_top` — a full coboundary block forces a full cocycle
  block (how the quoted `virasoroVOA` cocycle dimensions are actually pinned down).

## ⚠ Scope, stated honestly

* **Proved.**  The localisation is an honest `↔` for every VOA and every graded cochain, and the
  index bounds are explicit and hypothesis-free.  The cocycle space is an intersection of kernels
  of maps into finite-dimensional spaces.
* **Not proved.**  (i) No reduction of the `ℓ`-family, so the system at fixed input grades is
  still infinite (see "The coupling" above).  (ii) `gradedCocyclesAt W a b c` is an *image* of a
  kernel, not a kernel — computing its dimension at one tridegree still needs the coupled system.
  (iii) No concrete VOA computation is run here: no dimension at `(2,2,3)`/`(2,2,4)` is recomputed
  from the local system, and no nonzero `DeformationSpaceAt` is exhibited.  What is supplied is
  the machinery plus the detector (`not_isRigid_of_local`) that such a computation would feed.
* **Nothing here bears on `GradedToGlobalRigidity`**, whose obstruction (one `φ` per tridegree
  versus one global `φ`) lives entirely on the coboundary side and is untouched.

## Status
Hole-free.  No `sorry`, no `admit`, no `native_decide`, no `unsafe`, no new axioms;
`#print axioms` = `[propext, Classical.choice, Quot.sound]` on all 26 main declarations
(in particular `VOA.pbw` is *not* used).

## Dependencies
`Core.DeformationGraded` (`Cochain`, `cmode`, the four axioms, `gradedCochains`,
`gradedCocycles`, `gradedComponent`, `gradedCocyclesAt`, `DeformationSpaceAt`,
`truncated_of_graded`, `gradedCochain_vanishing_of_gt`), and transitively `Core.Deformation` and
`Core.Borcherds`.

## References
Gannon §5.1.3, eq. 5.1.7b (the identity being linearised); `Core.Deformation` file docstring for
the derivation of the order-`t` axioms.
-/

-- `DeformationSpaceAt` is a quotient of a submodule *of a submodule*, so the instance search
-- for `AddCommGroup ↥(gradedCocyclesAt …)` needs one extra level of pending synthesis.
set_option maxSynthPendingDepth 3

namespace VOA

namespace Deform

open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Vanishing above the grading bound -/

/-- **VOA4 positivity, in product form.**  If `u ∈ 𝒱ₐ` and `v ∈ 𝒱_b` then `u₍ₙ₎v = 0` as soon as
`n > a + b - 1`, because the target grade `a + b - n - 1` is then negative.  This is the
undeformed companion of `gradedCochain_vanishing_of_gt`, and it is the single fact that makes the
first-order Jacobi sums *finite at fixed grades*. -/
theorem smul_eq_zero_of_grading_lt (W : VertexOperatorAlgebra 𝒱) {a b : ℤ} {u v : 𝒱}
    (hu : u ∈ W.grading a) (hv : v ∈ W.grading b) {n : ℤ} (hn : a + b - 1 < n) :
    W.smul u n v = 0 := by
  have h := W.toPreVertexAlgebra.smul_mem_grading hu hv n
  rw [W.positivity (a + b - n - 1) (by omega)] at h
  exact (Submodule.mem_bot ℂ).mp h

/-! ## The summands of the first-order Jacobi identity, named -/

/-- The `i`-th summand of the **left**-hand side of the first-order (order-`t`) Jacobi identity
`JacobiAx`.  Compare `jacL`, its undeformed analogue: this is the Leibniz variation, carrying one
insertion of the cochain `f` in each of the four possible places. -/
noncomputable def jac1L (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u v x : 𝒱)
    (ℓ m n i : ℤ) : 𝒱 :=
  (negOnePow i * cbz ℓ i) •
    (cmode f u (ℓ + m - i) (W.smul v (n + i) x)
      + W.smul u (ℓ + m - i) (cmode f v (n + i) x)
      - negOnePow ℓ •
        (cmode f v (ℓ + n - i) (W.smul u (m + i) x)
          + W.smul v (ℓ + n - i) (cmode f u (m + i) x)))

/-- The `i`-th summand of the **right**-hand side of the first-order Jacobi identity. -/
noncomputable def jac1R (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u v x : 𝒱)
    (ℓ m n i : ℤ) : 𝒱 :=
  cbz m i •
    (W.smul (cmode f u (ℓ + i) v) (m + n - i) x
      + cmode f (W.smul u (ℓ + i) v) (m + n - i) x)

/-- The full left-hand side of `JacobiAx`, as a function of the three vectors. -/
noncomputable def jacTotL (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u v x : 𝒱)
    (ℓ m n : ℤ) : 𝒱 := ∑ᶠ i : ℤ, jac1L W f u v x ℓ m n i

/-- The full right-hand side of `JacobiAx`, as a function of the three vectors. -/
noncomputable def jacTotR (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u v x : 𝒱)
    (ℓ m n : ℤ) : 𝒱 := ∑ᶠ i : ℤ, jac1R W f u v x ℓ m n i

/-- `JacobiAx` in the `jacTotL`/`jacTotR` notation: pure renaming, `Iff.rfl`. -/
theorem jacobiAx_iff_jacTot (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) :
    JacobiAx W f ↔ ∀ (u v x : 𝒱) (ℓ m n : ℤ), jacTotL W f u v x ℓ m n = jacTotR W f u v x ℓ m n :=
  Iff.rfl

/-- The support of the left summand family is finite (restatement of `jacLHS_support_finite`). -/
theorem jac1L_support_finite (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱} (hf : Truncated f)
    (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ => jac1L W f u v x ℓ m n i).Finite :=
  jacLHS_support_finite W hf u v x ℓ m n

/-- The support of the right summand family is finite (restatement of `jacRHS_support_finite`). -/
theorem jac1R_support_finite (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱} (hf : Truncated f)
    (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ => jac1R W f u v x ℓ m n i).Finite :=
  jacRHS_support_finite W hf u v x ℓ m n

/-! ## The crux: at fixed grades the index range is finite and **explicit**

Both `finsum`s of `JacobiAx` are over `i : ℤ`.  They are cut off:

* **below**, for free and for every cochain, because `cbz ℓ i = 0` for `i < 0`
  (`cbz_apply_neg`) — so only `i ≥ 0` contributes;
* **above**, once the grades of `u, v, x` are fixed and the cochain is *graded*, because every
  factor in every summand is a product `(·)₍ₖ₎(·)` whose target grade decreases linearly in `i`
  and VOA4 positivity kills negative grades.

The resulting bounds `jacBoundL` and `jacBoundR` are explicit functions of the three input grades
and of `(ℓ, m, n)`; **no truncation hypothesis and no existential `N` is used**.  This is what the
`Truncated`-based bounds of `jacLHS_support_finite` do *not* give: those produce an unknown `N`
from an existential, so they cannot turn the identity into a written-out finite linear system. -/

/-- The explicit **upper bound of the left-hand index range** at input grades `(a,b,d)`:
the left summand `jac1L … i` vanishes for `i > jacBoundL a b d m n`.
Both halves of the left-hand side are products against `x`, one through `v₍ₙ₊ᵢ₎x` (target grade
`b + d - n - i - 1`) and one through `u₍ₘ₊ᵢ₎x` (target grade `a + d - m - i - 1`); the bound is
where the later of the two first goes negative. -/
def jacBoundL (a b d m n : ℤ) : ℤ := max (b + d - n - 1) (a + d - m - 1)

/-- The explicit **upper bound of the right-hand index range**: the right summand `jac1R … i`
vanishes for `i > jacBoundR a b ℓ`, because both of its terms factor through a product
`u₍ℓ₊ᵢ₎v` of target grade `a + b - ℓ - i - 1`. -/
def jacBoundR (a b ℓ : ℤ) : ℤ := a + b - ℓ - 1

/-- **The target grade of the identity.**  Every summand of either side of the first-order Jacobi
identity, for `u ∈ 𝒱ₐ`, `v ∈ 𝒱_b`, `x ∈ 𝒱_d`, lands in `𝒱_e` with `e = a+b+d-ℓ-m-n-2`,
*independently of the summation index* `i`.  (See `jac1L_mem_grading`, `jac1R_mem_grading`.) -/
def jacTarget (a b d ℓ m n : ℤ) : ℤ := a + b + d - ℓ - m - n - 2

/-- Below the range: the left summand vanishes for `i < 0`, for **every** cochain. -/
theorem jac1L_eq_zero_of_neg (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u v x : 𝒱)
    (ℓ m n : ℤ) {i : ℤ} (hi : i < 0) : jac1L W f u v x ℓ m n i = 0 := by
  rw [jac1L, cbz_apply_neg ℓ hi, mul_zero, zero_smul]

/-- Below the range: the right summand vanishes for `i < 0`, for **every** cochain. -/
theorem jac1R_eq_zero_of_neg (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u v x : 𝒱)
    (ℓ m n : ℤ) {i : ℤ} (hi : i < 0) : jac1R W f u v x ℓ m n i = 0 := by
  rw [jac1R, cbz_apply_neg m hi, zero_smul]

/-- Above the range: for a **graded** cochain and homogeneous `u, v, x`, the left summand
vanishes for `i > jacBoundL a b d m n`.  Pure positivity — no truncation hypothesis. -/
theorem jac1L_eq_zero_of_gt (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) {a b d : ℤ} {u v x : 𝒱} (hu : u ∈ W.grading a)
    (hv : v ∈ W.grading b) (hx : x ∈ W.grading d) (ℓ m n : ℤ) {i : ℤ}
    (hi : jacBoundL a b d m n < i) : jac1L W f u v x ℓ m n i = 0 := by
  rw [jacBoundL, max_lt_iff] at hi
  obtain ⟨h1, h2⟩ := hi
  rw [jac1L, smul_eq_zero_of_grading_lt W hv hx (by omega),
    gradedCochain_vanishing_of_gt W hf hv hx (n := n + i) (by omega),
    smul_eq_zero_of_grading_lt W hu hx (n := m + i) (by omega),
    gradedCochain_vanishing_of_gt W hf hu hx (n := m + i) (by omega)]
  simp

/-- Above the range: for a **graded** cochain and homogeneous `u, v`, the right summand
vanishes for `i > jacBoundR a b ℓ`.  Pure positivity — no truncation hypothesis. -/
theorem jac1R_eq_zero_of_gt (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) {a b : ℤ} {u v : 𝒱} (hu : u ∈ W.grading a)
    (hv : v ∈ W.grading b) (x : 𝒱) (ℓ m n : ℤ) {i : ℤ} (hi : jacBoundR a b ℓ < i) :
    jac1R W f u v x ℓ m n i = 0 := by
  rw [jacBoundR] at hi
  rw [jac1R, smul_eq_zero_of_grading_lt W hu hv (n := ℓ + i) (by omega),
    gradedCochain_vanishing_of_gt W hf hu hv (n := ℓ + i) (by omega)]
  simp

/-- The left summand family is supported in `Finset.Icc 0 (jacBoundL a b d m n)`. -/
theorem jac1L_support_subset (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) {a b d : ℤ} {u v x : 𝒱} (hu : u ∈ W.grading a)
    (hv : v ∈ W.grading b) (hx : x ∈ W.grading d) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ => jac1L W f u v x ℓ m n i)
      ⊆ (Finset.Icc (0 : ℤ) (jacBoundL a b d m n) : Finset ℤ) := by
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Finset.coe_Icc, Set.mem_Icc]
  exact ⟨not_lt.mp fun h => hi (jac1L_eq_zero_of_neg W f u v x ℓ m n h),
    not_lt.mp fun h => hi (jac1L_eq_zero_of_gt W hf hu hv hx ℓ m n h)⟩

/-- The right summand family is supported in `Finset.Icc 0 (jacBoundR a b ℓ)`. -/
theorem jac1R_support_subset (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) {a b : ℤ} {u v : 𝒱} (hu : u ∈ W.grading a)
    (hv : v ∈ W.grading b) (x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ => jac1R W f u v x ℓ m n i)
      ⊆ (Finset.Icc (0 : ℤ) (jacBoundR a b ℓ) : Finset ℤ) := by
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Finset.coe_Icc, Set.mem_Icc]
  exact ⟨not_lt.mp fun h => hi (jac1R_eq_zero_of_neg W f u v x ℓ m n h),
    not_lt.mp fun h => hi (jac1R_eq_zero_of_gt W hf hu hv x ℓ m n h)⟩

/-- **The left-hand `finsum` is an explicit finite sum.**  At fixed input grades the
`∑ᶠ` of the first-order Jacobi identity is literally `∑ i ∈ Finset.Icc 0 (jacBoundL a b d m n)`. -/
theorem jacTotL_eq_finsetSum (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) {a b d : ℤ} {u v x : 𝒱} (hu : u ∈ W.grading a)
    (hv : v ∈ W.grading b) (hx : x ∈ W.grading d) (ℓ m n : ℤ) :
    jacTotL W f u v x ℓ m n
      = ∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundL a b d m n), jac1L W f u v x ℓ m n i :=
  finsum_eq_finsetSum_of_support_subset _ (jac1L_support_subset W hf hu hv hx ℓ m n)

/-- **The right-hand `finsum` is an explicit finite sum.** -/
theorem jacTotR_eq_finsetSum (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) {a b : ℤ} {u v : 𝒱} (hu : u ∈ W.grading a)
    (hv : v ∈ W.grading b) (x : 𝒱) (ℓ m n : ℤ) :
    jacTotR W f u v x ℓ m n
      = ∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundR a b ℓ), jac1R W f u v x ℓ m n i :=
  finsum_eq_finsetSum_of_support_subset _ (jac1R_support_subset W hf hu hv x ℓ m n)

/-! ## Trilinearity of the two sides

Both sides of `JacobiAx` are additive in each of `u`, `v`, `x` separately (and vanish when any
argument is `0`).  This is what lets a statement checked on *homogeneous* triples be promoted to
all triples, via `eq_of_homogeneous₃`.  The `Truncated` hypothesis enters only through
`finsum_add_distrib`, which needs both families finitely supported. -/

/-- Additivity of the left summand in the first slot. -/
theorem jac1L_add_left (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u₁ u₂ v x : 𝒱)
    (ℓ m n i : ℤ) :
    jac1L W f (u₁ + u₂) v x ℓ m n i = jac1L W f u₁ v x ℓ m n i + jac1L W f u₂ v x ℓ m n i := by
  simp only [jac1L, cmode_add_left, cmode_add_right, PreVertexAlgebra.smul_add_left,
    PreVertexAlgebra.smul_add_right, smul_add, smul_sub]
  abel

/-- Additivity of the left summand in the second slot. -/
theorem jac1L_add_mid (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u v₁ v₂ x : 𝒱)
    (ℓ m n i : ℤ) :
    jac1L W f u (v₁ + v₂) x ℓ m n i = jac1L W f u v₁ x ℓ m n i + jac1L W f u v₂ x ℓ m n i := by
  simp only [jac1L, cmode_add_left, cmode_add_right, PreVertexAlgebra.smul_add_left,
    PreVertexAlgebra.smul_add_right, smul_add, smul_sub]
  abel

/-- Additivity of the left summand in the third slot. -/
theorem jac1L_add_right (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u v x₁ x₂ : 𝒱)
    (ℓ m n i : ℤ) :
    jac1L W f u v (x₁ + x₂) ℓ m n i = jac1L W f u v x₁ ℓ m n i + jac1L W f u v x₂ ℓ m n i := by
  simp only [jac1L, cmode_add_left, cmode_add_right, PreVertexAlgebra.smul_add_left,
    PreVertexAlgebra.smul_add_right, smul_add, smul_sub]
  abel

/-- Additivity of the right summand in the first slot. -/
theorem jac1R_add_left (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u₁ u₂ v x : 𝒱)
    (ℓ m n i : ℤ) :
    jac1R W f (u₁ + u₂) v x ℓ m n i = jac1R W f u₁ v x ℓ m n i + jac1R W f u₂ v x ℓ m n i := by
  simp only [jac1R, cmode_add_left, cmode_add_right, PreVertexAlgebra.smul_add_left,
    PreVertexAlgebra.smul_add_right, smul_add]
  abel

/-- Additivity of the right summand in the second slot. -/
theorem jac1R_add_mid (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u v₁ v₂ x : 𝒱)
    (ℓ m n i : ℤ) :
    jac1R W f u (v₁ + v₂) x ℓ m n i = jac1R W f u v₁ x ℓ m n i + jac1R W f u v₂ x ℓ m n i := by
  simp only [jac1R, cmode_add_left, cmode_add_right, PreVertexAlgebra.smul_add_left,
    PreVertexAlgebra.smul_add_right, smul_add]
  abel

/-- Additivity of the right summand in the third slot. -/
theorem jac1R_add_right (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u v x₁ x₂ : 𝒱)
    (ℓ m n i : ℤ) :
    jac1R W f u v (x₁ + x₂) ℓ m n i = jac1R W f u v x₁ ℓ m n i + jac1R W f u v x₂ ℓ m n i := by
  simp only [jac1R, cmode_add_left, cmode_add_right, PreVertexAlgebra.smul_add_left,
    PreVertexAlgebra.smul_add_right, smul_add]
  abel

/-- The left summand vanishes when the first slot is `0`. -/
@[simp] theorem jac1L_zero_left (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (v x : 𝒱)
    (ℓ m n i : ℤ) : jac1L W f 0 v x ℓ m n i = 0 := by simp [jac1L]

/-- The left summand vanishes when the second slot is `0`. -/
@[simp] theorem jac1L_zero_mid (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u x : 𝒱)
    (ℓ m n i : ℤ) : jac1L W f u 0 x ℓ m n i = 0 := by simp [jac1L]

/-- The left summand vanishes when the third slot is `0`. -/
@[simp] theorem jac1L_zero_right (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u v : 𝒱)
    (ℓ m n i : ℤ) : jac1L W f u v 0 ℓ m n i = 0 := by simp [jac1L]

/-- The right summand vanishes when the first slot is `0`. -/
@[simp] theorem jac1R_zero_left (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (v x : 𝒱)
    (ℓ m n i : ℤ) : jac1R W f 0 v x ℓ m n i = 0 := by simp [jac1R]

/-- The right summand vanishes when the second slot is `0`. -/
@[simp] theorem jac1R_zero_mid (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u x : 𝒱)
    (ℓ m n i : ℤ) : jac1R W f u 0 x ℓ m n i = 0 := by simp [jac1R]

/-- The right summand vanishes when the third slot is `0`. -/
@[simp] theorem jac1R_zero_right (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u v : 𝒱)
    (ℓ m n i : ℤ) : jac1R W f u v 0 ℓ m n i = 0 := by simp [jac1R]

/-- Additivity of the whole left-hand side in the first slot. -/
theorem jacTotL_add_left (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱} (hf : Truncated f)
    (u₁ u₂ v x : 𝒱) (ℓ m n : ℤ) :
    jacTotL W f (u₁ + u₂) v x ℓ m n
      = jacTotL W f u₁ v x ℓ m n + jacTotL W f u₂ v x ℓ m n := by
  rw [jacTotL, jacTotL, jacTotL, finsum_congr (jac1L_add_left W f u₁ u₂ v x ℓ m n),
    finsum_add_distrib (jac1L_support_finite W hf u₁ v x ℓ m n)
      (jac1L_support_finite W hf u₂ v x ℓ m n)]

/-- Additivity of the whole left-hand side in the second slot. -/
theorem jacTotL_add_mid (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱} (hf : Truncated f)
    (u v₁ v₂ x : 𝒱) (ℓ m n : ℤ) :
    jacTotL W f u (v₁ + v₂) x ℓ m n
      = jacTotL W f u v₁ x ℓ m n + jacTotL W f u v₂ x ℓ m n := by
  rw [jacTotL, jacTotL, jacTotL, finsum_congr (jac1L_add_mid W f u v₁ v₂ x ℓ m n),
    finsum_add_distrib (jac1L_support_finite W hf u v₁ x ℓ m n)
      (jac1L_support_finite W hf u v₂ x ℓ m n)]

/-- Additivity of the whole left-hand side in the third slot. -/
theorem jacTotL_add_right (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱} (hf : Truncated f)
    (u v x₁ x₂ : 𝒱) (ℓ m n : ℤ) :
    jacTotL W f u v (x₁ + x₂) ℓ m n
      = jacTotL W f u v x₁ ℓ m n + jacTotL W f u v x₂ ℓ m n := by
  rw [jacTotL, jacTotL, jacTotL, finsum_congr (jac1L_add_right W f u v x₁ x₂ ℓ m n),
    finsum_add_distrib (jac1L_support_finite W hf u v x₁ ℓ m n)
      (jac1L_support_finite W hf u v x₂ ℓ m n)]

/-- Additivity of the whole right-hand side in the first slot. -/
theorem jacTotR_add_left (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱} (hf : Truncated f)
    (u₁ u₂ v x : 𝒱) (ℓ m n : ℤ) :
    jacTotR W f (u₁ + u₂) v x ℓ m n
      = jacTotR W f u₁ v x ℓ m n + jacTotR W f u₂ v x ℓ m n := by
  rw [jacTotR, jacTotR, jacTotR, finsum_congr (jac1R_add_left W f u₁ u₂ v x ℓ m n),
    finsum_add_distrib (jac1R_support_finite W hf u₁ v x ℓ m n)
      (jac1R_support_finite W hf u₂ v x ℓ m n)]

/-- Additivity of the whole right-hand side in the second slot. -/
theorem jacTotR_add_mid (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱} (hf : Truncated f)
    (u v₁ v₂ x : 𝒱) (ℓ m n : ℤ) :
    jacTotR W f u (v₁ + v₂) x ℓ m n
      = jacTotR W f u v₁ x ℓ m n + jacTotR W f u v₂ x ℓ m n := by
  rw [jacTotR, jacTotR, jacTotR, finsum_congr (jac1R_add_mid W f u v₁ v₂ x ℓ m n),
    finsum_add_distrib (jac1R_support_finite W hf u v₁ x ℓ m n)
      (jac1R_support_finite W hf u v₂ x ℓ m n)]

/-- Additivity of the whole right-hand side in the third slot. -/
theorem jacTotR_add_right (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱} (hf : Truncated f)
    (u v x₁ x₂ : 𝒱) (ℓ m n : ℤ) :
    jacTotR W f u v (x₁ + x₂) ℓ m n
      = jacTotR W f u v x₁ ℓ m n + jacTotR W f u v x₂ ℓ m n := by
  rw [jacTotR, jacTotR, jacTotR, finsum_congr (jac1R_add_right W f u v x₁ x₂ ℓ m n),
    finsum_add_distrib (jac1R_support_finite W hf u v x₁ ℓ m n)
      (jac1R_support_finite W hf u v x₂ ℓ m n)]

/-- The left-hand side vanishes when the first slot is `0`. -/
@[simp] theorem jacTotL_zero_left (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (v x : 𝒱)
    (ℓ m n : ℤ) : jacTotL W f 0 v x ℓ m n = 0 := by
  rw [jacTotL, finsum_congr (jac1L_zero_left W f v x ℓ m n), finsum_zero]

/-- The left-hand side vanishes when the second slot is `0`. -/
@[simp] theorem jacTotL_zero_mid (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u x : 𝒱)
    (ℓ m n : ℤ) : jacTotL W f u 0 x ℓ m n = 0 := by
  rw [jacTotL, finsum_congr (jac1L_zero_mid W f u x ℓ m n), finsum_zero]

/-- The left-hand side vanishes when the third slot is `0`. -/
@[simp] theorem jacTotL_zero_right (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u v : 𝒱)
    (ℓ m n : ℤ) : jacTotL W f u v 0 ℓ m n = 0 := by
  rw [jacTotL, finsum_congr (jac1L_zero_right W f u v ℓ m n), finsum_zero]

/-- The right-hand side vanishes when the first slot is `0`. -/
@[simp] theorem jacTotR_zero_left (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (v x : 𝒱)
    (ℓ m n : ℤ) : jacTotR W f 0 v x ℓ m n = 0 := by
  rw [jacTotR, finsum_congr (jac1R_zero_left W f v x ℓ m n), finsum_zero]

/-- The right-hand side vanishes when the second slot is `0`. -/
@[simp] theorem jacTotR_zero_mid (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u x : 𝒱)
    (ℓ m n : ℤ) : jacTotR W f u 0 x ℓ m n = 0 := by
  rw [jacTotR, finsum_congr (jac1R_zero_mid W f u x ℓ m n), finsum_zero]

/-- The right-hand side vanishes when the third slot is `0`. -/
@[simp] theorem jacTotR_zero_right (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (u v : 𝒱)
    (ℓ m n : ℤ) : jacTotR W f u v 0 ℓ m n = 0 := by
  rw [jacTotR, finsum_congr (jac1R_zero_right W f u v ℓ m n), finsum_zero]

/-! ## From homogeneous triples to all triples -/

/-- **Three-variable version of `eq_of_homogeneous`.**  Two tri-additive maps
`𝒱 × 𝒱 × 𝒱 → 𝒱` that agree on homogeneous triples agree everywhere.  This is the only place the
structure field `isInternal` is used in this file, and it is used in the only way it can be. -/
theorem eq_of_homogeneous₃ (W : VertexOperatorAlgebra 𝒱) {F G : 𝒱 → 𝒱 → 𝒱 → 𝒱}
    (hF0₁ : ∀ v x, F 0 v x = 0) (hF₁ : ∀ u₁ u₂ v x, F (u₁ + u₂) v x = F u₁ v x + F u₂ v x)
    (hF0₂ : ∀ u x, F u 0 x = 0) (hF₂ : ∀ u v₁ v₂ x, F u (v₁ + v₂) x = F u v₁ x + F u v₂ x)
    (hF0₃ : ∀ u v, F u v 0 = 0) (hF₃ : ∀ u v x₁ x₂, F u v (x₁ + x₂) = F u v x₁ + F u v x₂)
    (hG0₁ : ∀ v x, G 0 v x = 0) (hG₁ : ∀ u₁ u₂ v x, G (u₁ + u₂) v x = G u₁ v x + G u₂ v x)
    (hG0₂ : ∀ u x, G u 0 x = 0) (hG₂ : ∀ u v₁ v₂ x, G u (v₁ + v₂) x = G u v₁ x + G u v₂ x)
    (hG0₃ : ∀ u v, G u v 0 = 0) (hG₃ : ∀ u v x₁ x₂, G u v (x₁ + x₂) = G u v x₁ + G u v x₂)
    (h : ∀ (a b d : ℤ) (u : 𝒱), u ∈ W.grading a → ∀ v : 𝒱, v ∈ W.grading b →
      ∀ x : 𝒱, x ∈ W.grading d → F u v x = G u v x)
    (u v x : 𝒱) : F u v x = G u v x := by
  have hu : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun y => ∀ w z : 𝒱, F y w z = G y w z) hu ?_ ?_ ?_ v x
  · intro a y hy w z
    have hw : w ∈ ⨆ i, W.grading i := by
      rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction W.grading
      (motive := fun w' => ∀ z' : 𝒱, F y w' z' = G y w' z') hw ?_ ?_ ?_ z
    · intro b w' hw' z'
      have hz : z' ∈ ⨆ i, W.grading i := by
        rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
      refine Submodule.iSup_induction W.grading
        (motive := fun z'' => F y w' z'' = G y w' z'') hz ?_ ?_ ?_
      · intro d z'' hz''
        exact h a b d y hy w' hw' z'' hz''
      · change F y w' 0 = G y w' 0
        rw [hF0₃, hG0₃]
      · intro z₁ z₂ h₁ h₂
        change F y w' (z₁ + z₂) = G y w' (z₁ + z₂)
        rw [hF₃, hG₃, h₁, h₂]
    · intro z'
      rw [hF0₂, hG0₂]
    · intro w₁ w₂ h₁ h₂ z'
      rw [hF₂, hG₂, h₁ z', h₂ z']
  · intro w z
    rw [hF0₁, hG0₁]
  · intro y₁ y₂ h₁ h₂ w z
    rw [hF₁, hG₁, h₁ w z, h₂ w z]

/-! ## The local Jacobi condition and the equivalence -/

/-- **The local first-order Jacobi condition** at input grades `(a,b,d)` and indices
`(ℓ,m,n)`: a *single explicit finite* linear equation on the graded components of `f`,

`∑_{i=0}^{jacBoundL a b d m n} jac1L … i = ∑_{i=0}^{jacBoundR a b ℓ} jac1R … i`

quantified over homogeneous `u ∈ 𝒱ₐ`, `v ∈ 𝒱_b`, `x ∈ 𝒱_d`.  Both sums are honest
`Finset.sum`s over explicit ranges; nothing existential and nothing infinite occurs. -/
def LocalJacobiAt (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (a b d ℓ m n : ℤ) : Prop :=
  ∀ u ∈ W.grading a, ∀ v ∈ W.grading b, ∀ x ∈ W.grading d,
    (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundL a b d m n), jac1L W f u v x ℓ m n i)
      = ∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundR a b ℓ), jac1R W f u v x ℓ m n i

/-- **THE LOCALISATION.**  For a *graded* cochain, the first-order Jacobi identity — an
identity of `finsum`s over `ℤ`, quantified over all of `𝒱³` — is **equivalent** to the family of
explicit finite equations `LocalJacobiAt`, one for each `(a,b,d,ℓ,m,n) ∈ ℤ⁶`.

Both directions are proved.  `→` is the finite-support computation of `jacTotL_eq_finsetSum`;
`←` is `eq_of_homogeneous₃`, i.e. the internal direct-sum decomposition. -/
theorem jacobiAx_iff_localJacobiAt (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) :
    JacobiAx W f ↔ ∀ a b d ℓ m n : ℤ, LocalJacobiAt W f a b d ℓ m n := by
  have htr : Truncated f := truncated_of_graded W hf
  rw [jacobiAx_iff_jacTot]
  constructor
  · intro h a b d ℓ m n u hu v hv x hx
    rw [← jacTotL_eq_finsetSum W hf hu hv hx ℓ m n, ← jacTotR_eq_finsetSum W hf hu hv x ℓ m n]
    exact h u v x ℓ m n
  · intro h u v x ℓ m n
    refine eq_of_homogeneous₃ W
      (F := fun y w z => jacTotL W f y w z ℓ m n) (G := fun y w z => jacTotR W f y w z ℓ m n)
      (fun w z => jacTotL_zero_left W f w z ℓ m n)
      (fun y₁ y₂ w z => jacTotL_add_left W htr y₁ y₂ w z ℓ m n)
      (fun y z => jacTotL_zero_mid W f y z ℓ m n)
      (fun y w₁ w₂ z => jacTotL_add_mid W htr y w₁ w₂ z ℓ m n)
      (fun y w => jacTotL_zero_right W f y w ℓ m n)
      (fun y w z₁ z₂ => jacTotL_add_right W htr y w z₁ z₂ ℓ m n)
      (fun w z => jacTotR_zero_left W f w z ℓ m n)
      (fun y₁ y₂ w z => jacTotR_add_left W htr y₁ y₂ w z ℓ m n)
      (fun y z => jacTotR_zero_mid W f y z ℓ m n)
      (fun y w₁ w₂ z => jacTotR_add_mid W htr y w₁ w₂ z ℓ m n)
      (fun y w => jacTotR_zero_right W f y w ℓ m n)
      (fun y w z₁ z₂ => jacTotR_add_right W htr y w z₁ z₂ ℓ m n)
      (fun a b d y hy w hw z hz => ?_) u v x
    change jacTotL W f y w z ℓ m n = jacTotR W f y w z ℓ m n
    rw [jacTotL_eq_finsetSum W hf hy hw hz ℓ m n, jacTotR_eq_finsetSum W hf hy hw z ℓ m n]
    exact h a b d ℓ m n y hy w hw z hz

/-! ## Localising the vacuum and creation axioms

The two remaining nontrivial axioms are localised the same way, and more cheaply: they are
*linear* conditions on single graded components.  The truncation axiom needs no localisation at
all — it is automatic for a graded cochain (`truncated_of_graded`). -/

/-- One-variable version of `eq_of_homogeneous`: an additive map vanishing on every homogeneous
vector vanishes. -/
theorem eq_zero_of_homogeneous (W : VertexOperatorAlgebra 𝒱) {F : 𝒱 → 𝒱} (hF0 : F 0 = 0)
    (hFadd : ∀ v₁ v₂, F (v₁ + v₂) = F v₁ + F v₂)
    (h : ∀ (b : ℤ) (v : 𝒱), v ∈ W.grading b → F v = 0) (v : 𝒱) : F v = 0 := by
  have hv : v ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun y => F y = 0) hv ?_ ?_ ?_
  · intro b y hy
    exact h b y hy
  · exact hF0
  · intro y₁ y₂ h₁ h₂
    rw [hFadd, h₁, h₂, add_zero]

/-- The component of a graded cochain at tridegree `(a,b,c)` lands in `𝒱_c`.  (Repackaging of
`gradedComponent_mem` for bare vectors.) -/
theorem cmode_gradedMode_mem (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) (a b c : ℤ) {u v : 𝒱} (hu : u ∈ W.grading a)
    (hv : v ∈ W.grading b) : cmode f u (gradedMode a b c) v ∈ W.grading c := by
  have h := hf a b u hu v hv (gradedMode a b c)
  rwa [grading_of_gradedMode] at h

/-- A graded cochain has **no component at a negative target grade**: VOA4 again. -/
theorem cmode_gradedMode_eq_zero_of_neg (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) (a b : ℤ) {c : ℤ} (hc : c < 0) {u v : 𝒱}
    (hu : u ∈ W.grading a) (hv : v ∈ W.grading b) : cmode f u (gradedMode a b c) v = 0 := by
  have h := cmode_gradedMode_mem W hf a b c hu hv
  rw [W.positivity c hc] at h
  exact (Submodule.mem_bot ℂ).mp h

/-- **The local order-`t` vacuum axiom** at `(b,c)`: the component of `f` at tridegree
`(0,b,c)` vanishes.  (Source grade `0`, because `𝟙 ∈ 𝒱₀`.) -/
def VacuumAxLocal (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (b c : ℤ) : Prop :=
  ∀ v ∈ W.grading b, cmode f W.vacuum (gradedMode 0 b c) v = 0

/-- **The local order-`t` creation axiom** at `(a,c)`: for `c ≤ a` the component of `f` at
tridegree `(a,0,c)`, evaluated on the vacuum in the second slot, vanishes.  The constraint
`c ≤ a` is exactly the axiom's mode constraint `n ≥ -1`, since `n = gradedMode a 0 c = a-c-1`. -/
def CreationAxLocal (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (a c : ℤ) : Prop :=
  c ≤ a → ∀ u ∈ W.grading a, cmode f u (gradedMode a 0 c) W.vacuum = 0

/-- **Localisation of the vacuum axiom.**  `Y₁(𝟙,z) = 0` is the family of component equations
`VacuumAxLocal`.  (No gradedness is needed for this one.) -/
theorem vacuum_iff_local (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) :
    f W.vacuum = 0 ↔ ∀ b c : ℤ, VacuumAxLocal W f b c := by
  constructor
  · intro h b c v _
    rw [cmode_def, h, mode_zero, LinearMap.zero_apply]
  · intro h
    refine FormalDist.ext fun k => LinearMap.ext fun v => ?_
    have hz : cmode f W.vacuum (-k - 1) v = 0 := by
      refine eq_zero_of_homogeneous W (F := fun w => cmode f W.vacuum (-k - 1) w)
        (cmode_zero_right f W.vacuum (-k - 1))
        (fun w₁ w₂ => cmode_add_right f W.vacuum (-k - 1) w₁ w₂) (fun b w hw => ?_) v
      have hb := h b (b - (-k - 1) - 1) w hw
      rwa [show gradedMode 0 b (b - (-k - 1) - 1) = -k - 1 from by simp only [gradedMode]; ring]
        at hb
    rwa [cmode_def, mode_apply, show -(-k - 1) - 1 = k from by ring] at hz

/-- **Localisation of the creation axiom.**  `u¹₍ₙ₎𝟙 = 0` for `n ≥ -1` is the family of
component equations `CreationAxLocal`.  (No gradedness is needed for this one either.) -/
theorem creationAx_iff_local (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) :
    CreationAx W f ↔ ∀ a c : ℤ, CreationAxLocal W f a c := by
  constructor
  · intro h a c hc u _
    exact h u (gradedMode a 0 c) (by simp only [gradedMode]; omega)
  · intro h u k hk
    refine eq_zero_of_homogeneous W (F := fun w => cmode f w k W.vacuum)
      (cmode_zero_left f k W.vacuum) (fun w₁ w₂ => cmode_add_left f w₁ w₂ k W.vacuum)
      (fun a w hw => ?_) u
    have ha := h a (a - k - 1) (by omega) w hw
    rwa [show gradedMode a 0 (a - k - 1) = k from by simp only [gradedMode]; ring] at ha

/-- For a graded cochain the local vacuum condition at a **negative** target grade is automatic:
`𝒱_c = 0`.  So only `c ≥ 0` carries information. -/
theorem vacuumAxLocal_of_neg (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) (b : ℤ) {c : ℤ} (hc : c < 0) : VacuumAxLocal W f b c :=
  fun _ hv => cmode_gradedMode_eq_zero_of_neg W hf 0 b hc W.vacuum_mem hv

/-- For a graded cochain the local creation condition is nontrivial only for `0 ≤ c ≤ a`:
**finitely many conditions per source grade**.  (Negative `c` is killed by `𝒱_c = 0`, and `c > a`
is excluded by the axiom's own mode constraint.) -/
theorem creationAxLocal_of_neg (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) (a : ℤ) {c : ℤ} (hc : c < 0) : CreationAxLocal W f a c :=
  fun _ _ hu => cmode_gradedMode_eq_zero_of_neg W hf a 0 hc hu W.vacuum_mem

/-- **The cocycle condition is a system of explicit finite linear equations on the graded
components.**  For a graded cochain, membership in `cocycles W` — the conjunction of the four
order-`t` axioms — is equivalent to:

* the local vacuum equations `VacuumAxLocal` (one per `(b,c)`; automatic for `c < 0`);
* the local creation equations `CreationAxLocal` (one per `(a,c)`; nontrivial only for
  `0 ≤ c ≤ a`, i.e. finitely many per `a`);
* the local Jacobi equations `LocalJacobiAt` (one per `(a,b,d,ℓ,m,n)`, each an equality of two
  `Finset.sum`s over explicit ranges).

The truncation axiom does not appear: it is free (`truncated_of_graded`). -/
theorem mem_cocycles_iff_local (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) :
    f ∈ cocycles W ↔
      (∀ b c : ℤ, VacuumAxLocal W f b c) ∧ (∀ a c : ℤ, CreationAxLocal W f a c)
        ∧ ∀ a b d ℓ m n : ℤ, LocalJacobiAt W f a b d ℓ m n := by
  rw [mem_cocycles]
  constructor
  · rintro ⟨-, hvac, hcre, hjac⟩
    exact ⟨(vacuum_iff_local W f).mp hvac, (creationAx_iff_local W f).mp hcre,
      (jacobiAx_iff_localJacobiAt W hf).mp hjac⟩
  · rintro ⟨hvac, hcre, hjac⟩
    exact ⟨truncated_of_graded W hf, (vacuum_iff_local W f).mpr hvac,
      (creationAx_iff_local W f).mpr hcre, (jacobiAx_iff_localJacobiAt W hf).mpr hjac⟩

/-- The same statement inside `gradedCocycles W`, the submodule of `↥(gradedCochains W)` whose
image under `gradedComponent` defines `gradedCocyclesAt`. -/
theorem mem_gradedCocycles_iff_local (W : VertexOperatorAlgebra 𝒱) (f : ↥(gradedCochains W)) :
    f ∈ gradedCocycles W ↔
      (∀ b c : ℤ, VacuumAxLocal W (f : Cochain 𝒱) b c)
        ∧ (∀ a c : ℤ, CreationAxLocal W (f : Cochain 𝒱) a c)
        ∧ ∀ a b d ℓ m n : ℤ, LocalJacobiAt W (f : Cochain 𝒱) a b d ℓ m n :=
  mem_cocycles_iff_local W f.2

/-! ## The local system as a kernel

`LocalJacobiAt` is a *linear* condition, so it is the kernel of an explicit linear map.  The
target of that map is finite-dimensional (`GradedCochain`-like: a space of trilinear maps between
graded pieces), which is the precise sense in which the first-order Jacobi identity at a fixed
tridegree is finite linear algebra. -/

/-- Scalar-homogeneity of the left summand in the first slot. -/
theorem jac1L_smul_left (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (r : ℂ) (u v x : 𝒱)
    (ℓ m n i : ℤ) : jac1L W f (r • u) v x ℓ m n i = r • jac1L W f u v x ℓ m n i := by
  simp only [jac1L, cmode_smul_left, cmode_smul_right, PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right, smul_add, smul_sub, smul_comm r]

/-- Scalar-homogeneity of the left summand in the second slot. -/
theorem jac1L_smul_mid (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (r : ℂ) (u v x : 𝒱)
    (ℓ m n i : ℤ) : jac1L W f u (r • v) x ℓ m n i = r • jac1L W f u v x ℓ m n i := by
  simp only [jac1L, cmode_smul_left, cmode_smul_right, PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right, smul_add, smul_sub, smul_comm r]

/-- Scalar-homogeneity of the left summand in the third slot. -/
theorem jac1L_smul_right (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (r : ℂ) (u v x : 𝒱)
    (ℓ m n i : ℤ) : jac1L W f u v (r • x) ℓ m n i = r • jac1L W f u v x ℓ m n i := by
  simp only [jac1L, cmode_smul_left, cmode_smul_right, PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right, smul_add, smul_sub, smul_comm r]

/-- Scalar-homogeneity of the right summand in the first slot. -/
theorem jac1R_smul_left (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (r : ℂ) (u v x : 𝒱)
    (ℓ m n i : ℤ) : jac1R W f (r • u) v x ℓ m n i = r • jac1R W f u v x ℓ m n i := by
  simp only [jac1R, cmode_smul_left, cmode_smul_right, PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right, smul_add, smul_comm r]

/-- Scalar-homogeneity of the right summand in the second slot. -/
theorem jac1R_smul_mid (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (r : ℂ) (u v x : 𝒱)
    (ℓ m n i : ℤ) : jac1R W f u (r • v) x ℓ m n i = r • jac1R W f u v x ℓ m n i := by
  simp only [jac1R, cmode_smul_left, cmode_smul_right, PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right, smul_add, smul_comm r]

/-- Scalar-homogeneity of the right summand in the third slot. -/
theorem jac1R_smul_right (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (r : ℂ) (u v x : 𝒱)
    (ℓ m n i : ℤ) : jac1R W f u v (r • x) ℓ m n i = r • jac1R W f u v x ℓ m n i := by
  simp only [jac1R, cmode_smul_left, cmode_smul_right, PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right, smul_add, smul_comm r]

/-- The left summand is additive in the **cochain** — the cocycle condition is linear in `Y₁`. -/
theorem jac1L_add_cochain (W : VertexOperatorAlgebra 𝒱) (f g : Cochain 𝒱) (u v x : 𝒱)
    (ℓ m n i : ℤ) :
    jac1L W (f + g) u v x ℓ m n i = jac1L W f u v x ℓ m n i + jac1L W g u v x ℓ m n i := by
  simp only [jac1L, cmode_add_cochain, PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    smul_add, smul_sub]
  abel

/-- The right summand is additive in the cochain. -/
theorem jac1R_add_cochain (W : VertexOperatorAlgebra 𝒱) (f g : Cochain 𝒱) (u v x : 𝒱)
    (ℓ m n i : ℤ) :
    jac1R W (f + g) u v x ℓ m n i = jac1R W f u v x ℓ m n i + jac1R W g u v x ℓ m n i := by
  simp only [jac1R, cmode_add_cochain, PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    smul_add]
  abel

/-- The left summand is scalar-homogeneous in the cochain. -/
theorem jac1L_smul_cochain (W : VertexOperatorAlgebra 𝒱) (r : ℂ) (f : Cochain 𝒱) (u v x : 𝒱)
    (ℓ m n i : ℤ) : jac1L W (r • f) u v x ℓ m n i = r • jac1L W f u v x ℓ m n i := by
  simp only [jac1L, cmode_smul_cochain, PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right, smul_add, smul_sub, smul_comm r]

/-- The right summand is scalar-homogeneous in the cochain. -/
theorem jac1R_smul_cochain (W : VertexOperatorAlgebra 𝒱) (r : ℂ) (f : Cochain 𝒱) (u v x : 𝒱)
    (ℓ m n i : ℤ) : jac1R W (r • f) u v x ℓ m n i = r • jac1R W f u v x ℓ m n i := by
  simp only [jac1R, cmode_smul_cochain, PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right, smul_add, smul_comm r]

/-! ### Every summand lands in the same graded piece -/

/-- **The identity is grade-homogeneous.**  Each left summand lands in `𝒱_e` with
`e = jacTarget a b d ℓ m n`, *independently of `i`*.  (This is the reason the tridegree, not the
mode, is the right index: the mode is determined by the grades.) -/
theorem jac1L_mem_grading (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) {a b d : ℤ} {u v x : 𝒱} (hu : u ∈ W.grading a)
    (hv : v ∈ W.grading b) (hx : x ∈ W.grading d) (ℓ m n i : ℤ) :
    jac1L W f u v x ℓ m n i ∈ W.grading (jacTarget a b d ℓ m n) := by
  have e1 : ∀ j : ℤ, a + (b + d - (n + j) - 1) - (ℓ + m - j) - 1 = jacTarget a b d ℓ m n := by
    intro j; simp only [jacTarget]; ring
  have e2 : ∀ j : ℤ, b + (a + d - (m + j) - 1) - (ℓ + n - j) - 1 = jacTarget a b d ℓ m n := by
    intro j; simp only [jacTarget]; ring
  have hA : cmode f u (ℓ + m - i) (W.smul v (n + i) x) ∈ W.grading (jacTarget a b d ℓ m n) := by
    have h := hf a (b + d - (n + i) - 1) u hu _
      (W.toPreVertexAlgebra.smul_mem_grading hv hx (n + i)) (ℓ + m - i)
    rwa [e1 i] at h
  have hB : W.smul u (ℓ + m - i) (cmode f v (n + i) x) ∈ W.grading (jacTarget a b d ℓ m n) := by
    have h := W.toPreVertexAlgebra.smul_mem_grading hu (hf b d v hv x hx (n + i)) (ℓ + m - i)
    rwa [e1 i] at h
  have hC : cmode f v (ℓ + n - i) (W.smul u (m + i) x) ∈ W.grading (jacTarget a b d ℓ m n) := by
    have h := hf b (a + d - (m + i) - 1) v hv _
      (W.toPreVertexAlgebra.smul_mem_grading hu hx (m + i)) (ℓ + n - i)
    rwa [e2 i] at h
  have hD : W.smul v (ℓ + n - i) (cmode f u (m + i) x) ∈ W.grading (jacTarget a b d ℓ m n) := by
    have h := W.toPreVertexAlgebra.smul_mem_grading hv (hf a d u hu x hx (m + i)) (ℓ + n - i)
    rwa [e2 i] at h
  rw [jac1L]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.add_mem _ hA hB)
    (Submodule.smul_mem _ _ (Submodule.add_mem _ hC hD)))

/-- Each right summand lands in the same `𝒱_e`. -/
theorem jac1R_mem_grading (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) {a b d : ℤ} {u v x : 𝒱} (hu : u ∈ W.grading a)
    (hv : v ∈ W.grading b) (hx : x ∈ W.grading d) (ℓ m n i : ℤ) :
    jac1R W f u v x ℓ m n i ∈ W.grading (jacTarget a b d ℓ m n) := by
  have e3 : (a + b - (ℓ + i) - 1) + d - (m + n - i) - 1 = jacTarget a b d ℓ m n := by
    simp only [jacTarget]; ring
  have hA : W.smul (cmode f u (ℓ + i) v) (m + n - i) x ∈ W.grading (jacTarget a b d ℓ m n) := by
    have h := W.toPreVertexAlgebra.smul_mem_grading (hf a b u hu v hv (ℓ + i)) hx (m + n - i)
    rwa [e3] at h
  have hB : cmode f (W.smul u (ℓ + i) v) (m + n - i) x ∈ W.grading (jacTarget a b d ℓ m n) := by
    have h := hf (a + b - (ℓ + i) - 1) d _
      (W.toPreVertexAlgebra.smul_mem_grading hu hv (ℓ + i)) x hx (m + n - i)
    rwa [e3] at h
  rw [jac1R]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hA hB)

/-! ### The defect -/

/-- The **local Jacobi defect**: left-hand finite sum minus right-hand finite sum.
`LocalJacobiAt` says exactly that it vanishes on homogeneous triples. -/
noncomputable def jacDefect (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (a b d ℓ m n : ℤ)
    (u v x : 𝒱) : 𝒱 :=
  (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundL a b d m n), jac1L W f u v x ℓ m n i)
    - ∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundR a b ℓ), jac1R W f u v x ℓ m n i

/-- The defect lands in `𝒱_{jacTarget a b d ℓ m n}`. -/
theorem jacDefect_mem_grading (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) {a b d : ℤ} {u v x : 𝒱} (hu : u ∈ W.grading a)
    (hv : v ∈ W.grading b) (hx : x ∈ W.grading d) (ℓ m n : ℤ) :
    jacDefect W f a b d ℓ m n u v x ∈ W.grading (jacTarget a b d ℓ m n) :=
  Submodule.sub_mem _
    (Submodule.sum_mem _ fun i _ => jac1L_mem_grading W hf hu hv hx ℓ m n i)
    (Submodule.sum_mem _ fun i _ => jac1R_mem_grading W hf hu hv hx ℓ m n i)

/-- `LocalJacobiAt` is the vanishing of `jacDefect` on homogeneous triples. -/
theorem localJacobiAt_iff_jacDefect (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱)
    (a b d ℓ m n : ℤ) :
    LocalJacobiAt W f a b d ℓ m n
      ↔ ∀ u ∈ W.grading a, ∀ v ∈ W.grading b, ∀ x ∈ W.grading d,
          jacDefect W f a b d ℓ m n u v x = 0 := by
  simp only [LocalJacobiAt, jacDefect, sub_eq_zero]

/-! ### Linearity of the defect, slot by slot -/

/-- The defect is additive in the first vector slot. -/
theorem jacDefect_add_left (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (a b d ℓ m n : ℤ)
    (u₁ u₂ v x : 𝒱) :
    jacDefect W f a b d ℓ m n (u₁ + u₂) v x
      = jacDefect W f a b d ℓ m n u₁ v x + jacDefect W f a b d ℓ m n u₂ v x := by
  have hL : (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundL a b d m n), jac1L W f (u₁ + u₂) v x ℓ m n i)
      = (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundL a b d m n), jac1L W f u₁ v x ℓ m n i)
        + ∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundL a b d m n), jac1L W f u₂ v x ℓ m n i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => jac1L_add_left W f u₁ u₂ v x ℓ m n i
  have hR : (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundR a b ℓ), jac1R W f (u₁ + u₂) v x ℓ m n i)
      = (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundR a b ℓ), jac1R W f u₁ v x ℓ m n i)
        + ∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundR a b ℓ), jac1R W f u₂ v x ℓ m n i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => jac1R_add_left W f u₁ u₂ v x ℓ m n i
  simp only [jacDefect, hL, hR]
  abel

/-- The defect is additive in the second vector slot. -/
theorem jacDefect_add_mid (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (a b d ℓ m n : ℤ)
    (u v₁ v₂ x : 𝒱) :
    jacDefect W f a b d ℓ m n u (v₁ + v₂) x
      = jacDefect W f a b d ℓ m n u v₁ x + jacDefect W f a b d ℓ m n u v₂ x := by
  have hL : (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundL a b d m n), jac1L W f u (v₁ + v₂) x ℓ m n i)
      = (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundL a b d m n), jac1L W f u v₁ x ℓ m n i)
        + ∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundL a b d m n), jac1L W f u v₂ x ℓ m n i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => jac1L_add_mid W f u v₁ v₂ x ℓ m n i
  have hR : (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundR a b ℓ), jac1R W f u (v₁ + v₂) x ℓ m n i)
      = (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundR a b ℓ), jac1R W f u v₁ x ℓ m n i)
        + ∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundR a b ℓ), jac1R W f u v₂ x ℓ m n i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => jac1R_add_mid W f u v₁ v₂ x ℓ m n i
  simp only [jacDefect, hL, hR]
  abel

/-- The defect is additive in the third vector slot. -/
theorem jacDefect_add_right (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (a b d ℓ m n : ℤ)
    (u v x₁ x₂ : 𝒱) :
    jacDefect W f a b d ℓ m n u v (x₁ + x₂)
      = jacDefect W f a b d ℓ m n u v x₁ + jacDefect W f a b d ℓ m n u v x₂ := by
  have hL : (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundL a b d m n), jac1L W f u v (x₁ + x₂) ℓ m n i)
      = (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundL a b d m n), jac1L W f u v x₁ ℓ m n i)
        + ∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundL a b d m n), jac1L W f u v x₂ ℓ m n i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => jac1L_add_right W f u v x₁ x₂ ℓ m n i
  have hR : (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundR a b ℓ), jac1R W f u v (x₁ + x₂) ℓ m n i)
      = (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundR a b ℓ), jac1R W f u v x₁ ℓ m n i)
        + ∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundR a b ℓ), jac1R W f u v x₂ ℓ m n i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => jac1R_add_right W f u v x₁ x₂ ℓ m n i
  simp only [jacDefect, hL, hR]
  abel

/-- The defect is scalar-homogeneous in the first vector slot. -/
theorem jacDefect_smul_left (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (a b d ℓ m n : ℤ)
    (r : ℂ) (u v x : 𝒱) :
    jacDefect W f a b d ℓ m n (r • u) v x = r • jacDefect W f a b d ℓ m n u v x := by
  have hL := Finset.sum_congr (rfl : Finset.Icc (0 : ℤ) (jacBoundL a b d m n) = _)
    fun i _ => jac1L_smul_left W f r u v x ℓ m n i
  have hR := Finset.sum_congr (rfl : Finset.Icc (0 : ℤ) (jacBoundR a b ℓ) = _)
    fun i _ => jac1R_smul_left W f r u v x ℓ m n i
  simp only [jacDefect, hL, hR, ← Finset.smul_sum, smul_sub]

/-- The defect is scalar-homogeneous in the second vector slot. -/
theorem jacDefect_smul_mid (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (a b d ℓ m n : ℤ)
    (r : ℂ) (u v x : 𝒱) :
    jacDefect W f a b d ℓ m n u (r • v) x = r • jacDefect W f a b d ℓ m n u v x := by
  have hL := Finset.sum_congr (rfl : Finset.Icc (0 : ℤ) (jacBoundL a b d m n) = _)
    fun i _ => jac1L_smul_mid W f r u v x ℓ m n i
  have hR := Finset.sum_congr (rfl : Finset.Icc (0 : ℤ) (jacBoundR a b ℓ) = _)
    fun i _ => jac1R_smul_mid W f r u v x ℓ m n i
  simp only [jacDefect, hL, hR, ← Finset.smul_sum, smul_sub]

/-- The defect is scalar-homogeneous in the third vector slot. -/
theorem jacDefect_smul_right (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) (a b d ℓ m n : ℤ)
    (r : ℂ) (u v x : 𝒱) :
    jacDefect W f a b d ℓ m n u v (r • x) = r • jacDefect W f a b d ℓ m n u v x := by
  have hL := Finset.sum_congr (rfl : Finset.Icc (0 : ℤ) (jacBoundL a b d m n) = _)
    fun i _ => jac1L_smul_right W f r u v x ℓ m n i
  have hR := Finset.sum_congr (rfl : Finset.Icc (0 : ℤ) (jacBoundR a b ℓ) = _)
    fun i _ => jac1R_smul_right W f r u v x ℓ m n i
  simp only [jacDefect, hL, hR, ← Finset.smul_sum, smul_sub]

/-- The defect is additive in the **cochain**: the local system is linear. -/
theorem jacDefect_add_cochain (W : VertexOperatorAlgebra 𝒱) (f g : Cochain 𝒱) (a b d ℓ m n : ℤ)
    (u v x : 𝒱) :
    jacDefect W (f + g) a b d ℓ m n u v x
      = jacDefect W f a b d ℓ m n u v x + jacDefect W g a b d ℓ m n u v x := by
  have hL : (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundL a b d m n), jac1L W (f + g) u v x ℓ m n i)
      = (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundL a b d m n), jac1L W f u v x ℓ m n i)
        + ∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundL a b d m n), jac1L W g u v x ℓ m n i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => jac1L_add_cochain W f g u v x ℓ m n i
  have hR : (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundR a b ℓ), jac1R W (f + g) u v x ℓ m n i)
      = (∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundR a b ℓ), jac1R W f u v x ℓ m n i)
        + ∑ i ∈ Finset.Icc (0 : ℤ) (jacBoundR a b ℓ), jac1R W g u v x ℓ m n i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => jac1R_add_cochain W f g u v x ℓ m n i
  simp only [jacDefect, hL, hR]
  abel

/-- The defect is scalar-homogeneous in the cochain. -/
theorem jacDefect_smul_cochain (W : VertexOperatorAlgebra 𝒱) (r : ℂ) (f : Cochain 𝒱)
    (a b d ℓ m n : ℤ) (u v x : 𝒱) :
    jacDefect W (r • f) a b d ℓ m n u v x = r • jacDefect W f a b d ℓ m n u v x := by
  have hL := Finset.sum_congr (rfl : Finset.Icc (0 : ℤ) (jacBoundL a b d m n) = _)
    fun i _ => jac1L_smul_cochain W r f u v x ℓ m n i
  have hR := Finset.sum_congr (rfl : Finset.Icc (0 : ℤ) (jacBoundR a b ℓ) = _)
    fun i _ => jac1R_smul_cochain W r f u v x ℓ m n i
  simp only [jacDefect, hL, hR, ← Finset.smul_sum, smul_sub]

/-! ### The local system as an explicit linear map, and its kernel -/

/-- **The local first-order Jacobi system at `(a,b,d,ℓ,m,n)`, as a linear map.**

It sends a graded cochain to the trilinear map

`𝒱ₐ × 𝒱_b × 𝒱_d → 𝒱_e,  (u,v,x) ↦ jacDefect …,   e = jacTarget a b d ℓ m n`,

i.e. to the value of "left-hand finite sum minus right-hand finite sum".  Its **target is
finite-dimensional** (a space of trilinear maps between graded pieces of `W`), so this really is
a finite system of linear equations; and its kernel is `LocalJacobiAt`
(`mem_ker_localJacobiDefect`). -/
noncomputable def localJacobiDefect (W : VertexOperatorAlgebra 𝒱) (a b d ℓ m n : ℤ) :
    ↥(gradedCochains W) →ₗ[ℂ] ↥(W.grading a) →ₗ[ℂ] ↥(W.grading b) →ₗ[ℂ] ↥(W.grading d) →ₗ[ℂ]
      ↥(W.grading (jacTarget a b d ℓ m n)) where
  toFun f :=
    { toFun := fun u =>
        { toFun := fun v =>
            { toFun := fun x =>
                ⟨jacDefect W (f : Cochain 𝒱) a b d ℓ m n (u : 𝒱) (v : 𝒱) (x : 𝒱),
                  jacDefect_mem_grading W f.2 u.2 v.2 x.2 ℓ m n⟩
              map_add' := fun x₁ x₂ => by
                ext; simp only [Submodule.coe_add, jacDefect_add_right]
              map_smul' := fun r x => by
                ext; simp only [SetLike.val_smul, RingHom.id_apply, jacDefect_smul_right] }
          map_add' := fun v₁ v₂ => by
            ext x; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
              Submodule.coe_add, jacDefect_add_mid]
          map_smul' := fun r v => by
            ext x; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
              RingHom.id_apply, SetLike.val_smul, jacDefect_smul_mid] }
      map_add' := fun u₁ u₂ => by
        ext v x; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
          Submodule.coe_add, jacDefect_add_left]
      map_smul' := fun r u => by
        ext v x; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
          RingHom.id_apply, SetLike.val_smul, jacDefect_smul_left] }
  map_add' := fun f g => by
    ext u v x; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
      Submodule.coe_add, jacDefect_add_cochain]
  map_smul' := fun r f => by
    ext u v x; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      RingHom.id_apply, SetLike.val_smul, jacDefect_smul_cochain]

@[simp] theorem localJacobiDefect_apply (W : VertexOperatorAlgebra 𝒱) (a b d ℓ m n : ℤ)
    (f : ↥(gradedCochains W)) (u : ↥(W.grading a)) (v : ↥(W.grading b)) (x : ↥(W.grading d)) :
    (localJacobiDefect W a b d ℓ m n f u v x : 𝒱)
      = jacDefect W (f : Cochain 𝒱) a b d ℓ m n (u : 𝒱) (v : 𝒱) (x : 𝒱) := rfl

/-- **The local Jacobi condition IS a kernel.** -/
theorem mem_ker_localJacobiDefect (W : VertexOperatorAlgebra 𝒱) (a b d ℓ m n : ℤ)
    (f : ↥(gradedCochains W)) :
    f ∈ LinearMap.ker (localJacobiDefect W a b d ℓ m n)
      ↔ LocalJacobiAt W (f : Cochain 𝒱) a b d ℓ m n := by
  rw [LinearMap.mem_ker, localJacobiAt_iff_jacDefect]
  constructor
  · intro h u hu v hv x hx
    have := congrArg (fun T => ((T ⟨u, hu⟩ ⟨v, hv⟩ ⟨x, hx⟩ : ↥(W.grading _)) : 𝒱)) h
    simpa using this
  · intro h
    ext u v x
    simpa using h (u : 𝒱) u.2 (v : 𝒱) v.2 (x : 𝒱) x.2

/-- The **local vacuum system**: evaluation of the `(0,b,c)` component at the vacuum. -/
noncomputable def vacuumDefect (W : VertexOperatorAlgebra 𝒱) (b c : ℤ) :
    ↥(gradedCochains W) →ₗ[ℂ] ↥(W.grading b) →ₗ[ℂ] ↥(W.grading c) where
  toFun f := gradedComponent W 0 b c f ⟨W.vacuum, W.vacuum_mem⟩
  map_add' f g := by simp
  map_smul' r f := by simp

/-- The **local creation system**: evaluation of the `(a,0,c)` component at the vacuum. -/
noncomputable def creationDefect (W : VertexOperatorAlgebra 𝒱) (a c : ℤ) :
    ↥(gradedCochains W) →ₗ[ℂ] ↥(W.grading a) →ₗ[ℂ] ↥(W.grading c) where
  toFun f :=
    { toFun := fun u => gradedComponent W a 0 c f u ⟨W.vacuum, W.vacuum_mem⟩
      map_add' := fun u₁ u₂ => by simp
      map_smul' := fun r u => by simp }
  map_add' f g := by ext u; simp
  map_smul' r f := by ext u; simp

/-- The local vacuum axiom is the kernel of `vacuumDefect`. -/
theorem mem_ker_vacuumDefect (W : VertexOperatorAlgebra 𝒱) (b c : ℤ)
    (f : ↥(gradedCochains W)) :
    f ∈ LinearMap.ker (vacuumDefect W b c) ↔ VacuumAxLocal W (f : Cochain 𝒱) b c := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h v hv
    have := congrArg (fun T => ((T ⟨v, hv⟩ : ↥(W.grading c)) : 𝒱)) h
    simpa [vacuumDefect] using this
  · intro h
    ext v
    simpa [vacuumDefect] using h (v : 𝒱) v.2

/-- The local creation axiom (for `c ≤ a`) is the kernel of `creationDefect`. -/
theorem mem_ker_creationDefect (W : VertexOperatorAlgebra 𝒱) (a c : ℤ)
    (f : ↥(gradedCochains W)) :
    f ∈ LinearMap.ker (creationDefect W a c)
      ↔ ∀ u ∈ W.grading a, cmode (f : Cochain 𝒱) u (gradedMode a 0 c) W.vacuum = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h u hu
    have := congrArg (fun T => ((T ⟨u, hu⟩ : ↥(W.grading c)) : 𝒱)) h
    simpa [creationDefect] using this
  · intro h
    ext u
    simpa [creationDefect] using h (u : 𝒱) u.2

/-- **The graded cocycle space is an intersection of explicit kernels.**

Every one of the three families is the kernel of a linear map into a **finite-dimensional** space
of (bi/tri)linear maps between graded pieces of `W`.  This replaces the definition of
`gradedCocycles` (a comap of the four-axiom submodule, whose Jacobi clause is an identity of
`finsum`s over `ℤ` quantified over all of `𝒱³`) by a system of finite linear equations. -/
theorem gradedCocycles_eq_iInf (W : VertexOperatorAlgebra 𝒱) :
    gradedCocycles W =
      ((⨅ b : ℤ, ⨅ c : ℤ, LinearMap.ker (vacuumDefect W b c))
        ⊓ ⨅ a : ℤ, ⨅ c : ℤ, ⨅ _ : c ≤ a, LinearMap.ker (creationDefect W a c))
        ⊓ ⨅ a : ℤ, ⨅ b : ℤ, ⨅ d : ℤ, ⨅ ℓ : ℤ, ⨅ m : ℤ, ⨅ n : ℤ,
            LinearMap.ker (localJacobiDefect W a b d ℓ m n) := by
  ext f
  rw [mem_gradedCocycles_iff_local, Submodule.mem_inf, Submodule.mem_inf]
  simp only [Submodule.mem_iInf, mem_ker_vacuumDefect, mem_ker_creationDefect,
    mem_ker_localJacobiDefect, CreationAxLocal]
  tauto

/-! ## ⚠ Which of the local equations actually bite

The local Jacobi system has one equation per `(a,b,d,ℓ,m,n) ∈ ℤ⁶`.  Three explicit cones of
those equations are automatically satisfied, and the remaining region is exactly where the
computation has to be done.  ⚠ The remaining region is **still infinite** for fixed input grades
`(a,b,d)`, because `ℓ` is bounded above but not below (as `ℓ → -∞` the target grade
`jacTarget → +∞`, so the equation constrains components at deeper and deeper tridegrees).  See the
file docstring, "What is *not* achieved". -/

/-- The defect vanishes when the first vector slot is `0`. -/
@[simp] theorem jacDefect_zero_left (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱)
    (a b d ℓ m n : ℤ) (v x : 𝒱) : jacDefect W f a b d ℓ m n 0 v x = 0 := by
  simp only [jacDefect, jac1L_zero_left, jac1R_zero_left, Finset.sum_const_zero, sub_zero]

/-- The defect vanishes when the second vector slot is `0`. -/
@[simp] theorem jacDefect_zero_mid (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱)
    (a b d ℓ m n : ℤ) (u x : 𝒱) : jacDefect W f a b d ℓ m n u 0 x = 0 := by
  simp only [jacDefect, jac1L_zero_mid, jac1R_zero_mid, Finset.sum_const_zero, sub_zero]

/-- The defect vanishes when the third vector slot is `0`. -/
@[simp] theorem jacDefect_zero_right (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱)
    (a b d ℓ m n : ℤ) (u v : 𝒱) : jacDefect W f a b d ℓ m n u v 0 = 0 := by
  simp only [jacDefect, jac1L_zero_right, jac1R_zero_right, Finset.sum_const_zero, sub_zero]

/-- **Vacuity 1: both index ranges empty.**  If `n > b+d-1` *and* `m > a+d-1` *and* `ℓ > a+b-1`
then the equation reads `0 = 0`.  So the system is nontrivial only in the cone
`ℓ ≤ a+b-1` together with `n ≤ b+d-1 ∨ m ≤ a+d-1`. -/
theorem localJacobiAt_of_bounds_neg (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱)
    (a b d ℓ m n : ℤ) (hL : jacBoundL a b d m n < 0) (hR : jacBoundR a b ℓ < 0) :
    LocalJacobiAt W f a b d ℓ m n := by
  intro u _ v _ x _
  rw [Finset.Icc_eq_empty (by omega), Finset.Icc_eq_empty (by omega), Finset.sum_empty,
    Finset.sum_empty]

/-- **Vacuity 2: negative target grade.**  Both sides of the equation lie in
`𝒱_{jacTarget a b d ℓ m n}`, which is `0` when that grade is negative.  So the system is
nontrivial only for `ℓ + m + n ≤ a + b + d - 2`. -/
theorem localJacobiAt_of_target_neg (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) (a b d ℓ m n : ℤ) (he : jacTarget a b d ℓ m n < 0) :
    LocalJacobiAt W f a b d ℓ m n := by
  rw [localJacobiAt_iff_jacDefect]
  intro u hu v hv x hx
  have h := jacDefect_mem_grading W hf hu hv hx (a := a) (b := b) (d := d) ℓ m n
  rw [W.positivity _ he] at h
  exact (Submodule.mem_bot ℂ).mp h

/-- **Vacuity 3: an empty input grade.**  If `𝒱ₐ = 0` — in particular whenever `a < 0`, by VOA4 —
there is nothing to test. -/
theorem localJacobiAt_of_source_bot (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱)
    (a b d ℓ m n : ℤ) (ha : W.grading a = ⊥) : LocalJacobiAt W f a b d ℓ m n := by
  rw [localJacobiAt_iff_jacDefect]
  intro u hu v _ x _
  rw [ha, Submodule.mem_bot] at hu
  rw [hu, jacDefect_zero_left]

/-- **Vacuity 3'** for the middle slot. -/
theorem localJacobiAt_of_mid_bot (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱)
    (a b d ℓ m n : ℤ) (hb : W.grading b = ⊥) : LocalJacobiAt W f a b d ℓ m n := by
  rw [localJacobiAt_iff_jacDefect]
  intro u _ v hv x _
  rw [hb, Submodule.mem_bot] at hv
  rw [hv, jacDefect_zero_mid]

/-- **Vacuity 3''** for the last slot. -/
theorem localJacobiAt_of_target_bot (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱)
    (a b d ℓ m n : ℤ) (hd : W.grading d = ⊥) : LocalJacobiAt W f a b d ℓ m n := by
  rw [localJacobiAt_iff_jacDefect]
  intro u _ v _ x hx
  rw [hd, Submodule.mem_bot] at hx
  rw [hx, jacDefect_zero_right]

/-- Collecting the three vacuity criteria: **the local Jacobi system is supported in the
explicit cone**

`0 ≤ a`, `0 ≤ b`, `0 ≤ d`, `ℓ + m + n ≤ a + b + d - 2`,
`(ℓ ≤ a + b - 1) ∨ (n ≤ b + d - 1) ∨ (m ≤ a + d - 1)`.

Everything outside it is automatic. -/
theorem localJacobiAt_of_outside_cone (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) (a b d ℓ m n : ℤ)
    (h : a < 0 ∨ b < 0 ∨ d < 0 ∨ a + b + d - 2 < ℓ + m + n
      ∨ (a + b - 1 < ℓ ∧ b + d - 1 < n ∧ a + d - 1 < m)) :
    LocalJacobiAt W f a b d ℓ m n := by
  rcases h with ha | hb | hd | he | ⟨h1, h2, h3⟩
  · exact localJacobiAt_of_source_bot W f a b d ℓ m n (W.positivity a ha)
  · exact localJacobiAt_of_mid_bot W f a b d ℓ m n (W.positivity b hb)
  · exact localJacobiAt_of_target_bot W f a b d ℓ m n (W.positivity d hd)
  · exact localJacobiAt_of_target_neg W hf a b d ℓ m n (by simp only [jacTarget]; omega)
  · exact localJacobiAt_of_bounds_neg W f a b d ℓ m n
      (by simp only [jacBoundL, max_lt_iff]; omega) (by simp only [jacBoundR]; omega)

/-! ## Reading the equation as an equation among graded components -/

/-- **Every occurrence of the cochain in the local equation is a graded component.**  For a
graded cochain and homogeneous `u ∈ 𝒱ₐ`, `v ∈ 𝒱_b`, the product `cmode f u n v` *is* the value of
`gradedComponent W a b (a+b-n-1) f` at `(u,v)`: the tridegree is determined by the two source
grades and the mode.  Applying this to the six occurrences of `f` inside `jac1L`/`jac1R` turns the
local equation into a linear equation among finitely many finite-dimensional blocks. -/
theorem cmode_eq_gradedComponent (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) {a b : ℤ} {u v : 𝒱} (hu : u ∈ W.grading a)
    (hv : v ∈ W.grading b) (n : ℤ) :
    cmode f u n v
      = (gradedComponent W a b (a + b - n - 1) ⟨f, hf⟩ ⟨u, hu⟩ ⟨v, hv⟩ : 𝒱) := by
  rw [gradedComponent_apply, gradedMode_of_target]

/-- **`gradedCocyclesAt` is the image of an explicitly cut-out kernel.**  Combining
`gradedCocycles_eq_iInf` with the definition of `gradedCocyclesAt`, the cocycle space at a
tridegree is the `gradedComponent`-image of an intersection of kernels of explicit linear maps
into finite-dimensional spaces — rather than the image of a submodule defined by a `finsum`
identity quantified over all of `𝒱³`.

⚠ Honest reading: this is an *image of a kernel*, not a kernel.  Computing its dimension at one
tridegree still requires solving the coupled system (see the file docstring, "The coupling"), and
this file does not claim otherwise. -/
theorem gradedCocyclesAt_eq_map_iInf (W : VertexOperatorAlgebra 𝒱) (a b c : ℤ) :
    gradedCocyclesAt W a b c =
      (((⨅ b' : ℤ, ⨅ c' : ℤ, LinearMap.ker (vacuumDefect W b' c'))
          ⊓ ⨅ a' : ℤ, ⨅ c' : ℤ, ⨅ _ : c' ≤ a', LinearMap.ker (creationDefect W a' c'))
          ⊓ ⨅ a' : ℤ, ⨅ b' : ℤ, ⨅ d' : ℤ, ⨅ ℓ : ℤ, ⨅ m : ℤ, ⨅ n : ℤ,
              LinearMap.ker (localJacobiDefect W a' b' d' ℓ m n)).map
        (gradedComponent W a b c) := by
  rw [gradedCocyclesAt, gradedCocycles_eq_iInf]

/-! ## The payoff: solving the finite system detects an obstruction

The point of localising is that the finite system can be *solved* in a concrete VOA, and a
solution that is not a field redefinition disproves rigidity.  The pipeline is:

1. write down the local equations at the tridegrees of interest (finite, explicit — this file);
2. solve them for a graded cochain `f` (finite linear algebra in the concrete VOA);
3. compare `gradedComponent W a b c f` with `gradedCoboundariesAt W a b c`, which is already a
   computable image (`Core.DeformationGraded`, `Examples.VirasoroDeformationLow`);
4. a mismatch gives a nonzero `DeformationSpaceAt` and hence `¬ IsRigid W`. -/

/-- Consistency check in the useful direction: every **coboundary** satisfies every local
equation.  (Immediate from `jacobiAx_of_isCoboundary` and the localisation.) -/
theorem localJacobiAt_of_isCoboundary (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : IsCoboundary W f) (a b d ℓ m n : ℤ) : LocalJacobiAt W f a b d ℓ m n :=
  (jacobiAx_iff_localJacobiAt W (coboundaries_le_gradedCochains W hf)).mp
    (jacobiAx_of_isCoboundary hf) a b d ℓ m n

/-- **Solving the local system produces genuine cocycle components.**  A graded cochain
satisfying every local equation has all of its components in the corresponding
`gradedCocyclesAt`. -/
theorem mem_gradedCocyclesAt_of_local (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) (hvac : ∀ b c : ℤ, VacuumAxLocal W f b c)
    (hcre : ∀ a c : ℤ, CreationAxLocal W f a c)
    (hjac : ∀ a b d ℓ m n : ℤ, LocalJacobiAt W f a b d ℓ m n) (a b c : ℤ) :
    gradedComponent W a b c ⟨f, hf⟩ ∈ gradedCocyclesAt W a b c :=
  Submodule.mem_map_of_mem ((mem_gradedCocycles_iff_local W ⟨f, hf⟩).mpr ⟨hvac, hcre, hjac⟩)

/-- **The obstruction detector.**  If the finite local system has a solution whose component
at some tridegree is *not* a coboundary component there, the deformation space at that tridegree
is nonzero. -/
theorem deformationSpaceAt_ne_zero_of_local (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) (hvac : ∀ b c : ℤ, VacuumAxLocal W f b c)
    (hcre : ∀ a c : ℤ, CreationAxLocal W f a c)
    (hjac : ∀ a b d ℓ m n : ℤ, LocalJacobiAt W f a b d ℓ m n) (a b c : ℤ)
    (hnot : gradedComponent W a b c ⟨f, hf⟩ ∉ gradedCoboundariesAt W a b c) :
    ∃ z : DeformationSpaceAt W a b c, z ≠ 0 := by
  refine ⟨Submodule.Quotient.mk
    ⟨_, mem_gradedCocyclesAt_of_local W hf hvac hcre hjac a b c⟩, ?_⟩
  intro h
  rw [Submodule.Quotient.mk_eq_zero] at h
  exact hnot h

/-- **…and it disproves rigidity.**  Combining with
`gradedCocyclesAt_le_gradedCoboundariesAt_of_isRigid`: a solution of the finite local system whose
component at some tridegree is not a coboundary component shows `W` is *not* rigid to first
order.  This is the sense in which the cohomological calculation here has become finite linear
algebra with a verdict attached. -/
theorem not_isRigid_of_local (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) (hvac : ∀ b c : ℤ, VacuumAxLocal W f b c)
    (hcre : ∀ a c : ℤ, CreationAxLocal W f a c)
    (hjac : ∀ a b d ℓ m n : ℤ, LocalJacobiAt W f a b d ℓ m n) (a b c : ℤ)
    (hnot : gradedComponent W a b c ⟨f, hf⟩ ∉ gradedCoboundariesAt W a b c) : ¬ IsRigid W := by
  intro hR
  exact hnot (gradedCocyclesAt_le_gradedCoboundariesAt_of_isRigid hR a b c
    (mem_gradedCocyclesAt_of_local W hf hvac hcre hjac a b c))

/-! ## Sanity: the size of the system at a concrete tridegree

⚠ These are arithmetic checks on the *bounds*, not deformation-theoretic statements.  They are
here because a localisation with an accidentally-empty index range would be vacuous, and the
cheapest guard against that is to exhibit the ranges. -/

/-- The left-hand index range for input grades `(2,2,2)` at `m = n = 0` is `{0,1,2,3}`. -/
theorem jacBoundL_two_two_two : jacBoundL 2 2 2 0 0 = 3 := by
  simp only [jacBoundL]; norm_num

/-- The right-hand index range for input grades `(2,2,·)` at `ℓ = 0` is `{0,1,2,3}`. -/
theorem jacBoundR_two_two : jacBoundR 2 2 0 = 3 := by
  simp only [jacBoundR]; norm_num

/-- The target grade of the `(2,2,2)` equation at `ℓ = m = n = 0` is `4`. -/
theorem jacTarget_two_two_two : jacTarget 2 2 2 0 0 0 = 4 := by
  simp only [jacTarget]; norm_num

/-- A full coboundary block forces a full cocycle block: `gradedCoboundariesAt = ⊤` gives
`gradedCocyclesAt = ⊤`, so the cocycle dimension there equals the cochain dimension.  This is how
the cocycle dimensions quoted for `virasoroVOA c` at `(2,2,3)` and `(2,2,4)` are pinned down
(`Examples.VirasoroDeformationLow` proves the coboundary blocks are `⊤` there); no Jacobi system
has to be solved to get them, which is exactly why those numbers are *not* an independent test of
this file. -/
theorem gradedCocyclesAt_eq_top_of_coboundaries_top (W : VertexOperatorAlgebra 𝒱) {a b c : ℤ}
    (h : gradedCoboundariesAt W a b c = ⊤) : gradedCocyclesAt W a b c = ⊤ :=
  eq_top_iff.mpr (h ▸ gradedCoboundariesAt_le_gradedCocyclesAt W a b c)

end Deform

end VOA
