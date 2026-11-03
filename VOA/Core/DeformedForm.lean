/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# First-order deformations of a symmetric bilinear form: the first two Jantzen layers

This file is **pure finite-dimensional linear algebra**. No vertex algebra appears anywhere in it,
and no knowledge of vertex algebras is needed to read it.

## The situation

Fix a finite-dimensional vector space `E` over a field `K` and a family of symmetric bilinear
forms on `E` deformed to first order in a parameter `t`,
```
B t  =  B₀ + t • B₁ ,
```
where `t` is thought of as a dual number (`t² = 0`), so that only `B₀` and `B₁` are data. We never
form `B t` itself: everything below is phrased directly in terms of the pair `(B₀, B₁)`.

Write `R := radBil B₀ = {v | ∀ w, B₀ v w = 0}` for the **radical** of the undeformed form. A vector
`s ∈ R` is a "relation at `t = 0`". The question this file answers is:

> which relations at `t = 0` survive to first order in `t`?

Concretely, `s` **lifts to first order** if there is a correction `s₁ ∈ E` with
`(B₀ + t • B₁) (s + t • s₁) = 0` modulo `t²`, i.e. with
```
∀ v, B₁ s v + B₀ s₁ v = 0.
```

## The main theorem

`lift_iff_pairing_zero` : for any `s`,
```
(∃ s₁, ∀ v, B₁ s v + B₀ s₁ v = 0)   ↔   (∀ v ∈ radBil B₀, B₁ s v = 0).
```
The right-hand side is a *finite, checkable pairing condition inside the radical*; the left-hand
side is an existential over all of `E`. Trading the second for the first is the entire point.

(The hypothesis `s ∈ radBil B₀` from the informal statement is not actually needed for either
direction, so it is not assumed; the intended application always supplies it anyway.)

## Why this replaces an explicit singular-vector computation

Set
```
F₁ := radBil B₀                                     -- relations at order t⁰
F₂ := {s ∈ F₁ | ∀ v ∈ F₁, B₁ s v = 0}               -- radical of B₁ restricted to F₁
```
These are the first two **Jantzen layers** of the deformation: `F₁ ⊇ F₂ ⊇ ⋯`, where `Fₙ` collects
the relations that survive to order `tⁿ⁻¹`. `mem_F2_iff_liftable` says exactly that `F₂` is the
set of elements of `F₁` that lift to first order — so the layer filtration, which is defined by a
*bilinear pairing on a subspace*, computes the deformation-theoretic obstruction.

The consequence used in practice is the contrapositive, `not_liftable_of_not_mem_F2`: if some
`s ∈ F₁` fails the pairing test (`s ∉ F₂`), then no first-order correction `s₁` exists at all.
In the deformation-rigidity argument this is what forces the deformation parameter to vanish:
one exhibits a single relation of the undeformed structure that already fails to lift, and no
explicit singular vector of the deformed structure ever has to be written down. `F₂` is computed
by a pairing among vectors one already has, whereas a singular vector must be produced by hand.

## What is proved, and what is taken from Mathlib

Everything rests on one surjectivity statement, `range_eq_dualAnnihilator_radBil`:
```
LinearMap.range B  =  (radBil B).dualAnnihilator     (B symmetric, E finite-dimensional)
```
"a linear functional on `E` is of the form `B x` iff it kills the radical of `B`".

Mathlib survey (searched `.lake/packages/mathlib` for `BilinForm`, `radical`, `dualAnnihilator`):

* Mathlib has **no** `radical` for bilinear forms — `QuadraticMap.radical`
  (`Mathlib/LinearAlgebra/QuadraticForm/Radical.lean`) is for *quadratic* maps. For a bilinear
  form the radical is just `LinearMap.ker B` (a form `B : E →ₗ[K] E →ₗ[K] K` is a map into the
  dual, and its kernel is the radical). So `radBil B` below is a one-line abbreviation for
  `LinearMap.ker B`, kept as a named definition only for readability. That this is Mathlib's own
  spelling is confirmed by `LinearMap.BilinForm.orthogonal_top_eq_ker`
  (`Mathlib/LinearAlgebra/BilinearForm/Orthogonal.lean`): `B.orthogonal ⊤ = LinearMap.ker B`
  for reflexive `B`.
* `LinearMap.dualAnnihilator_ker_eq_range_flip` (`Mathlib/LinearAlgebra/Dual/Lemmas.lean`) states
  `(LinearMap.ker B).dualAnnihilator = LinearMap.range B.flip` for `B : V₁ →ₗ[K] V₂ →ₗ[K] K` with
  `V₂` reflexive. This *is* the surjectivity statement, and it is what we use: for a symmetric `B`
  one has `B.flip = B`. It supersedes the rank-counting argument (range of `B` sits inside the
  annihilator of the radical by symmetry, and the two have equal dimension) and it is also what
  makes the quotient construction unnecessary for the main theorem.
* `LinearMap.Nondegenerate` / `LinearMap.BilinForm.Nondegenerate`
  (`Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean`, `.../BilinearForm/Properties.lean`) is
  reused verbatim for the nondegeneracy statements; we do not define our own.
* Mathlib has no "form induced on `E ⧸ radical`", so `quotForm` and `nondegenerate_quotForm`
  below are built from `Submodule.liftQ`. They are *not* needed for the main theorem — they are
  the conceptual explanation of it, recorded because they are the standard way the statement is
  proved by hand ("`B₀` becomes nondegenerate on `E / rad`, so every functional killing the
  radical is represented there").

Finite-dimensionality of `E` is genuinely needed (it enters through reflexivity of `E`):
on an infinite-dimensional space a functional killing the radical need not be represented.
-/

namespace VOA.DefForm

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-! ### The radical of a bilinear form -/

/-- The **radical** of a bilinear form `B` on `E`: the vectors that pair to zero with everything.

Viewing `B : E →ₗ[K] E →ₗ[K] K` as the map `E → Module.Dual K E`, this is exactly its kernel,
and that is how it is defined; `radBil` exists to make the statements below readable. -/
def radBil (B : E →ₗ[K] E →ₗ[K] K) : Submodule K E := LinearMap.ker B

theorem radBil_eq_ker (B : E →ₗ[K] E →ₗ[K] K) : radBil B = LinearMap.ker B := rfl

@[simp]
theorem mem_radBil {B : E →ₗ[K] E →ₗ[K] K} {v : E} :
    v ∈ radBil B ↔ ∀ w : E, B v w = 0 := by
  simp [radBil, LinearMap.ext_iff]

/-- A radical vector pairs to zero on the right. -/
theorem apply_of_mem_radBil {B : E →ₗ[K] E →ₗ[K] K} {v : E} (hv : v ∈ radBil B) (w : E) :
    B v w = 0 := mem_radBil.mp hv w

/-- For a **symmetric** form, a radical vector also pairs to zero on the left. -/
theorem apply_of_mem_radBil' {B : E →ₗ[K] E →ₗ[K] K} (hB : ∀ x y : E, B x y = B y x) {v : E}
    (hv : v ∈ radBil B) (w : E) : B w v = 0 := by
  rw [hB]; exact mem_radBil.mp hv w

/-- A form is nondegenerate exactly when its radical vanishes (one direction; the direction we
use). -/
theorem radBil_eq_bot_of_nondegenerate {B : E →ₗ[K] E →ₗ[K] K} (hB : LinearMap.Nondegenerate B) :
    radBil B = ⊥ := by
  refine Submodule.eq_bot_iff _ |>.mpr fun x hx => ?_
  exact hB.1 x (mem_radBil.mp hx)

/-! ### The key surjectivity statement -/

/-- **The engine of the file.** For a symmetric bilinear form on a finite-dimensional space, a
linear functional is represented by the form (`φ = B x` for some `x`) **iff** it annihilates the
radical.

This is `LinearMap.dualAnnihilator_ker_eq_range_flip` from Mathlib together with `B.flip = B`. -/
theorem range_eq_dualAnnihilator_radBil [FiniteDimensional K E] {B : E →ₗ[K] E →ₗ[K] K}
    (hB : ∀ x y : E, B x y = B y x) :
    LinearMap.range B = (radBil B).dualAnnihilator := by
  have hflip : B.flip = B := by
    ext x y
    exact hB y x
  rw [radBil_eq_ker, LinearMap.dualAnnihilator_ker_eq_range_flip, hflip]

/-- Pointwise form of `range_eq_dualAnnihilator_radBil`: a functional killing the radical is
represented by the form. -/
theorem exists_apply_eq_of_annihilates_radBil [FiniteDimensional K E] {B : E →ₗ[K] E →ₗ[K] K}
    (hB : ∀ x y : E, B x y = B y x) (φ : E →ₗ[K] K) (hφ : ∀ v ∈ radBil B, φ v = 0) :
    ∃ x : E, ∀ v : E, B x v = φ v := by
  have hmem : φ ∈ (radBil B).dualAnnihilator := (Submodule.mem_dualAnnihilator φ).mpr hφ
  rw [← range_eq_dualAnnihilator_radBil hB] at hmem
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, fun v => by rw [hx]⟩

/-! ### The main equivalence -/

/-- **Main theorem.** Let `B₀` be a symmetric bilinear form on a finite-dimensional space `E`, and
let `B₁` be an arbitrary bilinear form (the first-order deformation). For any `s : E`:

* `s` admits a first-order correction `s₁` making it a radical vector of `B₀ + t • B₁` modulo `t²`,
  i.e. `∀ v, B₁ s v + B₀ s₁ v = 0`;

**iff**

* `s` pairs to zero with the whole radical of `B₀` under `B₁`.

Forward direction: for `v` in the radical, `B₀ s₁ v = B₀ v s₁ = 0` by symmetry, so the defining
equation collapses to `B₁ s v = 0`. Backward direction: `B₁ s` is then a functional killing the
radical, hence represented by `B₀`, by `exists_apply_eq_of_annihilates_radBil`.

Note the radical hypothesis on `s` itself is never used. -/
theorem lift_iff_pairing_zero [FiniteDimensional K E] {B₀ B₁ : E →ₗ[K] E →ₗ[K] K}
    (hB₀ : ∀ x y : E, B₀ x y = B₀ y x) (s : E) :
    (∃ s₁ : E, ∀ v : E, B₁ s v + B₀ s₁ v = 0) ↔ ∀ v ∈ radBil B₀, B₁ s v = 0 := by
  constructor
  · rintro ⟨s₁, h⟩ v hv
    have h0 : B₀ s₁ v = 0 := apply_of_mem_radBil' hB₀ hv s₁
    have := h v
    rwa [h0, add_zero] at this
  · intro h
    obtain ⟨s₁, hs₁⟩ :=
      exists_apply_eq_of_annihilates_radBil hB₀ (-(B₁ s)) (by
        intro v hv
        simp [h v hv])
    refine ⟨s₁, fun v => ?_⟩
    have : B₀ s₁ v = -(B₁ s v) := by simpa using hs₁ v
    rw [this, add_neg_cancel]

/-! ### The Jantzen layers -/

/-- The **first Jantzen layer**: the relations of the undeformed form, i.e. the radical of `B₀`. -/
def F1 (B₀ : E →ₗ[K] E →ₗ[K] K) : Submodule K E := radBil B₀

theorem F1_eq_radBil (B₀ : E →ₗ[K] E →ₗ[K] K) : F1 B₀ = radBil B₀ := rfl

@[simp]
theorem mem_F1 {B₀ : E →ₗ[K] E →ₗ[K] K} {s : E} : s ∈ F1 B₀ ↔ ∀ w : E, B₀ s w = 0 := mem_radBil

/-- The **second Jantzen layer**: the radical of `B₁` restricted to `F₁`. -/
def F2 (B₀ B₁ : E →ₗ[K] E →ₗ[K] K) : Submodule K E where
  carrier := {s | s ∈ F1 B₀ ∧ ∀ v ∈ F1 B₀, B₁ s v = 0}
  zero_mem' := ⟨(F1 B₀).zero_mem, by simp⟩
  add_mem' := fun {a b} ha hb =>
    ⟨(F1 B₀).add_mem ha.1 hb.1, fun v hv => by simp [ha.2 v hv, hb.2 v hv]⟩
  smul_mem' := fun c {a} ha => ⟨(F1 B₀).smul_mem c ha.1, fun v hv => by simp [ha.2 v hv]⟩

@[simp]
theorem mem_F2 {B₀ B₁ : E →ₗ[K] E →ₗ[K] K} {s : E} :
    s ∈ F2 B₀ B₁ ↔ s ∈ F1 B₀ ∧ ∀ v ∈ F1 B₀, B₁ s v = 0 := Iff.rfl

/-- The layers are nested: `F₂ ≤ F₁`. -/
theorem F2_le_F1 (B₀ B₁ : E →ₗ[K] E →ₗ[K] K) : F2 B₀ B₁ ≤ F1 B₀ := fun _ hs => hs.1

/-- **The layer filtration computes liftability.** An element of `F₁` lies in `F₂` exactly when it
survives to first order in the deformation parameter. -/
theorem mem_F2_iff_liftable [FiniteDimensional K E] {B₀ B₁ : E →ₗ[K] E →ₗ[K] K}
    (hB₀ : ∀ x y : E, B₀ x y = B₀ y x) (s : E) :
    s ∈ F2 B₀ B₁ ↔ s ∈ F1 B₀ ∧ ∃ s₁ : E, ∀ v : E, B₁ s v + B₀ s₁ v = 0 := by
  rw [mem_F2, lift_iff_pairing_zero hB₀ s]
  rfl

/-- **The form the rigidity argument consumes.** If a relation of the undeformed form fails the
`F₂` pairing test, then it does not lift to first order at all: there is *no* correction `s₁`.

In the application, `s` is an explicit relation of the undeformed vertex-algebra structure and the
pairing `B₁ s v` is computed directly; the conclusion is that the deformation parameter must
vanish. -/
theorem not_liftable_of_not_mem_F2 [FiniteDimensional K E] {B₀ B₁ : E →ₗ[K] E →ₗ[K] K}
    (hB₀ : ∀ x y : E, B₀ x y = B₀ y x) {s : E} (hs₁ : s ∈ F1 B₀) (hs₂ : s ∉ F2 B₀ B₁) :
    ¬∃ s₁ : E, ∀ v : E, B₁ s v + B₀ s₁ v = 0 := by
  intro h
  exact hs₂ ((mem_F2_iff_liftable hB₀ s).mpr ⟨hs₁, h⟩)

/-- Explicit witness form of `not_liftable_of_not_mem_F2`: a single radical vector `v` with
`B₁ s v ≠ 0` already obstructs the lift. -/
theorem not_liftable_of_pairing_ne_zero [FiniteDimensional K E] {B₀ B₁ : E →ₗ[K] E →ₗ[K] K}
    (hB₀ : ∀ x y : E, B₀ x y = B₀ y x) {s v : E} (hv : v ∈ radBil B₀) (hsv : B₁ s v ≠ 0) :
    ¬∃ s₁ : E, ∀ v : E, B₁ s v + B₀ s₁ v = 0 := by
  intro h
  exact hsv ((lift_iff_pairing_zero hB₀ s).mp h v hv)

/-! ### Degenerate sanity checks -/

/-- If the deformation is trivial (`B₁ = 0`) then nothing is obstructed: `F₂ = F₁`. -/
@[simp]
theorem F2_zero (B₀ : E →ₗ[K] E →ₗ[K] K) : F2 B₀ 0 = F1 B₀ := by
  ext s
  simp

/-- If the undeformed form is already nondegenerate there are no relations to lift: `F₁ = ⊥`. -/
theorem F1_eq_bot_of_nondegenerate {B₀ : E →ₗ[K] E →ₗ[K] K} (hB₀ : LinearMap.Nondegenerate B₀) :
    F1 B₀ = ⊥ := radBil_eq_bot_of_nondegenerate hB₀

/-- ... and then `F₂ = ⊥` as well, so the whole obstruction theory is vacuous. -/
theorem F2_eq_bot_of_nondegenerate {B₀ : E →ₗ[K] E →ₗ[K] K} (hB₀ : LinearMap.Nondegenerate B₀)
    (B₁ : E →ₗ[K] E →ₗ[K] K) : F2 B₀ B₁ = ⊥ :=
  le_bot_iff.mp (F1_eq_bot_of_nondegenerate hB₀ ▸ F2_le_F1 B₀ B₁)

/-! ### Appendix: the form induced on `E ⧸ radical`, and its nondegeneracy

This section is **not used** by anything above: `lift_iff_pairing_zero` goes through Mathlib's
`LinearMap.dualAnnihilator_ker_eq_range_flip` directly. It records the classical explanation of
why that statement is true — quotienting by the radical is precisely what turns a symmetric form
into a nondegenerate one, and `range_eq_dualAnnihilator_radBil` is the representability of
functionals that follows. Mathlib does not have this construction for bilinear forms, so it is
built here from `Submodule.liftQ`.
-/

section Quot

variable (B : E →ₗ[K] E →ₗ[K] K)

/-- `B` descends in its **first** slot to `E ⧸ radBil B`: the radical is by definition the kernel
of `B` viewed as a map `E →ₗ[K] Module.Dual K E`, so `Submodule.liftQ` applies with no further
hypothesis. Symmetry is not needed here. -/
def liftFst : (E ⧸ radBil B) →ₗ[K] E →ₗ[K] K := (radBil B).liftQ B le_rfl

@[simp]
theorem liftFst_mk (x y : E) : liftFst B (Submodule.Quotient.mk x) y = B x y := rfl

variable (hB : ∀ x y : E, B x y = B y x)

/-- The bilinear form induced by a symmetric `B` on the quotient `E ⧸ radBil B`.

The second descent is where symmetry enters: for `x` in the radical, `B y x = B x y = 0` for all
`y`, so the partially-applied map kills the radical in the remaining slot too. -/
def quotForm : (E ⧸ radBil B) →ₗ[K] (E ⧸ radBil B) →ₗ[K] K :=
  (radBil B).liftQ (liftFst B).flip <| by
    intro x hx
    refine LinearMap.mem_ker.mpr (LinearMap.ext fun q => ?_)
    refine Submodule.Quotient.induction_on _ q fun y => ?_
    change B y x = 0
    rw [hB]
    exact mem_radBil.mp hx y

@[simp]
theorem quotForm_mk (x y : E) :
    quotForm B hB (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = B x y := hB y x

/-- The induced form is symmetric. -/
theorem quotForm_symm (p q : E ⧸ radBil B) : quotForm B hB p q = quotForm B hB q p := by
  refine Submodule.Quotient.induction_on _ p fun x => ?_
  refine Submodule.Quotient.induction_on _ q fun y => ?_
  rw [quotForm_mk, quotForm_mk, hB]

/-- **Quotienting by the radical makes a symmetric form nondegenerate.** This is the supporting
fact behind `range_eq_dualAnnihilator_radBil`; `LinearMap.Nondegenerate` is Mathlib's notion
(left- and right-separating). -/
theorem nondegenerate_quotForm : LinearMap.Nondegenerate (quotForm B hB) := by
  constructor
  · intro p hp
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (radBil B) p
    rw [Submodule.Quotient.mk_eq_zero]
    refine mem_radBil.mpr fun w => ?_
    have h := hp (Submodule.Quotient.mk w)
    rwa [quotForm_mk] at h
  · intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (radBil B) q
    rw [Submodule.Quotient.mk_eq_zero]
    refine mem_radBil.mpr fun w => ?_
    have h := hq (Submodule.Quotient.mk w)
    rw [quotForm_mk] at h
    rw [hB]
    exact h

/-- The radical of the induced form is trivial. -/
theorem radBil_quotForm_eq_bot : radBil (quotForm B hB) = ⊥ :=
  radBil_eq_bot_of_nondegenerate (nondegenerate_quotForm B hB)

end Quot

end VOA.DefForm
