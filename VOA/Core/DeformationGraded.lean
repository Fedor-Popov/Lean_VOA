/-
Copyright (c) 2026 Leonardo Rastelli, Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.Deformation
import VOA.Core.Borcherds

/-!
# First-order deformations as linear algebra: the cochain complex and its graded pieces

`Core.Deformation` packages a first-order deformation as a *structure*
`FirstOrderDeformation W`, whose fields are the order-`t` parts of VA5, VA2, VA3 and the
Borcherds/Jacobi identity.  Every one of those conditions is **linear** in the datum `Y₁`.  This
file makes that visible and usable:

* the ambient space of cochains is `Cochain 𝒱 = 𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧` — literally the type of
  the field `Y₁`;
* `cocycles W` is the *submodule* cut out by the four axioms, and
  `cocycleEquivDeformation` identifies `↥(cocycles W)` with `FirstOrderDeformation W`;
* `Deform.coboundaries W` (built already in `Core.Deformation`) is the image of the field
  redefinitions, and `coboundaries_le_cocycles` proves the thing that makes the picture a
  complex: a coboundary really does satisfy the first-order Jacobi identity;
* `IsRigid W ↔ cocycles W ≤ coboundaries W`, and the deformation space `H W` is the honest
  quotient, with `isRigid_iff_H_trivial`.

Everything then restricts to the grading.  A `PreVertexAlgebra` in this repository already carries
`isInternal : DirectSum.IsInternal grading` and `finrank : ∀ n, FiniteDimensional ℂ (grading n)`
as *structure fields*, so **no extra hypothesis or typeclass is introduced anywhere below**, and
every definition instantiates directly at `virasoroVOA c` — including
`FiniteDimensional ℂ (GradedCochain (virasoroVOA c) a b c')` and
`FiniteDimensional ℂ (DeformationSpaceAt (virasoroVOA c) a b c')`, which typeclass inference
finds with no input (checked).

## ⚠ The mode index: what is and is not finite

For fixed grades this is the crux, so it is stated precisely.

If `u ∈ 𝒱ₐ`, `v ∈ 𝒱_b` and the deformation is graded, then `u¹₍ₙ₎v ∈ 𝒱_{a+b-n-1}`.  Hence:

* **The mode is not an independent index.**  Once the three grades `a` (of `u`), `b` (of `v`) and
  `c` (of the output) are fixed, the mode is *determined*: `n = a + b - c - 1`
  (`gradedMode`).  So "the components between fixed grades, at each mode" is the same data as
  "the components at each triple of grades".
* **Bounded above, automatically.**  `𝒱_k = 0` for `k < 0` (VOA4, `positivity`), so
  `u¹₍ₙ₎v = 0` as soon as `n > a + b - 1`: for a graded cochain the truncation axiom is *free*
  above that bound (`gradedCochain_vanishing_of_gt`, `truncated_of_graded`).
* **⚠ NOT bounded below.**  As `n → -∞` the target grade `a+b-n-1 → +∞`, and those graded pieces
  are in general nonzero.  So *infinitely many modes do contribute between two fixed grades*, and
  the space of components at fixed `(a,b)` summed over all modes is **infinite-dimensional**.
  The finite-dimensional object is the component at a fixed *triple* `(a,b,c)`, which is the
  single mode `a+b-c-1`.  `GradedCochain W a b c` is that space and it is finite-dimensional
  (`instFiniteDimensionalGradedCochain`).

This is why the "bidegree" of the task is realised here as a **tridegree** `(a,b,c)`.  Nothing is
lost: `(a,b,c) ↦ (a,b,n)` is a bijection for each fixed pair.

## ⚠ What is proved about rigidity, and what is only a target

* Proved: `isTrivial_of_components` — if a graded deformation and a *single* grade-preserving
  `φ` agree on every graded component, the deformation is trivial.  This is the step that turns
  the finite componentwise data into the global statement; it uses `isInternal`.
* Proved: `isRigid_iff_cocycles_le_coboundaries` and `isRigid_iff_H_trivial` — rigidity *is*
  the vanishing of the (global) quotient.
* Proved: `gradedCocyclesAt_le_gradedCoboundariesAt_of_isRigid` — the easy direction.  So a
  **nonzero** `DeformationSpaceAt W a b c` disproves rigidity: the finite computation is a
  genuine obstruction theory even though the converse is open.
* Proved: `isRigidGraded_of_gradedCocycles_le` — the correctly-posed criterion, phrased for the
  *total* family rather than tridegree by tridegree.
* ⚠ **Not proved, and stated as the named target `GradedToGlobalRigidity`:** that vanishing of
  the finite-dimensional cokernel at *every* tridegree implies `IsRigid`.  The obstruction is
  precise and is recorded in the docstring of `GradedToGlobalRigidity`: the coboundary map at
  tridegree `(a,b,c)` only sees the three blocks `φ_a, φ_b, φ_c` of `φ`, so per-tridegree
  surjectivity produces one `φ` *per tridegree*, and there is no argument here that those choices
  can be made simultaneously.  Vanishing of each cokernel of a diagram does not give vanishing of
  the cokernel of the product map.

## Main results

* `cocycles` — the four first-order axioms as a `Submodule ℂ (Cochain 𝒱)`.
* `cocycleEquivDeformation` — `↥(cocycles W) ≃ FirstOrderDeformation W`.
* `coboundaries_le_cocycles` — coboundaries are cocycles (the complex is a complex).
* `isRigid_iff_cocycles_le_coboundaries`, `H`, `isRigid_iff_H_trivial`.
* `truncated_of_graded` — for a graded cochain the truncation axiom is automatic.
* `gradedCochains_ext`, `totalComponent_injective` — the finite componentwise data is faithful.
* `isRigidGraded_of_gradedCocycles_le`,
  `gradedCocyclesAt_le_gradedCoboundariesAt_of_isRigid`.
* `GradedCochain`, `instFiniteDimensionalGradedCochain` — the finite-dimensional cochain space
  at a tridegree.
* `gradedComponent` — the component map, a `ℂ`-linear map out of the graded cochains.
* `gradedCocyclesAt`, `gradedCoboundariesAt`, `gradedCoboundariesAt_le_gradedCocyclesAt`,
  `DeformationSpaceAt` and its `FiniteDimensional` instance.
* `isTrivial_of_components` — components determine triviality, given one global `φ`.
* ⚠ `GradedToGlobalRigidity` — the named target, *not* a theorem.

## Status
Complete and `sorry`-free / `admit`-free / `native_decide`-free; no new axioms.

## Dependencies
`Core.Deformation` (the structure, `IsCoboundary`, `coboundaries`, `IsRigid`),
`Core.Borcherds` (`VertexOperatorAlgebra.jacobi`, the undeformed identity whose linearisation is
the cocycle condition, and the support-finiteness lemmas `BR_fin`, `Puv_fin`, `Pvu_fin`).
-/

namespace VOA

namespace Deform

open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The ambient cochain space and its modes -/

/-- The ambient space of **deformation cochains**: exactly the type of the field
`FirstOrderDeformation.Y1`.  It is a `ℂ`-module, and all four first-order axioms are linear
conditions on it, which is the whole point of this file. -/
abbrev Cochain (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] : Type u :=
  𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧

/-- The `n`-th product of a cochain, `u¹₍ₙ₎v = mode (f u) n v`.  For `f = D.Y1` this is
`D.smul₁` on the nose (`cmode_Y1`). -/
def cmode (f : Cochain 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) : 𝒱 := mode (f u) n v

theorem cmode_def (f : Cochain 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) : cmode f u n v = mode (f u) n v := rfl

/-- `cmode` of the `Y₁` of a deformation is the deformation's own product `smul₁`. -/
theorem cmode_Y1 {W : VertexOperatorAlgebra 𝒱} (D : FirstOrderDeformation W) (u : 𝒱) (n : ℤ)
    (v : 𝒱) : cmode D.Y1 u n v = D.smul₁ u n v := rfl

@[simp] theorem cmode_add_cochain (f g : Cochain 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    cmode (f + g) u n v = cmode f u n v + cmode g u n v := by
  simp only [cmode_def, LinearMap.add_apply, mode_add]

@[simp] theorem cmode_smul_cochain (c : ℂ) (f : Cochain 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    cmode (c • f) u n v = c • cmode f u n v := by
  simp only [cmode_def, LinearMap.smul_apply, mode_smul]

@[simp] theorem cmode_zero_cochain (u : 𝒱) (n : ℤ) (v : 𝒱) :
    cmode (0 : Cochain 𝒱) u n v = 0 := by
  simp only [cmode_def, LinearMap.zero_apply, mode_zero, LinearMap.zero_apply]

@[simp] theorem cmode_add_left (f : Cochain 𝒱) (u₁ u₂ : 𝒱) (n : ℤ) (v : 𝒱) :
    cmode f (u₁ + u₂) n v = cmode f u₁ n v + cmode f u₂ n v := by
  simp only [cmode_def, map_add, mode_add, LinearMap.add_apply]

@[simp] theorem cmode_smul_left (f : Cochain 𝒱) (c : ℂ) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    cmode f (c • u) n v = c • cmode f u n v := by
  simp only [cmode_def, map_smul, mode_smul, LinearMap.smul_apply]

@[simp] theorem cmode_add_right (f : Cochain 𝒱) (u : 𝒱) (n : ℤ) (v₁ v₂ : 𝒱) :
    cmode f u n (v₁ + v₂) = cmode f u n v₁ + cmode f u n v₂ :=
  map_add (mode (f u) n) v₁ v₂

@[simp] theorem cmode_smul_right (f : Cochain 𝒱) (u : 𝒱) (c : ℂ) (n : ℤ) (v : 𝒱) :
    cmode f u n (c • v) = c • cmode f u n v :=
  map_smul (mode (f u) n) c v

@[simp] theorem cmode_zero_left (f : Cochain 𝒱) (n : ℤ) (v : 𝒱) : cmode f 0 n v = 0 := by
  simp only [cmode_def, map_zero, mode_zero, LinearMap.zero_apply]

@[simp] theorem cmode_zero_right (f : Cochain 𝒱) (u : 𝒱) (n : ℤ) : cmode f u n 0 = 0 :=
  map_zero (mode (f u) n)

/-- A cochain is determined by its modes. -/
theorem cochain_ext {f g : Cochain 𝒱} (h : ∀ u n v, cmode f u n v = cmode g u n v) : f = g := by
  refine LinearMap.ext fun u => FormalDist.ext fun k => LinearMap.ext fun v => ?_
  have := h u (-k - 1) v
  rwa [cmode_def, cmode_def, mode_apply, mode_apply, show -(-k - 1) - 1 = k from by ring] at this

/-- A cochain all of whose modes vanish is zero. -/
theorem cochain_eq_zero {f : Cochain 𝒱} (h : ∀ u n v, cmode f u n v = 0) : f = 0 :=
  cochain_ext fun u n v => by rw [h u n v, cmode_zero_cochain]

/-! ## The four axioms, as linear conditions -/

/-- **Order-`t` VA5.** The truncation axiom, as a condition on a cochain. -/
def Truncated (f : Cochain 𝒱) : Prop :=
  ∀ u v : 𝒱, ∃ N : ℤ, ∀ n : ℤ, N ≤ n → cmode f u n v = 0

/-- **Order-`t` VA3.** The creation axiom, as a condition on a cochain. -/
def CreationAx (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) : Prop :=
  ∀ (u : 𝒱) (n : ℤ), -1 ≤ n → cmode f u n W.vacuum = 0

/-- **Order-`t` Jacobi/Borcherds.** The cocycle condition, as a condition on a cochain: it is
`FirstOrderDeformation.borcherds₁` with `D.smul₁` replaced by `cmode f`, and it is *linear* in
`f` (`cocycles` below). -/
def JacobiAx (W : VertexOperatorAlgebra 𝒱) (f : Cochain 𝒱) : Prop :=
  ∀ (u v x : 𝒱) (ℓ m n : ℤ),
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (cmode f u (ℓ + m - i) (W.smul v (n + i) x)
          + W.smul u (ℓ + m - i) (cmode f v (n + i) x)
          - negOnePow ℓ •
            (cmode f v (ℓ + n - i) (W.smul u (m + i) x)
              + W.smul v (ℓ + n - i) (cmode f u (m + i) x))))
      = ∑ᶠ i : ℤ, cbz m i •
          (W.smul (cmode f u (ℓ + i) v) (m + n - i) x
            + cmode f (W.smul u (ℓ + i) v) (m + n - i) x)

/-! ### The two `finsum`s of `JacobiAx` are finite sums

Same proofs as `Deform.FirstOrderDeformation.jacobiLHS_support_finite` /
`jacobiRHS_support_finite`, but hypothesised on `Truncated f` rather than on a bundled
deformation, so that they are available while *building* the submodule. -/

theorem jacLHS_support_finite (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱} (hf : Truncated f)
    (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ℓ i) •
        (cmode f u (ℓ + m - i) (W.smul v (n + i) x)
          + W.smul u (ℓ + m - i) (cmode f v (n + i) x)
          - negOnePow ℓ •
            (cmode f v (ℓ + n - i) (W.smul u (m + i) x)
              + W.smul v (ℓ + n - i) (cmode f u (m + i) x)))).Finite := by
  obtain ⟨Nv, hNv⟩ := W.toPreVertexAlgebra.smul_eventually_zero v x
  obtain ⟨Nu, hNu⟩ := W.toPreVertexAlgebra.smul_eventually_zero u x
  obtain ⟨Mv, hMv⟩ := hf v x
  obtain ⟨Mu, hMu⟩ := hf u x
  refine Set.Finite.subset
    (Set.finite_Icc 0 (max (max (Nv - n) (Mv - n)) (max (Nu - m) (Mu - m)))) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · rw [max_lt_iff, max_lt_iff, max_lt_iff] at h
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
    rw [hNv (n + i) (by omega), hMv (n + i) (by omega), hNu (m + i) (by omega),
      hMu (m + i) (by omega)]
    simp

theorem jacRHS_support_finite (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱} (hf : Truncated f)
    (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ => cbz m i •
        (W.smul (cmode f u (ℓ + i) v) (m + n - i) x
          + cmode f (W.smul u (ℓ + i) v) (m + n - i) x)).Finite := by
  obtain ⟨N, hN⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
  obtain ⟨M, hM⟩ := hf u v
  refine Set.Finite.subset (Set.finite_Icc 0 (max (N - ℓ) (M - ℓ))) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg m h, zero_smul]
  · rw [max_lt_iff] at h
    obtain ⟨h1, h2⟩ := h
    rw [hN (ℓ + i) (by omega), hM (ℓ + i) (by omega)]
    simp

/-! ## The cocycle submodule -/

/-- The **cocycles**: the cochains satisfying all four first-order axioms, as a submodule of
`Cochain 𝒱`.  Membership is *definitionally* the conjunction of the fields of
`FirstOrderDeformation` (see `cocycleEquivDeformation`), so this is not a new notion — it is the
statement that the notion is linear. -/
def cocycles (W : VertexOperatorAlgebra 𝒱) : Submodule ℂ (Cochain 𝒱) where
  carrier := {f | Truncated f ∧ f W.vacuum = 0 ∧ CreationAx W f ∧ JacobiAx W f}
  add_mem' := by
    rintro f g ⟨hft, hfv, hfc, hfj⟩ ⟨hgt, hgv, hgc, hgj⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u v
      obtain ⟨Nf, hNf⟩ := hft u v
      obtain ⟨Ng, hNg⟩ := hgt u v
      exact ⟨max Nf Ng, fun n hn => by
        rw [cmode_add_cochain, hNf n (le_trans (le_max_left _ _) hn),
          hNg n (le_trans (le_max_right _ _) hn), add_zero]⟩
    · rw [LinearMap.add_apply, hfv, hgv, add_zero]
    · intro u n hn
      rw [cmode_add_cochain, hfc u n hn, hgc u n hn, add_zero]
    · intro u v x ℓ m n
      have hL : ∀ i : ℤ, (negOnePow i * cbz ℓ i) •
          (cmode (f + g) u (ℓ + m - i) (W.smul v (n + i) x)
            + W.smul u (ℓ + m - i) (cmode (f + g) v (n + i) x)
            - negOnePow ℓ •
              (cmode (f + g) v (ℓ + n - i) (W.smul u (m + i) x)
                + W.smul v (ℓ + n - i) (cmode (f + g) u (m + i) x)))
          = (negOnePow i * cbz ℓ i) •
              (cmode f u (ℓ + m - i) (W.smul v (n + i) x)
                + W.smul u (ℓ + m - i) (cmode f v (n + i) x)
                - negOnePow ℓ •
                  (cmode f v (ℓ + n - i) (W.smul u (m + i) x)
                    + W.smul v (ℓ + n - i) (cmode f u (m + i) x)))
            + (negOnePow i * cbz ℓ i) •
              (cmode g u (ℓ + m - i) (W.smul v (n + i) x)
                + W.smul u (ℓ + m - i) (cmode g v (n + i) x)
                - negOnePow ℓ •
                  (cmode g v (ℓ + n - i) (W.smul u (m + i) x)
                    + W.smul v (ℓ + n - i) (cmode g u (m + i) x))) := by
        intro i
        simp only [cmode_add_cochain, PreVertexAlgebra.smul_add_right, smul_add, smul_sub]
        abel
      have hR : ∀ i : ℤ, cbz m i •
          (W.smul (cmode (f + g) u (ℓ + i) v) (m + n - i) x
            + cmode (f + g) (W.smul u (ℓ + i) v) (m + n - i) x)
          = cbz m i •
              (W.smul (cmode f u (ℓ + i) v) (m + n - i) x
                + cmode f (W.smul u (ℓ + i) v) (m + n - i) x)
            + cbz m i •
              (W.smul (cmode g u (ℓ + i) v) (m + n - i) x
                + cmode g (W.smul u (ℓ + i) v) (m + n - i) x) := by
        intro i
        simp only [cmode_add_cochain, PreVertexAlgebra.smul_add_left, smul_add]
        abel
      rw [finsum_congr hL, finsum_congr hR,
        finsum_add_distrib (jacLHS_support_finite W hft u v x ℓ m n)
          (jacLHS_support_finite W hgt u v x ℓ m n),
        finsum_add_distrib (jacRHS_support_finite W hft u v x ℓ m n)
          (jacRHS_support_finite W hgt u v x ℓ m n),
        hfj u v x ℓ m n, hgj u v x ℓ m n]
  zero_mem' := by
    refine ⟨fun u v => ⟨0, fun n _ => cmode_zero_cochain u n v⟩, rfl,
      fun u n _ => cmode_zero_cochain u n W.vacuum, fun u v x ℓ m n => ?_⟩
    simp
  smul_mem' := by
    rintro c f ⟨hft, hfv, hfc, hfj⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u v
      obtain ⟨N, hN⟩ := hft u v
      exact ⟨N, fun n hn => by rw [cmode_smul_cochain, hN n hn, smul_zero]⟩
    · rw [LinearMap.smul_apply, hfv, smul_zero]
    · intro u n hn
      rw [cmode_smul_cochain, hfc u n hn, smul_zero]
    · intro u v x ℓ m n
      have hL : ∀ i : ℤ, (negOnePow i * cbz ℓ i) •
          (cmode (c • f) u (ℓ + m - i) (W.smul v (n + i) x)
            + W.smul u (ℓ + m - i) (cmode (c • f) v (n + i) x)
            - negOnePow ℓ •
              (cmode (c • f) v (ℓ + n - i) (W.smul u (m + i) x)
                + W.smul v (ℓ + n - i) (cmode (c • f) u (m + i) x)))
          = c • ((negOnePow i * cbz ℓ i) •
              (cmode f u (ℓ + m - i) (W.smul v (n + i) x)
                + W.smul u (ℓ + m - i) (cmode f v (n + i) x)
                - negOnePow ℓ •
                  (cmode f v (ℓ + n - i) (W.smul u (m + i) x)
                    + W.smul v (ℓ + n - i) (cmode f u (m + i) x)))) := by
        intro i
        simp only [cmode_smul_cochain, PreVertexAlgebra.smul_smul_right, smul_add, smul_sub,
          smul_comm c]
      have hR : ∀ i : ℤ, cbz m i •
          (W.smul (cmode (c • f) u (ℓ + i) v) (m + n - i) x
            + cmode (c • f) (W.smul u (ℓ + i) v) (m + n - i) x)
          = c • (cbz m i •
              (W.smul (cmode f u (ℓ + i) v) (m + n - i) x
                + cmode f (W.smul u (ℓ + i) v) (m + n - i) x)) := by
        intro i
        simp only [cmode_smul_cochain, PreVertexAlgebra.smul_smul_left, smul_add, smul_comm c]
      rw [finsum_congr hL, finsum_congr hR,
        ← smul_finsum' c (jacLHS_support_finite W hft u v x ℓ m n),
        ← smul_finsum' c (jacRHS_support_finite W hft u v x ℓ m n), hfj u v x ℓ m n]

@[simp] theorem mem_cocycles {W : VertexOperatorAlgebra 𝒱} {f : Cochain 𝒱} :
    f ∈ cocycles W ↔ Truncated f ∧ f W.vacuum = 0 ∧ CreationAx W f ∧ JacobiAx W f := Iff.rfl

/-! ### Cocycles *are* first-order deformations -/

/-- The `Y₁` of a first-order deformation is a cocycle. -/
theorem Y1_mem_cocycles {W : VertexOperatorAlgebra 𝒱} (D : FirstOrderDeformation W) :
    D.Y1 ∈ cocycles W :=
  ⟨D.truncation, D.vacuum_Y1, D.creation, D.borcherds₁⟩

/-- Every cocycle is the `Y₁` of a first-order deformation. -/
def ofCocycle {W : VertexOperatorAlgebra 𝒱} (f : Cochain 𝒱) (hf : f ∈ cocycles W) :
    FirstOrderDeformation W where
  Y1 := f
  truncation := hf.1
  vacuum_Y1 := hf.2.1
  creation := hf.2.2.1
  jacobi := hf.2.2.2

@[simp] theorem ofCocycle_Y1 {W : VertexOperatorAlgebra 𝒱} (f : Cochain 𝒱) (hf : f ∈ cocycles W) :
    (ofCocycle f hf).Y1 = f := rfl

/-- The cocycle submodule **is** the space of first-order deformations: the structure carries no
information beyond its `Y₁`.  This is what licenses replacing `FirstOrderDeformation W` by linear
algebra in `Cochain 𝒱`. -/
def cocycleEquivDeformation (W : VertexOperatorAlgebra 𝒱) :
    ↥(cocycles W) ≃ FirstOrderDeformation W where
  toFun f := ofCocycle f.1 f.2
  invFun D := ⟨D.Y1, Y1_mem_cocycles D⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## Coboundaries are cocycles

`Deform.coboundaries W` is already a `Submodule` (`Core.Deformation`), and `IsCoboundary W f`
already *is* the field-redefinition side: `f = δφ` for a grade-preserving `φ` killing the vacuum.
What is *not* in `Core.Deformation` is the check that makes the picture a complex: that `δφ`
satisfies the first-order Jacobi identity.  That is proved here.

The proof is the conceptual one.  Write `𝒟` for the operation "insert `φ` into each of the three
arguments in turn, then subtract `φ` of the whole thing".  Each side of the *undeformed* Borcherds
identity is a finite sum whose summand is trilinear in `(u,v,x)`, and a direct expansion shows
that substituting `δφ` for `Y₁` in the *first-order* identity turns each summand into `𝒟` of the
undeformed summand (`jacL_delta`, `jacR_delta`).  Applying `VertexOperatorAlgebra.jacobi` at
`(φu,v,x)`, `(u,φv,x)`, `(u,v,φx)` and `(u,v,x)` then closes it.  This is the mode form of the
familiar statement that `Yᵗ(u,z)v := (1+tφ)Y((1-tφ)u, z)(1-tφ)v` is again a vertex algebra. -/

/-- Left-slot linearity of `smul` over subtraction (the `+` case is
`PreVertexAlgebra.smul_add_left`). -/
theorem smul_sub_left (W : VertexOperatorAlgebra 𝒱) (u₁ u₂ : 𝒱) (n : ℤ) (v : 𝒱) :
    W.smul (u₁ - u₂) n v = W.smul u₁ n v - W.smul u₂ n v := by
  simp only [PreVertexAlgebra.smul_def, map_sub, mode_sub, LinearMap.sub_apply]

/-- Right-slot linearity of `smul` over subtraction. -/
theorem smul_sub_right (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (n : ℤ) (v₁ v₂ : 𝒱) :
    W.smul u n (v₁ - v₂) = W.smul u n v₁ - W.smul u n v₂ :=
  map_sub (mode (W.Y u) n) v₁ v₂

/-- The support of a pointwise sum of two finitely-supported families is finite. -/
theorem support_add_finite {ι : Type*} {M : Type*} [AddCommGroup M] {A B : ι → M}
    (hA : (Function.support A).Finite) (hB : (Function.support B).Finite) :
    (Function.support fun i => A i + B i).Finite := by
  refine Set.Finite.subset (hA.union hB) fun i hi => ?_
  rw [Function.mem_support] at hi
  rcases eq_or_ne (A i) 0 with hAi | hAi
  · refine Or.inr ?_
    rw [Function.mem_support]
    intro hBi
    exact hi (by rw [hAi, hBi, add_zero])
  · exact Or.inl hAi

/-- The support of a pointwise difference of two finitely-supported families is finite. -/
theorem support_sub_finite {ι : Type*} {M : Type*} [AddCommGroup M] {A B : ι → M}
    (hA : (Function.support A).Finite) (hB : (Function.support B).Finite) :
    (Function.support fun i => A i - B i).Finite := by
  refine Set.Finite.subset (hA.union hB) fun i hi => ?_
  rw [Function.mem_support] at hi
  rcases eq_or_ne (A i) 0 with hAi | hAi
  · refine Or.inr ?_
    rw [Function.mem_support]
    intro hBi
    exact hi (by rw [hAi, hBi, sub_zero])
  · exact Or.inl hAi

/-- Post-composing a finitely-supported family with a linear map keeps the support finite. -/
theorem support_map_finite {ι : Type*} {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (φ : M →ₗ[ℂ] N) {A : ι → M}
    (hA : (Function.support A).Finite) : (Function.support fun i => φ (A i)).Finite := by
  refine Set.Finite.subset hA fun i hi => ?_
  rw [Function.mem_support] at hi ⊢
  intro h
  exact hi (by rw [h, map_zero])

/-- The `i`-th summand of the **left**-hand side of the undeformed Borcherds identity. -/
noncomputable def jacL (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n i : ℤ) : 𝒱 :=
  (negOnePow i * cbz ℓ i) •
    (W.smul u (ℓ + m - i) (W.smul v (n + i) x)
      - negOnePow ℓ • W.smul v (ℓ + n - i) (W.smul u (m + i) x))

/-- The `i`-th summand of the **right**-hand side of the undeformed Borcherds identity. -/
noncomputable def jacR (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n i : ℤ) : 𝒱 :=
  cbz m i • W.smul (W.smul u (ℓ + i) v) (m + n - i) x

/-- `VertexOperatorAlgebra.jacobi` in the `jacL`/`jacR` notation. -/
theorem jacobi_jacL_jacR (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (∑ᶠ i : ℤ, jacL W u v x ℓ m n i) = ∑ᶠ i : ℤ, jacR W u v x ℓ m n i :=
  W.jacobi u v x ℓ m n

theorem jacL_support_finite (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ => jacL W u v x ℓ m n i).Finite := by
  obtain ⟨Nv, hNv⟩ := W.toPreVertexAlgebra.smul_eventually_zero v x
  obtain ⟨Nu, hNu⟩ := W.toPreVertexAlgebra.smul_eventually_zero u x
  refine Set.Finite.subset (Set.finite_Icc 0 (max (Nv - n) (Nu - m))) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [jacL, cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · rw [max_lt_iff] at h
    obtain ⟨h1, h2⟩ := h
    rw [jacL, hNv (n + i) (by omega), hNu (m + i) (by omega)]
    simp

theorem jacR_support_finite (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ => jacR W u v x ℓ m n i).Finite := by
  obtain ⟨N, hN⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
  refine Set.Finite.subset (Set.finite_Icc 0 (N - ℓ)) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [jacR, cbz_apply_neg m h, zero_smul]
  · rw [jacR, hN (ℓ + i) (by omega)]
    simp

/-- The Leibniz identity for the **left**-hand summand: substituting the coboundary `δφ` for
`Y₁` in the first-order Jacobi left-hand summand produces `𝒟` of the undeformed summand. -/
theorem jacL_delta (W : VertexOperatorAlgebra 𝒱) (φ : 𝒱 →ₗ[ℂ] 𝒱) (u v x : 𝒱) (ℓ m n i : ℤ) :
    (negOnePow i * cbz ℓ i) •
        ((W.smul (φ u) (ℓ + m - i) (W.smul v (n + i) x)
            - φ (W.smul u (ℓ + m - i) (W.smul v (n + i) x))
            + W.smul u (ℓ + m - i) (φ (W.smul v (n + i) x)))
          + W.smul u (ℓ + m - i)
              (W.smul (φ v) (n + i) x - φ (W.smul v (n + i) x) + W.smul v (n + i) (φ x))
          - negOnePow ℓ •
            ((W.smul (φ v) (ℓ + n - i) (W.smul u (m + i) x)
                - φ (W.smul v (ℓ + n - i) (W.smul u (m + i) x))
                + W.smul v (ℓ + n - i) (φ (W.smul u (m + i) x)))
              + W.smul v (ℓ + n - i)
                  (W.smul (φ u) (m + i) x - φ (W.smul u (m + i) x) + W.smul u (m + i) (φ x))))
      = jacL W (φ u) v x ℓ m n i + jacL W u (φ v) x ℓ m n i + jacL W u v (φ x) ℓ m n i
          - φ (jacL W u v x ℓ m n i) := by
  simp only [jacL, map_smul, map_sub, smul_sub, smul_add, PreVertexAlgebra.smul_add_right,
    smul_sub_right, smul_comm (negOnePow i * cbz ℓ i) (negOnePow ℓ)]
  abel

/-- The Leibniz identity for the **right**-hand summand. -/
theorem jacR_delta (W : VertexOperatorAlgebra 𝒱) (φ : 𝒱 →ₗ[ℂ] 𝒱) (u v x : 𝒱) (ℓ m n i : ℤ) :
    cbz m i •
        (W.smul (W.smul (φ u) (ℓ + i) v - φ (W.smul u (ℓ + i) v) + W.smul u (ℓ + i) (φ v))
            (m + n - i) x
          + (W.smul (φ (W.smul u (ℓ + i) v)) (m + n - i) x
              - φ (W.smul (W.smul u (ℓ + i) v) (m + n - i) x)
              + W.smul (W.smul u (ℓ + i) v) (m + n - i) (φ x)))
      = jacR W (φ u) v x ℓ m n i + jacR W u (φ v) x ℓ m n i + jacR W u v (φ x) ℓ m n i
          - φ (jacR W u v x ℓ m n i) := by
  simp only [jacR, map_smul, PreVertexAlgebra.smul_add_left, smul_sub_left, smul_add, smul_sub]
  abel

/-- **A coboundary satisfies the first-order Jacobi identity.** -/
theorem jacobiAx_of_isCoboundary {W : VertexOperatorAlgebra 𝒱} {f : Cochain 𝒱}
    (hf : IsCoboundary W f) : JacobiAx W f := by
  obtain ⟨φ, -, -, hφ⟩ := hf
  intro u v x ℓ m n
  have hL : ∀ i : ℤ, (negOnePow i * cbz ℓ i) •
      (cmode f u (ℓ + m - i) (W.smul v (n + i) x)
        + W.smul u (ℓ + m - i) (cmode f v (n + i) x)
        - negOnePow ℓ •
          (cmode f v (ℓ + n - i) (W.smul u (m + i) x)
            + W.smul v (ℓ + n - i) (cmode f u (m + i) x)))
      = jacL W (φ u) v x ℓ m n i + jacL W u (φ v) x ℓ m n i + jacL W u v (φ x) ℓ m n i
          - φ (jacL W u v x ℓ m n i) := by
    intro i
    rw [cmode_def, cmode_def, cmode_def, cmode_def, hφ, hφ, hφ, hφ]
    exact jacL_delta W φ u v x ℓ m n i
  have hR : ∀ i : ℤ, cbz m i •
      (W.smul (cmode f u (ℓ + i) v) (m + n - i) x
        + cmode f (W.smul u (ℓ + i) v) (m + n - i) x)
      = jacR W (φ u) v x ℓ m n i + jacR W u (φ v) x ℓ m n i + jacR W u v (φ x) ℓ m n i
          - φ (jacR W u v x ℓ m n i) := by
    intro i
    rw [cmode_def, cmode_def, hφ, hφ]
    exact jacR_delta W φ u v x ℓ m n i
  have hLfin₁ := jacL_support_finite W (φ u) v x ℓ m n
  have hLfin₂ := jacL_support_finite W u (φ v) x ℓ m n
  have hLfin₃ := jacL_support_finite W u v (φ x) ℓ m n
  have hLfin₄ := jacL_support_finite W u v x ℓ m n
  have hRfin₁ := jacR_support_finite W (φ u) v x ℓ m n
  have hRfin₂ := jacR_support_finite W u (φ v) x ℓ m n
  have hRfin₃ := jacR_support_finite W u v (φ x) ℓ m n
  have hRfin₄ := jacR_support_finite W u v x ℓ m n
  rw [finsum_congr hL, finsum_congr hR,
    finsum_sub_distrib (support_add_finite (support_add_finite hLfin₁ hLfin₂) hLfin₃)
      (support_map_finite φ hLfin₄),
    finsum_add_distrib (support_add_finite hLfin₁ hLfin₂) hLfin₃,
    finsum_add_distrib hLfin₁ hLfin₂,
    finsum_sub_distrib (support_add_finite (support_add_finite hRfin₁ hRfin₂) hRfin₃)
      (support_map_finite φ hRfin₄),
    finsum_add_distrib (support_add_finite hRfin₁ hRfin₂) hRfin₃,
    finsum_add_distrib hRfin₁ hRfin₂,
    ← map_finsum φ hLfin₄, ← map_finsum φ hRfin₄,
    jacobi_jacL_jacR W (φ u) v x ℓ m n, jacobi_jacL_jacR W u (φ v) x ℓ m n,
    jacobi_jacL_jacR W u v (φ x) ℓ m n, jacobi_jacL_jacR W u v x ℓ m n]

/-- **The complex is a complex:** every coboundary is a cocycle.  Together with
`cocycleEquivDeformation` this says that a field redefinition really does produce a first-order
deformation, and hence that the quotient `cocycles ⧸ coboundaries` is defined. -/
theorem coboundaries_le_cocycles (W : VertexOperatorAlgebra 𝒱) :
    coboundaries W ≤ cocycles W := by
  intro f hf
  have hcob : IsCoboundary W f := hf
  obtain ⟨φ, hφ0, -, hφ⟩ := hcob
  refine ⟨?_, ?_, ?_, jacobiAx_of_isCoboundary hf⟩
  · intro u v
    obtain ⟨N₁, hN₁⟩ := W.toPreVertexAlgebra.smul_eventually_zero (φ u) v
    obtain ⟨N₂, hN₂⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
    obtain ⟨N₃, hN₃⟩ := W.toPreVertexAlgebra.smul_eventually_zero u (φ v)
    refine ⟨max (max N₁ N₂) N₃, fun k hk => ?_⟩
    rw [cmode_def, hφ, hN₁ k (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk),
      hN₂ k (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk),
      hN₃ k (le_trans (le_max_right _ _) hk), map_zero, sub_zero, add_zero]
  · refine FormalDist.ext fun k => LinearMap.ext fun w => ?_
    have h := hφ W.vacuum (-k - 1) w
    rw [mode_apply, show -(-k - 1) - 1 = k from by ring, hφ0,
      PreVertexAlgebra.smul_zero_left, PreVertexAlgebra.smul_vacuum_left,
      PreVertexAlgebra.smul_vacuum_left] at h
    rw [h]
    split_ifs with hk
    · simp
    · simp
  · intro w k hk
    rw [cmode_def, hφ, hφ0, PreVertexAlgebra.smul_zero_right, add_zero]
    rcases eq_or_lt_of_le hk with h | h
    · rw [← h, PreVertexAlgebra.smul_vacuum_neg_one, PreVertexAlgebra.smul_vacuum_neg_one, sub_self]
    · rw [W.toPreVertexAlgebra.smul_vacuum_nonneg (φ w) (by omega),
        W.toPreVertexAlgebra.smul_vacuum_nonneg w (by omega), map_zero, sub_self]

/-! ## Rigidity *is* the vanishing of the quotient -/

/-- Rigidity, restated as an inclusion of submodules.  Both directions are immediate from
`cocycleEquivDeformation`: the structure `FirstOrderDeformation W` carries no data beyond a
cocycle. -/
theorem isRigid_iff_cocycles_le_coboundaries (W : VertexOperatorAlgebra 𝒱) :
    IsRigid W ↔ cocycles W ≤ coboundaries W := by
  constructor
  · intro h f hf
    exact h (ofCocycle f hf)
  · intro h D
    exact h (Y1_mem_cocycles D)

/-- The coboundaries, viewed as a submodule *of the cocycles* (legitimate by
`coboundaries_le_cocycles`). -/
def coboundariesIn (W : VertexOperatorAlgebra 𝒱) : Submodule ℂ ↥(cocycles W) :=
  (coboundaries W).comap (cocycles W).subtype

@[simp] theorem mem_coboundariesIn {W : VertexOperatorAlgebra 𝒱} {f : ↥(cocycles W)} :
    f ∈ coboundariesIn W ↔ (f : Cochain 𝒱) ∈ coboundaries W := Iff.rfl

/-- The **first-order deformation space** of `W`: cocycles modulo coboundaries.  This is the
object the paper calls `H²` of the deformation complex; here it is an honest quotient module and
nothing more. -/
abbrev H (W : VertexOperatorAlgebra 𝒱) : Type u := ↥(cocycles W) ⧸ coboundariesIn W

/-- `W` is rigid to first order exactly when its deformation space vanishes. -/
theorem isRigid_iff_H_trivial (W : VertexOperatorAlgebra 𝒱) :
    IsRigid W ↔ ∀ z : H W, z = 0 := by
  rw [isRigid_iff_cocycles_le_coboundaries]
  constructor
  · intro h z
    refine Quotient.inductionOn' z fun f => ?_
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h f.2)
  · intro h f hf
    have hz := h (Submodule.Quotient.mk (⟨f, hf⟩ : ↥(cocycles W)))
    rw [Submodule.Quotient.mk_eq_zero] at hz
    exact hz

/-! ## Extending from homogeneous vectors

The bridge between the componentwise (finite) data and the global statements.  It is the only
place `isInternal` is used, and it is used in the only way it can be: a bi-additive identity that
holds on homogeneous pairs holds everywhere. -/

/-- Two bi-additive maps `𝒱 × 𝒱 → 𝒱` that agree on **homogeneous** pairs agree everywhere.
This is `DirectSum.IsInternal` doing its one job. -/
theorem eq_of_homogeneous (W : VertexOperatorAlgebra 𝒱) {F G : 𝒱 → 𝒱 → 𝒱}
    (hF0l : ∀ v, F 0 v = 0) (hFl : ∀ u₁ u₂ v, F (u₁ + u₂) v = F u₁ v + F u₂ v)
    (hF0r : ∀ u, F u 0 = 0) (hFr : ∀ u v₁ v₂, F u (v₁ + v₂) = F u v₁ + F u v₂)
    (hG0l : ∀ v, G 0 v = 0) (hGl : ∀ u₁ u₂ v, G (u₁ + u₂) v = G u₁ v + G u₂ v)
    (hG0r : ∀ u, G u 0 = 0) (hGr : ∀ u v₁ v₂, G u (v₁ + v₂) = G u v₁ + G u v₂)
    (h : ∀ (a b : ℤ) (u : 𝒱), u ∈ W.grading a → ∀ (v : 𝒱), v ∈ W.grading b → F u v = G u v)
    (u v : 𝒱) : F u v = G u v := by
  have hu : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun y => ∀ w : 𝒱, F y w = G y w) hu
    ?_ ?_ ?_ v
  · intro a y hy w
    have hw : w ∈ ⨆ i, W.grading i := by
      rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction W.grading (motive := fun z => F y z = G y z) hw ?_ ?_ ?_
    · intro b z hz
      exact h a b y hy z hz
    · change F y 0 = G y 0
      rw [hF0r, hG0r]
    · intro z₁ z₂ h₁ h₂
      change F y (z₁ + z₂) = G y (z₁ + z₂)
      rw [hFr, hGr, h₁, h₂]
  · intro w
    rw [hF0l, hG0l]
  · intro y₁ y₂ h₁ h₂ w
    rw [hFl, hGl, h₁ w, h₂ w]

/-- Two cochains whose modes agree on all homogeneous pairs are equal. -/
theorem cochain_eq_of_homogeneous (W : VertexOperatorAlgebra 𝒱) {f g : Cochain 𝒱}
    (h : ∀ (a b : ℤ) (u : 𝒱), u ∈ W.grading a → ∀ (v : 𝒱), v ∈ W.grading b → ∀ n : ℤ,
      cmode f u n v = cmode g u n v) : f = g := by
  refine cochain_ext fun u n v => ?_
  exact eq_of_homogeneous W (F := fun y w => cmode f y n w) (G := fun y w => cmode g y n w)
    (fun w => cmode_zero_left f n w) (fun y₁ y₂ w => cmode_add_left f y₁ y₂ n w)
    (fun y => cmode_zero_right f y n) (fun y w₁ w₂ => cmode_add_right f y n w₁ w₂)
    (fun w => cmode_zero_left g n w) (fun y₁ y₂ w => cmode_add_left g y₁ y₂ n w)
    (fun y => cmode_zero_right g y n) (fun y w₁ w₂ => cmode_add_right g y n w₁ w₂)
    (fun a b y hy w hw => h a b y hy w hw n) u v

/-- **Components determine triviality.**  If a deformation and a *single* grade-preserving `φ`
(killing the vacuum) agree on every homogeneous pair — which is exactly the componentwise, finite
data of `gradedComponent` below — then the deformation is trivial.

This is the honest half of the reduction from the graded picture to `IsRigid`: what it needs, and
what per-tridegree cokernel vanishing does *not* by itself supply, is the single global `φ`. -/
theorem isTrivial_of_components {W : VertexOperatorAlgebra 𝒱} (D : FirstOrderDeformation W)
    (φ : 𝒱 →ₗ[ℂ] 𝒱) (hφ0 : φ W.vacuum = 0) (hφg : GradePreserving W φ)
    (h : ∀ (a b : ℤ) (u : 𝒱), u ∈ W.grading a → ∀ (v : 𝒱), v ∈ W.grading b → ∀ n : ℤ,
      D.smul₁ u n v = W.smul (φ u) n v - φ (W.smul u n v) + W.smul u n (φ v)) :
    D.IsTrivial := by
  refine ⟨φ, hφ0, hφg, fun u n v => ?_⟩
  refine eq_of_homogeneous W (F := fun y w => D.smul₁ y n w)
    (G := fun y w => W.smul (φ y) n w - φ (W.smul y n w) + W.smul y n (φ w))
    (fun w => D.smul₁_zero_left n w) (fun y₁ y₂ w => D.smul₁_add_left y₁ y₂ n w)
    (fun y => D.smul₁_zero_right y n) (fun y w₁ w₂ => D.smul₁_add_right y n w₁ w₂)
    (fun w => by simp) (fun y₁ y₂ w => by simp; abel)
    (fun y => by simp) (fun y w₁ w₂ => by simp; abel)
    (fun a b y hy w hw => h a b y hy w hw n) u v

/-! ## The graded truncation: finite-dimensional cochains at a tridegree -/

/-- The mode determined by a tridegree `(a,b,c)`: if `u ∈ 𝒱ₐ`, `v ∈ 𝒱_b` and the product
`u¹₍ₙ₎v` is to land in `𝒱_c`, then necessarily `n = a + b - c - 1`.  The mode is therefore *not*
an independent index; see the file docstring. -/
def gradedMode (a b c : ℤ) : ℤ := a + b - c - 1

@[simp] theorem grading_of_gradedMode (a b c : ℤ) : a + b - gradedMode a b c - 1 = c := by
  simp only [gradedMode]; ring

@[simp] theorem gradedMode_of_target (a b n : ℤ) : gradedMode a b (a + b - n - 1) = n := by
  simp only [gradedMode]; ring

/-- The **cochain space at tridegree `(a,b,c)`**: the bilinear maps `𝒱ₐ × 𝒱_b → 𝒱_c`.  Because
the mode is determined by the tridegree, this records *exactly* the component of `Y₁` between
those graded pieces.  It is finite-dimensional. -/
abbrev GradedCochain (W : VertexOperatorAlgebra 𝒱) (a b c : ℤ) : Type u :=
  ↥(W.grading a) →ₗ[ℂ] ↥(W.grading b) →ₗ[ℂ] ↥(W.grading c)

/-- **The finite linear algebra.**  Every graded piece of a VOA in this repository is
finite-dimensional (`PreVertexAlgebra.finrank`, a structure field), hence so is the cochain space at
each tridegree.  No hypothesis is needed. -/
instance instFiniteDimensionalGradedCochain (W : VertexOperatorAlgebra 𝒱) (a b c : ℤ) :
    FiniteDimensional ℂ (GradedCochain W a b c) := by
  haveI := W.toPreVertexAlgebra.finrank a
  haveI := W.toPreVertexAlgebra.finrank b
  haveI := W.toPreVertexAlgebra.finrank c
  infer_instance

/-- The **graded cochains**: order-`t` VA1, `u¹₍ₙ₎ : 𝒱ₐ ⊗ 𝒱_b → 𝒱_{a+b-n-1}`.  A linear
condition, hence a submodule; it is `FirstOrderDeformation.IsGraded` transported to cochains
(`isGraded_iff_Y1_mem_gradedCochains`). -/
def gradedCochains (W : VertexOperatorAlgebra 𝒱) : Submodule ℂ (Cochain 𝒱) where
  carrier := {f | ∀ (a b : ℤ) (u : 𝒱), u ∈ W.grading a → ∀ (v : 𝒱), v ∈ W.grading b →
      ∀ n : ℤ, cmode f u n v ∈ W.grading (a + b - n - 1)}
  add_mem' := by
    intro f g hf hg a b u hu v hv n
    rw [cmode_add_cochain]
    exact Submodule.add_mem _ (hf a b u hu v hv n) (hg a b u hu v hv n)
  zero_mem' := by
    intro a b u _ v _ n
    rw [cmode_zero_cochain]
    exact Submodule.zero_mem _
  smul_mem' := by
    intro c f hf a b u hu v hv n
    rw [cmode_smul_cochain]
    exact Submodule.smul_mem _ c (hf a b u hu v hv n)

@[simp] theorem mem_gradedCochains {W : VertexOperatorAlgebra 𝒱} {f : Cochain 𝒱} :
    f ∈ gradedCochains W ↔ ∀ (a b : ℤ) (u : 𝒱), u ∈ W.grading a → ∀ (v : 𝒱), v ∈ W.grading b →
      ∀ n : ℤ, cmode f u n v ∈ W.grading (a + b - n - 1) := Iff.rfl

/-- `FirstOrderDeformation.IsGraded` is membership of `Y₁` in `gradedCochains`. -/
theorem isGraded_iff_Y1_mem_gradedCochains {W : VertexOperatorAlgebra 𝒱}
    (D : FirstOrderDeformation W) : D.IsGraded ↔ D.Y1 ∈ gradedCochains W := Iff.rfl

/-- ⚠ **Bounded above for free.**  Since `𝒱_k = 0` for `k < 0` (VOA4), a graded cochain has no
component at all between `𝒱ₐ` and `𝒱_b` in modes `n > a + b - 1`. -/
theorem gradedCochain_vanishing_of_gt (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) {a b : ℤ} {u v : 𝒱} (hu : u ∈ W.grading a) (hv : v ∈ W.grading b)
    {n : ℤ} (hn : a + b - 1 < n) : cmode f u n v = 0 := by
  have h := hf a b u hu v hv n
  rw [W.positivity (a + b - n - 1) (by omega)] at h
  exact (Submodule.mem_bot ℂ).mp h

/-- A graded cochain automatically satisfies the truncation axiom: the mode bound is a
consequence of the grading, not an extra hypothesis. -/
theorem truncated_of_graded (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) : Truncated f := by
  intro u v
  have hu : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun y => ∀ w : 𝒱, ∃ N : ℤ, ∀ n : ℤ, N ≤ n → cmode f y n w = 0) hu ?_ ?_ ?_ v
  · intro a y hy w
    have hw : w ∈ ⨆ i, W.grading i := by
      rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction W.grading
      (motive := fun z => ∃ N : ℤ, ∀ n : ℤ, N ≤ n → cmode f y n z = 0) hw ?_ ?_ ?_
    · intro b z hz
      exact ⟨a + b, fun n hn => gradedCochain_vanishing_of_gt W hf hy hz (by omega)⟩
    · exact ⟨0, fun n _ => by simp⟩
    · rintro z₁ z₂ ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
      refine ⟨max N₁ N₂, fun n hn => ?_⟩
      simp only [cmode_add_right, h₁ n (le_trans (le_max_left _ _) hn),
        h₂ n (le_trans (le_max_right _ _) hn), add_zero]
  · intro w
    exact ⟨0, fun n _ => by simp⟩
  · rintro y₁ y₂ h₁ h₂ w
    obtain ⟨N₁, hN₁⟩ := h₁ w
    obtain ⟨N₂, hN₂⟩ := h₂ w
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    simp only [cmode_add_left, hN₁ n (le_trans (le_max_left _ _) hn),
      hN₂ n (le_trans (le_max_right _ _) hn), add_zero]

/-- Coboundaries are graded cochains: a grade-preserving `φ` produces a grade-preserving `δφ`.
Without this the graded coboundary space would be empty of content. -/
theorem coboundaries_le_gradedCochains (W : VertexOperatorAlgebra 𝒱) :
    coboundaries W ≤ gradedCochains W := by
  intro f hf
  obtain ⟨φ, -, hφg, hφ⟩ := hf
  intro a b u hu v hv n
  rw [cmode_def, hφ]
  refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
  · exact W.toPreVertexAlgebra.smul_mem_grading (hφg a u hu) hv n
  · exact hφg _ _ (W.toPreVertexAlgebra.smul_mem_grading hu hv n)
  · exact W.toPreVertexAlgebra.smul_mem_grading hu (hφg b v hv) n

/-! ### The component map -/

/-- The `(a,b,c)`-component of a graded cochain really lands in `𝒱_c`. -/
theorem gradedComponent_mem (W : VertexOperatorAlgebra 𝒱) {f : Cochain 𝒱}
    (hf : f ∈ gradedCochains W) (a b c : ℤ) (u : ↥(W.grading a)) (v : ↥(W.grading b)) :
    cmode f (u : 𝒱) (gradedMode a b c) (v : 𝒱) ∈ W.grading c := by
  have h := hf a b (u : 𝒱) u.2 (v : 𝒱) v.2 (gradedMode a b c)
  rwa [grading_of_gradedMode] at h

/-- The **component map** at tridegree `(a,b,c)`: a `ℂ`-linear map from the graded cochains to
the finite-dimensional space `GradedCochain W a b c`.  This is the passage from the infinite
object `Y₁` to finite linear algebra. -/
def gradedComponent (W : VertexOperatorAlgebra 𝒱) (a b c : ℤ) :
    ↥(gradedCochains W) →ₗ[ℂ] GradedCochain W a b c where
  toFun f :=
    { toFun := fun u =>
        { toFun := fun v =>
            ⟨cmode (f : Cochain 𝒱) (u : 𝒱) (gradedMode a b c) (v : 𝒱),
              gradedComponent_mem W f.2 a b c u v⟩
          map_add' := fun v₁ v₂ => by ext; simp
          map_smul' := fun r v => by ext; simp }
      map_add' := fun u₁ u₂ => by ext v; simp
      map_smul' := fun r u => by ext v; simp }
  map_add' := fun f g => by ext u v; simp
  map_smul' := fun r f => by ext u v; simp

@[simp] theorem gradedComponent_apply (W : VertexOperatorAlgebra 𝒱) (a b c : ℤ)
    (f : ↥(gradedCochains W)) (u : ↥(W.grading a)) (v : ↥(W.grading b)) :
    (gradedComponent W a b c f u v : 𝒱)
      = cmode (f : Cochain 𝒱) (u : 𝒱) (gradedMode a b c) (v : 𝒱) := rfl

/-- **The finite componentwise data is faithful.**  A graded cochain is determined by its
components at all tridegrees.  (This is what makes the obstruction in `GradedToGlobalRigidity`
sharp rather than an artefact: the data is complete, the *quotient* statement is what does not
patch.) -/
theorem gradedCochains_ext (W : VertexOperatorAlgebra 𝒱) {f g : ↥(gradedCochains W)}
    (h : ∀ a b c : ℤ, gradedComponent W a b c f = gradedComponent W a b c g) : f = g := by
  refine Subtype.ext (cochain_eq_of_homogeneous W fun a b u hu v hv n => ?_)
  have hc := congrArg (fun t => ((t ⟨u, hu⟩ ⟨v, hv⟩ : ↥(W.grading (a + b - n - 1))) : 𝒱))
    (h a b (a + b - n - 1))
  simpa using hc

/-- The total component map: the family of all finite-dimensional components. -/
def totalComponent (W : VertexOperatorAlgebra 𝒱) :
    ↥(gradedCochains W) →ₗ[ℂ] ((a : ℤ) → (b : ℤ) → (c : ℤ) → GradedCochain W a b c) :=
  LinearMap.pi fun a => LinearMap.pi fun b => LinearMap.pi fun c => gradedComponent W a b c

/-- The total component map is injective. -/
theorem totalComponent_injective (W : VertexOperatorAlgebra 𝒱) :
    Function.Injective (totalComponent W) := by
  intro f g hfg
  refine gradedCochains_ext W fun a b c => ?_
  have h := congrFun (congrFun (congrFun hfg a) b) c
  exact h

/-! ### Cocycles, coboundaries and the deformation space at a tridegree -/

/-- The cocycles among the graded cochains. -/
def gradedCocycles (W : VertexOperatorAlgebra 𝒱) : Submodule ℂ ↥(gradedCochains W) :=
  (cocycles W).comap (gradedCochains W).subtype

/-- The coboundaries among the graded cochains. -/
def gradedCoboundaries (W : VertexOperatorAlgebra 𝒱) : Submodule ℂ ↥(gradedCochains W) :=
  (coboundaries W).comap (gradedCochains W).subtype

theorem gradedCoboundaries_le_gradedCocycles (W : VertexOperatorAlgebra 𝒱) :
    gradedCoboundaries W ≤ gradedCocycles W :=
  Submodule.comap_mono (coboundaries_le_cocycles W)

/-- The **cocycle space at tridegree `(a,b,c)`**: a submodule of a finite-dimensional space. -/
def gradedCocyclesAt (W : VertexOperatorAlgebra 𝒱) (a b c : ℤ) :
    Submodule ℂ (GradedCochain W a b c) :=
  (gradedCocycles W).map (gradedComponent W a b c)

/-- The **coboundary space at tridegree `(a,b,c)`**: the image of the field redefinitions. -/
def gradedCoboundariesAt (W : VertexOperatorAlgebra 𝒱) (a b c : ℤ) :
    Submodule ℂ (GradedCochain W a b c) :=
  (gradedCoboundaries W).map (gradedComponent W a b c)

/-- **Coboundaries are cocycles, at every tridegree.**  The graded complex is a complex. -/
theorem gradedCoboundariesAt_le_gradedCocyclesAt (W : VertexOperatorAlgebra 𝒱) (a b c : ℤ) :
    gradedCoboundariesAt W a b c ≤ gradedCocyclesAt W a b c :=
  Submodule.map_mono (gradedCoboundaries_le_gradedCocycles W)

/-- The coboundaries at a tridegree, viewed inside the cocycles there. -/
def gradedCoboundariesIn (W : VertexOperatorAlgebra 𝒱) (a b c : ℤ) :
    Submodule ℂ ↥(gradedCocyclesAt W a b c) :=
  (gradedCoboundariesAt W a b c).comap (gradedCocyclesAt W a b c).subtype

/-- The **deformation space at tridegree `(a,b,c)`**: `ker(first-order Jacobi) / im(field
redefinition)` in that single finite-dimensional component. -/
abbrev DeformationSpaceAt (W : VertexOperatorAlgebra 𝒱) (a b c : ℤ) : Type u :=
  ↥(gradedCocyclesAt W a b c) ⧸ gradedCoboundariesIn W a b c

/-- The deformation space at each tridegree is **finite-dimensional**: this is the sense in
which first-order deformation theory here is finite linear algebra. -/
instance instFiniteDimensionalDeformationSpaceAt (W : VertexOperatorAlgebra 𝒱) (a b c : ℤ) :
    FiniteDimensional ℂ (DeformationSpaceAt W a b c) := by
  haveI : FiniteDimensional ℂ ↥(gradedCocyclesAt W a b c) := inferInstance
  infer_instance

/-! ### Rigidity: what the graded picture does and does not give -/

/-- Rigidity restricted to *graded* deformations.  Note that `IsRigid` quantifies over all
first-order deformations, graded or not (`IsGraded` is a predicate, not a field of
`FirstOrderDeformation`), so this is genuinely weaker. -/
def IsRigidGraded (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ D : FirstOrderDeformation W, D.IsGraded → D.IsTrivial

theorem isRigidGraded_of_isRigid {W : VertexOperatorAlgebra 𝒱} (h : IsRigid W) :
    IsRigidGraded W := fun D _ => h D

/-- **The criterion that is provable.**  If every graded cocycle is a coboundary *as a cochain*
— i.e. the inclusion holds for the total family, with a single `φ` per cocycle — then every graded
deformation is trivial.  This is the correct target of the finite computation. -/
theorem isRigidGraded_of_gradedCocycles_le (W : VertexOperatorAlgebra 𝒱)
    (h : gradedCocycles W ≤ gradedCoboundaries W) : IsRigidGraded W := by
  intro D hD
  have hmem : (⟨D.Y1, hD⟩ : ↥(gradedCochains W)) ∈ gradedCocycles W := Y1_mem_cocycles D
  exact h hmem

/-- **Rigidity implies vanishing of every graded cokernel** — the easy direction of the
reduction, and the reason the finite computation is a genuine obstruction theory: a nonzero
`DeformationSpaceAt W a b c` *disproves* rigidity. -/
theorem gradedCocyclesAt_le_gradedCoboundariesAt_of_isRigid {W : VertexOperatorAlgebra 𝒱}
    (h : IsRigid W) (a b c : ℤ) :
    gradedCocyclesAt W a b c ≤ gradedCoboundariesAt W a b c := by
  rw [isRigid_iff_cocycles_le_coboundaries] at h
  exact Submodule.map_mono (Submodule.comap_mono h)

/-- ⚠ **NAMED TARGET — stated, deliberately NOT proved.**

`GradedToGlobalRigidity W` is the converse of
`gradedCocyclesAt_le_gradedCoboundariesAt_of_isRigid`: that vanishing of the finite-dimensional
cokernel at *every* tridegree forces `IsRigid W`.

Why it does not follow from anything in this file, stated precisely.  Write `Φ` for the space of
grade-preserving `φ` with `φ𝟙 = 0`; a grade-preserving `φ` is a family of blocks
`φ_k : 𝒱_k → 𝒱_k`, and the coboundary `δφ` at tridegree `(a,b,c)` is
`(u,v) ↦ (φ_a u)₍ₙ₎v − φ_c(u₍ₙ₎v) + u₍ₙ₎(φ_b v)` with `n = a+b-c-1`: it depends on `φ` **only
through the three blocks `φ_a, φ_b, φ_c`**.  The hypothesis
`∀ a b c, gradedCocyclesAt ≤ gradedCoboundariesAt` therefore says: for each tridegree separately
there exist blocks trivialising *that* component.  Concluding `IsRigid` requires *one* `φ` working
at **all** tridegrees at once (`isTrivial_of_components` is exactly the statement that one such
`φ` suffices), and per-tridegree surjectivity of a diagram of linear maps does not give
surjectivity of the induced map into the product.  There is no lim¹-type vanishing argument here,
and none is claimed.

Two further gaps, recorded rather than hidden:
* `IsRigid` quantifies over *ungraded* deformations too; the graded data can at best reach
  `IsRigidGraded` (see `isRigidGraded_of_gradedCocycles_le`).
* Even for graded deformations the correct provable criterion is the *total* inclusion
  `gradedCocycles W ≤ gradedCoboundaries W`, not the family of tridegree inclusions.

Anyone proving this should prove the strictly weaker and better-posed statement
`(∀ a b c, gradedCocyclesAt W a b c ≤ gradedCoboundariesAt W a b c) → gradedCocycles W ≤
gradedCoboundaries W` first; that is where the real content sits. -/
def GradedToGlobalRigidity (W : VertexOperatorAlgebra 𝒱) : Prop :=
  (∀ a b c : ℤ, gradedCocyclesAt W a b c ≤ gradedCoboundariesAt W a b c) → IsRigid W

end Deform

end VOA
