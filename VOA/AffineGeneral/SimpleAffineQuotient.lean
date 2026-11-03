/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.Simple
import VOA.AffineGeneral.SimpleQuotient

/-!
# The simple affine VOA `L_k(𝔤)` of a simple Lie algebra: a named wrapper

**Naming warning.**  `VOA.AffineGeneral.universalAffineVOA 𝔤 κ hinv hnd k hk` is the **universal**
affine VOA `V^k(𝔤)` (the full vacuum module `AffineLie.vacuumSpace κ hinv k`).
The deprecated alias `simpleAffineVOA` ("simple" referring to the Lie algebra `𝔤`, not to the
VOA) points to it.

The **simple quotient** `L_k(𝔤)` — the quotient of `V^k(𝔤)` by its maximal proper graded ideal — is
`simpleVOA (simpleData 𝔤 κ hinv hnd) k hk`.  This file gives it a name of its own,
`simpleAffineQuotientVOA`, and transports the existing facts to it:

* `simpleAffineQuotientVOA_isSimple` — `L_k(𝔤)` is simple (among all ideals);
* `simpleAffineQuotientVOA_centralCharge` — central charge `dim 𝔤 · k / (k + h)`, the same as
  `V^k(𝔤)`;
* `simpleAffineQuotientProjection` — the projection `V^k(𝔤) → L_k(𝔤)`, with
  `simpleAffineQuotientProjection_smul` (it intertwines all `n`-th products),
  `simpleAffineQuotientProjection_surjective`, and `simpleAffineQuotientProjection_grading`.

As in `Simple.lean`, `h = (simpleData 𝔤 κ hinv hnd).h` is the Casimir number of `κ` (half the
adjoint Casimir eigenvalue), not a separately identified dual Coxeter number.
-/

namespace VOA.AffineGeneral

noncomputable section

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤] [LieAlgebra.IsSimple ℂ 𝔤]

/-- **The simple affine VOA `L_k(𝔤)`**: the quotient of `V^k(𝔤) = universalAffineVOA 𝔤 κ hinv hnd k hk`
by its maximal proper graded ideal.  (Note that `universalAffineVOA` itself is the *universal* algebra;
see the module docstring.) -/
def simpleAffineQuotientVOA (κ : LinearMap.BilinForm ℂ 𝔤) (hinv : κ.IsInvariant)
    (hnd : LinearMap.BilinForm.Nondegenerate κ) (k : ℂ) (hk : k + (simpleData 𝔤 κ hinv hnd).h ≠ 0) :
    VertexOperatorAlgebra
      (Vacuum (simpleData 𝔤 κ hinv hnd) k ⧸ maxIdeal (simpleData 𝔤 κ hinv hnd) k hk) :=
  simpleVOA (simpleData 𝔤 κ hinv hnd) k hk

/-- `L_k(𝔤)` is simple (among all ideals). -/
theorem simpleAffineQuotientVOA_isSimple (κ : LinearMap.BilinForm ℂ 𝔤) (hinv : κ.IsInvariant)
    (hnd : LinearMap.BilinForm.Nondegenerate κ) (k : ℂ) (hk : k + (simpleData 𝔤 κ hinv hnd).h ≠ 0) :
    (simpleAffineQuotientVOA 𝔤 κ hinv hnd k hk).IsSimple :=
  simpleVOA_isSimple (simpleData 𝔤 κ hinv hnd) k hk

/-- The central charge of `L_k(𝔤)` is `dim 𝔤 · k / (k + h)`, that of `V^k(𝔤)`. -/
theorem simpleAffineQuotientVOA_centralCharge (κ : LinearMap.BilinForm ℂ 𝔤) (hinv : κ.IsInvariant)
    (hnd : LinearMap.BilinForm.Nondegenerate κ) (k : ℂ) (hk : k + (simpleData 𝔤 κ hinv hnd).h ≠ 0) :
    (simpleAffineQuotientVOA 𝔤 κ hinv hnd k hk).centralCharge =
      (Module.finrank ℂ 𝔤 : ℂ) * k / (k + (simpleData 𝔤 κ hinv hnd).h) :=
  universalAffineVOA_centralCharge 𝔤 κ hinv hnd k hk

/-- The projection `V^k(𝔤) → L_k(𝔤)`. -/
def simpleAffineQuotientProjection (κ : LinearMap.BilinForm ℂ 𝔤) (hinv : κ.IsInvariant)
    (hnd : LinearMap.BilinForm.Nondegenerate κ) (k : ℂ) (hk : k + (simpleData 𝔤 κ hinv hnd).h ≠ 0) :
    Vacuum (simpleData 𝔤 κ hinv hnd) k →ₗ[ℂ]
      Vacuum (simpleData 𝔤 κ hinv hnd) k ⧸ maxIdeal (simpleData 𝔤 κ hinv hnd) k hk :=
  simpleProjection (simpleData 𝔤 κ hinv hnd) k hk

/-- The projection `V^k(𝔤) → L_k(𝔤)` intertwines all `n`-th products: `[u₍ₙ₎v] = [u]₍ₙ₎[v]`. -/
theorem simpleAffineQuotientProjection_smul (κ : LinearMap.BilinForm ℂ 𝔤) (hinv : κ.IsInvariant)
    (hnd : LinearMap.BilinForm.Nondegenerate κ) (k : ℂ) (hk : k + (simpleData 𝔤 κ hinv hnd).h ≠ 0)
    (u : Vacuum (simpleData 𝔤 κ hinv hnd) k) (n : ℤ) (v : Vacuum (simpleData 𝔤 κ hinv hnd) k) :
    (simpleAffineQuotientVOA 𝔤 κ hinv hnd k hk).smul
        (simpleAffineQuotientProjection 𝔤 κ hinv hnd k hk u) n
        (simpleAffineQuotientProjection 𝔤 κ hinv hnd k hk v) =
      simpleAffineQuotientProjection 𝔤 κ hinv hnd k hk
        ((universalAffineVOA 𝔤 κ hinv hnd k hk).smul u n v) :=
  QuotVOA.quotientVOA_mkQ_smul (QuotVOA.maxGradedIdeal_isIdeal _)
    (QuotVOA.maxGradedIdeal_isGradedIdeal _) u n v

/-- The projection `V^k(𝔤) → L_k(𝔤)` is surjective. -/
theorem simpleAffineQuotientProjection_surjective (κ : LinearMap.BilinForm ℂ 𝔤)
    (hinv : κ.IsInvariant) (hnd : LinearMap.BilinForm.Nondegenerate κ) (k : ℂ)
    (hk : k + (simpleData 𝔤 κ hinv hnd).h ≠ 0) :
    Function.Surjective (simpleAffineQuotientProjection 𝔤 κ hinv hnd k hk) :=
  QuotVOA.quotientVOA_mkQ_surjective _

/-- The projection `V^k(𝔤) → L_k(𝔤)` preserves the conformal weight. -/
theorem simpleAffineQuotientProjection_grading (κ : LinearMap.BilinForm ℂ 𝔤)
    (hinv : κ.IsInvariant) (hnd : LinearMap.BilinForm.Nondegenerate κ) (k : ℂ)
    (hk : k + (simpleData 𝔤 κ hinv hnd).h ≠ 0) {n : ℤ} {x : Vacuum (simpleData 𝔤 κ hinv hnd) k}
    (hx : x ∈ (universalAffineVOA 𝔤 κ hinv hnd k hk).grading n) :
    simpleAffineQuotientProjection 𝔤 κ hinv hnd k hk x ∈
      (simpleAffineQuotientVOA 𝔤 κ hinv hnd k hk).grading n :=
  QuotVOA.quotientVOA_mkQ_grading (QuotVOA.maxGradedIdeal_isIdeal _)
    (QuotVOA.maxGradedIdeal_isGradedIdeal _) hx

end

end VOA.AffineGeneral
