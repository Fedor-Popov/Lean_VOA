/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneIntegral
import VOA.Huang.DeligneDeterminant
import VOA.Huang.DeligneApplications
import VOA.Huang.TannakianSymmetric

/-!
# Deligne's theorem — the top-level reduction

`DeligneTannakian` (`VOA/Huang/TannakianSymmetric.lean`) splits into the two classical halves:

* `SymmetricFiberFunctorExists` — **existence of a fiber functor** (Deligne, *Catégories
  tannakiennes* (1990) §7, *Catégories tensorielles* (2002); EGNO *Tensor categories* §9.9): a
  symmetric fusion category over `ℂ` whose simples have positive braided dimension admits a
  braided (= symmetric) monoidal, `ℂ`-linear, faithful functor to `FGModuleCat ℂ`.
* `FiberFunctorReconstruction` — **Tannaka reconstruction**, finite semisimple case
  (Saavedra Rivano; Deligne–Milne, *Tannakian categories* Thm 2.11; EGNO §5.2–5.4): a symmetric
  fusion category with such a fiber functor `ω` is braided-equivalent, by a `ℂ`-linear functor, to
  `FDRep ℂ G` for the finite group `G = Aut⊗(ω)`.

Proved here:

* `deligneTannakian_of_fiberFunctor` — `SymmetricFiberFunctorExists → FiberFunctorReconstruction
  → DeligneTannakian`;
* `symmetricFiberFunctorExists_of_deligneTannakian` — the converse half: `DeligneTannakian` implies
  `SymmetricFiberFunctorExists` (compose with the braided forgetful functor of `FDRep`).  So the
  existence statement is not stronger than the target.

Both Props are true at every universe level; neither is vacuous (`FDRep ℂ G` itself satisfies the
hypotheses: `symDim_fdRep`).  What is already proved toward `SymmetricFiberFunctorExists`
(stages D1–D5): `symDim` additive/multiplicative (`DeligneDim`), real positive on simples
(`symDim_simple_real_pos`), **natural numbers** on every object (`symDim_eq_nat`), exterior powers
with `dim Λ^k X = (d choose k)` and `Λ^k X = 0` for `k > dim X` (`DeligneIntegral`), the
determinant `Λ^{dim X} X` invertible (`DeligneDeterminant`); and, as an application, the
trivial-twist dimensions of a ribbon fusion category are positive integers without Deligne's
theorem (`trivialTwist_dim_nat`, `DeligneApplications`).

`import VOA.Huang.DeligneReduction` reaches all eight `Deligne*` files.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false

noncomputable section

namespace VOA.Huang.TensorCat

open CategoryTheory MonoidalCategory Limits Module

universe v u

/-- **Deligne's existence theorem** (fusion case): every symmetric fusion category over `ℂ` whose
simples have positive braided dimension admits a symmetric (braided), `ℂ`-linear, faithful monoidal
functor to finite-dimensional vector spaces. -/
def SymmetricFiberFunctorExists : Prop :=
  ∀ (D : Type u) [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
    [RightRigidCategory D] [SymmetricCategory D] [F : FusionCategory D],
    (∀ i, 0 < (symDim (F.simple i)).re) →
    ∃ ω : D ⥤ FGModuleCat ℂ, Nonempty ω.Braided ∧ ω.Linear ℂ ∧ ω.Faithful

/-- **Tannaka reconstruction** (finite semisimple, symmetric case): a symmetric fusion category
over `ℂ` with a braided, `ℂ`-linear, faithful monoidal functor to `FGModuleCat ℂ` is
braided-equivalent, by a `ℂ`-linear functor, to `FDRep ℂ G` for a finite group `G`. -/
def FiberFunctorReconstruction : Prop :=
  ∀ (D : Type u) [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
    [RightRigidCategory D] [SymmetricCategory D] [FusionCategory D]
    (ω : D ⥤ FGModuleCat ℂ), Nonempty ω.Braided → ω.Linear ℂ → ω.Faithful →
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (Φ : D ⥤ FDRep ℂ G),
      Nonempty Φ.Braided ∧ Φ.Linear ℂ ∧ Φ.IsEquivalence

/-- **Deligne = existence of a fiber functor + reconstruction.** -/
theorem deligneTannakian_of_fiberFunctor (hF : SymmetricFiberFunctorExists.{v, u})
    (hR : FiberFunctorReconstruction.{v, u}) : DeligneTannakian.{v, u} := by
  intro D _ _ _ _ _ _ _ _ _ _ _ hpos
  obtain ⟨ω, hω, hlin, hfaith⟩ := hF D hpos
  exact hR D ω hω hlin hfaith

/-- The existence statement is implied by `DeligneTannakian` (compose with the braided forgetful
functor `FDRep ℂ G ⥤ FGModuleCat ℂ`). -/
theorem symmetricFiberFunctorExists_of_deligneTannakian (h : DeligneTannakian.{v, u}) :
    SymmetricFiberFunctorExists.{v, u} := by
  intro D _ _ _ _ _ _ _ _ _ _ _ hpos
  obtain ⟨G, _, _, Φ, ⟨hΦ⟩, hlin, hequiv⟩ := h D hpos
  letI := hΦ
  refine ⟨Φ ⋙ Action.forget (FGModuleCat ℂ) G, ⟨inferInstance⟩, inferInstance, inferInstance⟩

end VOA.Huang.TensorCat
