import VOA.Modules.Character
import VOA.Modules.ZeroModeMult
import VOA.Core.BilinearForm
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Graded weak modules (generalized / logarithmic `L₀`) and their restricted duals

Input to the McRae rigidity argument (contragredients of finite-length generalized modules).

The library's contragredient (`Modules/Contragredient*.lean`, `ContragredientClose.contragredientModule`)
is built for `OrdVModule`, whose weight spaces are honest `L₀`-EIGENspaces.  A Huang projective
cover `P_S` of a `C₂`-cofinite VOA is in general logarithmic (`L₀` not semisimple), so its weight
spaces are GENERALIZED eigenspaces.  An audit of the contragredient development shows that the
`L₀`-eigenvalue law enters ONLY through the weight-shift law `mode_mem_weight`
(`u ∈ 𝒱_β, x ∈ M_α ⟹ u₍ₙ₎x ∈ M_{α+β−n−1}`) and the `L₀_weight` field of the output.  So we
abstract exactly that:

* `GWModule W M` — a weak module with a grading `M = ⨁_α M_α` by finite-dimensional subspaces,
  bounded below, obeying the weight-shift law.  No condition on how `L₀` acts on `M_α`; for the
  generalized-eigenspace grading of a finite-length module of a `C₂`-cofinite VOA, it is a theorem.
* `OrdVModule.toGW` — every ordinary module is one.
* `RestrictedDual N = ⨁_α (M_α)*` and its weight spaces, as in `Modules/Contragredient.lean`.

Everything lives in the namespace `VOA.C2Rigid`, so the ported contragredient development
(`Modules/C2RigidContra*.lean`) can reuse the original declaration names without clashing.
-/

namespace VOA.C2Rigid

open Module (End Dual)
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- A **graded weak module**: a weak module with a bounded-below grading by finite-dimensional
subspaces that obeys the weight-shift law of the modes.  This covers both ordinary modules
(eigenspace grading) and grading-restricted generalized (logarithmic) modules (generalized
eigenspace grading). -/
structure GWModule (W : VertexOperatorAlgebra 𝒱) (M : Type u)
    [AddCommGroup M] [Module ℂ M] extends WeakModule W M where
  /-- The grading `M = ⨁_α M_α`. -/
  weight : ℂ → Submodule ℂ M
  /-- The grading is an internal direct sum. -/
  isInternal : DirectSum.IsInternal weight
  /-- The weight-shift law: `u ∈ 𝒱_β`, `x ∈ M_α` ⟹ `u₍ₙ₎ x ∈ M_{α+β−n−1}`. -/
  mode_mem_weight' : ∀ {β : ℤ} {v : 𝒱}, v ∈ W.grading β → ∀ {α : ℂ} {x : M},
    x ∈ weight α → ∀ n : ℤ, mode (YM v) n x ∈ weight (α + (β : ℂ) - n - 1)
  /-- Each graded piece is finite-dimensional. -/
  finrank : ∀ α, FiniteDimensional ℂ (weight α)
  /-- Bounded below. -/
  boundedBelow : ∃ B : ℝ, ∀ α : ℂ, weight α ≠ ⊥ → B ≤ α.re

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The weight-shift law (the only place the contragredient construction uses `L₀`). -/
theorem mode_mem_weight (N : GWModule W M) {β : ℤ} {v : 𝒱} (hv : v ∈ W.grading β)
    {α : ℂ} {x : M} (hx : x ∈ N.weight α) (n : ℤ) :
    mode (N.YM v) n x ∈ N.weight (α + (β : ℂ) - n - 1) :=
  N.mode_mem_weight' hv hx n

/-- Every ordinary module is a graded weak module. -/
def _root_.VOA.OrdVModule.toGW (N : OrdVModule W M) : GWModule W M where
  toWeakModule := N.toWeakModule
  weight := N.weight
  isInternal := N.isInternal
  mode_mem_weight' hv _ _ hx n := VOA.mode_mem_weight N hv hx n
  finrank := N.finrank
  boundedBelow := N.boundedBelow

@[simp] theorem _root_.VOA.OrdVModule.toGW_weight (N : OrdVModule W M) :
    N.toGW.weight = N.weight := rfl

@[simp] theorem _root_.VOA.OrdVModule.toGW_toWeakModule (N : OrdVModule W M) :
    N.toGW.toWeakModule = N.toWeakModule := rfl

/-! ## The restricted dual `M* = ⊕_α (M_α)*` -/

/-- The **restricted dual** `⨁_α (M_α)*` of a graded weak module. -/
def RestrictedDual (N : GWModule W M) : Type u :=
  DirectSum ℂ (fun α => Module.Dual ℂ (N.weight α))

noncomputable instance (N : GWModule W M) : AddCommGroup (RestrictedDual N) :=
  inferInstanceAs (AddCommGroup (DirectSum ℂ (fun α => Module.Dual ℂ (N.weight α))))

noncomputable instance (N : GWModule W M) : Module ℂ (RestrictedDual N) :=
  inferInstanceAs (Module ℂ (DirectSum ℂ (fun α => Module.Dual ℂ (N.weight α))))

/-- The `α`-graded piece of the restricted dual: `(M*)_α = (M_α)*`. -/
noncomputable def RestrictedDual.weight (N : GWModule W M) (α : ℂ) :
    Submodule ℂ (RestrictedDual N) :=
  LinearMap.range (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α)

end VOA.C2Rigid
