/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUFull
import VOA.Modules.ZhuVermaAnArchDJ28Final

/-!
# DJ's GENUINE `M(U)` 𝒱-action on the full ideal — the bimodule-composition mode (NOT a levelShift).

Dong–Jiang's induced module `M(U) = ⊕ₙ A_{n,0}(𝒱) ⊗_{A(𝒱)} U` carries the 𝒱-action defined by the
CANONICAL BIMODULE COMPOSITION (`math/0601626`, §4): for `v ∈ 𝒱` the level-`(m → n)` component is

  `o_{n,m}(v) : M(U)(m) → M(U)(n)`,   `o_{n,m}(v)([g] ⊗ u) = [v *ⁿ_{0,m} g] ⊗ u`,

where `[v] ∈ A_{n,m}(𝒱)` acts on the module element `[g] ∈ A_{m,0}(𝒱)` by the composition
`ψ : A_{n,m} ⊗_{A_m} A_{m,0} → A_{n,0}` (Prop 3.4).  On an ambient admissible module `M`,
`o_{n,m}(u)w = u₍wt u+m−n−1₎ w` is the GENUINE VOA mode of `Y_M(u,z)` (Lemma 4.1:
`o_{n,m}(a *ⁿ_{m,p} b) = o_{n,p}(a) o_{p,m}(b)`), and Thm 4.13 proves `M(U)` is a valid admissible
𝒱-module.

## Why this is the RIGHT action (the levelShift degeneracy was a wrong-carrier artifact)

The repo's earlier loop-rep carriers (`levelShiftRho`, `fzRhoMU`) are degenerate/false, but they are
repo-invented ansätze, NOT DJ's action.  DJ's genuine composition mode `o_{n,m}(v)` is NON-DEGENERATE:
its Borcherds derivative relation is LEVEL-DEPENDENT,

  `o_{n,m}(L₋₁v) = −(wt v + m − n) · o_{n,m}(v)`

(from `(L₋₁v)₍k₎ = −k · v₍k−1₎`), so it is a level-INDEXED family — NOT the level-agnostic
constant-degree `hderiv` that `derivObstruction`/`levelShift_deg0_layer_vanish` require to force zero.
So the composition action ESCAPES the levelShift obstruction — exactly analogous to `CrossCircCore`
being a wrong-IDEAL artifact. 

## What is proved here

* `anmComposeFullRight` — the descended DJ composition in the RIGHT slot (`a` fixed left, the module
  element varying), `AnmFull W p m →ₗ AnmFull W n m`, well-defined modulo the single named residual
  `LeftGradingResidual W n m p` (the DJ Lemma 2.8 LEFT inclusion `𝒱 *ⁿ_{m,p} O_{p,m} ⊆ O_{n,m}`; DJ
  prove it unconditional, this file carries it as `LeftGradingResidual`).
* `oFull` — DJ's genuine `M(U)` 𝒱-mode operator `o_{n,m}(v)` on `MUPieceFull`, `[g]⊗u ↦ [v *ⁿ_{0,m} g]⊗u`.

The module Jacobi (Gannon 5.3.1b / DJ Thm 4.13, via the composition associativity `ψ`, Prop 3.4) is NOT
closed here — it is the remaining Half-B core, on solid (non-degenerate) ground; the bijection is
NOT claimed here.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §4 (line 49–53 the action = bimodule composition; line ~1818 `o_{n,m}`;
Lemma 4.1; Prop 3.4 `ψ`; Thm 4.13); Gannon §5.3.1–§5.3.2; `ZhuVermaAnArchMUFull`,
`ZhuVermaAnArchDJ28Final` (`anmGen_OnmFull_left_of_leftGrading`, `LeftGradingResidual`),
`ZhuVermaAnArchDJ28` (`anmGenRightMap`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped TensorProduct DirectSum

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The descended DJ composition on the full ideal, RIGHT slot** (`a` fixed on the left, the module
element `[g]` varying on the right): `[g] ↦ [a *ⁿ_{m,p} g]` as `AnmFull W p m →ₗ AnmFull W n m`.
Well-defined by the DJ Lemma 2.8 left inclusion `anmGen_OnmFull_left_of_leftGrading`, modulo the single
named residual `LeftGradingResidual W n m p`. -/
noncomputable def anmComposeFullRight (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (a : 𝒱)
    (hgrad : LeftGradingResidual W n m p) : AnmFull W p m →ₗ[ℂ] AnmFull W n m :=
  Submodule.liftQ (OnmFull W p m) ((OnmFull W n m).mkQ.comp (anmGenRightMap W n m p a))
    (fun g hg => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, anmGenRightMap_apply]
      exact anmGen_OnmFull_left_of_leftGrading W n m p a hgrad g hg)

@[simp] theorem anmComposeFullRight_mk (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (a : 𝒱)
    (hgrad : LeftGradingResidual W n m p) (g : 𝒱) :
    anmComposeFullRight W n m p a hgrad (mkAnmFull W p m g) = mkAnmFull W n m (anmGen W n m p a g) := by
  simp only [anmComposeFullRight, mkAnmFull, Submodule.liftQ_apply, LinearMap.comp_apply,
    Submodule.mkQ_apply, anmGenRightMap_apply]

/-- **DJ's genuine `M(U)` 𝒱-mode operator on the full ideal** — the level-`(m → n)` component
`o_{n,m}(v)` of the induced-module action: `[g] ⊗ u ↦ [v *ⁿ_{0,m} g] ⊗ u`, acting by the RIGHT-slot
composition `anmComposeFullRight` on the `AnmFull W m 0` factor, identity on `U`.  This is the BIMODULE
COMPOSITION action (DJ §4 / Lemma 4.1), NOT a levelShift — the NON-DEGENERATE genuine action (its
Borcherds derivative `o_{n,m}(L₋₁v) = −(wt v + m − n) o_{n,m}(v)` is level-dependent, escaping the
levelShift `derivObstruction`).  Well-defined modulo `LeftGradingResidual W n 0 m`. -/
noncomputable def oFull (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n m : ℕ) (v : 𝒱)
    (hgrad : LeftGradingResidual W n 0 m) : MUPieceFull W U m →ₗ[ℂ] MUPieceFull W U n :=
  TensorProduct.map (anmComposeFullRight W n 0 m v hgrad) LinearMap.id

@[simp] theorem oFull_tmul (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n m : ℕ) (v g : 𝒱)
    (hgrad : LeftGradingResidual W n 0 m) (u : U.carrier) :
    oFull W U n m v hgrad (mkAnmFull W m 0 g ⊗ₜ[ℂ] u)
      = mkAnmFull W n 0 (anmGen W n 0 m v g) ⊗ₜ[ℂ] u := by
  simp only [oFull, TensorProduct.map_tmul, LinearMap.id_coe, id_eq, anmComposeFullRight_mk]

/-- **The genuine `M(U)` action is `ℂ`-linear in the acting vector `v`** (as it must be for a field
`Y_{M(U)}(v,z)`): `o_{n,m}(v₁+v₂) = o_{n,m}(v₁) + o_{n,m}(v₂)` and `o_{n,m}(c•v) = c • o_{n,m}(v)`, on
generators.  (From `anmGen_add_left`/`anmGen_smul_left`.) -/
theorem oFull_add_left (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n m : ℕ) (v₁ v₂ : 𝒱)
    (hgrad : LeftGradingResidual W n 0 m) (g : 𝒱) (u : U.carrier) :
    oFull W U n m (v₁ + v₂) hgrad (mkAnmFull W m 0 g ⊗ₜ[ℂ] u)
      = oFull W U n m v₁ hgrad (mkAnmFull W m 0 g ⊗ₜ[ℂ] u)
        + oFull W U n m v₂ hgrad (mkAnmFull W m 0 g ⊗ₜ[ℂ] u) := by
  simp only [oFull_tmul, anmGen_add_left, map_add, TensorProduct.add_tmul]

/-! ## The composition property (DJ Lemma 4.1) — toward the module Jacobi.

DJ Lemma 4.1 (`o_{n,m}(a *ⁿ_{m,p} b) = o_{n,p}(a) o_{p,m}(b)`) is the multiplicative structure of the
`M(U)` action, and on `M(U)` it amounts to the associativity of the composition of the three products
`a, b, g` — i.e. the associativity of DJ's composition `ψ` on the full-ideal quotient.  DJ Thm 2.9
guarantees this associativity holds (it is exactly why `O''` is put into the ideal `O_{n,m}`), so the
residual `MUFullCompAssoc` below is TRUE; but its proof is DJ Thm 2.9's genuine content (Lemma 2.6/2.7/2.8
+ the `O''`/`O'''` reassociation), NOT a single `assocDefect` instance — the bare associator
`a*(b*g) − (a*b)*g` is not literally an `O''` generator (those carry an outer `u`-multiplication).
`oFull_comp` derives the composition property from this residual, reducing the module Jacobi's
multiplicative core to it. -/

/-- **The composition-associativity residual** — the membership form of DJ Thm 2.9's associativity of
the composition `ψ` on the full ideal: `a *ⁿ_{0,p} (b *ᵖ_{0,m} g) ≡ (a *ⁿ_{m,p} b) *ⁿ_{0,m} g`
`(mod OnmFull W n 0)`.  TRUE by DJ Thm 2.9 (the associativity of `ψ`, the raison d'être of `O''`), but a
genuine residual — its proof is DJ Thm 2.9's content, not a trivial `assocDefect_mem_OnmFull` instance
(the bare associator carries no outer `u`).  The precise leaf the composition property needs. -/
def MUFullCompAssoc (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) : Prop :=
  ∀ a b g : 𝒱,
    anmGen W n 0 p a (anmGen W p 0 m b g) - anmGen W n 0 m (anmGen W n m p a b) g ∈ OnmFull W n 0

/-- **The composition property (DJ Lemma 4.1) for the `M(U)` mode operators**, from the associativity
residual `MUFullCompAssoc`: `o_{n,p}(a) ∘ o_{p,m}(b) = o_{n,m}(a *ⁿ_{m,p} b)` on `MUFull`.  This is the
multiplicative core of the module Jacobi (Gannon 5.3.1b / DJ Thm 4.13), reduced to the single named
associativity leaf. -/
theorem oFull_comp (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n m p : ℕ) (a b : 𝒱)
    (hassoc : MUFullCompAssoc W n m p)
    (h₁ : LeftGradingResidual W n 0 p) (h₂ : LeftGradingResidual W p 0 m)
    (h₃ : LeftGradingResidual W n 0 m) :
    (oFull W U n p a h₁).comp (oFull W U p m b h₂) = oFull W U n m (anmGen W n m p a b) h₃ := by
  apply TensorProduct.ext'
  intro y u
  obtain ⟨g, rfl⟩ := (OnmFull W m 0).mkQ_surjective y
  show oFull W U n p a h₁ (oFull W U p m b h₂ (mkAnmFull W m 0 g ⊗ₜ[ℂ] u))
    = oFull W U n m (anmGen W n m p a b) h₃ (mkAnmFull W m 0 g ⊗ₜ[ℂ] u)
  rw [oFull_tmul, oFull_tmul, oFull_tmul]
  have hv : mkAnmFull W n 0 (anmGen W n 0 p a (anmGen W p 0 m b g))
      = mkAnmFull W n 0 (anmGen W n 0 m (anmGen W n m p a b) g) := by
    rw [mkAnmFull, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq]
    exact hassoc a b g
  rw [hv]

/-- **`MUFullCompAssoc W n m p` is unconditional** (DJ Thm 2.9's ψ-associativity on the full
ideal, proved).  The bare three-index associator is `−bareAssoc(n,0,m,p,a,b,g)`, and
`bareAssoc_mem_OnmFull` puts it in `OnmFull W n 0` (it is the associator defect `assocDefect` at the
vacuum-diagonal outer factor — an `O''_{n,0}` generator).  So the composition ψ IS associative on
`AnmFull` — exactly what `O''` is put into DJ's ideal to guarantee (DJ Thm 2.9). -/
theorem mUFullCompAssoc_holds (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) :
    MUFullCompAssoc W n m p := by
  intro a b g
  have h := (OnmFull W n 0).neg_mem (bareAssoc_mem_OnmFull W n 0 m p a b g)
  rwa [neg_sub] at h

/-- **The composition property (DJ Lemma 4.1) needing ONLY `LeftGradingResidual`** — `MUFullCompAssoc`
is discharged (`mUFullCompAssoc_holds`).  So `o_{n,p}(a) ∘ o_{p,m}(b) = o_{n,m}(a *ⁿ_{m,p} b)` on
`MUFull` rests on the single remaining Half-B leaf `LeftGradingResidual` (three instances; DJ Lemma 2.8's
left inclusion, which DJ prove unconditional). -/
theorem oFull_comp_of_leftGrading (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n m p : ℕ) (a b : 𝒱)
    (h₁ : LeftGradingResidual W n 0 p) (h₂ : LeftGradingResidual W p 0 m)
    (h₃ : LeftGradingResidual W n 0 m) :
    (oFull W U n p a h₁).comp (oFull W U p m b h₂) = oFull W U n m (anmGen W n m p a b) h₃ :=
  oFull_comp W U n m p a b (mUFullCompAssoc_holds W n m p) h₁ h₂ h₃

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.anmComposeFullRight
  #print axioms VOA.oFull
-/
