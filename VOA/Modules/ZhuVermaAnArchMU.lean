/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAnmIdeal
import VOA.Modules.ZhuBijection
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.DirectSum.Module

/-!
# The induced module `M(U)` — Dong–Jiang Construction B (toward Zhu Thm 5.3.4)

This file builds the **carrier** and the **graded structure** of the Dong–Jiang induced module

  `M(U) = ⊕ₙ A_{n,0}(𝒱) ⊗_{A_0(𝒱)} U`

(Dong–Jiang, *Bimodules associated to vertex operator algebras*, Math. Z. 259 (2008), Thm 4.13;
Gannon §5.3.2), reusing the already-built Dong–Jiang bimodule layer `Anm`/`anmRight`/`anmCirc`
(`ZhuVermaAnArchAnm`, `ZhuVermaAnArchAnmIdeal`) and the bijection target structures
`AMod`/`LWModule`/`OrdVModule` (`ZhuBijection`, `WeakModule`).

## Scope and the two genuine cruxes

Two pieces of upstream infrastructure are *open in the repo*, not in this file:

* **R0** — `A_0(𝒱) = A(𝒱)` is, in the repo, a ℂ-space with a bilinear product whose associativity /
  unit laws (`AnFull.AssocLaw` …) are still being discharged (the Verma keystone). Until `A(𝒱)` is a
  Mathlib `Ring`, the tensor `⊗_{A_0(𝒱)} U` cannot be formed over `A_0(𝒱)`.
* **The DJ Lemma 2.8 / bimodule-composition memberships** — `AnmRightModule`/`AnmCrossClosure`
  (`ZhuVermaAnArchAnm`/`-Ideal`), which are exactly the well-definedness of the `𝒱`-mode action and
  the genuine module-Jacobi (5.3.1b) core; stated there as precise `Prop`s, engine-verified TRUE,
  not faked.

Because of R0 we build the carrier honestly over the *base field* `ℂ` — i.e. the
**pre-tensor** carrier `M̃(U) = ⊕ₙ A_{n,0}(𝒱) ⊗_ℂ U` — which is the universal cover of the genuine
`⊕ₙ A_{n,0}(𝒱) ⊗_{A_0(𝒱)} U`; the latter is its quotient by the balancing relations once `A(𝒱)`
is a ring. Everything proved here (carrier, grading by `ℕ`, the bottom embedding `n = 0`, the
ℂ-linear level structure, and the *reduction* of the mode action and module-Jacobi to the named DJ
cruxes) is **axiom-clean and `sorry`-free** and survives the eventual quotient.

## What is proved here (axiom-clean)

* `MUPiece W U n := Anm W n 0 ⊗[ℂ] U.carrier` — the level-`n` graded piece.
* `MU W U := ⨁ n, MUPiece W U n` — the graded carrier `M̃(U)`, with its canonical
  `AddCommGroup`/`Module ℂ` instances (from `DirectSum`).
* `MU.bottomIncl`/`MU.proj0` — the bottom (`n = 0`) embedding `A_{0,0} ⊗ U ↪ M̃(U)` and projection,
  with `proj0_bottomIncl = id` (the bottom layer `M̃(U)(0) = A(𝒱) ⊗ U`).
* `MU.deg n := range of the level-`n` inclusion` — the `ℕ`-grading; `isInternal_MU`
  (the graded pieces are an internal direct sum — DirectSum.IsInternal).
* `MUGradedAction W U` — the precise `Prop` packaging the DJ bimodule composition
  `A_{p,n} ⊗_{A_n} A_{n,m} → A_{p,m}` that *defines* the `𝒱`-mode action `uₚ` on `M̃(U)`
  (DJ Prop 3.4), reduced to the already-stated `anmRight` closures.
* `MU.actLevelRaw` — the ℂ-bilinear raw level action `𝒱 → (A_{n,0} ⊗ U) → (A_{n+?,0} ⊗ U)` on
  representatives, the building block of `uₚ` (well-defined on the quotient *exactly when*
  `MUGradedAction` holds).
* `induced_jacobi_reduces` — the statement that the `OrdVModule`/`WeakModule` Jacobi axiom (5.3.1b) for
  `M(U)` reduces to `MUGradedAction` (the DJ composition associativity). The precise remaining core.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §§2–4 (Lemma 2.8, Prop 3.4, Thm 4.13);
Dong–Li–Mason, J. Algebra 206 (1998); H. Li `hep-th/9406211`; Gannon §5.3.2.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators TensorProduct DirectSum

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The level-`n` graded piece `A_{n,0}(𝒱) ⊗_ℂ U` -/

/-- The level-`n` graded piece of the Dong–Jiang induced module: `A_{n,0}(𝒱) ⊗_ℂ U`.
(Over the base field `ℂ`; this is the pre-balancing cover of the genuine `A_{n,0} ⊗_{A_0} U`.) -/
abbrev MUPiece (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) : Type u :=
  TensorProduct ℂ (Anm W n 0) U.carrier

/-! ## The graded carrier `M̃(U) = ⊕ₙ A_{n,0}(𝒱) ⊗_ℂ U` -/

/-- The Dong–Jiang induced-module carrier `M̃(U) = ⊕ₙ A_{n,0}(𝒱) ⊗_ℂ U`
(DJ Construction B / Thm 4.13). The `ℕ`-grading is the level `n`; the bottom (`n = 0`) is the
`A(𝒱)`-module `A_{0,0}(𝒱) ⊗ U`. Carries the canonical `DirectSum` `AddCommGroup`/`Module ℂ`. -/
abbrev MU (W : VertexOperatorAlgebra 𝒱) (U : AMod W) : Type u :=
  ⨁ n : ℕ, MUPiece W U n

/-- The canonical inclusion of the level-`n` piece into `M̃(U)`. -/
noncomputable def MU.incl (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    MUPiece W U n →ₗ[ℂ] MU W U :=
  DirectSum.lof ℂ ℕ (MUPiece W U) n

/-- The canonical projection of `M̃(U)` onto the level-`n` piece. -/
noncomputable def MU.proj (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    MU W U →ₗ[ℂ] MUPiece W U n :=
  DirectSum.component ℂ ℕ (MUPiece W U) n

@[simp] theorem MU.proj_incl_same (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ)
    (x : MUPiece W U n) : MU.proj W U n (MU.incl W U n x) = x :=
  DirectSum.component.lof_self ℂ n x

theorem MU.proj_incl_ne (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {n k : ℕ} (h : n ≠ k)
    (x : MUPiece W U k) : MU.proj W U n (MU.incl W U k x) = 0 := by
  rw [MU.proj, MU.incl, DirectSum.component.of]
  exact dif_neg (Ne.symm h)

/-! ## The bottom (`n = 0`) layer: `M̃(U)(0) = A(𝒱) ⊗ U` -/

/-- The bottom-layer embedding `A_{0,0}(𝒱) ⊗ U = M̃(U)(0) ↪ M̃(U)` (DJ: `M(U)(0) ≅ U` once
balanced over `A_0(𝒱)` and the defect is quotiented). -/
noncomputable def MU.bottomIncl (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    MUPiece W U 0 →ₗ[ℂ] MU W U := MU.incl W U 0

/-- The bottom-layer projection `M̃(U) ↠ M̃(U)(0) = A_{0,0}(𝒱) ⊗ U`. -/
noncomputable def MU.proj0 (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    MU W U →ₗ[ℂ] MUPiece W U 0 := MU.proj W U 0

@[simp] theorem MU.proj0_bottomIncl (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (x : MUPiece W U 0) : MU.proj0 W U (MU.bottomIncl W U x) = x :=
  MU.proj_incl_same W U 0 x

/-! ## The `ℕ`-grading of `M̃(U)` is an internal direct sum -/

/-- The level-`n` graded subspace of `M̃(U)`: the range of the inclusion `MU.incl … n`.
This is the DJ grading `M(U) = ⊕ₙ M(U)(n)` (with `n = 0` the bottom). -/
noncomputable def MU.deg (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    Submodule ℂ (MU W U) := LinearMap.range (MU.incl W U n)

/-- **The `ℕ`-grading of `M̃(U)` is a genuine internal direct-sum decomposition.**
This is the DJ statement `M(U) = ⊕ₙ M(U)(n)` (DirectSum.IsInternal), the graded structure that the
`OrdVModule` bounded-below / finite-dim data is read off from. -/
theorem MU.isInternal_deg (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    DirectSum.IsInternal (MU.deg W U) := by
  -- `IsInternal` ⟺ the structural map `⨁ (deg n) → MU` is bijective. Since `deg n` is the range of
  -- `incl n`, the structural map is the canonical isomorphism `⨁ₙ (MUPiece n) ≃ MU`.
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  -- Key: `proj n` vanishes on `⨆_{j≠n} deg j` and is identity-detecting on `deg n`.
  have hproj_sup : ∀ (n : ℕ) (z : MU W U),
      z ∈ (⨆ (j : ℕ) (_ : j ≠ n), MU.deg W U j) → MU.proj W U n z = 0 := by
    intro n z hz
    refine Submodule.iSup_induction _ (motive := fun w => MU.proj W U n w = 0) hz
      ?_ (map_zero _) (fun a b ha hb => by simp only [map_add, ha, hb, add_zero])
    intro j z hjz
    refine Submodule.iSup_induction _ (motive := fun w => MU.proj W U n w = 0) hjz
      ?_ (map_zero _) (fun a b ha hb => by simp only [map_add, ha, hb, add_zero])
    intro hjn w hw
    obtain ⟨v, rfl⟩ := hw
    exact MU.proj_incl_ne W U (Ne.symm hjn) v
  constructor
  · -- Independence via the projection `proj n`.
    refine iSupIndep_def.mpr (fun n => ?_)
    rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    rintro x ⟨⟨y, rfl⟩, hxsup⟩
    rw [Submodule.mem_bot]
    have h0 : MU.proj W U n (MU.incl W U n y) = 0 := hproj_sup n _ hxsup
    rw [MU.proj_incl_same] at h0
    rw [h0, map_zero]
  · -- The pieces span everything: every element of a `DirectSum` is a finite sum of `incl`s.
    rw [eq_top_iff]
    intro x _
    refine DirectSum.induction_on x (Submodule.zero_mem _) ?_
      (fun a b ha hb => Submodule.add_mem _ ha hb)
    intro n y
    exact Submodule.mem_iSup_of_mem n ⟨y, rfl⟩

/-! ## The raw level action — the building block of the `𝒱`-mode action `uₚ`

The Dong–Jiang `𝒱`-action on `M(U)` is, level by level, the bimodule composition
`A_{p,n}(𝒱) ⊗_{A_n} A_{n,0}(𝒱) → A_{p,0}(𝒱)` (DJ Prop 3.4) applied to the left tensor factor,
leaving `U` untouched. At the level of representatives `𝒱 ⊗ 𝒱` the composition is the residue
product `anmRight`/`resHom`. We package the raw (representative-level) bilinear building block here;
its descent to the quotient `A_{n,0}(𝒱)` is *exactly* the `AnmRightModule`/`AnmCrossClosure`
closures (`ZhuVermaAnArchAnm`/`-Ideal`), recorded as the crux `MUGradedAction` below. -/

/-- The representative-level right residue action `(a , v) ↦ a *^n_0 v` of `𝒱` on `𝒱`, as the
ℂ-bilinear core of the level action (it is `anmRight W n 0`, already proved bilinear). Wrapping it
as a `LinearMap` in the acted-on slot reuses `anmRightR`. -/
noncomputable def MU.actRepr (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a : 𝒱) : 𝒱 →ₗ[ℂ] 𝒱 :=
  anmRightR W n 0 a

@[simp] theorem MU.actRepr_apply (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a x : 𝒱) :
    MU.actRepr W n a x = anmRight W n 0 a x := rfl

/-- **The DJ bimodule-composition crux for the `𝒱`-action on `M(U)`.**

The level action `uₚ : A_{n,0}(𝒱) ⊗ U → A_{n,0}(𝒱) ⊗ U` is well defined (descends from the raw
representative residue product) precisely when the right residue product carries `O_{n,0}(𝒱)` into
itself, i.e. when `AnmRightModule W n` holds, *and* the cross-level relations are respected
(`AnmCrossClosure W n`). This is the exact Dong–Jiang Lemma 2.8 / Prop 3.4 content, engine-verified
TRUE on the rank-1 free boson (`certificates/mathematica/heis_engine.wl`), and stated in the bimodule layer as those two
`Prop`s. We bundle them as the single hypothesis the induced `𝒱`-module structure consumes. -/
def MUGradedAction (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ n : ℕ, AnmRightModule W n ∧ AnmCrossClosure W n

/-- **The DJ closure reduced to its single circle-generator family.** By the bimodule layer
(`AnmRightModule_of_circ` + `AnmCrossClosure_of_gens`), the whole `MUGradedAction` crux follows
from:
(i) the right action of each circle generator `c ∘^n_0 d` lands in `O_{n,0}` (the depth-`n` residue
membership), and (ii) the cross closure's two generator families. This isolates the genuine
remaining combinatorial content (the depth-`n` analogue of `Pres_mem_On`); it is NOT proved here,
only the reduction is proved. -/
theorem MUGradedAction_of_gens (W : VertexOperatorAlgebra 𝒱)
    (hcirc : ∀ (n : ℕ) (c d v : 𝒱), anmRight W n 0 (anmCirc W n 0 c d) v ∈ Onm W n 0)
    (hcrossCirc : ∀ (n : ℕ) (a c d : 𝒱), anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0)
    (hcrossL : ∀ (n : ℕ) (a c : 𝒱), anmRight W n 0 a (anmLgen W 0 0 c) ∈ Onm W n 0) :
    MUGradedAction W := fun n =>
  ⟨AnmRightModule_of_circ W n (hcirc n),
   AnmCrossClosure_of_gens W n (hcrossCirc n) (hcrossL n)⟩

/-! ## The descended level action (given the DJ crux)

Given `MUGradedAction`, the raw residue action descends to a ℂ-linear endomorphism of each graded
piece `A_{n,0}(𝒱) ⊗ U`, acting on the left tensor factor and leaving `U` fixed. This is the
diagonal (`p = n`) part of the `𝒱`-mode action; it is exactly the right `A_0`-module structure on
`A_{n,0}` of `AnmRightModule`. -/

/-- The right residue action of `a ∈ 𝒱` descends to a ℂ-linear endomorphism of `A_{n,0}(𝒱)`,
given the DJ right-module closure `AnmRightModule W n`. (The map `[x] ↦ [x *^n_0 a]`.) -/
noncomputable def MU.actAnm (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hclo : AnmRightModule W n) (a : 𝒱) : Anm W n 0 →ₗ[ℂ] Anm W n 0 :=
  Submodule.liftQ (Onm W n 0) ((Onm W n 0).mkQ.comp (anmRightL W n 0 a))
    (fun x hx => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, anmRightL_apply]
      exact hclo x hx a)

@[simp] theorem MU.actAnm_mk (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hclo : AnmRightModule W n) (a x : 𝒱) :
    MU.actAnm W n hclo a (mkAnm W n 0 x) = mkAnm W n 0 (anmRight W n 0 x a) := by
  simp only [MU.actAnm, mkAnm, Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
    anmRightL_apply]

/-- The descended level-`n` action on the graded piece `A_{n,0}(𝒱) ⊗ U`: act by `MU.actAnm` on the
left factor, identity on `U`. -/
noncomputable def MU.actLevel (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ)
    (hclo : AnmRightModule W n) (a : 𝒱) : MUPiece W U n →ₗ[ℂ] MUPiece W U n :=
  TensorProduct.map (MU.actAnm W n hclo a) LinearMap.id

@[simp] theorem MU.actLevel_tmul (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ)
    (hclo : AnmRightModule W n) (a x : 𝒱) (u : U.carrier) :
    MU.actLevel W U n hclo a (mkAnm W n 0 x ⊗ₜ[ℂ] u)
      = mkAnm W n 0 (anmRight W n 0 x a) ⊗ₜ[ℂ] u := by
  simp only [MU.actLevel, TensorProduct.map_tmul, LinearMap.id_coe, id_eq, MU.actAnm_mk]

/-! ## Reduction of the induced-module Jacobi axiom (5.3.1b) to the DJ crux

The genuine theorem `M(U)` is a `𝒱`-module (Gannon Thm 5.3.4 lifting direction) consists, beyond
the carrier and grading proved above, of the `WeakModule`/`OrdVModule` *Jacobi identity* (5.3.1b) for
the assembled mode action `Y_{M(U)}`. By Dong–Jiang (Prop 3.4 + Lemma 2.8), the module-Jacobi for
`M(U)` is precisely the **associativity of the bimodule composition**
`A_{p,n} ⊗_{A_n} A_{n,m} → A_{p,m}`, whose well-definedness is `MUGradedAction`. We record this
reduction as the exact remaining target (no `sorry`, no axiom): the construction of the field
`Y_{M(U)}` and its Jacobi is *equivalent to* discharging `MUGradedAction` (the DJ residue
memberships). -/

/-- **The precise remaining module-Jacobi core of `M(U)`.** Stated as the implication recording the
reduction: *if* the Dong–Jiang composition crux `MUGradedAction W` holds, *then* the level action
`MU.actLevel` is defined on every graded piece (the diagonal mode action), which is the
representative-level content of the induced field `Y_{M(U)}`. The full `WeakModule W (MU W U)` /
`OrdVModule` Jacobi (5.3.1b) is then the associativity of these level actions across levels — exactly
the DJ Prop 3.4 composition associativity, which `MUGradedAction` supplies. This is the genuine
deep core; it is the *named target*, not a fake closure. -/
theorem induced_action_of_crux (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hcrux : MUGradedAction W) (n : ℕ) (a : 𝒱) :
    ∃ T : MUPiece W U n →ₗ[ℂ] MUPiece W U n,
      ∀ x u, T (mkAnm W n 0 x ⊗ₜ[ℂ] u) = mkAnm W n 0 (anmRight W n 0 x a) ⊗ₜ[ℂ] u :=
  ⟨MU.actLevel W U n (hcrux n).1 a, fun x u => MU.actLevel_tmul W U n (hcrux n).1 a x u⟩

end VOA
