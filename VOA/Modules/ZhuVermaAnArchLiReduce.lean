/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchLiDuality
import VOA.Modules.ZhuVermaAnArchDJ28Term1Capstone

/-!
# `CrossCircCore` from Li's two obligations (the Li-route reduction, ported to the repo).

Using the abstract annihilator-stability duality `mapsTo_of_dualMap_annihilator` (`LiDuality`, = Li Lemma
2.16), this file reduces the sole open Half-A residue `CrossCircCore W n`
(`anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0`) to the two Li-route obligations:

* **`OnmWeakClosed W n`** — `Onm W n 0` is weak-* closed (`p.dualAnnihilator.dualCoannihilator ≤ p`).
  Provable from the graded finite-dimensional structure of `𝒱` (`Onm` is a graded submodule of `𝒱`, each
  `L₀`-weight space finite-dim ⟹ `Onm` equals its double-coannihilator in the full dual).  This is the
  linear-algebra obligation of the Li route.
* **`LiDualStable W n`** — the dual-stability condition: for every `a`, the transpose
  `(anmRightR W n 0 a).dualMap` carries `Ann (Onm W n 0)` into `Ann (Onm W 0 0)`.  This is Haisheng Li's
  regular-representation content (arXiv 2205.05481, Thm 3.17): the annihilators `Ann(Onm n 0) = (A_{n,0})*`
  are modules over `Ω_{0,n}(D^{(-1)}(𝒱))` and the dual action is a module map, so it respects the
  annihilators.  The genuine module-theory obligation of the Li route.

Combined with the proved main theorem `mUGradedAction_of_crossCircCore`, this gives
`MUGradedAction W ⟸ (∀ n, OnmWeakClosed W n) + (∀ n, LiDualStable W n)`, and (via
`zhu534_of_crossCircCore`) reduces the whole Zhu-5.3.4 bijection's Half A to these two Li obligations.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
H. Li arXiv 2205.05481, Thm 3.17 / Lemmas 2.14/2.16; Dong–Jiang math/0601626; Gannon §5.3.
-/

namespace VOA

open VertexOperatorAlgebra Submodule LinearMap

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The Li dual-stability condition** (unbarred `*ⁿ_0`): for every `a`, the transpose of the right
action `anmRightR W n 0 a` carries the annihilator of `Onm W n 0` into the annihilator of `Onm W 0 0`.
Li's regular-representation output (Thm 3.17): the dual of the `O'`-quotient is a module and the dual
action is a module map. -/
def LiDualStable (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  ∀ a : 𝒱, ∀ f ∈ (Onm W n 0).dualAnnihilator,
    (anmRightR W n 0 a).dualMap f ∈ (Onm W 0 0).dualAnnihilator

/-- **`Onm W n 0` is weak-* closed** — the graded finite-dimensional closedness obligation of the Li
route (`p = p.dualAnnihilator.dualCoannihilator`, stated as the nontrivial `≤`). -/
def OnmWeakClosed (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  (Onm W n 0).dualAnnihilator.dualCoannihilator ≤ Onm W n 0

/-- **`CrossCircCore W n` from the two Li obligations** — the Li-route reduction, via the abstract
annihilator-stability duality `mapsTo_of_dualMap_annihilator`.  With `OnmWeakClosed W n` (weak-*
closedness) and `LiDualStable W n` (the dual-module condition), the cross-level closure
`anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0` holds. -/
theorem crossCircCore_of_liDual (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hclosed : OnmWeakClosed W n) (hdual : LiDualStable W n) : CrossCircCore W n := by
  intro K a _ c d
  have hcl : (Onm W n 0).dualAnnihilator.dualCoannihilator ≤ Onm W n 0 := hclosed
  have hdu : ∀ f ∈ (Onm W n 0).dualAnnihilator,
      (anmRightR W n 0 a).dualMap f ∈ (Onm W 0 0).dualAnnihilator := hdual a
  have h := mapsTo_of_dualMap_annihilator (anmRightR W n 0 a) (Onm W n 0) (Onm W 0 0)
    hcl hdu (anmCirc W 0 0 c d) (anmCirc_mem_Onm W 0 0 c d)
  rwa [anmRightR_apply, anmRight_zero, anmCirc_zero_zero] at h

/-- **`MUGradedAction W` from the two Li obligations** (all `n`).  Chaining
`crossCircCore_of_liDual` into the proved main theorem `mUGradedAction_of_crossCircCore` (`Term₂` discharged
by `Term2Level_holds`): the entire Dong–Jiang `M(U)` graded-action crux reduces to the Li-route
obligations `OnmWeakClosed` (graded closedness) + `LiDualStable` (regular-representation module map). -/
theorem mUGradedAction_of_liDual (W : VertexOperatorAlgebra 𝒱)
    (hclosed : ∀ n, OnmWeakClosed W n) (hdual : ∀ n, LiDualStable W n) : MUGradedAction W :=
  mUGradedAction_of_crossCircCore W (fun n => crossCircCore_of_liDual W n (hclosed n) (hdual n))

/-! ## `OnmWeakClosed` is unconditional — over the field `ℂ`, every subspace is weak-* closed. -/

/-- **`OnmWeakClosed W n` holds unconditionally.**  Over a field, any subspace equals its double
annihilator (`Subspace.dualAnnihilator_dualCoannihilator_eq`: linear functionals separate points from
subspaces).  So the graded-closedness obligation of the Li route is discharged — no finiteness needed. -/
theorem onmWeakClosed_holds (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : OnmWeakClosed W n := by
  show (Onm W n 0).dualAnnihilator.dualCoannihilator ≤ Onm W n 0
  exact le_of_eq Subspace.dualAnnihilator_dualCoannihilator_eq

/-- **`CrossCircCore W n` from the SINGLE Li obligation `LiDualStable`** (`OnmWeakClosed` discharged).
The cross-level closure reduces to just the regular-representation dual-module condition. -/
theorem crossCircCore_of_liDualStable (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hdual : LiDualStable W n) : CrossCircCore W n :=
  crossCircCore_of_liDual W n (onmWeakClosed_holds W n) hdual

/-- **`MUGradedAction W` from the SINGLE Li obligation `LiDualStable`** (all `n`).  With `OnmWeakClosed`
unconditional and `Term₂` proved, the ENTIRE Half-A keystone `MUGradedAction W` rests on exactly one
statement: `LiDualStable W n` — Haisheng Li's regular-representation dual-module condition (arXiv
2205.05481, Thm 3.17), the sole remaining obligation for the whole Zhu-5.3.4 bijection's A-direction. -/
theorem mUGradedAction_of_liDualStable (W : VertexOperatorAlgebra 𝒱)
    (hdual : ∀ n, LiDualStable W n) : MUGradedAction W :=
  mUGradedAction_of_liDual W (fun n => onmWeakClosed_holds W n) hdual

/-! ## `LiDualStable` is EQUIVALENT to the primal closure (over `ℂ`) — the honest reduction status.

Over the field `ℂ`, `LiDualStable W n` is not a *weaker* target than the primal cross-level closure — it
is the same statement in dual form.  The forward `LiDualStable ⟹ primal` uses the double-annihilator
(`onmWeakClosed_holds`); the reverse `primal ⟹ LiDualStable` is unconditional (below).  So the
`LiDuality`/`LiReduce` bricks are the correct **adapter** carrying Li's regular-representation output
(`LiDualStable`, the dual-module condition his Thm 3.17 produces) to the repo's `MUGradedAction`, NOT a
reduction in difficulty: the genuine content is the *proof* of `LiDualStable` via the regular
representation `D^{(-1)}(𝒱)` (Li §3, the remaining construction). -/

/-- **`LiDualStable W n` from the primal cross-level closure**, unconditional.  If the right action
`anmRight W n 0 a (·)` carries `O(𝒱) = Onm W 0 0` into `Onm W n 0` (the primal closure), then the dual
condition `LiDualStable` holds trivially (a functional vanishing on `Onm n 0` pulls back, along
`anmRightR n 0 a`, to one vanishing on `Onm 0 0`).  Together with `crossCircCore_of_liDualStable` (the
converse, via the double annihilator) this shows `LiDualStable ⟺ primal closure` over `ℂ` — `LiDualStable`
is the wall in dual form, and Li's regular representation is the genuine (non-circular) proof of it. -/
theorem liDualStable_of_closure (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hprimal : ∀ a : 𝒱, ∀ g ∈ Onm W 0 0, anmRight W n 0 a g ∈ Onm W n 0) :
    LiDualStable W n := by
  intro a f hf
  rw [Submodule.mem_dualAnnihilator]
  intro g hg
  rw [LinearMap.dualMap_apply, anmRightR_apply]
  rw [Submodule.mem_dualAnnihilator] at hf
  exact hf _ (hprimal a g hg)

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossCircCore_of_liDual
  #print axioms VOA.mUGradedAction_of_liDual
-/
