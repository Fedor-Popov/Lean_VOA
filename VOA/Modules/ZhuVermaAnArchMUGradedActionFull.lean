/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ28IntoFull
import VOA.Modules.ZhuVermaAnArchMUcircV

/-!
# `MUGradedActionFull` — the DJ Theorem 2.9 keystone into DJ's ACTUAL ideal `OnmFull`, unconditional.

The repo's `MUGradedAction W` (the `M(U)` `𝒱`-action closure, Half A) targets the PARTIAL ideal `Onm`
(= DJ `O'_{n,0}`).  Its open half `AnmCrossClosure` (`𝒱 *ⁿ₀ O(𝒱) ⊆ O'_{n,0}`) is precisely the
**Dong–Jiang Remark 2.10 open problem** (`O_{n,m}(V) = O'_{n,m}(V)` for `m ≠ n`, of which DJ write
"it seems that this is a very difficult problem and we cannot find a proof for this in this paper";
`math/0601626`).  DJ's own bimodule `A_{n,m}(V) = V/O_{n,m}(V)` uses the FULL ideal
`O_{n,m} = O' + O'' + O''' = OnmFull`, and DJ Theorem 2.9 (the `A_n`-`A_m`-bimodule property) is proven
**into that full ideal** by Lemma 2.8 (reassociation + the off-diagonal `Res` pole-shift Lemma 2.4).

This file proves the corresponding unconditional keystone `MUGradedActionFull W` — the `M(U)`
`𝒱`-action closure into `OnmFull` — as an axiom-clean term with ZERO open hypotheses:

* the right-module family (`O'_{n,0} *ⁿ₀ 𝒱 ⊆ OnmFull`) is `anmRight_OnmFull_unconditional` (DJ 2.8 right);
* the cross family (`𝒱 *ⁿ₀ O(𝒱) ⊆ OnmFull`) is the full **span-closure** of `dj28IntoFull_unconditional`'s
  `crossCirc`/`crossL` generator families (`anmRight W n 0 a (·)` is ℂ-linear via `anmRightR`).

This is the concrete certificate that the Half-A keystone is proved once DJ's real ideal `OnmFull`
is used.  In contrast, the `Onm`(O')
`MUGradedAction` is unprovable in general (its cross half is DJ Rmk 2.10).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemmas 2.4–2.8, Thm 2.9, Rmk 2.10);
Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The cross closure into the FULL ideal** — `𝒱 *ⁿ₀ O(𝒱) ⊆ OnmFull W n 0`, unconditional.  For every
`a` and every `g ∈ O(𝒱) = Onm W 0 0`, `anmRight W n 0 a g ∈ OnmFull W n 0`.  This is the full span
closure (over all `g ∈ O(𝒱)`, not just the generators) of `dj28IntoFull_unconditional`'s `crossCirc`
and `crossL` families: `anmRight W n 0 a (·)` is ℂ-linear (`anmRightR`), so the preimage
`(OnmFull W n 0).comap (anmRightR W n 0 a)` is a submodule containing the circle generators
`anmCirc W 0 0 u v` (`crossCirc`) and the grading generators `anmLgen W 0 0 u` (`crossL`), hence all of
`Onm W 0 0 = span{circle} ⊔ OnmL`.  The DJ Rmk 2.10-free analogue of the open `AnmCrossClosure`. -/
theorem anmCrossClosureFull (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a : 𝒱) :
    ∀ g ∈ Onm W 0 0, anmRight W n 0 a g ∈ OnmFull W n 0 := by
  have hDJ := dj28IntoFull_unconditional W
  have hle : Onm W 0 0 ≤ (OnmFull W n 0).comap (anmRightR W n 0 a) := by
    rw [Onm_eq_sup_span]
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro x ⟨u, v, rfl⟩
      show anmRightR W n 0 a (anmCirc W 0 0 u v) ∈ OnmFull W n 0
      rw [anmRightR_apply]; exact hDJ.crossCirc n a u v
    · rw [OnmL, Submodule.span_le]
      rintro x ⟨u, rfl⟩
      show anmRightR W n 0 a (anmLgen W 0 0 u) ∈ OnmFull W n 0
      rw [anmRightR_apply]; exact hDJ.crossL n a u
  intro g hg
  have hmem := hle hg
  rwa [Submodule.mem_comap, anmRightR_apply] at hmem

/-- **`MUGradedActionFull W`** — the DJ Theorem 2.9 `M(U)` `𝒱`-action closure into DJ's ACTUAL ideal
`OnmFull`.  For every `n`: the right-module family `O'_{n,0} *ⁿ₀ 𝒱 ⊆ OnmFull` and the cross family
`𝒱 *ⁿ₀ O(𝒱) ⊆ OnmFull`.  This is exactly `MUGradedAction` (`AnmRightModule ∧ AnmCrossClosure`) with the
`Onm`(O') targets replaced by `OnmFull` (= DJ's real `O_{n,m}`). -/
def MUGradedActionFull (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ n : ℕ, (∀ g ∈ OnmFull W n 0, ∀ v : 𝒱, anmRight W n 0 g v ∈ OnmFull W n 0)
    ∧ (∀ a : 𝒱, ∀ g ∈ Onm W 0 0, anmRight W n 0 a g ∈ OnmFull W n 0)

/-- **`MUGradedActionFull W` is unconditional** — the DJ Thm 2.9 keystone into the full ideal, with NO
open hypothesis (contrast `MUGradedAction`, whose cross half `AnmCrossClosure` into `Onm`(O') is the DJ
Rmk 2.10 open problem).  Right-module half: `anmRight_OnmFull_unconditional` (DJ 2.8 right); cross half:
`anmCrossClosureFull` (the span-closure of DJ 2.8 `crossCirc`/`crossL`). -/
theorem mUGradedActionFull_holds (W : VertexOperatorAlgebra 𝒱) : MUGradedActionFull W :=
  fun n => ⟨fun g hg v => anmRight_OnmFull_unconditional W n 0 v g hg,
    anmCrossClosureFull W n⟩

/-! ## The descended layer action on `AnmFull W n 0`, unconditional.

The right residue action of `a ∈ 𝒱` descends to a ℂ-linear endomorphism of the FULL-ideal bimodule
carrier `AnmFull W n 0 = 𝒱 ⧸ OnmFull W n 0` with NO open hypothesis — the `OnmFull` analogue of
`MU.actAnm`, which on `Onm`(O') requires the (unprovable, DJ Rmk 2.10) closure `hclo : AnmRightModule W n`.
Here the well-definedness is the unconditional `anmRight_OnmFull_unconditional` (DJ 2.8 right). -/

/-- **The descended right action on `AnmFull W n 0`, unconditional.**  `[x] ↦ [x *ⁿ₀ a]` on
`AnmFull W n 0 = 𝒱 ⧸ OnmFull W n 0`.  Well-defined because `x ∈ OnmFull ⟹ x *ⁿ₀ a ∈ OnmFull`
(`anmRight_OnmFull_unconditional`) — no closure hypothesis, unlike the `Onm`(O') `MU.actAnm`. -/
noncomputable def actAnmFull (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a : 𝒱) :
    AnmFull W n 0 →ₗ[ℂ] AnmFull W n 0 :=
  Submodule.liftQ (OnmFull W n 0) ((OnmFull W n 0).mkQ.comp (anmRightL W n 0 a))
    (fun x hx => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, anmRightL_apply]
      exact anmRight_OnmFull_unconditional W n 0 a x hx)

@[simp] theorem actAnmFull_mk (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a x : 𝒱) :
    actAnmFull W n a (mkAnmFull W n 0 x) = mkAnmFull W n 0 (anmRight W n 0 x a) := by
  simp only [actAnmFull, mkAnmFull, Submodule.liftQ_apply, LinearMap.comp_apply,
    Submodule.mkQ_apply, anmRightL_apply]

/-- **The descended level action on the FULL-ideal `M(U)` piece `AnmFull W n 0 ⊗ U`, unconditional.**
Act by `actAnmFull` on the left `AnmFull` factor, identity on `U` — the `OnmFull` analogue of
`MU.actLevel` (which needs the open `AnmRightModule W n`). -/
noncomputable def actLevelFull (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) (a : 𝒱) :
    TensorProduct ℂ (AnmFull W n 0) U.carrier →ₗ[ℂ] TensorProduct ℂ (AnmFull W n 0) U.carrier :=
  TensorProduct.map (actAnmFull W n a) LinearMap.id

@[simp] theorem actLevelFull_tmul (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) (a x : 𝒱)
    (u : U.carrier) :
    actLevelFull W U n a (mkAnmFull W n 0 x ⊗ₜ[ℂ] u)
      = mkAnmFull W n 0 (anmRight W n 0 x a) ⊗ₜ[ℂ] u := by
  simp only [actLevelFull, TensorProduct.map_tmul, LinearMap.id_coe, id_eq, actAnmFull_mk]

/-- **The right action on `AnmFull` factors through `A(𝒱)`** — `actAnmFull W n a = 0` whenever
`a ∈ O(𝒱) = Onm W 0 0`, so the right residue action descends to a genuine right `A(𝒱)`-action on the
FULL-ideal bimodule carrier `AnmFull W n 0`.  This is the right-`A(𝒱)`-module well-definedness of DJ
Theorem 2.9 (into `OnmFull`), unconditional: `x *ⁿ₀ a ∈ OnmFull` for `a ∈ O(𝒱)` is `anmCrossClosureFull`.
(On `Onm`(O') this is again the DJ Rmk 2.10 open cross closure.) -/
theorem actAnmFull_apply_mem_O (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {a : 𝒱}
    (ha : a ∈ Onm W 0 0) : actAnmFull W n a = 0 := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (OnmFull W n 0).mkQ_surjective y
  rw [LinearMap.zero_apply]
  show actAnmFull W n a (mkAnmFull W n 0 x) = 0
  rw [actAnmFull_mk, mkAnmFull, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact anmCrossClosureFull W n x a ha

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.anmCrossClosureFull
  #print axioms VOA.mUGradedActionFull_holds
-/
