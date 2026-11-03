/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUGradedActionFull
import VOA.Modules.ZhuVermaAnArchMU

/-!
# `M(U)` on Dong–Jiang's GENUINE full-ideal bimodules — Half A closed unconditionally.

Dong–Jiang define `A_{n,m}(V) = V/O_{n,m}(V)` with the FULL ideal `O_{n,m} = O' + O'' + O'''`
(`math/0601626`, line 1013 / line 1257; Thm 2.9), and their induced module (Construction B / Thm 4.13)
is built on those full-ideal bimodules `A_{n,0}(V)`.  This file names DJ's induced-module pieces on the
genuine ideal — `MUPieceFull W U n = AnmFull W n 0 ⊗_ℂ U` with `AnmFull W n 0 = 𝒱 ⧸ OnmFull W n 0` — and
records that the graded (diagonal) `𝒱`-action layer of Zhu Thm 5.3.4's `M(U)` is **already a term,
unconditionally**, on DJ's actual ideal.

## Why this is the correct foundation (the prime-ideal wall was self-inflicted)

The repo's `MUPiece W U n = Anm W n 0 ⊗ U` uses the PRIME ideal `Onm = O'_{n,0}`, so its descended action
`MU.actLevel` requires the closure `AnmRightModule W n` (`𝒱 *ⁿ₀ Onm ⊆ Onm`), whose cross companion is the
OPEN DJ Remark 2.10-adjacent `CrossCircCore` wall.  On DJ's GENUINE full ideal `OnmFull` this closure is
DJ Lemma 2.8 — `mUGradedActionFull_holds`, PROVEN unconditional — so:

* `MUFull.actLevel = actLevelFull` (the level-`n` action on `AnmFull W n 0 ⊗ U`) is a term for every `n`,
  with NO `AnmRightModule` hypothesis;
* the right residue action descends to a genuine right `A(𝒱)`-action (`actAnmFull_apply_mem_O`: it kills
  `O(𝒱) = Onm W 0 0`), the DJ Thm 2.9 right-`A(𝒱)`-module well-definedness, unconditional.

So the Half-A graded-action layer of `M(U)` — the exact obstruction that on the prime ideal is the
`CrossCircCore`/`MUGradedAction` wall — is closed once DJ's genuine ideal is used.  What remains for the
full Zhu-5.3.4 bijection through this carrier is the CROSS (loop) action and the downstream lifting/
irreducibility data (Half B), which are ideal-agnostic-deep and NOT closed here — the bijection row is
NOT flipped.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 (line 1013 `O_{n,m}=O'+O''+O'''`, line 1257 `A_{n,m}=V/O_{n,m}`, Thm 2.9,
Lemma 2.8, Rmk 2.10; §4 Thm 4.13 induced module); Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchAnmFull` (`OnmFull`/`AnmFull`), `ZhuVermaAnArchMUGradedActionFull`
(`mUGradedActionFull_holds`/`actAnmFull`/`actLevelFull`/`actAnmFull_apply_mem_O`), `ZhuVermaAnArchMU`
(the prime `MUPiece`/`MU.actLevel` this mirrors).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped TensorProduct DirectSum

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The full-ideal graded pieces `A_{n,0}(𝒱) ⊗_ℂ U` and carrier `⊕ₙ …`. -/

/-- **The level-`n` graded piece of DJ's induced module on the GENUINE (full) ideal**:
`A_{n,0}(𝒱) ⊗_ℂ U` with `A_{n,0}(𝒱) = 𝒱 ⧸ OnmFull W n 0` = DJ's genuine bimodule `V/O_{n,0}` (full
ideal, `math/0601626` line 1257).  The `OnmFull` analogue of `MUPiece`. -/
abbrev MUPieceFull (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) : Type u :=
  TensorProduct ℂ (AnmFull W n 0) U.carrier

/-- **DJ's induced-module carrier on the genuine (full) ideal**: `M̃(U) = ⊕ₙ A_{n,0}(𝒱) ⊗_ℂ U`,
`A_{n,0} = 𝒱 ⧸ OnmFull W n 0`.  The `OnmFull` analogue of `MU`. -/
abbrev MUFull (W : VertexOperatorAlgebra 𝒱) (U : AMod W) : Type u :=
  ⨁ n : ℕ, MUPieceFull W U n

/-- The canonical inclusion of the level-`n` full-ideal piece into `M̃(U)`. -/
noncomputable def MUFull.incl (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    MUPieceFull W U n →ₗ[ℂ] MUFull W U :=
  DirectSum.lof ℂ ℕ (MUPieceFull W U) n

/-- The canonical projection of `M̃(U)` onto the level-`n` full-ideal piece. -/
noncomputable def MUFull.proj (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    MUFull W U →ₗ[ℂ] MUPieceFull W U n :=
  DirectSum.component ℂ ℕ (MUPieceFull W U) n

/-! ## The unconditional graded (diagonal) `𝒱`-action layer of `M(U)` on DJ's ideal. -/

/-- **The descended level-`n` graded action on `MUPieceFull`, unconditional** (= `actLevelFull`): act
by `actAnmFull` on the left `AnmFull` factor, identity on `U`.  Unlike the prime `MU.actLevel` (which
requires the open `AnmRightModule W n`), this carries NO closure hypothesis — its well-definedness is
`anmRight_OnmFull_unconditional` (DJ Lemma 2.8 right, into DJ's genuine full ideal). -/
noncomputable def MUFull.actLevel (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) (a : 𝒱) :
    MUPieceFull W U n →ₗ[ℂ] MUPieceFull W U n :=
  actLevelFull W U n a

@[simp] theorem MUFull.actLevel_tmul (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) (a x : 𝒱)
    (u : U.carrier) :
    MUFull.actLevel W U n a (mkAnmFull W n 0 x ⊗ₜ[ℂ] u)
      = mkAnmFull W n 0 (anmRight W n 0 x a) ⊗ₜ[ℂ] u :=
  actLevelFull_tmul W U n a x u

/-- **The graded action layer of `M(U)` on DJ's genuine ideal is unconditional** — for every level `n`
and every `a ∈ 𝒱`, the descended diagonal action `MUFull.actLevel W U n a` on the piece
`A_{n,0}(𝒱) ⊗ U` is a term with no open hypothesis.  This is the `OnmFull`-analogue realization of DJ
Theorem 2.9's graded action; on the prime ideal the same layer is the open `MUGradedAction`
(`CrossCircCore`) wall.  (The closure certificate is `mUGradedActionFull_holds`.) -/
theorem mUFull_actLevel_unconditional (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    ∀ (n : ℕ) (a : 𝒱),
      MUFull.actLevel W U n a
        = TensorProduct.map (actAnmFull W n a) LinearMap.id :=
  fun _ _ => rfl

/-- **The right residue action on each full-ideal piece factors through `A(𝒱)`, unconditional** — for
`a ∈ O(𝒱) = Onm W 0 0`, `MUFull.actLevel W U n a = 0`.  So the level action descends to a genuine right
`A(𝒱)`-action on `MUPieceFull W U n`, the DJ Theorem 2.9 right-`A(𝒱)`-module well-definedness into DJ's
genuine ideal — with NO Remark 2.10 collapse (contrast the prime ideal, where this is the open cross
closure).  Immediate from `actAnmFull_apply_mem_O`. -/
theorem mUFull_actLevel_mem_O (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) {a : 𝒱}
    (ha : a ∈ Onm W 0 0) : MUFull.actLevel W U n a = 0 := by
  show actLevelFull W U n a = 0
  rw [actLevelFull, actAnmFull_apply_mem_O W n ha, TensorProduct.map_zero_left]

/-! ## The DJ Theorem 2.9 bimodule composition on DJ's genuine ideal — left slot, unconditional.

DJ Thm 2.9 makes `A_{n,m}(𝒱) = 𝒱 ⧸ OnmFull W n m` an `A_n`-`A_m`-bimodule; the composition
`A_{n,p}(𝒱) → A_{n,m}(𝒱)`, `[g] ↦ [g *ⁿ_{m,p} v]`, is the left-factor structure (well-definedness = the
left ideal `O_{n,p}` maps into `O_{n,m}`, DJ Lemma 2.8).  On DJ's genuine FULL ideal this is
`anmGen_OnmFull_right_unconditional` — unconditional, no descent hypothesis.  (On the prime `Onm` the
same composition `anmComposeHom` requires the descent `AnmComposeDescR`, whose off-diagonal instances are
the Rmk 2.10-adjacent walls.) -/

/-- **The descended DJ Thm 2.9 bimodule composition on the full ideal** (left slot), unconditional:
`[g] ↦ [g *ⁿ_{m,p} v]` as a `ℂ`-linear map `AnmFull W n p →ₗ AnmFull W n m`.  Well-defined by
`anmGen_OnmFull_right_unconditional` (DJ Lemma 2.8) — no descent hypothesis. -/
noncomputable def anmComposeFull (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (v : 𝒱) :
    AnmFull W n p →ₗ[ℂ] AnmFull W n m :=
  Submodule.liftQ (OnmFull W n p) ((OnmFull W n m).mkQ.comp (anmGenLeftMap W n m p v))
    (fun g hg => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, anmGenLeftMap_apply]
      exact anmGen_OnmFull_right_unconditional W n m p v g hg)

@[simp] theorem anmComposeFull_mk (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (v g : 𝒱) :
    anmComposeFull W n m p v (mkAnmFull W n p g) = mkAnmFull W n m (anmGen W n m p g v) := by
  simp only [anmComposeFull, mkAnmFull, Submodule.liftQ_apply, LinearMap.comp_apply,
    Submodule.mkQ_apply, anmGenLeftMap_apply]

/-- **The right-slot residue action on DJ's full-ideal bimodule descends, unconditional**: for the
diagonal composition (`p = m`), `anmComposeFull W n m m v = actAnmFull W n v`-style right action.  In
particular the level-`n` right `A(𝒱)`-module action `[g] ↦ [g *ⁿ₀ v]` of `M(U)` is exactly
`anmComposeFull W n 0 0 v`, matching `actAnmFull W n v` on the carrier `AnmFull W n 0`. -/
theorem anmComposeFull_diag_eq_actAnmFull (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (v : 𝒱) :
    anmComposeFull W n 0 0 v = actAnmFull W n v := by
  apply LinearMap.ext
  intro y
  obtain ⟨g, rfl⟩ := (OnmFull W n 0).mkQ_surjective y
  show anmComposeFull W n 0 0 v (mkAnmFull W n 0 g) = actAnmFull W n v (mkAnmFull W n 0 g)
  rw [anmComposeFull_mk, actAnmFull_mk]
  congr 1
  rw [anmGen_eq_anmRight]

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.MUFull.actLevel
  #print axioms VOA.mUFull_actLevel_unconditional
  #print axioms VOA.mUFull_actLevel_mem_O
-/
