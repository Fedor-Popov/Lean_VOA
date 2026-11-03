/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ28Left
import VOA.Modules.ZhuVermaAnArchDJ28Right
import VOA.Modules.ZhuVermaAnArchDJ25

/-!
# Dong–Jiang **Lemma 2.8** — the maximal assembly from the closed generator branches.

This file assembles the headline Dong–Jiang, *Bimodules associated to vertex operator algebras*,
Math. Z. 259 (2008) 799–826 (`math/0601626`), **Lemma 2.8** from the generator branches discharged
by the prior runs.  It reduces the entire residual `DJ28Residual` (and the two general inclusions
`anmGen_OnmFull_left`/`anmGen_OnmFull_right`, and the headline specializations
`anmGenBar_OnmFull`/`anmRight_OnmFull`) to the **single** remaining analytic identity

  `LeftGradingResidual W n m p`  (`ZhuVermaAnArchDJ28Left`),

i.e. the general right-slot grading absorption `a ∗ⁿ_{m,p} (anmLgen W p m c) ∈ O_{n,m}` (DJ display
(2.1), the `O'_{p,m}` grading generator).  Everything else is a proven term.

## What is closed (axiom-clean; no `sorry`/`pbw`), and where

* **RIGHT inclusion** `O_{n,p} ∗ⁿ_{m,p} V ⊆ O_{n,m}` (DJ (2.2)) — **fully unconditional**.  Its
  three generator branches `rightO'Circ` (DJ Lemma 2.5), `rightO''`, `rightO'''` are
  `dj28Residual_right` (`ZhuVermaAnArchDJ28Right`); each closes via the bare associator landing on
  an `assocDefect`/`levelMix` generator, plus DJ 2.2 for the circle branch.
* **DJ Lemma 2.5** (`offCirc`, the `O'_{p₂,p₁}` circle cross term) — `offCirc_mem`
  (`ZhuVermaAnArchDJ25`), unconditional, so `DJ27ChainTail` is `dj27ChainTail_holds` and DJ Lemma
  2.7 is `levelMixGen_mem_OnmFull_unconditional`.
* **LEFT inclusion** `V ∗ⁿ_{m,p} O_{p,m} ⊆ O_{n,m}` (DJ (2.1)):
  - `leftO''` (associator branch) — `leftO''_mem` (`ZhuVermaAnArchDJ28Left`), **unconditional**;
  - `leftO'''` (level-mixing branch) — `leftO'''_mem`, via DJ's published coupled induction; here
    the coupling **bottoms out unconditionally**, because `leftO'''` consumes only the RIGHT
    inclusion at the inner level `q` (which uses only the three unconditional right fields);
  - `leftO'Lgen` (the `O'_{p,m}` grading branch) — the **single genuinely-open** identity, carried as
    `LeftGradingResidual` (the general right-slot residue absorption, the right-factor analogue of
    `anmGen_offdiag_Lgen_eq_general`; only its `m = 0` special case
    `anmRight_zero_crossL_mem_Onm` exists on disk).

## The key structural point — the left/right coupling bottoms out

DJ's Lemma 2.8 is a single across-levels induction.  In this repo `leftO'''` is the only left branch
that references another inclusion, and it references the **right** inclusion at the inner level `q`.
The right inclusion is unconditional, so the coupling is not circular: `dj28Residual_rightFilled`
supplies a `DJ28Residual W n m q` whose three right fields are `dj28Residual_right` (term-level),
and `anmGen_OnmFull_right` consumes only those.  Hence `leftO'''_mem` needs no carried hypothesis
beyond what is already a term, and the *whole* `DJ28Residual W n m p` is built from
`LeftGradingResidual W n m p` alone.

## Proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `dj28Residual_rightFilled` — a `DJ28Residual W n m p` with the three right fields and `leftO''`
  filled by proven terms, and the left grading/level fields supplied (the level field needs nothing
  open; the grading field is the single `LeftGradingResidual` hypothesis).
* `dj28Residual_of_leftGrading` — `LeftGradingResidual W n m p` ⟹ `DJ28Residual W n m p` (all six
  fields), the maximal packaging.
* `anmGen_OnmFull_left_of_leftGrading` / `anmGen_OnmFull_right_unconditional` — DJ 2.8 both general
  inclusions (left modulo `LeftGradingResidual`; right unconditional).
* `anmGenBar_OnmFull_of_leftGrading` / `anmRight_OnmFull_unconditional` — DJ 2.8 "in particular"
  (the `∗̄ⁿ_m` headline modulo `LeftGradingResidual`; the `∗ⁿ_m` headline unconditional).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemmas 2.2, 2.5, 2.7, **2.8**).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The right inclusion is unconditional (no carried hypothesis). -/

/-- **DJ Lemma 2.8, the right inclusion `O_{n,p} ∗ⁿ_{m,p} V ⊆ O_{n,m}` — unconditional.**

Same `Submodule.mem_sup` split over `OnmFull W n p = (Onm ⊔ OnmAssoc) ⊔ OnmLevel` as the conditional
`anmGen_OnmFull_right`, but fed directly on the three unconditional right generator families
(`anmRight_O'Circ_mem`/`anmRight_O''_mem`/`anmRight_O'''_mem`, `ZhuVermaAnArchDJ28Right`).  No
`DJ28Residual` (and hence no `LeftGradingResidual`) is consumed: the right inclusion is closed
outright. -/
theorem anmGen_OnmFull_right_unconditional (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (v : 𝒱) :
    ∀ g ∈ OnmFull W n p, anmGen W n m p g v ∈ OnmFull W n m := by
  intro g hg
  rw [OnmFull, Submodule.mem_sup] at hg
  obtain ⟨y, hy, z, hz, rfl⟩ := hg
  rw [anmGen_add_left]
  refine (OnmFull W n m).add_mem ?_ ?_
  · rw [Submodule.mem_sup] at hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hy
    rw [anmGen_add_left]
    refine (OnmFull W n m).add_mem ?_ ?_
    · -- `y₁ ∈ Onm W n p` (the `O'` summand): circle = `rightO'Circ`, grading = closed off-diagonal.
      have hle := Onm_le_comap_leftMap W n m p v
        (fun c d => anmRight_O'Circ_mem W n m p c d v)
      have hx : y₁ ∈ (OnmFull W n m).comap (anmGenLeftMap W n m p v) := hle hy₁
      rwa [Submodule.mem_comap, anmGenLeftMap_apply] at hx
    · -- `y₂ ∈ OnmAssoc W n p` (the `O''` summand): `rightO''`.
      have hle := OnmAssoc_le_comap_leftMap W n m p v
        (fun q₁ q₂ q₃ b₁ b₂ b₃ w => anmRight_O''_mem W n m p v q₁ q₂ q₃ b₁ b₂ b₃ w)
      have hx : y₂ ∈ (OnmFull W n m).comap (anmGenLeftMap W n m p v) := hle hy₂
      rwa [Submodule.mem_comap, anmGenLeftMap_apply] at hx
  · -- `z ∈ OnmLevel W n p` (the `O'''` summand): `rightO'''`.
    have hle := OnmLevel_le_comap_leftMap W n m p v
      (fun q b w g hg => anmRight_O'''_mem W n m p v q b w g hg)
    have hx : z ∈ (OnmFull W n m).comap (anmGenLeftMap W n m p v) := hle hz
    rwa [Submodule.mem_comap, anmGenLeftMap_apply] at hx

/-! ## The level-mixing left branch `leftO'''`, with the right-inclusion coupling discharged. -/

/-- **`leftO'''`, unconditional.**  `a ∗ⁿ_{m,p} (levelMix W p m q b g w) ∈ O_{n,m}` for `g ∈ O_q`.

This is `leftO'''_mem` (DJ's coupled induction), whose only carried hypothesis was
`DJ28Residual W n m q` — and that hypothesis is consumed *exclusively* by the right inclusion at
level `q` (the `O_{n,q} ∗ⁿ_{m,q} V` correction), which reads only the right fields.  We inline
`anmGen_OnmFull_right_unconditional` in place of the coupled-induction hypothesis, mirroring
`leftO'''_mem` but with the inner right inclusion supplied unconditionally. -/
theorem leftO'''_unconditional (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (a : 𝒱)
    (q : ℕ) (b w : 𝒱) (g : 𝒱) (hg : g ∈ Onm W q q) :
    anmGen W n m p a (levelMix W p m q b g w) ∈ OnmFull W n m := by
  -- `X = b ∗^p_q g`, the inner `*^p_{q,q}` product.
  set X : 𝒱 := anmGen W p q q b g with hX
  have hdef : levelMix W p m q b g w = anmGen W p m q X w := rfl
  rw [hdef]
  -- STEP 1: bare associator with `(p₂,p₁) = (p,q)`, `(b,c) = (X,w)`.
  have hbare1 := bareAssoc_mem_OnmFull W n m q p a X w
  set Y : 𝒱 := anmGen W n q p a X with hY
  -- STEP 2: bare associator with `(p₂,p₁) = (p,q)`, `(b,c) = (b,g)` at top level `q`.
  have hbare2 := bareAssoc_mem_OnmFull W n q q p a b g
  set Z : 𝒱 := anmGen W n q q (anmGen W n q p a b) g with hZ
  set D : 𝒱 := Z - Y with hD
  have hDmem : D ∈ OnmFull W n q := hbare2
  have hYsplit : Y = Z - D := by rw [hD]; abel
  have hsplit : anmGen W n m q Y w = anmGen W n m q Z w - anmGen W n m q D w := by
    have := (anmGenLeftMap W n m q w).map_sub Z D
    simp only [anmGenLeftMap_apply] at this
    rw [hYsplit]; exact this
  have hlevelMem : anmGen W n m q Z w ∈ OnmFull W n m := by
    have hLM : anmGen W n m q Z w = levelMix W n m q (anmGen W n q p a b) g w := rfl
    rw [hLM]
    exact levelMix_mem_OnmFull W n m q (anmGen W n q p a b) w g hg
  -- the `O_{n,q}` correction, after the outer `· ∗ⁿ_{m,q} w`, via the unconditional right inclusion.
  have hcorrMem : anmGen W n m q D w ∈ OnmFull W n m :=
    anmGen_OnmFull_right_unconditional W n m q w D hDmem
  have hYmem : anmGen W n m q Y w ∈ OnmFull W n m := by
    rw [hsplit]; exact (OnmFull W n m).sub_mem hlevelMem hcorrMem
  have := (OnmFull W n m).sub_mem hYmem hbare1
  rwa [sub_sub_cancel] at this

/-! ## The maximal `DJ28Residual` — from `LeftGradingResidual` alone. -/

/-- **`LeftGradingResidual W n m p` ⟹ `DJ28Residual W n m p`** — the maximal packaging.

Five of the six branches are proven terms:
* `leftO'Lgen`  — `leftO'Lgen_mem … hgrad` (the carried `LeftGradingResidual`);
* `leftO''`     — `leftO''_mem` (unconditional);
* `leftO'''`    — `leftO'''_unconditional` (coupling discharged via the unconditional right inclusion);
* `rightO'Circ` — `anmRight_O'Circ_mem` (DJ Lemma 2.5, unconditional);
* `rightO''`    — `anmRight_O''_mem` (unconditional);
* `rightO'''`   — `anmRight_O'''_mem` (unconditional). -/
theorem dj28Residual_of_leftGrading (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ)
    (hgrad : LeftGradingResidual W n m p) :
    DJ28Residual W n m p where
  leftO'Lgen a c := leftO'Lgen_mem W n m p a c hgrad
  leftO'' a q₁ q₂ q₃ b₁ b₂ b₃ w := leftO''_mem W n m p a q₁ q₂ q₃ b₁ b₂ b₃ w
  leftO''' a q b w g hg := leftO'''_unconditional W n m p a q b w g hg
  rightO'Circ c d v := anmRight_O'Circ_mem W n m p c d v
  rightO'' v q₁ q₂ q₃ b₁ b₂ b₃ w := anmRight_O''_mem W n m p v q₁ q₂ q₃ b₁ b₂ b₃ w
  rightO''' v q b w g hg := anmRight_O'''_mem W n m p v q b w g hg

/-! ## DJ Lemma 2.8 — the two general inclusions, maximally discharged. -/

/-- **DJ Lemma 2.8, the LEFT inclusion `V ∗ⁿ_{m,p} O_{p,m} ⊆ O_{n,m}` modulo `LeftGradingResidual`.**
`∀ g ∈ OnmFull W p m, anmGen W n m p a g ∈ OnmFull W n m`. -/
theorem anmGen_OnmFull_left_of_leftGrading (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (a : 𝒱)
    (hgrad : LeftGradingResidual W n m p) :
    ∀ g ∈ OnmFull W p m, anmGen W n m p a g ∈ OnmFull W n m :=
  anmGen_OnmFull_left W n m p a (dj28Residual_of_leftGrading W n m p hgrad)

/-! ## DJ Lemma 2.8 "in particular" — the headline specializations. -/

/-- **DJ Lemma 2.8 "in particular": `V ∗̄ⁿ_m O_{n,m} ⊆ O_{n,m}`** (left action `∗̄ⁿ_m`, `p = n`),
modulo `LeftGradingResidual W n m n`. -/
theorem anmGenBar_OnmFull_of_leftGrading (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (a : 𝒱)
    (hgrad : LeftGradingResidual W n m n) :
    ∀ g ∈ OnmFull W n m, anmGenBar W n m a g ∈ OnmFull W n m := by
  intro g hg
  rw [anmGenBar]
  exact anmGen_OnmFull_left_of_leftGrading W n m n a hgrad g hg

/-- **DJ Lemma 2.8 "in particular": `O_{n,m} ∗ⁿ_m V ⊆ O_{n,m}`** (right action `∗ⁿ_m`, `p = m`) —
**fully unconditional** (the right inclusion needs no `LeftGradingResidual`). -/
theorem anmRight_OnmFull_unconditional (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (v : 𝒱) :
    ∀ g ∈ OnmFull W n m, anmRight W n m g v ∈ OnmFull W n m := by
  intro g hg
  rw [← anmGen_eq_anmRight]
  exact anmGen_OnmFull_right_unconditional W n m m v g hg

end VOA
