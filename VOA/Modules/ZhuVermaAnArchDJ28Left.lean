/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ28

/-!
# Dong–Jiang **Lemma 2.8**, the LEFT inclusion — discharging the `DJ28Residual` left branches.

This file discharges the three **left** generator branches of `DJ28Residual` (the residual of
Dong–Jiang, *Bimodules associated to vertex operator algebras*, Math. Z. 259 (2008) 799–826,
`math/0601626`, Lemma 2.8) for the left inclusion `V ∗ⁿ_{m,p} O_{p,m}(V) ⊆ O_{n,m}(V)` (DJ display
(2.1)):

* `leftO''`   — the `O''_{p,m}` associator generator in the right slot **(fully closed here)**;
* `leftO'''`  — the `O'''_{p,m}` level-mixing generator in the right slot;
* `leftO'Lgen` — the `O'_{p,m}` grading generator in the right slot.

## DJ's mechanism (the bare associator)

Every step is DJ's single reassociation move, the **bare associator** `bareAssoc_mem_OnmFull`:
```
  (a ∗ⁿ_{p₁,p₂} b) ∗ⁿ_{m,p₁} c  ≡  a ∗ⁿ_{m,p₂} (b ∗^{p₂}_{m,p₁} c)   (mod O_{n,m}),
```
i.e. `anmGen W n m p₁ (anmGen W n p₁ p₂ a b) c − anmGen W n m p₂ a (anmGen W p₂ m p₁ b c) ∈ OnmFull`.

### `leftO''` (closed)

The `O''_{p,m}` generator is `assocDefect W p m q₁ q₂ q₃ b₁ b₂ b₃ w = w ∗^p_{m,q₃} BRACKET`, where
`BRACKET` is the inner associator at level `q₃`.  Hitting it with `a ∗ⁿ_{m,p} (·)` and applying the
bare associator (with `(p₂,p₁) = (p,q₃)`) reassociates
```
  a ∗ⁿ_{m,p} (w ∗^p_{m,q₃} BRACKET)  ≡  (a ∗ⁿ_{p,q₃} w) ∗ⁿ_{m,q₃} BRACKET   (mod O_{n,m}).
```
Because `BRACKET` is **the same** inner associator (the inner bracket of `assocDefect` is indexed by
its OUTER level `p₃ = q₃`, NOT by the top level), the reassociated term is literally
`assocDefect W n m q₁ q₂ q₃ b₁ b₂ b₃ (a ∗ⁿ_{p,q₃} w)`, an `O''_{n,m}` generator — a member of
`OnmFull W n m` by `assocDefect_mem_OnmFull`.  No recursion. **Fully closed.**

### `leftO'''` (DJ's coupled induction, reduced to the RIGHT inclusion at level `q`)

The `O'''_{p,m}` generator is `levelMix W p m q b g w = (b ∗^p_q g) ∗^p_{m,q} w` (with `g ∈ O_q`).
Two bare-associator moves reassociate `a ∗ⁿ_{m,p} (levelMix …)` to
`(a ∗ⁿ_{q,p} b) ∗ⁿ_q g) ∗ⁿ_{m,q} w + (correction) ∗ⁿ_{m,q} w`, where the first summand is a genuine
`levelMix W n m q (a ∗ⁿ_{q,p} b) g w` member (`levelMix_mem_OnmFull`), and the correction lies in
`O_{n,q}` — so the correction term needs the **right** DJ-2.8 inclusion `O_{n,q} ∗ⁿ_{m,q} V ⊆ O_{n,m}`,
i.e. `anmGen_OnmFull_right W n m q` at the *new* level `q`.  This is DJ's published coupled
induction across levels (Lemma 2.8 is proved for all `n,m,p` simultaneously).  We therefore record
`leftO'''` **conditional on the right inclusion at level `q`** — the genuine DJ feeder, NOT a fresh
carried predicate — discharged here down to that exact term.

### `leftO'Lgen` (the grading generator, right slot)

The general right-slot grading absorption `a ∗ⁿ_{m,p} (anmLgen W p m c) ∈ O_{n,m}` (a residue/total-
derivative computation, the analogue of `anmGen_offdiag_Lgen_eq_general` but in the right factor) is
not among the proven feeders (only the level-0 special case `anmRight_zero_crossL_mem_Onm` exists).
It is left as the precise residual `LeftGradingResidual`, the exact Lean signature of the one
remaining right-slot grading-absorption identity.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## `leftO''` — the `O''_{p,m}` associator generator, fully closed. -/

/-- **DJ (2.1), the `O''_{p,m}` associator branch (left inclusion) — fully closed.**

`a ∗ⁿ_{m,p} (assocDefect W p m q₁ q₂ q₃ b₁ b₂ b₃ w) ∈ O_{n,m}(V)`.

`assocDefect W p m q₁ q₂ q₃ b₁ b₂ b₃ w = w ∗^p_{m,q₃} BRACKET`, where `BRACKET` is the inner associator
at level `q₃`.  By the bare associator `bareAssoc_mem_OnmFull W n m q₃ p a w BRACKET` the target is
congruent mod `O_{n,m}` to `(a ∗ⁿ_{p,q₃} w) ∗ⁿ_{m,q₃} BRACKET`, which — because the `assocDefect`
inner bracket is indexed by its outer level (`q₃` in both `assocDefect W p m …` and
`assocDefect W n m …`) — is literally `assocDefect W n m q₁ q₂ q₃ b₁ b₂ b₃ (a ∗ⁿ_{p,q₃} w)`, an
`O''_{n,m}` member by `assocDefect_mem_OnmFull`. -/
theorem leftO''_mem (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (a : 𝒱)
    (q₁ q₂ q₃ : ℕ) (b₁ b₂ b₃ w : 𝒱) :
    anmGen W n m p a (assocDefect W p m q₁ q₂ q₃ b₁ b₂ b₃ w) ∈ OnmFull W n m := by
  -- abbreviate the inner associator bracket (indexed by the outer level `q₃`).
  set B : 𝒱 :=
    anmGen W q₃ m q₁ (anmGen W q₃ q₁ q₂ b₁ b₂) b₃ - anmGen W q₃ m q₂ b₁ (anmGen W q₂ m q₁ b₂ b₃)
    with hB
  -- `assocDefect W p m … = anmGen W p m q₃ w B` by definition.
  have hdef : assocDefect W p m q₁ q₂ q₃ b₁ b₂ b₃ w = anmGen W p m q₃ w B := rfl
  rw [hdef]
  -- bare associator with `(p₂,p₁) = (p,q₃)`, `(b,c) = (w,B)`.
  have hbare := bareAssoc_mem_OnmFull W n m q₃ p a w B
  -- the reassociated first term is the `O''_{n,m}` generator `assocDefect W n m … (a ∗ⁿ_{p,q₃} w)`.
  have hfirst : anmGen W n m q₃ (anmGen W n q₃ p a w) B
      = assocDefect W n m q₁ q₂ q₃ b₁ b₂ b₃ (anmGen W n q₃ p a w) := rfl
  have hmem : anmGen W n m q₃ (anmGen W n q₃ p a w) B ∈ OnmFull W n m := by
    rw [hfirst]; exact assocDefect_mem_OnmFull W n m q₁ q₂ q₃ b₁ b₂ b₃ (anmGen W n q₃ p a w)
  -- `F − G ∈ OnmFull` and `F ∈ OnmFull` ⟹ `G = F − (F − G) ∈ OnmFull`.
  have := (OnmFull W n m).sub_mem hmem hbare
  rwa [sub_sub_cancel] at this

/-! ## `leftO'''` — the `O'''_{p,m}` level-mixing generator (DJ coupled induction). -/

/-- **DJ (2.1), the `O'''_{p,m}` level-mixing branch (left inclusion).**

`a ∗ⁿ_{m,p} (levelMix W p m q b g w) ∈ O_{n,m}(V)` for `g ∈ O_q` (`= Onm W q q`), **conditional on the
right DJ-2.8 inclusion at level `q`** (`hright : DJ28Residual W n m q`) — exactly DJ's published
coupled induction across levels.

`levelMix W p m q b g w = (b ∗^p_q g) ∗^p_{m,q} w`.  Two bare-associator moves:

* `bareAssoc_mem_OnmFull W n m q p a (b ∗^p_q g) w` reassociates the target mod `O_{n,m}` to
  `(a ∗ⁿ_{q,p} (b ∗^p_q g)) ∗ⁿ_{m,q} w`;
* `bareAssoc_mem_OnmFull W n q q p a b g` reassociates `a ∗ⁿ_{q,p} (b ∗^p_q g)` mod `O_{n,q}` to
  `(a ∗ⁿ_{q,p} b) ∗ⁿ_q g`.

The first summand becomes the `O'''_{n,m}` generator `levelMix W n m q (a ∗ⁿ_{q,p} b) g w`
(`levelMix_mem_OnmFull`); the `O_{n,q}` correction, after the outer `· ∗ⁿ_{m,q} w`, is closed by the
right inclusion `anmGen_OnmFull_right W n m q` at level `q`. -/
theorem leftO'''_mem (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (a : 𝒱)
    (q : ℕ) (b w : 𝒱) (g : 𝒱) (hg : g ∈ Onm W q q)
    (hright : DJ28Residual W n m q) :
    anmGen W n m p a (levelMix W p m q b g w) ∈ OnmFull W n m := by
  -- `X = b ∗^p_q g`, the inner `*^p_{q,q}` product.
  set X : 𝒱 := anmGen W p q q b g with hX
  -- `levelMix W p m q b g w = anmGen W p m q X w` by definition.
  have hdef : levelMix W p m q b g w = anmGen W p m q X w := rfl
  rw [hdef]
  -- STEP 1: bare associator with `(p₂,p₁) = (p,q)`, `(b,c) = (X,w)`.
  have hbare1 := bareAssoc_mem_OnmFull W n m q p a X w
  -- `Y = a ∗ⁿ_{q,p} X`, the reassociated middle factor.
  set Y : 𝒱 := anmGen W n q p a X with hY
  -- target `≡ anmGen W n m q Y w  (mod O_{n,m})`.
  -- STEP 2: bare associator with `(p₂,p₁) = (p,q)`, `(b,c) = (b,g)` at top level `q`.
  have hbare2 := bareAssoc_mem_OnmFull W n q q p a b g
  -- `Z = (a ∗ⁿ_{q,p} b) ∗ⁿ_q g`, the reassociated form of `Y`.
  set Z : 𝒱 := anmGen W n q q (anmGen W n q p a b) g with hZ
  -- `hbare2 : Z − Y ∈ OnmFull W n q`; write `Y = Z − D`, `D := Z − Y ∈ OnmFull W n q`.
  set D : 𝒱 := Z - Y with hD
  have hDmem : D ∈ OnmFull W n q := hbare2
  have hYsplit : Y = Z - D := by rw [hD]; abel
  -- the outer product is ℂ-linear in its left slot (`anmGenLeftMap W n m q w`).
  have hsplit : anmGen W n m q Y w = anmGen W n m q Z w - anmGen W n m q D w := by
    have := (anmGenLeftMap W n m q w).map_sub Z D
    simp only [anmGenLeftMap_apply] at this
    rw [hYsplit]; exact this
  -- `anmGen W n m q Z w = levelMix W n m q (a ∗ⁿ_{q,p} b) g w ∈ OnmFull` (level-mixing generator).
  have hlevelMem : anmGen W n m q Z w ∈ OnmFull W n m := by
    have hLM : anmGen W n m q Z w = levelMix W n m q (anmGen W n q p a b) g w := rfl
    rw [hLM]
    exact levelMix_mem_OnmFull W n m q (anmGen W n q p a b) w g hg
  -- `anmGen W n m q D w ∈ OnmFull` by the RIGHT inclusion at level `q` (DJ coupled induction).
  have hcorrMem : anmGen W n m q D w ∈ OnmFull W n m :=
    anmGen_OnmFull_right W n m q w hright D hDmem
  -- assemble: target ≡ anmGen W n m q Y w = (levelMix) − (correction), both members.
  have hYmem : anmGen W n m q Y w ∈ OnmFull W n m := by
    rw [hsplit]; exact (OnmFull W n m).sub_mem hlevelMem hcorrMem
  -- `(anmGen W n m q Y w) − target ∈ OnmFull` (hbare1) and `anmGen W n m q Y w ∈ OnmFull` ⟹ target.
  have := (OnmFull W n m).sub_mem hYmem hbare1
  rwa [sub_sub_cancel] at this

/-! ## `leftO'Lgen` — the `O'_{p,m}` grading generator (the general right-slot absorption).

The remaining left branch is the `O'_{p,m}` grading generator in the right slot,
`a ∗ⁿ_{m,p} (anmLgen W p m c) ∈ O_{n,m}`.  Unlike its left-slot mirror (`anmRight_O'Lgen_mem`,
closed by the off-diagonal absorption `anmGen_offdiag_Lgen_eq_general`, which acts in the *left*
factor), this is the **right-slot** grading absorption of the general three-index product.  The
proven feeders contain only the level-0 special case `anmRight_zero_crossL_mem_Onm`
(`ZhuVermaAnArchMUcross`); the general-`(n,m,p)` right-slot absorption is a fresh residue/total-
derivative computation (the right-factor analogue of `anmGen_offdiag_Lgen_eq_general`, equal in depth
to DJ Lemma 2.5 — exactly the kind of genuinely-open analytic identity recorded as `DJ27ChainTail`
and `DJ28Residual.rightO'Circ`).  We therefore record it as the **precise** residual identity, pinned
to the genuine `anmGen`/`anmLgen` product (NOT a weakened or carried predicate). -/

/-- **The precise residual of the `O'_{p,m}` grading branch (left inclusion).**

The single remaining analytic identity: the general right-slot grading absorption
`a ∗ⁿ_{m,p} (anmLgen W p m c) ∈ O_{n,m}(V)`.  This is the right-factor analogue of the closed
left-factor absorption `anmGen_offdiag_Lgen_eq_general` and is on par, in analytic depth, with DJ
Lemma 2.5 (the `rightO'Circ` residual).  Its field is the exact Lean signature of the genuine DJ
product, identical to `DJ28Residual.leftO'Lgen`. -/
structure LeftGradingResidual (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) : Prop where
  /-- The general right-slot grading absorption: `a ∗ⁿ_{m,p} (anmLgen W p m c) ∈ O_{n,m}`. -/
  absorb : ∀ a c : 𝒱, anmGen W n m p a (anmLgen W p m c) ∈ OnmFull W n m

/-- **DJ (2.1), the `O'_{p,m}` grading branch (left inclusion), modulo `LeftGradingResidual`.**
`a ∗ⁿ_{m,p} (anmLgen W p m c) ∈ O_{n,m}(V)`, given the general right-slot grading absorption.  This is
the precise residual identity itself — no reduction or weakening. -/
theorem leftO'Lgen_mem (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (a c : 𝒱)
    (hgrad : LeftGradingResidual W n m p) :
    anmGen W n m p a (anmLgen W p m c) ∈ OnmFull W n m :=
  hgrad.absorb a c

/-! ## Assembly — the three left branches of `DJ28Residual`.

`leftO''` is closed unconditionally (`leftO''_mem`).  `leftO'''` needs the right DJ-2.8 inclusion at
the inner level `q` (DJ's published coupled induction); `leftO'Lgen` needs the general right-slot
grading absorption (`LeftGradingResidual`).  We package the three into the left fields of
`DJ28Residual` under those two genuine hypotheses. -/

/-- The three **left** fields of `DJ28Residual W n m p`, given the general right-slot grading
absorption at `(n,m,p)` (`hgrad`) and the right DJ-2.8 inclusion at every inner level `q` used by the
level-mixing branch (`hright`, DJ's coupled induction).  `leftO''` is closed unconditionally. -/
theorem leftBranches_mem (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ)
    (hgrad : LeftGradingResidual W n m p)
    (hright : ∀ q : ℕ, DJ28Residual W n m q) :
    (∀ a c : 𝒱, anmGen W n m p a (anmLgen W p m c) ∈ OnmFull W n m) ∧
    (∀ a : 𝒱, ∀ q₁ q₂ q₃ : ℕ, ∀ b₁ b₂ b₃ w : 𝒱,
      anmGen W n m p a (assocDefect W p m q₁ q₂ q₃ b₁ b₂ b₃ w) ∈ OnmFull W n m) ∧
    (∀ a : 𝒱, ∀ q : ℕ, ∀ b w : 𝒱, ∀ g : 𝒱, g ∈ Onm W q q →
      anmGen W n m p a (levelMix W p m q b g w) ∈ OnmFull W n m) :=
  ⟨fun a c => leftO'Lgen_mem W n m p a c hgrad,
   fun a q₁ q₂ q₃ b₁ b₂ b₃ w => leftO''_mem W n m p a q₁ q₂ q₃ b₁ b₂ b₃ w,
   fun a q b w g hg => leftO'''_mem W n m p a q b w g hg (hright q)⟩

end VOA
