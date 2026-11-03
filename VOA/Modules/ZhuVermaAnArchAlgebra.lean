/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArch

/-!
# The `A_n(𝒱)` quotient algebra structure, CONDITIONAL on `AnIdeal W n`.

Building on the corrected ideal architecture of `ZhuVermaAnArch.lean`, this file constructs, from a
single hypothesis `h : AnIdeal W n` (the Dong–Li–Mason 2-sided ideal `OnFull W n` under the FZ product
`leftProd = *ₙ`), the **quotient `A_n(𝒱) = 𝒱 / O_n(𝒱)`** together with its **well-defined bilinear
product** `[a] · [x] = [a *ₙ x]`.

## What is proved here (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `AnFull W n := 𝒱 ⧸ OnFull W n` (the corrected quotient, ℂ-module via `Submodule.Quotient`),
  `mkAnFull` the quotient map.
* `AnFull.mulAux h x` — for fixed left factor `x`, the right-slot descent `[b] ↦ [x *ₙ b]` as
  `AnFull →ₗ AnFull` (well-defined by `h.right`, via `OnFull.mapQ`).
* `AnFull.mulHom h` — `x ↦ AnFull.mulAux h x` bundled as `𝒱 →ₗ (AnFull →ₗ AnFull)` (linear in `x`).
* `AnFull.mul h` — the **descended bilinear product** `AnFull →ₗ AnFull →ₗ AnFull` (the left slot is
  descended through `AnFull = 𝒱/OnFull` using `h.left`, i.e. `OnFull ≤ ker`).
* `AnFull.mul_mk` — the **representative-evaluation lemma** `[a] · [x] = [a *ₙ x]`
  (`AnFull.mul h (mkAnFull a) (mkAnFull x) = mkAnFull (leftProd W n a x)`).

These are genuine, results: a fully well-defined (in both slots) ℂ-bilinear product on the
corrected quotient `A_n(𝒱)`, conditional only on the boss-approved `AnIdeal W n`.

## What is OPEN (precise, NOT faked)

* **Associativity** `([a]·[b])·[c] = [a]·([b]·[c])`.  This is the Frenkel–Zhu associator identity
  (Dong–Li–Mason Lemma 2.1 / Thm 2.4): `(a *ₙ b) *ₙ c - a *ₙ (b *ₙ c) ∈ O_n`.  It requires the FZ
  iterate/associator combinatorics (the depth-`n` analogue of Zhu's `n=0` associativity), which is
  NOT available among the imported lemmas.  Stated as the precise open `AnFull.AssocLaw` below
  (a `Prop`, NOT an axiom, NOT a `sorry`).
* **Identity `[𝟙]`** (the vacuum class is a two-sided unit) — likewise needs the FZ unit identities
  `𝟙 *ₙ a ≡ a` and `a *ₙ 𝟙 ≡ a (mod O_n)`, not available here; stated as `AnFull.LeftUnitLaw` /
  `AnFull.RightUnitLaw`.
* **The filtration/surjection `OnFull W n ≤ OnFull W 0`** (⟹ `A_n(𝒱) ↠ A_0(𝒱) = A(𝒱)`).  This is
  FALSE as a plain submodule inclusion in the *other* direction and even in this direction is NOT
  provable from the imported lemmas: it needs `circ W n c d ∈ OnFull W 0` for the level-`n` circle
  generators (a `2(n)`-vs-`0` pole-order shift identity, the level-lowering part of DLM Prop. 2.4),
  which is exactly the kind of higher-pole-residue content that is not proved.  See the precise
  statement `AnFull.SurjData` and the discussion below; reported as a blocker, NOT faked.

## References
Dong–Li–Mason, J. Algebra 206 (1998) 67–96 (`q-alg/9612010`), Lemmas 2.1–2.2, Thm 2.4;
Frenkel–Zhu, Duke 66 (1992); Zhu, J. AMS 9 (1996); Gannon §5.3.2 Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The corrected quotient `A_n(𝒱) = 𝒱 / O_n(𝒱)`. -/

/-- **`AnFull W n := 𝒱 ⧸ OnFull W n`** — the corrected `A_n(𝒱)` underlying ℂ-module (the quotient by
the Dong–Li–Mason `O_n = span{u ∘ₙ v} + {(L(-1)+L(0))u}`, NOT the circle-only `On W n`). -/
abbrev AnFull (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Type u := 𝒱 ⧸ OnFull W n

/-- The quotient map `𝒱 →ₗ A_n(𝒱)` onto the corrected quotient. -/
def mkAnFull (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : 𝒱 →ₗ[ℂ] AnFull W n := (OnFull W n).mkQ

@[simp] theorem mkAnFull_apply (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (x : 𝒱) :
    mkAnFull W n x = Submodule.Quotient.mk x := rfl

/-! ## The descended FZ product on `A_n(𝒱)`, conditional on `AnIdeal W n`. -/

section Product

variable (W : VertexOperatorAlgebra 𝒱) (n : ℕ)

/-- For a fixed left factor `x`, the right-slot descent `[b] ↦ [x *ₙ b]` as `AnFull →ₗ AnFull`.
Well-defined by `h.right` (`𝒱 *ₙ O_n ⊆ O_n`, the RIGHT ideal): the second-slot linear map
`leftProdR W n x` maps `OnFull` into `OnFull`, so it descends via `Submodule.mapQ`. -/
noncomputable def AnFull.mulAux (h : AnIdeal W n) (x : 𝒱) : AnFull W n →ₗ[ℂ] AnFull W n :=
  (OnFull W n).mapQ (OnFull W n) (leftProdR W n x) (by
    intro b hb
    rw [Submodule.mem_comap, leftProdR_apply]
    exact h.right x b hb)

@[simp] theorem AnFull.mulAux_mk (h : AnIdeal W n) (x b : 𝒱) :
    AnFull.mulAux W n h x (mkAnFull W n b) = mkAnFull W n (leftProd W n x b) := rfl

/-- `x ↦ AnFull.mulAux x` bundled as a linear map `𝒱 →ₗ (A_n →ₗ A_n)` (linear in the left factor `x`). -/
noncomputable def AnFull.mulHom (h : AnIdeal W n) : 𝒱 →ₗ[ℂ] AnFull W n →ₗ[ℂ] AnFull W n where
  toFun := AnFull.mulAux W n h
  map_add' x₁ x₂ := by
    refine LinearMap.ext fun y => ?_
    refine Submodule.Quotient.induction_on _ y fun b => ?_
    simp only [LinearMap.add_apply]
    rw [show (Submodule.Quotient.mk b : AnFull W n) = mkAnFull W n b from rfl,
      AnFull.mulAux_mk, AnFull.mulAux_mk, AnFull.mulAux_mk, leftProd_add_left, map_add]
  map_smul' c x := by
    refine LinearMap.ext fun y => ?_
    refine Submodule.Quotient.induction_on _ y fun b => ?_
    simp only [LinearMap.smul_apply, RingHom.id_apply]
    rw [show (Submodule.Quotient.mk b : AnFull W n) = mkAnFull W n b from rfl,
      AnFull.mulAux_mk, AnFull.mulAux_mk, leftProd_smul_left, map_smul]

@[simp] theorem AnFull.mulHom_apply (h : AnIdeal W n) (x b : 𝒱) :
    AnFull.mulHom W n h x (mkAnFull W n b) = mkAnFull W n (leftProd W n x b) :=
  AnFull.mulAux_mk W n h x b

/-- **The descended FZ product on `A_n(𝒱)`** `A_n →ₗ A_n →ₗ A_n`, `([a], [x]) ↦ [a *ₙ x]`.
The right (`A_n`) slot is descended via `h.right` (inside `AnFull.mulAux`); the left (`A_n`) slot is
descended here through `A_n = 𝒱/O_n` via `h.left` (`O_n *ₙ 𝒱 ⊆ O_n`, so `OnFull ≤ ker`). -/
noncomputable def AnFull.mul (h : AnIdeal W n) : AnFull W n →ₗ[ℂ] AnFull W n →ₗ[ℂ] AnFull W n :=
  (OnFull W n).liftQ (AnFull.mulHom W n h) (by
    intro g hg
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun y => ?_
    refine Submodule.Quotient.induction_on _ y fun b => ?_
    change AnFull.mulHom W n h g (mkAnFull W n b) = (0 : AnFull W n →ₗ[ℂ] AnFull W n) (mkAnFull W n b)
    rw [AnFull.mulHom_apply, LinearMap.zero_apply]
    -- `g ∈ OnFull` ⟹ `g *ₙ b ∈ OnFull` (left ideal `h.left`), so its class is `0`.
    rw [mkAnFull_apply, Submodule.Quotient.mk_eq_zero]
    exact h.left g hg b)

/-- **Representative-evaluation lemma** `[a] · [x] = [a *ₙ x]`. -/
@[simp] theorem AnFull.mul_mk (h : AnIdeal W n) (a x : 𝒱) :
    AnFull.mul W n h (mkAnFull W n a) (mkAnFull W n x) = mkAnFull W n (leftProd W n a x) :=
  AnFull.mulAux_mk W n h a x

end Product

/-! ## The OPEN laws (associativity, units, surjection) — stated precisely as `Prop`s, NOT axioms. -/

section OpenLaws

variable (W : VertexOperatorAlgebra 𝒱) (n : ℕ)

/-- **(OPEN, associativity)** The Frenkel–Zhu associator identity for the descended product:
`([a]·[b])·[c] = [a]·([b]·[c])` for all classes.  Equivalently (DLM Lemma 2.1)
`(a *ₙ b) *ₙ c - a *ₙ (b *ₙ c) ∈ O_n`.  Needs the FZ iterate/associator combinatorics (depth-`n`
analogue of Zhu's `n = 0` associativity); NOT available among the imported lemmas. -/
def AnFull.AssocLaw (h : AnIdeal W n) : Prop :=
  ∀ p q r : AnFull W n,
    AnFull.mul W n h (AnFull.mul W n h p q) r = AnFull.mul W n h p (AnFull.mul W n h q r)

/-- **(OPEN, left unit)** The vacuum class `[𝟙]` is a left unit: `[𝟙] · [a] = [a]`, i.e.
`𝟙 *ₙ a ≡ a (mod O_n)`.  Needs the FZ left-unit identity; NOT available here. -/
def AnFull.LeftUnitLaw (h : AnIdeal W n) : Prop :=
  ∀ a : 𝒱, AnFull.mul W n h (mkAnFull W n W.vacuum) (mkAnFull W n a) = mkAnFull W n a

/-- **(OPEN, right unit)** The vacuum class `[𝟙]` is a right unit: `[a] · [𝟙] = [a]`, i.e.
`a *ₙ 𝟙 ≡ a (mod O_n)`.  Needs the FZ right-unit identity; NOT available here. -/
def AnFull.RightUnitLaw (h : AnIdeal W n) : Prop :=
  ∀ a : 𝒱, AnFull.mul W n h (mkAnFull W n a) (mkAnFull W n W.vacuum) = mkAnFull W n a

/-- **(OPEN, surjection data)** The level-lowering filtration `O_n(𝒱) ⊆ O_0(𝒱)` that induces the
surjection `A_n(𝒱) ↠ A_0(𝒱) = A(𝒱)` (DLM Prop. 2.4).  NOT provable from the imported lemmas: it
needs `circ W n c d ∈ OnFull W 0` for the level-`n` circle generators (a `2n`-vs-`0` pole-order shift),
which is unbanked higher-pole-residue content.  (`OnL W` already lands in `OnFull W 0` —
`OnL_le_OnFull` — so only the `On W n ≤ OnFull W 0` part is the genuine blocker.) -/
def AnFull.SurjData : Prop := OnFull W n ≤ OnFull W 0

end OpenLaws

/-! ## Conditional consequences of the OPEN laws (proved: if you discharge a law, the structure follows).

These show the laws are *exactly* what is needed — each is a clean green theorem turning the open
`Prop` into the corresponding algebraic fact, so discharging the FZ combinatorics later flips them
unconditionally with zero extra wiring. -/

section Consequences

variable (W : VertexOperatorAlgebra 𝒱) (n : ℕ)

/-- Given the associativity law, the product is associative on representatives:
`[a *ₙ b] · [c] = [a] · [b *ₙ c]`.  (Immediate from `AssocLaw` + `mul_mk`; proves the reduction.) -/
theorem AnFull.assoc_repr (h : AnIdeal W n) (hassoc : AnFull.AssocLaw W n h) (a b c : 𝒱) :
    AnFull.mul W n h (mkAnFull W n (leftProd W n a b)) (mkAnFull W n c)
      = AnFull.mul W n h (mkAnFull W n a) (mkAnFull W n (leftProd W n b c)) := by
  have := hassoc (mkAnFull W n a) (mkAnFull W n b) (mkAnFull W n c)
  rwa [AnFull.mul_mk, AnFull.mul_mk] at this

/-- Given the left-unit law on the vacuum, `[𝟙] · [a] = [a]` for representatives. -/
theorem AnFull.left_unit_repr (h : AnIdeal W n) (hunit : AnFull.LeftUnitLaw W n h) (a : 𝒱) :
    mkAnFull W n (leftProd W n W.vacuum a) = mkAnFull W n a := by
  have := hunit a
  rwa [AnFull.mul_mk] at this

/-- Given the right-unit law on the vacuum, `[a] · [𝟙] = [a]` for representatives. -/
theorem AnFull.right_unit_repr (h : AnIdeal W n) (hunit : AnFull.RightUnitLaw W n h) (a : 𝒱) :
    mkAnFull W n (leftProd W n a W.vacuum) = mkAnFull W n a := by
  have := hunit a
  rwa [AnFull.mul_mk] at this

/-- Given the surjection data `O_n ⊆ O_0`, the level-lowering quotient map
`A_n(𝒱) →ₗ A_0(𝒱)`, `[a]_n ↦ [a]_0`, is a well-defined ℂ-linear **surjection**. -/
noncomputable def AnFull.surj (hsurj : AnFull.SurjData W n) : AnFull W n →ₗ[ℂ] AnFull W 0 :=
  (OnFull W n).liftQ (mkAnFull W 0) (by
    intro g hg
    rw [LinearMap.mem_ker, mkAnFull_apply, Submodule.Quotient.mk_eq_zero]
    exact hsurj hg)

@[simp] theorem AnFull.surj_mk (hsurj : AnFull.SurjData W n) (a : 𝒱) :
    AnFull.surj W n hsurj (mkAnFull W n a) = mkAnFull W 0 a := rfl

theorem AnFull.surj_surjective (hsurj : AnFull.SurjData W n) :
    Function.Surjective (AnFull.surj W n hsurj) := by
  intro y
  refine Submodule.Quotient.induction_on _ y fun a => ?_
  exact ⟨mkAnFull W n a, by rw [show (Submodule.Quotient.mk a : AnFull W 0) = mkAnFull W 0 a from rfl,
    ← AnFull.surj_mk W n hsurj a]⟩

end Consequences

/-!
## Status

**Axiom-clean (`[propext, Classical.choice, Quot.sound]`):**
* `AnFull`/`mkAnFull` — the corrected quotient `A_n(𝒱) = 𝒱/O_n(𝒱)` and its quotient map.
* `AnFull.mulAux`/`mulHom`/`mul`/`mul_mk` — the **fully well-defined ℂ-bilinear FZ product** on
  `A_n(𝒱)`, conditional ONLY on `h : AnIdeal W n` (well-defined in BOTH slots: right slot via
  `h.right`, left slot via `h.left`).  `mul_mk` is the representative-evaluation lemma `[a]·[x]=[a*ₙx]`.
* `AnFull.assoc_repr`, `left_unit_repr`, `right_unit_repr` — clean reductions of the open laws to
  representative identities.
* `AnFull.surj`/`surj_mk`/`surj_surjective` — the level-lowering surjection `A_n ↠ A_0`, conditional
  on the filtration `AnFull.SurjData` (`O_n ≤ O_0`).

**OPEN (stated precisely as `Prop`s; NOT `sorry`, NOT axioms):**
* `AnFull.AssocLaw` — associativity (FZ associator `(a*ₙb)*ₙc - a*ₙ(b*ₙc) ∈ O_n`, DLM Lemma 2.1);
  the FZ iterate/associator combinatorics are not among the imported lemmas.
* `AnFull.LeftUnitLaw`/`RightUnitLaw` — `[𝟙]` is a two-sided unit (FZ unit identities).
* `AnFull.SurjData` (`O_n ≤ O_0`) — the genuine blocker is `On W n ≤ OnFull W 0`, i.e.
  `circ W n c d ∈ OnFull W 0` for the level-`n` circle generators (a `2n`-vs-`0` pole-order shift,
  DLM Prop. 2.4); unbanked higher-pole-residue content.  (`OnL W ≤ OnFull W 0` already holds via
  `OnL_le_OnFull`, so the `OnL` half is free.)
-/

end VOA
