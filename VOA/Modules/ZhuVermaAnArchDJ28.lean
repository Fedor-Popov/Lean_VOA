/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAnmFull
import VOA.Modules.ZhuVermaAnArchAnm
import VOA.Modules.ZhuVermaAnArchDJ22
import VOA.Modules.ZhuVermaAnArchDJ27

/-!
# Dong–Jiang **Lemma 2.8** — the bimodule ideal-closure (into the FULL ideal `O_{n,m}`)

This file assembles Dong–Jiang, *Bimodules associated to vertex operator algebras*,
Math. Z. 259 (2008) 799–826 (`math/0601626`), **Lemma 2.8** — the headline ideal-closure lemma — into
the genuine full Dong–Jiang ideal `OnmFull W n m = O'_{n,m} ⊔ O''_{n,m} ⊔ O'''_{n,m}` (the prime,
associator, and level-mixing summands).

DJ Lemma 2.8 (verbatim): *For any `m, n, p ∈ ℤ₊`,*
```
  V ∗ⁿ_{m,p} O_{p,m}(V) ⊆ O_{n,m}(V),      O_{n,p}(V) ∗ⁿ_{m,p} V ⊆ O_{n,m}(V).
```
*In particular,* `V ∗̄ⁿ_m O_{n,m}(V) ⊆ O_{n,m}(V)`, `O_{n,m}(V) ∗ⁿ_m V ⊆ O_{n,m}(V)`.

In the repo `OnmFull`/`anmGen` infrastructure these are
```
  anmGen_OnmFull_left  : ∀ g ∈ OnmFull W p m, anmGen W n m p a g ∈ OnmFull W n m
  anmGen_OnmFull_right : ∀ g ∈ OnmFull W n p, anmGen W n m p g v ∈ OnmFull W n m
```
and the two "in particular" specializations (`p = n` left, `p = m` right):
```
  anmGenBar_OnmFull : ∀ g ∈ OnmFull W n m, anmGenBar W n m a g ∈ OnmFull W n m
  anmRight_OnmFull  : ∀ g ∈ OnmFull W n m, anmRight W n m g v ∈ OnmFull W n m
```
(`anmGenBar = anmGen W n m n`, `anmRight = anmGen W n m m`.)

## DJ's published proof (formalized faithfully here)

DJ p.9, lines 716–805.  *"By the definition of `O_{n,m}(V)` and Lemma 2.7, it suffices to prove
(2.1) `V ∗ⁿ_{m,p}((V∗^p_{p₁}O_{p₁})∗^p_{m,p₁}V + O''_{p,m}) ⊆ O_{n,m}` and (2.2)
`((V∗^n_{p₁}O_{p₁})∗^n_{p,p₁}V + O''_{n,p})∗ⁿ_{m,p}V ⊆ O_{n,m}`."*  The `O'_{·}` summand is DJ
Lemma 2.7; what remains is the associator (`O''`) and level-mixing (`O'''`) summands, reassociated
(via the `u = 1` bare associator) to `0 (mod O_{n,m})`.

This file performs the **abstract span/membership assembly** verbatim: the `OnmFull` ideal is the
join of three spans (`Onm ⊔ OnmAssoc ⊔ OnmLevel`); the action map `anmGen W n m p · g` (resp.
`anmGen W n m p a ·`) is ℂ-linear, so `Submodule.mem_sup` + `span_le`/`comap` reduces the closure to
the closure on **each generator family**.  Of those families we discharge here, from the closed DJ
feeders, exactly:

* **O' grading generator, right action** — `anmGen W n m m (anmLgen W n m c) v` — by the off-diagonal
  absorption `anmGen_offdiag_Lgen_eq_general` (DJ Lemma 2.7 step a): collapses to a scalar multiple of
  the circle generator `anmCirc W n m c v ∈ Onm ⊆ OnmFull`.  **Fully closed.**
* **O' circle generator, left action** — `anmGen W n m n a (anmCirc W n m c d)` — by `circCross_mem`
  (DJ Lemma 2.2 + bare associator + `levelMix_mem_OnmFull`).  **Fully closed.**

The remaining generator families are DJ's own remaining content (the `O''`/`O'''` reassociations of
(2.1)/(2.2) and the `O'` circle-right / grading-left pieces that bottom out in DJ Lemma 2.5).  They
are collected — **with their exact Lean signatures, pinned to the genuine DJ products, not strengthened
or reduced to a fresh carried predicate** — into the residual structure `DJ28Residual`.  The four
headline theorems are then proved **modulo `DJ28Residual`** following DJ's published assembly.

## What is proved here (axiom-clean; NO `sorry`/`pbw`)

* `anmGenLeftMap`/`anmGenRightMap` — `anmGen W n m p · g` / `anmGen W n m p a ·` as ℂ-linear maps.
* `anmRight_O'Lgen_mem` / `anmGenBar_O'Circ_mem` — the two fully-closed O' generator branches.
* `DJ28Residual` — the precise residual structure (the genuinely-open DJ 2.8 generator families).
* `anmGen_OnmFull_left` / `anmGen_OnmFull_right` — DJ 2.8, both general inclusions, modulo
  `DJ28Residual`.
* `anmGenBar_OnmFull` / `anmRight_OnmFull` — DJ 2.8 "in particular" (the headline), modulo
  `DJ28Residual`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Dong–Li–Mason,
J. Algebra 206 (1998) 67–96.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The general product `*^n_{m,p}` as ℂ-linear maps in each slot. -/

/-- The left action `g ↦ g *^n_{m,p} v` as a ℂ-linear map (the *left-factor* slot). -/
noncomputable def anmGenLeftMap (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (v : 𝒱) :
    𝒱 →ₗ[ℂ] 𝒱 where
  toFun g := anmGen W n m p g v
  map_add' g₁ g₂ := anmGen_add_left W n m p g₁ g₂ v
  map_smul' c g := anmGen_smul_left W n m p c g v

@[simp] theorem anmGenLeftMap_apply (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (v g : 𝒱) :
    anmGenLeftMap W n m p v g = anmGen W n m p g v := rfl

/-- The right action `g ↦ a *^n_{m,p} g` as a ℂ-linear map (the *right-factor* slot). -/
noncomputable def anmGenRightMap (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (a : 𝒱) :
    𝒱 →ₗ[ℂ] 𝒱 where
  toFun g := anmGen W n m p a g
  map_add' g₁ g₂ := anmGen_add_right W n m p a g₁ g₂
  map_smul' c g := anmGen_smul_right W n m p c a g

@[simp] theorem anmGenRightMap_apply (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (a g : 𝒱) :
    anmGenRightMap W n m p a g = anmGen W n m p a g := rfl

/-! ## The two fully-closed `O'` generator branches (from the DJ feeders). -/

/-- **O' grading generator, right action (DJ 2.8, the `O'` part of (2.2), diagonal `p = m`).**
`anmGen W n m m (anmLgen W n m c) v = (anmRight W n m (anmLgen W n m c) v)` is a scalar multiple of the
circle generator `anmCirc W n m c v`, hence in `OnmFull`.  Via the off-diagonal absorption
`anmGen_offdiag_Lgen_eq_general` (DJ Lemma 2.7 step a) with `(p₂, p₁) = (n, m)`. -/
theorem anmRight_O'Lgen_mem (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (c v : 𝒱) :
    anmGen W n m m (anmLgen W n m c) v ∈ OnmFull W n m := by
  -- `anmLgen W n m c = L₋₁c + L₀c + (m−n)•c`; the off-diagonal absorption with `(p₂,p₁) = (n,m)`
  -- gives `anmGen W n m m (·) v = scalar • anmCirc W n m c v`.
  rw [show anmLgen W n m c = W.L (-1) c + W.L 0 c + ((m : ℂ) - (n : ℂ)) • c from rfl]
  rw [anmGen_offdiag_Lgen_eq_general W m m n c v]
  exact Submodule.smul_mem _ _ (anmCirc_mem_OnmFull W n m c v)

/-- **O' circle generator, left action (DJ 2.8, the `O'` part of (2.1), diagonal `p = n`).**
`anmGenBar W n m a (anmCirc W n m c d) = anmGen W n m n a (anmCirc W n m c d) ∈ OnmFull`.  This is
exactly `circCross_mem W n m n a d c` (DJ Lemma 2.2 + bare associator + `levelMix_mem_OnmFull`). -/
theorem anmGenBar_O'Circ_mem (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (a c d : 𝒱) :
    anmGen W n m n a (anmCirc W n m c d) ∈ OnmFull W n m :=
  circCross_mem W n m n a d c

/-! ## The DJ 2.8 residual structure — the genuinely-open generator families.

These are exactly DJ's own remaining sub-steps after Lemma 2.7 is consumed: the `O''`/`O'''`
reassociations of (2.1)/(2.2), and the two `O'` pieces that bottom out in DJ Lemma 2.5 (the
circle-generator under right action and the grading-generator under left action).  Each field is the
precise Lean signature of one DJ generator family; the products are the genuine DJ `anmGen` products,
NOT a weakened or carried predicate.  -/

/-- **The residual of DJ Lemma 2.8** (the generator families not discharged by the closed feeders).

For the **left inclusion** `V ∗ⁿ_{m,p} O_{p,m} ⊆ O_{n,m}` (DJ (2.1)) the open families are:
* `leftO'Lgen` — the `O'_{p,m}` grading generator in the right slot;
* `leftO''`   — the `O''_{p,m}` associator generator in the right slot;
* `leftO'''`  — the `O'''_{p,m}` level-mixing generator in the right slot.

For the **right inclusion** `O_{n,p} ∗ⁿ_{m,p} V ⊆ O_{n,m}` (DJ (2.2)) the open families are:
* `rightO'Circ` — the `O'_{n,p}` circle generator in the left slot (DJ Lemma 2.5);
* `rightO''`    — the `O''_{n,p}` associator generator in the left slot;
* `rightO'''`   — the `O'''_{n,p}` level-mixing generator in the left slot. -/
structure DJ28Residual (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) : Prop where
  /-- DJ (2.1), `O'_{p,m}` grading generator (right slot): `a ∗ⁿ_{m,p} (anmLgen W p m c) ∈ O_{n,m}`. -/
  leftO'Lgen : ∀ a c : 𝒱, anmGen W n m p a (anmLgen W p m c) ∈ OnmFull W n m
  /-- DJ (2.1), `O''_{p,m}` associator generator (right slot). -/
  leftO'' : ∀ a : 𝒱, ∀ q₁ q₂ q₃ : ℕ, ∀ b₁ b₂ b₃ w : 𝒱,
    anmGen W n m p a (assocDefect W p m q₁ q₂ q₃ b₁ b₂ b₃ w) ∈ OnmFull W n m
  /-- DJ (2.1), `O'''_{p,m}` level-mixing generator (right slot). -/
  leftO''' : ∀ a : 𝒱, ∀ q : ℕ, ∀ b w : 𝒱, ∀ g : 𝒱, g ∈ Onm W q q →
    anmGen W n m p a (levelMix W p m q b g w) ∈ OnmFull W n m
  /-- DJ (2.2), `O'_{n,p}` circle generator (left slot), DJ Lemma 2.5:
  `(anmCirc W n p c d) ∗ⁿ_{m,p} v ∈ O_{n,m}`. -/
  rightO'Circ : ∀ c d v : 𝒱, anmGen W n m p (anmCirc W n p c d) v ∈ OnmFull W n m
  /-- DJ (2.2), `O''_{n,p}` associator generator (left slot). -/
  rightO'' : ∀ v : 𝒱, ∀ q₁ q₂ q₃ : ℕ, ∀ b₁ b₂ b₃ w : 𝒱,
    anmGen W n m p (assocDefect W n p q₁ q₂ q₃ b₁ b₂ b₃ w) v ∈ OnmFull W n m
  /-- DJ (2.2), `O'''_{n,p}` level-mixing generator (left slot). -/
  rightO''' : ∀ v : 𝒱, ∀ q : ℕ, ∀ b w : 𝒱, ∀ g : 𝒱, g ∈ Onm W q q →
    anmGen W n m p (levelMix W n p q b g w) v ∈ OnmFull W n m

/-! ## `span_le` over the three `OnmFull` summands (right action). -/

/-- The `O'_{n,p}` (= `Onm W n p`) summand is mapped into `OnmFull W n m` by the left-action map
`anmGen W n m p · v`, given the two `O'` generator families (circle = `rightO'Circ`, grading =
the closed off-diagonal absorption `anmRight_O'Lgen`-style — but at the *general* off-diagonal we
must absorb with `(p₂,p₁) = (n,p)`, which is `anmGen_offdiag_Lgen_eq_general W m p n c v`). -/
theorem Onm_le_comap_leftMap (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (v : 𝒱)
    (hcirc : ∀ c d : 𝒱, anmGen W n m p (anmCirc W n p c d) v ∈ OnmFull W n m) :
    Onm W n p ≤ (OnmFull W n m).comap (anmGenLeftMap W n m p v) := by
  rw [Onm_eq_sup_span]
  refine sup_le ?_ ?_
  · rw [Submodule.span_le]
    rintro x ⟨c, d, rfl⟩
    simpa only [SetLike.mem_coe, Submodule.mem_comap, anmGenLeftMap_apply] using hcirc c d
  · rw [OnmL, Submodule.span_le]
    rintro x ⟨c, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, anmGenLeftMap_apply]
    -- `anmGen W n m p (anmLgen W n p c) v`: off-diagonal absorption with `(p₂,p₁) = (n,p)`.
    rw [show anmLgen W n p c = W.L (-1) c + W.L 0 c + ((p : ℂ) - (n : ℂ)) • c from rfl,
        anmGen_offdiag_Lgen_eq_general W m p n c v]
    exact Submodule.smul_mem _ _ (anmCirc_mem_OnmFull W n m c v)

/-- The `O''_{n,p}` (= `OnmAssoc W n p`) summand is mapped into `OnmFull W n m` by `anmGen W n m p · v`,
given the associator generator family `rightO''`. -/
theorem OnmAssoc_le_comap_leftMap (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (v : 𝒱)
    (hassoc : ∀ q₁ q₂ q₃ : ℕ, ∀ b₁ b₂ b₃ w : 𝒱,
      anmGen W n m p (assocDefect W n p q₁ q₂ q₃ b₁ b₂ b₃ w) v ∈ OnmFull W n m) :
    OnmAssoc W n p ≤ (OnmFull W n m).comap (anmGenLeftMap W n m p v) := by
  rw [OnmAssoc, Submodule.span_le]
  rintro x ⟨q₁, q₂, q₃, b₁, b₂, b₃, w, rfl⟩
  simpa only [SetLike.mem_coe, Submodule.mem_comap, anmGenLeftMap_apply] using
    hassoc q₁ q₂ q₃ b₁ b₂ b₃ w

/-- The `O'''_{n,p}` (= `OnmLevel W n p`) summand is mapped into `OnmFull W n m` by `anmGen W n m p · v`,
given the level-mixing generator family `rightO'''`. -/
theorem OnmLevel_le_comap_leftMap (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (v : 𝒱)
    (hlevel : ∀ q : ℕ, ∀ b w : 𝒱, ∀ g : 𝒱, g ∈ Onm W q q →
      anmGen W n m p (levelMix W n p q b g w) v ∈ OnmFull W n m) :
    OnmLevel W n p ≤ (OnmFull W n m).comap (anmGenLeftMap W n m p v) := by
  rw [OnmLevel, Submodule.span_le]
  rintro x ⟨q, b, w, g, hg, rfl⟩
  simpa only [SetLike.mem_coe, Submodule.mem_comap, anmGenLeftMap_apply] using
    hlevel q b w g hg

/-! ## `span_le` over the three `OnmFull` summands (left action). -/

/-- The `O'_{p,m}` (= `Onm W p m`) summand is mapped into `OnmFull W n m` by the right-action map
`anmGen W n m p a ·`, given the circle generator family (= the closed `circCross_mem`-style branch at
the general off-diagonal) and the grading generator family `leftO'Lgen`. -/
theorem Onm_le_comap_rightMap (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (a : 𝒱)
    (hcirc : ∀ c d : 𝒱, anmGen W n m p a (anmCirc W p m c d) ∈ OnmFull W n m)
    (hL : ∀ c : 𝒱, anmGen W n m p a (anmLgen W p m c) ∈ OnmFull W n m) :
    Onm W p m ≤ (OnmFull W n m).comap (anmGenRightMap W n m p a) := by
  rw [Onm_eq_sup_span]
  refine sup_le ?_ ?_
  · rw [Submodule.span_le]
    rintro x ⟨c, d, rfl⟩
    simpa only [SetLike.mem_coe, Submodule.mem_comap, anmGenRightMap_apply] using hcirc c d
  · rw [OnmL, Submodule.span_le]
    rintro x ⟨c, rfl⟩
    simpa only [SetLike.mem_coe, Submodule.mem_comap, anmGenRightMap_apply] using hL c

/-- The `O''_{p,m}` summand mapped into `OnmFull W n m` by `anmGen W n m p a ·`, given `leftO''`. -/
theorem OnmAssoc_le_comap_rightMap (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (a : 𝒱)
    (hassoc : ∀ q₁ q₂ q₃ : ℕ, ∀ b₁ b₂ b₃ w : 𝒱,
      anmGen W n m p a (assocDefect W p m q₁ q₂ q₃ b₁ b₂ b₃ w) ∈ OnmFull W n m) :
    OnmAssoc W p m ≤ (OnmFull W n m).comap (anmGenRightMap W n m p a) := by
  rw [OnmAssoc, Submodule.span_le]
  rintro x ⟨q₁, q₂, q₃, b₁, b₂, b₃, w, rfl⟩
  simpa only [SetLike.mem_coe, Submodule.mem_comap, anmGenRightMap_apply] using
    hassoc q₁ q₂ q₃ b₁ b₂ b₃ w

/-- The `O'''_{p,m}` summand mapped into `OnmFull W n m` by `anmGen W n m p a ·`, given `leftO'''`. -/
theorem OnmLevel_le_comap_rightMap (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (a : 𝒱)
    (hlevel : ∀ q : ℕ, ∀ b w : 𝒱, ∀ g : 𝒱, g ∈ Onm W q q →
      anmGen W n m p a (levelMix W p m q b g w) ∈ OnmFull W n m) :
    OnmLevel W p m ≤ (OnmFull W n m).comap (anmGenRightMap W n m p a) := by
  rw [OnmLevel, Submodule.span_le]
  rintro x ⟨q, b, w, g, hg, rfl⟩
  simpa only [SetLike.mem_coe, Submodule.mem_comap, anmGenRightMap_apply] using
    hlevel q b w g hg

/-! ## DJ Lemma 2.8 — the two general inclusions (modulo `DJ28Residual`). -/

/-- **DJ Lemma 2.8, the left inclusion** `V ∗ⁿ_{m,p} O_{p,m}(V) ⊆ O_{n,m}(V)`:
`∀ g ∈ OnmFull W p m, anmGen W n m p a g ∈ OnmFull W n m`.

`OnmFull W p m = (Onm ⊔ OnmAssoc) ⊔ OnmLevel`; the right-action map `anmGen W n m p a ·` is ℂ-linear,
so `Submodule.mem_sup` splits `g` into the three summands and `span_le` reduces each to its generator
family.  The `O'` circle branch is the closed `circCross_mem`; the `O'` grading, `O''`, `O'''`
branches are the residual fields `leftO'Lgen`/`leftO''`/`leftO'''`. -/
theorem anmGen_OnmFull_left (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (a : 𝒱)
    (hres : DJ28Residual W n m p) :
    ∀ g ∈ OnmFull W p m, anmGen W n m p a g ∈ OnmFull W n m := by
  intro g hg
  -- `OnmFull = (Onm ⊔ OnmAssoc) ⊔ OnmLevel`; split via `Submodule.mem_sup` twice.
  rw [OnmFull, Submodule.mem_sup] at hg
  obtain ⟨y, hy, z, hz, rfl⟩ := hg
  rw [anmGen_add_right]
  refine (OnmFull W n m).add_mem ?_ ?_
  · -- `y ∈ Onm W p m ⊔ OnmAssoc W p m`.
    rw [Submodule.mem_sup] at hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hy
    rw [anmGen_add_right]
    refine (OnmFull W n m).add_mem ?_ ?_
    · -- `y₁ ∈ Onm W p m` (the `O'` summand).
      have hle := Onm_le_comap_rightMap W n m p a
        (fun c d => circCross_mem W n m p a d c) (hres.leftO'Lgen a)
      have hx : y₁ ∈ (OnmFull W n m).comap (anmGenRightMap W n m p a) := hle hy₁
      rwa [Submodule.mem_comap, anmGenRightMap_apply] at hx
    · -- `y₂ ∈ OnmAssoc W p m` (the `O''` summand).
      have hle := OnmAssoc_le_comap_rightMap W n m p a (hres.leftO'' a)
      have hx : y₂ ∈ (OnmFull W n m).comap (anmGenRightMap W n m p a) := hle hy₂
      rwa [Submodule.mem_comap, anmGenRightMap_apply] at hx
  · -- `z ∈ OnmLevel W p m` (the `O'''` summand).
    have hle := OnmLevel_le_comap_rightMap W n m p a (hres.leftO''' a)
    have hx : z ∈ (OnmFull W n m).comap (anmGenRightMap W n m p a) := hle hz
    rwa [Submodule.mem_comap, anmGenRightMap_apply] at hx

/-- **DJ Lemma 2.8, the right inclusion** `O_{n,p}(V) ∗ⁿ_{m,p} V ⊆ O_{n,m}(V)`:
`∀ g ∈ OnmFull W n p, anmGen W n m p g v ∈ OnmFull W n m`.

Same split, via the left-action map `anmGen W n m p · v`.  The `O'` grading branch is the closed
off-diagonal absorption (inside `Onm_le_comap_leftMap`); the `O'` circle, `O''`, `O'''` branches are
the residual fields `rightO'Circ`/`rightO''`/`rightO'''`. -/
theorem anmGen_OnmFull_right (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (v : 𝒱)
    (hres : DJ28Residual W n m p) :
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
    · -- `y₁ ∈ Onm W n p` (the `O'` summand).
      have hle := Onm_le_comap_leftMap W n m p v (hres.rightO'Circ · · v)
      have hx : y₁ ∈ (OnmFull W n m).comap (anmGenLeftMap W n m p v) := hle hy₁
      rwa [Submodule.mem_comap, anmGenLeftMap_apply] at hx
    · -- `y₂ ∈ OnmAssoc W n p` (the `O''` summand).
      have hle := OnmAssoc_le_comap_leftMap W n m p v (hres.rightO'' v)
      have hx : y₂ ∈ (OnmFull W n m).comap (anmGenLeftMap W n m p v) := hle hy₂
      rwa [Submodule.mem_comap, anmGenLeftMap_apply] at hx
  · -- `z ∈ OnmLevel W n p` (the `O'''` summand).
    have hle := OnmLevel_le_comap_leftMap W n m p v (hres.rightO''' v)
    have hx : z ∈ (OnmFull W n m).comap (anmGenLeftMap W n m p v) := hle hz
    rwa [Submodule.mem_comap, anmGenLeftMap_apply] at hx

/-! ## DJ Lemma 2.8 "in particular" — the headline specializations. -/

/-- **DJ Lemma 2.8 "in particular": `V ∗̄ⁿ_m O_{n,m}(V) ⊆ O_{n,m}(V)`** (left action `∗̄ⁿ_m`, `p = n`).
`∀ g ∈ OnmFull W n m, anmGenBar W n m a g ∈ OnmFull W n m`.  Specialization of `anmGen_OnmFull_left`
at `p = n` (`anmGenBar = anmGen W n m n`). -/
theorem anmGenBar_OnmFull (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (a : 𝒱)
    (hres : DJ28Residual W n m n) :
    ∀ g ∈ OnmFull W n m, anmGenBar W n m a g ∈ OnmFull W n m := by
  intro g hg
  rw [anmGenBar]
  exact anmGen_OnmFull_left W n m n a hres g hg

/-- **DJ Lemma 2.8 "in particular": `O_{n,m}(V) ∗ⁿ_m V ⊆ O_{n,m}(V)`** (right action `∗ⁿ_m`, `p = m`).
`∀ g ∈ OnmFull W n m, anmRight W n m g v ∈ OnmFull W n m`.  Specialization of `anmGen_OnmFull_right`
at `p = m` (`anmRight = anmGen W n m m`). -/
theorem anmRight_OnmFull (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (v : 𝒱)
    (hres : DJ28Residual W n m m) :
    ∀ g ∈ OnmFull W n m, anmRight W n m g v ∈ OnmFull W n m := by
  intro g hg
  rw [← anmGen_eq_anmRight]
  exact anmGen_OnmFull_right W n m m v hres g hg

end VOA
