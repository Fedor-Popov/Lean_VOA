/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchFrobeniusLift

/-!
# `ker q = J` — the first-isomorphism core of the freeness of `M(U)` (Zhu Thm 5.3.4, Tier 3)

`Modules.ZhuVermaAnArchFrobeniusLift` carries the universal-property datum `FrobeniusUniversalData`
of the generalized-Verma module `M(U)` for an irreducible lowest-weight `P`: a **nonzero**
`𝒱`-intertwiner `q : M(U) → P` that is the identity on the bottom (`q_bottom`), with the kernel
identification `ker q = J` (`q_ker`) carried as a *field*. This file **proves** that kernel
identification from the purely structural inputs — irreducibility of `P`, the bottom-identity
normalization (`q` injective on the bottom), and the *maximality* of `J` among bottom-trivial
submodules — so that `q_ker` is not an opaque assumption but a derived fact of the
submodule/irreducibility API.

## The structural picture (first-isomorphism theorem)

Fix an irreducible lowest-weight `P` and a `𝒱`-intertwiner `q : M(U) → P` that is the identity on
the bottom `M(U)_h = range (MU.incl … 0)` (its bottom component is the *iso* `β`, hence `q` is
injective on the bottom). Let `J` be the maximal submodule of `M(U)` meeting the bottom trivially.

* **`q` is surjective** — its range is a `𝒱`-submodule of the irreducible `P`, nonzero (`q ≠ 0`),
  hence all of `P`. *Generation-from-bottom ⟹ surjectivity* (carried via the same `q_act`/range
  argument as `FrobeniusLiftData.surjective`).
* **`ker q ⊆ J`** — `ker q` is a `𝒱`-submodule of `M(U)` meeting the bottom trivially (`q` is
  injective on the bottom, so a bottom vector in `ker q` is `0`); by **maximality** of `J` among
  bottom-trivial submodules, `ker q ⊆ J`.
* **`ker q` is a coatom** — `M(U)/ker q ≅ P` is irreducible, so no submodule lies strictly between
  `ker q` and `⊤`: if `ker q ⊆ N` then `q(N)` is a submodule of `P`, `= ⊥` (forcing `N = ker q`) or
  `= ⊤` (forcing `N = ⊤` since `q` is surjective and `ker q ⊆ N`).
* **`J ≠ ⊤`** — `J` meets the *nonzero* bottom `M(U)_h` trivially, so `J = ⊤` would force
  `M(U)_h = ⊥`, contradicting realization.

Combining: `ker q ⊆ J`, `J ≠ ⊤`, and the coatom property of `ker q` force `ker q = J`. This is the
genuine first-isomorphism content; every step is built from the submodule/irreducibility API.

## What is carried — `KerJData` (no `sorry`, never an axiom)

The maximality of `J` and the bottom-identity normalization are the honest structural inputs. We
bundle them — and only them — into `KerJData`:

* `bottom` — the bottom subspace `M(U)_h = range (MU.incl … 0)` (the realized lowest-weight space);
* `bottom_ne_bot` — the bottom is nonzero (realization);
* `J` — the candidate maximal bottom-trivial `𝒱`-submodule;
* `J_bottom_trivial` — `J ⊓ bottom = ⊥` (`J` meets the bottom trivially);
* `J_maximal` — *maximality*: any `𝒱`-submodule meeting the bottom trivially is `⊆ J`;
* `q`, `q_act` — the intertwiner and its mode-intertwining;
* `q_ne_zero` — `q ≠ 0` (the bottom-identity lift is nonzero);
* `q_inj_on_bottom` — `q` is injective on the bottom (the bottom component `β` is an iso);
* `P_irreducible` — `P` is irreducible.

From this we **prove** `KerJData.ker_eq_J : ker q = J.carrier`, axiom-clean. The single residual is
exactly the *existence* of such `q` and the maximal `J` (the Dong–Jiang/Frenkel–Zhu construction),
carried as data — never an axiom.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4; Zhu [574]; Frenkel–Zhu.
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱} {U : AMod W} {h : ℂ}

/-! ## The structural inputs — `KerJData` -/

/-- **The structural data realizing `ker q = J`** for an intertwiner into an irreducible `P`.

Bundles the maximality of the bottom-trivial submodule `J`, the bottom-identity normalization
(`q` injective on the bottom, `q ≠ 0`), and irreducibility of `P`. From it `ker q = J` is *proved*
(first-isomorphism theorem), so the `q_ker` field of `FrobeniusUniversalData` is not opaque.

* `bottom` — the realized bottom subspace `M(U)_h = range (MU.incl … 0)`;
* `bottom_ne_bot` — the bottom is nonzero (realization);
* `J` — the candidate maximal bottom-trivial `𝒱`-submodule;
* `J_bottom_trivial` — `J ⊓ bottom = ⊥`;
* `J_maximal` — any `𝒱`-submodule meeting the bottom trivially is `⊆ J` (maximality);
* `q`, `q_act` — the intertwiner and its mode-intertwining;
* `q_ne_zero` — `q ≠ 0`;
* `q_inj_on_bottom` — `q` injective on `bottom`;
* `P_irreducible` — `P` is irreducible. -/
structure KerJData (D : MUModuleData W U h) (P : LWModule W) where
  /-- The realized bottom subspace `M(U)_h = range (MU.incl … 0)`. -/
  bottom : Submodule ℂ (MU W U)
  /-- The bottom is nonzero (realization). -/
  bottom_ne_bot : bottom ≠ ⊥
  /-- The candidate maximal bottom-trivial `𝒱`-submodule `J`. -/
  J : WeakModule.Submodule' D.toOrdVModule.toWeakModule
  /-- `J` meets the bottom trivially. -/
  J_bottom_trivial : J.carrier ⊓ bottom = ⊥
  /-- **Maximality:** any `𝒱`-submodule meeting the bottom trivially is `⊆ J`. -/
  J_maximal : ∀ N : WeakModule.Submodule' D.toOrdVModule.toWeakModule,
    N.carrier ⊓ bottom = ⊥ → N.carrier ≤ J.carrier
  /-- The intertwiner `q : M(U) → P`. -/
  q : MU W U →ₗ[ℂ] P.carrier
  /-- `q` intertwines every mode (it is a `𝒱`-module homomorphism). -/
  q_act : ∀ (u : 𝒱) (n : ℤ) (x : MU W U),
    q (D.toOrdVModule.toWeakModule.act u n x) = P.isMod.toWeakModule.act u n (q x)
  /-- `q ≠ 0`. -/
  q_ne_zero : q ≠ 0
  /-- `q` is injective on the bottom (the bottom component is an iso). -/
  q_inj_on_bottom : ∀ x ∈ bottom, q x = 0 → x = 0
  /-- `P` is irreducible. -/
  P_irreducible : P.IsIrreducibleLW

namespace KerJData

variable {D : MUModuleData W U h} {P : LWModule W}

/-! ## The range and kernel as `𝒱`-submodules -/

/-- The range of `q` as a `𝒱`-weak-submodule of `P`. Closure under every mode is the intertwining
property `q_act`: `u₍ₙ₎ (q x) = q (u₍ₙ₎ x) ∈ range q`. -/
noncomputable def rangeSubmodule (K : KerJData D P) :
    WeakModule.Submodule' P.isMod.toWeakModule where
  carrier := LinearMap.range K.q
  act_mem := by
    intro u n x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨D.toOrdVModule.toWeakModule.act u n y, K.q_act u n y⟩

@[simp] theorem rangeSubmodule_carrier (K : KerJData D P) :
    K.rangeSubmodule.carrier = LinearMap.range K.q := rfl

/-- The kernel of `q` as a `𝒱`-weak-submodule of `M(U)`. Closure under every mode is the
intertwining property `q_act`: if `q x = 0` then `q (u₍ₙ₎ x) = u₍ₙ₎ (q x) = u₍ₙ₎ 0 = 0`. -/
noncomputable def kerSubmodule (K : KerJData D P) :
    WeakModule.Submodule' D.toOrdVModule.toWeakModule where
  carrier := LinearMap.ker K.q
  act_mem := by
    intro u n x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    rw [K.q_act u n x, hx]
    exact WeakModule.act_zero_right _ _ _

@[simp] theorem kerSubmodule_carrier (K : KerJData D P) :
    K.kerSubmodule.carrier = LinearMap.ker K.q := rfl

/-! ## Surjectivity of `q` from irreducibility -/

/-- **`q` is surjective.** Its range is a `𝒱`-submodule of the irreducible `P`, hence `⊥` or `⊤`;
`q ≠ 0` rules out `⊥`. (The *generation-from-bottom ⟹ surjectivity* step.) -/
theorem surjective (K : KerJData D P) : Function.Surjective K.q := by
  rcases K.P_irreducible.2 K.rangeSubmodule with hbot | htop
  · rw [rangeSubmodule_carrier] at hbot
    exact absurd (LinearMap.range_eq_bot.mp hbot) K.q_ne_zero
  · rw [rangeSubmodule_carrier] at htop
    exact LinearMap.range_eq_top.mp htop

/-! ## `ker q ⊆ J` by maximality -/

/-- `ker q` meets the bottom trivially: a bottom vector in the kernel is `0` (`q_inj_on_bottom`). -/
theorem ker_bottom_trivial (K : KerJData D P) :
    K.kerSubmodule.carrier ⊓ K.bottom = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxk, hxb⟩ := hx
  rw [kerSubmodule_carrier] at hxk
  simp only [SetLike.mem_coe, LinearMap.mem_ker] at hxk
  rw [Submodule.mem_bot]
  exact K.q_inj_on_bottom x hxb hxk

/-- **`ker q ⊆ J`.** `ker q` is a `𝒱`-submodule meeting the bottom trivially
(`ker_bottom_trivial`); maximality of `J` (`J_maximal`) gives the inclusion. -/
theorem ker_le_J (K : KerJData D P) : LinearMap.ker K.q ≤ K.J.carrier := by
  have := K.J_maximal K.kerSubmodule K.ker_bottom_trivial
  rwa [kerSubmodule_carrier] at this

/-! ## `J ≠ ⊤` from realization -/

/-- **`J ≠ ⊤`.** If `J = ⊤` then `bottom = bottom ⊓ ⊤ = bottom ⊓ J = ⊥`, contradicting
`bottom_ne_bot`. -/
theorem J_ne_top (K : KerJData D P) : K.J.carrier ≠ ⊤ := by
  intro htop
  apply K.bottom_ne_bot
  have : K.bottom ⊓ K.J.carrier = K.bottom := by rw [htop, inf_top_eq]
  rw [inf_comm] at this
  rw [← this, K.J_bottom_trivial]

/-! ## `ker q` is a coatom, and `ker q = J` -/

/-- The image submodule `q(N) ≤ P` of a `𝒱`-submodule `N ≤ M(U)`. Closure under modes is `q_act`:
`u₍ₙ₎ (q y) = q (u₍ₙ₎ y) ∈ q(N)` for `y ∈ N`. -/
noncomputable def mapSubmodule (K : KerJData D P)
    (N : WeakModule.Submodule' D.toOrdVModule.toWeakModule) :
    WeakModule.Submodule' P.isMod.toWeakModule where
  carrier := N.carrier.map K.q
  act_mem := by
    intro u n x hx
    obtain ⟨y, hyN, rfl⟩ := hx
    exact ⟨D.toOrdVModule.toWeakModule.act u n y, N.act_mem u n hyN, K.q_act u n y⟩

@[simp] theorem mapSubmodule_carrier (K : KerJData D P)
    (N : WeakModule.Submodule' D.toOrdVModule.toWeakModule) :
    (K.mapSubmodule N).carrier = N.carrier.map K.q := rfl

/-- **`ker q` is a coatom (maximal proper submodule).** Any `𝒱`-submodule `N` with `ker q ⊆ N`
satisfies `N = ker q` or `N = ⊤`.

The image `q(N)` is a `𝒱`-submodule of the irreducible `P`, hence `⊥` or `⊤`. If `q(N) = ⊥` then
`N ⊆ ker q` (and `ker q ⊆ N`), so `N = ker q`. If `q(N) = ⊤` then, since `q` is surjective and
`ker q ⊆ N`, `N = ⊤` (`N ⊇ comap q (q(N)) = comap q ⊤ = ⊤`). -/
theorem coatom (K : KerJData D P) (N : WeakModule.Submodule' D.toOrdVModule.toWeakModule)
    (hN : LinearMap.ker K.q ≤ N.carrier) :
    N.carrier = LinearMap.ker K.q ∨ N.carrier = ⊤ := by
  rcases K.P_irreducible.2 (K.mapSubmodule N) with himg | himg
  · -- `q(N) = ⊥` ⟹ `N ≤ ker q`, combined with `ker q ≤ N` gives `N = ker q`.
    left
    rw [mapSubmodule_carrier] at himg
    apply le_antisymm _ hN
    intro x hxN
    rw [LinearMap.mem_ker]
    have : K.q x ∈ N.carrier.map K.q := ⟨x, hxN, rfl⟩
    rw [himg, Submodule.mem_bot] at this
    exact this
  · -- `q(N) = ⊤` ⟹ `N = ⊤` (surjectivity + `ker q ≤ N`).
    right
    rw [mapSubmodule_carrier] at himg
    rw [eq_top_iff]
    intro x _
    -- `q x ∈ ⊤ = q(N)`, so `q x = q y` for some `y ∈ N`; then `x - y ∈ ker q ≤ N`, so `x ∈ N`.
    have hqx : K.q x ∈ N.carrier.map K.q := by rw [himg]; trivial
    obtain ⟨y, hyN, hxy⟩ := hqx
    have hxy0 : K.q (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hmem : x - y ∈ N.carrier := hN (LinearMap.mem_ker.mpr hxy0)
    have hxeq : x = (x - y) + y := by abel
    rw [hxeq]
    exact N.carrier.add_mem hmem hyN

/-- **`ker q = J`.** From `ker q ⊆ J` (`ker_le_J`), the coatom property of `ker q` (`coatom`), and
`J ≠ ⊤` (`J_ne_top`): applying `coatom` to `N = J` gives `J = ker q ∨ J = ⊤`; the latter is
excluded, so `J = ker q`. This is the first-isomorphism core of the freeness of `M(U)`. -/
theorem ker_eq_J (K : KerJData D P) : LinearMap.ker K.q = K.J.carrier := by
  rcases K.coatom K.J K.ker_le_J with hJ | hJ
  · exact hJ.symm
  · exact absurd hJ K.J_ne_top

end KerJData

end InducedAssignment

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
