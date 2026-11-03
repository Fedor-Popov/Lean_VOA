/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDLM3Admissible

/-!
# DLM3 Theorem 4.1, part III — the `ℤ`-grading of `M̄_n(U)` and the level-`n` piece

Dong–Li–Mason, *Vertex operator algebras and associative algebras*, J. Algebra **206** (1998)
67–96 (arXiv `q-alg/9612010v2`), (4.1) grade the induced module by

> "If we give `U` degree `n`, the `ℤ`-gradation of `V̂` lifts to `M_n(U)` which thus becomes a
> `ℤ`-graded module for `V̂`.  The PBW theorem implies that `M_n(U)(i) = U(V̂)_{i−n} U`."

This file builds that grading — **PBW-free** — and reads off what it gives about the level-`n`
piece.

## The grading

`U(V̂)` is graded by the span of words in homogeneous loop modes:

* `VHat.uenvStep W e S` — the span of `uι x · y` with `x ∈ V̂(e)`, `y ∈ S`;
* `VHat.uenvDegLen W r d` — words of length exactly `r` and total degree `d` (recursion on `r`,
  base `ℂ·1` in degree `0`);
* `VHat.uenvDeg W d = ⨆ r, uenvDegLen W r d` — the degree-`d` part `U(V̂)_d`.

Its three structural properties are proved here: `one_mem_uenvDeg` (`1 ∈ U(V̂)₀`),
`uenvDeg_mul` (`U(V̂)_d · U(V̂)_{d'} ⊆ U(V̂)_{d+d'}`) and `uenvDeg_iSup_top`
(`⨆_d U(V̂)_d = ⊤`, whose loop-level input is the new `VHat.deg_iSup_top`, `⨆_d V̂(d) = V̂`).
Transporting along `y ↦ [y ⊗ u]` gives `DLM3.levCover P k = M_n(U)(k)` and, after the defect
quotient, `DLM3.levBar P k = M̄_n(U)(k)` — with `U` placed in degree `n`, exactly DLM3 (4.1).

⚠ **`DirectSum.IsInternal` is NOT claimed.**  The three theorems delivered are
`levBar_spanning` (`⨆_k M̄_n(U)(k) = ⊤`), `actMode_levBar` (the mode `a₍ₚ₎` shifts the level by
`wt a − p − 1`) and `indBarBottom_mem_levBar` (`[1 ⊗ U] ⊆ M̄_n(U)(n)`).  *Directness* of the
decomposition is exactly the place where DLM3 invoke PBW, and it is not formalized; accordingly the
packaging structure `ZGradedWeakModule` carries a spanning family, **not** an internal direct sum,
and imposes neither finite-dimensionality nor an `L₀`-eigenvalue condition (`OrdVModule.finrank` is
deliberately kept out of this construction).

## The level-`n` payoff (DLM3 Theorem 4.1's second clause, `M̄_n(U)(n) = U`)

`indBar_levelN` is the main theorem.  What is achieved, precisely:

1. `indBarBottom P : U →ₗ[ℂ] M̄_n(U)` is `ℂ`-linear and lands in the level-`n` piece
   `M̄_n(U)(n)` — the "`U ⊆ M̄_n(U)(n)`" half, as a map;
2. it **intertwines** the `P_n`-action on `U` with the `V̂`-action on `M̄_n(U)`
   (`indBarBottom_equivariant`); on a degree-`0` generator `a(wt a − 1)` — DLM3's `o(a)` — this is
   `o(a)·[1 ⊗ u] = [1 ⊗ a·u]`;
3. its injectivity is **equivalent** to `U` admitting a separating weak-module realization
   (`indBarBottom_injective_iff`).

**Which of DLM3's two formulations is achieved:** *not* "`M̄_n(U)(n) ≅ U` as `A_n(V)`-modules", and
*not* "`M̄_n(U)(n) ≅ U` as `ℂ`-vector spaces".  What is achieved is **`ℂ`-linearity plus the
pointwise intertwining** of item 2, together with the exact obstruction of item 3.  The two missing
inputs are named and unproved:

* DLM3 **Proposition 3.1** (`V̂(0) ↠ A_n(V)` as Lie algebras) is not in the repo, so the
  intertwining cannot yet be upgraded to `A_n(𝒱)`-linearity; the `A_n(𝒱)`-module `U` enters only
  through the `P_n`-representation `ParabolicRep`;
* injectivity and surjectivity of `U → M̄_n(U)(n)` are both open.  DLM3 get injectivity from
  `J ∩ U = 0` for the radical `J` of their pairing (4.5), which rests on Propositions 4.3/4.6/4.7 —
  and Proposition 4.6 has **no printed proof** (DLM3 defer it to [DLM] Prop 6.1).  Surjectivity is
  their single-mode spanning step (`M̄_n(U)(m) = V̂(m−n)(U + U(V̂)W)`, quoted from [DM] Prop 2.4 /
  [L2] Lemma 6.1.1), also not formalized.

Everything here is `sorry`-free, `pbw`-free and `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`).

## References
DLM3 (`q-alg/9612010v2`) §3 (3.1)–(3.3), §4 (4.1)–(4.5), Thm 4.1;
`ZhuVermaAnArchDLM3Deg` (`deg`, `degSpan`), `ZhuVermaAnArchDLM3Induced` (`IndMod`, `indRho`,
`indMk`, `ind_generation`), `ZhuVermaAnArchDLM3Admissible` (`indBottom`, `indBarBottom`,
`Realization`, `indBarBottom_injective_iff`), `Modules/WeakModule` (`WeakModule`).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## A `ℤ`-graded weak module: a spanning level family, no internality, no finiteness -/

/-- A **`ℤ`-graded weak `𝒱`-module**: a weak module together with a family of level subspaces which
*spans* the module and along which the modes shift the level by `wt a − p − 1`.

This is deliberately weaker than `OrdVModule` (Gannon 5.3.1c) in three respects, each of which matters
for `M̄_n(U)`: the family is not asserted to be an internal direct sum (that is DLM3's PBW step),
the pieces are not asserted finite-dimensional, and no `L₀`-eigenvalue condition is imposed. -/
structure ZGradedWeakModule (W : VertexOperatorAlgebra 𝒱) (M : Type u) [AddCommGroup M]
    [Module ℂ M] where
  /-- The underlying weak module (Gannon Def. 5.3.1a–b). -/
  weak : WeakModule W M
  /-- The level filtration `M(k)`, `k ∈ ℤ` (DLM3 (4.1)). -/
  lev : ℤ → Submodule ℂ M
  /-- The levels **span** `M`.  (Directness — `DirectSum.IsInternal` — is *not* asserted.) -/
  lev_spanning : ⨆ k : ℤ, lev k = ⊤
  /-- A mode of a homogeneous state shifts the level by its `V̂`-degree `wt a − p − 1`. -/
  act_lev : ∀ ⦃w p k : ℤ⦄ ⦃a : 𝒱⦄, a ∈ W.grading w → ∀ ⦃x : M⦄, x ∈ lev k →
    weak.act a p x ∈ lev (k + (w - p - 1))

namespace VHat

/-! ## The loop algebra is spanned by its graded pieces -/

/-- **`⨆_d V̂(d) = V̂`.**  Every loop generator `a(m)` decomposes into homogeneous pieces along the
internal grading of `𝒱`, and the generators span `V̂` (`gen_span_top`). -/
theorem deg_iSup_top (W : VertexOperatorAlgebra 𝒱) : (⨆ d : ℤ, deg W d) = ⊤ := by
  refine eq_top_iff.mpr ?_
  have hspan : Submodule.span ℂ (Set.range (fun p : 𝒱 × ℤ => gen W p.1 p.2)) = ⊤ :=
    gen_span_top W
  rw [← hspan]
  refine Submodule.span_le.mpr ?_
  rintro x ⟨⟨a, m⟩, rfl⟩
  have ha : a ∈ ⨆ w : ℤ, W.grading w := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun a => gen W a m ∈ ⨆ d : ℤ, deg W d) ha ?_ ?_ ?_
  · intro w b hb
    exact Submodule.mem_iSup_of_mem (w - m - 1) (gen_mem_deg W hb m)
  · dsimp only
    rw [gen_zero_left]; exact Submodule.zero_mem _
  · intro a₁ a₂ h₁ h₂
    rw [gen_add_left]
    exact Submodule.add_mem _ h₁ h₂

/-! ## The `ℤ`-grading of `U(V̂)` by word span -/

/-- One step of the word recursion: the span of `uι x · y` with `x ∈ V̂(e)` and `y ∈ S`. -/
noncomputable def uenvStep (W : VertexOperatorAlgebra 𝒱) (e : ℤ)
    (S : Submodule ℂ (UEnv W)) : Submodule ℂ (UEnv W) :=
  Submodule.span ℂ {z | ∃ x ∈ deg W e, ∃ y ∈ S, z = uι W x * y}

theorem mem_uenvStep (W : VertexOperatorAlgebra 𝒱) {e : ℤ} {S : Submodule ℂ (UEnv W)}
    {x : VHatCarrier W} (hx : x ∈ deg W e) {y : UEnv W} (hy : y ∈ S) :
    uι W x * y ∈ uenvStep W e S :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩

/-- Words of length `r` and total `V̂`-degree `d` inside `U(V̂)`. -/
noncomputable def uenvDegLen (W : VertexOperatorAlgebra 𝒱) : ℕ → ℤ → Submodule ℂ (UEnv W)
  | 0, d => if d = 0 then Submodule.span ℂ {(1 : UEnv W)} else ⊥
  | (r + 1), d => ⨆ e : ℤ, uenvStep W e (uenvDegLen W r (d - e))

theorem uenvDegLen_zero (W : VertexOperatorAlgebra 𝒱) (d : ℤ) :
    uenvDegLen W 0 d = if d = 0 then Submodule.span ℂ {(1 : UEnv W)} else ⊥ := rfl

theorem uenvDegLen_succ (W : VertexOperatorAlgebra 𝒱) (r : ℕ) (d : ℤ) :
    uenvDegLen W (r + 1) d = ⨆ e : ℤ, uenvStep W e (uenvDegLen W r (d - e)) := rfl

/-- **The degree-`d` part `U(V̂)_d`** of the universal enveloping algebra: the span of all words in
homogeneous loop modes of total degree `d`.  (No PBW input: this is a span, not a direct
summand.) -/
noncomputable def uenvDeg (W : VertexOperatorAlgebra 𝒱) (d : ℤ) : Submodule ℂ (UEnv W) :=
  ⨆ r : ℕ, uenvDegLen W r d

theorem uenvDegLen_le_uenvDeg (W : VertexOperatorAlgebra 𝒱) (r : ℕ) (d : ℤ) :
    uenvDegLen W r d ≤ uenvDeg W d :=
  le_iSup (fun r : ℕ => uenvDegLen W r d) r

/-- `1 ∈ U(V̂)₀` (the empty word). -/
theorem one_mem_uenvDeg (W : VertexOperatorAlgebra 𝒱) : (1 : UEnv W) ∈ uenvDeg W 0 := by
  refine uenvDegLen_le_uenvDeg W 0 0 ?_
  rw [uenvDegLen_zero, if_pos rfl]
  exact Submodule.mem_span_singleton_self _

/-- **Left multiplication by a homogeneous loop mode shifts the degree**:
`uι(V̂(e)) · U(V̂)_d ⊆ U(V̂)_{e+d}`. -/
theorem uenvDeg_uι_mul (W : VertexOperatorAlgebra 𝒱) {e d : ℤ} {x : VHatCarrier W}
    (hx : x ∈ deg W e) {y : UEnv W} (hy : y ∈ uenvDeg W d) :
    uι W x * y ∈ uenvDeg W (e + d) := by
  refine Submodule.iSup_induction (fun r : ℕ => uenvDegLen W r d)
    (motive := fun y => uι W x * y ∈ uenvDeg W (e + d)) hy ?_ ?_ ?_
  · intro r y hy'
    refine uenvDegLen_le_uenvDeg W (r + 1) (e + d) ?_
    rw [uenvDegLen_succ]
    refine Submodule.mem_iSup_of_mem e ?_
    rw [show e + d - e = d from by ring]
    exact mem_uenvStep W hx hy'
  · dsimp only
    rw [mul_zero]; exact Submodule.zero_mem _
  · intro y₁ y₂ h₁ h₂
    rw [mul_add]
    exact Submodule.add_mem _ h₁ h₂

/-- Right multiplication of a length-`r` word by an arbitrary graded element (induction on `r`). -/
theorem uenvDegLen_mul (W : VertexOperatorAlgebra 𝒱) (r : ℕ) :
    ∀ {d d' : ℤ} {y : UEnv W}, y ∈ uenvDegLen W r d → ∀ {z : UEnv W}, z ∈ uenvDeg W d' →
      y * z ∈ uenvDeg W (d + d') := by
  induction r with
  | zero =>
    intro d d' y hy z hz
    rw [uenvDegLen_zero] at hy
    by_cases hd : d = 0
    · rw [if_pos hd] at hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [smul_mul_assoc, one_mul, hd, zero_add]
      exact Submodule.smul_mem _ _ hz
    · rw [if_neg hd, Submodule.mem_bot] at hy
      rw [hy, zero_mul]
      exact Submodule.zero_mem _
  | succ r ih =>
    intro d d' y hy z hz
    rw [uenvDegLen_succ] at hy
    refine Submodule.iSup_induction (fun e : ℤ => uenvStep W e (uenvDegLen W r (d - e)))
      (motive := fun y => y * z ∈ uenvDeg W (d + d')) hy ?_ ?_ ?_
    · intro e y hy'
      refine Submodule.span_induction
        (p := fun y _ => y * z ∈ uenvDeg W (d + d')) ?_ ?_ ?_ ?_ hy'
      · rintro y ⟨x, hx, y', hy'', rfl⟩
        rw [mul_assoc]
        have hstep : y' * z ∈ uenvDeg W ((d - e) + d') := ih hy'' hz
        have := uenvDeg_uι_mul W hx hstep
        rwa [show e + ((d - e) + d') = d + d' from by ring] at this
      · dsimp only
        rw [zero_mul]; exact Submodule.zero_mem _
      · intro y₁ y₂ _ _ h₁ h₂
        rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
      · intro c y₁ _ h₁
        rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
    · dsimp only
      rw [zero_mul]; exact Submodule.zero_mem _
    · intro y₁ y₂ h₁ h₂
      rw [add_mul]; exact Submodule.add_mem _ h₁ h₂

/-- **`U(V̂)_d · U(V̂)_{d'} ⊆ U(V̂)_{d+d'}`** — the grading is multiplicative. -/
theorem uenvDeg_mul (W : VertexOperatorAlgebra 𝒱) {d d' : ℤ} {y z : UEnv W}
    (hy : y ∈ uenvDeg W d) (hz : z ∈ uenvDeg W d') : y * z ∈ uenvDeg W (d + d') := by
  refine Submodule.iSup_induction (fun r : ℕ => uenvDegLen W r d)
    (motive := fun y => y * z ∈ uenvDeg W (d + d')) hy ?_ ?_ ?_
  · intro r y hy'
    exact uenvDegLen_mul W r hy' hz
  · dsimp only
    rw [zero_mul]; exact Submodule.zero_mem _
  · intro y₁ y₂ h₁ h₂
    rw [add_mul]; exact Submodule.add_mem _ h₁ h₂

/-- **`⨆_d U(V̂)_d = U(V̂)`** — the graded pieces span the enveloping algebra.  (Word induction
`uenv_induction`, whose generator step is `deg_iSup_top`.) -/
theorem uenvDeg_iSup_top (W : VertexOperatorAlgebra 𝒱) : (⨆ d : ℤ, uenvDeg W d) = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  refine uenv_induction (C := fun y => y ∈ ⨆ d : ℤ, uenvDeg W d) ?_ ?_ ?_ ?_ y
  · intro c
    refine Submodule.mem_iSup_of_mem 0 ?_
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (one_mem_uenvDeg W)
  · intro x
    have hx : x ∈ ⨆ d : ℤ, deg W d := by rw [deg_iSup_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction (fun d : ℤ => deg W d)
      (motive := fun x => uι W x ∈ ⨆ d : ℤ, uenvDeg W d) hx ?_ ?_ ?_
    · intro d x hx'
      refine Submodule.mem_iSup_of_mem d ?_
      have := uenvDeg_uι_mul W hx' (one_mem_uenvDeg W)
      rwa [mul_one, add_zero] at this
    · dsimp only
      rw [map_zero]; exact Submodule.zero_mem _
    · intro x₁ x₂ h₁ h₂
      rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  · intro a b ha hb
    refine Submodule.iSup_induction (fun d : ℤ => uenvDeg W d)
      (motive := fun a => a * b ∈ ⨆ d : ℤ, uenvDeg W d) ha ?_ ?_ ?_
    · intro d a ha'
      refine Submodule.iSup_induction (fun d' : ℤ => uenvDeg W d')
        (motive := fun b => a * b ∈ ⨆ d : ℤ, uenvDeg W d) hb ?_ ?_ ?_
      · intro d' b hb'
        exact Submodule.mem_iSup_of_mem (d + d') (uenvDeg_mul W ha' hb')
      · dsimp only
        rw [mul_zero]; exact Submodule.zero_mem _
      · intro b₁ b₂ h₁ h₂
        rw [mul_add]; exact Submodule.add_mem _ h₁ h₂
    · dsimp only
      rw [zero_mul]; exact Submodule.zero_mem _
    · intro a₁ a₂ h₁ h₂
      rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
  · intro a b ha hb
    exact Submodule.add_mem _ ha hb

namespace DLM3

variable {W : VertexOperatorAlgebra 𝒱} {n : ℕ} {U : Type u} [AddCommGroup U] [Module ℂ U]

/-! ## The level filtration of `M_n(U)` (DLM3 (4.1): `U` sits in degree `n`) -/

/-- **`M_n(U)(k) = U(V̂)_{k−n}·U`** (DLM3 (4.1), with `U` placed in degree `n`). -/
noncomputable def levCover (P : ParabolicRep W n U) (k : ℤ) : Submodule ℂ (IndMod P) :=
  Submodule.span ℂ {z | ∃ y ∈ uenvDeg W (k - (n : ℤ)), ∃ u : U, z = indMk P (y ⊗ₜ[ℂ] u)}

theorem mem_levCover (P : ParabolicRep W n U) {k : ℤ} {y : UEnv W}
    (hy : y ∈ uenvDeg W (k - (n : ℤ))) (u : U) :
    indMk P (y ⊗ₜ[ℂ] u) ∈ levCover P k :=
  Submodule.subset_span ⟨y, hy, u, rfl⟩

/-- **The bottom `1 ⊗ U` sits in level `n`** — DLM3's placement of `U` in degree `n`. -/
theorem indBottom_mem_levCover (P : ParabolicRep W n U) (u : U) :
    indBottom P u ∈ levCover P (n : ℤ) := by
  rw [indBottom_apply]
  refine mem_levCover P ?_ u
  rw [sub_self]
  exact one_mem_uenvDeg W

/-- **The levels span `M_n(U)`.** -/
theorem levCover_spanning (P : ParabolicRep W n U) : (⨆ k : ℤ, levCover P k) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  obtain ⟨t, rfl⟩ := (balancing P).mkQ_surjective z
  change indMk P t ∈ ⨆ k : ℤ, levCover P k
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul y u =>
    have hy : y ∈ ⨆ d : ℤ, uenvDeg W d := by rw [uenvDeg_iSup_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction (fun d : ℤ => uenvDeg W d)
      (motive := fun y => indMk P (y ⊗ₜ[ℂ] u) ∈ ⨆ k : ℤ, levCover P k) hy ?_ ?_ ?_
    · intro d y hy'
      refine Submodule.mem_iSup_of_mem (d + (n : ℤ)) (mem_levCover P ?_ u)
      rwa [show d + (n : ℤ) - (n : ℤ) = d from by ring]
    · dsimp only
      rw [TensorProduct.zero_tmul, map_zero]; exact Submodule.zero_mem _
    · intro y₁ y₂ h₁ h₂
      rw [TensorProduct.add_tmul, map_add]
      exact Submodule.add_mem _ h₁ h₂
  | add t₁ t₂ h₁ h₂ =>
    rw [map_add]; exact Submodule.add_mem _ h₁ h₂

/-- **The modes shift the level by the `V̂`-degree**: `a₍ₚ₎ · M_n(U)(k) ⊆ M_n(U)(k + wt a − p − 1)`
for homogeneous `a`. -/
theorem actMode_levCover (P : ParabolicRep W n U) {w p k : ℤ} {a : 𝒱} (ha : a ∈ W.grading w)
    {z : IndMod P} (hz : z ∈ levCover P k) :
    (indRho P).actMode a p z ∈ levCover P (k + (w - p - 1)) := by
  refine Submodule.span_induction
    (p := fun z _ => (indRho P).actMode a p z ∈ levCover P (k + (w - p - 1))) ?_ ?_ ?_ ?_ hz
  · rintro z ⟨y, hy, u, rfl⟩
    rw [indRho_actMode_mk]
    refine mem_levCover P ?_ u
    have := uenvDeg_uι_mul W (gen_mem_deg W ha p) hy
    rwa [show w - p - 1 + (k - (n : ℤ)) = k + (w - p - 1) - (n : ℤ) from by ring] at this
  · dsimp only
    rw [map_zero]; exact Submodule.zero_mem _
  · intro z₁ z₂ _ _ h₁ h₂
    rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  · intro c z₁ _ h₁
    rw [map_smul]; exact Submodule.smul_mem _ _ h₁

/-! ## The level filtration of `M̄_n(U)` -/

/-- **`M̄_n(U)(k)`** — the image of `M_n(U)(k)` in the defect quotient. -/
noncomputable def levBar (P : ParabolicRep W n U) (k : ℤ) : Submodule ℂ (IndBar P) :=
  (levCover P k).map (VHatRep.defectSubmodule (indRho P)).mkQ

theorem mem_levBar (P : ParabolicRep W n U) {k : ℤ} {z : IndMod P} (hz : z ∈ levCover P k) :
    (Submodule.Quotient.mk z : IndBar P) ∈ levBar P k :=
  Submodule.mem_map_of_mem hz

/-- The bottom of `M̄_n(U)` sits in level `n` — the "`U ⊆ M̄_n(U)(n)`" half of DLM3 Theorem 4.1,
as a statement about the canonical map. -/
theorem indBarBottom_mem_levBar (P : ParabolicRep W n U) (u : U) :
    indBarBottom P u ∈ levBar P (n : ℤ) :=
  mem_levBar P (indBottom_mem_levCover P u)

/-- **The levels span `M̄_n(U)`.** -/
theorem levBar_spanning (P : ParabolicRep W n U) : (⨆ k : ℤ, levBar P k) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  refine Submodule.Quotient.induction_on _ z (fun y => ?_)
  have hy : y ∈ ⨆ k : ℤ, levCover P k := by rw [levCover_spanning]; exact Submodule.mem_top
  refine Submodule.iSup_induction (fun k : ℤ => levCover P k)
    (motive := fun y => (Submodule.Quotient.mk y : IndBar P) ∈ ⨆ k : ℤ, levBar P k) hy ?_ ?_ ?_
  · intro k y hy'
    exact Submodule.mem_iSup_of_mem k (mem_levBar P hy')
  · dsimp only
    rw [Submodule.Quotient.mk_zero]; exact Submodule.zero_mem _
  · intro y₁ y₂ h₁ h₂
    rw [Submodule.Quotient.mk_add]
    exact Submodule.add_mem _ h₁ h₂

/-- **The modes shift the level on `M̄_n(U)`.** -/
theorem actMode_levBar (P : ParabolicRep W n U) {w p k : ℤ} {a : 𝒱} (ha : a ∈ W.grading w)
    {z : IndBar P} (hz : z ∈ levBar P k) :
    (indBarRho P).actMode a p z ∈ levBar P (k + (w - p - 1)) := by
  obtain ⟨y, hy, rfl⟩ := hz
  rw [Submodule.mkQ_apply, indBarRho, VHatRep.actMode_quotientRep]
  exact mem_levBar P (actMode_levCover P ha hy)

/-! ## The graded packaging of `M̄_n(U)` -/

/-- **DLM3 Theorem 4.1, first clause, in the strongest PBW-free form available here.**  `M̄_n(U)` is
a weak `𝒱`-module (`indBarWeakModule`) equipped with a `ℤ`-indexed family of level subspaces which
spans it and along which the modes shift the level by `wt a − p − 1`.

⚠ This is *not* "admissible" in the full sense: `DirectSum.IsInternal` of the level family is
exactly DLM3's PBW step and is **not** proved, and `M̄_n(U)(m) = 0` for `m < 0` (which DLM3 read off
from that decomposition) is likewise not claimed. -/
noncomputable def indBarGraded (P : ParabolicRep W n U) : ZGradedWeakModule W (IndBar P) where
  weak := indBarWeakModule P
  lev := levBar P
  lev_spanning := levBar_spanning P
  act_lev := by
    intro w p k a ha x hx
    rw [indBarWeakModule_act]
    exact actMode_levBar P ha hx

@[simp] theorem indBarGraded_lev (P : ParabolicRep W n U) (k : ℤ) :
    (indBarGraded P).lev k = levBar P k := rfl

/-! ## The main theorem: what DLM3 Theorem 4.1's `M̄_n(U)(n) = U` amounts to here -/

/-- **The level-`n` statement of DLM3 Theorem 4.1, exactly as achieved.**

The canonical map `indBarBottom P : U → M̄_n(U)` is

1. `ℂ`-linear with image inside the level-`n` piece `M̄_n(U)(n)`;
2. **pointwise intertwining**: `[1 ⊗ g·u] = g·[1 ⊗ u]` for every `g ∈ P_n`.  On a degree-`0`
   generator `g = a(wt a − 1)` this is DLM3's `o(a)·[1 ⊗ u] = [1 ⊗ a·u]`, i.e. `A_n(𝒱)`-linearity
   *modulo* DLM3 Proposition 3.1 (`V̂(0) ↠ A_n(𝒱)`), which is not built in this repo;
3. injective **iff** `U` admits a separating weak-module realization.

So the identification is achieved at the level of "`ℂ`-linear plus the pointwise intertwining"
(DLM3's fallback formulation), **not** as an isomorphism of `A_n(𝒱)`-modules and not even as a
`ℂ`-linear isomorphism: injectivity is reduced to — not discharged by — item 3, and surjectivity
onto `M̄_n(U)(n)` (DLM3's single-mode spanning step) is untouched. -/
theorem indBar_levelN (P : ParabolicRep W n U) :
    (∀ u : U, indBarBottom P u ∈ (indBarGraded P).lev (n : ℤ)) ∧
      (∀ (g : Pn W n) (u : U),
        indBarBottom P (P.act g u) = indBarRho P (g : VHatCarrier W) (indBarBottom P u)) ∧
      (Function.Injective (indBarBottom P) ↔ ∃ R : Realization W n U P, R.Separates) :=
  ⟨indBarBottom_mem_levBar P, indBarBottom_equivariant P, indBarBottom_injective_iff P⟩

end DLM3

end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
