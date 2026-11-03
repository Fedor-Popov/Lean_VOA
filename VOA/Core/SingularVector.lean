/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.QuotientVOA
import VOA.Core.InvariantFormFHL2

/-!
# Singular vectors, the ideals they generate, and the simple quotient

This is the **interface file** between explicit singular-vector computations (the Virasoro
minimal-model vector at `c = 1/2`, the affine `sl₂` vector at `k = -4/3`, …) and the
structural statements they are meant to feed: *`𝒱` is not simple*, *the simple quotient is
`𝒱 / (s)`*, and, downstream, the deformation-rigidity argument of Linshaw–Qi
(arXiv:2601.12017), where a singular vector is forced to deform to zero.

## What a singular vector is — two notions, and why the distinction matters

* `IsSingularOfWeight W k s` — the **Virasoro** notion: `s ≠ 0`, `s ∈ 𝒱ₖ` with `k > 0`, and
  `Lₙ s = 0` for all `n > 0`.  This is the condition an explicit computation verifies (it is
  a finite linear system: only `L₁, …, L_k` can act nontrivially).
* `IsStronglySingularOfWeight W k s` — the **vertex-algebra** notion: additionally
  `u₍ₙ₎ s = 0` for every homogeneous `u ∈ 𝒱ₘ` and every `n ≥ m`, i.e. *every* positive mode of
  *every* field annihilates `s`.  Since `Lₙ = ω₍ₙ₊₁₎` and `ω ∈ 𝒱₂`, this implies the Virasoro
  notion (`IsStronglySingularOfWeight.toIsSingularOfWeight`).

⚠ **The Virasoro notion alone does NOT make the generated ideal proper**, and this file is
careful not to pretend otherwise.  The tempting argument — "everything in `(s)` has weight
`≥ wt s > 0`, and `𝟙` has weight `0`" — is *false as stated*: a mode `u₍ₙ₎` with `n ≥ wt u`
*lowers* weight without bound, so an ideal is never contained in a "weight `≥ k`" subspace
merely because its generator is.  Concretely, in a **simple** affine VOA every `x ∈ 𝒱₁ = 𝔤`
satisfies `Lₙ x = 0` for `n > 0` (it is primary), yet `(x) = 𝒱` — indeed `y₍₁₎x = k⟨x,y⟩𝟙`
reaches the vacuum in one step.  What fails for such an `x` is precisely strong singularity:
`y₍₁₎x ≠ 0` with `wt y = 1 ≤ 1`.

The weight argument *does* work one layer deep, and that much is proved here:
`smul_mem_wtGE` (`u₍ₙ₎s ∈ 𝒱_{≥k}` for strongly singular `s`) together with
`vacuum_not_mem_wtGE`.  Turning that into properness of the whole ideal would need
`(s) = span {u₍ₙ₎s}` (Lepowsky–Li Prop. 4.5.6), which needs weak associativity and is **not**
in the repo.  So properness is obtained instead by the **invariant-form** route, which is
both shorter and unconditional.

## The mechanism actually used: the radical of the invariant form

`Core.BilinearForm` already proves that the **left** radical of a fully invariant form is an
ideal (`InvariantForm.radical_isIdeal`), and `Core.InvariantFormFHL2` produces a fully
invariant normalised form `canonicalInvariantForm` unconditionally (given `𝟙 ≠ 0` and
`L₁𝒱₁ = 0`).  A normalised form has `(𝟙|𝟙) = 1 ≠ 0`, so **its radical is a proper ideal**.
Hence any singular vector lying in a radical generates a proper ideal.  Two independent
criteria put a singular vector there:

* `mem_rightRadical_of_stronglySingular` — a **strongly** singular vector is orthogonal to
  everything, `(x|s) = 0`: write `x = x₍₋₁₎𝟙` and expand by full invariance; every term is
  `(𝟙 | (L₁ʲx)₍₂p-1-j₎ s)` with `2p-1-j ≥ p-j = wt(L₁ʲx)` as soon as `p ≥ 1`, so every term is
  killed by strong singularity, while `p = 0` is killed by weight orthogonality.  This needs
  the **right** radical to be an ideal, which is proved here (`rightRadical_isIdeal`) by
  downward induction on the weight of the acting state — the `j = 0` term of full invariance
  is `(a|u₍ₙ₎b)`, and all `j ≥ 1` corrections involve `L₁ʲu` of *strictly smaller* weight.
* `mem_leftRadical_of_shapovalov` — a **Virasoro** singular vector `s` with vanishing
  Shapovalov pairing `s₍₂ₖ₋₁₎x = 0` for all `x ∈ 𝒱ₖ` is in the left radical.  Here
  `L₁s = 0` collapses the full-invariance sum to its `j = 0` term, giving
  `(s|x) = (-1)^k (𝟙 | s₍₂ₖ₋₁₎x)`, and `s₍₂ₖ₋₁₎x ∈ 𝒱_{wt x - k}` pairs with `𝟙 ∈ 𝒱₀` only in
  weight `k`.  *This is the criterion an explicit computation should aim at*: it is a
  finite rank condition on the single weight space `𝒱ₖ`, exactly the statement that `s` is in
  the radical of the level-`k` Shapovalov/Gram matrix — which is how the degenerate values of
  `c` (or of the level) are found in the first place.

## Contents

* `IsSingularOfWeight`, `IsSingular`, `IsStronglySingularOfWeight`, `IsStronglySingular` (a).
* `idealGen W s`, `idealGen_isIdeal`, `mem_idealGen_self`, `idealGen_le` (b).
* `idealGen_isGradedIdeal` (c) — immediate from `QuotVOA.isGradedIdeal_of_isIdeal` (every
  VOA ideal is graded), which is the form `Core.QuotientVOA` wants.
* `wtGE`, `vacuum_not_mem_wtGE`, `smul_mem_wtGE` — the weight argument, exactly as far as it
  is true (d, partial, see the warning above).
* `vacuum_not_mem_idealGen_of_le`, `idealGen_proper_of_stronglySingular`,
  `idealGen_proper_of_shapovalov` — properness (d).
* `not_isSimple_of_stronglySingular`, `not_isSimple_of_shapovalov` and their
  hypothesis-free-in-the-form versions `…_FHL` — the bridge theorem (e).
* `quotientBySingular`, `quotientBySingular_centralCharge`, `mkQ_singular_eq_zero`,
  `quotientBySingular_vacuum_ne_zero` (f).

## Recorded, NOT proved (the converse direction, per the task statement)

For the two families this workflow targets, the maximal proper ideal is *generated by*
singular vectors — this is a representation-theoretic input, not a formal consequence of the
definitions, and nothing here assumes it:

* **Virasoro.** `VirUniv c = U(Vir)/J(c)` is the universal vacuum module `V(c,0)`; for
  `c = c_{p,q} = 1 - 6(p-q)²/(pq)` its maximal ideal is generated by the single singular
  vector at level `(p-1)(q-1)` (Feigin–Fuchs, Astashkevich), and the simple quotient is the
  minimal-model VOA `L(c,0)`.
* **Affine.** For `V^k(𝔤)` at admissible level the maximal ideal is generated by one singular
  vector (Kac–Kazhdan; Gorelik–Kac); at `𝔰𝔩₂`, level `-4/3`, it sits in weight `3` — the
  vector Linshaw–Qi use to force `10c = 0`.

## Naming note

The **universal** Virasoro vacuum module is `VirUniv c` (`Foundations.VirasoroModule`), and
`L(c,0)` denotes the *simple* quotient.  The intended reading of `quotientBySingular` in the
Virasoro case is "`L(c,0) = VirUniv c / (s)`".

## Status

`sorry`-free / axiom-free.  Every statement below is proved; the only mathematical inputs
taken from elsewhere are `Core.BilinearForm` (`radical_isIdeal`, `orthogonal_of_ne`),
`Core.InvariantFormFHL2` (`canonicalInvariantForm`) and `Core.QuotientVOA`
(`isGradedIdeal_of_isIdeal`, `quotientVOA'`).  Verified with `#print axioms`:
`idealGen_isIdeal`, `idealGen_isGradedIdeal`, `vacuum_not_mem_wtGE`, `smul_mem_wtGE`,
`rightRadical_isIdeal`, `mem_rightRadical_of_stronglySingular`,
`mem_leftRadical_of_shapovalov`, `not_isSimple_of_stronglySingular_FHL`,
`not_isSimple_of_shapovalov_FHL`, `quotientBySingular`, `quotientBySingular_mkQ_smul`,
`le_maxGradedIdeal_of_proper` all report `[propext, Classical.choice, Quot.sound]` — no
`sorry`, no project axiom.

## Universal Virasoro specialization proved separately

`Examples.VirasoroSingularGram` proves that, in the universal Virasoro vacuum module,
a positive-weight state killed by `L₁` and `L₂` lies in the canonical radical. Creation-word
spanning and adjointness supply the pairing condition automatically. Independent such states
give factors of the actual partition Gram determinant. This does not extend the same claim to
arbitrary VOAs (the affine-primary counterexample above still applies), nor does it construct
the uniform minimal-model singular vectors or prove that their roots are simple.

## What is NOT here (and would be the natural next step)

`(s) = span {u₍ₙ₎s}` (Lepowsky–Li Prop. 4.5.6), which needs weak associativity
(`Core.WeakAssoc`, `Core.Borcherds`) and a downward induction on the mode index.  With it,
`smul_mem_wtGE` + `vacuum_not_mem_wtGE` would give properness for a strongly singular vector
with no invariant form at all, and the concrete cases would not have to supply `𝟙 ≠ 0` /
`L₁𝒱₁ = 0`.  Also missing: `IsSingularOfWeight → IsStronglySingularOfWeight` for a VOA
*generated by* `ω` (the Virasoro case), which would let a purely Virasoro computation feed
`not_isSimple_of_stronglySingular` directly instead of going through the Shapovalov
criterion.

## References
* Gannon §5.1.3 (ideals, simplicity, Def. 5.3.2); Lepowsky–Li §4.5 (ideals generated by a
  vector); Frenkel–Huang–Lepowsky, Li JPAA 96 (1994) 279–297 (the invariant form);
  Linshaw–Qi, arXiv:2601.12017 (deformation rigidity).
-/

set_option linter.style.longLine false

namespace VOA

open Module (End)
open scoped BigOperators

universe u

namespace SingVec

open VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1.  Singular vectors  (task (a)) -/

/-- A **singular vector of weight `k`** in the Virasoro sense: a nonzero homogeneous state of
*positive* conformal weight annihilated by every positive Virasoro mode,
`Lₙ s = 0` for `n > 0` (equivalently, by `L₁, …, L_k`, the higher ones vanishing by weight).
Also called a *primary* state of positive weight.

This is the notion an explicit computation verifies.  It is **weaker** than
`IsStronglySingularOfWeight` and, by itself, does *not* force the ideal `(s)` to be proper —
see the file docstring. -/
structure IsSingularOfWeight (W : VertexOperatorAlgebra 𝒱) (k : ℤ) (s : 𝒱) : Prop where
  /-- `s ≠ 0`. -/
  ne_zero : s ≠ 0
  /-- The weight is positive (so `s` is not a multiple of the vacuum). -/
  weight_pos : 0 < k
  /-- `s` is homogeneous of weight `k`. -/
  homogeneous : s ∈ W.grading k
  /-- Every **positive** Virasoro mode annihilates `s`: `Lₙ s = 0` for `n > 0`. -/
  annihilated : ∀ n : ℤ, 0 < n → W.L n s = 0

/-- `W` **has a singular vector** (Virasoro sense). -/
def IsSingular (W : VertexOperatorAlgebra 𝒱) (s : 𝒱) : Prop :=
  ∃ k : ℤ, IsSingularOfWeight W k s

/-- A **strongly singular vector of weight `k`** — the vertex-algebra notion: nonzero,
homogeneous of positive weight `k`, and annihilated by *every* positive mode of *every*
field, `u₍ₙ₎s = 0` for `u ∈ 𝒱ₘ` and `n ≥ m`.

The index convention: `u₍ₙ₎` maps `𝒱ₖ → 𝒱_{m+k-n-1}`, so `n ≥ m` is exactly the set of modes
that do not raise weight, i.e. the "annihilation" half.  For the Virasoro field `ω ∈ 𝒱₂` this
reads `ω₍ₙ₎ = L_{n-1}` with `n ≥ 2`, i.e. `Lₙ` with `n ≥ 1` — the Virasoro condition. -/
structure IsStronglySingularOfWeight (W : VertexOperatorAlgebra 𝒱) (k : ℤ) (s : 𝒱) : Prop where
  /-- `s ≠ 0`. -/
  ne_zero : s ≠ 0
  /-- The weight is positive. -/
  weight_pos : 0 < k
  /-- `s` is homogeneous of weight `k`. -/
  homogeneous : s ∈ W.grading k
  /-- Every non-weight-raising mode annihilates `s`: `u₍ₙ₎s = 0` for `u ∈ 𝒱ₘ`, `n ≥ m`. -/
  annihilated : ∀ (m : ℤ) (u : 𝒱), u ∈ W.grading m → ∀ n : ℤ, m ≤ n → W.smul u n s = 0

/-- `W` **has a strongly singular vector**. -/
def IsStronglySingular (W : VertexOperatorAlgebra 𝒱) (s : 𝒱) : Prop :=
  ∃ k : ℤ, IsStronglySingularOfWeight W k s

variable {W : VertexOperatorAlgebra 𝒱}

/-- Strong singularity implies Virasoro singularity: `Lₙ = ω₍ₙ₊₁₎` with `ω ∈ 𝒱₂`, and
`n > 0 ↔ n + 1 ≥ 2`. -/
theorem IsStronglySingularOfWeight.toIsSingularOfWeight {k : ℤ} {s : 𝒱}
    (hs : IsStronglySingularOfWeight W k s) : IsSingularOfWeight W k s where
  ne_zero := hs.ne_zero
  weight_pos := hs.weight_pos
  homogeneous := hs.homogeneous
  annihilated := by
    intro n hn
    rw [L_def, ← PreVertexAlgebra.smul_def]
    exact hs.annihilated 2 W.conformalVector W.conformal_mem (n + 1) (by omega)

theorem IsStronglySingular.toIsSingular {s : 𝒱} (hs : IsStronglySingular W s) :
    IsSingular W s :=
  ⟨hs.choose, hs.choose_spec.toIsSingularOfWeight⟩

/-! ## §2.  The ideal generated by a vector  (task (b)) -/

/-- The **ideal generated by `s`**: the smallest subspace containing `s` and closed under all
modes `u₍ₙ₎` (`Core.BilinearForm.IsIdeal`).  Defined as the infimum of all ideals containing
`s`; the family is nonempty (`⊤` is one), and an infimum of ideals is an ideal
(`idealGen_isIdeal`). -/
def idealGen (W : VertexOperatorAlgebra 𝒱) (s : 𝒱) : Submodule ℂ 𝒱 :=
  sInf {I : Submodule ℂ 𝒱 | s ∈ I ∧ W.IsIdeal I}

theorem mem_idealGen_self (W : VertexOperatorAlgebra 𝒱) (s : 𝒱) : s ∈ idealGen W s :=
  Submodule.mem_sInf.mpr fun _ hp => hp.1

/-- Minimality: `(s)` is contained in every ideal containing `s`. -/
theorem idealGen_le {I : Submodule ℂ 𝒱} {s : 𝒱} (hI : W.IsIdeal I) (hs : s ∈ I) :
    idealGen W s ≤ I :=
  sInf_le ⟨hs, hI⟩

/-- **`(s)` is an ideal**: membership in an infimum is membership in each member, and each
member absorbs every mode. -/
theorem idealGen_isIdeal (W : VertexOperatorAlgebra 𝒱) (s : 𝒱) : W.IsIdeal (idealGen W s) := by
  intro u v n hv
  rw [idealGen, Submodule.mem_sInf] at hv ⊢
  exact fun p hp => hp.2 u v n (hv p hp)

/-- **`(s)` is a graded ideal** — the hypothesis `Core.QuotientVOA` asks for.  In a VOA
this is automatic: every ideal is graded (`QuotVOA.isGradedIdeal_of_isIdeal`, proved by
splitting a member into `L₀`-eigencomponents). -/
theorem idealGen_isGradedIdeal (W : VertexOperatorAlgebra 𝒱) (s : 𝒱) :
    QuotVOA.IsGradedIdeal W (idealGen W s) :=
  QuotVOA.isGradedIdeal_of_isIdeal (idealGen_isIdeal W s)

theorem idealGen_ne_bot {s : 𝒱} (hs : s ≠ 0) : idealGen W s ≠ ⊥ := by
  intro h
  exact hs ((Submodule.mem_bot ℂ).mp (h ▸ mem_idealGen_self W s))

/-- An ideal containing `𝟙` is everything, so `𝟙 ∉ (s)` is exactly properness. -/
theorem idealGen_eq_top_iff {s : 𝒱} : idealGen W s = ⊤ ↔ W.vacuum ∈ idealGen W s := by
  constructor
  · intro h; rw [h]; exact Submodule.mem_top
  · exact QuotVOA.eq_top_of_vacuum_mem (idealGen_isIdeal W s)

/-! ## §3.  The weight argument, exactly as far as it is true  (task (d), first layer)

For a *strongly* singular `s` of weight `k`, the states `u₍ₙ₎s` all have weight `≥ k`: the
weight-lowering modes are precisely the ones that kill `s`.  Since `𝟙` has weight `0 < k`,
the **first layer** `𝒱·s` of the ideal misses the vacuum.  What is *not* available here is
that this first layer is already the whole ideal (Lepowsky–Li Prop. 4.5.6, which needs weak
associativity); §5 reaches properness by a different, complete route. -/

/-- The subspace of states of conformal weight `≥ k`. -/
def wtGE (W : VertexOperatorAlgebra 𝒱) (k : ℤ) : Submodule ℂ 𝒱 :=
  ⨆ n : ℤ, ⨆ (_ : k ≤ n), W.grading n

theorem mem_wtGE {k n : ℤ} (hkn : k ≤ n) {x : 𝒱} (hx : x ∈ W.grading n) : x ∈ wtGE W k :=
  le_iSup₂ (f := fun (m : ℤ) (_ : k ≤ m) => W.grading m) n hkn hx

/-- **The vacuum has weight `0`, so it is not of weight `≥ k` for `k > 0`** — by the
independence of the homogeneous components (`isInternal`). -/
theorem vacuum_not_mem_wtGE (W : VertexOperatorAlgebra 𝒱) (hvac : W.vacuum ≠ 0) {k : ℤ}
    (hk : 0 < k) : W.vacuum ∉ wtGE W k := by
  intro hmem
  have hle : wtGE W k ≤ ⨆ (n : ℤ) (_ : n ≠ 0), W.grading n := by
    refine iSup₂_le fun n hn => ?_
    exact le_iSup₂ (f := fun (m : ℤ) (_ : m ≠ 0) => W.grading m) n (by omega)
  exact hvac (Submodule.disjoint_def.mp
    (iSupIndep_def.mp W.isInternal.submodule_iSupIndep 0) W.vacuum W.vacuum_mem (hle hmem))

/-- **The first layer of `(s)` has weight `≥ k`.**  For homogeneous `u ∈ 𝒱ₘ` either `n ≥ m`,
and then `u₍ₙ₎s = 0` by strong singularity, or `n ≤ m-1`, and then
`u₍ₙ₎s ∈ 𝒱_{m+k-n-1}` with `m+k-n-1 ≥ k`. -/
theorem smul_mem_wtGE {k : ℤ} {s : 𝒱} (hs : IsStronglySingularOfWeight W k s) (u : 𝒱) (n : ℤ) :
    W.smul u n s ∈ wtGE W k := by
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun u => W.smul u n s ∈ wtGE W k)
    hutop ?_ ?_ ?_
  · intro m x hx
    by_cases hmn : m ≤ n
    · rw [hs.annihilated m x hx n hmn]
      exact Submodule.zero_mem _
    · exact mem_wtGE (by omega) (W.smul_mem_grading hx hs.homogeneous n)
  · change W.smul (0 : 𝒱) n s ∈ wtGE W k
    rw [W.smul_zero_left]
    exact Submodule.zero_mem _
  · intro x y hx hy
    rw [W.smul_add_left]
    exact Submodule.add_mem _ hx hy

/-! ## §4.  The two radicals of an invariant form

`Core.BilinearForm` defines `InvariantForm.leftRadical B = ker (·|·)` and proves it is an
ideal for a fully invariant `B` (`radical_isIdeal`).  We add the **right** radical and the
same statement for it; the two criteria of §5 use one each. -/

/-- The **right radical** `{b | ∀ a, (a|b) = 0}` of a bilinear form. -/
def rightRadical (B : InvariantForm W) : Submodule ℂ 𝒱 := LinearMap.ker B.form.flip

theorem mem_rightRadical {B : InvariantForm W} {b : 𝒱} :
    b ∈ rightRadical B ↔ ∀ a : 𝒱, B.form a b = 0 := by
  constructor
  · intro h a
    have h' : B.form.flip b = 0 := LinearMap.mem_ker.mp h
    have := LinearMap.congr_fun h' a
    rwa [LinearMap.flip_apply, LinearMap.zero_apply] at this
  · intro h
    refine LinearMap.mem_ker.mpr (LinearMap.ext fun a => ?_)
    rw [LinearMap.flip_apply, LinearMap.zero_apply]
    exact h a

/-- The inductive step of `rightRadical_isIdeal`, isolated so that the outer induction on the
weight is a two-line wrapper.  Full invariance applied with mode index `2·wt - n - 2` has
`(u₍₂ᵂᵗ⁻ⁿ⁻²₎a | b)` on the left — zero because `b` is in the right radical — and on the right
the `j = 0` term `(a | u₍ₙ₎b)` we want, plus corrections `(a | (L₁ʲu)₍ₙ₋ⱼ₎b)` whose acting
state `L₁ʲu` has weight `wt - j < wt`.  For `wt < 0` the weight space is `⊥`. -/
theorem rightRadical_step {B : InvariantForm W} (hB : B.IsFullyInvariant) {b : 𝒱}
    (hb : ∀ a : 𝒱, B.form a b = 0) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt) (n : ℤ) (a : 𝒱)
    (ih : ∀ wt' : ℤ, wt' < wt → ∀ u' : 𝒱, u' ∈ W.grading wt' → ∀ (n' : ℤ) (a' : 𝒱),
      B.form a' (W.smul u' n' b) = 0) :
    B.form a (W.smul u n b) = 0 := by
  by_cases hneg : wt < 0
  · rw [W.positivity wt hneg] at hu
    rw [(Submodule.mem_bot ℂ).mp hu, W.smul_zero_left]
    exact map_zero (B.form a)
  · have key := hB wt u hu (2 * wt - n - 2) a b
    rw [hb (W.smul u (2 * wt - n - 2) a), eq_comm, smul_eq_mul] at key
    have hne : ((-1 : ℂ)) ^ wt ≠ 0 := by
      apply zpow_ne_zero
      norm_num
    have hS := (mul_eq_zero.mp key).resolve_left hne
    have hzero : ∀ j ∈ Finset.range (wt.toNat + 1), j ≠ 0 →
        ((j.factorial : ℂ)⁻¹) • B.form a (W.smul (((W.L 1) ^ j) u)
          (2 * wt - (2 * wt - n - 2) - 2 - (j : ℤ)) b) = 0 := by
      intro j _ hj
      have hmem : ((W.L 1) ^ j) u ∈ W.grading (wt - (j : ℤ)) := L_one_pow_mem W hu j
      rw [ih (wt - (j : ℤ)) (by omega) _ hmem _ a, smul_zero]
    have hidx : (2 * wt - (2 * wt - n - 2) - 2 - ((0 : ℕ) : ℤ)) = n := by push_cast; ring
    rw [Finset.sum_eq_single 0 hzero
        (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h),
      pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
      hidx] at hS
    exact hS

/-- The homogeneous case of `rightRadical_isIdeal`, by induction on the weight of the acting
state (packaged through `wt.toNat ≤ N`). -/
theorem rightRadical_smul_homog {B : InvariantForm W} (hB : B.IsFullyInvariant) {b : 𝒱}
    (hb : ∀ a : 𝒱, B.form a b = 0) :
    ∀ (N : ℕ) (wt : ℤ), wt.toNat ≤ N → ∀ u : 𝒱, u ∈ W.grading wt → ∀ (n : ℤ) (a : 𝒱),
      B.form a (W.smul u n b) = 0 := by
  intro N
  induction N with
  | zero =>
    intro wt hwt u hu n a
    refine rightRadical_step hB hb hu n a fun wt' hlt u' hu' n' a' => ?_
    rw [W.positivity wt' (by omega)] at hu'
    rw [(Submodule.mem_bot ℂ).mp hu', W.smul_zero_left]
    exact map_zero (B.form a')
  | succ N ih =>
    intro wt hwt u hu n a
    exact rightRadical_step hB hb hu n a
      fun wt' hlt u' hu' n' a' => ih wt' (by omega) u' hu' n' a'

/-- **The right radical of a fully invariant form is an ideal.**  (The left-radical
statement is `Core.BilinearForm`'s `InvariantForm.radical_isIdeal`; there the full-invariance
identity gives the result in one step, here it has to be inverted, which is what the weight
induction of `rightRadical_step` does.) -/
theorem rightRadical_isIdeal {B : InvariantForm W} (hB : B.IsFullyInvariant) :
    W.IsIdeal (rightRadical B) := by
  intro u v n hv
  rw [mem_rightRadical] at hv ⊢
  intro a
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => ∀ (n : ℤ) (a : 𝒱), B.form a (W.smul u n v) = 0) hutop ?_ ?_ ?_ n a
  · intro i x hx n a
    exact rightRadical_smul_homog hB hv i.toNat i le_rfl x hx n a
  · intro n a
    rw [W.smul_zero_left]
    exact map_zero (B.form a)
  · intro x y hx hy n a
    rw [W.smul_add_left, map_add, hx n a, hy n a, add_zero]

/-- A normalised form has `(𝟙|𝟙) = 1 ≠ 0`, so `𝟙` is in neither radical. -/
theorem vacuum_not_mem_rightRadical {B : InvariantForm W} (hn : B.Normalized) :
    W.vacuum ∉ rightRadical B := by
  intro h
  have := (mem_rightRadical.mp h) W.vacuum
  rw [InvariantForm.Normalized.vacuum_self hn] at this
  exact absurd this (by norm_num)

theorem vacuum_not_mem_leftRadical {B : InvariantForm W} (hn : B.Normalized) :
    W.vacuum ∉ InvariantForm.leftRadical B := by
  intro h
  have hz := DFunLike.congr_fun (InvariantForm.mem_leftRadical.mp h) W.vacuum
  rw [LinearMap.zero_apply, InvariantForm.Normalized.vacuum_self hn] at hz
  exact absurd hz (by norm_num)

/-! ## §5.  Two criteria putting a singular vector into a radical -/

/-- **A strongly singular vector is orthogonal to everything**: `(x|s) = 0` for all `x`.
Write `x = x₍₋₁₎𝟙` and expand by full invariance: for `x ∈ 𝒱ₚ` with `p ≥ 1` every term is
`(𝟙 | (L₁ʲx)₍₂ₚ₋₁₋ⱼ₎s)` with `2p-1-j ≥ p-j = wt (L₁ʲ x)`, hence zero by strong singularity;
`p = 0` is zero because `𝒱₀ ⟂ 𝒱ₖ` for `k ≠ 0`; `p < 0` is the zero space. -/
theorem mem_rightRadical_of_stronglySingular {B : InvariantForm W} (hB : B.IsFullyInvariant)
    {k : ℤ} {s : 𝒱} (hs : IsStronglySingularOfWeight W k s) : s ∈ rightRadical B := by
  rw [mem_rightRadical]
  intro x
  have hxtop : x ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun x => B.form x s = 0) hxtop ?_ ?_ ?_
  · intro p y hy
    rcases lt_trichotomy p 0 with hp | hp | hp
    · rw [W.positivity p hp] at hy
      rw [(Submodule.mem_bot ℂ).mp hy, map_zero, LinearMap.zero_apply]
    · subst hp
      exact InvariantForm.orthogonal_of_ne B (ne_of_lt hs.weight_pos) hy hs.homogeneous
    · have key := hB p y hy (-1) W.vacuum s
      rw [W.smul_vacuum_neg_one] at key
      rw [key]
      have hterm : ∀ j ∈ Finset.range (p.toNat + 1),
          ((j.factorial : ℂ)⁻¹) • B.form W.vacuum (W.smul (((W.L 1) ^ j) y)
            (2 * p - (-1) - 2 - (j : ℤ)) s) = 0 := by
        intro j _
        have hmem : ((W.L 1) ^ j) y ∈ W.grading (p - (j : ℤ)) := L_one_pow_mem W hy j
        rw [hs.annihilated (p - (j : ℤ)) _ hmem _ (by omega), map_zero, smul_zero]
      rw [Finset.sum_eq_zero hterm, smul_zero]
  · change B.form (0 : 𝒱) s = 0
    rw [map_zero, LinearMap.zero_apply]
  · intro x y hx hy
    rw [map_add, LinearMap.add_apply, hx, hy, add_zero]

/-- **The Shapovalov criterion.**  For a *Virasoro* singular vector `s ∈ 𝒱ₖ`, full
invariance collapses (only `j = 0` survives, since `L₁s = 0`) to
`(s|x) = (-1)^k (𝟙 | s₍₂ₖ₋₁₎x)`.  As `s₍₂ₖ₋₁₎x ∈ 𝒱_{wt x - k}` pairs with `𝟙 ∈ 𝒱₀` only when
`wt x = k`, the single hypothesis `s₍₂ₖ₋₁₎ 𝒱ₖ = 0` — the vanishing of the level-`k` Shapovalov
pairing against `s` — puts `s` in the left radical.

This is the practical entry point: `hpair` is a finite linear condition on one weight
space. -/
theorem mem_leftRadical_of_shapovalov {B : InvariantForm W} (hB : B.IsFullyInvariant)
    {k : ℤ} {s : 𝒱} (hs : IsSingularOfWeight W k s)
    (hpair : ∀ x ∈ W.grading k, W.smul s (2 * k - 1) x = 0) :
    s ∈ InvariantForm.leftRadical B := by
  rw [InvariantForm.mem_leftRadical]
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.zero_apply]
  have hxtop : x ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun x => B.form s x = 0) hxtop ?_ ?_ ?_
  · intro p y hy
    have key := hB k s hs.homogeneous (-1) W.vacuum y
    rw [W.smul_vacuum_neg_one] at key
    have hzero : ∀ j ∈ Finset.range (k.toNat + 1), j ≠ 0 →
        ((j.factorial : ℂ)⁻¹) • B.form W.vacuum (W.smul (((W.L 1) ^ j) s)
          (2 * k - (-1) - 2 - (j : ℤ)) y) = 0 := by
      intro j _ hj
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      rw [pow_succ, Module.End.mul_apply, hs.annihilated 1 (by norm_num), map_zero,
        W.smul_zero_left, map_zero, smul_zero]
    have hidx : (2 * k - (-1) - 2 - ((0 : ℕ) : ℤ)) = 2 * k - 1 := by push_cast; ring
    rw [Finset.sum_eq_single 0 hzero
        (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h),
      pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
      hidx] at key
    rcases eq_or_ne p k with rfl | hpk
    · rw [hpair y hy, map_zero, smul_zero] at key
      exact key
    · have hmem : W.smul s (2 * k - 1) y ∈ W.grading (p - k) := by
        have h := W.smul_mem_grading hs.homogeneous hy (2 * k - 1)
        rwa [show (k + p - (2 * k - 1) - 1 : ℤ) = p - k by ring] at h
      rw [InvariantForm.orthogonal_of_ne B (by omega : (0 : ℤ) ≠ p - k) W.vacuum_mem hmem,
        smul_zero] at key
      exact key
  · exact map_zero (B.form s)
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

/-! ## §6.  Properness of `(s)`  (task (d)) -/

/-- Properness by comparison: if `(s)` sits inside an ideal missing the vacuum, it misses the
vacuum. -/
theorem vacuum_not_mem_idealGen_of_le {s : 𝒱} {J : Submodule ℂ 𝒱} (hJ : W.IsIdeal J)
    (hsJ : s ∈ J) (hv : W.vacuum ∉ J) : W.vacuum ∉ idealGen W s :=
  fun h => hv (idealGen_le hJ hsJ h)

/-- **`(s)` is proper for a strongly singular `s`** — via the right radical of a normalised
fully invariant form. -/
theorem idealGen_proper_of_stronglySingular {B : InvariantForm W} (hB : B.IsFullyInvariant)
    (hn : B.Normalized) {k : ℤ} {s : 𝒱} (hs : IsStronglySingularOfWeight W k s) :
    W.vacuum ∉ idealGen W s :=
  vacuum_not_mem_idealGen_of_le (rightRadical_isIdeal hB)
    (mem_rightRadical_of_stronglySingular hB hs) (vacuum_not_mem_rightRadical hn)

/-- **`(s)` is proper for a Virasoro singular vector with vanishing Shapovalov pairing** —
via the left radical. -/
theorem idealGen_proper_of_shapovalov {B : InvariantForm W} (hB : B.IsFullyInvariant)
    (hn : B.Normalized) {k : ℤ} {s : 𝒱} (hs : IsSingularOfWeight W k s)
    (hpair : ∀ x ∈ W.grading k, W.smul s (2 * k - 1) x = 0) :
    W.vacuum ∉ idealGen W s :=
  vacuum_not_mem_idealGen_of_le (InvariantForm.radical_isIdeal hB)
    (mem_leftRadical_of_shapovalov hB hs hpair) (vacuum_not_mem_leftRadical hn)

theorem idealGen_ne_top_of_proper {s : 𝒱} (h : W.vacuum ∉ idealGen W s) :
    idealGen W s ≠ ⊤ :=
  fun htop => h (idealGen_eq_top_iff.mp htop)

/-! ## §7.  The bridge: a singular vector obstructs simplicity  (task (e)) -/

/-- **A nonzero vector generating a proper ideal obstructs simplicity.**  `(s)` is an ideal,
it is not `⊥` (it contains `s ≠ 0`) and not `⊤` (it misses `𝟙`), so `W` has a nontrivial
ideal. -/
theorem not_isSimple_of_idealGen_proper {s : 𝒱} (hs0 : s ≠ 0)
    (hv : W.vacuum ∉ idealGen W s) : ¬ W.IsSimple := by
  intro hsimple
  rcases hsimple.2 (idealGen W s) (idealGen_isIdeal W s) with h | h
  · exact idealGen_ne_bot hs0 h
  · exact idealGen_ne_top_of_proper hv h

/-- **A strongly singular vector of positive weight obstructs simplicity**, given a
normalised fully invariant form.  So the simple quotient of `W` is a *proper* quotient. -/
theorem not_isSimple_of_stronglySingular {B : InvariantForm W} (hB : B.IsFullyInvariant)
    (hn : B.Normalized) {k : ℤ} {s : 𝒱} (hs : IsStronglySingularOfWeight W k s) :
    ¬ W.IsSimple :=
  not_isSimple_of_idealGen_proper hs.ne_zero (idealGen_proper_of_stronglySingular hB hn hs)

/-- **The same, with no form to supply**: the canonical FHL form is fully invariant and
normalised for any `W` with `𝟙 ≠ 0` and `L₁𝒱₁ = 0` (`Core.InvariantFormFHL2`).  This is the
form of the bridge theorem the concrete cases should use. -/
theorem not_isSimple_of_stronglySingular_FHL (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {k : ℤ} {s : 𝒱}
    (hs : IsStronglySingularOfWeight W k s) : ¬ W.IsSimple :=
  not_isSimple_of_stronglySingular (canonicalInvariantForm_isFullyInvariant hne hqp)
    (canonicalInvariantForm_normalized hne hqp) hs

/-- **A Virasoro singular vector with vanishing Shapovalov pairing obstructs simplicity.** -/
theorem not_isSimple_of_shapovalov {B : InvariantForm W} (hB : B.IsFullyInvariant)
    (hn : B.Normalized) {k : ℤ} {s : 𝒱} (hs : IsSingularOfWeight W k s)
    (hpair : ∀ x ∈ W.grading k, W.smul s (2 * k - 1) x = 0) : ¬ W.IsSimple :=
  not_isSimple_of_idealGen_proper hs.ne_zero (idealGen_proper_of_shapovalov hB hn hs hpair)

/-- **The same, with no form to supply.** -/
theorem not_isSimple_of_shapovalov_FHL (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {k : ℤ} {s : 𝒱} (hs : IsSingularOfWeight W k s)
    (hpair : ∀ x ∈ W.grading k, W.smul s (2 * k - 1) x = 0) : ¬ W.IsSimple :=
  not_isSimple_of_shapovalov (canonicalInvariantForm_isFullyInvariant hne hqp)
    (canonicalInvariantForm_normalized hne hqp) hs hpair

/-! ## §8.  The quotient by a singular vector  (task (f))

`Core.QuotientVOA` supplies the whole VOA structure on `𝒱 ⧸ I` for an arbitrary ideal
(gradedness being automatic), so this is a one-liner.  Note the quotient is *not* claimed to
be simple: `(s)` need not be the maximal ideal.  For the maximal one use
`QuotVOA.maxQuotientVOA`, which `QuotVOA.isSimple_maxQuotientVOA'` does prove simple;
`le_maxGradedIdeal_of_proper` below records that `(s)` sits inside it, so
`𝒱/(s) ↠ 𝒱/max = L(c,0)`. -/

/-- **The quotient VOA `𝒱 / (s)`** — same central charge, `s` killed, vacuum surviving
whenever `(s)` is proper. -/
noncomputable def quotientBySingular (W : VertexOperatorAlgebra 𝒱) (s : 𝒱) :
    VertexOperatorAlgebra (𝒱 ⧸ idealGen W s) :=
  QuotVOA.quotientVOA' W (idealGen W s) (idealGen_isIdeal W s)

@[simp] theorem quotientBySingular_centralCharge (W : VertexOperatorAlgebra 𝒱) (s : 𝒱) :
    (quotientBySingular W s).centralCharge = W.centralCharge := rfl

@[simp] theorem quotientBySingular_vacuum (W : VertexOperatorAlgebra 𝒱) (s : 𝒱) :
    (quotientBySingular W s).vacuum = (idealGen W s).mkQ W.vacuum := rfl

/-- The singular vector dies in the quotient. -/
theorem mkQ_singular_eq_zero (W : VertexOperatorAlgebra 𝒱) (s : 𝒱) :
    (idealGen W s).mkQ s = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (mem_idealGen_self W s)

/-- The quotient is **nonzero** exactly when `(s)` is proper: the vacuum survives. -/
theorem quotientBySingular_vacuum_ne_zero {s : 𝒱} (hv : W.vacuum ∉ idealGen W s) :
    (quotientBySingular W s).vacuum ≠ 0 :=
  fun h => hv ((Submodule.Quotient.mk_eq_zero _).mp h)

/-- The products descend: `[u₍ₙ₎v] = [u]₍ₙ₎[v]`. -/
theorem quotientBySingular_mkQ_smul (W : VertexOperatorAlgebra 𝒱) (s : 𝒱) (u : 𝒱) (n : ℤ)
    (v : 𝒱) :
    (quotientBySingular W s).smul ((idealGen W s).mkQ u) n ((idealGen W s).mkQ v)
      = (idealGen W s).mkQ (W.smul u n v) :=
  QuotVOA.quotientVOA_mkQ_smul (idealGen_isIdeal W s)
    (QuotVOA.isGradedIdeal_of_isIdeal (idealGen_isIdeal W s)) u n v

/-- `(s)` is contained in the maximal proper ideal, so the simple quotient
`QuotVOA.maxQuotientVOA W` is a further quotient of `𝒱/(s)`.  (Equality — "the maximal ideal
is generated by the singular vector" — is the representation-theoretic input recorded, not
proved, in the file docstring.) -/
theorem le_maxGradedIdeal_of_proper {s : 𝒱} (hv : W.vacuum ∉ idealGen W s) :
    idealGen W s ≤ QuotVOA.maxGradedIdeal W :=
  QuotVOA.le_maxGradedIdeal' (idealGen_isIdeal W s) hv

end SingVec

end VOA
