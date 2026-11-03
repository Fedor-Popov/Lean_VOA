/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.PoissonDescent

/-!
# `C₂`-cofinite ⟹ finitely generated (Gannon 5.3.11a) — reduced to one degree step

The finite-generation half of Zhu's `C₂`-cofiniteness theory: if `C2Cofinite W`, then `𝒱` is
spanned by iterated products `s^{i₁}₍₋m₁₎⋯s^{iₖ}₍₋mₖ₎𝟙` of lifts `S` of an `A₂(𝒱)`-basis
(`iterProdSpan W S = ⊤`). Built here up to a single, precisely-isolated degree step:

  * `O₂_eq_span_homGen`  — `O₂` is a **graded** submodule (= span of its *homogeneous* generators
    `a₍₋₂₎b`, `a ∈ 𝒱ₚ`, `b ∈ 𝒱_q`), so the PBW induction can run per-degree.
  * `factor_deg_lt` — the strict factor-degree drop for a nonzero `a₍₋₂₎b ∈ 𝒱ₙ`.
  * `iterProdSpan_eq_top_of_O₂_le` — the lattice reduction `S ⊆ T` + `span S ⊔ O₂ = ⊤` + `(★)` ⟹ `T = ⊤`.
  * `grading_le_of_step` — the degree strong-induction wrapper (bounded below by `positivity`).
  * **`iterProdSpan_eq_top_of_degStep`** — the full theorem `iterProdSpan W S = ⊤` from ONE explicit
    per-degree closure hypothesis `degStep`.

## Status
`sorry`-free, with no project axioms.  The graded-`O₂` structure, the degree
bookkeeping, the lattice + well-founded-induction reduction `iterProdSpan_eq_top_of_degStep`
(5.3.11a modulo one per-degree step `degStep`) are all `[propext, Classical.choice, Quot.sound]`.

The `degStep` hypothesis is itself **discharged unconditionally** in `Modules.FiniteGenerationProof`
(`degStep_unconditional`, via the convergent `mode_iterate` master peeling `genPeel_master`), so
5.3.11a holds *unconditionally* there (`iterProdSpan_eq_top`) — no `sorry`, no new axiom.

## Original development note

We copy the infrastructure
(`IsHomog`, `IsIterProd`, `iterProdSpan`, the membership/closure/grading lemmas) and add the
genuine new ingredients for `(★)`:

  * `O₂_eq_span_homGen`  — `O₂` is a **graded** submodule: it equals the span of its
     *homogeneous* generators `a₍₋₂₎b` with `a ∈ 𝒱ₚ`, `b ∈ 𝒱_q`.  (Bilinear decomposition of
     a general generator into homogeneous ones.)  This is what lets the PBW induction run on a
     fixed degree.
  * `homGen_mem_grading`  — a homogeneous `O₂`-generator `a₍₋₂₎b` (a∈𝒱ₚ, b∈𝒱_q) lies in
     `𝒱_{p+q+1}`, and (nonzero ⇒ `p,q ≥ 0` by `positivity`) the two factor degrees are
     **strictly below** `p+q+1` — the degree drop.
  * `iterProdSpan_eq_top_of_O₂_le`  — the lattice reduction:  `S ⊆ T` + `span S ⊔ O₂ = ⊤`
     + `(★)` ⟹ `T = ⊤`.
  * `grading_le_of_step`  — the **degree strong-induction wrapper** (bounded below by
     `positivity`): to prove `∀ n, 𝒱ₙ ≤ T` it suffices to prove the single degree step
     `(∀ k<n, 𝒱ₖ ≤ T) → 𝒱ₙ ≤ T`.
  * `iterProdSpan_eq_top_of_degStep`  — assembling the above into a clean conditional: the
     full theorem follows from one explicit per-degree closure hypothesis, isolating exactly
     the remaining `mode_iterate` peeling content (the precise blocker; see the closing note).

All lemmas below are `sorry`-free / axiom-free.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Supporting infrastructure
(general lemmas used below). -/

/-- **Homogeneity predicate**: `x` is homogeneous iff it lies in some grading piece. -/
def IsHomog (W : VertexOperatorAlgebra 𝒱) (x : 𝒱) : Prop := ∃ n : ℤ, x ∈ W.grading n

/-- The set of all homogeneous vectors spans `𝒱` (`⊤ = span (⋃ₙ 𝒱ₙ)`, from `isInternal`). -/
theorem span_homog_eq_top (W : VertexOperatorAlgebra 𝒱) :
    Submodule.span ℂ {x | IsHomog W x} = ⊤ := by
  rw [eq_top_iff, ← W.isInternal.submodule_iSup_eq_top, Submodule.iSup_eq_span]
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, hn⟩

/-- The set of iterated products `s^{i₁}₍₋m₁₎ ⋯ s^{iₖ}₍₋mₖ₎ 𝟙` with `s^{i_j} ∈ S`, `m_j ≥ 1`. -/
inductive IsIterProd (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱) : 𝒱 → Prop
  | vacuum : IsIterProd W S W.vacuum
  | step (s : 𝒱) (hs : s ∈ S) (m : ℤ) (hm : 1 ≤ m) (x : 𝒱) (hx : IsIterProd W S x) :
      IsIterProd W S (W.smul s (-m) x)

/-- The submodule `T` spanned by the iterated products (Gannon 5.3.11a). -/
def iterProdSpan (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | IsIterProd W S x}

theorem vacuum_mem_iterProdSpan (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱) :
    W.vacuum ∈ iterProdSpan W S :=
  Submodule.subset_span (IsIterProd.vacuum)

theorem smul_mem_iterProdSpan (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    {s : 𝒱} (hs : s ∈ S) {m : ℤ} (hm : 1 ≤ m) {x : 𝒱} (hx : x ∈ iterProdSpan W S) :
    W.smul s (-m) x ∈ iterProdSpan W S := by
  refine Submodule.span_induction
    (p := fun x _ => W.smul s (-m) x ∈ iterProdSpan W S) ?_ ?_ ?_ ?_ hx
  · intro y hy
    exact Submodule.subset_span (IsIterProd.step s hs m hm y hy)
  · simp only [W.smul_zero_right]; exact (iterProdSpan W S).zero_mem
  · intro y z _ _ hy hz
    simp only [W.smul_add_right]; exact (iterProdSpan W S).add_mem hy hz
  · intro c y _ hy
    simp only [W.smul_smul_right]; exact (iterProdSpan W S).smul_mem c hy

theorem subset_iterProdSpan (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱) {s : 𝒱} (hs : s ∈ S) :
    s ∈ iterProdSpan W S := by
  have hmem : W.smul s (-(1 : ℤ)) W.vacuum ∈ iterProdSpan W S :=
    smul_mem_iterProdSpan W S hs (le_refl 1) (vacuum_mem_iterProdSpan W S)
  simpa using hmem

/-- `span ℂ S ≤ T` for the `S`-iterated-product span. -/
theorem span_S_le_iterProdSpan (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱) :
    Submodule.span ℂ S ≤ iterProdSpan W S := by
  rw [Submodule.span_le]; intro s hs; exact subset_iterProdSpan W S hs

/-! ## `O₂` is a graded submodule (span of its homogeneous generators). -/

/-- The set of **homogeneous** `O₂`-generators `a₍₋₂₎b`, `a ∈ 𝒱ₚ`, `b ∈ 𝒱_q`. -/
def O₂homGen (W : VertexOperatorAlgebra 𝒱) : Set 𝒱 :=
  {x | ∃ (p q : ℤ) (a b : 𝒱), a ∈ W.grading p ∧ b ∈ W.grading q ∧ x = W.smul a (-2) b}

/-- For homogeneous `a` and arbitrary `b`, `a₍₋₂₎b` lies in the span of homogeneous generators
(decompose `b` into homogeneous pieces; `b ↦ a₍₋₂₎b` is `ℂ`-linear). -/
theorem genHomA_mem_span_homGen (W : VertexOperatorAlgebra 𝒱) {p : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading p) (b : 𝒱) :
    W.smul a (-2) b ∈ Submodule.span ℂ (O₂homGen W) := by
  have hb : b ∈ Submodule.span ℂ {x | IsHomog W x} := by rw [span_homog_eq_top]; trivial
  refine Submodule.span_induction
    (p := fun b _ => W.smul a (-2) b ∈ Submodule.span ℂ (O₂homGen W)) ?_ ?_ ?_ ?_ hb
  · rintro y ⟨q, hq⟩
    exact Submodule.subset_span ⟨p, q, a, y, ha, hq, rfl⟩
  · simp
  · intro y z _ _ hy hz
    rw [W.smul_add_right]; exact (Submodule.span ℂ (O₂homGen W)).add_mem hy hz
  · intro c y _ hy
    rw [W.smul_smul_right]; exact (Submodule.span ℂ (O₂homGen W)).smul_mem c hy

/-- For arbitrary `a, b`, `a₍₋₂₎b` lies in the span of homogeneous generators (decompose `a`;
`a ↦ a₍₋₂₎b` is `ℂ`-linear). -/
theorem gen_mem_span_homGen (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) :
    W.smul a (-2) b ∈ Submodule.span ℂ (O₂homGen W) := by
  have ha : a ∈ Submodule.span ℂ {x | IsHomog W x} := by rw [span_homog_eq_top]; trivial
  refine Submodule.span_induction
    (p := fun a _ => W.smul a (-2) b ∈ Submodule.span ℂ (O₂homGen W)) ?_ ?_ ?_ ?_ ha
  · rintro y ⟨p, hp⟩; exact genHomA_mem_span_homGen W hp b
  · simp
  · intro y z _ _ hy hz
    rw [W.smul_add_left]; exact (Submodule.span ℂ (O₂homGen W)).add_mem hy hz
  · intro c y _ hy
    rw [W.smul_smul_left]; exact (Submodule.span ℂ (O₂homGen W)).smul_mem c hy

/-- **`O₂` is graded**: it equals the span of its *homogeneous* generators `a₍₋₂₎b`
(`a ∈ 𝒱ₚ`, `b ∈ 𝒱_q`).  Each such generator is homogeneous of degree `p+q+1`
(`homGen_mem_grading`), so this exhibits `O₂` as a homogeneous submodule. -/
theorem O₂_eq_span_homGen (W : VertexOperatorAlgebra 𝒱) :
    O₂ W = Submodule.span ℂ (O₂homGen W) := by
  apply le_antisymm
  · rw [O₂, Submodule.span_le]; rintro x ⟨a, b, rfl⟩; exact gen_mem_span_homGen W a b
  · rw [Submodule.span_le]; rintro x ⟨p, q, a, b, ha, hb, rfl⟩
    exact Submodule.subset_span ⟨a, b, rfl⟩

/-! ## Degree bookkeeping: the homogeneous `O₂`-generators raise degree by `1`. -/

/-- A homogeneous `O₂`-generator lands one degree up: `a₍₋₂₎b ∈ 𝒱_{p+q+1}`. -/
theorem gen_mem_grading (W : VertexOperatorAlgebra 𝒱) {p q : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) :
    W.smul a (-2) b ∈ W.grading (p + q + 1) := by
  have h := W.smul_mem_grading ha hb (-2)
  rwa [show p + q - (-2) - 1 = p + q + 1 from by ring] at h

/-- A `s₍₋m₎(·)` step (`s ∈ 𝒱ₖ`, `m ≥ 1`) lands `𝒱_ℓ` in `𝒱_{k+ℓ+m-1}`. -/
theorem step_mem_grading (W : VertexOperatorAlgebra 𝒱) {k ℓ m : ℤ} {s x : 𝒱}
    (hs : s ∈ W.grading k) (hx : x ∈ W.grading ℓ) :
    W.smul s (-m) x ∈ W.grading (k + ℓ + m - 1) := by
  have h := W.smul_mem_grading hs hx (-m)
  rwa [show k + ℓ - (-m) - 1 = k + ℓ + m - 1 from by ring] at h

/-- **Negative grades vanish** (`positivity`/CFT type): `𝒱ₙ = 0` for `n < 0`. -/
theorem grading_eq_bot_of_neg (W : VertexOperatorAlgebra 𝒱) {n : ℤ} (hn : n < 0) :
    W.grading n = ⊥ := W.positivity n hn

/-- **Factor-degree drop.** In a *nonzero* homogeneous generator `a₍₋₂₎b ∈ 𝒱ₙ` with
`a ∈ 𝒱ₚ`, `b ∈ 𝒱_q` and `p+q+1 = n`, both factors are nonzero, hence (`positivity`) `p,q ≥ 0`,
so the two factor degrees are **strictly below** `n`: `p < n` and `q < n`. -/
theorem factor_deg_lt (W : VertexOperatorAlgebra 𝒱) {n p q : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (hpq : p + q + 1 = n)
    (hne : W.smul a (-2) b ≠ 0) : p < n ∧ q < n := by
  have hp : 0 ≤ p := by
    by_contra hp; push_neg at hp
    exact hne (by rw [show a = 0 by rw [W.positivity p hp, Submodule.mem_bot] at ha; exact ha,
      W.smul_zero_left])
  have hq : 0 ≤ q := by
    by_contra hq; push_neg at hq
    exact hne (by rw [show b = 0 by rw [W.positivity q hq, Submodule.mem_bot] at hb; exact hb,
      W.smul_zero_right])
  omega

/-! ## The lattice reduction. -/

/-- **Lattice reduction.** With `span S ⊆ T`, `span S ⊔ O₂ = ⊤` and the PBW core
`(★) : O₂ ≤ T`, the iterated-product span is everything: `T = ⊤`. -/
theorem iterProdSpan_eq_top_of_O₂_le (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (hO2 : O₂ W ≤ iterProdSpan W S) :
    iterProdSpan W S = ⊤ := by
  refine le_antisymm le_top ?_
  rw [htop]
  exact sup_le (span_S_le_iterProdSpan W S) hO2

/-! ## The degree strong-induction wrapper (bounded below by `positivity`). -/

/-- **Strong induction on the grading degree.** To prove every homogeneous piece lies in a
submodule `T`, it suffices to prove the single degree step at each `n ≥ 0`, assuming the claim
in all strictly lower degrees.  (Negative degrees are handled by `positivity`: `𝒱_{<0} = 0`.) -/
theorem grading_le_of_step (W : VertexOperatorAlgebra 𝒱) (T : Submodule ℂ 𝒱)
    (step : ∀ n : ℤ, 0 ≤ n → (∀ k : ℤ, k < n → W.grading k ≤ T) → W.grading n ≤ T) :
    ∀ n : ℤ, W.grading n ≤ T := by
  have key : ∀ N : ℕ, ∀ n : ℤ, n = N → W.grading n ≤ T := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro n hn
      subst hn
      apply step _ (by positivity)
      intro k hk
      by_cases hk0 : 0 ≤ k
      · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) := ⟨k.toNat, by omega⟩
        exact ih m (by omega) (m : ℤ) rfl
      · push_neg at hk0
        rw [W.positivity k hk0]; exact bot_le
  intro n
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, by omega⟩
    exact key m (m : ℤ) rfl
  · push_neg at hn; rw [W.positivity n hn]; exact bot_le

/-- **`(★)` and the full theorem from one per-degree closure step.**

Packaging the wrapper: if the single degree step `degStep` — *"every homogeneous `x ∈ 𝒱ₙ`
(`n ≥ 0`) lies in `T = iterProdSpan W S`, granted the same for all strictly lower degrees"* —
holds, then `T = ⊤` (finite generation 5.3.11a), and in particular `(★) : O₂ ≤ T`.

`degStep` is the *exact* remaining mathematical content of Gannon 5.3.11a: with `S ⊆ T` and
`O₂` graded (`O₂_eq_span_homGen`), it splits into
  (i) the **graded spanning** `𝒱ₙ ⊆ span(S∩𝒱ₙ) ⊔ (O₂ ⊓ 𝒱ₙ)`  (homogeneous projection), and
  (ii) the **PBW peeling** `O₂ ⊓ 𝒱ₙ ⊆ T`  — each homogeneous generator `a₍₋₂₎b ∈ 𝒱ₙ` has
       `a,b ∈ 𝒱_{<n} ⊆ T` by the induction hypothesis (`factor_deg_lt`), and is rewritten via
       the all-`ℤ` Borcherds iterate `mode_iterate` into `S`-iterated products in `T`.
See the closing note for why (ii) is the deep residual `mode_iterate`-peeling step. -/
theorem iterProdSpan_eq_top_of_degStep (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (degStep : ∀ n : ℤ, 0 ≤ n →
      (∀ k : ℤ, k < n → W.grading k ≤ iterProdSpan W S) →
      W.grading n ≤ iterProdSpan W S) :
    iterProdSpan W S = ⊤ := by
  have hgr : ∀ n : ℤ, W.grading n ≤ iterProdSpan W S :=
    grading_le_of_step W (iterProdSpan W S) degStep
  refine le_antisymm le_top ?_
  rw [← W.isInternal.submodule_iSup_eq_top]
  exact iSup_le hgr

/-! ## Closing note — the degree-step content (discharged in `FiniteGenerationProof`).

Everything above is `sorry`-free / axiom-free.  The full unconditional theorem
`iterProdSpan W S = ⊤` (hence `(★) : O₂ ≤ iterProdSpan W S`) is reduced — by
`iterProdSpan_eq_top_of_degStep` — to discharging the single per-degree step `degStep`, which is
**proved unconditionally** in `Modules.FiniteGenerationProof` (`degStep_unconditional`). The two
inputs it factors into are described below for orientation; both are realised there.

`degStep` factors (granting `S ⊆ T`, `O₂` graded via `O₂_eq_span_homGen`, and the degree drop
`factor_deg_lt`) into two inputs:

  (i)  **Graded spanning** `𝒱ₙ ≤ span(S ∩ 𝒱ₙ) ⊔ (O₂ W ⊓ 𝒱ₙ)`.  Both `span S` (since `S` is
       homogeneous, Step A′ of wf3) and `O₂` (just shown) are homogeneous submodules with
       `span S ⊔ O₂ = ⊤`; applying the graded projection `π_n` (from `W.isInternal`, built off
       `DirectSum.IsInternal.chooseDecomposition`) to a homogeneous `x ∈ 𝒱ₙ` yields this split.
       This is routine but needs the `π_n`-preserves-homogeneous-submodule lemma.

  (ii) **PBW peeling** `O₂ W ⊓ 𝒱ₙ ≤ T`.  Via `O₂_eq_span_homGen` this reduces to: a homogeneous
       generator `a₍₋₂₎b ∈ 𝒱ₙ` (with `a ∈ 𝒱ₚ`, `b ∈ 𝒱_q`, `p,q < n` by `factor_deg_lt`, so
       `a,b ∈ T` by the induction hypothesis) lies in `T`.  Since `T` is **not** a priori a
       subalgebra — it is only closed under `s₍₋m₎(·)` for the *generators* `s ∈ S`, not for
       general `a ∈ T` — one must peel `a` apart: writing `a = s₍₋k₎a'` (an `IsIterProd` step),
       `mode_iterate` expands
         `(s₍₋k₎a')₍₋₂₎b = ∑ᵢ ±C(...)·( s₍₋k-i₎(a'₍₋2+i₎b) − ± a'₍-2-k... ₎(s₍ᵢ₎b) )`,
       where the first family is an `S`-step `s₍₋(k+i)₎(·)` applied to a *structurally smaller*
       product `a'₍₋2+i₎b` (closed by an inner induction on the `IsIterProd` structure of `a'`),
       and the second family carries *non-negative* inner modes `s₍ᵢ₎b` (`i ≥ 0`), which lower
       degree and feed back through the degree induction.  This nested `mode_iterate`/structural
       double induction — the same engine as `PoissonDescent.gen_smul_mem_O₂` /
       `poissonMul_assoc_mem_O₂` but run to convergence on `T` rather than on `O₂` — is the
       genuine deep residual.  It is recorded here as the precise blocker, not faked.
-/

end VOA
