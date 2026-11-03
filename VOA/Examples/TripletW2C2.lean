/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.TripletW2
import VOA.Modularity.C2GradedVanishing
import VOA.Modularity.BlockZeroMode
import VOA.Modules.C2ImpliesZhuFinite

/-!
# `C₂`-cofiniteness of the triplet algebra `W(2)`: criteria, reduction, and the isolated gap

The target is `C2Cofinite tripletW2` — that the triplet vertex operator algebra
`W(2) = SF(1)⁺` at `c = -2` (`Examples.TripletW2`) has a finite-dimensional Poisson quotient
`A₂(W(2)) = W(2) ⧸ O₂(W(2))`.  It is **not** proved here.  What is proved here is everything
around it: two general positive criteria for `C₂`-cofiniteness (compare
`trivial_C2Cofinite` for the one-dimensional VOA and the *negative*
`heisenberg_not_C2Cofinite`), the reduction of the target to a statement about words, and the
first of Abe's three computational pillars.

## The mathematics

T. Abe, *A `Z₂`-orbifold model of the symplectic fermionic vertex operator superalgebra*,
Math. Z. **255** (2007) 755–792 = `arXiv:math/0503472`, proves in **Theorem 3.9** that
`SF(1)⁺ = W(2)` is `C₂`-cofinite, with the quantitative content in **Proposition 3.11**:
`dim W(2)/C₂(W(2)) ≤ 11`, spanned by `{1, ω̄, ω̄², ω̄³, ω̄⁴, Ē, ω̄Ē, H̄, ω̄H̄, F̄, ω̄F̄}`.
(⚠ Citing this as "Thm 3.10" is a misattribution — 3.10 is a Remark.)  His proof has
three pillars: **Prop. 2.2** (strong generation ⟹ ring generation of `A₂`), **Prop. 3.7**
(strong generation of `W(2)` by `ω, E, H, F`), and **§3.3** (the relations, in particular
nilpotency of the four generators).

## Main results

### General theory (any VOA)

* `C2Cofinite_of_grading_le_O₂` — if `𝒱ₙ ⊆ O₂(𝒱)` for all `n ≥ N`, then `𝒱` is
  `C₂`-cofinite.  The exact converse of Buhl's `exists_grading_le_O₂`, so
* `C2Cofinite_iff_exists_grading_le_O₂` — `C₂`-cofiniteness **is** the eventual vanishing of
  the graded pieces modulo `O₂`.  Isolating the gap there therefore loses nothing.
* `C2Cofinite_of_finite_span_sup` — a finite set spanning `𝒱` modulo `O₂` suffices.
* `A₂monSpan_eq_top_of_iterProdSpan` — **Abe, Proposition 2.2**: strong generation of `𝒱`
  by `S` (`iterProdSpan W S = ⊤`, the repository's own 5.3.11a vocabulary) implies that
  `A₂(𝒱)` is generated *as a commutative ring* by the classes of `S`.  Every iterated product
  containing a mode `₍₋m₎` with `m ≥ 2` dies in `A₂`, by `smul_le_neg_two_mem_O₂`.  This is the
  converse of `Modules.FiniteGenerationProof.iterProdSpan_eq_top`, and it was missing.
* `finiteDimensional_A₂monSpan` — a commutative ring spanned by the monomials in finitely
  many **nilpotent** elements is finite-dimensional.
* `C2Cofinite_of_iterProdSpan_of_nilpotent` — the two combined: **strong generation by a
  finite set + nilpotency of the generator classes ⟹ `C₂`-cofinite.**  This is the positive
  template the repository lacked, and it is a criterion with real content: the free boson fails
  it precisely because `[a₍₋₁₎𝟙]` is not nilpotent in `A₂(M(1)) ≅ ℂ[x]`.
  ⚠ Only *nilpotency* is needed, not Abe's full relation list.
* `vacuumGradeZero_of_VOA` — `VacuumGradeZero W` holds for **every** vertex operator algebra
  here: it is the `≤` half of the structure field `vacuum_grade : 𝒱₀ = ℂ𝟙`.  A dozen results in
  `Modularity/` carry it as a hypothesis unnecessarily.

### `W(2)` specifically

* `tripletW2_vacuumGradeZero` — one of the two hypotheses of the Arike–Nagatomo modularity
  bound, discharged.
* `mem_span_even_words_of_mem_grading` — the even part meets a conformal weight space in the
  span of the **even-length words of that weight**: an even vector has no odd component, by
  disjointness of the two Clifford parities.
* `tripletW2_C2Cofinite_of_words` — **the target, reduced to a statement about words**:
  if every even word of weight `≥ N` gives a state in `C₂(W(2))`, then `W(2)` is `C₂`-cofinite.
  Equivalent to the target, and finitely checkable at each weight (`sfWords_nat_finite`).
* `tripletW2_C2Cofinite_of_grading_le_O₂`, `tripletW2_C2Cofinite_of_generators` — the same
  target conditional on the grading form, resp. on Abe's Prop. 3.7 + §3.3 in the exact shape
  `C2Cofinite_of_iterProdSpan_of_nilpotent` consumes.
* `tripletW2_zhuFiniteness_of_C2Cofinite` — what closing the gap would buy: *both* finiteness
  hypotheses `hA : FiniteDimensional ℂ (A tripletW2)` and
  `hAnm : ∀ n, FiniteDimensional ℂ (AnmFull tripletW2 n 0)` carried at
  `Examples/TripletW2Log.lean:620,628,636` and `Examples/ZhuTripletW2Alt.lean:334,343`, via
  `Modules.C2ImpliesZhuFinite.zhuFinitenessPackage_of_C2Cofinite`.  (Their third hypothesis
  `hgate : DJAnnEqAn _ 0` is not a finiteness statement and is untouched.)
* `BW2_reduce` — **Abe, Lemma 3.4**, proved: the two-letter classes collapse,
  `B(m,a,n,b) = (−1)ⁿ binom(m+n,n) · B(m+n,a,0,b)` in `A₂(W(2))`, where `B(m,a,n,b)` is the
  class of `χᵃ₋ₘ₋₁χᵇ₋ₙ₋₁|0⟩`.  Proved from `T_stWordSF_pair` (`T` is a derivation on states,
  `SymplecticFermionT.T_mul`) together with `L₋₁𝒱 ⊆ O₂` (`L_neg_one_mem_O₂`), via the relation
  `BW2_rel : (m+1)B(m+1,a,n,b) + (n+1)B(m,a,n+1,b) = 0`.  So at each conformal weight the
  two-letter part of `A₂(W(2))` is spanned by the four classes `B(w−2,a,0,b)`.

## ⚠ Status: the target is NOT proved.  The exact remaining gap

`C2Cofinite tripletW2` is **open** here.  By `C2Cofinite_iff_exists_grading_le_O₂` and
`tripletW2_C2Cofinite_of_words` the open statement is exactly:

> there is an `N` such that every even word `l` with `sfWeight l ≥ N` has
> `wordW2 l ∈ O₂ tripletW2`,

equivalently (Abe Prop. 3.7 + §3.3) that `W(2)` is strongly generated by `ω, E, H, F` and that
the four classes `ω̄, Ē, H̄, F̄` are nilpotent in `A₂(W(2))`.

Two of Abe's three pillars are missing, and both need the **two-letter mode formula**
`mode (YSF (stWordSF [(m,a),(n,b)])) k` — the analogue, for a whole family of states, of the
1550-line computation (`SymplecticFermionVirasoro{A,B}`) that produced `LSF_eq_mode` for the
single state `ωSF`:

1. the **length reduction** (Abe Lem. 3.5/3.6, Prop. 3.7): modulo `C₂`, an even word of length
   `≥ 4` reduces to shorter words of the same weight, via
   `P₍₋₂₎v ∈ O₂` for a two-letter `P` expanded by Wick contraction;
2. the **relation chain** (Abe §3.3): `Γ_m(e,f)Γ_k(e,f) = (1/m + 1/k)Γ_{m+k}(e,f)`,
   `Γ₃(e,e)² = Γ₇(e,e) = 0`, `ω̄⁵ = 0`, `2H̄² = −ĒF̄ = (16/9)ω̄³`.

Pillar 1 of Abe's argument that does *not* need it — his Prop. 2.2 — is proved above, as is his
Lemma 3.4, which is the `L₋₁` half of §3.2.

## Dependencies
`Examples.TripletW2`, `Modularity.C2GradedVanishing` (Buhl Rem. 3.5), `Modularity.BlockZeroMode`
(`VacuumGradeZero`), `Modules.C2ImpliesZhuFinite`.  Imported by the umbrella `VOA/Examples.lean`.

## Status
Every declaration in this file is `sorry`-free and axiom-clean: `#print axioms` on all 19 gives
exactly `[propext, Classical.choice, Quot.sound]` — no `VOA.pbw`, no `sorryAx`, no new
axiom.  No result is stated unconditionally that is not proved unconditionally; the three
`tripletW2_C2Cofinite_of_*` theorems carry their open input as an explicit named hypothesis.

## References
* T. Abe, *A `Z₂`-orbifold model of the symplectic fermionic vertex operator superalgebra*,
  Math. Z. **255** (2007) 755–792; `arXiv:math/0503472`, Prop. 2.2, Lem. 3.4, Prop. 3.7,
  Thm. 3.9, Prop. 3.11.
* Gannon §5.3.2, Def. 5.3.5; Zhu [574]; Buhl, Remark 3.5; Carqueville–Flohr, Adamović–Milas
  for general `p`.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1  A positive criterion for `C₂`-cofiniteness -/

/-- `𝒱_{<N} := ⨆_{0 ≤ i < N} 𝒱ᵢ`, the sum of the lowest `N` graded pieces. -/
noncomputable def lowGrades (W : VertexOperatorAlgebra 𝒱) (N : ℕ) : Submodule ℂ 𝒱 :=
  (Finset.range N).sup fun i : ℕ => W.grading (i : ℤ)

/-- Each of the lowest `N` graded pieces sits inside `𝒱_{<N}`. -/
theorem grading_le_lowGrades (W : VertexOperatorAlgebra 𝒱) {N i : ℕ} (hi : i < N) :
    W.grading (i : ℤ) ≤ lowGrades W N :=
  Finset.le_sup (f := fun i : ℕ => W.grading (i : ℤ)) (Finset.mem_range.mpr hi)

/-- `𝒱_{<N}` is finite-dimensional: a finite sup of the (finite-dimensional, by the vertex
algebra axiom `finrank`) graded pieces. -/
instance finiteDimensional_lowGrades (W : VertexOperatorAlgebra 𝒱) (N : ℕ) :
    FiniteDimensional ℂ (lowGrades W N) := by
  haveI : ∀ i : ℕ, FiniteDimensional ℂ (W.grading (i : ℤ)) := fun i => W.finrank _
  exact Submodule.finiteDimensional_finset_sup _ _

open Classical in
/-- Every element is the (finite) sum of its homogeneous components. -/
theorem sum_piHom (W : VertexOperatorAlgebra 𝒱) (x : 𝒱) :
    x = ∑ j ∈ (DirectSum.decompose W.grading x).support, piHom W j x := by
  conv_lhs => rw [← DirectSum.sum_support_decompose W.grading x]
  exact Finset.sum_congr rfl fun j _ => (piHom_apply W j x).symm

/-- **A positive criterion for `C₂`-cofiniteness.**  If all graded pieces from degree `N`
on lie inside `O₂(𝒱) = C₂(𝒱)`, then `A₂(𝒱)` is finite-dimensional.

This is the exact converse of Buhl's `exists_grading_le_O₂`, and it is what turns
`C₂`-cofiniteness into a *checkable* statement: the classes of the finitely many low degrees
`𝒱₀,…,𝒱_{N−1}` — each finite-dimensional by the vertex-algebra axiom — already span `A₂(𝒱)`,
because the negative degrees vanish (`positivity`) and all degrees `≥ N` die in the quotient. -/
theorem C2Cofinite_of_grading_le_O₂ (W : VertexOperatorAlgebra 𝒱) {N : ℕ}
    (hN : ∀ n : ℤ, (N : ℤ) ≤ n → W.grading n ≤ O₂ W) : C2Cofinite W := by
  classical
  set f : lowGrades W N →ₗ[ℂ] A₂ W := (mk₂ W).comp (lowGrades W N).subtype with hf
  have hpi : ∀ (j : ℤ) (x : 𝒱), mk₂ W (piHom W j x) ∈ LinearMap.range f := by
    intro j x
    rcases lt_or_ge j 0 with hj | hj
    · have hz : piHom W j x = 0 := by
        have hm := piHom_mem W j x
        rw [W.positivity j hj] at hm
        simpa using hm
      rw [hz, map_zero]
      exact (LinearMap.range f).zero_mem
    · rcases lt_or_ge j (N : ℤ) with hjN | hjN
      · obtain ⟨i, rfl⟩ : ∃ i : ℕ, j = (i : ℤ) := ⟨j.toNat, by omega⟩
        have hiN : i < N := by exact_mod_cast hjN
        have hmem : piHom W (i : ℤ) x ∈ lowGrades W N :=
          grading_le_lowGrades W hiN (piHom_mem W _ x)
        exact ⟨⟨_, hmem⟩, rfl⟩
      · have hO : piHom W j x ∈ O₂ W := hN j hjN (piHom_mem W j x)
        rw [(mk₂_eq_zero_iff W).mpr hO]
        exact (LinearMap.range f).zero_mem
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := mk₂_surjective W y
    have hx : mk₂ W x
        = ∑ j ∈ (DirectSum.decompose W.grading x).support, mk₂ W (piHom W j x) := by
      conv_lhs => rw [sum_piHom W x]
      rw [map_sum]
    have hmem : mk₂ W x ∈ LinearMap.range f := by
      rw [hx]
      exact Submodule.sum_mem _ fun j _ => hpi j x
    exact hmem
  exact Module.Finite.of_surjective f hsurj

/-- **`C₂`-cofiniteness is exactly the eventual vanishing of the graded pieces mod `O₂`.**
The forward direction is Buhl Remark 3.5 (`exists_grading_le_O₂`); the backward direction is
`C2Cofinite_of_grading_le_O₂`. -/
theorem C2Cofinite_iff_exists_grading_le_O₂ (W : VertexOperatorAlgebra 𝒱) :
    C2Cofinite W ↔ ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ n → W.grading n ≤ O₂ W :=
  ⟨fun h => exists_grading_le_O₂ W h, fun ⟨_, hN⟩ => C2Cofinite_of_grading_le_O₂ W hN⟩

/-- A finite spanning set modulo `O₂` suffices — the "exhibit a finite spanning set" form of the
criterion, with no grading in sight. -/
theorem C2Cofinite_of_finite_span_sup (W : VertexOperatorAlgebra 𝒱) (S : Finset 𝒱)
    (hS : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (S : Set 𝒱) ⊔ O₂ W) : C2Cofinite W := by
  classical
  set f : (Submodule.span ℂ (S : Set 𝒱)) →ₗ[ℂ] A₂ W :=
    (mk₂ W).comp (Submodule.span ℂ (S : Set 𝒱)).subtype with hf
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (S : Set 𝒱)) :=
    FiniteDimensional.span_of_finite ℂ S.finite_toSet
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := mk₂_surjective W y
    have hx : x ∈ Submodule.span ℂ (S : Set 𝒱) ⊔ O₂ W := by rw [← hS]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨a, ha⟩, ?_⟩
    change mk₂ W a = mk₂ W (a + b)
    rw [mk₂_eq_iff]
    simpa using (O₂ W).neg_mem hb
  exact Module.Finite.of_surjective f hsurj

/-! ## §2  The positive template: strong generation + nilpotent generators

The repository already proves the *forward* finite-generation statement 5.3.11a
(`Modules.FiniteGenerationProof.iterProdSpan_eq_top`: `C₂`-cofinite ⟹ strongly generated).
This section supplies the **converse direction that a positive `C₂` proof actually needs**
(Abe, *A `Z₂`-orbifold model …*, Math. Z. 255 (2007) 755–792, Proposition 2.2):

  *if `𝒱` is strongly generated by `S`, then `A₂(𝒱)` is generated, **as a commutative ring**,
  by the classes `[s]`, `s ∈ S`.*

The mechanism is one line of mode arithmetic: in an iterated product
`s¹₍₋m₁₎ ⋯ sʳ₍₋mᵣ₎𝟙` any factor with `mᵢ ≥ 2` already lands the whole vector in `O₂`
(`smul_le_neg_two_mem_O₂`), so only the all-`mᵢ = 1` monomials survive in the quotient — and
those are exactly the ring products `[s¹]⋯[sʳ]`.

Adding nilpotency of each generator then closes the argument by pure commutative algebra:
a commutative ring spanned by the monomials in finitely many **nilpotent** elements is a
finite-dimensional vector space. -/

/-- Multiplication in `A₂(𝒱)` is the descended Poisson product, so it is `ℂ`-bilinear:
`(c • p) * q = c • (p * q)`. -/
theorem A₂_smul_mul (W : VertexOperatorAlgebra 𝒱) (c : ℂ) (p q : A₂ W) :
    (c • p) * q = c • (p * q) := by
  change A₂mul W (c • p) q = c • A₂mul W p q
  rw [map_smul]
  rfl

/-- Multiplication in `A₂(𝒱)` is `ℂ`-bilinear: `p * (c • q) = c • (p * q)`. -/
theorem A₂_mul_smul (W : VertexOperatorAlgebra 𝒱) (c : ℂ) (p q : A₂ W) :
    p * (c • q) = c • (p * q) := by
  change A₂mul W p (c • q) = c • A₂mul W p q
  rw [map_smul]

/-- **Monomials in `S`** inside the commutative ring `A₂(𝒱)`: the unit `1 = [𝟙]`, closed under
multiplying by a class `[s]` with `s ∈ S`. -/
inductive IsA₂Mon (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱) : A₂ W → Prop
  | one : IsA₂Mon W S 1
  | step (s : 𝒱) (hs : s ∈ S) (p : A₂ W) (hp : IsA₂Mon W S p) : IsA₂Mon W S (mk₂ W s * p)

/-- The `ℂ`-span of the monomials in `S`; `A₂monSpan W S = ⊤` says exactly that `A₂(𝒱)` is
generated as a commutative `ℂ`-algebra by the classes of `S`. -/
noncomputable def A₂monSpan (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱) : Submodule ℂ (A₂ W) :=
  Submodule.span ℂ {p | IsA₂Mon W S p}

theorem A₂monSpan_def (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱) :
    A₂monSpan W S = Submodule.span ℂ {p | IsA₂Mon W S p} := rfl

theorem mem_A₂monSpan (W : VertexOperatorAlgebra 𝒱) {S : Set 𝒱} {p : A₂ W}
    (hp : IsA₂Mon W S p) : p ∈ A₂monSpan W S := Submodule.subset_span hp

/-- The monomial span is stable under multiplication by a generator class. -/
theorem mul_mem_A₂monSpan (W : VertexOperatorAlgebra 𝒱) {S : Set 𝒱} {s : 𝒱} (hs : s ∈ S)
    {q : A₂ W} (hq : q ∈ A₂monSpan W S) : mk₂ W s * q ∈ A₂monSpan W S := by
  refine Submodule.span_induction (p := fun q _ => mk₂ W s * q ∈ A₂monSpan W S) ?_ ?_ ?_ ?_ hq
  · intro y hy; exact mem_A₂monSpan W (IsA₂Mon.step s hs y hy)
  · change mk₂ W s * 0 ∈ A₂monSpan W S
    rw [mul_zero]; exact (A₂monSpan W S).zero_mem
  · intro y z _ _ hy hz; rw [mul_add]; exact (A₂monSpan W S).add_mem hy hz
  · intro c y _ hy; rw [A₂_mul_smul]; exact (A₂monSpan W S).smul_mem c hy

/-- **Abe, Proposition 2.2** — strong generation descends to ring generation of `A₂(𝒱)`.

If `𝒱` is spanned by the iterated products `s¹₍₋m₁₎⋯sʳ₍₋mᵣ₎𝟙` (`mᵢ ≥ 1`, `sᵢ ∈ S`), then
`A₂(𝒱)` is spanned by the ring monomials `[s¹]⋯[sʳ]`.  Every iterated product containing a
mode `₍₋m₎` with `m ≥ 2` dies in `A₂(𝒱)`, because `u₍ₙ₎v ∈ O₂` for `n ≤ -2`. -/
theorem A₂monSpan_eq_top_of_iterProdSpan (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (h : iterProdSpan W S = ⊤) : A₂monSpan W S = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨x, rfl⟩ := mk₂_surjective W y
  have hx : x ∈ iterProdSpan W S := by rw [h]; trivial
  refine Submodule.span_induction (p := fun x _ => mk₂ W x ∈ A₂monSpan W S) ?_ ?_ ?_ ?_ hx
  · intro z hz
    induction hz with
    | vacuum =>
        have h1 : mk₂ W W.vacuum = (1 : A₂ W) := (A₂_one_eq W).symm
        rw [h1]
        exact mem_A₂monSpan W IsA₂Mon.one
    | step s hs m hm z _ ih =>
        rcases eq_or_lt_of_le hm with h1 | h2
        · have h2 := mul_mem_A₂monSpan W hs ih
          rw [A₂_mul_mk] at h2
          rw [← h1]
          exact h2
        · have hO : W.smul s (-m) z ∈ O₂ W :=
            smul_le_neg_two_mem_O₂ W s z (by omega)
          rw [(mk₂_eq_zero_iff W).mpr hO]
          exact (A₂monSpan W S).zero_mem
  · change mk₂ W 0 ∈ A₂monSpan W S
    rw [map_zero]; exact (A₂monSpan W S).zero_mem
  · intro a b _ _ ha hb; rw [map_add]; exact (A₂monSpan W S).add_mem ha hb
  · intro c a _ ha; rw [map_smul]; exact (A₂monSpan W S).smul_mem c ha

/-- Splitting off one generator: every monomial in `insert a T` is a power of `[a]` times a
monomial in `T` (commutativity of `A₂(𝒱)` lets `[a]` be collected in front). -/
theorem IsA₂Mon.insert_split (W : VertexOperatorAlgebra 𝒱) {a : 𝒱} {T : Set 𝒱} {p : A₂ W}
    (hp : IsA₂Mon W (insert a T) p) :
    ∃ (i : ℕ) (q : A₂ W), IsA₂Mon W T q ∧ p = (mk₂ W a) ^ i * q := by
  induction hp with
  | one => exact ⟨0, 1, IsA₂Mon.one, by rw [pow_zero, one_mul]⟩
  | step s hs p _ ih =>
      obtain ⟨i, q, hq, hpq⟩ := ih
      rcases Set.mem_insert_iff.mp hs with hsa | hsT
      · exact ⟨i + 1, q, hq, by rw [hpq, hsa]; ring⟩
      · exact ⟨i, mk₂ W s * q, IsA₂Mon.step s hsT q hq, by rw [hpq]; ring⟩

/-- **Finitely many nilpotent generators ⟹ finite dimension.**  The monomial span of a
finite set of elements of `A₂(𝒱)` whose classes are nilpotent is finite-dimensional: bounded
exponents give finitely many monomials. -/
theorem finiteDimensional_A₂monSpan (W : VertexOperatorAlgebra 𝒱) :
    ∀ S : Finset 𝒱, (∀ s ∈ S, ∃ k : ℕ, (mk₂ W s) ^ k = 0) →
      FiniteDimensional ℂ (A₂monSpan W (S : Set 𝒱)) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro _
      have hle : A₂monSpan W ((∅ : Finset 𝒱) : Set 𝒱)
          ≤ Submodule.span ℂ ({1} : Set (A₂ W)) := by
        rw [A₂monSpan_def, Submodule.span_le]
        rintro p hp
        have hp1 : p = 1 := by
          induction hp with
          | one => rfl
          | step s hs p _ _ => simp only [Finset.coe_empty, Set.mem_empty_iff_false] at hs
        rw [hp1]
        exact Submodule.subset_span rfl
      haveI : FiniteDimensional ℂ (Submodule.span ℂ ({1} : Set (A₂ W))) :=
        FiniteDimensional.span_of_finite ℂ (Set.finite_singleton 1)
      exact Submodule.finiteDimensional_of_le hle
  | @insert a T ha ih =>
      intro hnil
      haveI hT : FiniteDimensional ℂ (A₂monSpan W (T : Set 𝒱)) :=
        ih (fun s hs => hnil s (Finset.mem_insert_of_mem hs))
      obtain ⟨k, hk⟩ := hnil a (Finset.mem_insert_self a T)
      set Q : Submodule ℂ (A₂ W) :=
        (Finset.range k).sup
          (fun i => Submodule.map (A₂mul W ((mk₂ W a) ^ i)) (A₂monSpan W (T : Set 𝒱))) with hQdef
      haveI : FiniteDimensional ℂ Q := by
        rw [hQdef]
        exact Submodule.finiteDimensional_finset_sup _ _
      have hle : A₂monSpan W ((insert a T : Finset 𝒱) : Set 𝒱) ≤ Q := by
        rw [A₂monSpan_def, Submodule.span_le]
        rintro p hp
        have hp' : IsA₂Mon W (insert a (T : Set 𝒱)) p := by
          rw [Finset.coe_insert] at hp
          exact hp
        obtain ⟨i, q, hq, rfl⟩ := IsA₂Mon.insert_split W hp'
        rcases lt_or_ge i k with hik | hik
        · have hmem : (mk₂ W a) ^ i * q
              ∈ Submodule.map (A₂mul W ((mk₂ W a) ^ i)) (A₂monSpan W (T : Set 𝒱)) :=
            ⟨q, mem_A₂monSpan W hq, rfl⟩
          have hsup := Finset.le_sup (f := fun i =>
            Submodule.map (A₂mul W ((mk₂ W a) ^ i)) (A₂monSpan W (T : Set 𝒱)))
            (Finset.mem_range.mpr hik)
          rw [hQdef]
          exact hsup hmem
        · have hz : (mk₂ W a) ^ i = 0 := by
            obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = k + j := ⟨i - k, by omega⟩
            rw [pow_add, hk, zero_mul]
          rw [hz, zero_mul]
          exact Q.zero_mem
      exact Submodule.finiteDimensional_of_le hle

/-- **The positive `C₂`-cofiniteness template.**  A vertex operator algebra that is
strongly generated by a finite set `S` whose classes in `A₂(𝒱)` are all nilpotent is
`C₂`-cofinite.

This is the shape of Abe's proof for the triplet algebra (Prop. 2.2 + the relations of §3.3),
and — unlike `trivial_C2Cofinite` — it is a criterion with real content: it is exactly what the
free boson fails, since `[a₍₋₁₎𝟙]` is *not* nilpotent in `A₂(M(1)) ≅ ℂ[x]`
(`Examples.HeisenbergC2.heisenberg_not_C2Cofinite`). -/
theorem C2Cofinite_of_iterProdSpan_of_nilpotent (W : VertexOperatorAlgebra 𝒱) (S : Finset 𝒱)
    (hgen : iterProdSpan W (S : Set 𝒱) = ⊤)
    (hnil : ∀ s ∈ S, ∃ k : ℕ, (mk₂ W s) ^ k = 0) : C2Cofinite W := by
  have htop : A₂monSpan W (S : Set 𝒱) = ⊤ := A₂monSpan_eq_top_of_iterProdSpan W _ hgen
  have hfd : FiniteDimensional ℂ (A₂monSpan W (S : Set 𝒱)) :=
    finiteDimensional_A₂monSpan W S hnil
  rw [htop] at hfd
  haveI := hfd
  exact Module.Finite.equiv (Submodule.topEquiv)

/-! ## §3  `VacuumGradeZero` is free

`Modularity.BlockZeroMode.VacuumGradeZero W` (`𝒱₀ ⊆ ℂ𝟙`) is carried as a hypothesis in a dozen
places in `Modularity/`.  It is in fact **an axiom of `VertexOperatorAlgebra`** in this
development: `vacuum_grade : grading 0 = ℂ ∙ vacuum` is a structure field (VOA4, part 1), and
`VacuumGradeZero` is the `≤` half of that equality.  So no VOA in this repository ever needs it
assumed. -/

/-- **`VacuumGradeZero` holds for every vertex operator algebra**: it is the `≤` half of the
CFT-type structure field `vacuum_grade : 𝒱₀ = ℂ𝟙`. -/
theorem vacuumGradeZero_of_VOA (W : VertexOperatorAlgebra 𝒱) : VacuumGradeZero W :=
  le_of_eq W.vacuum_grade

namespace SympFerm

open VOA
open CliffordAlgebra

/-- `VacuumGradeZero tripletW2` — one of the two hypotheses of the Arike–Nagatomo bound
`dim C₁(V) ≤ dim SLF(A(V))`.  Free, by `vacuumGradeZero_of_VOA`. -/
theorem tripletW2_vacuumGradeZero : VacuumGradeZero tripletW2 :=
  vacuumGradeZero_of_VOA tripletW2

/-! ## §4  `C₂`-cofiniteness of `W(2)`: the reduction and the isolated gap

Abe (*A `Z₂`-orbifold model of the symplectic fermionic vertex operator superalgebra*,
Math. Z. **255** (2007) 755–792 = `arXiv:math/0503472`) proves in **Theorem 3.9** that
`SF(1)⁺ = W(2)` is `C₂`-cofinite, with the quantitative content in **Proposition 3.11**,
`dim W(2)/C₂(W(2)) ≤ 11`, spanned by
`{1, ω̄, ω̄², ω̄³, ω̄⁴, Ē, ω̄Ē, H̄, ω̄H̄, F̄, ω̄F̄}`.
(⚠ Citing this as "Thm 3.10" is a misattribution: 3.10 is a Remark.)

Everything in that proof except two explicitly identified computations is available here:

* Abe **Prop. 2.2** — strong generation ⟹ ring generation of `A₂` — is `§2`'s
  `A₂monSpan_eq_top_of_iterProdSpan`;
* the passage from "finitely many nilpotent ring generators" to `dim A₂ < ∞` is
  `finiteDimensional_A₂monSpan`;
* the two are combined in `C2Cofinite_of_iterProdSpan_of_nilpotent`;
* the alternative, grading-flavoured route is `C2Cofinite_of_grading_le_O₂`, whose hypothesis is
  by `C2Cofinite_iff_exists_grading_le_O₂` *equivalent* to the goal, so nothing is lost by
  isolating the gap there.

What is **not** proved here is the input, in either of its two equivalent shapes.  Both are
stated below as explicit named hypotheses, never as axioms. -/

/-- **`C₂`-cofiniteness of `W(2)`, conditional on the eventual vanishing of the graded
pieces modulo `C₂`.**

The hypothesis `habe` is Abe's Theorem 3.9/Proposition 3.11 restated in this repository's
vocabulary, and by `C2Cofinite_iff_exists_grading_le_O₂` it is *equivalent* to the conclusion —
so this theorem is a faithful reduction, not a weakening.  What it buys is that the hypothesis
is a statement about the finitely many word states of each fixed conformal weight, hence
checkable, whereas `C2Cofinite` is a statement about an infinite-dimensional quotient. -/
theorem tripletW2_C2Cofinite_of_grading_le_O₂ {N : ℕ}
    (habe : ∀ n : ℤ, (N : ℤ) ≤ n → tripletW2.grading n ≤ O₂ tripletW2) :
    C2Cofinite tripletW2 :=
  C2Cofinite_of_grading_le_O₂ tripletW2 habe

/-- **`C₂`-cofiniteness of `W(2)`, conditional on Abe's Proposition 3.7 + §3.3.**

The two hypotheses are exactly Abe's two inputs:
* `hgen` — Abe **Prop. 3.7 / Cor. 3.8**: `W(2)` is *strongly generated* by
  `ω = e₍₋₁₎f`, `E = e₍₋₂₎e`, `H = ½(e₍₋₂₎f + f₍₋₂₎e)`, `F = f₍₋₂₎f`
  (`S` is meant to be that four-element set, but the statement is uniform in `S`);
* `hnil` — the consequence of Abe **§3.3** that each generator is nilpotent in `A₂`:
  `Ē² = F̄² = 0`, `ω̄⁵ = 0` and `2H̄² = (16/9)ω̄³` (so `H̄¹⁰ = 0`).

⚠ Only nilpotency is needed, not Abe's full relation list: a commutative ring spanned by the
monomials in finitely many nilpotents is automatically finite-dimensional. -/
theorem tripletW2_C2Cofinite_of_generators (S : Finset (evenOdd QSF (0 : ZMod 2)))
    (hgen : iterProdSpan tripletW2 (S : Set (evenOdd QSF (0 : ZMod 2))) = ⊤)
    (hnil : ∀ s ∈ S, ∃ k : ℕ, (mk₂ tripletW2 s) ^ k = 0) :
    C2Cofinite tripletW2 :=
  C2Cofinite_of_iterProdSpan_of_nilpotent tripletW2 S hgen hnil

/-! ## §5  What `C2Cofinite tripletW2` would discharge

`Modules.C2ImpliesZhuFinite.zhuFinitenessPackage_of_C2Cofinite` turns `C₂`-cofiniteness into
*both* finiteness hypotheses carried by the logarithmic-`W(2)` consumers, so the statements
below are recorded conditionally, with the same single open input. -/

/-- Conditional on `C2Cofinite tripletW2`: the Zhu algebra `A(W(2))` is finite-dimensional,
and so is every `AnmFull (W(2)) n 0`.

These are exactly the hypotheses `hA : FiniteDimensional ℂ (A tripletW2)` and
`hAnm : ∀ n, FiniteDimensional ℂ (AnmFull tripletW2 n 0)` carried at
`Examples/TripletW2Log.lean:620,628,636` and `Examples/ZhuTripletW2Alt.lean:334,343`.
(The third carried hypothesis there, `hgate : DJAnnEqAn _ 0`, is *not* a finiteness statement
and is untouched by `C₂`-cofiniteness.) -/
theorem tripletW2_zhuFiniteness_of_C2Cofinite (hC2 : C2Cofinite tripletW2) :
    (∀ n : ℕ, FiniteDimensional ℂ (AnmFull tripletW2 n 0))
      ∧ FiniteDimensional ℂ (A tripletW2) :=
  zhuFinitenessPackage_of_C2Cofinite tripletW2 hC2

/-! ## §6  The gap, restated at the level of words

`W(2)` is spanned by the **even-length** word states `χ^{a₁}_{-k₁-1}⋯χ^{a_{2r}}_{-k_{2r}-1}|0⟩`,
and at each conformal weight there are only finitely many of them (`sfWords_nat_finite`).  This
section shows that `tripletW2.grading n ≤ O₂ tripletW2` may be checked **word by word**: the
weight-`n` part of `W(2)` is exactly the span of the even words of weight `n`, no ambient odd
states interfering.  Combined with `§1` this turns the whole `C₂` target into the purely
combinatorial statement `tripletW2_C2Cofinite_of_words` below. -/

/-- An even-length word state, viewed inside `W(2) = (FockSF)₀̄`. -/
noncomputable def wordW2 {l : SFWord} (hl : Even l.length) : evenOdd QSF (0 : ZMod 2) :=
  ⟨stWordSF l, stWordSF_mem_evenPart hl⟩

@[simp] theorem wordW2_coe {l : SFWord} (hl : Even l.length) :
    ((wordW2 hl : evenOdd QSF (0 : ZMod 2)) : FockSF) = stWordSF l := rfl

/-- **The even part meets a weight space in the span of the even words of that weight.**

A vector of weight `h` is a combination of the (finitely many) words of weight `h`; splitting
that combination by parity gives an even and an odd piece, and the two parities are disjoint
(`evenOdd_disjoint_succ`), so an even vector has no odd piece at all. -/
theorem mem_span_even_words_of_mem_grading {h : ℂ} {x : FockSF}
    (hx : x ∈ gradingSF h) (hpar : x ∈ evenOdd QSF (0 : ZMod 2)) :
    x ∈ Submodule.span ℂ
      (stWordSF '' {l : SFWord | (sfWeight l : ℂ) = h ∧ Even l.length}) := by
  classical
  rw [gradingSF] at hx
  obtain ⟨c, hcsupp, hcx⟩ :=
    (Finsupp.mem_span_image_iff_linearCombination (R := ℂ) (v := stWordSF)).mp hx
  have hcsupp' : ∀ l ∈ c.support, (sfWeight l : ℂ) = h := fun l hl => hcsupp hl
  set A : SFWord →₀ ℂ := c.filter (fun l => ((l.length : ℕ) : ZMod 2) = 0) with hA
  set B : SFWord →₀ ℂ := c.filter (fun l => ¬ (((l.length : ℕ) : ZMod 2) = 0)) with hB
  have hsplit : c = A + B :=
    finsupp_parity_split (fun l : SFWord => ((l.length : ℕ) : ZMod 2)) 0 c
  have hAsupp : ∀ l ∈ A.support, ((l.length : ℕ) : ZMod 2) = 0 := by
    intro l hl
    have hmem := Finsupp.support_filter
      (p := fun l : SFWord => ((l.length : ℕ) : ZMod 2) = 0) (f := c) ▸ hl
    exact (Finset.mem_filter.mp hmem).2
  have hBsupp : ∀ l ∈ B.support, ((l.length : ℕ) : ZMod 2) = 0 + 1 := by
    intro l hl
    have hmem := Finsupp.support_filter
      (p := fun l : SFWord => ¬ (((l.length : ℕ) : ZMod 2) = 0)) (f := c) ▸ hl
    exact zmod_two_ne 0 ((l.length : ℕ) : ZMod 2) (Finset.mem_filter.mp hmem).2
  have hSA : Finsupp.linearCombination ℂ stWordSF A ∈ evenOdd QSF (0 : ZMod 2) :=
    lc_stWordSF_mem_evenOdd A 0 hAsupp
  have hSB : Finsupp.linearCombination ℂ stWordSF B ∈ evenOdd QSF ((0 : ZMod 2) + 1) :=
    lc_stWordSF_mem_evenOdd B _ hBsupp
  have hxeq : x = Finsupp.linearCombination ℂ stWordSF A
      + Finsupp.linearCombination ℂ stWordSF B := by
    rw [← hcx]
    conv_lhs => rw [hsplit]
    rw [map_add]
  have hSBeven : Finsupp.linearCombination ℂ stWordSF B ∈ evenOdd QSF (0 : ZMod 2) := by
    have : Finsupp.linearCombination ℂ stWordSF B
        = x - Finsupp.linearCombination ℂ stWordSF A := by rw [hxeq]; abel
    rw [this]
    exact Submodule.sub_mem _ hpar hSA
  have hSB0 : Finsupp.linearCombination ℂ stWordSF B = 0 :=
    Submodule.disjoint_def.mp (evenOdd_disjoint_succ (0 : ZMod 2)) _ hSBeven hSB
  have hxA : x = Finsupp.linearCombination ℂ stWordSF A := by rw [hxeq, hSB0, add_zero]
  rw [hxA]
  refine (Finsupp.mem_span_image_iff_linearCombination (R := ℂ) (v := stWordSF)).mpr ⟨A, ?_, rfl⟩
  intro l hl
  have hmem : l ∈ (c.filter (fun l => ((l.length : ℕ) : ZMod 2) = 0)).support := hl
  rw [Finsupp.support_filter] at hmem
  obtain ⟨hl1, hl2⟩ := Finset.mem_filter.mp hmem
  exact ⟨hcsupp' l hl1, ZMod.natCast_eq_zero_iff_even.mp hl2⟩

/-- **Word-by-word criterion for a graded piece to die in `A₂(W(2))`.** -/
theorem tripletW2_grading_le_O₂_of_words {n : ℤ}
    (hw : ∀ (l : SFWord) (hl : Even l.length), (sfWeight l : ℤ) = n →
      wordW2 hl ∈ O₂ tripletW2) :
    tripletW2.grading n ≤ O₂ tripletW2 := by
  intro x hx
  have hx1 : (x : FockSF) ∈ gradingSF ((n : ℤ) : ℂ) := hx
  have hx2 : (x : FockSF) ∈ evenOdd QSF (0 : ZMod 2) := x.2
  have hspan := mem_span_even_words_of_mem_grading hx1 hx2
  have hle : Submodule.span ℂ
      (stWordSF '' {l : SFWord | (sfWeight l : ℂ) = ((n : ℤ) : ℂ) ∧ Even l.length})
      ≤ Submodule.map (evenOdd QSF (0 : ZMod 2)).subtype (O₂ tripletW2) := by
    rw [Submodule.span_le]
    rintro _ ⟨l, ⟨hwt, hev⟩, rfl⟩
    have hwt' : (sfWeight l : ℤ) = n := by exact_mod_cast hwt
    exact ⟨wordW2 hev, hw l hev hwt', rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle hspan
  have hyx' : y = x := Subtype.ext hyx
  rwa [hyx'] at hy

/-- **The `C₂` target for `W(2)`, reduced to a statement about words.**

If every even word of conformal weight at least `N` gives a state lying in `C₂(W(2))`, then
`W(2)` is `C₂`-cofinite.  By `C2Cofinite_iff_exists_grading_le_O₂` (plus
`mem_span_even_words_of_mem_grading`) this hypothesis is *equivalent* to the conclusion, so it is
a faithful restatement of Abe's Theorem 3.9 and not a weakening of it.

**This is the precise remaining gap.**  Abe's proof of it (Prop. 3.7 + §3.3) is a spanning-set
computation in the free-field mode algebra: modulo `C₂`, any word of length `≥ 4` reduces to
shorter ones of the same weight, any length-`2` word `B_{m,n}` reduces to `±B_{m+n−1,1}` using
`L₋₁𝒱 ⊆ C₂`, and the resulting classes `Γ_m` satisfy
`Γ_m(e,f)Γ_k(e,f) = (1/m + 1/k)Γ_{m+k}(e,f)`, `Γ₃(e,e)² = Γ₇(e,e) = 0`, `ω̄⁵ = 0`, which cuts
the list down to `11` classes.  Formalising it needs the two-letter mode formula
`mode (YSF (stWordSF [(m,a),(n,b)])) k` — the analogue, for a family of states, of the
1550-line computation that produced `LSF_eq_mode` for the single state `ωSF`. -/
theorem tripletW2_C2Cofinite_of_words {N : ℕ}
    (hw : ∀ (l : SFWord) (hl : Even l.length), N ≤ sfWeight l → wordW2 hl ∈ O₂ tripletW2) :
    C2Cofinite tripletW2 := by
  refine C2Cofinite_of_grading_le_O₂ tripletW2 (N := N) ?_
  intro n hn
  refine tripletW2_grading_le_O₂_of_words ?_
  intro l hl hwt
  refine hw l hl ?_
  omega

/-! ## §7  Abe's Lemma 3.4, concretely: the `L₋₁`-relation among two-letter classes

The one part of Abe's §3.2 that needs no mode formula at all is his equation preceding
Lemma 3.4, `L₋₁B_{m,n} = (m+n)(B_{m+1,n} + B_{m,n+1})`: it only uses that `L₋₁ = T` is a
*derivation* on states, which for symplectic fermions is `Examples.SymplecticFermionT.T_mul`.
Since `L₋₁𝒱 ⊆ O₂` (`L_neg_one_mem_O₂`), it descends to a linear relation in `A₂(W(2))` among
the classes of the two-letter word states.  Iterating it collapses every two-letter class at a
given weight onto a single one — Abe's Lemma 3.4.

Both letters are shifted here, not just the level: writing `B(m,a,n,b)` for the class of
`χᵃ₋ₘ₋₁χᵇ₋ₙ₋₁|0⟩` the relation is `(m+1)B(m+1,a,n,b) + (n+1)B(m,a,n+1,b) = 0`, and its solution
is `B(m,a,n,b) = (−1)ⁿ binom(m+n, n) B(m+n,a,0,b)`. -/

/-- A two-letter word has even length, so its state lies in `W(2)`. -/
theorem even_length_pair (p q : ℕ × Fin 2) : Even ([p, q] : SFWord).length := ⟨1, rfl⟩

/-- **`T` on a two-letter word state** — the Leibniz rule, twice.  `T` shifts each creation
level by one, with the weight as coefficient. -/
theorem T_stWordSF_pair (p q : ℕ × Fin 2) :
    T (stWordSF [p, q])
      = ((p.1 : ℂ) + 1) • stWordSF [(p.1 + 1, p.2), q]
        + ((q.1 : ℂ) + 1) • stWordSF [p, (q.1 + 1, q.2)] := by
  simp only [stWordSF_cons, stWordSF_nil, mul_one]
  rw [T_mul, T_ι, T_ι, shiftMap_single, shiftMap_single, one_smul, one_smul, map_smul, map_smul,
    mul_smul_comm, smul_mul_assoc]
  abel

/-- **`L₋₁` of a two-letter state of `W(2)`, computed.** -/
theorem tripletW2_L_neg_one_pair (p q : ℕ × Fin 2) :
    tripletW2.L (-1) (wordW2 (even_length_pair p q))
      = ((p.1 : ℂ) + 1) • wordW2 (even_length_pair (p.1 + 1, p.2) q)
        + ((q.1 : ℂ) + 1) • wordW2 (even_length_pair p (q.1 + 1, q.2)) := by
  apply Subtype.ext
  rw [tripletW2_L_coe, LSF_neg_one_eq_T]
  simp only [wordW2_coe, Submodule.coe_add, Submodule.coe_smul]
  exact T_stWordSF_pair p q

/-- **Abe's `L₋₁`-relation (Lemma 3.4, the identity it is proved from), in `O₂`.** -/
theorem tripletW2_T_pair_mem_O₂ (p q : ℕ × Fin 2) :
    ((p.1 : ℂ) + 1) • wordW2 (even_length_pair (p.1 + 1, p.2) q)
      + ((q.1 : ℂ) + 1) • wordW2 (even_length_pair p (q.1 + 1, q.2)) ∈ O₂ tripletW2 := by
  rw [← tripletW2_L_neg_one_pair]
  exact L_neg_one_mem_O₂ tripletW2 _

/-- The class in `A₂(W(2))` of the two-letter state `χᵃ₋ₘ₋₁ χᵇ₋ₙ₋₁|0⟩` (Abe's `B_{m+1,n+1}`
up to the normalisation factor `m!n!/(m+n+1)!`, which is irrelevant to spanning statements). -/
noncomputable def BW2 (m : ℕ) (a : Fin 2) (n : ℕ) (b : Fin 2) : A₂ tripletW2 :=
  mk₂ tripletW2 (wordW2 (even_length_pair (m, a) (n, b)))

/-- **The two-letter relation in `A₂(W(2))`**: `(m+1)B(m+1,n) + (n+1)B(m,n+1) = 0`. -/
theorem BW2_rel (m n : ℕ) (a b : Fin 2) :
    ((m : ℂ) + 1) • BW2 (m + 1) a n b + ((n : ℂ) + 1) • BW2 m a (n + 1) b = 0 := by
  have h := tripletW2_T_pair_mem_O₂ (m, a) (n, b)
  have h0 : mk₂ tripletW2
      (((m : ℂ) + 1) • wordW2 (even_length_pair (m + 1, a) (n, b))
        + ((n : ℂ) + 1) • wordW2 (even_length_pair (m, a) (n + 1, b))) = 0 :=
    (mk₂_eq_zero_iff tripletW2).mpr h
  rw [map_add, map_smul, map_smul] at h0
  exact h0

/-- **Abe, Lemma 3.4.**  Every two-letter class collapses onto the one with second level
`0`: `B(m,a,n,b) = (−1)ⁿ binom(m+n, n) · B(m+n,a,0,b)`.

So at each conformal weight the two-letter part of `A₂(W(2))` is spanned by the four classes
`B(w−2, a, 0, b)`.  (Abe's `Γ`'s; the further collapse to finitely many *weights* is his §3.3,
which needs the two-letter mode formula and is not proved here.) -/
theorem BW2_reduce (a b : Fin 2) : ∀ (n m : ℕ),
    BW2 m a n b = ((-1 : ℂ) ^ n * ((m + n).choose n : ℂ)) • BW2 (m + n) a 0 b := by
  intro n
  induction n with
  | zero => intro m; simp
  | succ n ih =>
      intro m
      have hne : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      have hrel := BW2_rel m n a b
      have hB : BW2 m a (n + 1) b
          = (-(((m : ℂ) + 1) / ((n : ℂ) + 1))) • BW2 (m + 1) a n b := by
        have h1 : ((n : ℂ) + 1) • BW2 m a (n + 1) b
            = -(((m : ℂ) + 1) • BW2 (m + 1) a n b) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact hrel
        have h2 : BW2 m a (n + 1) b
            = ((n : ℂ) + 1)⁻¹ • (((n : ℂ) + 1) • BW2 m a (n + 1) b) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
        rw [h2, h1, smul_neg, smul_smul]
        rw [show -((((n : ℂ) + 1)⁻¹ * ((m : ℂ) + 1)) • BW2 (m + 1) a n b)
            = (-((((n : ℂ) + 1)⁻¹ * ((m : ℂ) + 1)))) • BW2 (m + 1) a n b from by
          rw [neg_smul]]
        congr 1
        field_simp
      have hidx : m + 1 + n = m + (n + 1) := by omega
      rw [hB, ih (m + 1), smul_smul, hidx]
      congr 1
      have hchoose : ((m + (n + 1)).choose (n + 1)) * (n + 1)
          = ((m + (n + 1)).choose n) * (m + 1) := by
        have h := Nat.choose_succ_right_eq (m + (n + 1)) n
        rw [h]
        congr 1
        omega
      have hchooseC : (((m + (n + 1)).choose (n + 1) : ℕ) : ℂ) * ((n : ℂ) + 1)
          = (((m + (n + 1)).choose n : ℕ) : ℂ) * ((m : ℂ) + 1) := by
        exact_mod_cast congrArg (fun k : ℕ => (k : ℂ)) hchoose
      field_simp
      linear_combination ((-1 : ℂ) ^ n) * hchooseC

end SympFerm

end VOA


