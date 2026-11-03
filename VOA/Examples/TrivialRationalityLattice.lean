/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Examples.ZhuInstantiation
import VOA.Modules.RationalityLattice

/-!
# Satisfiability witnesses for the whole rationality lattice, at `trivialVOA`

`Modules/RationalityLattice.lean` introduces nine predicates — `Regular`,
`DLMSimpleAdmissibleOrdinary`, `DLMFinitelyManyIrredAdmissible`, `ABDWeakIsAdmissible`,
`ABDIrreducibleWeakIsOrdinary`, `ABDRegularOfC2AndRational`, `LiC2CofiniteOfRegular`,
`GannonAdmissibleIsOrdinary` and `GannonRational` — and a predicate without a model is a real gap, not a cosmetic one: an accidentally over-strong predicate is vacuously
unsatisfiable, and every `¬ …` theorem stated against it is then true and worthless, while every
`… → …` theorem carrying it as a hypothesis is vacuously true.

This file closes that gap by exhibiting a single VOA that satisfies **all nine** — the trivial
(rank-zero lattice) VOA `trivialVOA = ℂ𝟙` of `Examples/ZhuInstantiation.lean`, which is already
the repository's witness for `AdmissiblyRational` (`Examples/TrivialAdmissiblyRational.lean`) and
for `IsSemisimpleRing (A 𝒱)`.

## What is proved, and how much of it is real work

The main theorem is `trivial_regular : Regular trivialVOA` — *every weak module over `ℂ𝟙` is completely
reducible, and every irreducible weak module is ordinary*.  Since `Regular` is the **strongest**
notion in the lattice, seven of the nine predicates then follow by composition, in one line each.

Two of the nine are genuine work beyond `Regular`:

* `ABDWeakIsAdmissible` quantifies over **all** weak modules, including infinite-dimensional ones,
  which over `ℂ𝟙` need not be ordinary at all (`OrdVModule` demands finite-dimensional weight
  spaces).  It is proved directly, by putting the whole module in level `0`.
* `DLMFinitelyManyIrredAdmissible` needs `Finite (Φadm trivialVOA)`, i.e. a classification of the
  irreducible admissible `ℂ𝟙`-modules up to isomorphism.  Proved here: irreducibility over `ℂ𝟙`
  forces `dim M = 1`, and any two one-dimensional carriers are intertwined by *any* linear
  isomorphism, because every mode is a scalar multiple of `𝟙₍₋₁₎ = id`.  So `Φadm trivialVOA` is a
  subsingleton, hence finite, and `Φ(trivialVOA)` is a singleton — which also makes
  `Holomorphic trivialVOA` true and gives `Holomorphic` its first model.

## The shape of the argument, once

`trivial_span_vacuum : span ℂ {𝟙} = ⊤` (`Examples/ZhuInstantiation.lean`) means every state is
`c·𝟙`, so **every** mode acts as `c·δ_{n,−1}·id`.  Three consequences drive everything below:

* every `ℂ`-subspace of every weak module is a weak submodule (`act_mem_of_span_vacuum`, already in
  `Modules/AdmissibleRationality.lean`), and `ℂ`-subspaces always have complements;
* `L₀ = ω₍₁₎` acts as `0`, so the one-point grading "everything at weight `0`" is a legitimate
  `OrdVModule` grading;
* an irreducible weak module is spanned by any nonzero vector, hence one-dimensional.

## Status
`sorry`-free, `admit`-free, `native_decide`-free.  No new axioms; the theorem
`VOA.pbw` is not used.  Every declaration is
`[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

universe u v

/-! ## §1  Weak modules over a VOA spanned by its vacuum -/

section SpanVacuum

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- The zero state acts as zero. -/
theorem WeakModule.act_zero_left (A : WeakModule W M) (n : ℤ) (x : M) :
    A.act (0 : 𝒱) n x = 0 := by
  simp only [WeakModule.act_def, map_zero, mode_zero, LinearMap.zero_apply]

/-- **The only mode of `c·𝟙`.**  `(c𝟙)₍ₙ₎ x = c·δ_{n,−1}·x`, for every weak module. -/
theorem WeakModule.act_smul_vacuum (A : WeakModule W M) (c : ℂ) (n : ℤ) (x : M) :
    A.act (c • W.vacuum) n x = c • (if n = -1 then x else 0) := by
  have hsm : A.act (c • W.vacuum) n x = c • A.act W.vacuum n x := by
    change mode (A.YM (c • W.vacuum)) n x = c • mode (A.YM W.vacuum) n x
    rw [map_smul, mode_smul]; rfl
  rw [hsm, A.act_vacuum]

/-- If `𝒱 = ℂ𝟙` then every state is a multiple of the vacuum. -/
theorem exists_smul_vacuum (hspan : Submodule.span ℂ ({W.vacuum} : Set 𝒱) = ⊤) (u : 𝒱) :
    ∃ c : ℂ, u = c • W.vacuum := by
  have hu : u ∈ Submodule.span ℂ ({W.vacuum} : Set 𝒱) := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu
  exact ⟨c, hc.symm⟩

/-- If `𝒱 = ℂ𝟙` then every mode other than `₍₋₁₎` is zero. -/
theorem WeakModule.act_eq_zero_of_span_vacuum
    (hspan : Submodule.span ℂ ({W.vacuum} : Set 𝒱) = ⊤) (A : WeakModule W M)
    (u : 𝒱) {n : ℤ} (hn : n ≠ -1) (x : M) : A.act u n x = 0 := by
  obtain ⟨c, rfl⟩ := exists_smul_vacuum hspan u
  rw [A.act_smul_vacuum, if_neg hn, smul_zero]

/-- If `𝒱 = ℂ𝟙` then `𝒱ₙ = 0` for every `n ≠ 0`: the whole space sits in degree `0` by
`vacuum_grade`, and the grading is a direct sum. -/
theorem grading_eq_bot_of_span_vacuum
    (hspan : Submodule.span ℂ ({W.vacuum} : Set 𝒱) = ⊤) {w : ℤ} (hw : w ≠ 0) :
    W.grading w = ⊥ := by
  have h0 : W.grading 0 = ⊤ := by rw [W.vacuum_grade]; exact hspan
  have hind := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W.grading).mp
    W.isInternal
  have hdis : Disjoint (W.grading w) (⨆ (j : ℤ) (_ : j ≠ w), W.grading j) :=
    iSupIndep_def.mp hind.1 w
  have htop : (⨆ (j : ℤ) (_ : j ≠ w), W.grading j) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← h0]
    exact le_iSup_of_le 0 (le_iSup_of_le (Ne.symm hw) le_rfl)
  rw [htop] at hdis
  exact disjoint_top.mp hdis

end SpanVacuum

/-! ## §2  The one-point grading

Both an `OrdVModule` weight family (indexed by `ℂ`) and an `AdmissibleModule` level family
(indexed by `ℤ`) are needed below, and in both cases everything sits in a single degree.  One
definition serves for both. -/

section PointGrading

variable (M : Type v) [AddCommGroup M] [Module ℂ M]

/-- The grading of `M` concentrated in the single degree `i₀`. -/
def pointGrading {ι : Type*} (i₀ i : ι) : Submodule ℂ M :=
  ⨆ _ : i = i₀, (⊤ : Submodule ℂ M)

variable {M}

@[simp] theorem pointGrading_self {ι : Type*} (i₀ : ι) :
    pointGrading M i₀ i₀ = ⊤ := iSup_pos rfl

theorem pointGrading_of_ne {ι : Type*} {i₀ i : ι} (h : i ≠ i₀) :
    pointGrading M i₀ i = ⊥ := iSup_neg h

theorem pointGrading_isInternal {ι : Type*} [DecidableEq ι] (i₀ : ι) :
    DirectSum.IsInternal (pointGrading M i₀) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro i
    by_cases hi : i = i₀
    · subst hi
      have hb : (⨆ (j : ι) (_ : j ≠ i), pointGrading M i j) = ⊥ :=
        iSup_eq_bot.mpr fun _ => iSup_eq_bot.mpr fun hj => pointGrading_of_ne hj
      rw [hb]
      exact disjoint_bot_right
    · rw [pointGrading_of_ne hi]
      exact disjoint_bot_left
  · exact le_antisymm le_top (le_iSup_of_le i₀ (le_of_eq (pointGrading_self (M := M) i₀).symm))

end PointGrading

/-! ## §3  Ordinary and admissible structures over a VOA spanned by its vacuum -/

section Structures

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **Every weak module over `ℂ𝟙` with finite-dimensional carrier is ordinary**, on the *same*
underlying weak module: `L₀ = ω₍₁₎` acts as `0` (because `1 ≠ −1`), so the one-point grading at
weight `0` satisfies the `L₀`-eigenvalue axiom, and the remaining axioms are immediate. -/
def WeakModule.toOrdOfSpanVacuum (hspan : Submodule.span ℂ ({W.vacuum} : Set 𝒱) = ⊤)
    (A : WeakModule W M) [FiniteDimensional ℂ M] : OrdVModule W M where
  toWeakModule := A
  weight := pointGrading M (0 : ℂ)
  isInternal := pointGrading_isInternal (0 : ℂ)
  L0_weight := by
    intro α x hx
    have hL : mode (A.YM W.conformalVector) 1 x = 0 :=
      A.act_eq_zero_of_span_vacuum hspan W.conformalVector (by decide) x
    by_cases hα : α = 0
    · subst hα; rw [hL, zero_smul]
    · rw [pointGrading_of_ne hα, Submodule.mem_bot] at hx
      subst hx
      rw [hL, smul_zero]
  finrank := fun _ => inferInstance
  boundedBelow := ⟨0, by
    intro α hα
    by_cases h : α = 0
    · subst h; simp
    · exact absurd (pointGrading_of_ne h) hα⟩

/-- **Every weak module over `ℂ𝟙` is admissible**, on the same underlying weak module: put all of
`M` in level `0`.  No finite-dimensionality is needed — which is exactly why this is not a
corollary of `toOrdOfSpanVacuum`. -/
def WeakModule.toAdmissibleOfSpanVacuum (hspan : Submodule.span ℂ ({W.vacuum} : Set 𝒱) = ⊤)
    (A : WeakModule W M) : AdmissibleModule W M where
  toWeakModule := A
  lev := pointGrading M (0 : ℤ)
  lev_eq_bot_of_neg := fun _ hk => pointGrading_of_ne (by omega)
  isInternal := pointGrading_isInternal (0 : ℤ)
  act_lev := by
    intro w p k a ha x hx
    obtain ⟨c, rfl⟩ := exists_smul_vacuum hspan a
    by_cases hk : k = 0
    · subst hk
      by_cases hp : p = -1
      · subst hp
        by_cases hw : w = 0
        · subst hw
          rw [show (0 : ℤ) + (0 - (-1) - 1) = 0 by ring, pointGrading_self]
          exact Submodule.mem_top
        · have ha0 : c • W.vacuum = 0 := by
            rw [grading_eq_bot_of_span_vacuum hspan hw, Submodule.mem_bot] at ha
            exact ha
          have hz : mode (A.YM (c • W.vacuum)) (-1 : ℤ) x = 0 := by
            rw [ha0]; exact A.act_zero_left _ _
          rw [hz]
          exact Submodule.zero_mem _
      · have hz : mode (A.YM (c • W.vacuum)) p x = 0 := by
          have := A.act_smul_vacuum c p x
          rw [WeakModule.act_def] at this
          rw [this, if_neg hp, smul_zero]
        rw [hz]
        exact Submodule.zero_mem _
    · rw [pointGrading_of_ne hk, Submodule.mem_bot] at hx
      subst hx
      rw [map_zero]
      exact Submodule.zero_mem _

/-- An irreducible weak module over `ℂ𝟙` is spanned by any nonzero vector, hence
finite-dimensional. -/
theorem finiteDimensional_of_irreducible_span_vacuum
    (hspan : Submodule.span ℂ ({W.vacuum} : Set 𝒱) = ⊤) (A : WeakModule W M)
    (hA : Nontrivial M ∧ ∀ P : WeakModule.Submodule' A, P.carrier = ⊥ ∨ P.carrier = ⊤) :
    FiniteDimensional ℂ M := by
  obtain ⟨hnt, hirr⟩ := hA
  haveI := hnt
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have key : Submodule.span ℂ ({x} : Set M) = ⊥ ∨ Submodule.span ℂ ({x} : Set M) = ⊤ :=
    hirr ⟨Submodule.span ℂ ({x} : Set M),
      fun u n {_} hy => WeakModule.act_mem_of_span_vacuum hspan A _ u n hy⟩
  rcases key with h | h
  · exfalso
    apply hx
    have hmem : x ∈ (⊥ : Submodule ℂ M) := by
      rw [← h]; exact Submodule.mem_span_singleton_self x
    simpa using hmem
  · exact Module.finite_def.mpr ⟨{x}, by simpa using h⟩

/-- …and it is one-dimensional. -/
theorem finrank_eq_one_of_irreducible_span_vacuum
    (hspan : Submodule.span ℂ ({W.vacuum} : Set 𝒱) = ⊤) (A : WeakModule W M)
    (hA : Nontrivial M ∧ ∀ P : WeakModule.Submodule' A, P.carrier = ⊥ ∨ P.carrier = ⊤) :
    Module.finrank ℂ M = 1 := by
  obtain ⟨hnt, hirr⟩ := hA
  haveI := hnt
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have key : Submodule.span ℂ ({x} : Set M) = ⊥ ∨ Submodule.span ℂ ({x} : Set M) = ⊤ :=
    hirr ⟨Submodule.span ℂ ({x} : Set M),
      fun u n {_} hy => WeakModule.act_mem_of_span_vacuum hspan A _ u n hy⟩
  rcases key with h | h
  · exfalso
    apply hx
    have hmem : x ∈ (⊥ : Submodule ℂ M) := by
      rw [← h]; exact Submodule.mem_span_singleton_self x
    simpa using hmem
  · have h1 : Module.finrank ℂ ↥(Submodule.span ℂ ({x} : Set M)) = 1 := finrank_span_singleton hx
    rw [h, finrank_top] at h1
    exact h1

end Structures

/-! ## §4  `Regular trivialVOA` — the main witness -/

/-- **The trivial VOA `ℂ𝟙` is regular**: every *weak* module is completely reducible, and every
irreducible weak module carries an ordinary structure on that same weak module.

This is Dong–Li–Mason's strongest notion (arXiv q-alg/9508018v1, Def. 3.1) — the honest referent of
the phrase "weakly rational" — so it is the single witness from which seven of the nine predicates
of `Modules/RationalityLattice.lean` follow by composition.

Both fields come from `span ℂ {𝟙} = ⊤`: every `ℂ`-subspace is a weak submodule and `ℂ`-subspaces
have complements; and an irreducible weak module is one-dimensional, so the one-point grading at
weight `0` makes it ordinary. -/
theorem trivial_regular : Regular trivialVOA := by
  constructor
  · intro M _ _ A P
    obtain ⟨q, hq⟩ := Submodule.exists_isCompl P.carrier
    exact ⟨⟨q, fun u n {_} hx =>
      WeakModule.act_mem_of_span_vacuum trivial_span_vacuum A q u n hx⟩, hq⟩
  · intro M _ _ A hA
    haveI : FiniteDimensional ℂ M :=
      finiteDimensional_of_irreducible_span_vacuum trivial_span_vacuum A hA
    exact ⟨A.toOrdOfSpanVacuum trivial_span_vacuum, rfl⟩

/-! ## §5  The seven free consequences -/

/-- `Regular ⟹ AdmissiblyRational` (Dong–Li–Mason Rmk. 3.2), instantiated.  Agrees with
`Examples/TrivialAdmissiblyRational.trivial_admissiblyRational`, which reaches the same conclusion
by the direct span-vacuum argument; both are kept, from independent routes. -/
theorem trivial_admissiblyRational_of_regular : AdmissiblyRational trivialVOA :=
  trivial_regular.admissiblyRational

/-- Gannon Def. 5.3.2 clause (3) holds at `trivialVOA`. -/
theorem trivial_gannonAdmissibleIsOrdinary : GannonAdmissibleIsOrdinary trivialVOA :=
  trivial_regular.gannonAdmissibleIsOrdinary

/-- Dong–Li–Mason Thm. 8.1(c) holds at `trivialVOA` — so the named hypothesis is satisfiable,
and no theorem carrying it is vacuous. -/
theorem trivial_dlmSimpleAdmissibleOrdinary : DLMSimpleAdmissibleOrdinary trivialVOA :=
  fun _ => trivial_regular.gannonAdmissibleIsOrdinary

/-- Abe–Buhl–Dong Cor. 5.8 holds at `trivialVOA`. -/
theorem trivial_abdIrreducibleWeakIsOrdinary : ABDIrreducibleWeakIsOrdinary trivialVOA :=
  trivial_regular.abdIrreducibleWeakIsOrdinary

/-- Abe–Buhl–Dong Thm. 4.5 (hard direction) holds at `trivialVOA` — trivially, since the
conclusion holds outright. -/
theorem trivial_abdRegularOfC2AndRational : ABDRegularOfC2AndRational trivialVOA :=
  fun _ _ => trivial_regular

/-- H. Li Thm. 3.8 holds at `trivialVOA`: `C₂`-cofiniteness is already proved there
(`Examples/ZhuInstantiation.trivial_C2Cofinite`). -/
theorem trivial_liC2CofiniteOfRegular : LiC2CofiniteOfRegular trivialVOA :=
  fun _ => trivial_C2Cofinite

/-- Abe–Buhl–Dong Prop. 5.7 holds at `trivialVOA`.

⚠ Not a corollary of `trivial_regular`: this quantifies over **all** weak modules, including
infinite-dimensional ones, which over `ℂ𝟙` are *not* ordinary (`OrdVModule` demands
finite-dimensional weight spaces).  It is proved directly, by putting all of `M` in level `0`. -/
theorem trivial_abdWeakIsAdmissible : ABDWeakIsAdmissible trivialVOA :=
  fun _ _ _ _ A => ⟨A.toAdmissibleOfSpanVacuum trivial_span_vacuum, rfl⟩

/-! ## §6  `Φadm(ℂ𝟙)` is a singleton, and the last two predicates -/

/-- **Any two irreducible admissible `ℂ𝟙`-modules are isomorphic.**  Both carriers are
one-dimensional, so *any* `ℂ`-linear isomorphism between them exists; and it automatically
intertwines every mode, because every mode of `c·𝟙` is `c·δ_{n,−1}·id` on both sides. -/
theorem trivial_irrAdmModule_iso (A B : IrrAdmModule trivialVOA) :
    IrrAdmModule.Iso trivialVOA A B := by
  haveI : FiniteDimensional ℂ A.carrier :=
    finiteDimensional_of_irreducible_span_vacuum trivial_span_vacuum _ A.irreducible
  haveI : FiniteDimensional ℂ B.carrier :=
    finiteDimensional_of_irreducible_span_vacuum trivial_span_vacuum _ B.irreducible
  have hr : Module.finrank ℂ A.carrier = Module.finrank ℂ B.carrier := by
    rw [finrank_eq_one_of_irreducible_span_vacuum trivial_span_vacuum _ A.irreducible,
      finrank_eq_one_of_irreducible_span_vacuum trivial_span_vacuum _ B.irreducible]
  refine ⟨⟨LinearEquiv.ofFinrankEq _ _ hr, ?_⟩⟩
  intro u n x
  obtain ⟨c, rfl⟩ := exists_smul_vacuum trivial_span_vacuum u
  rw [WeakModule.act_smul_vacuum, WeakModule.act_smul_vacuum, map_smul]
  by_cases hn : n = -1
  · rw [if_pos hn, if_pos hn]
  · rw [if_neg hn, if_neg hn, map_zero]

/-- `Φadm(ℂ𝟙)` has at most one element. -/
theorem trivial_subsingleton_Φadm : Subsingleton (Φadm trivialVOA) :=
  ⟨fun a b => Quotient.inductionOn₂ a b
    (fun A B => Quotient.sound (trivial_irrAdmModule_iso A B))⟩

/-- **`Φadm(ℂ𝟙)` is finite** — the one clause of the lattice that is not free from `Regular`. -/
theorem trivial_finite_Φadm : Finite (Φadm trivialVOA) :=
  haveI := trivial_subsingleton_Φadm
  Finite.of_subsingleton

/-- Dong–Li–Mason Thm. 8.1(b) holds at `trivialVOA`. -/
theorem trivial_dlmFinitelyManyIrredAdmissible :
    DLMFinitelyManyIrredAdmissible trivialVOA :=
  fun _ => trivial_finite_Φadm

/-- **`GannonRational trivialVOA`** — the ninth and last predicate of the lattice, and the
first model of Gannon Def. 5.3.2 anywhere in the repository. -/
theorem trivial_gannonRational : GannonRational trivialVOA :=
  gannonRational_of_regular trivial_regular trivial_dlmFinitelyManyIrredAdmissible

/-! ## §7  Bonus: `Holomorphic trivialVOA` -/

/-- `Φ(ℂ𝟙)` has at most one element, by the injection `Φ(𝒱) ↪ Φadm(𝒱)`. -/
theorem trivial_subsingleton_Φ : Subsingleton (Φ trivialVOA) :=
  ⟨fun a b => ΦtoΦadm_injective trivialVOA
    (@Subsingleton.elim _ trivial_subsingleton_Φadm _ _)⟩

/-- `Φ(ℂ𝟙)` has exactly one element: the adjoint module. -/
theorem trivial_card_Φ : Nat.card (Φ trivialVOA) = 1 := by
  haveI := trivial_subsingleton_Φ
  haveI : Nonempty (Φ trivialVOA) := ⟨Quotient.mk (IrrModule.setoid trivialVOA) trivialAdjointIrr⟩
  haveI : Unique (Φ trivialVOA) := uniqueOfSubsingleton (Classical.arbitrary _)
  exact Nat.card_unique

/-- **`trivialVOA` is holomorphic** (Gannon §5.3.1): `GannonRational` with a unique irreducible
module, necessarily `𝒱` itself.  The first model of `Holomorphic` in the repository — which matters,
because `Holomorphic` is the hypothesis of the Moonshine corollary. -/
theorem trivial_holomorphic : Holomorphic trivialVOA :=
  ⟨trivial_gannonRational, trivial_card_Φ⟩

end VOA
