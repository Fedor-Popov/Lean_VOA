/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.SymplecticFermionSpan
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Symplectic fermions: the conformal weight grading

`χᵃ` has conformal weight `1`, so the creation mode `χᵃ_{-k-1}` raises the weight by `k + 1` and
the state `stWordSF l = χ^{a₁}_{-k₁-1} ⋯ χ^{aₙ}_{-kₙ-1}|0⟩` has weight `∑ᵢ (kᵢ + 1)`.  This file
turns that bookkeeping into an honest **internal direct sum decomposition** of `FockSF` with
finite-dimensional pieces — the `grading`, `isInternal` and `finrank` data that
`SuperVertexAlgebra` will consume.

All weights here are **positive integers** and the vacuum sits at weight `0`; note that both
parities carry integer weights, so spin-statistics fails for symplectic fermions and the
`ℂ`-grading below cannot be turned into a `ℤ`-grading indexed by parity.  The grading is indexed
by `ℂ` because that is what the super vertex algebra structure expects; the pieces at
non-natural-number weights are simply `⊥`.

## Why independence needs an argument

The obvious definition — the weight-`h` piece is the span of the words of weight `h` — makes the
spanning half trivial (`stWordSF_span` already says the words span everything) but says nothing
about **independence**, and independence is exactly where the naive picture fails: the words are
*not* a basis.  `stWordSF` is a product of `ι`'s in an exterior algebra, so reordering a word
permutes it up to a sign and a repeated index kills it outright.  A weight-`h` piece therefore
has many more spanning words than its dimension, and no counting argument on words can prove that
distinct weights meet only in `0`.

Rather than build a basis (Mathlib's exterior-algebra basis is indexed by `Finset`s of the mode
index type, and matching it up against words costs a permutation-sign bookkeeping we do not need),
we exhibit the grading as the **eigenspace decomposition of a single operator**: the weight
operator `L₀`.  Eigenspaces of one endomorphism for distinct eigenvalues are automatically
independent (`Module.End.eigenspaces_iSupIndep`), and each weight-`h` piece is contained in the
`h`-eigenspace of `L₀` by a one-line induction on words.  Independence then comes for free, and
because the pieces already span, they *are* the eigenspaces.

## Constructing `L₀`

`L₀` is the even derivation extending the diagonal map `χᵃ_{-k-1} ↦ (k+1)·χᵃ_{-k-1}` on the mode
space.  Mathlib's `CliffordAlgebra.lift` produces algebra maps, not derivations, so we use the
same dual-number device as `Examples/SymplecticFermionT` builds `T = L₋₁`: an algebra map into
`FockSF[ε]` is precisely a pair (algebra map, derivation along it), and `TrivSqZeroExt.snd_mul`
*is* the Leibniz rule.  The Clifford condition is free at `Q = 0`.

Only the interface `L0SF_mul`, `L0SF_one`, `L0SF_ι` is used afterwards, so `l0Hom` is sealed with
`attribute [irreducible]` — the same precaution the `T` file documents, since leaving a
`CliffordAlgebra.lift` application transparent lets tactics unfold it and elaboration blows up.
In fact nothing below performs a Clifford induction at all: everything is an induction on words.

## Finiteness

Each generator in a word contributes at least `1` to the weight, so a word of weight `n` has
length at most `n` and every level appearing in it is `< n`.  Words of weight `n` therefore form a
finite set — lists of bounded length over the finite alphabet `Fin n × Fin 2` — and the weight-`n`
piece is the span of a finite set.
-/

namespace VOA.SympFerm

open CliffordAlgebra
open scoped DualNumber

/-! ## The weight operator `L₀` -/

/-- The diagonal map `(k, a) ↦ (k+1)·(k, a)` on mode space: the conformal weight of the mode
`χᵃ_{-k-1}`, which is `k + 1` because `χᵃ` has weight `1`. -/
noncomputable def wtMap : SFModes →ₗ[ℂ] SFModes :=
  Finsupp.lsum ℂ fun p =>
    LinearMap.toSpanSingleton ℂ SFModes (((p.1 : ℂ) + 1) • Finsupp.single p (1 : ℂ))

@[simp] theorem wtMap_single (p : ℕ × Fin 2) (c : ℂ) :
    wtMap (Finsupp.single p c) = c • (((p.1 : ℂ) + 1) • Finsupp.single p (1 : ℂ)) := by
  simp [wtMap]

/-- The generator map into dual numbers: `v ↦ (ι v, ι (wt v))`.  Its `ε`-component will be the
derivation `L₀`. -/
noncomputable def l0Gen : SFModes →ₗ[ℂ] FockSF[ε] where
  toFun v := TrivSqZeroExt.inl (ι QSF v) + TrivSqZeroExt.inr (ι QSF (wtMap v))
  map_add' u v := by
    simp only [map_add, TrivSqZeroExt.inl_add, TrivSqZeroExt.inr_add]
    abel
  map_smul' c v := by
    simp only [RingHom.id_apply, map_smul, TrivSqZeroExt.inl_smul, TrivSqZeroExt.inr_smul,
      smul_add]

@[simp] theorem l0Gen_fst (v : SFModes) : (l0Gen v).fst = ι QSF v := by
  change (TrivSqZeroExt.inl (ι QSF v) + TrivSqZeroExt.inr (ι QSF (wtMap v))).fst = _
  rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]

@[simp] theorem l0Gen_snd (v : SFModes) : (l0Gen v).snd = ι QSF (wtMap v) := by
  change (TrivSqZeroExt.inl (ι QSF v) + TrivSqZeroExt.inr (ι QSF (wtMap v))).snd = _
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]

/-- The Clifford condition — free at `Q = 0`: the `fst` entry is `ι_sq_scalar` and the `snd` entry
is the polar form, and both vanish. -/
theorem l0Gen_sq (v : SFModes) : l0Gen v * l0Gen v = algebraMap ℂ FockSF[ε] (QSF v) := by
  have hQ : QSF v = 0 := rfl
  rw [hQ, map_zero]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, l0Gen_fst, ι_sq_scalar]
    change (algebraMap ℂ FockSF) (QSF v) = (0 : FockSF[ε]).fst
    rw [hQ, map_zero]; rfl
  · rw [TrivSqZeroExt.snd_mul, l0Gen_fst, l0Gen_snd]
    change (ι QSF v) * (ι QSF (wtMap v)) + (ι QSF (wtMap v)) * (ι QSF v) = (0 : FockSF[ε]).snd
    rw [ι_mul_ι_add_swap]
    change (algebraMap ℂ FockSF) (QuadraticMap.polar (⇑QSF) v (wtMap v)) = 0
    rw [show QuadraticMap.polar (⇑QSF) v (wtMap v) = 0 by simp [QuadraticMap.polar], map_zero]

/-- The algebra map whose `ε`-component is `L₀`. -/
noncomputable def l0Hom : FockSF →ₐ[ℂ] FockSF[ε] := CliffordAlgebra.lift QSF ⟨l0Gen, l0Gen_sq⟩

@[simp] theorem l0Hom_ι (v : SFModes) : l0Hom (ι QSF v) = l0Gen v := by
  rw [l0Hom, CliffordAlgebra.lift_ι_apply]

/-- `l0Hom` has first component the identity — both sides are algebra maps agreeing on
generators. -/
theorem l0Hom_fst (x : FockSF) : (l0Hom x).fst = x := by
  have h : (TrivSqZeroExt.fstHom ℂ FockSF FockSF).comp l0Hom = AlgHom.id ℂ FockSF := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext; intro v
    change (l0Hom (ι QSF v)).fst = ι QSF v
    rw [l0Hom_ι, l0Gen_fst]
  exact congrArg (fun (f : FockSF →ₐ[ℂ] FockSF) => f x) h

/-- **The weight operator** `L₀`, as the `ε`-component of `l0Hom`. -/
noncomputable def L0SF : Module.End ℂ FockSF where
  toFun x := (l0Hom x).snd
  map_add' x y := by simp only [map_add, TrivSqZeroExt.snd_add]
  map_smul' c x := by simp only [RingHom.id_apply, map_smul, TrivSqZeroExt.snd_smul]

@[simp] theorem L0SF_apply (x : FockSF) : L0SF x = (l0Hom x).snd := rfl

/-- **`L₀` is an even derivation** — weights add under multiplication of states, which is the
whole content of the grading. -/
theorem L0SF_mul (x y : FockSF) : L0SF (x * y) = x * L0SF y + L0SF x * y := by
  rw [L0SF_apply, map_mul, TrivSqZeroExt.snd_mul, l0Hom_fst, l0Hom_fst]
  rfl

@[simp] theorem L0SF_one : L0SF (1 : FockSF) = 0 := by
  rw [L0SF_apply, map_one]; rfl

@[simp] theorem L0SF_ι (v : SFModes) : L0SF (ι QSF v) = ι QSF (wtMap v) := by
  rw [L0SF_apply, l0Hom_ι, l0Gen_snd]

/-! `L0SF_mul`, `L0SF_one`, `L0SF_ι` are a complete interface, so `l0Hom` is sealed here: with a
`CliffordAlgebra.lift` application left transparent, tactics can unfold it and elaboration blows
up (the `T` file records two 35-minute incidents). -/

attribute [irreducible] l0Hom

/-- The weight operator scales a single creation mode by its weight `k + 1`. -/
theorem L0SF_gen (p : ℕ × Fin 2) :
    L0SF (ι QSF (Finsupp.single p (1 : ℂ)))
      = ((p.1 : ℂ) + 1) • ι QSF (Finsupp.single p (1 : ℂ)) := by
  rw [L0SF_ι, wtMap_single, one_smul, map_smul]

/-! ## The weight of a word -/

/-- The conformal weight of a word: `χᵃ_{-k-1}` contributes `k + 1`. -/
def sfWeight (l : SFWord) : ℕ := (l.map fun p => p.1 + 1).sum

@[simp] theorem sfWeight_nil : sfWeight [] = 0 := rfl

@[simp] theorem sfWeight_cons (p : ℕ × Fin 2) (rest : SFWord) :
    sfWeight (p :: rest) = p.1 + 1 + sfWeight rest := by
  simp [sfWeight]

/-- **Every word state is an `L₀`-eigenvector**, with eigenvalue its weight.  This is the one
computation the whole grading rests on, and it is a bare induction on the word: the Leibniz rule
turns "the operator is a derivation" into "weights add". -/
theorem L0SF_stWordSF (l : SFWord) : L0SF (stWordSF l) = (sfWeight l : ℂ) • stWordSF l := by
  induction l with
  | nil => rw [stWordSF_nil, L0SF_one, sfWeight_nil, Nat.cast_zero, zero_smul]
  | cons p rest ih =>
      rw [stWordSF_cons, L0SF_mul, ih, L0SF_gen, mul_smul_comm, smul_mul_assoc, ← add_smul]
      congr 1
      push_cast [sfWeight_cons]
      ring

/-! ## The grading -/

/-- The words of conformal weight `h`.  Empty unless `h` is a natural number. -/
def sfWordsAt (h : ℂ) : Set SFWord := {l : SFWord | (sfWeight l : ℂ) = h}

/-- **The conformal weight grading of the symplectic-fermion Fock space**: the weight-`h` piece is
spanned by the states the words of weight `h` create from the vacuum. -/
noncomputable def gradingSF (h : ℂ) : Submodule ℂ FockSF :=
  Submodule.span ℂ (stWordSF '' sfWordsAt h)

theorem stWordSF_mem_gradingSF (l : SFWord) : stWordSF l ∈ gradingSF (sfWeight l : ℂ) :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

/-- The vacuum has weight `0` — it is the empty word. -/
theorem vacSF_mem : vacSF ∈ gradingSF 0 := by
  have h := stWordSF_mem_gradingSF []
  rwa [sfWeight_nil, Nat.cast_zero, stWordSF_nil] at h

/-- Each graded piece sits inside the corresponding `L₀`-eigenspace: its spanning states are
eigenvectors of that eigenvalue, and an eigenspace is a submodule. -/
theorem gradingSF_le_eigenspace (h : ℂ) : gradingSF h ≤ Module.End.eigenspace L0SF h := by
  rw [gradingSF, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  change (sfWeight l : ℂ) = h at hl
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, L0SF_stWordSF, hl]

/-- **The graded pieces are independent.**  This is the half that the naive "span of the words
of weight `h`" definition does not give you, and it is where `L₀` earns its keep: the pieces are
contained in the eigenspaces of a *single* operator, and distinct eigenspaces of one operator
always meet in `0`.  (`Module.End.eigenspaces_iSupIndep` wants `Module.IsTorsionFree ℂ FockSF`,
which instance search supplies: `ℂ` is a domain and a `ℂ`-vector space has no zero smul
divisors.) -/
theorem gradingSF_iSupIndep : iSupIndep gradingSF :=
  (Module.End.eigenspaces_iSupIndep L0SF).mono gradingSF_le_eigenspace

/-- The graded pieces span, because the words already span (`stWordSF_span`) and each word lies in
the piece of its own weight. -/
theorem gradingSF_iSup_eq_top : ⨆ h : ℂ, gradingSF h = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← stWordSF_span, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  exact le_iSup gradingSF ((sfWeight l : ℕ) : ℂ) (stWordSF_mem_gradingSF l)

/-- **`FockSF` is the internal direct sum of its conformal weight spaces.** -/
theorem gradingSF_isInternal : DirectSum.IsInternal gradingSF :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    gradingSF_iSupIndep gradingSF_iSup_eq_top

/-- **A spanning family inside an independent family is that family.**  Pure lattice theory, and
the only place modularity of the lattice of submodules is used: with `R = ⨆_{j ≠ i} p j`,

`q i = ⊤ ⊓ q i = (p i ⊔ R) ⊓ q i = p i ⊔ (R ⊓ q i) = p i ⊔ ⊥`,

the middle step being the modular law (legal because `p i ≤ q i`) and the last one independence
of `q` together with `R ≤ ⨆_{j ≠ i} q j`. -/
theorem eq_of_le_of_iSupIndep_of_iSup_eq_top {ι : Type*}
    {p q : ι → Submodule ℂ FockSF} (hpq : ∀ i, p i ≤ q i) (hq : iSupIndep q)
    (hp : ⨆ i, p i = ⊤) (i : ι) : p i = q i := by
  have hsplit : ⨆ j, p j = p i ⊔ ⨆ (j) (_ : j ≠ i), p j := by
    refine le_antisymm (iSup_le fun j => ?_)
      (sup_le (le_iSup p i) (iSup₂_le fun j _ => le_iSup p j))
    by_cases hj : j = i
    · subst hj; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂ (f := fun (j : ι) (_ : j ≠ i) => p j) j hj)
  have hbot : (⨆ (j) (_ : j ≠ i), p j) ⊓ q i = ⊥ := by
    rw [inf_comm]
    exact le_bot_iff.mp
      (le_trans (inf_le_inf_left (q i) (iSup₂_mono fun j _ => hpq j)) (hq i).le_bot)
  have hmod := sup_inf_assoc_of_le (α := Submodule ℂ FockSF) (x := p i)
    (⨆ (j) (_ : j ≠ i), p j) (hpq i)
  rw [← hsplit, hp, top_inf_eq] at hmod
  rw [hmod, hbot, sup_bot_eq]

/-- Since the pieces are independent *and* span, they exhaust the eigenspaces: the containment of
`gradingSF_le_eigenspace` is an equality.  (Not needed downstream, but it is the statement that
`L₀` really is *the* grading operator, not merely one that happens to separate the pieces.) -/
theorem gradingSF_eq_eigenspace (h : ℂ) :
    gradingSF h = Module.End.eigenspace L0SF h :=
  eq_of_le_of_iSupIndep_of_iSup_eq_top gradingSF_le_eigenspace
    (Module.End.eigenspaces_iSupIndep L0SF) gradingSF_iSup_eq_top h

/-! ## Finite dimensionality

Every generator contributes at least `1`, so weight `n` bounds both the length of a word and every
level occurring in it — leaving only finitely many words. -/

/-- A generator in a word contributes at least its own weight to the total. -/
theorem sfWeight_succ_le_of_mem {l : SFWord} {p : ℕ × Fin 2} (hp : p ∈ l) :
    p.1 + 1 ≤ sfWeight l := by
  induction l with
  | nil => exact absurd hp (List.not_mem_nil)
  | cons q rest ih =>
      rw [sfWeight_cons]
      rcases List.mem_cons.mp hp with h | h
      · subst h; omega
      · have := ih h; omega

/-- A word of weight `n` has at most `n` letters. -/
theorem sfWeight_length_le (l : SFWord) : l.length ≤ sfWeight l := by
  induction l with
  | nil => simp
  | cons p rest ih =>
      rw [List.length_cons, sfWeight_cons]
      omega

/-- A word all of whose levels are `< n` is the image of a list over the finite alphabet
`Fin n × Fin 2`. -/
theorem exists_finList {n : ℕ} (l : SFWord) (h : ∀ p ∈ l, p.1 < n) :
    ∃ l' : List (Fin n × Fin 2), l'.map (fun q => ((q.1 : ℕ), q.2)) = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons p rest ih =>
      obtain ⟨l', hl'⟩ := ih fun q hq => h q (by simp [hq])
      exact ⟨(⟨p.1, h p (by simp)⟩, p.2) :: l', by rw [List.map_cons, hl']⟩

/-- **Only finitely many words have a given weight.**  They have length `≤ n` and all their
letters come from the finite alphabet `Fin n × Fin 2`, so they are the image of a finite set of
lists. -/
theorem sfWords_nat_finite (n : ℕ) : {l : SFWord | sfWeight l = n}.Finite := by
  refine Set.Finite.subset
    ((List.finite_length_le (Fin n × Fin 2) n).image
      fun l' : List (Fin n × Fin 2) => l'.map fun q => ((q.1 : ℕ), q.2)) ?_
  intro l hl
  have hw : sfWeight l = n := hl
  obtain ⟨l', hl'⟩ := exists_finList (n := n) l fun p hp => by
    have := sfWeight_succ_le_of_mem hp; omega
  refine ⟨l', ?_, hl'⟩
  have hlen : l'.length = l.length := by rw [← hl', List.length_map]
  change l'.length ≤ n
  have := sfWeight_length_le l
  omega

theorem sfWordsAt_finite (h : ℂ) : (sfWordsAt h).Finite := by
  by_cases hn : ∃ n : ℕ, (n : ℂ) = h
  · obtain ⟨n, rfl⟩ := hn
    refine (sfWords_nat_finite n).subset fun l hl => ?_
    exact Nat.cast_injective (hl : (sfWeight l : ℂ) = (n : ℂ))
  · refine Set.Finite.subset Set.finite_empty fun l hl => ?_
    exact absurd ⟨sfWeight l, (hl : (sfWeight l : ℂ) = h)⟩ hn

/-- **Every conformal weight space is finite dimensional** — it is the span of a finite set of
word states. -/
theorem gradingSF_finrank (h : ℂ) : FiniteDimensional ℂ (gradingSF h) :=
  FiniteDimensional.span_of_finite ℂ ((sfWordsAt_finite h).image stWordSF)

instance instFiniteDimensionalGradingSF (h : ℂ) : FiniteDimensional ℂ (gradingSF h) :=
  gradingSF_finrank h

end VOA.SympFerm
