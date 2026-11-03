/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.GradedUnitaryCohomologyKahler
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Filtered cohomology of a Kähler complex and the leading-cohomology bound

Continuation of `GradedUnitaryCohomologyKahler`. For a `KahlerComplex` `C` on a
finite-dimensional space (one conformal weight), let `H = ker 𝐐⁻ / im 𝐐⁻` be the full
cohomology and, for a set `A` of bidegrees `(2R, gh)`, let `cohomFilt A ≤ H` be the classes
having a `𝐐⁻`-closed representative supported on bidegrees in `A`.

* `exists_harm_rep_mem_degOn`: the harmonic representative of such a class is itself
  supported on `A` (Beem–Garner Remark 4.4: the `ℜ`-filtration on cohomology is refined by the
  grading of harmonic representatives).
* `cohomFilt_eq_map_harm`: `cohomFilt A` is exactly the image of the harmonic vectors supported
  on `A`, and `finrank_cohomFilt` computes its dimension.
* `finrank_cohomFilt_row_le_lead` (**the harmonic bound of the coset note**): for a finite set
  `S` of values of `2R` and a ghost number `g`,
  `dim (classes with a representative in ⊕_{j ∈ S} K_{(j,g)}) ≤ Σ_{j ∈ S} dim H(Q⁻)_{(j,g)}`.
  With `g = 0`, `S = {0, …, 2r}` and truncation `R ≥ 0`, this is
  `dim H⁰_full(N, R ≤ r) ≤ Σ_{s ≤ r} dim H⁰(Q⁻)(N, s)`, the shifted grading `t = R - gh/2`
  coinciding with `R` at ghost number zero.

All proved outright from the `KahlerComplex` hypotheses.
-/

namespace VOA.GradedUnitaryCohomology

open VOA.LeeYangCosetTransfer
open Module (finrank)

universe u

namespace KahlerComplex

variable {K : Type u} [AddCommGroup K] [Module ℂ K] (C : KahlerComplex K)

/-- Classes of the full cohomology `ker 𝐐⁻ / im 𝐐⁻` having a closed representative supported on
the bidegrees in `A`. -/
def cohomFilt (A : Set (ℤ × ℤ)) : Submodule ℂ (cycleQuotient C.D) :=
  Submodule.map (boundariesInCycles C.D).mkQ
    (Submodule.comap (LinearMap.ker C.D).subtype (C.degOn A))

/-- Harmonic vectors supported on `A`, as a subspace of the harmonic space. -/
def harmOn (A : Set (ℤ × ℤ)) : Submodule ℂ C.harm :=
  Submodule.comap C.harm.subtype (C.degOn A)

theorem degOn_union (A B : Set (ℤ × ℤ)) : C.degOn (A ∪ B) ≤ C.degOn A ⊔ C.degOn B := by
  refine iSup_le fun a => ?_
  rcases a.2 with h | h
  · exact (C.deg_le_degOn h).trans le_sup_left
  · exact (C.deg_le_degOn h).trans le_sup_right

theorem degOn_singleton (a : ℤ × ℤ) : C.degOn {a} ≤ C.deg a :=
  iSup_le fun b => by rw [b.2]

variable [FiniteDimensional ℂ K]

/-- **The harmonic representative stays in the filtration piece.** If `x` is `𝐐⁻`-closed and
supported on `A`, its class has a harmonic representative supported on `A`. -/
theorem exists_harm_rep_mem_degOn (A : Set (ℤ × ℤ)) {x : K} (hxD : C.D x = 0)
    (hxA : x ∈ C.degOn A) : ∃ z ∈ C.harm, z ∈ C.degOn A ∧ z - x ∈ LinearMap.range C.D := by
  obtain ⟨⟨z, hz⟩, hzx⟩ := harmonicToCohomology_surjective C.P C.pos C.herm C.D C.Dadj C.D_sq
    C.adj_D ((boundariesInCycles C.D).mkQ ⟨x, hxD⟩)
  have hzx' : z - x ∈ LinearMap.range C.D := by
    have := (Submodule.Quotient.eq _).mp hzx
    exact this
  refine ⟨z, hz, ?_, hzx'⟩
  obtain ⟨u, hu, v, hv, huv⟩ := C.exists_split A z
  have hvh : v ∈ C.harm := (C.harm_split A hu hv (huv ▸ hz)).2
  have hdisj : Disjoint Aᶜ A := by rw [disjoint_comm]; exact disjoint_compl_right
  have h1 : C.P v x = 0 := C.orth_degOn hdisj hv hxA
  have h2 : C.P v (z - x) = 0 := by
    obtain ⟨y, hy⟩ := hzx'
    rw [← hy]; exact C.P_harm_D v y hvh
  have h3 : C.P v u = 0 := C.orth_degOn hdisj hv hu
  have hvv : C.P v v = 0 := by
    have hz' : z = x + (z - x) := by abel
    have : C.P v z = 0 := by rw [hz', C.P.add_right, h1, h2, add_zero]
    rwa [huv, C.P.add_right, h3, zero_add] at this
  rw [huv, C.eq_zero_of_self v hvv, add_zero]
  exact hu

/-- **Filtered cohomology is spanned by filtered harmonic vectors.** -/
theorem cohomFilt_eq_map_harm (A : Set (ℤ × ℤ)) :
    C.cohomFilt A = Submodule.map (harmonicToCohomology C.D C.Dadj) (C.harmOn A) := by
  apply le_antisymm
  · rintro _ ⟨⟨x, hxD⟩, hxA, rfl⟩
    obtain ⟨z, hz, hzA, hzx⟩ := C.exists_harm_rep_mem_degOn A hxD hxA
    refine ⟨⟨z, hz⟩, hzA, ?_⟩
    apply (Submodule.Quotient.eq _).mpr
    exact hzx
  · rintro _ ⟨⟨z, hz⟩, hzA, rfl⟩
    exact ⟨⟨z, hz.1⟩, hzA, rfl⟩

omit [FiniteDimensional ℂ K] in
theorem finrank_harmOn (A : Set (ℤ × ℤ)) :
    finrank ℂ (C.harmOn A) = finrank ℂ (C.harm ⊓ C.degOn A : Submodule ℂ K) := by
  rw [← Submodule.map_comap_subtype]
  exact (Submodule.equivMapOfInjective _ C.harm.injective_subtype _).finrank_eq

/-- The dimension of a filtered piece of cohomology is the dimension of the harmonic vectors
supported there. -/
theorem finrank_cohomFilt (A : Set (ℤ × ℤ)) :
    finrank ℂ (C.cohomFilt A) = finrank ℂ (C.harm ⊓ C.degOn A : Submodule ℂ K) := by
  rw [C.cohomFilt_eq_map_harm, ← C.finrank_harmOn]
  exact (Submodule.equivMapOfInjective _
    (harmonicToCohomology_injective C.P C.pos C.D C.Dadj C.adj_D) _).finrank_eq.symm

/-- The bidegrees `(j, g)` with `j ∈ S`: ghost number `g`, twice the `ℜ`-degree in `S`. -/
def rowSet (S : Finset ℤ) (g : ℤ) : Set (ℤ × ℤ) := {a | a.1 ∈ S ∧ a.2 = g}

omit [FiniteDimensional ℂ K] in
theorem harm_inf_row_insert (i : ℤ) (S : Finset ℤ) (hi : i ∉ S) (g : ℤ) :
    (C.harm ⊓ C.degOn (rowSet (insert i S) g) : Submodule ℂ K) ≤
      C.harmDeg (i, g) ⊔ (C.harm ⊓ C.degOn (rowSet S g)) := by
  rintro x ⟨hxh, hxA⟩
  have hsub : rowSet (insert i S) g ⊆ {(i, g)} ∪ rowSet S g := by
    rintro ⟨j, k⟩ ⟨hj, rfl⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Or.inl rfl
    · exact Or.inr ⟨hj, rfl⟩
  obtain ⟨y, hy, z, hz, rfl⟩ :=
    Submodule.mem_sup.mp (C.degOn_union _ _ (C.degOn_mono hsub hxA))
  have hzc : z ∈ C.degOn ({(i, g)} : Set (ℤ × ℤ))ᶜ := by
    refine C.degOn_mono ?_ hz
    rintro ⟨j, k⟩ ⟨hj, rfl⟩ h
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, and_true] at h
    exact hi (h ▸ hj)
  obtain ⟨hyh, hzh⟩ := C.harm_split _ hy hzc hxh
  exact Submodule.add_mem_sup ⟨hyh, C.degOn_singleton _ hy⟩ ⟨hzh, hz⟩

omit [FiniteDimensional ℂ K] in
theorem degOn_empty : C.degOn ∅ = ⊥ := by
  rw [eq_bot_iff]; exact iSup_le fun a => a.2.elim

/-- Harmonic vectors in a row of bidegrees: at most the sum over the row of the harmonic
dimensions of each bidegree. -/
theorem finrank_harm_row_le (S : Finset ℤ) (g : ℤ) :
    finrank ℂ (C.harm ⊓ C.degOn (rowSet S g) : Submodule ℂ K) ≤
      ∑ j ∈ S, finrank ℂ (C.harmDeg (j, g)) := by
  induction S using Finset.induction_on with
  | empty =>
    have : rowSet (∅ : Finset ℤ) g = ∅ := by ext a; simp [rowSet]
    rw [this, C.degOn_empty, inf_bot_eq, finrank_bot]; simp
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    calc finrank ℂ (C.harm ⊓ C.degOn (rowSet (insert i S) g) : Submodule ℂ K)
        ≤ finrank ℂ (C.harmDeg (i, g) ⊔ (C.harm ⊓ C.degOn (rowSet S g)) : Submodule ℂ K) :=
          Submodule.finrank_mono (C.harm_inf_row_insert i S hi g)
      _ ≤ finrank ℂ (C.harmDeg (i, g)) +
            finrank ℂ (C.harm ⊓ C.degOn (rowSet S g) : Submodule ℂ K) :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ _ := Nat.add_le_add_left ih _

/-- **The harmonic bound** (coset note, §“Good action and harmonic bound”). For a finite set
`S` of values of `2R` and a ghost number `g`, the classes of the full cohomology `H(𝐐⁻)` having a
representative of ghost number `g` with `2R ∈ S` span at most `Σ_{j ∈ S} dim H(Q⁻)_{(j,g)}`
dimensions. At `g = 0` and `S = {0,…,2r}` (with `R ≥ 0`) this is
`dim H⁰_full(N, R ≤ r) ≤ Σ_{s ≤ r} dim H⁰(Q⁻)(N, s)`. -/
theorem finrank_cohomFilt_row_le_lead (S : Finset ℤ) (g : ℤ) :
    finrank ℂ (C.cohomFilt (rowSet S g)) ≤ ∑ j ∈ S, finrank ℂ (C.leadCohom (j, g)) := by
  rw [C.finrank_cohomFilt]
  exact (C.finrank_harm_row_le S g).trans
    (Finset.sum_le_sum fun j _ => C.finrank_harmDeg_le_lead (j, g))

end KahlerComplex

end VOA.GradedUnitaryCohomology
