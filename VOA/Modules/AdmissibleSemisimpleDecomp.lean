/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Modules.AdmissibleModule
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Adjoin.Basic

/-!
# Completely reducible admissible modules are direct sums of irreducible weak submodules

`AdmissibleModule.IsCompletelyReducible` asks that every weak submodule be complemented. This file
derives the direct-sum form: the module is the independent supremum of a family of **irreducible**
(minimal nonzero) weak submodules.

* `invariant_exists_iSupIndep_minimal`: the abstract statement for any set `S` of endomorphisms. If
  every `S`-invariant subspace has an `S`-invariant complement, then `M` is the independent sum of
  minimal nonzero `S`-invariant subspaces.
* `AdmissibleModule.exists_iSupIndep_irreducible`: the specialisation to the modes of an
  admissible module.
* `AdmissiblyRational.exists_iSupIndep_irreducible`: so, for a rational VOA, every admissible module
  is an internal direct sum of irreducible weak submodules.

## Method

Let `R = ℂ⟨S⟩ ⊆ End M`. `S`-invariant subspaces are exactly the `R`-submodules. The hypothesis says
`Submodule R M` is complemented, which is Mathlib's `IsSemisimpleModule R M`, and
`IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top` gives the decomposition.

## ⚠ What is not proved

That the summands are **ordinary**, or even admissible: a summand need not be level-graded inside `M`
(think of a diagonal copy inside `M' ⊕ M'[shift]`). The form "a direct sum of irreducible ordinary
modules" needs that step. It is supplied, for `C₂`-cofinite VOAs, by
`AdmissiblyRational.exists_iSupIndep_irreducible_ordinary`
(`Classification/COne/RationalAdmissibleDecomposition.lean`), a `C₂`-cofinite analogue of
Dong–Li–Mason, Math. Ann. **310** (1998), Thm 8.1(c); without `C₂` it is not proved here.
-/

namespace VOA

open Module (End)

section Invariant

universe u

variable {M : Type u} [AddCommGroup M] [Module ℂ M] (S : Set (End ℂ M))

/-- An `S`-invariant subspace. -/
def IsInvariant (P : Submodule ℂ M) : Prop := ∀ f ∈ S, ∀ x ∈ P, f x ∈ P

variable {S}

/-- An `S`-invariant subspace is invariant under the whole algebra `ℂ⟨S⟩`. -/
theorem IsInvariant.adjoin {P : Submodule ℂ M} (hP : IsInvariant S P) :
    ∀ r ∈ Algebra.adjoin ℂ S, ∀ x ∈ P, r x ∈ P := by
  intro r hr
  induction hr using Algebra.adjoin_induction with
  | mem f hf => exact hP f hf
  | algebraMap c => intro x hx; simpa [Algebra.algebraMap_eq_smul_one] using P.smul_mem c hx
  | add f g _ _ hf hg => intro x hx; exact P.add_mem (hf x hx) (hg x hx)
  | mul f g _ _ hf hg => intro x hx; exact hf _ (hg x hx)

/-- The `ℂ⟨S⟩`-submodule carried by an `S`-invariant subspace. -/
def IsInvariant.toSub {P : Submodule ℂ M} (hP : IsInvariant S P) :
    Submodule (Algebra.adjoin ℂ S) M where
  carrier := P
  add_mem' := P.add_mem
  zero_mem' := P.zero_mem
  smul_mem' r x hx := hP.adjoin r.1 r.2 x hx

@[simp] theorem IsInvariant.restrictScalars_toSub {P : Submodule ℂ M} (hP : IsInvariant S P) :
    hP.toSub.restrictScalars ℂ = P := rfl

theorem isInvariant_restrictScalars (Q : Submodule (Algebra.adjoin ℂ S) M) :
    IsInvariant S (Q.restrictScalars ℂ) := fun f hf _ hx =>
  Q.smul_mem (⟨f, Algebra.subset_adjoin hf⟩ : Algebra.adjoin ℂ S) hx

/-- Complements of invariant subspaces give a complemented lattice of `ℂ⟨S⟩`-submodules. -/
theorem complementedLattice_of_invariant
    (h : ∀ P : Submodule ℂ M, IsInvariant S P → ∃ Q, IsInvariant S Q ∧ IsCompl P Q) :
    ComplementedLattice (Submodule (Algebra.adjoin ℂ S) M) := by
  refine ⟨fun A => ?_⟩
  obtain ⟨Q, hQ, hc⟩ := h _ (isInvariant_restrictScalars A)
  refine ⟨hQ.toSub, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxA hxQ
    exact (Submodule.disjoint_def.mp hc.disjoint) x hxA hxQ
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x ∈ A.restrictScalars ℂ ⊔ Q := by rw [hc.codisjoint.eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    exact Submodule.add_mem_sup hy hz

/-- **The abstract decomposition.** If every `S`-invariant subspace has an `S`-invariant complement,
then `M` is the independent sum of a family of minimal nonzero `S`-invariant subspaces. -/
theorem invariant_exists_iSupIndep_minimal
    (h : ∀ P : Submodule ℂ M, IsInvariant S P → ∃ Q, IsInvariant S Q ∧ IsCompl P Q) :
    ∃ (ι : Type u) (P : ι → Submodule ℂ M), (∀ i, IsInvariant S (P i)) ∧ iSupIndep P ∧
      ⨆ i, P i = ⊤ ∧ ∀ i, P i ≠ ⊥ ∧
        ∀ Q : Submodule ℂ M, IsInvariant S Q → Q ≤ P i → Q = ⊥ ∨ Q = P i := by
  set R := Algebra.adjoin ℂ S
  haveI : IsSemisimpleModule R M := { toComplementedLattice := complementedLattice_of_invariant h }
  obtain ⟨s, hind, htop, hsimple⟩ := IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top R M
  let ρ := Submodule.restrictScalarsLatticeHom ℂ R M
  have hρ : ∀ m : Submodule R M, ρ m = m.restrictScalars ℂ := fun _ => rfl
  have hiind : iSupIndep (Subtype.val : s → Submodule R M) := (sSupIndep_iff s).mp hind
  refine ⟨↥s, fun m => (m : Submodule R M).restrictScalars ℂ, fun m => isInvariant_restrictScalars _,
    ?_, ?_, ?_⟩
  · intro i
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have heq : ρ (⨆ (j : s) (_ : j ≠ i), (j : Submodule R M))
        = ⨆ (j : s) (_ : j ≠ i), ρ (j : Submodule R M) := by
      simp only [map_iSup]
    have hx2' : x ∈ ρ (⨆ (j : s) (_ : j ≠ i), (j : Submodule R M)) := by rw [heq]; exact hx2
    exact Submodule.disjoint_def.mp (hiind i) x hx1 hx2'
  · have heq : ρ (⨆ (m : s), (m : Submodule R M)) = ⨆ (m : s), ρ (m : Submodule R M) := by
      simp only [map_iSup]
    show ⨆ (m : s), ρ (m : Submodule R M) = ⊤
    rw [← heq, ← sSup_eq_iSup', htop, map_top]
  · intro m
    have hatom : IsAtom (m : Submodule R M) := isSimpleModule_iff_isAtom.mp (hsimple m m.2)
    refine ⟨fun h0 => hatom.1 (Submodule.restrictScalars_injective ℂ R M
      (by rw [Submodule.restrictScalars_bot]; exact h0)), ?_⟩
    intro Q hQ hle
    have hle' : hQ.toSub ≤ (m : Submodule R M) := fun x hx => hle hx
    rcases hle'.lt_or_eq with hlt | heq
    · left
      have := hatom.2 _ hlt
      rw [← hQ.restrictScalars_toSub, this]
      rfl
    · right
      rw [← hQ.restrictScalars_toSub, heq]

end Invariant

section Admissible

universe w v

variable {𝒱 : Type w} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- The set of all modes `u₍ₙ₎` of a weak module, as endomorphisms. -/
def WeakModule.modeSet (A : WeakModule W M) : Set (End ℂ M) :=
  Set.range fun p : 𝒱 × ℤ => mode (A.YM p.1) p.2

theorem WeakModule.isInvariant_iff (A : WeakModule W M) (P : Submodule ℂ M) :
    IsInvariant A.modeSet P ↔ ∀ (u : 𝒱) (n : ℤ) {x : M}, x ∈ P → A.act u n x ∈ P := by
  constructor
  · intro h u n x hx
    exact h _ ⟨(u, n), rfl⟩ x hx
  · rintro h f ⟨⟨u, n⟩, rfl⟩ x hx
    exact h u n hx

/-- The weak submodule carried by an invariant subspace. -/
def WeakModule.submoduleOfInvariant (A : WeakModule W M) {P : Submodule ℂ M}
    (hP : IsInvariant A.modeSet P) : WeakModule.Submodule' A :=
  ⟨P, (A.isInvariant_iff P).mp hP⟩

/-- **A completely reducible admissible module is the internal direct sum of irreducible weak
submodules.** -/
theorem AdmissibleModule.exists_iSupIndep_irreducible (N : AdmissibleModule W M)
    (hN : N.IsCompletelyReducible) :
    ∃ (ι : Type v) (P : ι → WeakModule.Submodule' N.toWeakModule),
      iSupIndep (fun i => (P i).carrier) ∧ ⨆ i, (P i).carrier = ⊤ ∧
      ∀ i, (P i).carrier ≠ ⊥ ∧ ∀ Q : WeakModule.Submodule' N.toWeakModule,
        Q.carrier ≤ (P i).carrier → Q.carrier = ⊥ ∨ Q.carrier = (P i).carrier := by
  have h : ∀ P : Submodule ℂ M, IsInvariant N.toWeakModule.modeSet P →
      ∃ Q, IsInvariant N.toWeakModule.modeSet Q ∧ IsCompl P Q := by
    intro P hP
    obtain ⟨Q, hQ⟩ := hN (N.toWeakModule.submoduleOfInvariant hP)
    exact ⟨Q.carrier, (N.toWeakModule.isInvariant_iff _).mpr Q.act_mem, hQ⟩
  obtain ⟨ι, P, hinv, hind, htop, hmin⟩ := invariant_exists_iSupIndep_minimal h
  refine ⟨ι, fun i => N.toWeakModule.submoduleOfInvariant (hinv i), hind, htop, fun i =>
    ⟨(hmin i).1, fun Q hQ => (hmin i).2 Q.carrier ((N.toWeakModule.isInvariant_iff _).mpr Q.act_mem)
      hQ⟩⟩

/-- **For a rational VOA, every admissible module is an internal direct sum of irreducible weak
submodules.** -/
theorem AdmissiblyRational.exists_iSupIndep_irreducible (hrat : AdmissiblyRational W)
    {M : Type w} [AddCommGroup M] [Module ℂ M] (N : AdmissibleModule W M) :
    ∃ (ι : Type w) (P : ι → WeakModule.Submodule' N.toWeakModule),
      iSupIndep (fun i => (P i).carrier) ∧ ⨆ i, (P i).carrier = ⊤ ∧
      ∀ i, (P i).carrier ≠ ⊥ ∧ ∀ Q : WeakModule.Submodule' N.toWeakModule,
        Q.carrier ≤ (P i).carrier → Q.carrier = ⊥ ∨ Q.carrier = (P i).carrier :=
  N.exists_iSupIndep_irreducible (hrat N)

end Admissible

end VOA

section AxiomAudit
#print axioms VOA.invariant_exists_iSupIndep_minimal
#print axioms VOA.AdmissibleModule.exists_iSupIndep_irreducible
#print axioms VOA.AdmissiblyRational.exists_iSupIndep_irreducible
end AxiomAudit
