/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Modules.AdmissibleSemisimpleDecomp
import VOA.Modules.OrdSubmodule
import VOA.Classification.COne.ABDWeakAdmissibleComplete
import VOA.Classification.COne.AdmissibleOrdinaryC2

/-!
# Rational `C₂`-cofinite VOAs: admissible modules are direct sums of irreducible ordinary modules

`AdmissiblyRational.exists_iSupIndep_irreducible_ordinary`. For a `C₂`-cofinite VOA `W` with
`AdmissiblyRational W`, every admissible module `N` is the internal direct sum (independent, spanning)
of weak submodules `P i`. Each `P i`, with the restricted action, carries an **irreducible ordinary**
module structure.

This is a `C₂`-cofinite analogue of Dong–Li–Mason Thm 8.1(c) (*Twisted representations of vertex
operator algebras*, Math. Ann. **310** (1998) 571–600, at `g = 1`), with the decomposition of an
admissible module made explicit. "Rational" here is the library's `AdmissiblyRational` (weak
complements). The proof has three steps:
1. the decomposition into irreducible weak submodules (`AdmissibleModule.exists_iSupIndep_irreducible`,
   from Mathlib's semisimple-module theory);
2. Abe–Buhl–Dong Prop. 5.7 (`ABDWeakAdmissible.abdWeakIsAdmissible`: every weak module of a
   `C₂`-cofinite VOA is admissible);
3. `irreducible_admissible_isOrdinary` (irreducible admissible ⇒ ordinary, under `C₂`).

`⚠` `C₂`-cofiniteness is used in steps 2–3, and is an extra hypothesis relative to DLM. DLM prove
Thm 8.1 for rational VOAs without it, through the finite-dimensionality of `A(V)`; that version is
not formalised here. `M` ranges over `Type u`, the universe of `𝒱`.
-/

namespace VOA

open Classification.COne

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- A minimal nonzero weak submodule, with the restricted action, has no proper nonzero weak
submodules. It is stated for any weak-module structure equal to the restricted one. -/
theorem submodule_bot_or_top_of_minimal (N : AdmissibleModule W M)
    (P : WeakModule.Submodule' N.toWeakModule)
    (hmin : ∀ Q : WeakModule.Submodule' N.toWeakModule,
      Q.carrier ≤ P.carrier → Q.carrier = ⊥ ∨ Q.carrier = P.carrier)
    (A : WeakModule W P.carrier) (hA : A = N.toWeakModule.submodule P)
    (Q : WeakModule.Submodule' A) : Q.carrier = ⊥ ∨ Q.carrier = ⊤ := by
  subst hA
  -- push `Q` forward to a weak submodule of `N`
  let Q' : WeakModule.Submodule' N.toWeakModule :=
    { carrier := Q.carrier.map P.carrier.subtype
      act_mem := by
        rintro u n _ ⟨y, hy, rfl⟩
        exact ⟨_, Q.act_mem u n hy, rfl⟩ }
  have hle : Q'.carrier ≤ P.carrier := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  have hinj : Function.Injective (Submodule.map P.carrier.subtype) :=
    Submodule.map_injective_of_injective P.carrier.injective_subtype
  rcases hmin Q' hle with h0 | htop
  · left
    apply hinj
    rw [Submodule.map_bot]
    exact h0
  · right
    apply hinj
    rw [Submodule.map_top, Submodule.range_subtype]
    exact htop

/-- **A `C₂`-cofinite analogue of DLM Thm 8.1(c)** (Math. Ann. **310** (1998)), with the
decomposition. For a `C₂`-cofinite VOA that is rational in the library's sense
(`AdmissiblyRational`), every admissible module is an internal direct sum of weak submodules, each
an irreducible ordinary module under the restricted action. -/
theorem AdmissiblyRational.exists_iSupIndep_irreducible_ordinary (hC2 : C2Cofinite W)
    (hrat : AdmissiblyRational W) (N : AdmissibleModule W M) :
    ∃ (ι : Type u) (P : ι → WeakModule.Submodule' N.toWeakModule),
      iSupIndep (fun i => (P i).carrier) ∧ ⨆ i, (P i).carrier = ⊤ ∧
      ∀ i, ∃ O : OrdVModule W (P i).carrier,
        O.toWeakModule = N.toWeakModule.submodule (P i) ∧ O.IsIrreducible := by
  obtain ⟨ι, P, hind, htop, hmin⟩ := hrat.exists_iSupIndep_irreducible N
  refine ⟨ι, P, hind, htop, fun i => ?_⟩
  obtain ⟨Ni, hNi⟩ := ABDWeakAdmissible.abdWeakIsAdmissible hC2 (N.toWeakModule.submodule (P i))
  have hnt : Nontrivial (P i).carrier := Submodule.nontrivial_iff_ne_bot.mpr (hmin i).1
  have hirr : Ni.IsIrreducible :=
    ⟨hnt, submodule_bot_or_top_of_minimal N (P i) (hmin i).2 _ hNi⟩
  obtain ⟨O, hO⟩ := AdmissibleOrdinary.irreducible_admissible_isOrdinary hC2 Ni hirr
  exact ⟨O, hO.trans hNi,
    ⟨hnt, submodule_bot_or_top_of_minimal N (P i) (hmin i).2 _ (hO.trans hNi)⟩⟩

end VOA

section AxiomAudit
#print axioms VOA.AdmissiblyRational.exists_iSupIndep_irreducible_ordinary
end AxiomAudit
