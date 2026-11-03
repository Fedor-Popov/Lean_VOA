/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.LeadingKoszulBicomplex
import VOA.Examples.GradedUnitaryCohomologyKahler

/-!
# The leading cohomology `H⁰(Q⁻)` is the space of `g[t]`-invariants

This file connects the collapse theorem of `LeadingKoszulBicomplex` to the abstract
Kähler package `KahlerComplex` of `GradedUnitaryCohomologyKahler`, at one conformal weight.

The target statement of the explicit leading contraction in the coset BRST–Koszul transfer
argument (with the shifted grading) is

  `H⁰(Q⁻)(N, r) ≅ ((gr_r A) ⊗ B)^{g[t]}_N`.

Here it is proved in the following form. Fix a bidegree `a = (2r, 0)` of a `KahlerComplex`.
Suppose

* the three graded pieces `deg (a - (1,1))`, `deg a`, `deg (a + (1,1))` (ghost numbers
  `-1, 0, +1`, all at shifted degree `t = r`) are identified with the product totalizations of
  the diagonals `Y`, `X`, `Z` of a `LeadingBicomplex` (the last only injectively), so that
  `Q⁻` becomes `d_K + d_CE` (`hQX`, `hQY`);
* Koszul `H₀` of the two lowest rows is identified with a module `N` and with `κ → N`
  (`e0`, `e1`), so that the induced Chevalley–Eilenberg map becomes `v ↦ (ρ k v)_k` (`hρ`),
  for a family `ρ` of operators on `N` (the degree-preserving positive-mode action).

Then `leadCohomEquivInvariants : C.leadCohom a ≃ₗ[ℂ] invariants ρ`, and in particular
(`finrank_harmDeg_le_invariants`) the harmonic vectors of bidegree `a` have dimension at most
`dim (⋂_k ker ρ k)`: this is the bound `dim H⁰_full(N,R) ≤ dim ((gr_r A ⊗ B)^{g[t]})_N` of
the coset note.

Everything is proved outright from the listed hypotheses. The concrete relative BRST complex,
the identifications `eX, eY, eZ, e0, e1` for it, and the bicomplex relations are not built in
this file; for the Lee–Yang endpoint they are supplied by `KoszulConcreteBlocks.lean`
(`KoszulBlocks.leadModel`), `KoszulConcreteEndpoint.lean` and the `KoszulResidual*` files
(`KoszulResidual.koszulResidual_of_symbols`, `KoszulResidual.symbolResidual_endpoint`); see the
final comment.
-/

namespace VOA.LeadingKoszul

open VOA.GradedUnitaryCohomology
open Module (finrank)

universe u v

/-! ### From `ker d̄_CE` to invariants -/

section Invariants

variable {R : Type*} [CommRing R]
variable {X Y Z G : ℕ → Type v}
variable [∀ p, AddCommGroup (X p)] [∀ p, Module R (X p)]
variable [∀ p, AddCommGroup (Y p)] [∀ p, Module R (Y p)]
variable [∀ p, AddCommGroup (Z p)] [∀ p, Module R (Z p)]
variable [∀ p, AddCommGroup (G p)] [∀ p, Module R (G p)]
variable {N : Type*} [AddCommGroup N] [Module R N] {κ : Type*}

/-- The joint kernel `⋂_k ker ρ k` (the invariants of the positive-mode action). -/
def invariants (ρ : κ → N →ₗ[R] N) : Submodule R N := ⨅ k, LinearMap.ker (ρ k)

theorem mem_invariants (ρ : κ → N →ₗ[R] N) (n : N) : n ∈ invariants ρ ↔ ∀ k, ρ k n = 0 := by
  simp [invariants, Submodule.mem_iInf]

/-- **`ker d̄_CE` is the space of invariants**, once Koszul `H₀` of the two lowest rows is
identified with `N` and `κ → N` compatibly with `ρ`. -/
noncomputable def LeadingBicomplex.kerDbarEquivInvariants (B : LeadingBicomplex R X Y Z G)
    (e0 : B.KH0 ≃ₗ[R] N) (e1 : B.KH1 ≃ₗ[R] (κ → N)) (ρ : κ → N →ₗ[R] N)
    (hρ : ∀ v k, e1 (B.dbar v) k = ρ k (e0 v)) :
    LinearMap.ker B.dbar ≃ₗ[R] invariants ρ :=
  e0.ofSubmodules _ _ (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext n
    simp only [Submodule.mem_comap, LinearMap.mem_ker, mem_invariants]
    constructor
    · intro h k
      have := congrArg (fun w => e1 w k) h
      simpa [hρ] using this
    · intro h
      apply e1.injective
      funext k
      rw [map_zero, Pi.zero_apply]
      have := hρ (e0.symm n) k
      rw [LinearEquiv.apply_symm_apply] at this
      rw [LinearEquiv.coe_coe, this, h k])

end Invariants

/-! ### From the Kähler package to the bicomplex -/

section Kahler

variable {K : Type u} [AddCommGroup K] [Module ℂ K] (C : KahlerComplex K)
variable {X Y Z G : ℕ → Type v}
variable [∀ p, AddCommGroup (X p)] [∀ p, Module ℂ (X p)]
variable [∀ p, AddCommGroup (Y p)] [∀ p, Module ℂ (Y p)]
variable [∀ p, AddCommGroup (Z p)] [∀ p, Module ℂ (Z p)]
variable [∀ p, AddCommGroup (G p)] [∀ p, Module ℂ (G p)]
variable (B : LeadingBicomplex ℂ X Y Z G) (a : ℤ × ℤ)

/-- **The Koszul–CE model of the leading complex at bidegree `a`.** The three graded pieces of
ghost numbers `-1, 0, +1` are identified with the product totalizations of the diagonals of
`B`, intertwining `Q⁻` with `d_K + d_CE`. -/
structure LeadModel where
  eX : C.deg a ≃ₗ[ℂ] (∀ p, X p)
  eY : C.deg (a - shQm) ≃ₗ[ℂ] (∀ p, Y p)
  eZ : C.deg (a + shQm) →ₗ[ℂ] (∀ p, Z p)
  eZ_inj : Function.Injective eZ
  hQX : ∀ (x : C.deg a) (h : C.Qm x ∈ C.deg (a + shQm)), eZ ⟨C.Qm x, h⟩ = B.D0 (eX x)
  hQY : ∀ (y : C.deg (a - shQm)) (h : C.Qm y ∈ C.deg a), eX ⟨C.Qm y, h⟩ = B.Dm (eY y)

variable {C B a}

theorem Qm_mem_up (x : C.deg a) : C.Qm x ∈ C.deg (a + shQm) := C.Qm_deg a x x.2

theorem Qm_mem_mid (y : C.deg (a - shQm)) : C.Qm y ∈ C.deg a :=
  C.mem_deg_of_eq (by simp) (C.Qm_deg _ y y.2)

namespace LeadModel

variable (M : LeadModel C B a)

theorem D0_eX_eq_zero_iff (x : C.deg a) : B.D0 (M.eX x) = 0 ↔ C.Qm x = 0 := by
  rw [← M.hQX x (Qm_mem_up x)]
  constructor
  · intro h
    have := M.eZ_inj (h.trans (map_zero M.eZ).symm)
    exact congrArg Subtype.val this
  · intro h
    have : (⟨C.Qm x, Qm_mem_up x⟩ : C.deg (a + shQm)) = 0 := Subtype.ext h
    rw [this, map_zero]

/-- Cycles of `Q⁻` at bidegree `a` are the total cycles of the bicomplex. -/
noncomputable def cyclesEquiv : C.leadCycles a ≃ₗ[ℂ] B.cycles where
  toFun x := ⟨M.eX ⟨x, x.2.2⟩, (M.D0_eX_eq_zero_iff _).mpr x.2.1⟩
  invFun ξ := ⟨(M.eX.symm ξ : K), (M.D0_eX_eq_zero_iff _).mp (by
      rw [LinearEquiv.apply_symm_apply]; exact ξ.2), (M.eX.symm ξ).2⟩
  map_add' x y := by
    apply Subtype.ext
    change M.eX ⟨x + y, _⟩ = M.eX ⟨x, _⟩ + M.eX ⟨y, _⟩
    rw [← map_add]; rfl
  map_smul' c x := by
    apply Subtype.ext
    change M.eX ⟨c • x, _⟩ = c • M.eX ⟨x, _⟩
    rw [← map_smul]; rfl
  left_inv x := by
    apply Subtype.ext
    change ((M.eX.symm (M.eX ⟨x, x.2.2⟩) : C.deg a) : K) = x
    rw [LinearEquiv.symm_apply_apply]
  right_inv ξ := by
    apply Subtype.ext
    change M.eX ⟨(M.eX.symm ξ : K), _⟩ = ξ
    rw [Subtype.coe_eta, LinearEquiv.apply_symm_apply]

theorem mem_boundaries_iff (x : C.leadCycles a) :
    M.cyclesEquiv x ∈ B.boundaries ↔ x ∈ C.leadBoundaries a := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨(M.eY.symm w : K), (M.eY.symm w).2, ?_⟩
    have h1 := M.hQY (M.eY.symm w) (Qm_mem_mid _)
    rw [LinearEquiv.apply_symm_apply, hw] at h1
    have h2 := M.eX.injective h1
    exact congrArg Subtype.val h2
  · rintro ⟨y, hy, hyx⟩
    refine ⟨M.eY ⟨y, hy⟩, ?_⟩
    rw [← M.hQY ⟨y, hy⟩ (Qm_mem_mid _)]
    change M.eX _ = M.eX ⟨x, x.2.2⟩
    congr 1
    exact Subtype.ext hyx

/-- **`H⁰(Q⁻)` at bidegree `a` is the total ghost-zero cohomology of the bicomplex.** -/
noncomputable def leadCohomEquivH0 : C.leadCohom a ≃ₗ[ℂ] B.H0 :=
  Submodule.Quotient.equiv _ _ M.cyclesEquiv (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext ξ
    rw [Submodule.mem_comap, ← M.mem_boundaries_iff, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply])

/-- **The leading Koszul step.** Under the Koszul–CE model `M` and the identification of the
induced CE map with the action `ρ`, `H⁰(Q⁻)` at bidegree `a` is the space of invariants
`⋂_k ker ρ k`. -/
noncomputable def leadCohomEquivInvariants {N : Type*} [AddCommGroup N] [Module ℂ N]
    {κ : Type*}
    (e0 : B.KH0 ≃ₗ[ℂ] N) (e1 : B.KH1 ≃ₗ[ℂ] (κ → N)) (ρ : κ → N →ₗ[ℂ] N)
    (hρ : ∀ v k, e1 (B.dbar v) k = ρ k (e0 v)) : C.leadCohom a ≃ₗ[ℂ] invariants ρ :=
  M.leadCohomEquivH0.trans (B.equivKer.trans (B.kerDbarEquivInvariants e0 e1 ρ hρ))

theorem finrank_leadCohom_eq_invariants (M : LeadModel C B a) {N : Type*} [AddCommGroup N]
    [Module ℂ N] {κ : Type*}
    (e0 : B.KH0 ≃ₗ[ℂ] N) (e1 : B.KH1 ≃ₗ[ℂ] (κ → N)) (ρ : κ → N →ₗ[ℂ] N)
    (hρ : ∀ v k, e1 (B.dbar v) k = ρ k (e0 v)) :
    finrank ℂ (C.leadCohom a) = finrank ℂ (invariants ρ) :=
  (M.leadCohomEquivInvariants e0 e1 ρ hρ).finrank_eq

/-- **The harmonic bound of the coset note**: harmonic vectors of bidegree `a` (which compute
the full cohomology by the positive Hodge theory) have dimension at most that of the
invariants. -/
theorem finrank_harmDeg_le_invariants [FiniteDimensional ℂ K] (M : LeadModel C B a)
    {N : Type*} [AddCommGroup N] [Module ℂ N] {κ : Type*}
    (e0 : B.KH0 ≃ₗ[ℂ] N) (e1 : B.KH1 ≃ₗ[ℂ] (κ → N)) (ρ : κ → N →ₗ[ℂ] N)
    (hρ : ∀ v k, e1 (B.dbar v) k = ρ k (e0 v)) :
    finrank ℂ (C.harmDeg a) ≤ finrank ℂ (invariants ρ) :=
  (C.finrank_harmDeg_le_lead a).trans (M.finrank_leadCohom_eq_invariants e0 e1 ρ hρ).le

end LeadModel

end Kahler

/-! **Concrete instantiation (since supplied elsewhere).** As originally recorded: nothing in the
`LeadingKoszul*` files constructs the
relative semi-infinite complex of `L_{-4/3}(sl2) ⊗ L_1(sl2) ⊗ V^{-11/3}(sl2)` with three
`bc` ghost systems, nor its Kähler package. To obtain
`H⁰(Q⁻)(N,r) ≅ ((gr_r A) ⊗ B)^{g[t]}_N` for it, a concrete instantiation must supply:
(1) a `KahlerComplex` at weight `N`; (2) a `LeadingBicomplex` with Koszul rows
(`LeadingBicomplex.ofKoszulRows`, rows from `translatedWeyl`/`WeylDatum.rTensor` with
coefficients `gr A ⊗ B ⊗ Λ^q(c)`), i.e. the Chevalley–Eilenberg components and the relations
of `(d_K + d_CE)² = 0`, including stability of the Koszul ideal under the positive-mode action;
(3) a `LeadModel` (the identification of `Q⁻` with `d_K + d_CE`); (4) the identifications
`e0, e1` of Koszul `H₀` (from `WeylDatum.rowH0Equiv`) intertwining `d̄_CE` with the
degree-preserving action `ρ`. These are supplied for the endpoint geometry
`ConcreteHodge.endpointKahler hA` by `KoszulConcreteBlocks.lean` / `KoszulConcreteEndpoint.lean`
(`KoszulConcrete.endpointGrLeadKoszul_of_residual`) and the `KoszulResidual*` files. -/

end VOA.LeadingKoszul
