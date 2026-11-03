/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.LatticeGenInstance
import VOA.Modularity.GNProp8PBW
import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# The trivial VOA `V = ℂ𝟙` — first concrete input to Zhu's modularity theorem

Instantiates `latticeVOAGen` at the rank-zero lattice.  The carrier is
`FockN 0 ⊗ ℂ{0} ≅ ℂ`, so every hypothesis of the modularity theorem cascades from
one-dimensionality.
-/

namespace VOA

open VOA.IntegralLattice HeisenbergN

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The rank-zero lattice -/

theorem std0_even : (stdLattice 0).Even := by
  intro v
  refine ⟨0, ?_⟩
  show Matrix.toBilin' (1 : Matrix (Fin 0) (Fin 0) ℤ) v v = 2 * 0
  rw [Matrix.toBilin'_apply', Matrix.one_mulVec]
  simp [dotProduct]

theorem std0_posDef : (stdLattice 0).PosDef := by
  intro v hv
  refine absurd ?_ hv
  show (v : Fin 0 → ℤ) = 0
  funext i
  exact i.elim0

/-- **The trivial vertex operator algebra** `V = ℂ𝟙`, central charge `0`:
the lattice VOA of the rank-zero lattice. -/
noncomputable def trivialVOA : VertexOperatorAlgebra (LatGen.LatModuleGen (stdLattice 0)) :=
  LatGen.latticeVOAGen (stdLattice 0) std0_even std0_posDef

/-! ## The carrier is one-dimensional -/

instance : Unique ((stdLattice 0).carrier) :=
  inferInstanceAs (Unique (Fin 0 → ℤ))

theorem rank_stdLattice_zero : rank (stdLattice 0) = 0 :=
  Module.finrank_zero_of_subsingleton

instance : IsEmpty (Fin (rank (stdLattice 0))) := by
  rw [rank_stdLattice_zero]; infer_instance

/-- The rank-zero Fock space is `ℂ` (polynomials in no variables). -/
noncomputable def fockZeroEquiv : FockN (rank (stdLattice 0)) ≃ₗ[ℂ] ℂ :=
  (MvPolynomial.isEmptyAlgEquiv ℂ (ℕ × Fin (rank (stdLattice 0)))).toLinearEquiv

/-- The rank-zero group algebra `ℂ{0}` is `ℂ`. -/
noncomputable def chargeZeroEquiv : ((stdLattice 0).carrier →₀ ℂ) ≃ₗ[ℂ] ℂ :=
  Finsupp.uniqueLinearEquiv ℂ ℂ (default : (stdLattice 0).carrier)

/-- **The trivial-VOA carrier is `ℂ`.** -/
noncomputable def trivialCarrierEquiv : LatGen.LatModuleGen (stdLattice 0) ≃ₗ[ℂ] ℂ :=
  (TensorProduct.congr fockZeroEquiv chargeZeroEquiv).trans (TensorProduct.lid ℂ ℂ)

instance : FiniteDimensional ℂ (LatGen.LatModuleGen (stdLattice 0)) :=
  trivialCarrierEquiv.symm.finiteDimensional

theorem trivial_finrank : Module.finrank ℂ (LatGen.LatModuleGen (stdLattice 0)) = 1 := by
  rw [trivialCarrierEquiv.finrank_eq, Module.finrank_self]

/-- The vacuum maps to `1` under the carrier equivalence. -/
theorem trivialCarrierEquiv_vacuum :
    trivialCarrierEquiv (LatGen.latVacuumGen (stdLattice 0)) = 1 := by
  show trivialCarrierEquiv (LatGen.latStateGen (stdLattice 0) (vacuumN (rank (stdLattice 0))) 0) = 1
  unfold trivialCarrierEquiv LatGen.latStateGen
  simp only [fockZeroEquiv, chargeZeroEquiv, vacuumN, LatGen.eGen]
  simp [Subsingleton.elim (default : (stdLattice 0).carrier) 0, Finsupp.single_eq_same]

/-- The vacuum of the trivial VOA is nonzero. -/
theorem trivialVacuum_ne_zero : LatGen.latVacuumGen (stdLattice 0) ≠ 0 := by
  intro h
  have := trivialCarrierEquiv_vacuum
  rw [h, map_zero] at this
  exact zero_ne_one this

instance : Nontrivial (LatGen.LatModuleGen (stdLattice 0)) :=
  nontrivial_of_ne _ 0 trivialVacuum_ne_zero

/-! ## The one-dimensionality cascade -/

/-- Submodules of a space of dimension `≤ 1` are `⊥` or `⊤`. -/
theorem submodule_eq_bot_or_top_of_finrank_le_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (h1 : Module.finrank ℂ V ≤ 1) (S : Submodule ℂ V) :
    S = ⊥ ∨ S = ⊤ := by
  have hle : Module.finrank ℂ S ≤ 1 := le_trans (Submodule.finrank_le S) h1
  interval_cases h : Module.finrank ℂ S
  · exact Or.inl (Submodule.finrank_eq_zero.mp h)
  · refine Or.inr (Submodule.eq_top_of_finrank_eq ?_)
    have hge : 1 ≤ Module.finrank ℂ V := h ▸ Submodule.finrank_le S
    rw [h, le_antisymm h1 hge]

theorem trivial_submodule (S : Submodule ℂ (LatGen.LatModuleGen (stdLattice 0))) :
    S = ⊥ ∨ S = ⊤ :=
  submodule_eq_bot_or_top_of_finrank_le_one (le_of_eq trivial_finrank) S

/-- The vacuum spans: `𝒱 = ℂ𝟙`. -/
theorem trivial_span_vacuum :
    Submodule.span ℂ ({trivialVOA.vacuum} : Set (LatGen.LatModuleGen (stdLattice 0))) = ⊤ := by
  rcases trivial_submodule (Submodule.span ℂ ({trivialVOA.vacuum} : Set (LatGen.LatModuleGen (stdLattice 0)))) with h | h
  · exfalso
    exact trivialVacuum_ne_zero (by
      simpa [h] using Submodule.mem_span_singleton_self (R := ℂ) trivialVOA.vacuum)
  · exact h

/-- **Obligation 1**: the vacuum grade condition. -/
theorem trivial_vacuumGradeZero : VacuumGradeZero trivialVOA := by
  unfold VacuumGradeZero
  rw [trivial_span_vacuum]
  exact le_top

/-- **Obligation 5**: `C₂`-cofiniteness — a quotient of a finite-dimensional space. -/
theorem trivial_C2Cofinite : C2Cofinite trivialVOA := by
  unfold C2Cofinite A₂
  infer_instance

/-! ## Obligation 6: the Zhu algebra is semisimple -/

/-- A finite-dimensional `ℂ`-algebra of dimension `≤ 1` is a semisimple ring
(the zero ring vacuously; a one-dimensional algebra because it is simple over itself). -/
theorem isSemisimpleRing_of_finrank_le_one (R : Type*) [Ring R] [Algebra ℂ R]
    [FiniteDimensional ℂ R] (h1 : Module.finrank ℂ R ≤ 1) : IsSemisimpleRing R := by
  rcases subsingleton_or_nontrivial R with hsub | hnt
  · infer_instance
  · have hbt : (⊥ : Submodule R R) ≠ ⊤ := by
      intro h
      have h1mem : (1 : R) ∈ (⊥ : Submodule R R) := h ▸ Submodule.mem_top
      exact one_ne_zero ((Submodule.mem_bot R).mp h1mem)
    have hsimple : IsSimpleModule R R :=
      { exists_pair_ne := ⟨⊥, ⊤, hbt⟩
        eq_bot_or_eq_top := fun N => by
          rcases submodule_eq_bot_or_top_of_finrank_le_one h1 (N.restrictScalars ℂ) with h | h
          · exact Or.inl ((Submodule.restrictScalars_eq_bot_iff ℂ R R).mp h)
          · exact Or.inr ((Submodule.restrictScalars_eq_top_iff ℂ R R).mp h) }
    infer_instance

theorem trivial_semisimpleA :
    letI := instRingA trivialVOA; IsSemisimpleRing (A trivialVOA) := by
  letI := instRingA trivialVOA
  letI := instAlgebraA trivialVOA
  haveI : FiniteDimensional ℂ (A trivialVOA) := by unfold A; infer_instance
  refine isSemisimpleRing_of_finrank_le_one _ ?_
  calc Module.finrank ℂ (A trivialVOA)
      ≤ Module.finrank ℂ (LatGen.LatModuleGen (stdLattice 0)) := by
        unfold A; exact Submodule.finrank_quotient_le _
    _ = 1 := trivial_finrank

/-! ## Obligation 7: the adjoint module has conformal weight 0 (any VOA) -/

/-- **The adjoint module of any VOA has conformal weight `0`** (given `𝟙 ≠ 0`): its weights
lie in `0 + ℕ` by positivity. -/
theorem adjoint_hasConformalWeight (W : VertexOperatorAlgebra 𝒱) (hvac : W.vacuum ≠ 0) :
    HasConformalWeight (adjointModule W) 0 := by
  constructor
  · intro hbot
    apply hvac
    have h0 : ((0 : ℤ) : ℂ) = (0 : ℂ) := by norm_num
    have := adjWeight_cast W 0
    rw [h0] at this
    have hmem : W.vacuum ∈ (adjointModule W).weight 0 := by
      show W.vacuum ∈ adjWeight W 0
      rw [this]; exact W.vacuum_mem
    rw [hbot] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  · intro α hα
    by_cases h : ∃ m : ℤ, (m : ℂ) = α
    · obtain ⟨m, rfl⟩ := h
      have hm : ¬ m < 0 := by
        intro hneg
        exact hα (by show adjWeight W _ = ⊥; rw [adjWeight_cast W m, W.positivity m hneg])
      refine ⟨m.toNat, ?_⟩
      rw [zero_add]
      exact_mod_cast (Int.toNat_of_nonneg (not_lt.mp hm)).symm
    · exact absurd (by show adjWeight W α = ⊥; exact adjWeight_eq_bot W (not_exists.mp h)) hα

/-! ## The adjoint module of the trivial VOA is irreducible -/

theorem trivial_adjoint_irreducible :
    OrdVModule.IsIrreducible (adjointModule trivialVOA) :=
  ⟨inferInstance, fun P => trivial_submodule P.carrier⟩

/-- The adjoint module of the trivial VOA, bundled as an irreducible module. -/
noncomputable def trivialAdjointIrr : IrrModule trivialVOA where
  carrier := LatGen.LatModuleGen (stdLattice 0)
  isMod := adjointModule trivialVOA
  irreducible := trivial_adjoint_irreducible

/-! ## Obligation 3: the bottom `A(𝒱)`-module is simple -/

theorem trivial_isSimpleAMod (hlw : IsLowestWeight (adjointModule trivialVOA) 0) :
    IsSimpleAMod (lowestAMod hlw) := by
  constructor
  · -- the bottom contains the (nonzero) vacuum
    have h0 : ((0 : ℤ) : ℂ) = (0 : ℂ) := by norm_num
    have hcast := adjWeight_cast trivialVOA 0
    rw [h0] at hcast
    have hmem : trivialVOA.vacuum ∈ (adjointModule trivialVOA).weight 0 := by
      show trivialVOA.vacuum ∈ adjWeight trivialVOA 0
      rw [hcast]; exact trivialVOA.vacuum_mem
    exact ⟨⟨trivialVOA.vacuum, hmem⟩, 0, by
      intro h
      exact trivialVacuum_ne_zero (congrArg Subtype.val h)⟩
  · intro S
    have hfr : Module.finrank ℂ ((adjointModule trivialVOA).weight 0) ≤ 1 :=
      le_trans (Submodule.finrank_le _) (le_of_eq trivial_finrank)
    exact submodule_eq_bot_or_top_of_finrank_le_one hfr S.carrier

/-! ## The assembled first input to Zhu's modularity theorem -/

set_option maxHeartbeats 1000000 in
/-- **Zhu's modularity theorem, instantiated at the trivial VOA**, with the classification input
`card Φ = 1` ("the trivial VOA is holomorphic")
as a hypothesis.  That input is a theorem, `trivial_card_Φ` (`TrivialRationalityLattice.lean`),
and `AKZhuModularity.trivial_exists_zhuModularity_etingofFinite` reaches the modularity conclusion
without `Finite (Φ trivialVOA)`, without `hcard`, and without `VOA.pbw`.  All seven other
hypotheses are discharged above.  The instance `Finite (Φ trivialVOA)` is also a theorem
(`VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite_pbw trivial_C2Cofinite`), and the closed form of
this statement, with both inputs discharged, is `trivialVOA_zhuModularity_closed`
(`Modularity/ZhuModularityCanonical.lean`). -/
theorem trivialVOA_zhuModularity [Finite (Φ trivialVOA)]
    (hcard : Nat.card (Φ trivialVOA) = 1) :
    ∃ D : ModularData trivialVOA (Fin 1),
      D.Mfam = (fun _ => trivialAdjointIrr) ∧ D.h = (fun _ => 0) ∧
        ZhuModularityAnalytic D := by
  refine zhuModularity_pinned_of_C2Cofinite_voaPBW
    (fun _ => trivialAdjointIrr) (fun _ => 0)
    trivial_C2Cofinite trivial_semisimpleA
    (by simpa using hcard.symm)
    (fun _ => adjoint_hasConformalWeight trivialVOA trivialVacuum_ne_zero)
    (fun j k hjk _ => absurd (Subsingleton.elim j k) hjk)

end VOA
