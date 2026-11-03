/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.SuperNearVOA
import VOA.Examples.TripletWpTwoClose
import VOA.Examples.TripletWpTwoFelderStart
import VOA.Modules.RationalityLattice

/-!
# Irrationality of the lattice triplet at `p = 2`

This file proves that the lattice realization `tripletWVOA 2 hp` is not Gannon-rational.  The
argument stays entirely inside its ambient background-charge lattice VOA.  Strong generation by
the weight-two conformal vector and the three weight-three screening states implies that the
triplet carrier has no weight-one state.  On the other hand, the ambient restricted ordinary
module contains the charged ground state `e^alpha` in weight one, and

`F_(3) e^alpha = epsilon(-alpha,alpha) e^0`

is nonzero.  A weak-module complement of the triplet carrier would have to contain `e^alpha`,
and stability under `F_(3)` would then put this nonzero vacuum multiple in both complementary
summands, a contradiction.

No Felder exactness, maximal-null-ideal classification, symplectic-fermion realization, or
identification of standard kernels is used.
-/

namespace VOA

open scoped BigOperators
open Module (End)

universe u v

/-! ## An ordinary module's declared weights are its full `L_0` eigenspaces -/

/-- In an ordinary module, every `L_0` eigenvector of eigenvalue `alpha` belongs to the declared
weight space `M_alpha`.  The converse is the structure field `OrdVModule.L0_weight`; this direction
uses only that the weight decomposition is internal. -/
theorem OrdVModule.mem_weight_of_L0_eq {V : Type u} [AddCommGroup V] [Module ℂ V]
    {W : VertexOperatorAlgebra V} {M : Type v} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) {alpha : ℂ} {x : M}
    (hx : mode (N.YM W.conformalVector) 1 x = alpha • x) :
    x ∈ N.weight alpha := by
  classical
  letI := N.isInternal.chooseDecomposition N.weight
  have hzero : ∀ beta : ℂ, beta ≠ alpha → homogProj N.weight beta x = 0 := by
    intro beta hba
    have hcomm := homogProj_comm N.weight
      (mode (N.YM W.conformalVector) 1)
      (fun gamma y hy => by
        rw [N.L0_weight gamma y hy]
        exact (N.weight gamma).smul_mem gamma hy)
      beta x
    rw [hx, LinearMap.map_smul,
      N.L0_weight beta (homogProj N.weight beta x) (homogProj_mem N.weight beta x)] at hcomm
    have hz : (beta - alpha) • homogProj N.weight beta x = 0 := by
      rw [sub_smul, ← hcomm, sub_self]
    exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hba)
  obtain ⟨s, hs, -⟩ := exists_sum_homogProj N.weight x
  rw [← hs]
  refine Submodule.sum_mem _ (fun beta _ => ?_)
  by_cases hba : beta = alpha
  · subst beta
    exact homogProj_mem N.weight alpha x
  · rw [hzero beta hba]
    exact Submodule.zero_mem _

/-! ## A weight-one gap for strong generators of weight at least two -/

/-- Every strictly-negative-mode word in generators of weights at least two has weight zero
(the vacuum word) or weight at least two. -/
theorem isIterProd_weight_zero_or_ge_two {V : Type u} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) {S : Set V}
    (hS : ∀ s ∈ S, ∃ d : ℤ, 2 ≤ d ∧ s ∈ W.grading d)
    {x : V} (hx : IsIterProd W S x) :
    ∃ k : ℤ, (k = 0 ∨ 2 ≤ k) ∧ x ∈ W.grading k := by
  induction hx with
  | vacuum => exact ⟨0, Or.inl rfl, W.vacuum_mem⟩
  | step s hs m hm y _ ih =>
      obtain ⟨k, hk, hky⟩ := ih
      obtain ⟨d, hd, hds⟩ := hS s hs
      refine ⟨d + k + m - 1, Or.inr ?_, ?_⟩
      · rcases hk with rfl | hk <;> omega
      · have h := W.smul_mem_grading hds hky (-m)
        rwa [show d + k - (-m) - 1 = d + k + m - 1 from by ring] at h

/-- The weight-one part of the iterated-product span vanishes when all generators have weight at
least two. -/
theorem eq_zero_of_mem_iterProdSpan_and_grading_one
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) {S : Set V}
    (hS : ∀ s ∈ S, ∃ d : ℤ, 2 ≤ d ∧ s ∈ W.grading d)
    {x : V} (hxT : x ∈ iterProdSpan W S) (hx1 : x ∈ W.grading 1) : x = 0 := by
  have hSpos : ∀ s ∈ S, ∃ d : ℤ, 1 ≤ d ∧ s ∈ W.grading d := by
    intro s hs
    obtain ⟨d, hd, hsd⟩ := hS s hs
    exact ⟨d, by omega, hsd⟩
  have hxspan := mem_span_gradedWords W hSpos hxT hx1
  have hle : Submodule.span ℂ {y | IsIterProd W S y ∧ y ∈ W.grading 1} ≤ ⊥ := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨hyword, hy1⟩ := hy
    obtain ⟨k, hk, hyk⟩ := isIterProd_weight_zero_or_ge_two W hS hyword
    have hy0 : y = 0 := eq_zero_of_mem_grading_ne W (by rcases hk with rfl | hk <;> omega) hyk hy1
    simp [hy0]
  exact (Submodule.mem_bot ℂ).mp (hle hxspan)

namespace LatGen.Wp

open LatGen
open LatGen.Triplet
open LatGen.WpC2
open IntegralLattice

/-- At `p = 2`, each of the four lattice triplet generators has weight at least two: `omega` has
weight two, while `E,H,F` have weight three. -/
theorem tripGens_two_weight_ge_two (hp : 1 ≤ 2) :
    ∀ s ∈ tripGens 2, ∃ d : ℤ, 2 ≤ d ∧ s ∈ (tripletLatticeVOA 2 hp).grading d := by
  intro s hs
  rcases hs with rfl | hs
  · exact ⟨2, le_rfl, omegaTrip_mem_grading 2 hp⟩
  rcases hs with rfl | hs
  · exact ⟨3, by norm_num, by simpa using Etrip_mem_grading 2 hp⟩
  rcases hs with rfl | hs
  · exact ⟨3, by norm_num, by simpa using Htrip_mem_grading 2 hp⟩
  · rw [Set.mem_singleton_iff] at hs
    subst s
    exact ⟨3, by norm_num, by simpa using Ftrip_mem_grading 2 hp⟩

/-- The unconditional finite mixed table implies strong generation of lattice `W(2)`. -/
theorem strongGenWp_two (hp : 1 ≤ 2) : StrongGenWp 2 hp :=
  strongGenWp_of_genPairClosed 2 hp
    (genPairClosedWp_of_tail_mixed 2 hp (omegaTailWp_all 2 hp) (mixedPairsWp_two hp))

/-- The lattice triplet carrier has no weight-one state. -/
theorem eq_zero_of_mem_tripletW_two_and_grading_one (hp : 1 ≤ 2)
    {x : LatModuleGen (latP 2)} (hxW : x ∈ (tripletW 2 hp).carrier)
    (hx1 : x ∈ (tripletLatticeVOA 2 hp).grading 1) : x = 0 := by
  have hstrong : iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2)
      = (tripletW 2 hp).carrier := (strongGenWp_iff 2 hp).mp (strongGenWp_two hp)
  exact eq_zero_of_mem_iterProdSpan_and_grading_one (tripletLatticeVOA 2 hp)
    (tripGens_two_weight_ge_two hp) (hstrong.symm ▸ hxW) hx1

/-- The first nonzero opposite-charge product used in the nonsplitting argument:
`F_(3)e^alpha = epsilon(-alpha,alpha)e^0`. -/
theorem Ftrip_three_latChargeGen_alpha (hp : 1 ≤ 2) :
    (tripletLatticeVOA 2 hp).smul (Ftrip 2) 3
        (latChargeGen (latP 2) (alphaP 2))
      = latticeCocycle (latP 2) (-alphaP 2) (alphaP 2) •
          latChargeGen (latP 2) (-alphaP 2 + alphaP 2) := by
  have hform : (latP 2).form (-alphaP 2) (alphaP 2) = -4 := by
    have hneg : (latP 2).form (-alphaP 2) = -((latP 2).form (alphaP 2)) :=
      map_neg (latP 2).form (alphaP 2)
    rw [hneg, LinearMap.neg_apply, latP_form_alpha]
    norm_num
  rw [PreVertexAlgebra.smul_def, show Ftrip 2 = latChargeGen (latP 2) (-alphaP 2) from rfl,
    Y_latChargeGen, show (3 : ℤ) = -(latP 2).form (-alphaP 2) (alphaP 2) - 1 by rw [hform]; norm_num]
  exact smul_latChargeGen_bottom (latP 2) (-alphaP 2) (alphaP 2)

/-- The ambient restricted ordinary module is not completely reducible: its embedded triplet
carrier admits no weak-module complement. -/
theorem tripletAmbientOrdModuleTwo_not_completelyReducible (hp : 1 ≤ 2) :
    ¬ OrdVModule.IsCompletelyReducible (tripletAmbientOrdModuleTwo hp) := by
  intro hcr
  obtain ⟨Q, hcompl⟩ := hcr (tripletCarrierWeakSubmoduleTwo hp)
  let e : LatModuleGen (latP 2) := latChargeGen (latP 2) (alphaP 2)
  have heWeight : e ∈ (tripletAmbientOrdModuleTwo hp).weight 1 := by
    change e ∈ adjWeight (tripletLatticeVOA 2 hp) (1 : ℂ)
    rw [show (1 : ℂ) = ((1 : ℤ) : ℂ) by norm_num, adjWeight_cast]
    exact latChargeGen_alpha_mem_grade_one 2 hp
  have heSup : e ∈ (tripletCarrierWeakSubmoduleTwo hp).carrier ⊔ Q.carrier := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, q, haq⟩ := Submodule.mem_sup'.mp heSup
  let L0 : End ℂ (LatModuleGen (latP 2)) :=
    mode ((tripletAmbientOrdModuleTwo hp).YM (tripletWVOA 2 hp).conformalVector) 1
  have heL0 : L0 e = e := by
    change mode ((tripletAmbientOrdModuleTwo hp).YM (tripletWVOA 2 hp).conformalVector) 1 e = e
    simpa using (tripletAmbientOrdModuleTwo hp).L0_eq_weight heWeight
  have haL0mem : L0 (a : LatModuleGen (latP 2)) ∈
      (tripletCarrierWeakSubmoduleTwo hp).carrier := by
    exact (tripletCarrierWeakSubmoduleTwo hp).act_mem
      (tripletWVOA 2 hp).conformalVector 1 a.property
  have hqL0mem : L0 (q : LatModuleGen (latP 2)) ∈ Q.carrier := by
    exact Q.act_mem (tripletWVOA 2 hp).conformalVector 1 q.property
  have hsumL0 : L0 (a : LatModuleGen (latP 2)) + L0 (q : LatModuleGen (latP 2))
      = (a : LatModuleGen (latP 2)) + q := by
    calc
      L0 (a : LatModuleGen (latP 2)) + L0 (q : LatModuleGen (latP 2))
          = L0 ((a : LatModuleGen (latP 2)) + q) := (map_add L0 _ _).symm
      _ = L0 e := by rw [haq]
      _ = e := heL0
      _ = (a : LatModuleGen (latP 2)) + q := haq.symm
  have hdiff : L0 (a : LatModuleGen (latP 2)) - a = -(L0 (q : LatModuleGen (latP 2)) - q) := by
    calc
      L0 (a : LatModuleGen (latP 2)) - a =
          (L0 (a : LatModuleGen (latP 2)) + L0 q) - (a + L0 q) := by abel
      _ = ((a : LatModuleGen (latP 2)) + q) - (a + L0 q) := by rw [hsumL0]
      _ = -(L0 (q : LatModuleGen (latP 2)) - q) := by abel
  have hdiffP : L0 (a : LatModuleGen (latP 2)) - a ∈
      (tripletCarrierWeakSubmoduleTwo hp).carrier :=
    (tripletCarrierWeakSubmoduleTwo hp).carrier.sub_mem haL0mem a.property
  have hdiffQ : L0 (a : LatModuleGen (latP 2)) - a ∈ Q.carrier := by
    rw [hdiff]
    exact Q.carrier.neg_mem (Q.carrier.sub_mem hqL0mem q.property)
  have hdiff0 : L0 (a : LatModuleGen (latP 2)) - a = 0 := by
    apply (Submodule.mem_bot ℂ).mp
    exact hcompl.disjoint.le_bot ⟨hdiffP, hdiffQ⟩
  have haL0 : L0 (a : LatModuleGen (latP 2)) = a := sub_eq_zero.mp hdiff0
  have haWeight : (a : LatModuleGen (latP 2)) ∈
      (tripletAmbientOrdModuleTwo hp).weight 1 := by
    apply OrdVModule.mem_weight_of_L0_eq (tripletAmbientOrdModuleTwo hp)
    simpa [L0] using haL0
  have haGrade : (a : LatModuleGen (latP 2)) ∈ (tripletLatticeVOA 2 hp).grading 1 := by
    change (a : LatModuleGen (latP 2)) ∈ adjWeight (tripletLatticeVOA 2 hp) (1 : ℂ) at haWeight
    rw [show (1 : ℂ) = ((1 : ℤ) : ℂ) by norm_num, adjWeight_cast] at haWeight
    exact haWeight
  have ha0 : (a : LatModuleGen (latP 2)) = 0 :=
    eq_zero_of_mem_tripletW_two_and_grading_one hp a.property haGrade
  have hqe : (q : LatModuleGen (latP 2)) = e := by
    simpa [ha0] using haq
  have heQ : e ∈ Q.carrier := hqe ▸ q.property
  let f : (tripletW 2 hp).carrier := ⟨Ftrip 2, Ftrip_mem_tripletW 2 hp⟩
  have hmodeQ : (tripletAmbientOrdModuleTwo hp).act f 3 e ∈ Q.carrier :=
    Q.act_mem f 3 heQ
  have hmode : (tripletAmbientOrdModuleTwo hp).act f 3 e =
      latticeCocycle (latP 2) (-alphaP 2) (alphaP 2) •
        latChargeGen (latP 2) (-alphaP 2 + alphaP 2) := by
    exact Ftrip_three_latChargeGen_alpha hp
  have hvac : latChargeGen (latP 2) (-alphaP 2 + alphaP 2) ∈
      (tripletCarrierWeakSubmoduleTwo hp).carrier := by
    rw [neg_add_cancel]
    change latVacuumGen (latP 2) ∈ (tripletW 2 hp).carrier
    exact (tripletW 2 hp).vacuum_mem
  have hmodeP : (tripletAmbientOrdModuleTwo hp).act f 3 e ∈
      (tripletCarrierWeakSubmoduleTwo hp).carrier := by
    rw [hmode]
    exact (tripletCarrierWeakSubmoduleTwo hp).carrier.smul_mem _ hvac
  have hmode0 : (tripletAmbientOrdModuleTwo hp).act f 3 e = 0 := by
    apply (Submodule.mem_bot ℂ).mp
    exact hcompl.disjoint.le_bot ⟨hmodeP, hmodeQ⟩
  have hcoc : latticeCocycle (latP 2) (-alphaP 2) (alphaP 2) ≠ 0 :=
    Screen.latticeCocycle_ne_zero (latP 2) (-alphaP 2) (alphaP 2)
  have hcharge : latChargeGen (latP 2) (-alphaP 2 + alphaP 2) ≠ 0 :=
    latChargeGen_ne_zero 2 (-alphaP 2 + alphaP 2)
  exact (smul_ne_zero hcoc hcharge) (hmode.symm.trans hmode0)

/-- The lattice triplet VOA at `p = 2` is not Gannon-rational. -/
theorem not_gannonRational_tripletWVOA_two (hp : 1 ≤ 2) :
    ¬ GannonRational (tripletWVOA 2 hp) := by
  intro hrat
  exact tripletAmbientOrdModuleTwo_not_completelyReducible hp
    (hrat.completelyReducible (tripletAmbientOrdModuleTwo hp))

/-- The lattice triplet VOA at `p = 2` is not admissibly rational in the Dong--Li--Mason sense.
Indeed, admissible rationality would make every ordinary module completely reducible, including
the nonsplit ambient module above. -/
theorem not_admissiblyRational_tripletWVOA_two (hp : 1 ≤ 2) :
    ¬ AdmissiblyRational (tripletWVOA 2 hp) := by
  intro hrat
  exact tripletAmbientOrdModuleTwo_not_completelyReducible hp
    ((tripletAmbientOrdModuleTwo hp).isCompletelyReducible_of_admissiblyRational hrat)

/-- The first unconditional same-carrier package: lattice `W(2)` is `C_2`-cofinite but not
Gannon-rational. -/
theorem tripletWVOA_two_c2Cofinite_and_not_gannonRational (hp : 1 ≤ 2) :
    C2Cofinite (tripletWVOA 2 hp) ∧ ¬ GannonRational (tripletWVOA 2 hp) :=
  ⟨tripletWVOA_two_c2Cofinite hp, not_gannonRational_tripletWVOA_two hp⟩

/-- The literature-aligned irrationality package: lattice `W(2)` is `C_2`-cofinite but not
admissibly rational. -/
theorem tripletWVOA_two_c2Cofinite_and_not_admissiblyRational (hp : 1 ≤ 2) :
    C2Cofinite (tripletWVOA 2 hp) ∧ ¬ AdmissiblyRational (tripletWVOA 2 hp) :=
  ⟨tripletWVOA_two_c2Cofinite hp, not_admissiblyRational_tripletWVOA_two hp⟩

end LatGen.Wp
end VOA

section AxiomAudit
#print axioms VOA.OrdVModule.mem_weight_of_L0_eq
#print axioms VOA.LatGen.Wp.tripletAmbientOrdModuleTwo_not_completelyReducible
#print axioms VOA.LatGen.Wp.not_gannonRational_tripletWVOA_two
#print axioms VOA.LatGen.Wp.tripletWVOA_two_c2Cofinite_and_not_gannonRational
#print axioms VOA.LatGen.Wp.not_admissiblyRational_tripletWVOA_two
#print axioms VOA.LatGen.Wp.tripletWVOA_two_c2Cofinite_and_not_admissiblyRational
end AxiomAudit
