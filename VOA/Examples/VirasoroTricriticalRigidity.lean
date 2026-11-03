/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroTricriticalNorm
import VOA.Examples.VirasoroSingularGram
import VOA.Examples.VirasoroMinimalChargeArithmetic
import VOA.Examples.VirasoroVacuumProjection

/-!
# Graded rigidity of the tricritical Ising minimal model

The actual weight-twelve expression is killed by L1 and L2 at charge 7/10,
so it vanishes in the simple vacuum quotient. Its operator-valued norm
has a nonzero first derivative there. The actual two-sided pairing
obstruction forces zero central motion, and fixed-charge reconstruction
trivializes every graded first-order deformation. No Kac determinant or
unproved general fusion normalization is assumed.
-/
namespace VOA.VirDeformModes
open Module (End)
open VirModule VirSimple VertexOperatorAlgebra Deform

/-- The central charge of the tricritical Ising model M(4,5). -/
noncomputable def tricriticalC : ℂ := 7/10

/-- The displayed rational charge agrees with the package's minimal-model formula. -/
theorem tricritical_minimal_charge : minimalCentralCharge 4 5=tricriticalC := by
  norm_num [minimalCentralCharge,tricriticalC]

/-- The same partition words with the nonnegative creation-index convention:
index j denotes L minus (j+2). This connects the certificate to the grading. -/
def tricriticalNatWords : Fin 21 → List ℕ := ![[10],[8,0],[7,1],[6,2],[6,0,0],[5,3],[5,1,0],[4,4],[4,2,0],[4,1,1],[4,0,0,0],[3,3,0],[3,2,1],[3,1,0,0],[2,2,2],[2,2,0,0],[2,1,1,0],[2,0,0,0,0],[1,1,1,1],[1,1,0,0,0],[0,0,0,0,0,0]]

/-- The finite certificate words are actual universal creation words. -/
theorem tricritical_word_eq (c : ℂ) (i : Fin 21) :
    virWord (virasoroVOA c).L (tricriticalWords i) (vacVec c)=
      negWordVir c (tricriticalNatWords i) := by
  fin_cases i <;>
    simp [tricriticalWords,tricriticalNatWords,virWord,Module.End.mul_apply,
      Module.End.one_apply,virasoroVOA_L_eq_Lop,negWordVir]

/-- Every summand has weight twelve, so the whole certified expression
lies in the actual weight-twelve subspace at every central charge. -/
theorem tricriticalState_mem_grading (c : ℂ) :
    tricriticalState (virasoroVOA c).L (vacVec c) ∈ gradingVir c 12 := by
  unfold tricriticalState
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  rw [tricritical_word_eq]
  have hw : SortedWord (tricriticalNatWords i) := by
    fin_cases i <;> decide
  have he : energyVir (tricriticalNatWords i)=12 := by
    fin_cases i <;> rfl
  exact VirGram56.negWordVir_mem_grading c 12 _ hw he

/-- Under the actual vacuum survival functional a creation word loses
its first letter only if that letter is L-minus-two; the multiplier is one half. -/
theorem tricritical_creation_survival (c : ℂ) (i : ℕ) (w : List ℕ) :
    InverseDS.VirasoroVerma.vacuumSurvival c (negWordVir c (i::w))=
      (if i=0 then (2:ℂ)⁻¹ else 0)*
        InverseDS.VirasoroVerma.vacuumSurvival c (negWordVir c w) := by
  rw [negWordVir_cons]
  have hh := InverseDS.VirasoroVerma.vacuumSurvival_mode c (i+1) (negWordVir c w)
  have hm : -((i+1:ℕ):ℤ)-1=-(i:ℤ)-2 := by push_cast; ring
  rw [hm] at hh
  simpa only [show i+1=1 ↔ i=0 by omega] using hh

/-- The actual scalar survival value is 8000 at every charge: only the
all-L-minus-two term contributes, with coefficient 512000 and six factors
of one half. This verifies that the certified vacuum state is nonzero. -/
theorem tricriticalState_survival (c : ℂ) :
    InverseDS.VirasoroVerma.vacuumSurvival c
      (tricriticalState (virasoroVOA c).L (vacVec c))=8000 := by
  simp only [tricriticalState,map_sum,map_smul,smul_eq_mul,tricritical_word_eq]
  norm_num [tricriticalNatWords,tricriticalCoefficients,Fin.sum_univ_succ,
    tricritical_creation_survival,negWordVir_nil]

/-- The finite singular-word expression never vanishes in the universal
vacuum module, independently of charge. Its specialization at 7/10 is
therefore a genuine nonzero singular vector. -/
theorem tricriticalState_ne_zero (c : ℂ) :
    tricriticalState (virasoroVOA c).L (vacVec c)≠0 := by
  intro hz
  have hh := tricriticalState_survival c
  rw [hz,map_zero] at hh
  norm_num at hh

/-- The actual universal vacuum modes with their ordinary scalar center.
This supplies the commutators used by the independently checked certificate. -/
noncomputable def tricriticalUniversalData (c : ℂ) : CentralVirasoroData (VirUniv c) where
  L := (virasoroVOA c).L
  central := c • 1
  comm m n := by
    simp only [virasoroVOA_L_eq_Lop,LieRing.of_associative_ring_bracket,Lop_bracket]
    by_cases h : m+n=0 <;> simp [h,smul_smul]
  central_comm n := by
    change (c • (1 : End ℂ (VirUniv c)))*(virasoroVOA c).L n=_
    simp

/-- The certified relation satisfies the two positive Ward equations in
the genuine universal vacuum module at charge 7/10. -/
theorem tricritical_universal_singular :
    Lop tricriticalC 1 (tricriticalState (virasoroVOA tricriticalC).L (vacVec tricriticalC))=0 ∧
    Lop tricriticalC 2 (tricriticalState (virasoroVOA tricriticalC).L (vacVec tricriticalC))=0 := by
  let A := tricriticalUniversalData tricriticalC
  have hv (n : ℤ) (hn : -1≤n) : A.L n (vacVec tricriticalC)=0 := by
    simpa only [A,tricriticalUniversalData,virasoroVOA_L_eq_Lop] using Lop_vacuum tricriticalC hn
  have hK : A.central=(7/10:ℂ) • 1 := rfl
  constructor
  · simpa only [A,tricriticalUniversalData,virasoroVOA_L_eq_Lop] using tricritical_L1_zero A _ hv hK
  · simpa only [A,tricriticalUniversalData,virasoroVOA_L_eq_Lop] using tricritical_L2_zero A _ hv hK

/-- The actual simple quotient kills the certified positive-weight singular
state. This uses ordinary radical invariance, not a deformed invariant form. -/
theorem tricritical_simple_relation :
    tricriticalState (virasoroSimple tricriticalC).L (virasoroSimple tricriticalC).vacuum=0 := by
  have hz := NormalOrdering.singular_mkQ_eq_zero tricriticalC (n:=12) (by omega)
    _ (tricriticalState_mem_grading tricriticalC)
    tricritical_universal_singular.1 tricritical_universal_singular.2
  simpa only [tricriticalState,map_sum,map_smul,virWord_mkQ,virasoroSimple_vacuum] using hz

set_option maxHeartbeats 1000000 in
/-- Substituting the actual dual central operator into the norm polynomial
leaves its nonzero derivative times central variation in the tangent coordinate. -/
theorem tricritical_weight12_central {V : Type*} [AddCommGroup V] [Module ℂ V]
    (δ : ℂ) (v : V) :
    let K : End ℂ (V × V) := tricriticalC • 1+δ • tangentShift
    (321372476328566880:ℂ) • K (v,0) +
      (-1083581144832396000:ℂ) • (K^2) (v,0) +
      (866474649917232000:ℂ) • (K^3) (v,0) +
      (36252776782320000:ℂ) • (K^4) (v,0) +
      (527065804800000:ℂ) • (K^5) (v,0) +
      (2949120000000:ℂ) • (K^6) (v,0) = (0,(128451135137139360*δ) • v) := by
  dsimp only
  apply Prod.ext <;>
    simp [tricriticalC,pow_succ,Module.End.mul_apply,LinearMap.add_apply,
      LinearMap.smul_apply,tangentShift,smul_add,smul_smul] <;> module

/-- Every actual graded deformation at the tricritical charge has zero
normalized central variation, forced by the certified singular relation
and its nonzero actual norm derivative. -/
theorem tricritical_actual_central_variation_zero
    (D : FirstOrderDeformation (virasoroSimple tricriticalC)) (hD : D.IsGraded) (α β : ℂ)
    (ha : D.smul₁ (virasoroSimple tricriticalC).conformalVector 3
      (virasoroSimple tricriticalC).conformalVector = α • (virasoroSimple tricriticalC).vacuum)
    (hb : D.smul₁ (virasoroSimple tricriticalC).conformalVector 1
      (virasoroSimple tricriticalC).conformalVector = β • (virasoroSimple tricriticalC).conformalVector) :
    2*α-β*tricriticalC=0 := by
  let W := virasoroSimple tricriticalC
  let A := normalizedData D hD (virasoroSimple_grading_one _) α β ha hb
  have hv (n : ℤ) (hn : -1≤n) : A.L n (W.vacuum,0)=0 :=
    normalizedL_vacuum D β n hn
  have hp := tricritical_weight12_polynomial A (W.vacuum,0) hv
  have hz := virWord_pairing_obstruction D β (VirQuotForm.Bsimp _)
    tricriticalWords tricriticalCoefficients tricritical_simple_relation
  change (VirQuotForm.Bsimp _).form W.vacuum
    (tricriticalAdjoint A.L (tricriticalState A.L (W.vacuum,0))).2=0 at hz
  have hK : A.central=tricriticalC • 1+(2*α-β*tricriticalC) • tangentShift := rfl
  rw [pow_one,hK,tricritical_weight12_central] at hp
  rw [hp] at hz
  change (VirQuotForm.Bsimp tricriticalC).form W.vacuum
    ((128451135137139360*(2*α-β*tricriticalC)) • W.vacuum)=0 at hz
  have hB : (VirQuotForm.Bsimp tricriticalC).form W.vacuum W.vacuum=1 :=
    VirQuotForm.Bsimp_normalized _
  simp only [map_smul,smul_eq_mul,hB,mul_one] at hz
  linear_combination hz/128451135137139360

/-- All graded first-order deformations of the simple tricritical Ising
Virasoro algebra are coordinate changes. There are no residual rigidity inputs. -/
theorem tricritical_graded_rigidity : Deform.IsRigidGraded (virasoroSimple tricriticalC) := by
  intro D hD
  obtain ⟨α,β,A,ha,hb,hL,hK⟩ := virasoroSimple_exists_normalizedData _ D hD
  exact isTrivial_of_zero_central_variation _ D hD α β ha hb
    (tricritical_actual_central_variation_zero D hD α β ha hb)

/-- The same unconditional result in the package's M(4,5) parameter notation. -/
theorem minimal_four_five_graded_rigidity :
    Deform.IsRigidGraded (virasoroSimple (minimalCentralCharge 4 5)) := by
  rw [tricritical_minimal_charge]
  exact tricritical_graded_rigidity

end VOA.VirDeformModes
