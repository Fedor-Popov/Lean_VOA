/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2BoundarySymbolNonzero
import VOA.Commutative.BoundaryAuxiliaryInitial
import VOA.Filtered.AffineInfiniteClassicalFreeness
import VOA.Filtered.LiC2Bridge

/-! # The actual boundary relation map into the simple Li algebra -/
set_option maxHeartbeats 800000

namespace VOA.BoundaryArcLiMap
open VertexOperatorAlgebra MvPolynomial
open scoped BigOperators
noncomputable section

section Lift
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (W : VertexOperatorAlgebra V) (gen : Fin 3 → V)
    (hgen : ∀ i, gen i ∈ W.grading (1 : ℤ))

private def c2Eval : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] A₂ W :=
  MvPolynomial.aeval (fun i => mk₂ W (gen i))
private def liEval : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] liAssociatedGraded W :=
  MvPolynomial.aeval (fun i => liDegreeZeroClass W 1 ⟨gen i, hgen i⟩)

/-- A homogeneous state simultaneously represents the C2 and Li evaluations. -/
private def HasLift (p : MvPolynomial (Fin 3) ℂ) (N : ℕ) : Prop :=
  ∃ x : W.grading (N : ℤ), c2Eval W gen p = mk₂ W x.1 ∧
    liEval W gen hgen p = liDegreeZeroClass W N x

private theorem lift_X (i : Fin 3) : HasLift W gen hgen (X i) 1 :=
  ⟨⟨gen i, hgen i⟩, by simp [c2Eval], by simp [liEval]⟩

private theorem lift_one : HasLift W gen hgen 1 0 := by
  refine ⟨⟨W.vacuum, W.vacuum_mem_grading_zero⟩, ?_, ?_⟩
  · simp [c2Eval]; rfl
  · rw [map_one, liDegreeZeroClass_eq_liHomogeneousClass]
    exact (liHomogeneousClass_vacuum W).symm

private theorem lift_add {p q : MvPolynomial (Fin 3) ℂ} {N : ℕ}
    (hp : HasLift W gen hgen p N) (hq : HasLift W gen hgen q N) :
    HasLift W gen hgen (p+q) N := by
  obtain ⟨x,hxc,hxl⟩ := hp
  obtain ⟨y,hyc,hyl⟩ := hq
  refine ⟨x+y, by simp [hxc,hyc], ?_⟩
  rw [map_add,hxl,hyl]
  simp only [liDegreeZeroClass, ← map_add]
  rfl

private theorem lift_smul {p : MvPolynomial (Fin 3) ℂ} {N : ℕ}
    (hp : HasLift W gen hgen p N) (c : ℂ) : HasLift W gen hgen (c • p) N := by
  obtain ⟨x,hxc,hxl⟩ := hp
  refine ⟨c • x, by simp [hxc], ?_⟩
  rw [map_smul,hxl]
  simp only [liDegreeZeroClass_eq_liHomogeneousClass]
  exact (liHomogeneousClass_smul W 0 N c _).symm

private theorem lift_mul {p q : MvPolynomial (Fin 3) ℂ} {N M : ℕ}
    (hp : HasLift W gen hgen p N) (hq : HasLift W gen hgen q M) :
    HasLift W gen hgen (p*q) (N+M) := by
  obtain ⟨x,hxc,hxl⟩ := hp
  obtain ⟨y,hyc,hyl⟩ := hq
  have hg : W.smul x.1 (-1) y.1 ∈ W.grading ((N+M : ℕ) : ℤ) := by
    simpa using W.smul_mem_grading x.2 y.2 (-1)
  refine ⟨⟨W.smul x.1 (-1) y.1,hg⟩, ?_, ?_⟩
  · rw [map_mul,hxc,hyc,A₂_mul_mk]
    rfl
  · rw [map_mul,hxl,hyl,liDegreeZeroClass_eq_liHomogeneousClass,
      liDegreeZeroClass_eq_liHomogeneousClass,liHomogeneousClass_mul]
    rfl

private theorem lift_pow {p : MvPolynomial (Fin 3) ℂ} {N : ℕ}
    (hp : HasLift W gen hgen p N) (r : ℕ) : HasLift W gen hgen (p^r) (r*N) := by
  induction r with
  | zero => simpa using lift_one W gen hgen
  | succ r ih => simpa [pow_succ,Nat.succ_mul] using lift_mul W gen hgen ih hp

private theorem lift_casimir : HasLift W gen hgen (BoundaryAuxiliary.casimir (R := ℂ)) 2 := by
  have hh := lift_pow W gen hgen (lift_X W gen hgen 1) 2
  have hef := lift_smul W gen hgen (lift_mul W gen hgen (lift_X W gen hgen 0)
    (lift_X W gen hgen 2)) 4
  convert lift_add W gen hgen hh hef using 1 <;>
    norm_num [BoundaryAuxiliary.casimir,smul_eq_C_mul,mul_assoc, map_ofNat]

/-- The actual boundary base relations lift simultaneously to C2 and Li. -/
theorem baseRelation_li_eq_zero_of_c2_eq_zero (m : ℕ) (i : Fin 3)
    (h : c2Eval W gen (BoundaryAuxiliary.baseRelation m i) = 0) :
    liEval W gen hgen (BoundaryAuxiliary.baseRelation m i) = 0 := by
  have hl := lift_mul W gen hgen (lift_X W gen hgen i)
    (lift_pow W gen hgen (lift_casimir W gen hgen) m)
  obtain ⟨x,hxc,hxl⟩ := hl
  change c2Eval W gen (BoundaryAuxiliary.baseRelation m i) = mk₂ W x.1 at hxc
  change liEval W gen hgen (BoundaryAuxiliary.baseRelation m i) = _ at hxl
  rw [hxl]
  exact liDegreeZeroClass_eq_zero_of_mem_O₂ W _ x
    ((mk₂_eq_zero_iff _).mp (hxc.symm.trans h))
private theorem sourceKernel_of_base (m : ℕ)
    (hbase : BoundaryAuxiliary.baseIdeal (R := ℂ) m ≤
      RingHom.ker (liEval W gen hgen).toRingHom) :
    BoundaryAuxiliary.sourceIdeal (R := ℂ) m ≤
      RingHom.ker (liInfiniteJetPolynomialMap W gen (fun _ => 1) hgen).toRingHom := by
  rw [BoundaryAuxiliary.sourceIdeal_eq_jetIdeal]
  intro f hf
  change liInfiniteJetPolynomialMap W gen (fun _ => 1) hgen f = 0
  rw [← liInfinitePresentedJetMap_mk_liGenerators W gen (fun _ => 1) hgen
    (BoundaryAuxiliary.baseIdeal (R := ℂ) m) hbase]
  have hz : InfiniteJet.presentedJetMk (R := ℂ)
      (BoundaryAuxiliary.baseIdeal (R := ℂ) m) f = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hf
  rw [hz,map_zero]
end Lift

open AffineVOA AffineVOA.Inst AffineVOA.CurrentLi
open AffineSl2BoundarySingularFamily AffineSl2BoundaryC2 AffineSl2UniversalC2PBW
open QuasiLisseSl2 Sl2Pres Sl2Symbol
variable {k : ℂ} {m : ℕ} (C : Candidate k m)

/-- The actual simple quotient at the candidate's level. -/
abbrev simpleVOA := QuotVOA.maxQuotientVOA (affineSl2VOA_closed k C.noncritical)

/-- Paper-order current states `(e,h,f)` in the actual simple quotient. -/
def gen (i : Fin 3) : WakModule k ⧸ QuotVOA.maxGradedIdeal (affineSl2VOA_closed k C.noncritical) :=
  (QuotVOA.maxGradedIdeal (affineSl2VOA_closed k C.noncritical)).mkQ
    (currentState k (symbolToCurrentColor i))

theorem gen_mem (i : Fin 3) : gen C i ∈ (simpleVOA C).grading (1 : ℤ) :=
  QuotVOA.quotientVOA_mkQ_grading (QuotVOA.maxGradedIdeal_isIdeal _)
    (QuotVOA.maxGradedIdeal_isGradedIdeal _) (currentState_mem_grading k C.noncritical _)

theorem c2Eval_eq_simpleSymbol : c2Eval (simpleVOA C) (gen C) = simpleSymbol C := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [c2Eval,MvPolynomial.aeval_X]
  change mk₂ (simpleVOA C) (gen C i) =
    QuotVOA.A₂quot (QuotVOA.maxGradedIdeal_isIdeal _)
      (QuotVOA.maxGradedIdeal_isGradedIdeal _)
      (symbolAlg k C.noncritical (X i))
  fin_cases i <;> simp [symbolAlg,gen,symbolToCurrentColor,eCl,hCl,fCl,
    colE,colH,colF,Equiv.swap_apply_def] <;> rfl

/-- The paper's literal ideal agrees with the three boundary relations. -/
theorem baseIdeal_le_boundaryIdeal : BoundaryAuxiliary.baseIdeal (R := ℂ) m ≤ boundaryIdeal m := by
  rw [BoundaryAuxiliary.baseIdeal, Ideal.span_le]
  rintro p ⟨i,rfl⟩
  fin_cases i
  · simpa [BoundaryAuxiliary.baseRelation,BoundaryAuxiliary.casimir,
      casSym,eSym,hSym,fSym,mul_comm] using cas_pow_mul_e_mem m
  · simpa [BoundaryAuxiliary.baseRelation,BoundaryAuxiliary.casimir,
      casSym,eSym,hSym,fSym,mul_comm] using cas_pow_mul_h_mem m
  · simpa [BoundaryAuxiliary.baseRelation,BoundaryAuxiliary.casimir,
      casSym,eSym,hSym,fSym,mul_comm] using cas_pow_mul_f_mem m

/-- The actual base relations vanish on paper-order simple Li current classes. -/
theorem baseIdeal_le_kernel : BoundaryAuxiliary.baseIdeal (R := ℂ) m ≤
    RingHom.ker (MvPolynomial.aeval (fun i =>
      liDegreeZeroClass (simpleVOA C) 1 ⟨gen C i,gen_mem C i⟩)).toRingHom := by
  rw [BoundaryAuxiliary.baseIdeal, Ideal.span_le]
  rintro p ⟨i,rfl⟩
  apply baseRelation_li_eq_zero_of_c2_eq_zero (simpleVOA C) (gen C) (gen_mem C)
  rw [c2Eval_eq_simpleSymbol]
  apply C.boundaryIdeal_le_kernel
  apply baseIdeal_le_boundaryIdeal
  exact Ideal.subset_span ⟨i,rfl⟩

/-- The canonical infinite jet polynomial map in the paper's `(e,h,f)` order. -/
def polynomialMap : BoundaryAuxiliary.JetPoly ℂ →ₐ[ℂ] liAssociatedGraded (simpleVOA C) :=
  liInfiniteJetPolynomialMap (simpleVOA C) (gen C) (fun _ => 1) (gen_mem C)

/-- Every coefficient of every boundary relation vanishes under the actual
infinite Li evaluation. -/
theorem sourceIdeal_le_kernel : BoundaryAuxiliary.sourceIdeal (R := ℂ) m ≤
    RingHom.ker (polynomialMap C).toRingHom := by
  exact sourceKernel_of_base (simpleVOA C) (gen C) (gen_mem C) m (baseIdeal_le_kernel C)

/-- The paper-order canonical polynomial map is onto the actual simple Li
algebra, by the intrinsic affine current-word spanning theorem. -/
theorem polynomialMap_surjective : Function.Surjective (polynomialMap C) := by
  let old : Fin 3 → liAssociatedGraded (simpleVOA C) :=
    maxQuotientAffineCurrentLiClass k C.noncritical
  let reindex : BoundaryAuxiliary.JetPoly ℂ →ₐ[ℂ] BoundaryAuxiliary.JetPoly ℂ :=
    MvPolynomial.rename (fun v : Fin 3 × ℕ => (symbolToCurrentColor.symm v.1,v.2))
  have hcomp : (polynomialMap C).comp reindex =
      InfiniteJet.derivationJetEval (liAssociatedGradedTranslation (simpleVOA C)) old := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply,reindex,MvPolynomial.rename_X,polynomialMap,
      liInfiniteJetPolynomialMap,InfiniteJet.derivationJetEval,MvPolynomial.aeval_X]
    congr 1
    simp only [old,maxQuotientAffineCurrentLiClass,quotientAffineCurrentLiClass,gen,
      Equiv.apply_symm_apply]
    rfl
  intro z
  obtain ⟨y,hy⟩ := maxQuotientAffine_liInfinitePresentedJetMap_surjective
    k C.noncritical ⊥ bot_le z
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨reindex f, ?_⟩
  change ((polynomialMap C).comp reindex) f = z
  rw [hcomp]
  exact hy

end
end VOA.BoundaryArcLiMap
