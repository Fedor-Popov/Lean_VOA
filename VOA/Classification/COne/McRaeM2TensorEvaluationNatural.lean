/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeM2TensorEvaluation

/-! # Genuine dinaturality of logarithmic tensor evaluation -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open Classification.COne Classification.COne.McRaeM1
open VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.SelfDual
universe u
variable {V R X : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup R] [Module ℂ R] [AddCommGroup X] [Module ℂ X]
  {W : VertexOperatorAlgebra V}

/-- The actual module vertex operator commutes with every actual weak module map. -/
theorem logModuleIntertwiner_natural (N : LogVModule W R) (P : LogVModule W X)
    (f : N.toWeakModule.Hom P.toWeakModule) :
    postcompose f (logModuleIntertwiner N.toWeakModule) =
      precompose (weakIdentity (unitLog W).toWeakModule) f (logModuleIntertwiner P.toWeakModule) := by
  apply Subtype.ext
  funext n k
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro x
  change f.toLinearMap (ofOrd (weakModuleModes N.toWeakModule) n k u x) =
    ofOrd (weakModuleModes P.toWeakModule) n k u (f.toLinearMap x)
  cases k with
  | succ k => simp only [ofOrd_succ,LinearMap.zero_apply,map_zero]
  | zero =>
    simp only [ofOrd_zero]
    by_cases hn : ∃ p : ℤ, (p:ℂ)=n
    · obtain ⟨p,rfl⟩ := hn
      rw [weakModuleModes_apply_intCast,weakModuleModes_apply_intCast]
      exact f.map_act u p x
    · rw [weakModuleModes_of_not_int N.toWeakModule (not_exists.mp hn),
        weakModuleModes_of_not_int P.toWeakModule (not_exists.mp hn)]
      simp only [LinearMap.zero_apply,map_zero]

/-- The actual inverse-skew right unit operator is natural in the genuine module. -/
theorem rightUnitIntertwiner_natural (N : LogVModule W R) (P : LogVModule W X)
    (f : N.toWeakModule.Hom P.toWeakModule) :
    postcompose f (rightUnitIntertwiner N) =
      precompose f (weakIdentity (unitLog W).toWeakModule) (rightUnitIntertwiner P) := by
  apply (omegaEquiv N.toWeakModule (unitLog W).toWeakModule P.toWeakModule 0).injective
  erw [omega_postcompose (rightUnitIntertwiner N) f 0,
    omega_precompose (rightUnitIntertwiner P) f (weakIdentity (unitLog W).toWeakModule) 0]
  have hN : omegaEquiv N.toWeakModule (adjointModule W).toWeakModule N.toWeakModule 0
      (rightUnitIntertwiner N) = logModuleIntertwiner N.toWeakModule :=
    LinearEquiv.apply_symm_apply _ _
  have hP : omegaEquiv P.toWeakModule (adjointModule W).toWeakModule P.toWeakModule 0
      (rightUnitIntertwiner P) = logModuleIntertwiner P.toWeakModule :=
    LinearEquiv.apply_symm_apply _ _
  rw [hN,hP]
  exact logModuleIntertwiner_natural N P f

/-- The genuinely prepared right unit modes retain naturality of the Jordan half-turn. -/
theorem rightUnit_prepared_natural (N : LogVModule W R) (P : LogVModule W X)
    (f : N.toWeakModule.Hom P.toWeakModule) (q : ℂ) (x : R) (v : V) :
    Ar.zeroFamily P (unitLog W) P (Ar.prepared P (unitLog W) P (rightUnitIntertwiner P))
      q (f.toLinearMap x) v =
      f.toLinearMap (Ar.zeroFamily N (unitLog W) N (Ar.prepared N (unitLog W) N
        (rightUnitIntertwiner N)) q x v) := by
  change (rightUnitIntertwiner P).1 q 0 (Contra.nilExp P (Ar.phase 0) (f.toLinearMap x)) v =
    f.toLinearMap ((rightUnitIntertwiner N).1 q 0 (Contra.nilExp N (Ar.phase 0) x) v)
  rw [← Contra.hom_nilExp N P f]
  have h := congrArg (fun Y => Y.1 q 0 (Contra.nilExp N (Ar.phase 0) x) v)
    (rightUnitIntertwiner_natural N P f)
  exact h.symm

/-- The actual dual-unit evaluation is dinatural, on every logarithmic coefficient. -/
theorem dualUnitEvaluation_dinatural (N : LogVModule W R) (P : LogVModule W X)
    (f : N.toWeakModule.Hom P.toWeakModule) :
    precompose (weakIdentity N.toWeakModule) (transposeLog N P f) (dualUnitEvaluationIntertwiner N) =
      precompose f (weakIdentity (contraLog P).toWeakModule) (dualUnitEvaluationIntertwiner P) := by
  apply logZero_injective
  funext n
  apply bilinear_ext_homogeneous N (contraLog P)
  intro a b x t hx ht
  apply restrictedDual_ext_of_pairing (unitLog W).toGW
  intro c v hv
  change dualPairing (unitLog W).toGW v
      ((Ar.transform N (unitLog W) N (rightUnitIntertwiner N)).1 n 0 x ((transposeLog N P f).toLinearMap t)) =
    dualPairing (unitLog W).toGW v
      ((Ar.transform P (unitLog W) P (rightUnitIntertwiner P)).1 n 0 (f.toLinearMap x) t)
  rw [Ar.transform_logZero,Ar.transform_logZero,
    Ar.pair_modes_zero N (unitLog W) N (rightUnitIntertwiner N) n hx,
    Ar.pair_modes_zero P (unitLog W) P (rightUnitIntertwiner P) n (Contra.hom_mem_weight N P f hx),
    transposeLog_pair]
  have htw : f.toLinearMap
      (Ar.twI N.toGW (Ar.zeroFamily N (unitLog W) N (Ar.prepared N (unitLog W) N
        (rightUnitIntertwiner N))) a n x v) =
      Ar.twI P.toGW (Ar.zeroFamily P (unitLog W) P (Ar.prepared P (unitLog W) P
        (rightUnitIntertwiner P))) a n (f.toLinearMap x) v := by
    obtain ⟨J,hJ⟩ := Ar.L1w_pow_eventually N.toGW x
    have hJP : ∀ j, J ≤ j → (Ar.L1w P.toGW.toWeakModule ^ j) (f.toLinearMap x) = 0 := by
      intro j hj
      rw [← Ar.hom_L1w_pow P N f j x,hJ j hj,map_zero]
    rw [Ar.twI_apply_eq_sum N.toGW _ a n hJ v,Ar.twI_apply_eq_sum P.toGW _ a n hJP v,
      map_smul,map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_smul,← Ar.hom_L1w_pow P N f j x,rightUnit_prepared_natural N P f]
  rw [htw]

/-- Genuine evaluation into the actual tensor unit is dinatural at every log degree. -/
theorem evaluationIntertwiner_dinatural (N : LogVModule W R) (P : LogVModule W X)
    (f : N.toWeakModule.Hom P.toWeakModule) (hs : W.SelfDual) :
    precompose (weakIdentity N.toWeakModule) (transposeLog N P f) (evaluationIntertwiner N hs) =
      precompose f (weakIdentity (contraLog P).toWeakModule) (evaluationIntertwiner P hs) := by
  have hd := dualUnitEvaluation_dinatural N P f
  apply Subtype.ext
  funext n k
  ext x t
  have h := congrArg (fun Y => Y.1 n k x t) hd
  change (formEquiv (unitForm hs) hs.choose_spec.2).symm
      ((dualUnitEvaluationIntertwiner N).1 n k x ((transposeLog N P f).toLinearMap t)) =
    (formEquiv (unitForm hs) hs.choose_spec.2).symm
      ((dualUnitEvaluationIntertwiner P).1 n k (f.toLinearMap x) t)
  exact congrArg _ h

end VOA.C2Rigid.LocalInjective
