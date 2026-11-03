import VOA.Huang.LogAssocTensorVacuumNormalization

/-! The genuine unit triangle for the actual logarithmic tensor associator.
Actual vacuum constant extraction, the proved unit inverses, and canonical
mode spanning establish the full carrier map equality. -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1200000
namespace VOA.C2Rigid.LocalInjective
open VOA.LogTensor VOA.LogTensor.Pz
universe u
variable {V M N : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (X : LogVModule W M) (Y : LogVModule W N)
  (hX : FinGen X.toWeakModule) (hY : FinGen Y.toWeakModule)

/-- The actual associator and actual left/right unit maps satisfy the
complete logarithmic triangle, with no coherence assumption. -/
theorem tensorTriangleHom_eq :
    (tensorTriangleLongHom hC2 X Y hX hY).toLinearMap=
      (tensorTriangleShortHom hC2 X Y hX hY).toLinearMap := by
  let U := (adjointModule W).toLog
  let T := rightUnitTensor hC2 X hX
  have hT : FinGen T.toWeakModule := tensorModule_finGen hC2 X U hX finGen_adjoint
  let F := tensorTriangleLongHom hC2 X Y hX hY
  let G := tensorTriangleShortHom hC2 X Y hX hY
  let ρ := tensorRightUnitHom hC2 X hX
  let ι := tensorRightUnitInvHom hC2 X hX
  let ηL := tensorIntertwiner hC2 T Y hT hY
  let ηR := tensorIntertwiner hC2 X U hX finGen_adjoint
  let η := tensorIntertwiner hC2 X Y hX hY
  have hxy (n : ℂ) (x : M) (y : N) :
      F.toLinearMap (ηL.1 n 0 (ι.toLinearMap x) y)=η.1 n 0 x y := by
    refine LogFin.induction_on X (C := fun x =>
      F.toLinearMap (ηL.1 n 0 (ι.toLinearMap x) y)=η.1 n 0 x y) x ?_ (by simp) ?_
    · intro a x hx
      refine LogFin.induction_on Y (C := fun y =>
        F.toLinearMap (ηL.1 n 0 (ι.toLinearMap x) y)=η.1 n 0 x y) y ?_ (by simp) ?_
      · intro b y hy
        apply sub_eq_zero.mp
        apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
        intro f
        rw [map_sub]
        apply sub_eq_zero.mpr
        let β := a+b-n-1
        have hn : a+b-β-1=n := by dsimp only [β]; ring
        have hnorm := tensorTriangleLong_vacuum_constant hC2 X Y hX hY hx hy β f
        change f (F.toLinearMap (ηL.1 (a+b-β-1) 0 (ηR.1 (-1) 0 x W.vacuum) y))=
          f (η.1 (a+b-β-1) 0 x y) at hnorm
        have hconst : ηR.1 (-1) 0 x W.vacuum=ι.toLinearMap x :=
          tensorRightUnit_vacuum_constant hC2 X hX x
        have harg : ηL.1 n 0 (ι.toLinearMap x) y=
            ηL.1 (a+b-β-1) 0 (ηR.1 (-1) 0 x W.vacuum) y :=
          (congrArg (fun q : ℂ => ηL.1 q 0 (ι.toLinearMap x) y) hn.symm).trans
            (congrArg (fun q => ηL.1 (a+b-β-1) 0 q y) hconst.symm)
        have hout : η.1 n 0 x y=η.1 (a+b-β-1) 0 x y :=
          congrArg (fun q : ℂ => η.1 q 0 x y) hn.symm
        exact (congrArg (f ∘ₗ F.toLinearMap) harg).trans (hnorm.trans (congrArg f hout).symm)
      · intro y z hy hz
        simp only [map_add,hy,hz]
    · intro x z hx hz
      simp only [map_add,LinearMap.add_apply,hx,hz]
  apply tensor_linearMap_ext hC2 T Y hT hY
  intro n ξ y
  have hr : ι.toLinearMap (ρ.toLinearMap ξ)=ξ := tensorRightUnit_inv_hom hC2 X hX ξ
  have hh : F.toLinearMap (ηL.1 n 0 ξ y)=η.1 n 0 (ρ.toLinearMap ξ) y :=
    (congrArg (fun q => F.toLinearMap (ηL.1 n 0 q y)) hr).symm.trans (hxy n (ρ.toLinearMap ξ) y)
  have hg := congrArg (fun Z : LogIntertwiningOperator T.toWeakModule Y.toWeakModule
      (tensorModule hC2 X Y hX hY).toWeakModule => Z.1 n 0 ξ y)
    (tensorMap_intertwiner hC2 T Y hT hY X Y hX hY ρ (weakIdentity Y.toWeakModule))
  change G.toLinearMap (ηL.1 n 0 ξ y)=η.1 n 0 (ρ.toLinearMap ξ) y at hg
  exact hh.trans hg.symm

end VOA.C2Rigid.LocalInjective
