import VOA.Huang.LogHuangODEIterateReduction

/-! The genuine coupled logarithmic derivative on normalized iterate coefficients.
The inner log-degree l+1 term is retained exactly. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogHuangODEIterate
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries VOA.Huang.FuchsianODE
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
  {A₁ : GWModule W M₁} {A₂ : GWModule W M₂} {A₅ : GWModule W M₅}

theorem QI_LogLm1 {Y₃ : LogModes M₅ M₃ M₄} {Y₄ : LogModes M₁ M₂ M₅}
    (hY₄ : IsLogIntertwining A₁.toWeakModule A₂.toWeakModule A₅.toWeakModule Y₄)
    (c ν : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃)
    (k l N₄ s : ℕ) :
    QI (fun n => Y₃ n k) (fun n => Y₄ n l) c ν f (Lm1 A₁.toWeakModule x) y z N₄ (s+1)
      = thetaShift (-(ν+s+1)) (QI (fun n => Y₃ n k) (fun n => Y₄ n l) c ν f x y z N₄ s)
        + ((l : ℂ)+1) • QI (fun n => Y₃ n k) (fun n => Y₄ n (l+1)) c ν f x y z N₄ s := by
  ext n
  rw [map_add,map_smul,coeff_thetaShift,QI,QI,QI,coeff_iterQ,coeff_iterQ,coeff_iterQ,
    hY₄.L_neg_one]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,smul_eq_mul]
  have he : ν+((s+1 : ℕ) : ℂ)-n-1=ν+s-n := by push_cast; ring
  rw [he]
  push_cast
  ring

end VOA.Huang.LogHuangODEIterate
