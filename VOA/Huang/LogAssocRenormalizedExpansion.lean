import VOA.Huang.LogHuangODEIterPointAnalytic
import VOA.Huang.LogAssocExpansionHelpers
import VOA.Huang.LogHuangODEIterPointGenerators
import VOA.Huang.LogRemovalBound

/-! Every actual collision-renormalized tuple has a genuine logarithmic
Frobenius expansion with a common normalization. This exposes the finite
base tuples used for uniform generalized-module coefficient bounds. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogHuangODEIterPoint
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries VOA.Huang.HuangODEAlgebra
open VOA.Huang.FuchsianODE
open VOA.Huang.LogHuangODEProduct VOA.Huang.LogAssocExpansion
open VOA.Huang.HuangODEIterPoint VOA.Huang.AssocExpansion
open VOA.Huang.LogRemovalCoeff VOA.Huang.LogRemovalBound
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- Actual renormalized tuples have a common collision normalization, while
the derivative descent retains both logarithmic indices. -/
theorem renormalized_QT_hasLogExp (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    {h₁ h₂ h₃ h₄ ν : ℂ} {B₁ B₂ B₃ B₄ : ℕ}
    (hl₁ : CosetBase N₁.toGW h₁) (hl₂ : CosetBase N₂.toGW h₂)
    (hl₃ : CosetBase N₃.toGW h₃) (hl₄ : CosetBase N₄.toGW h₄)
    (hUB : ∀ l,UnifBase N₂.toGW N₃.toGW (fun n => Y₂.1 n l) h₂ h₃ ν)
    (hC₁ : C1Graded N₁.toGW h₁ B₁) (hC₂ : C1Graded N₂.toGW h₂ B₂)
    (hC₃ : C1Graded N₃.toGW h₃ B₃) (hD₄ : DualC1Graded N₄.toGW h₄ B₄)
    (n₁ n₂ n₃ n₄ k l : ℕ) (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃)
    (hx : x∈N₁.weight (h₁+n₁)) (hy : y∈N₂.weight (h₂+n₂)) (hz : z∈N₃.weight (h₃+n₃)) :
    HasLogExp overlapDomain (Phi (h₁+h₂+h₃-h₄-2-ν)
      ((1-X)^(n₁+n₂+n₃+n₄)*
        QT (fun n => Y₁.1 n k) (fun n => Y₂.1 n l) (h₁+h₂+h₃-h₄-2) ν f x y z n₄
          (n₁+n₂+n₃+n₄))) := by
  classical
  obtain ⟨K₁,hK₁⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  obtain ⟨K₂,hK₂⟩ := uniform_log_degree_of_finGen N₂ N₃ N₅ hfg₂ hfg₃ hfg₅
  have hJ₁ (q : ℕ) := logCoefficient_isGradedJacobi Y₁.2 q
  have hJ₂ (q : ℕ) := logCoefficient_isGradedJacobi Y₂.2 q
  obtain ⟨NN,hFG,hmem⟩ := exists_joint_collision_fg hJ₁ hJ₂ hl₁ hl₂ hl₃ hl₄ hUB hC₁ hC₂ hC₃ hD₄
    (fun n q hq => hK₁ Y₁ n q hq) (fun n q hq => hK₂ Y₂ n q hq)
  let s := n₁+n₂+n₃+n₄
  let c := h₁+h₂+h₃-h₄-2
  let Q : (ℕ×ℕ) → ℕ → PowerSeries ℂ := fun p j =>
    QT (fun n => Y₁.1 n p.1) (fun n => Y₂.1 n p.2) c ν f x
      ((⇑(Lm1 N₂.toWeakModule))^[j] y) z n₄ (s+j)
  have hQmem : ∀ p j,(1-X)^(s+j)*Q p j∈NN := by
    intro p j
    have hh := hmem p.1 p.2 n₁ (n₂+j) n₃ n₄ f x
      ((⇑(Lm1 N₂.toWeakModule))^[j] y) z hx
      (Lm1_iterate_mem_weight (A₂ := N₂.toGW) hy j) hz
    simpa only [Q,c,s,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh
  let μ : ℕ → ℂ := fun j => ν+((s+j : ℕ) : ℂ)+1
  let next : ℕ×ℕ → ℕ×ℕ := fun p => (p.1,p.2+1)
  let d : ℕ×ℕ → ℂ := fun p => (p.2 : ℂ)+1
  have hQ : ∀ p j,Q p (j+1)=thetaShift (-(μ j)) (Q p j)+d p•Q (next p) j := by
    intro p j
    dsimp only [Q,μ,d,next]
    rw [Function.iterate_succ_apply',show s+(j+1)=s+j+1 by omega]
    exact QT_LogLm1 (A₂ := N₂.toGW) (A₃ := N₃.toGW) (A₅ := N₅.toGW)
      (Y₁ := Y₁.1) (Y₂ := Y₂.1) Y₂.2 c ν f x
      ((⇑(Lm1 N₂.toWeakModule))^[j] y) z p.1 p.2 n₄ (s+j)
  have hθ : ∀ p j,VOA.theta (Q p j)=Q p (j+1)+PowerSeries.C (μ j)*Q p j-d p•Q (next p) j := by
    intro p j
    rw [hQ]
    ext n
    simp only [theta_coeff,map_add,map_sub,coeff_thetaShift,coeff_C_mul,coeff_smul,smul_eq_mul]
    ring
  let H := (1-X)^s*Q (k,l) 0
  have hG : Q (k,l) 0∈SubexpPS := by
    apply subexp_of_summable_unitDisc
    intro t ht
    have hh := summable_log_product hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f x y z (c-ν-2*n₄) (ν+s) k l ht
    refine hh.congr fun n => ?_
    simp only [Q,Function.iterate_zero,id,Nat.add_zero,QT,coeff_prodQ]
  have hH : H∈SubexpPS := SubexpPS.mul_mem (SubexpPS.pow_mem one_sub_X_mem_subexp s) hG
  have hE := hasLogExp_collision hH (c-ν+1) 0
    (exists_dop_relation_coupled NN hFG (c-ν+1) 0 s Q next d μ hθ hQmem (k,l))
  refine VOA.Huang.AssocCoeffRules.hasLogExp_congr (fun t _ => ?_) hE
  dsimp only [Ev,Phi,H,Q,c,s,Function.iterate_zero,id,Nat.add_zero]
  simp only [zero_mul,neg_zero,Complex.exp_zero,one_mul]
  have he : -(h₁+h₂+h₃-h₄-2-ν+1)=-(h₁+h₂+h₃-h₄-2-ν)-1 := by ring
  rw [he]

end VOA.Huang.LogHuangODEIterPoint
