import VOA.Huang.LogHuangODEIterPointFinite
import VOA.Huang.LogHuangODEIterPointAlgebra

/-! Absolute convergence of actual logarithmic product coefficients.
All five modules are genuine finitely generated grading-restricted generalized
modules. C2-cofiniteness supplies C1 reduction; the coupled logarithmic
derivative supplies the regular Euler equation. No ordinary-module or
L0-semisimplicity premise appears. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogHuangODEIterPoint
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries VOA.Huang.FuchsianODE VOA.Huang.Convergence
open VOA.Huang.HuangODEAlgebra VOA.Huang.LogHuangODEProduct VOA.Huang.MatrixCoeff
open VOA.Huang.HuangODEIterPoint (DOp)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- A shifted actual logarithmic product coset, including the finite prefix
needed by a common lower bound for the generalized intermediate module. -/
noncomputable def logProductShiftSeries
    (Y₁ : LogModes M₁ M₅ M₄) (Y₂ : LogModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃)
    (a b : ℂ) (k l K : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => f (Y₁ (a+(n : ℂ)-K) k x (Y₂ (b-(n : ℂ)+K) l y z))

/-- Every actual logarithmic product coset has a polynomial monic equation
at the collision point, with both logarithmic indices kept in the descent. -/
theorem exists_collision_equation_log_product (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    {α₁ α₂ α₃ : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x ∈ N₁.weight α₁) (hy : y ∈ N₂.weight α₂) (hz : z ∈ N₃.weight α₃)
    (f : M₄ →ₗ[ℂ] ℂ) (a b : ℂ)  :
    ∃ s K : ℕ, (∀ l, IsBase (fun n => Y₂.1 n l) y z (b+K)) ∧
      ∀ (k l : ℕ) (κ σ : ℂ),
      ∃ (m : ℕ) (r : ℕ → PowerSeries ℂ), (∀ q,r q∈ratRing 0) ∧
      (DOp κ σ)^[m] ((1-X)^s * logProductShiftSeries Y₁.1 Y₂.1 f x y z a b k l K) =
        ∑ q ∈ Finset.range m,r q * (DOp κ σ)^[q]
          ((1-X)^s * logProductShiftSeries Y₁.1 Y₂.1 f x y z a b k l K) := by
  classical
  let α₄ := α₁+α₂+α₃-a-b-2
  obtain ⟨h₁,N₁',he₁,hl₁⟩ := exists_cosetBase N₁.toGW α₁
  obtain ⟨h₂,N₂',he₂,hl₂⟩ := exists_cosetBase N₂.toGW α₂
  obtain ⟨h₃,N₃',he₃,hl₃⟩ := exists_cosetBase N₃.toGW α₃
  obtain ⟨h₄,N₄',he₄,hl₄⟩ := exists_cosetBase N₄.toGW α₄
  have hx' : x ∈ N₁.weight (h₁+N₁') := he₁ ▸ hx
  have hy' : y ∈ N₂.weight (h₂+N₂') := he₂ ▸ hy
  have hz' : z ∈ N₃.weight (h₃+N₃') := he₃ ▸ hz
  obtain ⟨B₁,hC₁⟩ := exists_C1Graded hC2 N₁ hfg₁ hl₁
  obtain ⟨B₂,hC₂⟩ := exists_C1Graded hC2 N₂ hfg₂ hl₂
  obtain ⟨B₃,hC₃⟩ := exists_C1Graded hC2 N₃ hfg₃ hl₃
  obtain ⟨B₄,hD₄⟩ := exists_DualC1Graded hC2 N₄ hfg₄ hl₄
  obtain ⟨K₁,hK₁⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  obtain ⟨K₂,hK₂⟩ := uniform_log_degree_of_finGen N₂ N₃ N₅ hfg₂ hfg₃ hfg₅
  have hJ₁ (q : ℕ) := logCoefficient_isGradedJacobi Y₁.2 q
  have hJ₂ (q : ℕ) := logCoefficient_isGradedJacobi Y₂.2 q
  let s := N₁'+N₂'+N₃'+N₄'
  obtain ⟨K,hUB⟩ := exists_unifBase_family (A₂ := N₂.toGW) (A₃ := N₃.toGW) (A₅ := N₅.toGW)
    (fun q n => Y₂.1 n q) hJ₂ h₂ h₃ b s
  let ν := b-(s : ℂ)+K
  let c := h₁+h₂+h₃-h₄-2
  obtain ⟨NN,hFG,hmem⟩ := exists_joint_collision_fg (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) (h₄ := h₄)
    (ν := ν) hJ₁ hJ₂ hl₁ hl₂ hl₃ hl₄ hUB hC₁ hC₂ hC₃ hD₄
    (fun n q hq => hK₁ Y₁ n q hq) (fun n q hq => hK₂ Y₂ n q hq)
  let Q : (ℕ × ℕ) → ℕ → PowerSeries ℂ := fun p j =>
    QT (fun n => Y₁.1 n p.1) (fun n => Y₂.1 n p.2) c ν f x
      ((⇑(Lm1 N₂.toWeakModule))^[j] y) z N₄' (s+j)
  have hQmem : ∀ p j, (1-X)^(s+j)*Q p j ∈ NN := by
    intro p j
    have hh := hmem p.1 p.2 N₁' (N₂'+j) N₃' N₄' f x
      ((⇑(Lm1 N₂.toWeakModule))^[j] y) z hx'
      (Lm1_iterate_mem_weight (A₂ := N₂.toGW) hy' j) hz'
    simpa only [Q,c,s,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh
  let lam : ℕ → ℂ := fun j => -(ν+((s+j : ℕ) : ℂ)+1)
  let next : ℕ × ℕ → ℕ × ℕ := fun p => (p.1,p.2+1)
  let d : ℕ × ℕ → ℂ := fun p => (p.2 : ℂ)+1
  have hQ : ∀ p j, Q p (j+1)=thetaShift (lam j) (Q p j)+d p • Q (next p) j := by
    intro p j
    dsimp only [Q,lam,d,next]
    rw [Function.iterate_succ_apply',show s+(j+1)=s+j+1 by omega]
    exact QT_LogLm1 (A₂ := N₂.toGW) (A₃ := N₃.toGW) (A₅ := N₅.toGW)
      (Y₁ := Y₁.1) (Y₂ := Y₂.1) Y₂.2 c ν f x
      ((⇑(Lm1 N₂.toWeakModule))^[j] y) z p.1 p.2 N₄' (s+j)
  let μ : ℕ → ℂ := fun j => ν+((s+j : ℕ) : ℂ)+1
  have hθ : ∀ p j, VOA.theta (Q p j) =
      Q p (j+1)+PowerSeries.C (μ j)*Q p j-d p•Q (next p) j := by
    intro p j
    rw [hQ]
    ext n
    simp only [theta_coeff,map_add,map_sub,coeff_thetaShift,coeff_C_mul,coeff_smul]
    dsimp only [lam,μ]
    simp only [smul_eq_mul]
    ring
  have hQ0 (k l : ℕ) : Q (k,l) 0 =
      logProductShiftSeries Y₁.1 Y₂.1 f x y z a b k l K := by
    ext n
    simp only [Q,Function.iterate_zero,id,Nat.add_zero,QT,coeff_prodQ,
      logProductShiftSeries,PowerSeries.coeff_mk]
    have hc : c=a+b-(N₁' : ℂ)-N₂'-N₃'+N₄' := by
      dsimp only [c,α₄] at *
      linear_combination he₄-he₁-he₂-he₃
    have ha : c-ν-2*N₄'+(n : ℂ)=a+n-K := by
      rw [hc]
      dsimp [ν,s]
      push_cast
      ring
    have hb : ν+((s : ℕ) : ℂ)-(n : ℂ)=b-n+K := by
      dsimp [ν]
      push_cast
      ring
    rw [ha,hb]
  refine ⟨s,K,?_,?_⟩
  · intro l
    have hh := (hUB l).base hy' hz' (s := s) (by dsimp [s]; omega)
    have he : ν+(s : ℂ)=b+K := by dsimp [ν]; ring
    change IsBase (fun n => Y₂.1 n l) y z (ν+(s : ℂ)) at hh
    rw [he] at hh
    exact hh
  intro k l κ σ
  have hh := exists_dop_relation_coupled NN hFG κ σ s Q next d μ hθ hQmem (k,l)
  simpa only [hQ0] using hh

end VOA.Huang.LogHuangODEIterPoint
