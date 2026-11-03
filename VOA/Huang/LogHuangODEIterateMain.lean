import VOA.Huang.LogHuangODEIterateFinite

/-! Absolute convergence of actual logarithmic iterate coefficients.
All five modules are genuine finitely generated grading-restricted generalized
modules. C2-cofiniteness supplies C1 reduction; the coupled logarithmic
derivative supplies the regular Euler equation. No ordinary-module or
L0-semisimplicity premise appears. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogHuangODEIterate
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries VOA.Huang.FuchsianODE VOA.Huang.Convergence
open VOA.Huang.HuangODEAlgebra VOA.Huang.LogHuangODEProduct
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- Every actual logarithmic coefficient on every mode coset converges absolutely. -/
theorem summable_log_iterate_homogeneous (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    {α₁ α₂ α₃ : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x ∈ N₁.weight α₁) (hy : y ∈ N₂.weight α₂) (hz : z ∈ N₃.weight α₃)
    (f : M₄ →ₗ[ℂ] ℂ) (a b : ℂ) (k l : ℕ) {t : ℂ} (ht : ‖t‖ < 1) :
    Summable fun n : ℕ => ‖f (Y₃.1 (a+n) k (Y₄.1 (b-n) l x y) z) * t^n‖ := by
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
  obtain ⟨K₁,hK₁⟩ := uniform_log_degree_of_finGen N₅ N₃ N₄ hfg₅ hfg₃ hfg₄
  obtain ⟨K₂,hK₂⟩ := uniform_log_degree_of_finGen N₁ N₂ N₅ hfg₁ hfg₂ hfg₅
  have hJ₃ (q : ℕ) := logCoefficient_isGradedJacobi Y₃.2 q
  have hJ₄ (q : ℕ) := logCoefficient_isGradedJacobi Y₄.2 q
  let s := N₁'+N₂'+N₃'+N₄'
  obtain ⟨K,hUB⟩ := exists_unifBase_family (A₂ := N₁.toGW) (A₃ := N₂.toGW) (A₅ := N₅.toGW)
    (fun q n => Y₄.1 n q) hJ₄ h₁ h₂ b s
  let ν := b-(s : ℂ)+K
  let c := h₁+h₂+h₃-h₄-2
  obtain ⟨NN,hFG,hmem⟩ := exists_joint_fg (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) (h₄ := h₄)
    (ν := ν) hJ₃ hJ₄ hl₁ hl₂ hl₃ hl₄ hUB hC₁ hC₂ hC₃ hD₄
    (fun n q hq => hK₁ Y₃ n q hq) (fun n q hq => hK₂ Y₄ n q hq)
  let Q : (ℕ × ℕ) → ℕ → PowerSeries ℂ := fun p j =>
    QI (fun n => Y₃.1 n p.1) (fun n => Y₄.1 n p.2) c ν f ((⇑(Lm1 N₁.toWeakModule))^[j] x) y z N₄' (s+j)
  have hQmem : ∀ p j, Q p j ∈ NN := by
    intro p j
    have hh := hmem p.1 p.2 (N₁'+j) N₂' N₃' N₄' f
      ((⇑(Lm1 N₁.toWeakModule))^[j] x) y z
      (Lm1_iterate_mem_weight (A₂ := N₁.toGW) hx' j) hy' hz'
    simpa only [Q,c,s,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh
  let lam : ℕ → ℂ := fun j => -(ν+((s+j : ℕ) : ℂ)+1)
  let next : ℕ × ℕ → ℕ × ℕ := fun p => (p.1,p.2+1)
  let d : ℕ × ℕ → ℂ := fun p => (p.2 : ℂ)+1
  have hQ : ∀ p j, Q p (j+1)=thetaShift (lam j) (Q p j)+d p • Q (next p) j := by
    intro p j
    dsimp only [Q,lam,d,next]
    rw [Function.iterate_succ_apply',show s+(j+1)=s+j+1 by omega]
    exact QI_LogLm1 (A₁ := N₁.toGW) (A₂ := N₂.toGW) (A₅ := N₅.toGW)
      (Y₃ := Y₃.1) (Y₄ := Y₄.1) Y₄.2 c ν f ((⇑(Lm1 N₁.toWeakModule))^[j] x) y z p.1 p.2 N₄' (s+j)
  have hRat := ratFuchsian_of_coupled_fg NN hFG Q next d lam hQ hQmem (k,l) 0
  have hcoeff (n : ℕ) : coeff (n+K) (Q (k,l) 0) =
      f (Y₃.1 (a+n) k (Y₄.1 (b-n) l x y) z) := by
    simp only [Q,Function.iterate_zero,id,Nat.add_zero,QI,coeff_iterQ]
    have hc : c=a+b-(N₁' : ℂ)-N₂'-N₃'+N₄' := by
      dsimp only [c,α₄] at *
      linear_combination he₄-he₁-he₂-he₃
    have ha : c-ν-2*N₄'+((n+K : ℕ) : ℂ)=a+n := by
      rw [hc]
      dsimp [ν,s]
      push_cast
      ring
    have hb : ν+((s : ℕ) : ℂ)-((n+K : ℕ) : ℂ)=b-n := by
      dsimp [ν]
      push_cast
      ring
    rw [ha,hb]
  have hs := summable_shifted_coeff_of_ratFuchsian (by norm_num) hRat K ht
  exact hs.congr fun n => by rw [hcoeff]

/-- Finite generalized-weight decompositions extend convergence to all actual vectors. -/
theorem summable_log_iterate (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b : ℂ) (k l : ℕ)
    {t : ℂ} (ht : ‖t‖ < 1) :
    Summable fun n : ℕ => ‖f (Y₃.1 (a+n) k (Y₄.1 (b-n) l x y) z) * t^n‖ := by
  classical
  obtain ⟨F₁,_,hs₁⟩ := C2Rigid.exists_sum_cmp N₁.toGW x
  obtain ⟨F₂,_,hs₂⟩ := C2Rigid.exists_sum_cmp N₂.toGW y
  obtain ⟨F₃,_,hs₃⟩ := C2Rigid.exists_sum_cmp N₃.toGW z
  let g : ℂ → ℂ → ℂ → ℕ → ℂ := fun α β γ n =>
    f (Y₃.1 (a+n) k (Y₄.1 (b-n) l (C2Rigid.cmp N₁.toGW α x)
      (C2Rigid.cmp N₂.toGW β y)) (C2Rigid.cmp N₃.toGW γ z))
  have hgs (α β γ : ℂ) : Summable fun n => ‖g α β γ n * t^n‖ :=
    summable_log_iterate_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₃ Y₄ (C2Rigid.cmp_mem N₁.toGW α x) (C2Rigid.cmp_mem N₂.toGW β y)
      (C2Rigid.cmp_mem N₃.toGW γ z) f a b k l ht
  have hsum : Summable fun n => ∑ α ∈ F₁, ∑ β ∈ F₂, ∑ γ ∈ F₃, ‖g α β γ n * t^n‖ :=
    summable_sum fun α _ => summable_sum fun β _ => summable_sum fun γ _ => hgs α β γ
  have he (n : ℕ) : f (Y₃.1 (a+n) k (Y₄.1 (b-n) l x y) z) =
      ∑ α ∈ F₁, ∑ β ∈ F₂, ∑ γ ∈ F₃, g α β γ n := by
    conv_lhs => rw [← hs₁,← hs₂,← hs₃]
    simp only [map_sum,LinearMap.sum_apply,g]
    rw [Finset.sum_comm (s := F₃) (t := F₂)]
    simp_rw [Finset.sum_comm (s := F₃) (t := F₁)]
    rw [Finset.sum_comm (s := F₂) (t := F₁)]
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hsum
  intro n
  rw [he]
  simp_rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  exact norm_sum_le _ _

/-- The actual scalar logarithmic iterate series converges on the open unit disc. -/
theorem summable_log_iterate_series (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b : ℂ) (k l : ℕ)
    {t : ℂ} (ht : ‖t‖ < 1) :
    Summable fun n : ℕ => f (Y₃.1 (a+n) k (Y₄.1 (b-n) l x y) z) * t^n :=
  (summable_log_iterate hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₃ Y₄ f x y z a b k l ht).of_norm

end VOA.Huang.LogHuangODEIterate
