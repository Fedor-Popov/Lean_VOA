import VOA.Huang.LogAssocFivePointFamily

/-! Actual C2-cofinite generalized modules supply the finite all-log regular
module. The genuine coupled derivative gives the inner monic regular equation
for every original logarithmic coefficient of a three-operator product. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePointGraded
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries
open VOA.Huang.LogHuangODEProduct VOA.Huang.FivePointSep
open scoped BigOperators
universe u
variable {V M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
  [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
  [AddCommGroup M₆] [Module ℂ M₆]
variable (N₀ : LogVModule W M₀) (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (N₃ : LogVModule W M₃) (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅) (N₆ : LogVModule W M₆)

/-- The genuine regular inner equation, for arbitrary original log degrees,
with actual C2 and finite generation as its only structural premises. -/
theorem innerRegular_logNormalizedSeries (hC2 : C2Cofinite W)
    (hfg₀ : FinGen N₀.toWeakModule) (hfg₁ : FinGen N₁.toWeakModule)
    (hfg₂ : FinGen N₂.toWeakModule) (hfg₃ : FinGen N₃.toWeakModule)
    (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (hfg₆ : FinGen N₆.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₆.toWeakModule N₀.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₅.toWeakModule N₆.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule N₅.toWeakModule)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ}
    (hl₀ : CosetBase N₀.toGW h₀) (hl₁ : CosetBase N₁.toGW h₁)
    (hl₂ : CosetBase N₂.toGW h₂) (hl₃ : CosetBase N₃.toGW h₃) (hl₄ : CosetBase N₄.toGW h₄)
    (hB : ∀ l j, UniformTwoBase N₂.toGW N₃.toGW N₄.toGW
      (fun n => Y₂.1 n l) (fun n => Y₃.1 n j) h₂ h₃ h₄ ν μ)
    {n₀ n₁ n₂ n₃ n₄ : ℕ} (f : M₀  →ₗ[ℂ] ℂ)
    {x : M₁} {y : M₂} {z : M₃} {w : M₄}
    (hx : x  ∈  N₁.weight (h₁+n₁)) (hy : y  ∈  N₂.weight (h₂+n₂))
    (hz : z  ∈  N₃.weight (h₃+n₃)) (hw : w  ∈  N₄.weight (h₄+n₄)) (k l j : ℕ) (v : ℂ) :
    InnerRegular v (c2 (logNormalizedSeries Y₁.1 Y₂.1 Y₃.1
      (h₁+h₂+h₃+h₄-h₀-3) ν μ f x y z w n₀ (n₀+n₁+n₂+n₃+n₄) k l j)) := by
  obtain ⟨B₀,hD₀⟩ := exists_DualC1Graded hC2 N₀ hfg₀ hl₀
  obtain ⟨B₁,hC₁⟩ := exists_C1Graded hC2 N₁ hfg₁ hl₁
  obtain ⟨B₂,hC₂⟩ := exists_C1Graded hC2 N₂ hfg₂ hl₂
  obtain ⟨B₃,hC₃⟩ := exists_C1Graded hC2 N₃ hfg₃ hl₃
  obtain ⟨B₄,hC₄⟩ := exists_C1Graded hC2 N₄ hfg₄ hl₄
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₆ N₀ hfg₁ hfg₆ hfg₀
  obtain ⟨L,hL⟩ := uniform_log_degree_of_finGen N₂ N₅ N₆ hfg₂ hfg₅ hfg₆
  obtain ⟨J,hJ⟩ := uniform_log_degree_of_finGen N₃ N₄ N₅ hfg₃ hfg₄ hfg₅
  have hJ₁ (q : ℕ) := logCoefficient_isGradedJacobi Y₁.2 q
  have hJ₂ (q : ℕ) := logCoefficient_isGradedJacobi Y₂.2 q
  have hJ₃ (q : ℕ) := logCoefficient_isGradedJacobi Y₃.2 q
  obtain ⟨NN,hFG,hmem⟩ := exists_joint_fg hJ₁ hJ₂ hJ₃ hl₀ hl₁ hl₂ hl₃ hl₄ hB
    hD₀ hC₁ hC₂ hC₃ hC₄ (fun n q hq => hK Y₁ n q hq)
    (fun n q hq => hL Y₂ n q hq) (fun n q hq => hJ Y₃ n q hq)
  let c := h₁+h₂+h₃+h₄-h₀-3
  let s := n₀+n₁+n₂+n₃+n₄
  let Q : (ℕ × ℕ × ℕ)  →  ℕ  →  PS2 := fun p t =>
    logNormalizedSeries Y₁.1 Y₂.1 Y₃.1 c ν μ f x y
      ((⇑(Lm1 N₃.toWeakModule))^[t] z) w n₀ (s+t) p.1 p.2.1 p.2.2
  let next : (ℕ × ℕ × ℕ)  →  (ℕ × ℕ × ℕ) := fun p => (p.1,p.2.1,p.2.2+1)
  let d : (ℕ × ℕ × ℕ)  →  ℂ := fun p => (p.2.2 : ℂ)+1
  let lam : ℕ  →  ℂ := fun t => -(μ+((s+t : ℕ) : ℂ)+1)
  have hQmem : ∀ p t,Q p t ∈ NN := by
    intro p t
    have hm := hmem p.1 p.2.1 p.2.2 n₀ n₁ n₂ (n₃+t) n₄ f x y
      ((⇑(Lm1 N₃.toWeakModule))^[t] z) w hx hy
      (Lm1_iterate_mem_weight (A₂ := N₃.toGW) hz t) hw
    simpa only [Q,c,s,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hm
  have hQ : ∀ p t,Q p (t+1)=thetaY (lam t) (Q p t)+d p • Q (next p) t := by
    intro p t
    dsimp only [Q,lam,d,next]
    rw [Function.iterate_succ_apply',show s+(t+1)=s+t+1 by omega]
    exact logNormalizedSeries_Lm1_third Y₃ Y₁.1 Y₂.1 c ν μ f x y
      ((⇑(Lm1 N₃.toWeakModule))^[t] z) w n₀ (s+t) p.1 p.2.1 p.2.2
  have hh := innerRegular_of_coupled_fg NN hFG Q next d lam hQ hQmem (k,l,j) v
  simpa only [Q,c,s,Nat.add_zero,Function.iterate_zero,id] using hh

end VOA.Huang.LogAssocFivePointGraded
