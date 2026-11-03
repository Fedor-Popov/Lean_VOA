import VOA.Huang.LogAssocDenormalizedBounds

/-! Genuine uniform bounds on the literal logarithmic product in a complete
integer spectrum coset, across all generalized homogeneous input levels. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries VOA.Huang.HuangODEAlgebra
open VOA.Huang.LogHuangODEProduct VOA.Huang.LogHuangODEIterPoint
open VOA.Huang.AssocExpansion VOA.Huang.AssocCoeffRules VOA.Huang.MatrixCoeff VOA.Huang.FrobeniusLog
open VOA.Huang.LogRemovalCoeff VOA.Huang.LogRemovalBound VOA.Huang.LogRemovalWeightBound
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- Fixed actual lower generalized-weight bases give one collision log
bound and one normalized exponent bound for every genuine product tuple.
The original log powers and every integer mode in the coset are retained. -/
theorem exists_fullCoset_collision_bounds_on_bases (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    {h₁ h₂ h₃ h₄ : ℂ} (h₅ : ℂ)
    (hl₁ : CosetBase N₁.toGW h₁) (hl₂ : CosetBase N₂.toGW h₂)
    (hl₃ : CosetBase N₃.toGW h₃) (hl₄ : CosetBase N₄.toGW h₄) :
    ∃ K : ℕ,∃ M : ℝ,∀ (n₁ n₂ n₃ n₄ : ℕ) (f : M₄ →ₗ[ℂ] ℂ)
      (x : M₁) (y : M₂) (z : M₃),
      x∈N₁.weight (h₁+n₁) → y∈N₂.weight (h₂+n₂) → z∈N₃.weight (h₃+n₃) →
      LogDegLE K (logProductFullCosetFun Y₁.1 Y₂.1 f x y z
        ((h₁+n₁)+h₅-(h₄+n₄)-1) ((h₂+n₂)+(h₃+n₃)-h₅-1)) ∧
      ExpGE (M-(n₁+n₂+n₃+n₄ : ℕ)) (logProductFullCosetFun Y₁.1 Y₂.1 f x y z
        ((h₁+n₁)+h₅-(h₄+n₄)-1) ((h₂+n₂)+(h₃+n₃)-h₅-1)) := by
  classical
  let ν₀ := h₂+h₃-h₅-1
  obtain ⟨K₀,hUB₀⟩ := exists_unifBase_family (fun l n => Y₂.1 n l)
    (fun l => logCoefficient_isGradedJacobi Y₂.2 l) h₂ h₃ ν₀ 0
  let ν := ν₀+K₀
  have hUB : ∀ l,UnifBase N₂.toGW N₃.toGW (fun n => Y₂.1 n l) h₂ h₃ ν := by
    simpa only [Nat.cast_zero,sub_zero] using hUB₀
  obtain ⟨B₁,hC₁⟩ := exists_C1Graded hC2 N₁ hfg₁ hl₁
  obtain ⟨B₂,hC₂⟩ := exists_C1Graded hC2 N₂ hfg₂ hl₂
  obtain ⟨B₃,hC₃⟩ := exists_C1Graded hC2 N₃ hfg₃ hl₃
  obtain ⟨B₄,hD₄⟩ := exists_DualC1Graded hC2 N₄ hfg₄ hl₄
  obtain ⟨K,hK⟩ := exists_uniform_collision_log_bound hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hl₁ hl₂ hl₃ hl₄ hUB hC₁ hC₂ hC₃ hD₄
  obtain ⟨M,hM⟩ := exists_uniform_collision_weight_bound hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hl₁ hl₂ hl₃ hl₄ hUB hC₁ hC₂ hC₃ hD₄
  obtain ⟨K₁,hK₁⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  refine ⟨K,M,?_⟩
  intro n₁ n₂ n₃ n₄ f x y z hx hy hz
  let s := n₁+n₂+n₃+n₄
  let c := h₁+h₂+h₃-h₄-2
  let a := (h₁+n₁)+h₅-(h₄+n₄)-1
  let b := (h₂+n₂)+(h₃+n₃)-h₅-1
  have hσ : a+b=c+s-2*n₄ := by dsimp [a,b,c,s]; push_cast; ring
  have hb : ∀ l,IsBase (fun n => Y₂.1 n l) y z (ν+s) :=
    fun l => (hUB l).base hy hz (by dsimp [s]; omega)
  have heν : b+((K₀+n₁+n₄ : ℕ) : ℂ)=ν+s := by
    dsimp [b,ν,ν₀,s]; push_cast; ring
  have he (k l : ℕ) (t : ℂ) :
      logProductIntegerCosetFun Y₁.1 Y₂.1 f x y z a b k l t=
      (Complex.log (1+Complex.exp t))^k*
        prodFun (fun n => Y₁.1 n k) (fun n => Y₂.1 n l) f x y z (c+s-2*n₄) (ν+s) t := by
    unfold logProductIntegerCosetFun
    rw [hσ]
    have hh := prodFunZ_shift (fun n => Y₁.1 n k) (fun n => Y₂.1 n l)
      f x y z (c+s-2*n₄) b ((K₀+n₁+n₄ : ℕ) : ℤ) t
    simp only [Int.cast_natCast,heν] at hh
    rw [← hh,prodFunZ_eq_prodFun f x (hb l) t]
  have hG (k l : ℕ) : QT (fun n => Y₁.1 n k) (fun n => Y₂.1 n l) c ν f x y z n₄ s∈SubexpPS := by
    apply subexp_of_summable_unitDisc
    intro t ht
    have hh := summable_log_product hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f x y z (c-ν-2*n₄) (ν+s) k l ht
    simpa only [QT,coeff_prodQ] using hh
  have hk (k : ℕ) : LogDegLE K (logProductIntegerCosetFun Y₁.1 Y₂.1 f x y z a b k 0) := by
    have hh := logDegLE_denormalize (hG k 0) (hK n₁ n₂ n₃ n₄ k 0 f x y z hx hy hz)
    exact (LogDegLE.logOneAdd_mul hh k).congr fun t _ => (he k 0 t).symm
  have hm (k : ℕ) : ExpGE (M-s) (logProductIntegerCosetFun Y₁.1 Y₂.1 f x y z a b k 0) := by
    have hh := expGE_denormalize (hG k 0) (hM n₁ n₂ n₃ n₄ k 0 f x y z hx hy hz)
    exact (ExpGE.logOneAdd_mul hh k).congr fun t _ => (he k 0 t).symm
  have hefull (t : ℂ) :
      (∑ k∈Finset.range K₁,logProductIntegerCosetFun Y₁.1 Y₂.1 f x y z a b k 0 t)=
        logProductFullCosetFun Y₁.1 Y₂.1 f x y z a b t :=
    (fullCoset_eq_sum_log Y₂.1 (fun n k hk => hK₁ Y₁ n k hk) f x y z a b t).symm
  exact ⟨(logDegLE_sum (Finset.range K₁) (fun k _ => hk k)).congr (fun t _ => hefull t),
    (expGE_sum (Finset.range K₁) (fun k _ => hm k)).congr (fun t _ => hefull t)⟩

end VOA.Huang.LogAssocExpansion
