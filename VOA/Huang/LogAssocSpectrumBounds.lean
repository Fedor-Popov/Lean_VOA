import VOA.Huang.LogAssocFullCosetBounds
import VOA.Huang.LogHuangCosetBases
import VOA.Huang.LogAssocSpectrum

/-! Global collision bounds for the literal product over its entire genuine
intermediate spectrum. Finitely many lower generalized-weight coset bases
supply the uniform constants. -/
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

/-- One actual collision log bound covers all nonzero generalized weight
blocks. The exponent bound depends only on the four stated weights. -/
theorem exists_spectrum_collision_bounds (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule) :
    ∃ K : ℕ,∃ M : ℝ,∀ (a b c β : ℂ) (f : M₄ →ₗ[ℂ] ℂ)
      (x : M₁) (y : M₂) (z : M₃),
      N₁.weight a≠⊥ → N₂.weight b≠⊥ → N₃.weight c≠⊥ → N₄.weight β≠⊥ →
      x∈N₁.weight a → y∈N₂.weight b → z∈N₃.weight c →
      LogDegLE K (logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β) ∧
      ExpGE (M-a.re-b.re-c.re-β.re)
        (logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β) := by
  classical
  obtain ⟨H₁,hL₁,hH₁⟩ := exists_finite_cosetBases hC2 N₁ hfg₁
  obtain ⟨H₂,hL₂,hH₂⟩ := exists_finite_cosetBases hC2 N₂ hfg₂
  obtain ⟨H₃,hL₃,hH₃⟩ := exists_finite_cosetBases hC2 N₃ hfg₃
  obtain ⟨H₄,hL₄,hH₄⟩ := exists_finite_cosetBases hC2 N₄ hfg₄
  let J₁ := {h // h∈H₁}
  let J₂ := {h // h∈H₂}
  let J₃ := {h // h∈H₃}
  let J₄ := {h // h∈H₄}
  let J₅ := {mu // mu∈spectrumCosets hC2 N₅ hfg₅}
  let I := J₁×J₂×J₃×J₄×J₅
  choose Kq Mq hq using fun q : I =>
    exists_fullCoset_collision_bounds_on_bases hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ (spectrumCosetRep hC2 N₅ hfg₅ q.2.2.2.2)
      (hL₁ _ q.1.2) (hL₂ _ q.2.1.2) (hL₃ _ q.2.2.1.2) (hL₄ _ q.2.2.2.1.2)
  let K := Finset.univ.sup Kq
  let E : I → ℝ := fun q => Mq q+(q.1.1+q.2.1.1+q.2.2.1.1+q.2.2.2.1.1).re
  let M := -∑ q : I,|E q|
  have hMK (q : I) : Kq q≤K := Finset.le_sup (f := Kq) (Finset.mem_univ q)
  have hME (q : I) : M≤E q := by
    have h1 := Finset.single_le_sum (f := fun q : I => |E q|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ q)
    have h2 := neg_abs_le (E q)
    dsimp only [M]
    linarith
  refine ⟨K,M,?_⟩
  intro a b c β f x y z ha hb hc hβ hx hy hz
  obtain ⟨h₁,hh₁,n₁,rfl⟩ := hH₁ a ha
  obtain ⟨h₂,hh₂,n₂,rfl⟩ := hH₂ b hb
  obtain ⟨h₃,hh₃,n₃,rfl⟩ := hH₃ c hc
  obtain ⟨h₄,hh₄,n₄,rfl⟩ := hH₄ β hβ
  have hall (mu : ℂ) (hmu : mu∈spectrumCosets hC2 N₅ hfg₅) :
      LogDegLE K (logProductFullCosetFun Y₁.1 Y₂.1 f x y z
        ((h₁+n₁)+spectrumCosetRep hC2 N₅ hfg₅ mu-(h₄+n₄)-1)
        ((h₂+n₂)+(h₃+n₃)-spectrumCosetRep hC2 N₅ hfg₅ mu-1)) ∧
      ExpGE (M-(h₁+n₁).re-(h₂+n₂).re-(h₃+n₃).re-(h₄+n₄).re)
        (logProductFullCosetFun Y₁.1 Y₂.1 f x y z
          ((h₁+n₁)+spectrumCosetRep hC2 N₅ hfg₅ mu-(h₄+n₄)-1)
          ((h₂+n₂)+(h₃+n₃)-spectrumCosetRep hC2 N₅ hfg₅ mu-1)) := by
    let q : I := (⟨h₁,hh₁⟩,⟨h₂,hh₂⟩,⟨h₃,hh₃⟩,⟨h₄,hh₄⟩,⟨mu,hmu⟩)
    obtain ⟨hk,hm⟩ := hq q n₁ n₂ n₃ n₄ f x y z hx hy hz
    refine ⟨hk.mono (hMK q),hm.mono ?_⟩
    have hh := hME q
    dsimp only [E,q] at hh
    simp only [Complex.add_re,Complex.natCast_re,Nat.cast_add] at hh ⊢
    linarith
  exact ⟨logDegLE_sum _ (fun mu hmu => (hall mu hmu).1),
    expGE_sum _ (fun mu hmu => (hall mu hmu).2)⟩

end VOA.Huang.LogAssocExpansion
