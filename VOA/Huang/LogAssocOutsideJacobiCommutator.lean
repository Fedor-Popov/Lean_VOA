import VOA.Huang.LogAssocOutsideJacobiConvolution
import VOA.Huang.LogAssocCoefficientCoproductCompatAt

/-! The actual all-logarithmic coefficient commutator, written with the
genuine transposed P(1) action. All rearrangements use proved support. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocOutsideJacobi
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocCoefficients VOA.Huang.LogAssocCoefficientCoproduct
open VOA.Huang.LogAssocCoefficientCompatibility VOA.Huang.PzTensorRho
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
  (hfg₅ : FinGen N₅.toWeakModule)
  (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅

/-- The actual fixed-outside coefficient family eventually vanishes under
negative intermediate-weight shifts, as a full bilinear functional. -/
theorem coefficient_shift_vanish (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
    (hf : SupportedAt N₄ f β) (hz : z∈N₃.weight c) (d : ℤ) :
    ∃ I : ℤ,∀ i : ℤ,I ≤ i →
      coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
        f z c β (γ+d-i-1) k=0 := by
  obtain ⟨K,M,hB⟩ := exists_coefficient_bounds hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
  obtain ⟨I,hI⟩ := exists_int_gt (γ.re+(d : ℝ)-1-(M-c.re-β.re))
  refine ⟨I,fun i hi => hB _ _ _ f hz hf _ k (Or.inr ?_)⟩
  have hi' : (I : ℝ) ≤ i := by exact_mod_cast hi
  simp only [Complex.sub_re,Complex.add_re,Complex.intCast_re,Complex.one_re]
  linarith

/-- The genuine outside commutator on literal coefficient functionals. -/
theorem coefficient_commutator_homogeneous_rho (f : M₄ →ₗ[ℂ] ℂ) (z : M₃)
    (c β γ : ℂ) (k : ℕ) (hf : SupportedAt N₄ f β) (hz : z∈N₃.weight c)
    {d : ℤ} {u : V} (hu : u∈W.grading d) (m : ℤ)
    {a b : ℂ} {x : M₁} {y : M₂} (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) :
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
      (f ∘ₗ mode (N₄.YM u) m) z c (β-d+m+1) γ k x y -
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
      f (mode (N₃.YM u) m z) (c+d-m-1) β γ k x y =
    ∑ᶠ i : ℤ,cbz m i*rhoL N₁.toWeakModule N₂.toWeakModule u i
      (coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
        f z c β (γ+d-i-1) k) x y := by
  obtain ⟨NX,hX⟩ := exists_nat_truncation N₁ u x
  obtain ⟨NY,hY⟩ := exists_nat_truncation N₂ u y
  let N := max NX NY
  have hX' (i : ℤ) (hi : (N : ℤ) ≤ i) : mode (N₁.YM u) i x=0 := by
    have he := hX i.toNat (by dsimp [N] at hi; omega)
    rw [Int.toNat_of_nonneg (show 0 ≤ i by dsimp [N] at hi; omega)] at he
    exact he
  have hY' (i : ℤ) (hi : (N : ℤ) ≤ i) : mode (N₂.YM u) i y=0 := by
    have he := hY i.toNat (by dsimp [N] at hi; omega)
    rw [Int.toNat_of_nonneg (show 0 ≤ i by dsimp [N] at hi; omega)] at he
    exact he
  have hF := coefficient_shift_vanish hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz d
  have he := rho_convolution N₁.toWeakModule N₂.toWeakModule u x y
    (fun i => coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
      f z c β (γ+d-i-1) k) m hX' hY' hF
  have hs (i : ℤ) (j : ℕ) : γ+(d : ℂ)-((i+(j : ℤ) : ℤ) : ℂ)-1=γ+d-i-1-j := by
    push_cast
    ring
  simp only [hs] at he
  rw [he,coefficient_commutator_homogeneous hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hu m f z c β γ k hx hy hX' hY']
  ring

end VOA.Huang.LogAssocOutsideJacobi
