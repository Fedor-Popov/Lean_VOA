import VOA.Huang.LogAssocTensorOuterPairing
import VOA.Huang.LogAssocOutsideJacobiBorcherds

/-! The true outside Borcherds identity lifts from scalar matrix coefficients
to the actual coefficient span. Every sum has proved finite support. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocTensorOuterModes
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocCoefficients VOA.Huang.LogAssocCoefficientCompatibility
open VOA.Huang.LogAssocCoefficientCoproduct VOA.Huang.LogAssocOutsideJacobi
open VOA.Huang.PzTensorRho VOA.Huang.PzTensorOutside
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


noncomputable def outsideCoeffX (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
    (hf : SupportedAt N₄ f β) (hz : z∈N₃.weight c)
    {d : ℤ} {u : V} (hu : u∈W.grading d) (q : ℤ) :
    coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ :=
  ⟨coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
    (f ∘ₗ mode (N₄.YM u) q) z c (β-d+q+1) γ k,
    coefficient_mem_span hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ _ _ _ _ _ _ (supportedAt_comp_mode hf hu q) hz⟩

noncomputable def outsideCoeffY (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
    (hf : SupportedAt N₄ f β) (hz : z∈N₃.weight c)
    {d : ℤ} {u : V} (hu : u∈W.grading d) (q : ℤ) :
    coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ :=
  ⟨coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
    f (mode (N₃.YM u) q z) (c+d-q-1) β γ k,
    coefficient_mem_span hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ _ _ _ _ _ _ hf (N₃.mode_mem_weight hu hz q)⟩

noncomputable def outsideCoeffZ (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
    (hf : SupportedAt N₄ f β) (hz : z∈N₃.weight c)
    {d : ℤ} {u : V} (hu : u∈W.grading d) (q : ℤ) :
    coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ :=
  ⟨rhoL N₁.toWeakModule N₂.toWeakModule u q
    (coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β (γ+d-q-1) k),
    coefficientSpan_rho_stable hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hu q
      (coefficient_mem_span hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
        Y₁ Y₂ f z c β (γ+d-q-1) k hf hz)⟩

/-- The three actual outside families have the finite bounds needed to
apply genuine scalar duality to every Borcherds sum. -/
theorem outsideCoeff_bounds (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
    (hf : SupportedAt N₄ f β) (hz : z∈N₃.weight c)
    {d : ℤ} {u : V} (hu : u∈W.grading d) :
    (∃ Q : ℤ,∀ q : ℤ,q ≤ Q → outsideCoeffX hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz hu q=0) ∧
    (∃ Q : ℤ,∀ q : ℤ,Q ≤ q → outsideCoeffY hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz hu q=0) ∧
    (∃ Q : ℤ,∀ q : ℤ,Q ≤ q → outsideCoeffZ hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz hu q=0) := by
  constructor
  · obtain ⟨Q,hQ⟩ := exists_comp_mode_vanish_below hf hu
    refine ⟨Q,fun q hq => ?_⟩
    apply Subtype.ext
    change coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
      (f ∘ₗ mode (N₄.YM u) q) z c (β-d+q+1) γ k=0
    rw [hQ q hq,coefficient_zero_f]
  constructor
  · obtain ⟨Q,hQ⟩ := N₃.truncation u z
    refine ⟨Q,fun q hq => ?_⟩
    apply Subtype.ext
    change coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
      f (mode (N₃.YM u) q z) (c+d-q-1) β γ k=0
    rw [hQ q hq,LogAssocOutsideJacobi.coefficient_zero_z]
  · obtain ⟨Q,hQ⟩ := coefficient_shift_vanish hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz d
    refine ⟨Q,fun q hq => ?_⟩
    apply Subtype.ext
    change rhoL N₁.toWeakModule N₂.toWeakModule u q
      (coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
        f z c β (γ+d-q-1) k)=0
    rw [hQ q hq,map_zero]

/-- The genuine outside Borcherds identity in the actual coefficient module. -/
theorem outsideCoeff_borcherds (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
    (hf : SupportedAt N₄ f β) (hz : z∈N₃.weight c)
    {d : ℤ} {u : V} (hu : u∈W.grading d) (ell m : ℤ) :
    (∑ᶠ i : ℤ,(negOnePow i*cbz ell i) • outsideCoeffX hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz hu (ell+m-i))
    - negOnePow ell • (∑ᶠ i : ℤ,(negOnePow i*cbz ell i) • outsideCoeffY hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz hu (m+i))
    - (∑ᶠ i : ℤ,cbz m i • outsideCoeffZ hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz hu (ell+i))=0 := by
  let X := outsideCoeffX hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz hu
  let Y := outsideCoeffY hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz hu
  let Z := outsideCoeffZ hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz hu
  obtain ⟨⟨QX,hX⟩,⟨QY,hY⟩,⟨QZ,hZ⟩⟩ := outsideCoeff_bounds hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz hu
  have hFX : Function.HasFiniteSupport (fun i : ℤ => (negOnePow i*cbz ell i) • X (ell+m-i)) :=
    hfs_of _ 0 (max 0 (ell+m-QX)) (fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_apply_neg _ hi,mul_zero,zero_smul]
      · rw [show X (ell+m-i)=0 from hX _ (by omega),smul_zero])
  have hFY : Function.HasFiniteSupport (fun i : ℤ => (negOnePow i*cbz ell i) • Y (m+i)) :=
    hfs_of _ 0 (max 0 (QY-m)) (fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_apply_neg _ hi,mul_zero,zero_smul]
      · rw [show Y (m+i)=0 from hY _ (by omega),smul_zero])
  have hFZ : Function.HasFiniteSupport (fun i : ℤ => cbz m i • Z (ell+i)) :=
    hfs_of _ 0 (max 0 (QZ-ell)) (fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_apply_neg _ hi,zero_smul]
      · rw [show Z (ell+i)=0 from hZ _ (by omega),smul_zero])
  apply Subtype.ext
  apply bilinear_ext_homogeneous N₁ N₂
  intro a b x y hx hy
  let ev : coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ →ₗ[ℂ] ℂ :=
    { toFun := fun B => B.1 x y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change ev ((∑ᶠ i : ℤ,(negOnePow i*cbz ell i) • X (ell+m-i))
    - negOnePow ell • (∑ᶠ i : ℤ,(negOnePow i*cbz ell i) • Y (m+i))
    - (∑ᶠ i : ℤ,cbz m i • Z (ell+i)))=0
  rw [map_sub,map_sub,map_smul,map_finsum ev hFX,map_finsum ev hFY,map_finsum ev hFZ]
  simp only [map_smul,smul_eq_mul]
  exact coefficient_outside_borcherds_homogeneous hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz hu hx hy ell m

end VOA.Huang.LogAssocTensorOuterModes
