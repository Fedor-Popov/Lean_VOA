import VOA.Huang.LogAssocExpansionVectors
import VOA.Modules.LogTensorFinSpan

/-! The genuine intermediate generalized spectrum splits into finitely
many disjoint integer cosets. Actual product expansions are summed over
these cosets, once each, retaining all logarithmic degrees. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.Huang.FrobeniusLog VOA.Huang.AssocExpansion
open VOA.Huang.LogRemovalCoeff
open VOA.Huang.AssocCoeffRules (hasLogExp_sum)
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- Equality of monodromy eigenvalues is precisely the integer-coset relation. -/
theorem monoEig_add_int (a : ℂ) (d : ℤ) : monoEig (a+d)=monoEig a := by
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨d,?_⟩
  dsimp [monoEig,FrobeniusLog.twoPiI]
  ring

/-- This finite set comes from the actual finitely generated generalized module. -/
noncomputable def spectrumCosetSeeds (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) : Finset ℂ :=
  Classical.choose (LogFin.exists_weight_cosets N hC2 hfg)

theorem spectrumCosetSeeds_spec (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) (a : ℂ) (ha : N.weight a≠⊥) :
    ∃ h∈spectrumCosetSeeds hC2 N hfg,∃ d : ℤ,a=h+d :=
  Classical.choose_spec (LogFin.exists_weight_cosets N hC2 hfg) a ha

/-- Distinct monodromy values represent distinct actual integer cosets. -/
noncomputable def spectrumCosets (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) : Finset ℂ := by
  classical
  exact (spectrumCosetSeeds hC2 N hfg).image monoEig

/-- Select one real member of the proved finite seed set per represented coset. -/
noncomputable def spectrumCosetRep (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) (mu : ℂ) : ℂ := by
  classical
  exact if h : mu∈spectrumCosets hC2 N hfg then
    Classical.choose (Finset.mem_image.mp h) else 0

theorem spectrumCosetRep_spec (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) {mu : ℂ} (hmu : mu∈spectrumCosets hC2 N hfg) :
    spectrumCosetRep hC2 N hfg mu∈spectrumCosetSeeds hC2 N hfg ∧
      monoEig (spectrumCosetRep hC2 N hfg mu)=mu := by
  classical
  dsimp only [spectrumCosetRep]
  rw [dif_pos hmu]
  exact Classical.choose_spec (Finset.mem_image.mp hmu)

/-- Every nonzero actual weight belongs to exactly one of the chosen integer cosets. -/
theorem exists_spectrumCoset_weight (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) (a : ℂ) (ha : N.weight a≠⊥) :
    ∃ mu∈spectrumCosets hC2 N hfg,∃ d : ℤ,a=spectrumCosetRep hC2 N hfg mu+d := by
  classical
  obtain ⟨h,hh,d,rfl⟩ := spectrumCosetSeeds_spec hC2 N hfg a ha
  have hmu : monoEig h∈spectrumCosets hC2 N hfg := Finset.mem_image.mpr ⟨h,hh,rfl⟩
  obtain ⟨e,he⟩ := exists_int_of_monoEig_eq ((monoEig_add_int h d).trans
    (spectrumCosetRep_spec hC2 N hfg hmu).2.symm)
  exact ⟨monoEig h,hmu,e,by linear_combination he⟩

theorem spectrumCoset_weight_unique (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) {mu nu : ℂ}
    (hmu : mu∈spectrumCosets hC2 N hfg) (hnu : nu∈spectrumCosets hC2 N hfg)
    (d e : ℤ) (h : spectrumCosetRep hC2 N hfg mu+d=spectrumCosetRep hC2 N hfg nu+e) :
    mu=nu := by
  have hh := congrArg monoEig h
  rw [monoEig_add_int,monoEig_add_int,(spectrumCosetRep_spec hC2 N hfg hmu).2,
    (spectrumCosetRep_spec hC2 N hfg hnu).2] at hh
  exact hh

variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- The actual full product on every represented intermediate integer coset,
with each coset used once and all outer logarithmic degrees retained. -/
noncomputable def logProductSpectrumFun (hC2 : C2Cofinite W) (N₅ : LogVModule W M₅)
    (hfg₅ : FinGen N₅.toWeakModule) (Y₁ : LogModes M₁ M₅ M₄) (Y₂ : LogModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (α₁ α₂ α₃ β t : ℂ) : ℂ :=
  ∑ mu∈spectrumCosets hC2 N₅ hfg₅,
    logProductFullCosetFun Y₁ Y₂ f x y z
      (α₁+spectrumCosetRep hC2 N₅ hfg₅ mu-β-1)
      (α₂+α₃-spectrumCosetRep hC2 N₅ hfg₅ mu-1) t

/-- The entire genuine intermediate spectrum gives a finite convergent
logarithmic collision expansion, for arbitrary actual input vectors. -/
theorem log_product_spectrum_hasLogExp (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (α₁ α₂ α₃ β : ℂ)  :
    HasLogExp overlapDomain (logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z α₁ α₂ α₃ β) := by
  classical
  exact hasLogExp_sum _ fun mu _ =>
    log_product_fullCoset_hasLogExp_all hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f x y z _ _

end VOA.Huang.LogAssocExpansion
