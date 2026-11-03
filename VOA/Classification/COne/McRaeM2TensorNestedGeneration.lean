import VOA.Classification.COne.McRaeM2TensorGeneration
import VOA.Classification.COne.McRaeM2TensorClosure

/-! Actual nested canonical tensor coefficients generate the iterated tensor
objects as complex vector spaces. Equality on these literal coefficients
therefore determines arbitrary linear maps, supporting genuine associator
inverses and coherence once the associator maps are constructed. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.LogTensor VOA.LogTensor.Pz VOA.VHat VOA.VHat.DLM3
open Module (End)
universe u
variable {V M₁ M₂ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule)

/-- Literal canonical zero-log coefficients on specified actual source vectors. -/
def tensorValuesOn (S₁ : Set M₁) (S₂ : Set M₂) :
    Set (RestrictedDual (tensorDual hC2 N₁ N₂ h₁ h₂).toGW) :=
  {q | ∃ n x y,x∈S₁ ∧ y∈S₂ ∧ q=(tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 n 0 x y}

/-- Actual source spanning sets give an actual tensor spanning set. -/
theorem tensorValuesOn_span_eq_top (S₁ : Set M₁) (S₂ : Set M₂)
    (hS₁ : Submodule.span ℂ S₁=⊤) (hS₂ : Submodule.span ℂ S₂=⊤) :
    Submodule.span ℂ (tensorValuesOn hC2 N₁ N₂ h₁ h₂ S₁ S₂)=⊤ := by
  let T := Submodule.span ℂ (tensorValuesOn hC2 N₁ N₂ h₁ h₂ S₁ S₂)
  have hxy (n : ℂ) (x : M₁) (y : M₂) : (tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 n 0 x y∈T := by
    have hx : x∈Submodule.span ℂ S₁ := by rw [hS₁]; exact Submodule.mem_top
    have hy : y∈Submodule.span ℂ S₂ := by rw [hS₂]; exact Submodule.mem_top
    refine Submodule.span_induction (p := fun x _ => (tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 n 0 x y∈T)
      ?_ ?_ ?_ ?_ hx
    · intro x hx
      refine Submodule.span_induction (p := fun y _ => (tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 n 0 x y∈T)
        ?_ ?_ ?_ ?_ hy
      · intro y hy
        exact Submodule.subset_span ⟨n,x,y,hx,hy,rfl⟩
      · dsimp only; rw [map_zero]; exact T.zero_mem
      · intro y z _ _ hy hz
        rw [map_add]; exact T.add_mem hy hz
      · intro c y _ hy
        rw [map_smul]; exact T.smul_mem c hy
    · dsimp only; rw [map_zero,LinearMap.zero_apply]; exact T.zero_mem
    · intro x z _ _ hx hz
      rw [map_add,LinearMap.add_apply]; exact T.add_mem hx hz
    · intro c x _ hx
      rw [map_smul,LinearMap.smul_apply]; exact T.smul_mem c hx
  have hle : Submodule.span ℂ (tensorZeroModeValues hC2 N₁ N₂ h₁ h₂)≤T := by
    apply Submodule.span_le.mpr
    rintro q ⟨⟨n,x,y⟩,rfl⟩
    exact hxy n x y
  rw [tensor_zeroMode_span_eq_top hC2 N₁ N₂ h₁ h₂] at hle
  exact top_unique hle

/-- Arbitrary linear tensor maps are determined on any actual source spanning sets. -/
theorem tensor_sourceGenerators_linearMap_ext (S₁ : Set M₁) (S₂ : Set M₂)
    (hS₁ : Submodule.span ℂ S₁=⊤) (hS₂ : Submodule.span ℂ S₂=⊤)
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    {f g : RestrictedDual (tensorDual hC2 N₁ N₂ h₁ h₂).toGW →ₗ[ℂ] X}
    (h : ∀ n x y,x∈S₁ → y∈S₂ →
      f ((tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 n 0 x y)=
      g ((tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 n 0 x y)) : f=g := by
  apply LinearMap.ext_on (tensorValuesOn_span_eq_top hC2 N₁ N₂ h₁ h₂ S₁ S₂ hS₁ hS₂)
  rintro q ⟨n,x,y,hx,hy,rfl⟩
  exact h n x y hx hy

variable {M₃ : Type u} [AddCommGroup M₃] [Module ℂ M₃]
variable (N₃ : LogVModule W M₃) (h₃ : FinGen N₃.toWeakModule)

abbrev leftTripleModule := tensorModule hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
  (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃
abbrev leftTripleDual := tensorDual hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
  (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃
abbrev rightTripleModule := tensorModule hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
  h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃)
abbrev rightTripleDual := tensorDual hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
  h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃)

/-- Literal ((x tensor y) tensor z) canonical coefficients. -/
def leftTripleZeroModeValues : Set (RestrictedDual (leftTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW) :=
  tensorValuesOn hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
    (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃
    (tensorZeroModeValues hC2 N₁ N₂ h₁ h₂) Set.univ

/-- Literal (x tensor (y tensor z)) canonical coefficients. -/
def rightTripleZeroModeValues : Set (RestrictedDual (rightTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW) :=
  tensorValuesOn hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
    h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃)
    Set.univ (tensorZeroModeValues hC2 N₂ N₃ h₂ h₃)

/-- Genuine nested left coefficients linearly span the whole actual triple tensor. -/
theorem leftTriple_zeroMode_span_eq_top :
    Submodule.span ℂ (leftTripleZeroModeValues hC2 N₁ N₂ h₁ h₂ N₃ h₃)=⊤ :=
  tensorValuesOn_span_eq_top hC2 _ N₃ _ h₃ _ Set.univ
    (tensor_zeroMode_span_eq_top hC2 N₁ N₂ h₁ h₂) (by rw [Submodule.span_univ])

/-- The same actual spanning theorem holds for the genuine right triple tensor. -/
theorem rightTriple_zeroMode_span_eq_top :
    Submodule.span ℂ (rightTripleZeroModeValues hC2 N₁ N₂ h₁ h₂ N₃ h₃)=⊤ :=
  tensorValuesOn_span_eq_top hC2 N₁ _ h₁ _ Set.univ _
    (by rw [Submodule.span_univ]) (tensor_zeroMode_span_eq_top hC2 N₂ N₃ h₂ h₃)

/-- Equality on literal left nested zero-log modes determines arbitrary linear maps. -/
theorem leftTriple_linearMap_ext {X : Type*} [AddCommGroup X] [Module ℂ X]
    {f g : RestrictedDual (leftTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW →ₗ[ℂ] X}
    (h : ∀ n m x y z,
      f ((tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃).1 n 0
        ((tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 m 0 x y) z)=
      g ((tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃).1 n 0
        ((tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 m 0 x y) z)) : f=g := by
  apply LinearMap.ext_on (leftTriple_zeroMode_span_eq_top hC2 N₁ N₂ h₁ h₂ N₃ h₃)
  rintro q ⟨n,u,z,⟨⟨m,x,y⟩,rfl⟩,hz,rfl⟩
  exact h n m x y z

/-- Equality on literal right nested modes determines arbitrary linear maps. -/
theorem rightTriple_linearMap_ext {X : Type*} [AddCommGroup X] [Module ℂ X]
    {f g : RestrictedDual (rightTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW →ₗ[ℂ] X}
    (h : ∀ n m x y z,
      f ((tensorIntertwiner hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
        h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃)).1 n 0 x
        ((tensorIntertwiner hC2 N₂ N₃ h₂ h₃).1 m 0 y z))=
      g ((tensorIntertwiner hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
        h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃)).1 n 0 x
        ((tensorIntertwiner hC2 N₂ N₃ h₂ h₃).1 m 0 y z))) : f=g := by
  apply LinearMap.ext_on (rightTriple_zeroMode_span_eq_top hC2 N₁ N₂ h₁ h₂ N₃ h₃)
  rintro q ⟨n,x,u,hx,⟨⟨m,y,z⟩,rfl⟩,rfl⟩
  exact h n m x y z

end VOA.C2Rigid.LocalInjective
