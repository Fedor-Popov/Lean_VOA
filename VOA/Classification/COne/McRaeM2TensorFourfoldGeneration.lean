import VOA.Classification.COne.McRaeM2TensorNestedGeneration

/-! All five actual fourfold tensor parenthesizations are linearly generated
by their literal nested canonical coefficients. Equality on these values
determines arbitrary linear maps for genuine pentagon comparisons. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.LogTensor VOA.LogTensor.Pz VOA.VHat VOA.VHat.DLM3
universe u
variable {V M₁ M₂ M₃ M₄ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule)
  (N₃ : LogVModule W M₃) (h₃ : FinGen N₃.toWeakModule)
  (N₄ : LogVModule W M₄) (h₄ : FinGen N₄.toWeakModule)

theorem leftTriple_finGen : FinGen (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule :=
  tensorModule_finGen hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
    (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃

theorem rightTriple_finGen : FinGen (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule
    :=
  tensorModule_finGen hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
    h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃)

abbrev leftFourDual := tensorDual hC2 (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃) N₄
    (leftTriple_finGen hC2 N₁ N₂ h₁ h₂ N₃ h₃) h₄

/-- Actual nested canonical values for this genuine fourfold parenthesization. -/
def leftFourZeroModeValues : Set (RestrictedDual (leftFourDual hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄
    h₄).toGW) :=
  tensorValuesOn hC2 (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃) N₄ (leftTriple_finGen hC2
    N₁ N₂ h₁ h₂ N₃ h₃) h₄ (leftTripleZeroModeValues hC2 N₁ N₂ h₁ h₂ N₃ h₃) Set.univ

/-- These literal nested coefficients span the entire actual fourfold tensor. -/
theorem leftFour_zeroMode_span_eq_top :
    Submodule.span ℂ (leftFourZeroModeValues hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄)=⊤ :=
  tensorValuesOn_span_eq_top hC2 (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃) N₄
    (leftTriple_finGen hC2 N₁ N₂ h₁ h₂ N₃ h₃) h₄
    (leftTripleZeroModeValues hC2 N₁ N₂ h₁ h₂ N₃ h₃) Set.univ
      (leftTriple_zeroMode_span_eq_top hC2 N₁ N₂ h₁ h₂ N₃ h₃) (by rw [Submodule.span_univ])

/-- The literal three nested canonical insertions in this actual fourfold object. -/
def leftFourCoefficient (n m p : ℂ) (x : M₁) (y : M₂) (z : M₃) (w : M₄) :
    RestrictedDual (leftFourDual hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄).toGW :=
  ((tensorIntertwiner hC2 (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃) N₄ (leftTriple_finGen
    hC2 N₁ N₂ h₁ h₂ N₃ h₃) h₄).1 n 0 ((tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂
    h₁ h₂) N₃ (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃).1 m 0 ((tensorIntertwiner hC2 N₁
    N₂ h₁ h₂).1 p 0 x y) z) w)

/-- Three literal canonical coefficient insertions determine arbitrary linear maps. -/
theorem leftFour_linearMap_ext {X : Type*} [AddCommGroup X] [Module ℂ X]
    {f g : RestrictedDual (leftFourDual hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄).toGW →ₗ[ℂ] X}
    (h : ∀ n m p x y z w,
      f (leftFourCoefficient hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄ n m p x y z w)=
        g (leftFourCoefficient hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄ n m p x y z w)) : f=g := by
  apply LinearMap.ext_on (leftFour_zeroMode_span_eq_top hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄)
  rintro q ⟨n,u,w,⟨m,v,z,⟨⟨p,x,y⟩,rfl⟩,hz,rfl⟩,hw,rfl⟩
  exact h n m p x y z w

abbrev midLeftFourDual := tensorDual hC2 (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃) N₄
    (rightTriple_finGen hC2 N₁ N₂ h₁ h₂ N₃ h₃) h₄

/-- Actual nested canonical values for this genuine fourfold parenthesization. -/
def midLeftFourZeroModeValues : Set (RestrictedDual (midLeftFourDual hC2 N₁ N₂ h₁ h₂ N₃ h₃
    N₄ h₄).toGW) :=
  tensorValuesOn hC2 (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃) N₄ (rightTriple_finGen
    hC2 N₁ N₂ h₁ h₂ N₃ h₃) h₄ (rightTripleZeroModeValues hC2 N₁ N₂ h₁ h₂ N₃ h₃) Set.univ

/-- These literal nested coefficients span the entire actual fourfold tensor. -/
theorem midLeftFour_zeroMode_span_eq_top :
    Submodule.span ℂ (midLeftFourZeroModeValues hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄)=⊤ :=
  tensorValuesOn_span_eq_top hC2 (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃) N₄
    (rightTriple_finGen hC2 N₁ N₂ h₁ h₂ N₃ h₃) h₄
    (rightTripleZeroModeValues hC2 N₁ N₂ h₁ h₂ N₃ h₃) Set.univ
      (rightTriple_zeroMode_span_eq_top hC2 N₁ N₂ h₁ h₂ N₃ h₃) (by rw [Submodule.span_univ])

/-- The literal three nested canonical insertions in this actual fourfold object. -/
def midLeftFourCoefficient (n m p : ℂ) (x : M₁) (y : M₂) (z : M₃) (w : M₄) :
    RestrictedDual (midLeftFourDual hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄).toGW :=
  ((tensorIntertwiner hC2 (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃) N₄
    (rightTriple_finGen hC2 N₁ N₂ h₁ h₂ N₃ h₃) h₄).1 n 0 ((tensorIntertwiner hC2 N₁
    (tensorModule hC2 N₂ N₃ h₂ h₃) h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃)).1 m 0 x
    ((tensorIntertwiner hC2 N₂ N₃ h₂ h₃).1 p 0 y z)) w)

/-- Three literal canonical coefficient insertions determine arbitrary linear maps. -/
theorem midLeftFour_linearMap_ext {X : Type*} [AddCommGroup X] [Module ℂ X]
    {f g : RestrictedDual (midLeftFourDual hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄).toGW →ₗ[ℂ] X}
    (h : ∀ n m p x y z w,
      f (midLeftFourCoefficient hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄ n m p x y z w)=
        g (midLeftFourCoefficient hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄ n m p x y z w)) : f=g := by
  apply LinearMap.ext_on (midLeftFour_zeroMode_span_eq_top hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄)
  rintro q ⟨n,u,w,⟨m,x,v,hx,⟨⟨p,y,z⟩,rfl⟩,rfl⟩,hw,rfl⟩
  exact h n m p x y z w

abbrev middleFourDual := tensorDual hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) (tensorModule hC2
    N₃ N₄ h₃ h₄) (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) (tensorModule_finGen hC2 N₃
    N₄ h₃ h₄)

/-- Actual nested canonical values for this genuine fourfold parenthesization. -/
def middleFourZeroModeValues : Set (RestrictedDual (middleFourDual hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄
    h₄).toGW) :=
  tensorValuesOn hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) (tensorModule hC2 N₃ N₄ h₃ h₄)
    (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) (tensorModule_finGen hC2 N₃ N₄ h₃ h₄)
    (tensorZeroModeValues hC2 N₁ N₂ h₁ h₂) (tensorZeroModeValues hC2 N₃ N₄ h₃ h₄)

/-- These literal nested coefficients span the entire actual fourfold tensor. -/
theorem middleFour_zeroMode_span_eq_top :
    Submodule.span ℂ (middleFourZeroModeValues hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄)=⊤ :=
  tensorValuesOn_span_eq_top hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) (tensorModule hC2 N₃
    N₄ h₃ h₄) (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) (tensorModule_finGen hC2 N₃ N₄ h₃
    h₄)
    (tensorZeroModeValues hC2 N₁ N₂ h₁ h₂) (tensorZeroModeValues hC2 N₃ N₄ h₃ h₄)
      (tensor_zeroMode_span_eq_top hC2 N₁ N₂ h₁ h₂) (tensor_zeroMode_span_eq_top hC2 N₃
      N₄ h₃ h₄)

/-- The literal three nested canonical insertions in this actual fourfold object. -/
def middleFourCoefficient (n m p : ℂ) (x : M₁) (y : M₂) (z : M₃) (w : M₄) :
    RestrictedDual (middleFourDual hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄).toGW :=
  ((tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) (tensorModule hC2 N₃ N₄ h₃
    h₄) (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) (tensorModule_finGen hC2 N₃ N₄ h₃ h₄)).1 n
    0 ((tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 m 0 x y) ((tensorIntertwiner hC2 N₃ N₄ h₃
    h₄).1 p 0 z w))

/-- Three literal canonical coefficient insertions determine arbitrary linear maps. -/
theorem middleFour_linearMap_ext {X : Type*} [AddCommGroup X] [Module ℂ X]
    {f g : RestrictedDual (middleFourDual hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄).toGW →ₗ[ℂ] X}
    (h : ∀ n m p x y z w,
      f (middleFourCoefficient hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄ n m p x y z w)=
        g (middleFourCoefficient hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄ n m p x y z w)) : f=g := by
  apply LinearMap.ext_on (middleFour_zeroMode_span_eq_top hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄)
  rintro q ⟨n,u,v,⟨⟨m,x,y⟩,rfl⟩,⟨⟨p,z,w⟩,rfl⟩,rfl⟩
  exact h n m p x y z w

abbrev midRightFourDual := tensorDual hC2 N₁ (leftTripleModule hC2 N₂ N₃ h₂ h₃ N₄ h₄) h₁
    (leftTriple_finGen hC2 N₂ N₃ h₂ h₃ N₄ h₄)

/-- Actual nested canonical values for this genuine fourfold parenthesization. -/
def midRightFourZeroModeValues : Set (RestrictedDual (midRightFourDual hC2 N₁ N₂ h₁ h₂ N₃ h₃
    N₄ h₄).toGW) :=
  tensorValuesOn hC2 N₁ (leftTripleModule hC2 N₂ N₃ h₂ h₃ N₄ h₄) h₁ (leftTriple_finGen
    hC2 N₂ N₃ h₂ h₃ N₄ h₄) Set.univ (leftTripleZeroModeValues hC2 N₂ N₃ h₂ h₃ N₄ h₄)

/-- These literal nested coefficients span the entire actual fourfold tensor. -/
theorem midRightFour_zeroMode_span_eq_top :
    Submodule.span ℂ (midRightFourZeroModeValues hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄)=⊤ :=
  tensorValuesOn_span_eq_top hC2 N₁ (leftTripleModule hC2 N₂ N₃ h₂ h₃ N₄ h₄) h₁
    (leftTriple_finGen hC2 N₂ N₃ h₂ h₃ N₄ h₄)
    Set.univ (leftTripleZeroModeValues hC2 N₂ N₃ h₂ h₃ N₄ h₄) (by rw [Submodule.span_univ])
      (leftTriple_zeroMode_span_eq_top hC2 N₂ N₃ h₂ h₃ N₄ h₄)

/-- The literal three nested canonical insertions in this actual fourfold object. -/
def midRightFourCoefficient (n m p : ℂ) (x : M₁) (y : M₂) (z : M₃) (w : M₄) :
    RestrictedDual (midRightFourDual hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄).toGW :=
  ((tensorIntertwiner hC2 N₁ (leftTripleModule hC2 N₂ N₃ h₂ h₃ N₄ h₄) h₁
    (leftTriple_finGen hC2 N₂ N₃ h₂ h₃ N₄ h₄)).1 n 0 x ((tensorIntertwiner hC2
    (tensorModule hC2 N₂ N₃ h₂ h₃) N₄ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃) h₄).1 m 0
    ((tensorIntertwiner hC2 N₂ N₃ h₂ h₃).1 p 0 y z) w))

/-- Three literal canonical coefficient insertions determine arbitrary linear maps. -/
theorem midRightFour_linearMap_ext {X : Type*} [AddCommGroup X] [Module ℂ X]
    {f g : RestrictedDual (midRightFourDual hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄).toGW →ₗ[ℂ] X}
    (h : ∀ n m p x y z w,
      f (midRightFourCoefficient hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄ n m p x y z w)=
        g (midRightFourCoefficient hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄ n m p x y z w)) : f=g := by
  apply LinearMap.ext_on (midRightFour_zeroMode_span_eq_top hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄)
  rintro q ⟨n,x,u,hx,⟨m,v,w,⟨⟨p,y,z⟩,rfl⟩,hw,rfl⟩,rfl⟩
  exact h n m p x y z w

abbrev rightFourDual := tensorDual hC2 N₁ (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₄ h₄) h₁
    (rightTriple_finGen hC2 N₂ N₃ h₂ h₃ N₄ h₄)

/-- Actual nested canonical values for this genuine fourfold parenthesization. -/
def rightFourZeroModeValues : Set (RestrictedDual (rightFourDual hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄
    h₄).toGW) :=
  tensorValuesOn hC2 N₁ (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₄ h₄) h₁ (rightTriple_finGen
    hC2 N₂ N₃ h₂ h₃ N₄ h₄) Set.univ (rightTripleZeroModeValues hC2 N₂ N₃ h₂ h₃ N₄ h₄)

/-- These literal nested coefficients span the entire actual fourfold tensor. -/
theorem rightFour_zeroMode_span_eq_top :
    Submodule.span ℂ (rightFourZeroModeValues hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄)=⊤ :=
  tensorValuesOn_span_eq_top hC2 N₁ (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₄ h₄) h₁
    (rightTriple_finGen hC2 N₂ N₃ h₂ h₃ N₄ h₄)
    Set.univ (rightTripleZeroModeValues hC2 N₂ N₃ h₂ h₃ N₄ h₄) (by rw [Submodule.span_univ])
      (rightTriple_zeroMode_span_eq_top hC2 N₂ N₃ h₂ h₃ N₄ h₄)

/-- The literal three nested canonical insertions in this actual fourfold object. -/
def rightFourCoefficient (n m p : ℂ) (x : M₁) (y : M₂) (z : M₃) (w : M₄) :
    RestrictedDual (rightFourDual hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄).toGW :=
  ((tensorIntertwiner hC2 N₁ (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₄ h₄) h₁
    (rightTriple_finGen hC2 N₂ N₃ h₂ h₃ N₄ h₄)).1 n 0 x ((tensorIntertwiner hC2 N₂
    (tensorModule hC2 N₃ N₄ h₃ h₄) h₂ (tensorModule_finGen hC2 N₃ N₄ h₃ h₄)).1 m 0 y
    ((tensorIntertwiner hC2 N₃ N₄ h₃ h₄).1 p 0 z w)))

/-- Three literal canonical coefficient insertions determine arbitrary linear maps. -/
theorem rightFour_linearMap_ext {X : Type*} [AddCommGroup X] [Module ℂ X]
    {f g : RestrictedDual (rightFourDual hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄).toGW →ₗ[ℂ] X}
    (h : ∀ n m p x y z w,
      f (rightFourCoefficient hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄ n m p x y z w)=
        g (rightFourCoefficient hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄ n m p x y z w)) : f=g := by
  apply LinearMap.ext_on (rightFour_zeroMode_span_eq_top hC2 N₁ N₂ h₁ h₂ N₃ h₃ N₄ h₄)
  rintro q ⟨n,x,u,hx,⟨m,y,v,hy,⟨⟨p,z,w⟩,rfl⟩,rfl⟩,rfl⟩
  exact h n m p x y z w

end VOA.C2Rigid.LocalInjective
