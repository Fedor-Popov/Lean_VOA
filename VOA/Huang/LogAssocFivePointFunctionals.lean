import VOA.Huang.LogAssocCoefficientCompatibility
import VOA.Modules.LogTensorTwist

/-! Genuine homogeneous test functionals obtained by freezing one input and
one actual logarithmic mode. These prepare the actual single-weight sewing
identities, retaining arbitrary generalized weights and logarithmic degrees. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocFivePointFunctionals
open VOA VOA.LogTensor VOA.LogTensor.Contra
open VOA.Huang.LogAssocCoefficientCompatibility
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}
variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)

/-- Every true log mode with a frozen second input gives a genuinely
supported first-input functional at the forced generalized weight. -/
theorem supportedAt_intertwiner_flip {f : M₃ →ₗ[ℂ] ℂ} {β c : ℂ}
    (hf : SupportedAt N₃ f β) {z : M₂} (hz : z∈N₂.weight c) (n : ℂ) (k : ℕ) :
    SupportedAt N₁ (f ∘ₗ (Y.1 n k).flip z) (β-c+n+1) := by
  intro a ha x hx
  change f (Y.1 n k x z)=0
  apply hf (a+c-n-1)
  · intro he
    apply ha
    linear_combination he
  · exact Y.2.mem_weight hx hz n k

/-- Every true log mode with a frozen first input gives a genuinely
supported second-input functional at the forced generalized weight. -/
theorem supportedAt_intertwiner_left {f : M₃ →ₗ[ℂ] ℂ} {β a : ℂ}
    (hf : SupportedAt N₃ f β) {x : M₁} (hx : x∈N₁.weight a) (n : ℂ) (k : ℕ) :
    SupportedAt N₂ (f ∘ₗ Y.1 n k x) (β-a+n+1) := by
  intro b hb z hz
  change f (Y.1 n k x z)=0
  apply hf (a+b-n-1)
  · intro he
    apply hb
    linear_combination he
  · exact Y.2.mem_weight hx hz n k

end VOA.Huang.LogAssocFivePointFunctionals
