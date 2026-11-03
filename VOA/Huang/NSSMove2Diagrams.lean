import VOA.Huang.NSSMoveFourier
import VOA.Huang.NgSchauenburgTraceChannels
import VOA.Huang.NgSchauenburgCentralOrder

/-! # Explicit morphisms in the mixed NS exchange

The two crossings below have the same source and target. Their equality is
the local mixed version of the exchange in NS Theorem 5.4(i). It is a named
unproved proposition, not an additional field of a fusion category.
-/
noncomputable section
set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg
universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- The normalized mixed S entry, with the repository's dual-label convention. -/
def mixedExchangeCoefficient (F : SphericalFusion C) (a b : F.Label)
    (q : F.Label × F.Label) : ℂ :=
  F.globalDimension⁻¹ * categoricalS F q.1 a * categoricalS F (F.dualLabel q.2) b

/-- Project the right strand into `A`, cross it inversely, and project back.
The reverse maps are composition-dual; hence the inverse simple dimension. -/
def inverseChannelCrossing (F : SphericalFusion C) (A : Center C) (i j : F.Label) :
    F.simple i ⊗ F.simple j ⟶ F.simple j ⊗ F.simple i :=
  (F.dimension (F.simple j))⁻¹ • ∑ β,
    F.simple i ◁ F.simpleHomBasis A.1 j β ≫ (A.2.β (F.simple i)).inv ≫
      F.compositionDual (F.simpleHomBasis A.1 j) β ▷ F.simple i

/-- Project the left strand into `A`, cross it forwards, and project back. -/
def forwardChannelCrossing (F : SphericalFusion C) (A : Center C) (i j : F.Label) :
    F.simple i ⊗ F.simple j ⟶ F.simple j ⊗ F.simple i :=
  (F.dimension (F.simple i))⁻¹ • ∑ β,
    F.simpleHomBasis A.1 i β ▷ F.simple j ≫ (A.2.β (F.simple j)).hom ≫
      F.simple j ◁ F.compositionDual (F.simpleHomBasis A.1 i) β

/-- The local mixed Müger exchange. This contains no indicator, probe power,
modular representation, or assertion about exhaustion of the centre. -/
def MixedMugerExchange (F : SphericalFusion C) : Prop :=
  ∀ a b i j : F.Label,
    inverseChannelCrossing F (mixedCenter (F.simple a) (F.simple b)) i j =
      ∑ q : F.Label × F.Label, mixedExchangeCoefficient F a b q •
        forwardChannelCrossing F (mixedCenter (F.simple q.1) (F.simple q.2)) i j

/-- Any linear closure of the local exchange preserves its coefficients. -/
theorem mixedMugerExchange_contract (F : SphericalFusion C) (h : MixedMugerExchange F)
    (a b i j : F.Label)
    (L : (F.simple i ⊗ F.simple j ⟶ F.simple j ⊗ F.simple i) →ₗ[ℂ] ℂ) :
    L (inverseChannelCrossing F (mixedCenter (F.simple a) (F.simple b)) i j) =
      ∑ q : F.Label × F.Label, mixedExchangeCoefficient F a b q *
        L (forwardChannelCrossing F (mixedCenter (F.simple q.1) (F.simple q.2)) i j) := by
  rw [h a b i j]
  simp

/-- Testing every reverse morphism by the perfect categorical trace pairing
is equivalent to the local morphism identity. A single chosen closure would
only be a consequence, not an equivalent replacement. -/
theorem mixedMugerExchange_iff_closed (F : SphericalFusion C) :
    MixedMugerExchange F ↔
      ∀ (a b i j : F.Label) (f : F.simple j ⊗ F.simple i ⟶ F.simple i ⊗ F.simple j),
        F.scalarTrace (F.simple i ⊗ F.simple j)
          (inverseChannelCrossing F (mixedCenter (F.simple a) (F.simple b)) i j ≫ f) =
        ∑ q : F.Label × F.Label, mixedExchangeCoefficient F a b q *
          F.scalarTrace (F.simple i ⊗ F.simple j)
            (forwardChannelCrossing F (mixedCenter (F.simple q.1) (F.simple q.2)) i j ≫ f) := by
  constructor
  · intro h a b i j f
    rw [h a b i j]
    simp [Preadditive.sum_comp]
  · intro h a b i j
    apply F.tracePairing_injective (F.simple j ⊗ F.simple i) (F.simple i ⊗ F.simple j)
    ext f
    change F.scalarTrace _ (f ≫ _) = F.scalarTrace _ (f ≫ _)
    rw [F.scalarTrace_comp_comm f, F.scalarTrace_comp_comm f]
    simpa [Preadditive.sum_comp] using h a b i j f

/-- Reassociation of two blocks of the same object, with no braided crossing. -/
def blockReassociation (V : C) (n k : ℕ) :
    tensorPower V (n + 1) ⊗ tensorPower V (k + 1) ≅
      tensorPower V (k + 1) ⊗ tensorPower V (n + 1) :=
  joinPower V n k ≪≫ eqToIso (by congr 1; omega) ≪≫ (joinPower V k n).symm

/-- Insert both simple-channel resolutions and close the two blocks. The
indices `n,k` stand for the positive degrees `m=n+1,l=k+1`. -/
def twoBlockClosure (F : SphericalFusion C) (V : C) (n k : ℕ) (i j : F.Label) :
    (F.simple i ⊗ F.simple j ⟶ F.simple j ⊗ F.simple i) →ₗ[ℂ] ℂ where
  toFun f := ∑ α, ∑ β,
    F.scalarTrace (tensorPower V (k + 1) ⊗ tensorPower V (n + 1))
      ((F.compositionDual (F.simpleHomBasis (tensorPower V (k + 1)) i) β ⊗ₘ
          F.compositionDual (F.simpleHomBasis (tensorPower V (n + 1)) j) α) ≫
        f ≫ (F.simpleHomBasis (tensorPower V (n + 1)) j α ⊗ₘ
          F.simpleHomBasis (tensorPower V (k + 1)) i β) ≫
        (blockReassociation V n k).hom)
  map_add' f g := by simp [Preadditive.comp_add, Preadditive.add_comp, Finset.sum_add_distrib]
  map_smul' z f := by simp [Finset.mul_sum]

/-- Close and sum all exterior channels in the local exchange. -/
theorem mixedMugerExchange_twoBlock (F : SphericalFusion C) (h : MixedMugerExchange F)
    (V : C) (n k : ℕ) (a b : F.Label) :
    (∑ i, ∑ j, twoBlockClosure F V n k i j
      (inverseChannelCrossing F (mixedCenter (F.simple a) (F.simple b)) i j)) =
    ∑ q : F.Label × F.Label, mixedExchangeCoefficient F a b q *
      ∑ i, ∑ j, twoBlockClosure F V n k i j
        (forwardChannelCrossing F (mixedCenter (F.simple q.1) (F.simple q.2)) i j) := by
  simp_rw [mixedMugerExchange_contract F h, Finset.mul_sum]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- NS Proposition 3.1 / Remark 3.2 in the two channel resolutions used in
Theorem 5.4. Both comparisons with the genuine rotation remain obligations.
The second equality uses the SAME closure and the forward crossing. -/
def MixedTwoBlockTraceFormula (F : SphericalFusion C) : Prop :=
  ∀ (V : C) (n k : ℕ) (a b : F.Label),
    (generalizedIndicatorInt F.toPivotal (mixedCenter (F.simple a) (F.simple b)) V n
        (k + 1) =
      ∑ i, ∑ j, twoBlockClosure F V n k i j
        (inverseChannelCrossing F (mixedCenter (F.simple a) (F.simple b)) i j)) ∧
    (generalizedIndicatorInt F.toPivotal (mixedCenter (F.simple a) (F.simple b)) V k
        (-(n + 1)) =
      ∑ i, ∑ j, twoBlockClosure F V n k i j
        (forwardChannelCrossing F (mixedCenter (F.simple a) (F.simple b)) i j))

/-- The actual positive-degree Fourier identity follows from the two precise
diagram obligations. No comparison between a diagram and an indicator is implicit. -/
theorem mixedPositiveFourier_of_diagrams (F : SphericalFusion C)
    (htrace : MixedTwoBlockTraceFormula F) (hex : MixedMugerExchange F)
    (V : C) (n k : ℕ) (a b : F.Label) :
    generalizedIndicatorInt F.toPivotal (mixedCenter (F.simple a) (F.simple b)) V n
        (k + 1) =
      ∑ q : F.Label × F.Label, mixedExchangeCoefficient F a b q *
        generalizedIndicatorInt F.toPivotal
          (mixedCenter (F.simple q.1) (F.simple q.2)) V k (-(n + 1)) := by
  rw [(htrace V n k a b).1, mixedMugerExchange_twoBlock F hex]
  apply Finset.sum_congr rfl
  intro q _
  rw [(htrace V n k q.1 q.2).2]

end VOA.Huang.NSCongruence
