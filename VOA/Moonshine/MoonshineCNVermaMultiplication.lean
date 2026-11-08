import VOA.Moonshine.MoonshineCNRelativePBW

/-! The PBW--Verma multiplication map is bijective for complementary Lie subalgebras. -/

noncomputable section
open scoped TensorProduct
namespace VOA.Moonshine.ConwayNorton

open Module Finsupp
variable {g U : Type*} [LieRing g] [LieAlgebra ℂ g] [AddCommGroup U] [Module ℂ U]

theorem relativeTrivialBalancing_eq_bot :
    PBWTheorem.balancing (⊥ : LieSubalgebra ℂ g)
      (0 : (⊥ : LieSubalgebra ℂ g) →ₗ⁅ℂ⁆ End ℂ U) = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro _ ⟨a, x, u, rfl⟩
  have hx : (x : g) = 0 := x.property
  simp [hx]

/-- Inducing from the zero Lie algebra imposes no balancing relations. -/
def relativeTrivialInducedEquiv :
    relativeInducedSpace (⊥ : LieSubalgebra ℂ g)
      (0 : (⊥ : LieSubalgebra ℂ g) →ₗ⁅ℂ⁆ End ℂ U) ≃ₗ[ℂ]
        (UniversalEnvelopingAlgebra ℂ g ⊗[ℂ] U) :=
  (PBWTheorem.balancing _ _).quotEquivOfEqBot relativeTrivialBalancing_eq_bot

theorem relativeTrivialInducedEquiv_rep (z : g)
    (v : relativeInducedSpace (⊥ : LieSubalgebra ℂ g)
      (0 : (⊥ : LieSubalgebra ℂ g) →ₗ⁅ℂ⁆ End ℂ U)) :
    relativeTrivialInducedEquiv (relativeInducedRep (⊥ : LieSubalgebra ℂ g) 0 z v) =
      relativeTensorLeft (UniversalEnvelopingAlgebra.ι ℂ z) (relativeTrivialInducedEquiv v) := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rfl

variable (p q : LieSubalgebra ℂ g) (ρ : p →ₗ⁅ℂ⁆ End ℂ U)
variable {A : Type*} [LinearOrder A]
variable (hc : IsCompl p.toSubmodule q.toSubmodule) (bc : Basis A ℂ q)

/-- The same basis, now in the full subspace of the complement algebra. -/
def relativeComplementBasis : Basis A ℂ (⊤ : Submodule ℂ q) :=
  bc.map (Submodule.topEquiv).symm

/-- Multiplication into the genuine induced quotient: a ⊗ u maps to [ι(a) ⊗ u]. -/
def relativeVermaMultiplication :
    (UniversalEnvelopingAlgebra ℂ q ⊗[ℂ] U) →ₗ[ℂ] relativeInducedSpace p ρ :=
  (PBWTheorem.balancing p ρ).mkQ ∘ₗ
    (UniversalEnvelopingAlgebra.lift ℂ
      ((UniversalEnvelopingAlgebra.ι ℂ).comp q.incl)).toLinearMap.rTensor U

theorem relativeVermaMultiplication_action (z : q)
    (t : UniversalEnvelopingAlgebra ℂ q ⊗[ℂ] U) :
    relativeVermaMultiplication p q ρ (relativeTensorLeft (UniversalEnvelopingAlgebra.ι ℂ z) t) =
      relativeInducedRep p ρ (z : g) (relativeVermaMultiplication p q ρ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
      change Submodule.Quotient.mk
        ((UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp q.incl))
          (UniversalEnvelopingAlgebra.ι ℂ z * a) ⊗ₜ[ℂ] u) =
        Submodule.Quotient.mk ((UniversalEnvelopingAlgebra.ι ℂ (z : g) *
          (UniversalEnvelopingAlgebra.lift ℂ
            ((UniversalEnvelopingAlgebra.ι ℂ).comp q.incl)) a) ⊗ₜ[ℂ] u)
      rw [map_mul, UniversalEnvelopingAlgebra.lift_ι_apply]
      rfl
  | add t s ht hs => simpa only [map_add] using congrArg₂ (· + ·) ht hs

omit [LinearOrder A] in
theorem relativeVermaMultiplication_word (l : List A) (u : U) :
    relativeVermaMultiplication p q ρ
      (relativeTrivialInducedEquiv
        (relativeInducedWord (⊥ : LieSubalgebra ℂ q) 0 (relativeComplementBasis q bc) l u)) =
      relativeInducedWord p ρ bc l u := by
  induction l with
  | nil =>
      change Submodule.Quotient.mk
        ((UniversalEnvelopingAlgebra.lift ℂ
          ((UniversalEnvelopingAlgebra.ι ℂ).comp q.incl)) 1 ⊗ₜ[ℂ] u) = _
      rw [map_one]
      rfl
  | cons a l ih =>
      rw [relativeInducedWord_cons, relativeTrivialInducedEquiv_rep,
        relativeVermaMultiplication_action, relativeInducedWord_cons]
      change relativeInducedRep p ρ (bc a : g) _ = _
      rw [ih]

include hc bc in
/-- PBW–Verma multiplication in general form: actual multiplication, with both injectivity and
surjectivity. -/
theorem relativeVermaMultiplication_bijective :
    Function.Bijective (relativeVermaMultiplication p q ρ) := by
  let E : (Multiset A →₀ U) ≃ₗ[ℂ] (UniversalEnvelopingAlgebra ℂ q ⊗[ℂ] U) :=
    (relativePBWEquiv (⊥ : LieSubalgebra ℂ q) 0
      (show IsCompl (⊥ : Submodule ℂ q) ⊤ from isCompl_bot_top)
      (relativeComplementBasis q bc)).symm.trans relativeTrivialInducedEquiv
  let F := relativePBWEquiv p ρ hc bc
  have h : ∀ v : Multiset A →₀ U,
      relativeVermaMultiplication p q ρ (E v) = F.symm v := by
    suffices heq : relativeVermaMultiplication p q ρ ∘ₗ E.toLinearMap = F.symm.toLinearMap from
      fun v => LinearMap.congr_fun heq v
    apply Finsupp.lhom_ext
    intro m u
    change relativeVermaMultiplication p q ρ
      (relativeTrivialInducedEquiv
        (relativeInducedWordMap (⊥ : LieSubalgebra ℂ q) 0
          (relativeComplementBasis q bc) (single m u))) = relativeInducedWordMap p ρ bc (single m u)
    rw [relativeInducedWordMap_single, relativeInducedWordMap_single,
      relativeVermaMultiplication_word]
  constructor
  · intro x y hxy
    obtain ⟨v, rfl⟩ := E.surjective x
    obtain ⟨w, rfl⟩ := E.surjective y
    rw [h, h] at hxy
    rw [F.symm.injective hxy]
  · intro y
    exact ⟨E (F y), by rw [h, F.symm_apply_apply]⟩

namespace BorcherdsData

variable (D : BorcherdsData g) (ρ : D.parabolicPart →ₗ⁅ℂ⁆ End ℂ U)

def parabolicVermaMultiplication :
    (UniversalEnvelopingAlgebra ℂ D.positivePart ⊗[ℂ] U) →ₗ[ℂ]
      relativeInducedSpace D.parabolicPart ρ :=
  relativeVermaMultiplication D.parabolicPart D.positivePart ρ

/-- Relative PBW specialized using precisely the proved opposite-parabolic complement. -/
theorem parabolicVermaMultiplication_bijective :
    Function.Bijective (D.parabolicVermaMultiplication ρ) := by
  let bc := Basis.ofVectorSpace ℂ D.positivePart
  letI : LinearOrder (Basis.ofVectorSpaceIndex ℂ D.positivePart) :=
    WellOrderingRel.isWellOrder.linearOrder
  exact relativeVermaMultiplication_bijective D.parabolicPart D.positivePart ρ
    D.positive_parabolic_isCompl.symm bc

def parabolicVermaEquiv :
    (UniversalEnvelopingAlgebra ℂ D.positivePart ⊗[ℂ] U) ≃ₗ[ℂ]
      relativeInducedSpace D.parabolicPart ρ :=
  LinearEquiv.ofBijective (D.parabolicVermaMultiplication ρ)
    (D.parabolicVermaMultiplication_bijective ρ)

end BorcherdsData
end VOA.Moonshine.ConwayNorton
