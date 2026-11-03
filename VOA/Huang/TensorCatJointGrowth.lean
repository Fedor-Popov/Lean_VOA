import VOA.Huang.TensorCatSpectrum
import VOA.Huang.HuangODEThreeConvergence
import VOA.Huang.HuangODEThreeAlgebra
import VOA.Huang.HuangODEThreeC1

/-! # From local joint coefficient bounds to five-point sewing

This is a conditional bridge on the actual five-point coefficients. Strong
rationality supplies finite spectral support, but does not yet supply the
joint coefficient bounds in this file. All other sewing inputs remain explicit.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.HuangODEThree
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (F : FusionChoice W)

/-- The missing local coefficient estimate, on the genuine chart and all five
expansions. It contains no convergence or coherence assertion. -/
def FivePointCoefficientGrowth : Prop :=
  ∀ (X Y Z T U : Ordinary W) (b : FiveTree) (k : fiveObj F X Y Z T b ⟶ U)
    (d : FivePointTest X Y Z T U) (h h' : ℂ),
    LocalJointGrowth (fun m n => fivePointTerm F b k d (h + m, h' + n))

/-- The finite spectral cover reduces the genuine complex-weight sum to joint
natural-level estimates. Overlapping progressions require no quotient choices. -/
theorem fivePoint_summable_norm_of_coefficientGrowth (hV : StronglyRational W)
    (hΦ : Finite (Φ W)) (hg : FivePointCoefficientGrowth F)
    {X Y Z T U : Ordinary W} (b : FiveTree) (k : fiveObj F X Y Z T b ⟶ U)
    (d : FivePointTest X Y Z T U) :
    Summable (fun q : ℂ × ℂ => ‖fivePointTerm F b k d q‖) := by
  classical
  obtain ⟨S, R, hST⟩ := fivePoint_finite_spectral_cover F hV hΦ b k d
  apply summable_norm_of_finite_cover (fivePointTerm F b k d) (S ×ˢ R)
    (fun h (q : ℕ × ℕ) => (h.1 + q.1, h.2 + q.2))
  · intro h _ q q' hq
    apply Prod.ext
    · exact weight_progression_injective h.1 (congrArg Prod.fst hq)
    · exact weight_progression_injective h.2 (congrArg Prod.snd hq)
  · intro q hq
    obtain ⟨h, hh, h', hh', m, n, hm, hn⟩ := hST q.1 q.2 hq
    exact ⟨(h, h'), Finset.mem_product.mpr ⟨hh, hh'⟩, (m, n), Prod.ext hm.symm hn.symm⟩
  · intro h _
    exact (hg X Y Z T U b k d h.1 h.2).summable_norm

/-- Joint coefficient bounds imply the precise norm-growth obligation. -/
theorem fivePointNormGrowth_of_coefficientGrowth (hV : StronglyRational W)
    (hΦ : Finite (Φ W)) (hg : FivePointCoefficientGrowth F) : FivePointNormGrowth F := by
  intro X Y Z T U b k d
  exact ((summable_prod_of_nonneg (fun _ => norm_nonneg _)).mp
    (fivePoint_summable_norm_of_coefficientGrowth F hV hΦ hg b k d)).2

/-- PBW is used only to discharge finiteness of simple ordinary modules here. -/
theorem fivePointNormGrowth_of_coefficientGrowth_pbw (hV : StronglyRational W)
    (hg : FivePointCoefficientGrowth F) : FivePointNormGrowth F :=
  fivePointNormGrowth_of_coefficientGrowth F hV
    (PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hV) hg

/-- Conditional assembly. Neither coefficient growth nor the three remaining
coherence/normalization obligations are asserted to follow from strong rationality. -/
abbrev monoidalCategoryOfCoefficientGrowth_pbw (hV : StronglyRational W)
    (hg : FivePointCoefficientGrowth F) (hf : FivePointLeftFaithfulness F)
    (he : FivePointFiberEdges F
      (naturalReassociationOfEvaluation F (ordinaryFourPointInput_pbw F hV)).associators)
    (hv : VacuumCreationCompatibility F
      (naturalReassociationOfEvaluation F (ordinaryFourPointInput_pbw F hV)).associators) :
    MonoidalCategory (Ordinary W) :=
  monoidalCategoryOfStronglyRationalSewing F hV
    (fivePointSewingInput_of_normGrowth_pbw F hV _
      (fivePointNormGrowth_of_coefficientGrowth_pbw F hV hg) hf he) hv

end VOA.Huang.TensorCat
