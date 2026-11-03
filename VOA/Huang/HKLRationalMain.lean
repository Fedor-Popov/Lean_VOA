/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLRationalGeneration
import VOA.Huang.HKLRationalAssoc

/-!
# HKL rationality: `HKLRationalInput` reduced to two named inputs

`VOA.Huang.HKLNice.HKLRationalInput` (the extension `W` of a commutative haploid algebra `A`
with trivial twist and a Frobenius counit in `Ordinary V`, `V` nice, is `AdmissiblyRational`) is
reduced to two precisely stated inputs, each TRUE in the literature:

1. `HKLActionAssocInput` — **associativity of the `A`-action** of every ordinary `W`-module
   (`act N : A ⊠ N ⟶ N`, induced from `Y_N` by the universal property of `⊠`):
   `(μ ▷ N) ≫ act = α ≫ (A ◁ act) ≫ act`.  Huang–Kirillov–Lepowsky 2015 Thm 3.4 (the functor
   from `W`-modules to local `A`-modules), Creutzig–Kanade–McRae 2017; the module analogue of the
   proved `HKLLoc.local_extField` (same associativity isomorphism `evalAssoc_fourPoint`, run in the
   converse direction: Jacobi identity of `Y_N` ⇒ equality of the product and iterate four-point
   evaluations ⇒ equality of the two morphisms out of `(A ⊠ A) ⊠ N` by faithfulness).
   For `N = W` itself it is exactly `MonObj.mul_assoc`.
2. `HKLFrobeniusDimInput` — **`dim A ≠ 0`** in the form `c ≫ μ ≠ 0` for every Frobenius
   copairing `c` of `q`.  Since `c` is central and symmetric (`isCentral_of_frobenius`,
   `copairing_unique`), `c ≫ μ ≫ q = p ∘ β ∘ c` is the ribbon dimension of `A` computed with the
   trivial twist `θ_A = 1`; it is `Σ mult_i · S_{0i}/S_{00} > 0` for pseudo-unitary `V` (Huang:
   categorical dimensions are `S_{0i}/S_{00}`; Dong–Jiao–Xu positivity).  Kirillov–Ostrik 2002
   assume `dim A ≠ 0` explicitly (Thm 3.3).

`hklRationalInput_of_inputs : HKLActionAssocInput → HKLFrobeniusDimInput →
HKLRationalInput` — proved:
* Kirillov–Ostrik's Maschke argument (`exists_linear_retraction_of_frobenius`, pure category
  theory, `HKLRationalSeparable`) applied to the `V`-linear projection onto a `W`-submodule
  (`ordinary_complements`) gives `W`-complements in ordinary `W`-modules
  (`ordinary_weakCompletelyReducible`);
* `L₀` is semisimple on every weak `V`-module (`eigenSum_eq_top`), the cyclic `W`-submodule of an
  `L₀`-eigenvector is ordinary (`eigen_cyclic_isOrdinary`, `W` is `C₂`-cofinite), and a module
  spanned by completely reducible images is completely reducible
  (`weakCompletelyReducible_of_ordinary`, `completelyReducible_of_iSup`).

`VOA.Classification.COne.gannonRayhaun_hkl_inputs` — the forward Gannon–Rayhaun theorem
conditional on `DLNCongruenceInput`, `GaloisSymmetryNontrivialInput`, `QExpPrinciple24Away 2` and
the two inputs above.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Huang.HKLRational

open CategoryTheory MonoidalCategory Limits Module
open VOA VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.FusionUnit
  VOA.Huang.FusionProduct VOA.Huang.TensorCat.BraidRibbon VOA.Huang.HKLExt VOA.Huang.HKLNice

universe u

/-- **Input 1 (HKL 2015 Thm 3.4, CKM 2017): the `A`-action of an ordinary `W`-module is
associative.**  Same hypotheses as `HKLRationalInput`. -/
def HKLActionAssocInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱) (hV : Nice V)
    (F : FusionChoice V),
    letI := monoidalCategoryOfStronglyRational_pbw F hV.1
    letI := HexagonClose.braidedCategory_stronglyRational_pbw F hV.1
    ∀ (A : Ordinary V) [MonObj A], IsCommMonObj A → ∀ htw : (twistIso A).hom = 𝟙 A,
      finrank ℂ (𝟙_ (Ordinary V) ⟶ A) = 1 → ∀ q : A ⟶ 𝟙_ (Ordinary V), IsFrobeniusCounit A q →
      ∀ hloc hvac hpos (M : Type u) [AddCommGroup M] [Module ℂ M]
        (N : OrdVModule (extVOA F (MonObj.mul : tensorObj F A A ⟶ A)
          (MonObj.one : vacuumObject ⟶ A) (MonObj.one_mul A) (MonObj.mul_one A) htw hloc hvac
          hpos) M),
        (MonObj.mul ▷ actObj N) ≫ act N = (α_ A A (actObj N)).hom ≫ (A ◁ act N) ≫ act N

/-- **Input 2 (`dim A ≠ 0`, KO 2002 Thm 3.3's hypothesis; positivity for pseudo-unitary `V`):**
`c ≫ μ ≠ 0` for every Frobenius copairing `c` of `q`. -/
def HKLFrobeniusDimInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱) (hV : Nice V)
    (F : FusionChoice V),
    letI := monoidalCategoryOfStronglyRational_pbw F hV.1
    letI := HexagonClose.braidedCategory_stronglyRational_pbw F hV.1
    ∀ (A : Ordinary V) [MonObj A], IsCommMonObj A → (twistIso A).hom = 𝟙 A →
      finrank ℂ (𝟙_ (Ordinary V) ⟶ A) = 1 → ∀ q : A ⟶ 𝟙_ (Ordinary V),
      ∀ c : 𝟙_ (Ordinary V) ⟶ A ⊗ A, Zig₁ c (MonObj.mul ≫ q) → c ≫ MonObj.mul ≠ 0

/-- **`HKLRationalInput` from the two inputs.** -/
theorem hklRationalInput_of_inputs (h₁ : HKLActionAssocInput.{u})
    (h₂ : HKLFrobeniusDimInput.{u}) : HKLRationalInput.{u} := by
  intro 𝒱 _ _ V hV F
  letI := monoidalCategoryOfStronglyRational_pbw F hV.1
  letI := HexagonClose.braidedCategory_stronglyRational_pbw F hV.1
  intro A _ hcomm htw hhap q hfrob hloc hvac hpos M _ _ N
  have hE : VOA.Huang.LogRemovalAdmissible.eigenSum N.toWeakModule = ⊤ :=
    eigenSum_eq_top hV.1 (restrictWeak N.toWeakModule)
  exact weakCompletelyReducible_of_ordinary (extVOA_c2Cofinite hV.1) N.toWeakModule hE
    (ordinary_weakCompletelyReducible hV F A hcomm htw hhap q hfrob hloc hvac hpos
      (h₂ 𝒱 V hV F A hcomm htw hhap q) (h₁ 𝒱 V hV F A hcomm htw hhap q hfrob hloc hvac hpos))


/-- **Input 1 is proved** (`act_assoc`: four-point identity of the analytic associator +
module Jacobi identity + `assoc_series_eq`). -/
theorem hklActionAssocInput_holds : HKLActionAssocInput.{u} := by
  intro 𝒱 _ _ V hV F
  letI := monoidalCategoryOfStronglyRational_pbw F hV.1
  letI := HexagonClose.braidedCategory_stronglyRational_pbw F hV.1
  intro A _ hcomm htw hhap q hfrob hloc hvac hpos M _ _ N
  exact act_assoc N hV.1

/-- **`HKLRationalInput` from `dim A ≠ 0` alone.** -/
theorem hklRationalInput_of_dim (h₂ : HKLFrobeniusDimInput.{u}) : HKLRationalInput.{u} :=
  hklRationalInput_of_inputs hklActionAssocInput_holds h₂

end VOA.Huang.HKLRational

namespace VOA.Classification.COne

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward) with the HKL rationality input reduced to its
three named pieces.** -/
theorem gannonRayhaun_hkl_inputs
    (hC : VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u})
    (hG : VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u})
    (hQ : SSHecke.QExpPrinciple24Away 2)
    (h₁ : VOA.Huang.HKLRational.HKLActionAssocInput.{u})
    (h₂ : VOA.Huang.HKLRational.HKLFrobeniusDimInput.{u}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_hkl_rational hC hG hQ
    (VOA.Huang.HKLRational.hklRationalInput_of_inputs h₁ h₂)

/-- **Gannon–Rayhaun Theorem 3.1 (forward) with the whole HKL side reduced to
`HKLFrobeniusDimInput` (`dim A ≠ 0`).** -/
theorem gannonRayhaun_hkl_dim
    (hC : VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u})
    (hG : VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u})
    (hQ : SSHecke.QExpPrinciple24Away 2)
    (h₂ : VOA.Huang.HKLRational.HKLFrobeniusDimInput.{u}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_hkl_rational hC hG hQ (VOA.Huang.HKLRational.hklRationalInput_of_dim h₂)

end VOA.Classification.COne
