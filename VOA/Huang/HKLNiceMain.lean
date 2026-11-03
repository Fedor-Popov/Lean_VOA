/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLNicePU
import VOA.Huang.HKLLocInput

/-!
# HKL niceness reduced to rationality; Gannon–Rayhaun with HKL reduced to `HKLRationalInput`

For the extension `W` of a commutative haploid algebra `A` with trivial twist and a Frobenius
counit in `Ordinary V` (`V` nice), every clause of `Nice W` except rationality is proved:

* simple — `extVOA_isSimple` (KO rigidity via `ker_trivial_of_isFrobeniusCounit`);
* self-dual — `extVOA_selfDual` (`L₁W₁ = 0`, Li/Dong–Mason);
* `C₂`-cofinite — `extVOA_c2Cofinite` (Buhl, finite sums);
* pseudo-unitary — `extVOA_pseudoUnitary` (vacuum-like vectors, Li).

`hklNiceInput_of_rational : HKLRationalInput → HKLNiceInput`, where `HKLRationalInput` is the
single remaining clause: **`W` is rational** (every admissible `W`-module is completely
reducible; Kirillov–Ostrik 2002 Thm 3.3 + Huang–Kirillov–Lepowsky 2015 Thm 3.4 +
Creutzig–Kanade–McRae 2017: `W`-modules are local `A`-modules in the modular category `Rep V`,
semisimple because `A` is rigid with `dim A ≠ 0`).

`VOA.Classification.COne.gannonRayhaun_hkl_rational (hC hG hQ hR)` — the forward
Gannon–Rayhaun theorem conditional on `DLNCongruenceInput`, `GaloisSymmetryNontrivialInput`,
`QExpPrinciple24Away 2` and `HKLRationalInput`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false

noncomputable section

namespace VOA.Huang.HKLNice

open CategoryTheory MonoidalCategory Module
open VOA VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.FusionUnit
  VOA.Huang.FusionProduct VOA.Huang.TensorCat.BraidRibbon VOA.Huang.HKLExt

universe u

/-- **The one remaining HKL input: rationality of the extension** (KO 2002 Thm 3.3, HKL 2015
Thm 3.4, CKM 2017).  Same hypotheses as `HKLNiceInput`; conclusion: the extension is rational in
the admissible (Zhu/DLM) sense. -/
def HKLRationalInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱) (hV : Nice V)
    (F : FusionChoice V),
    letI := monoidalCategoryOfStronglyRational_pbw F hV.1
    letI := HexagonClose.braidedCategory_stronglyRational_pbw F hV.1
    ∀ (A : Ordinary V) [MonObj A], IsCommMonObj A → ∀ htw : (twistIso A).hom = 𝟙 A,
      finrank ℂ (𝟙_ (Ordinary V) ⟶ A) = 1 → ∀ q : A ⟶ 𝟙_ (Ordinary V), IsFrobeniusCounit A q →
      ∀ hloc hvac hpos,
        AdmissiblyRational (extVOA F (MonObj.mul : tensorObj F A A ⟶ A)
          (MonObj.one : vacuumObject ⟶ A) (MonObj.one_mul A) (MonObj.mul_one A) htw hloc hvac hpos)

/-- **Niceness of the extension from its rationality**: simplicity, self-duality,
`C₂`-cofiniteness and pseudo-unitarity are proved. -/
theorem hklNiceInput_of_rational (hR : HKLRationalInput.{u}) : HKLNiceInput.{u} := by
  intro 𝒱 _ _ V hV F
  letI := monoidalCategoryOfStronglyRational_pbw F hV.1
  letI := HexagonClose.braidedCategory_stronglyRational_pbw F hV.1
  intro A _ hcomm htw hhap q hfrob hloc hvac hpos
  letI := monoidalPreadditive_pbw F hV.1
  have hker : ∀ (X : Ordinary V) (f : X ⟶ A),
      tensorHom F (𝟙 A) f ≫ (MonObj.mul : tensorObj F A A ⟶ A) ≫ q = 0 → f = 0 :=
    fun X f hf => ker_trivial_of_isFrobeniusCounit hfrob f hf
  have hs := extVOA_isSimple hV hhap q hker (hl := MonObj.one_mul A) (hr := MonObj.mul_one A)
    (htw := htw) (hloc := hloc) (hvac := hvac) (hpos := hpos)
  have hsr : StronglyRational (extVOA F (MonObj.mul : tensorObj F A A ⟶ A)
      (MonObj.one : vacuumObject ⟶ A) (MonObj.one_mul A) (MonObj.mul_one A) htw hloc hvac hpos) :=
    ⟨⟨hs, extVOA_selfDual hV hhap q hker, extVOA_c2Cofinite hV.1⟩,
      hR 𝒱 V hV F A hcomm htw hhap q hfrob hloc hvac hpos⟩
  refine ⟨hsr, ?_⟩
  exact extVOA_pseudoUnitary hV hs

end VOA.Huang.HKLNice

namespace VOA.Classification.COne

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward) with HKL reduced to the rationality of the
extension** (`HKLRationalInput`). -/
theorem gannonRayhaun_hkl_rational
    (hC : VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u})
    (hG : VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u})
    (hQ : SSHecke.QExpPrinciple24Away 2) (hR : VOA.Huang.HKLNice.HKLRationalInput.{u}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_hkl_nice hC hG hQ (VOA.Huang.HKLNice.hklNiceInput_of_rational hR)

end VOA.Classification.COne
