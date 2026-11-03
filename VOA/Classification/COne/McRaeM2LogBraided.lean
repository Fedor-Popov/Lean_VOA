import VOA.Classification.COne.McRaeM2LogBraidedHexagon

/-! # The logarithmic braided tensor category of a C₂-cofinite VOA

The finite logarithmic modules of a `C₂`-cofinite VOA, with the genuine logarithmic
tensor product, the proved associator and unitors (`logarithmicMonoidalCategory`),
and the braiding induced by HLZ's skew-symmetry `Ω₀` (`braidingIso`), form a Mathlib
`BraidedCategory` (`logarithmicBraidedCategory`). Naturality is
`swapIso_naturality`; the forward hexagon is `hexagon_weak` for `r = 0`; the reverse
hexagon is the forward hexagon for the reverse braiding `Ω₋₁`, inverted. The only
hypothesis is `C2Cofinite W`. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.LogTensor.LogModuleCat
open CategoryTheory MonoidalCategory VOA.C2Rigid.LocalInjective
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

-- Actual nested categorical tensor types require a larger elaboration budget.
set_option maxHeartbeats 8000000 in
/-- The hexagon for the actual swap isomorphisms, for `r = 0` and `r = -1`. -/
theorem swapIso_hexagon (r : ℤ) (hr : r = 0 ∨ r = -1) (X Y Z : LogModuleCat W) :
    (associatorIso hC2 X Y Z).hom ≫ (swapIso hC2 X (tensorObject hC2 Y Z) r).hom ≫
        (associatorIso hC2 Y Z X).hom =
      tensorMorphism hC2 (swapIso hC2 X Y r).hom (𝟙 Z) ≫ (associatorIso hC2 Y X Z).hom ≫
        tensorMorphism hC2 (𝟙 Y) (swapIso hC2 X Z r).hom := by
  apply hom_ext
  intro q
  exact congrArg (fun F => F q) (hexagon_weak hC2 X.act Y.act Z.act X.finiteGeneration
    Y.finiteGeneration Z.finiteGeneration r hr)

-- Actual nested categorical tensor types require a larger elaboration budget.
set_option maxHeartbeats 8000000 in
/-- **The first hexagon** for the logarithmic braiding. -/
theorem hexagon_forward (X Y Z : LogModuleCat W) :
    letI := logarithmicMonoidalCategory hC2
    (α_ X Y Z).hom ≫ (braidingIso hC2 X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
      ((braidingIso hC2 X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (braidingIso hC2 X Z).hom) :=
  swapIso_hexagon hC2 0 (Or.inl rfl) X Y Z

-- Actual nested categorical tensor types require a larger elaboration budget.
set_option maxHeartbeats 8000000 in
/-- **The second hexagon**: the first hexagon for the reverse braiding `Ω₋₁`,
inverted. -/
theorem hexagon_reverse (X Y Z : LogModuleCat W) :
    letI := logarithmicMonoidalCategory hC2
    (α_ X Y Z).inv ≫ (braidingIso hC2 (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      (X ◁ (braidingIso hC2 Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braidingIso hC2 X Z).hom ▷ Y) := by
  letI := logarithmicMonoidalCategory hC2
  have h := swapIso_hexagon hC2 (-0-1) (Or.inr (by norm_num)) Z X Y
  have hI : (α_ Z X Y ≪≫ (braidingIso hC2 (X ⊗ Y) Z).symm ≪≫ α_ X Y Z) =
      (whiskerRightIso (braidingIso hC2 X Z).symm Y ≪≫ α_ X Z Y ≪≫
        whiskerLeftIso X (braidingIso hC2 Y Z).symm) := Iso.ext h
  have hinv := congrArg Iso.inv hI
  simp only [Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, whiskerRightIso_inv,
    Category.assoc] at hinv
  exact hinv

/-- **The logarithmic braided tensor category** of finite logarithmic modules of
a `C₂`-cofinite VOA (Huang–Lepowsky–Zhang): the genuine logarithmic tensor product, the
proved associator and unitors, and the braiding induced by skew-symmetry `Ω₀`, with
both hexagons proved. -/
abbrev logarithmicBraidedCategory :
    @BraidedCategory (LogModuleCat W) _ (logarithmicMonoidalCategory hC2) :=
  letI := logarithmicMonoidalCategory hC2
  { braiding := braidingIso hC2
    braiding_naturality_right := fun X {_ _} f => swapIso_naturality hC2 (𝟙 X) f 0
    braiding_naturality_left := fun {_ _} f Z => swapIso_naturality hC2 f (𝟙 Z) 0
    hexagon_forward := hexagon_forward hC2
    hexagon_reverse := hexagon_reverse hC2 }

/-- The braided structure uses the genuine logarithmic swap `Ω₀`. -/
theorem logarithmicBraidedCategory_braiding (X Y : LogModuleCat W) :
    @BraidedCategory.braiding _ _ (logarithmicMonoidalCategory hC2)
      (logarithmicBraidedCategory hC2) X Y = swapIso hC2 X Y 0 := rfl

/-- Existence of the logarithmic braided structure for every C₂-cofinite VOA. -/
theorem nonempty_logarithmicBraidedCategory (hC2 : C2Cofinite W) :
    Nonempty (@BraidedCategory (LogModuleCat W) _ (logarithmicMonoidalCategory hC2)) :=
  ⟨logarithmicBraidedCategory hC2⟩

end VOA.LogTensor.LogModuleCat
