import VOA.Huang.BraidRibbonHexagon
import VOA.Huang.TannakianInterface

set_option linter.style.longLine false

/-! # What `HuangRibbonRealization` needs, field by field, and the split of `HuangHKLInterface`

## Field map of `HuangRibbonRealization V D` (TannakianInterface.lean), for `C = Rep V`

| field | status for `Ordinary V` with `F`, `hV : StronglyRational V` |
|---|---|
| `C`, `cat` | the consumer uses `HuangHKLInterface.{u, 0, 0}`: `C : Type`, `Hom : Type`.  `Ordinary V : Type (u+1)` with `Hom : Type u`, so a **small skeletal model** is required (semisimple, finitely many simples, finite-dimensional `Hom`s: essentially small and locally small, so it exists; the transport of all structure is plumbing, not done here) |
| `preadditive`, `linear` | proved on `Ordinary V` (`TensorCatOrdinary`) |
| `monoidal` | proved: `monoidalCategoryOfStronglyRational_pbw F hV` |
| `monoidalPreadditive`, `monoidalLinear` | proved: `monoidalPreadditive_pbw`, `monoidalLinear_pbw` (from `tensorHom_add_*`, `tensorHom_smul_*`) |
| `braided` | proved modulo the hexagon: `braidedCategoryOfStronglyRational_pbw F hV : HexagonInput F → BraidedCategory`; naturality, inverse, monodromy, unit compatibility proved (`BraidRibbonBraiding`); `HexagonInput F` ⇔ the forward hexagons (`analyticHexagon_iff`) — OPEN, genus zero (Huang's hexagon theorem) |
| `rigid` | OPEN: Huang 2008 rigidity — uses the genus-one/Verlinde theory (Moore–Seiberg via modular invariance) |
| `kernels`, `biproducts` | not constructed on `Ordinary V` (kernels: submodules of ordinary modules are ordinary; biproducts: direct sums) — routine, not done |
| `fusion` | simples = `D.module a` (`IsModularData.irred/exhaust/distinct`); semisimplicity from strong rationality (library: `FusionProductSemisimple`, finite targets); not packaged |
| `R.twist`, `twist_naturality`, `balance` | proved: `twistIso`, `twist_naturality`, `twist_balance` (`BraidRibbonTwist`) |
| `R.piv`, `twist_dual` | OPEN: need duals (rigidity); `twist_dual` is the contragredient-weight statement once duals are contragredients |
| `T_eq` | proved in substance: `twistIso_module_eq` — on `D.module a`, `θ = e^{2πi h_a} • 𝟙` |
| `S_eq`, `qdim_eq`, `qdim_tensor` | OPEN: Huang 2008 (`S̃ = S/S₀₀` up to conjugation; `qdim = S_{a0}/S_{00}`) — genus-one/Verlinde-dependent |
| `symDim_eq` | OPEN: Turaev's formula, a theorem of genuine ribbon categories (not derivable from the library's weak `RibbonStructure`) |
| `lab`, `lab_unit` | from `IsModularData` (`vac_iso`) once the simples are indexed |

## The split of `HuangHKLInterface`

`HuangHKLInterface` bundles Huang and HKL because "HKL for every realization of `D`" quantifies
over fake categories (module docstring of `TannakianInterface`).  With the braiding and twist of
`Rep V` constructed, a realization can be **pinned to `Rep V`** (`IsRepRealization`): a
`ℂ`-linear monoidal equivalence `E : H.C ⥤ Ordinary V` (for the proved monoidal structure) that
carries `H`'s braiding to `braiding F`, `H`'s twist to `twistIso`, and `H.fusion.simple i` to
`D.module (H.lab i)`.  Then

* `HuangRepInput` — every nice `V` with modular data has a realization pinned to `Rep V`
  (Huang 2005/2008 + a small model), and
* `HKLRepInput` — **every** realization pinned to `Rep V` has the HKL extension property
  (HKL 2015, transported along `E`, which preserves commutative algebras, twists, `Hom`
  dimensions, and the simple ↔ module dictionary used in the graded-dimension formula; niceness
  of the extension: GR Prop. 2.7)

are separate statements, each TRUE, and `huangHKLInterface_of_rep : HuangRepInput →
HKLRepInput → HuangHKLInterface.{u, 0, 0}`.  `HKLRepInput` is not vacuous provided
`HuangRepInput` holds (it then applies to an actual realization).
-/

noncomputable section

namespace VOA.Huang.TensorCat.BraidRibbon

open CategoryTheory MonoidalCategory Complex
open VOA VOA.Classification.COne VOA.Huang.FusionUnit VOA.Huang.FusionProduct
open VOA.Huang.Tannakian

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}

/-! ## `monoidalPreadditive`, `monoidalLinear` -/

section Linear

variable (F : FusionChoice V) (hV : StronglyRational V)

theorem tensorHom_zero_right {X X' Y Y' : Ordinary V} (f : X ⟶ X') :
    tensorHom F f (0 : Y ⟶ Y') = 0 := by
  have h := tensorHom_smul_right F (0 : ℂ) f (0 : Y ⟶ Y')
  rwa [zero_smul, zero_smul] at h

theorem tensorHom_zero_left {X X' Y Y' : Ordinary V} (g : Y ⟶ Y') :
    tensorHom F (0 : X ⟶ X') g = 0 := by
  have h := tensorHom_smul_left F (0 : ℂ) (0 : X ⟶ X') g
  rwa [zero_smul, zero_smul] at h

/-- The proved monoidal structure is preadditive (`HuangRibbonRealization.monoidalPreadditive`). -/
theorem monoidalPreadditive_pbw :
    @MonoidalPreadditive (Ordinary V) _ _ (monoidalCategoryOfStronglyRational_pbw F hV) :=
  letI := monoidalCategoryOfStronglyRational_pbw F hV
  { whiskerLeft_zero := tensorHom_zero_right F _
    zero_whiskerRight := tensorHom_zero_left F _
    whiskerLeft_add := fun f g => tensorHom_add_right F _ f g
    add_whiskerRight := fun f g => tensorHom_add_left F f g _ }

/-- The proved monoidal structure is `ℂ`-linear (`HuangRibbonRealization.monoidalLinear`). -/
theorem monoidalLinear_pbw :
    letI := monoidalCategoryOfStronglyRational_pbw F hV
    letI := monoidalPreadditive_pbw F hV
    MonoidalLinear ℂ (Ordinary V) :=
  letI := monoidalCategoryOfStronglyRational_pbw F hV
  letI := monoidalPreadditive_pbw F hV
  { whiskerLeft_smul := fun _ _ _ r f => tensorHom_smul_right F r _ f
    smul_whiskerRight := fun r _ _ f _ => tensorHom_smul_left F r f _ }

end Linear

/-! ## `T_eq` on the actual modules -/

/-- If every weight of `X` lies in `h + ℕ`, the twist of `X` is the scalar `e^{2πih}`. -/
theorem twistIso_eq_smul_of_weights (X : Ordinary V) (h : ℂ)
    (hw : ∀ α, X.isMod.weight α ≠ ⊥ → ∃ n : ℕ, α = h + n) :
    (twistIso X).hom = tw h • 𝟙 X := by
  apply Subtype.ext
  refine linearMap_ext_homog X.isMod _ _ fun α x hx => ?_
  change (twistIso X).hom.val x = tw h • x
  rw [twistIso_hom_of_mem X hx]
  by_cases h0 : x = 0
  · rw [h0, smul_zero, smul_zero]
  · have hne : X.isMod.weight α ≠ ⊥ := fun hb => h0 (by
      rw [hb] at hx; exact (Submodule.mem_bot ℂ).mp hx)
    obtain ⟨n, rfl⟩ := hw α hne
    rw [show h + (n : ℂ) = h + ((n : ℤ) : ℂ) by push_cast; rfl, tw_add_int]

/-- **`T_eq` for the actual modules**: on `D.module a` the twist `θ = e^{2πi L(0)}` is the
scalar `e^{2πi h_a}`, the value `HuangRibbonRealization.T_eq` requires. -/
theorem twistIso_module_eq (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData) (a : D.ι) :
    (twistIso (Ordinary.of (D.module a))).hom =
      cexp (2 * Real.pi * I * (D.h a : ℂ)) • 𝟙 (Ordinary.of (D.module a)) :=
  twistIso_eq_smul_of_weights _ _ (hD.weight_support a)

/-! ## Realizations pinned to `Rep V` -/

/-- **A realization pinned to `Rep V`**: a `ℂ`-linear monoidal equivalence from `H.C` to the
proved monoidal category of ordinary `V`-modules (for some choice of fusion products), carrying
`H`'s braiding to the skew-symmetry braiding `braiding F`, `H`'s twist to `θ = e^{2πiL(0)}`, and
each simple `H.fusion.simple i` to the module `D.module (H.lab i)`. -/
def IsRepRealization {D : VOA.Classification.COne.ModularData V} (H : HuangRibbonRealization.{u, 0, 0} V D) : Prop :=
  ∃ (F : FusionChoice V) (hV : StronglyRational V),
    letI := monoidalCategoryOfStronglyRational_pbw F hV
    ∃ (E : H.C ⥤ Ordinary V) (_ : E.IsEquivalence) (_ : E.Additive) (_ : E.Linear ℂ)
      (_ : E.Monoidal),
      (∀ X Y : H.C, Functor.LaxMonoidal.μ E X Y ≫ E.map (β_ X Y).hom =
        (braiding F (E.obj X) (E.obj Y)).hom ≫ Functor.LaxMonoidal.μ E Y X) ∧
      (∀ X : H.C, E.map (H.R.twist X).hom = (twistIso (E.obj X)).hom) ∧
      (∀ i, Nonempty (E.obj (H.fusion.simple i) ≅ Ordinary.of (D.module (H.lab i))))

/-- **Huang's theorem, pinned to `Rep V`** (Huang 2005, 2008; with a small skeletal model):
every nice `V` with modular data `D` has a ribbon realization of `D` that is `Rep V`. -/
def HuangRepInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    ∀ D : VOA.Classification.COne.ModularData V, D.IsModularData →
      ∃ H : HuangRibbonRealization.{u, 0, 0} V D, IsRepRealization H

/-- **HKL on `Rep V`** (Huang–Kirillov–Lepowsky 2015, Kirillov–Ostrik 2002, CKM; GR Prop. 2.7):
every realization pinned to `Rep V` has the extension property. -/
def HKLRepInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    ∀ D : VOA.Classification.COne.ModularData V, D.IsModularData →
      ∀ H : HuangRibbonRealization.{u, 0, 0} V D, IsRepRealization H → H.HKLExtensionProperty

/-- **The bundled interface splits**: Huang (pinned to `Rep V`) and HKL (for every
realization pinned to `Rep V`) give `HuangHKLInterface`. -/
theorem huangHKLInterface_of_rep (h1 : HuangRepInput.{u}) (h2 : HKLRepInput.{u}) :
    HuangHKLInterface.{u, 0, 0} := by
  intro 𝒱 _ _ V hV D hD
  obtain ⟨H, hH⟩ := h1 𝒱 V hV D hD
  exact ⟨H, h2 𝒱 V hV D hD H hH⟩

/-- The numerical shadow follows from the pinned Huang input alone. -/
theorem huangRibbonInterface_of_rep (h1 : HuangRepInput.{u}) :
    HuangRibbonInterface.{u, 0, 0} := by
  intro 𝒱 _ _ V hV D hD
  obtain ⟨H, _⟩ := h1 𝒱 V hV D hD
  exact ⟨H⟩

end VOA.Huang.TensorCat.BraidRibbon
