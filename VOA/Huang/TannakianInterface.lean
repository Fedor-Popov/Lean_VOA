/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.TannakianAlgebra
import VOA.Classification.COne.Inputs

/-!
# The VOA-side inputs of `ITannakian`, and the assembly

`iTannakian_of_inputs : DeligneTannakian → HuangHKLInterface → ITannakian`.

The pure tensor-category half of Gannon–Rayhaun Props. 2.13/2.17 is proved in
`Huang/Tannakian{Muger,…,Algebra}.lean`.  This file states, at natural generality, what the VOA
side must supply, and assembles `ITannakian` from it and Deligne's theorem.

## The inputs

* `HuangRibbonRealization V D` (a `Type`, not a `Prop`): a `ℂ`-linear ribbon fusion category `C`
  (T1 classes) with simples labelled by the modular data, `lab : ι_C ≃ D.ι`, such that
  `T_i = e^{2πi h_{lab i}}` (`T_eq`), `S_{lab i, lab j} = S₀₀ · S̃_ij` or `S₀₀ · conj S̃_ij`
  (`S_eq`; either orientation convention, pair by pair), `qdim X_i = d_{lab i}` (`qdim_eq`),
  `qdim (X_i ⊗ X_j) = d d` (`qdim_tensor`), Turaev's formula at trivial twist (`symDim_eq`), and
  `lab 𝟙 = vac`.  This is the **numerical shadow of Huang's theorem**: for nice `V`, `Rep V` is a
  modular tensor category with twist `e^{2πi L₀}` whose `S̃` is the modular `S` up to `S₀₀`
  (Huang, *Rigidity and modularity of vertex tensor categories*, Commun. Contemp. Math. 10 (2008)
  871–911, and *Vertex operator algebras and the Verlinde conjecture*, PNAS 102 (2005); in the form
  GR Thm. 2.2 and (2.8) with `ε = +1`),
  with positive dimensions `d_a = S_{a0}/S_{00}` by pseudo-unitarity.  `qdim_tensor` and
  `symDim_eq` are theorems in any genuine ribbon category (monoidal pivotal structure;
  Turaev, *Quantum invariants of knots and 3-manifolds*, Ch. I) that the weak `RibbonStructure` of
  `TensorCategories` cannot derive, so they are recorded as fields.
* `HKLExtensionProperty H`: every commutative algebra `A` in `C` with `θ_A = 𝟙` and
  `dim Hom(𝟙, A) = 1` (haploid), acted on by a finite group `G` through algebra automorphisms whose
  sum `Σ_g ρ(g)` factors through the unit (`A^G = 𝟙`), yields a nice VOA `W` (carrier in the
  universe of `V`) with `c_W = c_V`, a finite `Γ ≤ Aut W` with `V ≅ W^Γ`, and
  `dim W_n = Σ_i dim Hom(A, X_i) · dim (V_{lab i})_n`.  **Sources:** Huang–Kirillov–Lepowsky,
  *Braided tensor categories and extensions of vertex operator algebras*, Commun. Math. Phys. 337
  (2015) (main theorem: VOA extensions `W ⊇ V` ↔ commutative associative algebras in `Rep V` with
  trivial twist and injective unit, as an isomorphism of categories — so algebra automorphisms of
  `A` are VOA automorphisms of `W` fixing `V` pointwise, and `W^Γ` is the extension attached to the
  invariant subalgebra `A^G = 𝟙`, i.e. `V`); Kirillov–Ostrik, Adv. Math. 171 (2002), and
  Creutzig–Kanade–McRae, arXiv:1705.05017 (`Rep W ≃ C_A^{loc}`); niceness of `W`: GR Prop. 2.7.
  (Theorem numbers inside HKL/CKM were not re-checked against the published versions here.)
* `HuangHKLInterface : Prop` — for every nice `V` with modular data `D`, **some** realization
  `H` has the extension property.

## Why Huang and HKL are one input, not two

HKL is a theorem about `Rep V` itself, not about every category with `Rep V`'s numbers.  No
Lean-checkable condition short of `Rep V` as a vertex tensor category pins `C` down: modular data
do not determine a modular category (Mignard–Schauenburg 2017), and fusion rules do not even
determine `Rep G` (`D₄` vs `Q₈`).  So "`∀` realizations `H`, HKL holds for `H`" would quantify
over fake categories and is not a published theorem; "`∃ H` realizing `D` with the HKL property"
is (take `H = Rep V`).  Stating them separately would be either false or vacuous; bundling them
is the faithful option.  `HuangRibbonInterface` (numerics only) is recorded as the numerical
form of Huang's theorem and follows from the bundle.

## Is `DLMSchurWeyl` needed?  No.

`ITannakian`'s consumer needs `V ≅ W^Γ` and the graded dimensions.  Both come out of the HKL
correspondence once `A^G = 𝟙` is checked on the regular algebra (`sum_leftTranslHom`: the
left-translation average of `Fun(G)` is `η ∘ Σ_x ev_x`); Dong–Li–Mason's Schur–Weyl duality is
the converse direction (`W^G`-modules from `W`) and is not used.  See `SchurWeylDLM.lean`.

## Universes

`C : Type w` with `Hom` in `Type v`, arbitrary; Deligne is used at the same `v, w`
(`DeligneTannakian.{v, w}` quantifies over all such categories).  Both inputs are true at every
`v, w` (a fusion category has small skeletal models).  `W` lives in the universe `u` of `V`, as
`ITannakian.{u}` requires (the HKL carrier is a direct sum of `V`-modules in `Type u`).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.Tannakian

open CategoryTheory MonoidalCategory Limits Module Complex
open VOA VOA.Classification.COne VOA.Huang.TensorCat

universe u v w

/-- **A ribbon-category realization of the modular data of `V`** — the numerical shadow of
Huang's theorem (see the module docstring for each field's source).  Labels: `fusion.simple i`
plays the role of the irreducible module `D.module (lab i)`. -/
structure HuangRibbonRealization {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (V : VertexOperatorAlgebra 𝒱) (D : VOA.Classification.COne.ModularData V) where
  C : Type w
  [cat : Category.{v} C]
  [preadditive : Preadditive C]
  [linear : Linear ℂ C]
  [monoidal : MonoidalCategory C]
  [monoidalPreadditive : MonoidalPreadditive C]
  [monoidalLinear : MonoidalLinear ℂ C]
  [rigid : RightRigidCategory C]
  [braided : BraidedCategory C]
  [kernels : HasKernels C]
  [biproducts : HasFiniteBiproducts C]
  [fusion : FusionCategory C]
  R : RibbonStructure C
  lab : fusion.ι ≃ D.ι
  lab_unit : lab fusion.unitLabel = D.vac
  T_eq : ∀ i, R.T i = cexp (2 * Real.pi * I * (D.h (lab i) : ℂ))
  S_eq : ∀ i j, D.S (lab i) (lab j) = (D.S00 : ℂ) * R.sTilde i j ∨
    D.S (lab i) (lab j) = (D.S00 : ℂ) * star (R.sTilde i j)
  qdim_eq : ∀ i, R.qdim (fusion.simple i) = (D.d (lab i) : ℂ)
  qdim_tensor : ∀ i j, R.qdim (fusion.simple i ⊗ fusion.simple j) =
    (D.d (lab i) : ℂ) * (D.d (lab j) : ℂ)
  symDim_eq : ∀ i, R.T i = 1 → symDim (fusion.simple i) = R.qdim (fusion.simple i)

attribute [instance] HuangRibbonRealization.cat HuangRibbonRealization.preadditive
  HuangRibbonRealization.linear HuangRibbonRealization.monoidal
  HuangRibbonRealization.monoidalPreadditive HuangRibbonRealization.monoidalLinear
  HuangRibbonRealization.rigid HuangRibbonRealization.braided HuangRibbonRealization.kernels
  HuangRibbonRealization.biproducts HuangRibbonRealization.fusion

namespace HuangRibbonRealization

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
  {D : VOA.Classification.COne.ModularData V}

/-- **The extension property** of a realization (Huang–Kirillov–Lepowsky 2015 + GR Prop. 2.7):
a commutative haploid algebra with trivial twist and a finite group of algebra automorphisms with
`A^G = 𝟙` gives a nice conformal extension `W` with `V ≅ W^Γ` and `W ≅ ⊕_i Hom(A, X_i) ⊗ V_{lab i}`
as graded spaces. -/
def HKLExtensionProperty (H : HuangRibbonRealization.{u, v, w} V D) : Prop :=
  ∀ (A : H.C) [MonObj A], IsCommMonObj A → (H.R.twist A).hom = 𝟙 A →
    finrank ℂ (𝟙_ H.C ⟶ A) = 1 →
    ∀ (G : Type) [Group G] [Fintype G] (ρ : G →* CategoryTheory.Aut A), (∀ g, IsMonHom (ρ g).hom) →
    (∃ q : A ⟶ 𝟙_ H.C, ∑ g, (ρ g).hom = q ≫ MonObj.one) →
    ∃ (𝒲 : Type u) (_ : AddCommGroup 𝒲) (_ : Module ℂ 𝒲) (W : VertexOperatorAlgebra 𝒲)
      (Γ : Subgroup (Aut W)), Nice W ∧ Finite Γ ∧ W.centralCharge = V.centralCharge ∧
      VOAIsomorphic V (orbifoldVOA Γ) ∧
      ∀ n : ℕ, (finrank ℂ (W.grading n) : ℝ) =
        ∑ i, (finrank ℂ (A ⟶ H.fusion.simple i) : ℝ) *
          (finrank ℂ ((D.module (H.lab i)).weight (n : ℂ)) : ℝ)

end HuangRibbonRealization

/-! ## Numerical lemmas -/

section Numerics

/-- `e^{2πi h} = 1` iff `h ∈ ℤ`, for rational `h`. -/
theorem cexp_two_pi_I_rat_eq_one_iff (h : ℚ) :
    cexp (2 * Real.pi * I * (h : ℂ)) = 1 ↔ h.den = 1 := by
  rw [Complex.exp_eq_one_iff, Rat.den_eq_one_iff]
  have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    have hq : (h : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ h2
      rw [hn]; ring
    have hq' : h = (n : ℚ) := by exact_mod_cast hq
    rw [hq']
    simp
  · intro hn
    refine ⟨h.num, ?_⟩
    have hc : (((h.num : ℚ)) : ℂ) = (h : ℂ) := congrArg _ hn
    rw [← hc]
    push_cast
    ring

/-- `|e^{2πi h}| = 1` for rational `h`. -/
theorem norm_cexp_two_pi_I_rat (h : ℚ) : ‖cexp (2 * Real.pi * I * (h : ℂ))‖ = 1 := by
  have : (2 * Real.pi * I * (h : ℂ)) = ((2 * Real.pi * (h : ℝ) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

end Numerics

namespace HuangRibbonRealization

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
  {D : VOA.Classification.COne.ModularData V}

/-- `T_i = 1` iff the module `V_{lab i}` has integer conformal weight. -/
theorem T_eq_one_iff (H : HuangRibbonRealization.{u, v, w} V D) (i : H.fusion.ι) :
    H.R.T i = 1 ↔ D.IsIntWeight (H.lab i) := by
  rw [H.T_eq]
  exact cexp_two_pi_I_rat_eq_one_iff _

/-- The pseudo-unitary data of a realization of genuine modular data. -/
def pseudoUnitaryData (H : HuangRibbonRealization.{u, v, w} V D) (hD : D.IsModularData) :
    PseudoUnitaryData H.R where
  d i := D.d (H.lab i)
  d_pos i := lt_of_lt_of_le one_pos (hD.d_ge_one _)
  qdim_eq := H.qdim_eq
  norm_T i := by rw [H.T_eq]; exact norm_cexp_two_pi_I_rat _
  qdim_tensor := H.qdim_tensor

/-- GR's factorization hypothesis on integer-weight labels gives `S̃_ij = d_i d_j` on trivial-twist
simples (either conjugation convention of Huang's `S`). -/
theorem sTilde_eq_of_factorized (H : HuangRibbonRealization.{u, v, w} V D) (hD : D.IsModularData)
    (hfact : ∀ a b, D.IsIntWeight a → D.IsIntWeight b → D.S a b = D.S00 * D.d a * D.d b)
    (i j : H.fusion.ι) (hi : H.R.T i = 1) (hj : H.R.T j = 1) :
    H.R.sTilde i j = ((H.pseudoUnitaryData hD).d i : ℂ) * ((H.pseudoUnitaryData hD).d j : ℂ) := by
  have hf := hfact _ _ ((H.T_eq_one_iff i).mp hi) ((H.T_eq_one_iff j).mp hj)
  have hS0 : (D.S00 : ℂ) ≠ 0 := by exact_mod_cast hD.S00_pos.ne'
  change H.R.sTilde i j = (D.d (H.lab i) : ℂ) * (D.d (H.lab j) : ℂ)
  rcases H.S_eq i j with h | h
  · rw [hf, mul_assoc] at h
    exact (mul_left_cancel₀ hS0 h).symm
  · rw [hf, mul_assoc] at h
    have h' := congrArg star (mul_left_cancel₀ hS0 h).symm
    rw [star_star] at h'
    rw [h']
    simp [Complex.conj_ofReal]

end HuangRibbonRealization

/-! ## The left-translation action on the regular algebra `Fun(G)` -/

section LeftTranslation

open TannakaDuality.FiniteGroup

variable {G : Type} [Group G] [Fintype G]

/-- Left translation `(λ_g f)(x) = f(g⁻¹ x)`, a `G`-map `Fun(G) ⟶ Fun(G)` (it commutes with the right
regular action). -/
def leftTranslHom (g : G) : (rightFDRep : FDRep ℂ G) ⟶ rightFDRep where
  hom := InducedCategory.homMk (ModuleCat.ofHom (LinearMap.funLeft ℂ ℂ (g⁻¹ * ·)))
  comm h := by
    ext f
    funext t
    change f (g⁻¹ * t * h) = f (g⁻¹ * (t * h))
    rw [mul_assoc]

theorem leftTranslHom_apply (g : G) (f : G → ℂ) (t : G) :
    (leftTranslHom g).hom f t = f (g⁻¹ * t) := rfl

theorem leftTranslHom_mul (g g' : G) :
    leftTranslHom (g * g') = leftTranslHom g' ≫ leftTranslHom g := by
  ext f
  funext t
  change f ((g * g')⁻¹ * t) = f (g'⁻¹ * (g⁻¹ * t))
  rw [mul_inv_rev, mul_assoc]

theorem leftTranslHom_one : leftTranslHom (1 : G) = 𝟙 _ := by
  ext f
  funext t
  change f (1⁻¹ * t) = f t
  rw [inv_one, one_mul]

/-- Left translation as an automorphism of `Fun(G)` in `Rep(G)`. -/
def leftTranslAut (g : G) : CategoryTheory.Aut (rightFDRep : FDRep ℂ G) where
  hom := leftTranslHom g
  inv := leftTranslHom g⁻¹
  hom_inv_id := by rw [← leftTranslHom_mul, inv_mul_cancel, leftTranslHom_one]
  inv_hom_id := by rw [← leftTranslHom_mul, mul_inv_cancel, leftTranslHom_one]

/-- The **left-translation action** `G →* Aut(Fun G)`. -/
def leftTransl : G →* CategoryTheory.Aut (rightFDRep : FDRep ℂ G) where
  toFun := leftTranslAut
  map_one' := by ext1; exact leftTranslHom_one
  map_mul' g g' := by ext1; exact leftTranslHom_mul g g'

/-- Left translations are **algebra automorphisms** of `Fun(G)`. -/
instance isMonHom_leftTranslHom (g : G) : IsMonHom (leftTranslHom g) where
  one_hom := by
    ext
    funext t
    rfl
  mul_hom := by
    apply Action.hom_ext
    apply ObjectProperty.hom_ext
    simp only [Action.comp_hom, Action.tensorHom_hom, ObjectProperty.FullSubcategory.comp_hom]
    ext : 1
    apply TensorProduct.ext'
    intro f f'
    rfl

/-- Summation `Fun(G) ⟶ ℂ`, `f ↦ Σ_x f(x)` (a `G`-map to the trivial representation). -/
def funSum : (rightFDRep : FDRep ℂ G) ⟶ 𝟙_ (FDRep ℂ G) where
  hom := InducedCategory.homMk (ModuleCat.ofHom
    { toFun := fun f => ∑ x, f x
      map_add' := fun f f' => by simp [Finset.sum_add_distrib]
      map_smul' := fun c f => by simp [Finset.mul_sum] })
  comm h := by
    ext f
    change ∑ x, f (x * h) = ∑ x, f x
    exact Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun _ => rfl)

/-- **The averaging idempotent of the left-translation action factors through the unit**:
`Σ_g λ_g = η ∘ (Σ_x ev_x)` — the `G`-invariant functions are the constants (`Fun(G)^G = ℂ`). -/
theorem sum_leftTranslHom :
    ∑ g : G, leftTranslHom g = funSum ≫ (MonObj.one : 𝟙_ (FDRep ℂ G) ⟶ rightFDRep) := by
  apply Action.hom_ext
  rw [Action.sum_hom]
  ext f
  funext t
  let ev : (((rightFDRep : FDRep ℂ G).V ⟶ (rightFDRep : FDRep ℂ G).V)) →+ ℂ :=
    { toFun := fun φ => φ.hom.hom f t
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ i, (leftTranslHom i).hom) = _
  rw [map_sum]
  change ∑ i, f (i⁻¹ * t) = ∑ x, f x
  exact Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight t)) _ _ (fun _ => rfl)

end LeftTranslation

/-! ## The interface and the assembly -/

/-- **The Huang–HKL interface**: every nice `V` with modular data `D` has a ribbon realization
of `D` (Huang 2005/2008) on which HKL's extension theorem holds (HKL 2015, KO 2002, CKM, GR
Prop. 2.7).  One input, not two: see the module docstring. -/
def HuangHKLInterface : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    ∀ D : VOA.Classification.COne.ModularData V, D.IsModularData →
      ∃ H : HuangRibbonRealization.{u, v, w} V D, H.HKLExtensionProperty

/-- **Huang's theorem, numerical shadow only**: every nice `V` with modular
data `D` has a ribbon realization of `D`.  Implied by `HuangHKLInterface`. -/
def HuangRibbonInterface : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    ∀ D : VOA.Classification.COne.ModularData V, D.IsModularData →
      Nonempty (HuangRibbonRealization.{u, v, w} V D)

theorem huangRibbonInterface_of_huangHKL (h : HuangHKLInterface.{u, v, w}) :
    HuangRibbonInterface.{u, v, w} := fun 𝒱 _ _ V hV D hD =>
  let ⟨H, _⟩ := h 𝒱 V hV D hD; ⟨H⟩

section Assembly

variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [RightRigidCategory C] [BraidedCategory C]
  [HasKernels C] [HasFiniteBiproducts C] [F : FusionCategory C]

/-- An object of trivial twist has no morphisms to a simple of nontrivial twist. -/
theorem hom_simple_eq_zero_of_twist (R : RibbonStructure C) {A : C} (hA : (R.twist A).hom = 𝟙 A)
    (i : F.ι) (hi : R.T i ≠ 1) (f : A ⟶ F.simple i) : f = 0 := by
  have h := R.twist_naturality f
  rw [hA, Category.id_comp, ← R.T_spec, Linear.comp_smul, Category.comp_id] at h
  have h2 : (R.T i - 1) • f = 0 := by rw [sub_smul, h, one_smul, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hi)

end Assembly

/-- **`ITannakian` from Deligne and the Huang–HKL interface.**  The Müger/Tannakian part
(`tannakian_dims_of_factorized`) gives `Rep(V)_{h∈ℤ} ≃ Rep(G)`; the regular algebra
`A = Φ⁻¹(Fun G)` is commutative, haploid, of trivial twist, with `dim Hom(A, X_i) = d_i` on
integer-weight simples and `0` otherwise, and `G` acts on it by left translations with
`A^G = 𝟙`; HKL then produces `W`. -/
theorem iTannakian_of_inputs (hDel : DeligneTannakian.{v, w})
    (hHK : HuangHKLInterface.{u, v, w}) : ITannakian.{u} := by
  intro 𝒱 _ _ V hV D hD hfact
  obtain ⟨H, hHKL⟩ := hHK 𝒱 V hV D hD
  set U := H.pseudoUnitaryData hD
  have hS := H.sTilde_eq_of_factorized hD hfact
  letI := isMonoidal_trivialTwist_of_factorized U hS
  letI := symmetricTrivialTwist_of_factorized U hS
  obtain ⟨G, hG, hGf, Φ, ⟨hbr⟩, hlin, heq, hdim⟩ := tannakian_dims_of_factorized hDel U hS H.symDim_eq
  letI := hbr
  let e := Φ.asEquivalence
  letI : e.functor.Braided := hbr
  letI : e.inverse.Braided := Equivalence.inverseBraided e
  let Fun : FDRep ℂ G := TannakaDuality.FiniteGroup.rightFDRep
  haveI : HasBinaryBiproducts (TT H.R) := hasBinaryBiproducts_of_finite_biproducts _
  haveI : Φ.Additive := Functor.additive_of_preserves_binary_products Φ
  haveI : e.functor.Additive := (inferInstance : Φ.Additive)
  let Ψ : FDRep ℂ G ⥤ H.C := e.inverse ⋙ (trivialTwist H.R).ι
  haveI : Ψ.Additive := inferInstanceAs (e.inverse ⋙ (trivialTwist H.R).ι).Additive
  letI : MonObj (Ψ.obj Fun) := Functor.monObjObj Fun
  have hcomm : IsCommMonObj (Ψ.obj Fun) := Functor.isCommMonObj_obj
  have htw : (H.R.twist (Ψ.obj Fun)).hom = 𝟙 _ := (e.inverse.obj Fun).2
  -- haploid
  have hhap : finrank ℂ (𝟙_ H.C ⟶ Ψ.obj Fun) = 1 := by
    have h1 : finrank ℂ (𝟙_ (TT H.R) ⟶ e.inverse.obj Fun) = 1 := by
      rw [(homLinearEquivOfFullyFaithful Φ _ _).finrank_eq]
      exact (Linear.homCongr ℂ (Functor.Monoidal.εIso Φ).symm (e.counitIso.app Fun)).finrank_eq.trans
        VOA.Huang.Tannakian.finrank_hom_unit_fun
    rw [← h1, (homLinearEquivOfFullyFaithful (trivialTwist H.R).ι _ _).finrank_eq]
    rfl
  -- the group action
  let ρ : G →* CategoryTheory.Aut (Ψ.obj Fun) := (Ψ.mapAut Fun).comp leftTransl
  have hρ : ∀ g, IsMonHom (ρ g).hom := fun g => by
    change IsMonHom (Ψ.map (leftTranslHom g))
    infer_instance
  have havg : ∃ q : Ψ.obj Fun ⟶ 𝟙_ H.C, ∑ g, (ρ g).hom = q ≫ MonObj.one := by
    refine ⟨Ψ.map funSum ≫ (Functor.Monoidal.εIso Ψ).inv, ?_⟩
    change ∑ g, Ψ.map (leftTranslHom g) = _
    rw [← Functor.map_sum, sum_leftTranslHom, Functor.map_comp]
    change _ = (Ψ.map funSum ≫ (Functor.Monoidal.εIso Ψ).inv) ≫ (Functor.LaxMonoidal.ε Ψ ≫ Ψ.map MonObj.one)
    simp
  obtain ⟨𝒲, i1, i2, W, Γ, hW, hΓ, hc, hiso, hdW⟩ := hHKL (Ψ.obj Fun) hcomm htw hhap G ρ hρ havg
  refine ⟨𝒲, i1, i2, W, Γ, hW, hΓ, hc, hiso, fun n => ?_⟩
  rw [hdW n]
  have hmult : ∀ i, (finrank ℂ (Ψ.obj Fun ⟶ H.fusion.simple i) : ℝ) =
      if D.IsIntWeight (H.lab i) then D.d (H.lab i) else 0 := by
    intro i
    split_ifs with hint
    · have hi : H.R.T i = 1 := (H.T_eq_one_iff i).mpr hint
      have h0 : finrank ℂ (Ψ.obj Fun ⟶ H.fusion.simple i) =
          finrank ℂ (e.inverse.obj Fun ⟶ ttSimple H.R ⟨i, hi⟩) :=
        ((homLinearEquivOfFullyFaithful (trivialTwist H.R).ι (e.inverse.obj Fun)
          (ttSimple H.R ⟨i, hi⟩)).finrank_eq).symm
      have hC : (finrank ℂ (e.inverse.obj Fun ⟶ ttSimple H.R ⟨i, hi⟩) : ℂ) = U.d i := by
        rw [(homLinearEquivOfFullyFaithful Φ _ _).finrank_eq]
        have h := (Linear.homCongr ℂ (e.counitIso.app Fun)
          (Iso.refl (Φ.obj (ttSimple H.R ⟨i, hi⟩)))).finrank_eq
        change _ = finrank ℂ (Fun ⟶ Φ.obj (ttSimple H.R ⟨i, hi⟩)) at h
        rw [VOA.Huang.Tannakian.finrank_hom_rightFDRep] at h
        change (finrank ℂ ((e.inverse ⋙ e.functor).obj Fun ⟶ Φ.obj (ttSimple H.R ⟨i, hi⟩)) : ℂ) = _
        rw [h, (hdim i hi).1]
      rw [h0]
      exact_mod_cast hC
    · have hi : H.R.T i ≠ 1 := fun h => hint ((H.T_eq_one_iff i).mp h)
      haveI : Subsingleton (Ψ.obj Fun ⟶ H.fusion.simple i) :=
        ⟨fun f g => by
          rw [hom_simple_eq_zero_of_twist H.R htw i hi f, hom_simple_eq_zero_of_twist H.R htw i hi g]⟩
      rw [finrank_zero_of_subsingleton]
      simp
  simp_rw [hmult, ite_mul, zero_mul]
  rw [VOA.Classification.COne.ModularData.intLabels, Finset.sum_filter]
  exact Fintype.sum_equiv H.lab _ _ (fun _ => rfl)

end VOA.Huang.Tannakian
