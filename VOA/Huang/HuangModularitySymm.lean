/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HuangModularityAssembly
import VOA.Huang.VerlindeRhoComplete
import VOA.Huang.VerlindeVacuumFusion

/-!
# The modular `S`-matrix of a nice VOA is symmetric (Huang 2008, Theorem 5.6)

* `symm_of_eigen_dual` (finite linear algebra) — if the columns of `S` are common eigenvectors of
  the fusion matrices (unit row `N_{a v0}^y = δ_ay`), the vacuum row and column agree,
  `S² = C` is the permutation matrix of an involution `σ`, and `N_{ax}^y = N_{a,σy}^{σx}`,
  then `S` is symmetric (Huang's argument: the rows of `S⁻¹ = S C` are left eigenvectors;
  duality of `N` turns them into right eigenvectors; evaluate at the vacuum).
* `tensorRightHomLinearEquiv` — Mathlib's `tensorRightHomEquiv` is `ℂ`-linear.
* `fus_dual` — `N_{ax}^y = N_{y,σx}^a` for the fusion rules of a nice VOA, proved in the rigid
  canonical model (`huangRigidityInput_holds`): `Hom(X_a ⊗ X_x, X_y) ≅ Hom(X_a, X_y ⊗ X_xᘁ)`,
  and `X_xᘁ ≅ X_{σx}` because
  `dim Hom(X_c, X_xᘁ) = dim Hom(X_c ⊗ X_x, 𝟙) = N_{cx}^{vac} = δ_{c,σx}`.
* `sSymmetricInput_holds : SSymmetricInput`.
* `huangModularityInput_of_qdimInput : HuangQDimInput → HuangModularityInput`,
  `huangRepInput_of_qdimInput : HuangQDimInput → HuangRepInput`, and
  `huangModularityInput_iff_qdim : HuangModularityInput ↔ HuangQDimInput`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HuangModularity

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Module VOA
  VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.TensorCat.BraidRibbon
  VOA.Huang.TensorCat.RepPackaging VOA.Huang.Tannakian VOA.Huang.HuangRigid
  VOA.Huang.FusionProduct VOA.Huang.SPinning VOA.Huang.VerlindeEigen VOA.Huang.VerlindeFusion

universe u

/-! ## §1 Linear algebra -/

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ι → ι → ℕ} {S : ι → ι → ℂ}
  {v0 : ι}

/-- **Symmetry of `S` from the eigenvector property, `S² = C` and duality of `N`.** -/
theorem symm_of_eigen_dual (σ : ι → ι) (hunit : ∀ a y, N a v0 y = if y = a then 1 else 0)
    (hE : FusionEigen N S) (hvac : ∀ z, S z v0 = S v0 z) (hσ : ∀ x, σ (σ x) = x)
    (hdualN : ∀ a x y, N a x y = N a (σ y) (σ x))
    (hSC : Matrix.of S * Matrix.of S = Matrix.of fun x y => if y = σ x then (1 : ℂ) else 0)
    (a b : ι) : S a b = S b a := by
  set C : Matrix ι ι ℂ := Matrix.of fun x y => if y = σ x then (1 : ℂ) else 0 with hC
  have hiff : ∀ x u, (x = σ u) ↔ (u = σ x) := fun x u =>
    ⟨fun h => by rw [h, hσ], fun h => by rw [h, hσ]⟩
  have hCC : C * C = 1 := by
    ext x z
    simp only [hC, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hσ]
    by_cases h : x = z
    · subst h; simp
    · simp [h, Ne.symm h]
  have hcomm : Matrix.of S * C = C * Matrix.of S := by
    rw [← hSC, Matrix.mul_assoc]
  set T : Matrix ι ι ℂ := Matrix.of S * C with hT
  have hTS : T * Matrix.of S = 1 := by
    rw [hT, Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hSC, hCC]
  have hST : Matrix.of S * T = 1 := by
    rw [hT, ← Matrix.mul_assoc, hSC, hCC]
  have hTent : ∀ z x, T z x = S z (σ x) := by
    intro z x
    simp only [hT, hC, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
    simp_rw [hiff x]
    simp
  have h := inv_eigen hE T hTS hST a b (σ v0)
  simp only [hTent, hσ] at h
  have hN : ∀ x, N a x (σ v0) = if σ x = a then 1 else 0 := by
    intro x
    rw [hdualN a x (σ v0), hσ, hunit]
  simp only [hN, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero] at h
  rw [Finset.sum_eq_single (σ a)] at h
  · rw [hσ, if_pos rfl] at h
    rw [h, hvac b, ← eq_eigval_mul hunit hE a b]
  · intro x _ hx
    rw [if_neg]
    intro hxa
    exact hx (by rw [← hxa, hσ])
  · intro hx; exact absurd (Finset.mem_univ _) hx

end Algebra

/-! ## §2 `tensorRightHomEquiv` is linear -/

section Linear

variable {C : Type*} [Category C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- `Hom(X ⊗ Y, Z) ≃ₗ Hom(X, Z ⊗ Y')` for an exact pairing `(Y, Y')`. -/
def tensorRightHomLinearEquiv (X Y Y' Z : C) [ExactPairing Y Y'] :
    (X ⊗ Y ⟶ Z) ≃ₗ[ℂ] (X ⟶ Z ⊗ Y') :=
  { tensorRightHomEquiv X Y Y' Z with
    map_add' := fun f g => by
      simp [tensorRightHomEquiv, MonoidalPreadditive.add_whiskerRight]
    map_smul' := fun c f => by
      simp [tensorRightHomEquiv] }

end Linear

/-! ## §3 Duality of the fusion rules -/

section Dual

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- A biproduct over `Fin 1` is its summand. -/
def biproductFinOneIso {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
    (g : Fin 1 → C) : (⨁ g) ≅ g 0 where
  hom := biproduct.π g 0
  inv := biproduct.ι g 0
  hom_inv_id := by
    rw [← biproduct.total, Fin.sum_univ_one]
  inv_hom_id := biproduct.ι_π_self g 0

/-- **Duality of the fusion rules**: `N_{ax}^y = N_{y,σx}^a`, where `σ` is the contragredient
involution read off the vacuum fusion rules (`N_{bx}^{vac} = δ_{x,σb}`). -/
theorem fus_dual (hW : Nice W) (D : VOA.Classification.COne.ModularData W)
    (hD : D.IsModularData) (σ : D.ι → D.ι) (hσ : ∀ x, σ (σ x) = x)
    (hvac : ∀ b x, fus D b x D.vac = if x = σ b then 1 else 0) (a x y : D.ι) :
    fus D a x y = fus D y (σ x) a := by
  classical
  obtain ⟨r⟩ := huangRigidityInput_holds V W hW D hD
  letI := r
  set M := canonicalModel hW D hD
  letI F := M.fusion D hD
  -- multiplicities of the dual `X_xᘁ`
  have hmult : ∀ c : D.ι, mult (F.simple x)ᘁ c = if c = σ x then 1 else 0 := by
    intro c
    let e1 : (F.simple c ⟶ (F.simple x)ᘁ) ≃ₗ[ℂ] (F.simple c ⟶ 𝟙_ M.C ⊗ (F.simple x)ᘁ) :=
      Linear.homCongr ℂ (Iso.refl _) (λ_ _).symm
    let e2 := (tensorRightHomLinearEquiv (F.simple c) (F.simple x) (F.simple x)ᘁ (𝟙_ M.C)).symm
    let e3 : (F.simple c ⊗ F.simple x ⟶ 𝟙_ M.C) ≃ₗ[ℂ] (F.simple c ⊗ F.simple x ⟶ F.simple D.vac) :=
      Linear.homCongr ℂ (Iso.refl _) F.unitIso.symm
    have h1 : mult (F.simple x)ᘁ c = finrank ℂ (F.simple c ⊗ F.simple x ⟶ F.simple D.vac) := by
      rw [mult, e1.finrank_eq, e2.finrank_eq, e3.finrank_eq]
    rw [h1, ← mult_eq_finrank_hom_to]
    have h2 := fusionN_eq hW M D hD c x D.vac
    change mult (F.simple c ⊗ F.simple x) D.vac = _ at h2
    rw [h2, hvac]
    by_cases h : c = σ x
    · rw [if_pos h, if_pos (by rw [h, hσ])]
    · rw [if_neg h, if_neg (fun h' => h (by rw [h', hσ]))]
  -- the dual of `X_x` is `X_{σx}`
  have hdual : Nonempty ((F.simple x)ᘁ ≅ F.simple (σ x)) := by
    obtain ⟨n, f, ⟨e⟩⟩ := F.semisimple (F.simple x)ᘁ
    have hcard : ∀ c, (Finset.univ.filter fun k => f k = c).card = if c = σ x then 1 else 0 :=
      fun c => by rw [← mult_eq_card f e c, hmult]
    have hn : n = 1 := by
      have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
        (t := (Finset.univ : Finset F.ι)) (f := f) (fun _ _ => Finset.mem_univ _)
      rw [Finset.card_univ, Fintype.card_fin] at this
      rw [this]
      simp_rw [hcard]
      simp
    subst hn
    have hf0 : f 0 = σ x := by
      have h1 := hcard (σ x)
      rw [if_pos rfl] at h1
      obtain ⟨k, hk⟩ := Finset.card_pos.mp (by rw [h1]; exact Nat.one_pos)
      have hk0 : k = 0 := Subsingleton.elim _ _
      rw [← hk0]
      exact (Finset.mem_filter.mp hk).2
    exact ⟨e ≪≫ biproductFinOneIso (fun k => F.simple (f k)) ≪≫ eqToIso (congrArg F.simple hf0)⟩
  obtain ⟨ed⟩ := hdual
  -- `N_{ax}^y = dim Hom(X_a ⊗ X_x, X_y) = dim Hom(X_a, X_y ⊗ X_{σx}) = N_{y,σx}^a`
  have h3 := fusionN_eq hW M D hD a x y
  change mult (F.simple a ⊗ F.simple x) y = _ at h3
  rw [mult_eq_finrank_hom_to] at h3
  have h4 := fusionN_eq hW M D hD y (σ x) a
  change mult (F.simple y ⊗ F.simple (σ x)) a = _ at h4
  rw [← h3, ← h4, mult, (tensorRightHomLinearEquiv (F.simple a) (F.simple x) (F.simple x)ᘁ
    (F.simple y)).finrank_eq]
  exact (Linear.homCongr ℂ (Iso.refl _) (whiskerLeftIso (F.simple y) ed)).finrank_eq

/-- The charge conjugation of `D` (from `ρ(−1) = C` and the vacuum fusion rules). -/
theorem exists_charge (hW : Nice W) (D : VOA.Classification.COne.ModularData W)
    (hD : D.IsModularData) :
    ∃ σ : D.ι → D.ι, (∀ x, σ (σ x) = x) ∧
      (∀ b x, fus D b x D.vac = if x = σ b then 1 else 0) ∧
      Matrix.of D.S * Matrix.of D.S = Matrix.of fun x y => if y = σ x then (1 : ℂ) else 0 := by
  obtain ⟨⟨Mfam, h, hw, rep, repS, hrS, hrT⟩, hM, hh, hZ⟩ := exists_zhuData hW D hD
  simp only at hM hh
  subst hM hh
  set D' : VOA.ModularData W D.ι := ⟨famOf D hD, hOf D, hw, rep, repS, hrS, hrT⟩ with hD'
  obtain ⟨Pr⟩ := ZhuModData.zhuPBWBottomInput_of_pbw V W
  have hSeq : D.S = D'.repS :=
    S_eq_repS Pr hW.1.c2Cofinite D hD D' hZ (fun _ _ _ => rfl)
  have hirr : Irredundant D'.Mfam := irredundant_famOf D hD
  have hcomp : Complete D'.Mfam := complete_famOf D hD
  have hv0 : Nonempty (ModuleEquiv W (D'.Mfam D.vac).isMod (adjointModule W)) := hD.vac_iso
  obtain ⟨σ, hrep, hfus⟩ := VerlindeVacuum.chargeConjugationInput_of_rhoNegOne
    VerlindeRho.rhoNegOneInput_pbw.{u, 0} V W hW D.ι D' hZ hirr hcomp D.vac hv0
  have hfus' : ∀ b x, fus D b x D.vac = if x = σ b then 1 else 0 := hfus
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    have h1 := hfus' x (σ x)
    rw [if_pos rfl] at h1
    have h2 : fus D (σ x) x D.vac = 1 := by
      rw [fus, BraidingSkew.fusionRule_swap]; exact h1
    rw [hfus'] at h2
    by_contra hne
    rw [if_neg (Ne.symm hne)] at h2
    exact zero_ne_one h2
  refine ⟨σ, hσ, hfus', ?_⟩
  have h := congrArg D'.rep modularS_mul_S
  rw [map_mul, D'.rep_S] at h
  rw [hSeq, h]
  ext x y
  exact hrep x y

/-- **Huang's Theorem 5.6: the `S`-matrix of a nice VOA is symmetric.** -/
theorem S_symm (hW : Nice W) (D : VOA.Classification.COne.ModularData W)
    (hD : D.IsModularData) (a b : D.ι) : D.S a b = D.S b a := by
  obtain ⟨hE, hunit, -⟩ := zhu_facts hW D hD
  obtain ⟨σ, hσ, hvac, hSC⟩ := exists_charge hW D hD
  have hvacS : ∀ z, D.S z D.vac = D.S D.vac z := fun z => by
    rw [hD.S_vac_left, hD.S_vac_right]
  have hdualN : ∀ a x y, fus D a x y = fus D a (σ y) (σ x) := by
    intro a x y
    rw [fus_dual hW D hD σ hσ hvac a x y, fus_dual hW D hD σ hσ hvac a (σ y) (σ x), hσ,
      fus, fus, BraidingSkew.fusionRule_swap]
  exact symm_of_eigen_dual σ hunit hE hvacS hσ hdualN hSC a b

end Dual

/-! ## §4 Assembly -/

/-- **`SSymmetricInput`.** -/
theorem sSymmetricInput_holds : SSymmetricInput.{u} :=
  fun _ _ _ _ hW D hD a b => S_symm hW D hD a b

/-- **Huang's modularity input from the dimension clause alone.** -/
theorem huangModularityInput_of_qdimInput (hq : HuangQDimInput.{u}) :
    HuangModularityInput.{u} :=
  huangModularityInput_of_qdim hq sSymmetricInput_holds

/-- **`HuangModularityInput` is exactly the dimension clause.** -/
theorem huangModularityInput_iff_qdim : HuangModularityInput.{u} ↔ HuangQDimInput.{u} :=
  ⟨huangQDimInput_of_modularity, huangModularityInput_of_qdimInput⟩

/-- **`HuangRepInput` from the dimension clause alone.** -/
theorem huangRepInput_of_qdimInput (hq : HuangQDimInput.{u}) : HuangRepInput.{u} :=
  huangRepInput_of_modularity (huangModularityInput_of_qdimInput hq)

end VOA.Huang.HuangModularity
