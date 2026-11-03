/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.TensorCategories

/-!
# Pivotal-trace calculus and the balancing formula for `S̃` (monoidal category theory only)

For the library's (weak, non-monoidal) `PivotalStructure` on a `ℂ`-linear right rigid monoidal
category:

* `trL_comp_comm` — **cyclicity** `tr(f ≫ g) = tr(g ≫ f)` for `f : X ⟶ Y`, `g : Y ⟶ X`
  (naturality of `piv` and the two mate identities; no monoidality of `piv` needed);
* `trL_conj`, `qdim_congr` — invariance under isomorphism;
* `trL_biproduct` — additivity over a finite biproduct.

For a fusion category (`FusionCategory`):

* `finrank_hom_simple` — `dim Hom(X_c, X_d) = δ_cd`; `finrank_hom_biproduct` and
  `finrank_biproduct_hom` — `dim Hom(X_c, ⨁ X_{f k}) = dim Hom(⨁ X_{f k}, X_c) = #{k | f k = c}`;
* `toScalar_trL_eigen` — the trace of an endomorphism `φ_X` from a natural family that acts on
  every simple by a scalar `λ_c` is `Σ_c N_X^c λ_c dim X_c`, `N_X^c = dim Hom(X_c, X)`;
* `qdim_tensor_eq_sum` — `dim(X_i ⊗ X_j) = Σ_c N_{ij}^c dim X_c`;
* `sTilde_mul_T` — **the balancing formula** `S̃_ij T_i T_j = Σ_c N_{ij}^c T_c dim X_c`
  (`S̃_ij = tr(c_{j,i} c_{i,j})`, from the balancing axiom of the twist).

No `sorry`, no axioms beyond Lean's.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HuangModularity

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Module
  VOA.Huang.TensorCat

universe v u

section Trace

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [RightRigidCategory C]

/-- **Cyclicity of the left pivotal trace.** -/
theorem trL_comp_comm (P : PivotalStructure C) {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    P.trL (f ≫ g) = P.trL (g ≫ f) := by
  simp only [PivotalStructure.trL]
  -- move `g` through the pivotal structure
  rw [← comp_whiskerRight_assoc, Category.assoc, P.naturality g, comp_whiskerRight_assoc,
    comp_whiskerRight_assoc, rightAdjointMate_comp_evaluation, ← comp_whiskerRight_assoc f,
    ← whisker_exchange_assoc, coevaluation_comp_rightAdjointMate_assoc]
  simp only [comp_whiskerRight, Category.assoc]

theorem trL_zero (P : PivotalStructure C) (X : C) : P.trL (0 : X ⟶ X) = 0 := by
  simp [PivotalStructure.trL]

theorem trL_sum (P : PivotalStructure C) {X : C} {J : Type*} (s : Finset J) (f : J → (X ⟶ X)) :
    P.trL (∑ j ∈ s, f j) = ∑ j ∈ s, P.trL (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [trL_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, P.trL_add, ih]

/-- Invariance of the trace under conjugation by an isomorphism. -/
theorem trL_conj (P : PivotalStructure C) {X Y : C} (e : X ≅ Y) (f : Y ⟶ Y) :
    P.trL (e.hom ≫ f ≫ e.inv) = P.trL f := by
  rw [trL_comp_comm, Category.assoc, e.inv_hom_id, Category.comp_id]

/-- **Pivotal dimension is invariant under isomorphism.** -/
theorem qdim_congr (P : PivotalStructure C) {X Y : C} (e : X ≅ Y) : P.qdim X = P.qdim Y := by
  simp only [PivotalStructure.qdim]
  rw [← e.hom_inv_id, trL_comp_comm, e.inv_hom_id]

/-- **Additivity of the trace over a finite biproduct.** -/
theorem trL_biproduct (P : PivotalStructure C) {J : Type} [Fintype J] (g : J → C)
    [HasBiproduct g] (f : ⨁ g ⟶ ⨁ g) :
    P.trL f = ∑ j, P.trL (biproduct.ι g j ≫ f ≫ biproduct.π g j) := by
  conv_lhs => rw [← Category.id_comp f, ← biproduct.total, Preadditive.sum_comp]
  rw [trL_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Category.assoc, trL_comp_comm, Category.assoc]

end Trace

section Fusion

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [RightRigidCategory C] [HasKernels C]
  [HasFiniteBiproducts C] [F : FusionCategory C]

/-- `toScalar` is additive (`End 𝟙 = ℂ`). -/
theorem toScalar_add (f g : 𝟙_ C ⟶ 𝟙_ C) : toScalar (f + g) = toScalar f + toScalar g := by
  have h1 := FusionCategory.finrank_end_unit (C := C)
  conv_lhs => rw [← toScalar_smul_id h1 f, ← toScalar_smul_id h1 g, ← add_smul]
  exact toScalar_smul h1 _

theorem toScalar_zero : toScalar (0 : 𝟙_ C ⟶ 𝟙_ C) = 0 := by
  have h1 := FusionCategory.finrank_end_unit (C := C)
  have := toScalar_smul h1 (0 : ℂ)
  rwa [zero_smul] at this

theorem toScalar_smul' (c : ℂ) (f : 𝟙_ C ⟶ 𝟙_ C) : toScalar (c • f) = c * toScalar f := by
  have h1 := FusionCategory.finrank_end_unit (C := C)
  conv_lhs => rw [← toScalar_smul_id h1 f, smul_smul]
  exact toScalar_smul h1 _

theorem toScalar_sum {J : Type*} (s : Finset J) (f : J → (𝟙_ C ⟶ 𝟙_ C)) :
    toScalar (∑ j ∈ s, f j) = ∑ j ∈ s, toScalar (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [toScalar_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, toScalar_add, ih]

/-- Schur: `dim Hom(X_c, X_d) = δ_cd`. -/
theorem finrank_hom_simple (c d : F.ι) :
    finrank ℂ (F.simple c ⟶ F.simple d) = if c = d then 1 else 0 := by
  haveI := F.isSimple c
  haveI := F.isSimple d
  haveI := F.finiteDimensional (F.simple c) (F.simple d)
  split_ifs with h
  · subst h
    haveI := F.finiteDimensional (F.simple c) (F.simple c)
    exact finrank_endomorphism_simple_eq_one ℂ (F.simple c)
  · have hz : ∀ f : F.simple c ⟶ F.simple d, f = 0 := by
      intro f
      by_contra hf
      haveI := isIso_of_hom_simple hf
      exact h (F.inequivalent c d ⟨asIso f⟩)
    haveI : Subsingleton (F.simple c ⟶ F.simple d) := ⟨fun a b => by rw [hz a, hz b]⟩
    exact finrank_zero_of_subsingleton

/-- `Hom(Z, ⨁ g) ≃ Π_k Hom(Z, g k)`, linearly. -/
def homBiproductEquiv {J : Type} [Fintype J] (g : J → C) (Z : C) :
    (Z ⟶ ⨁ g) ≃ₗ[ℂ] ((k : J) → (Z ⟶ g k)) where
  toFun h k := h ≫ biproduct.π g k
  map_add' a b := by funext k; simp [Preadditive.add_comp]
  map_smul' c a := by funext k; simp
  invFun p := biproduct.lift p
  left_inv h := by apply biproduct.hom_ext; intro k; simp
  right_inv p := by funext k; simp

/-- `Hom(⨁ g, Z) ≃ Π_k Hom(g k, Z)`, linearly. -/
def biproductHomEquiv {J : Type} [Fintype J] (g : J → C) (Z : C) :
    (⨁ g ⟶ Z) ≃ₗ[ℂ] ((k : J) → (g k ⟶ Z)) where
  toFun h k := biproduct.ι g k ≫ h
  map_add' a b := by funext k; simp [Preadditive.comp_add]
  map_smul' c a := by funext k; simp
  invFun p := biproduct.desc p
  left_inv h := by apply biproduct.hom_ext'; intro k; simp
  right_inv p := by funext k; simp

/-- `dim Hom(X_c, ⨁_k X_{f k}) = #{k | f k = c}`. -/
theorem finrank_hom_biproduct {n : ℕ} (f : Fin n → F.ι) (c : F.ι) :
    finrank ℂ (F.simple c ⟶ ⨁ fun k => F.simple (f k)) =
      (Finset.univ.filter fun k => f k = c).card := by
  rw [(homBiproductEquiv (fun k => F.simple (f k)) (F.simple c)).finrank_eq]
  haveI : ∀ k, FiniteDimensional ℂ (F.simple c ⟶ F.simple (f k)) := fun k =>
    F.finiteDimensional _ _
  rw [Module.finrank_pi_fintype, Finset.card_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [finrank_hom_simple]
  by_cases h : f k = c
  · simp [h]
  · simp [h, Ne.symm h]

/-- `dim Hom(⨁_k X_{f k}, X_c) = #{k | f k = c}`. -/
theorem finrank_biproduct_hom {n : ℕ} (f : Fin n → F.ι) (c : F.ι) :
    finrank ℂ ((⨁ fun k => F.simple (f k)) ⟶ F.simple c) =
      (Finset.univ.filter fun k => f k = c).card := by
  rw [(biproductHomEquiv (fun k => F.simple (f k)) (F.simple c)).finrank_eq]
  haveI : ∀ k, FiniteDimensional ℂ (F.simple (f k) ⟶ F.simple c) := fun k =>
    F.finiteDimensional _ _
  rw [Module.finrank_pi_fintype, Finset.card_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [finrank_hom_simple]

/-- The multiplicity of `X_c` in `X`: `dim Hom(X_c, X)`. -/
def mult (X : C) (c : F.ι) : ℕ := finrank ℂ (F.simple c ⟶ X)

theorem mult_eq_card {X : C} {n : ℕ} (f : Fin n → F.ι) (e : X ≅ ⨁ fun k => F.simple (f k))
    (c : F.ι) : mult X c = (Finset.univ.filter fun k => f k = c).card := by
  rw [mult, (Linear.homCongr ℂ (Iso.refl (F.simple c)) e).finrank_eq, finrank_hom_biproduct]

/-- Multiplicities are symmetric: `dim Hom(X_c, X) = dim Hom(X, X_c)`. -/
theorem mult_eq_finrank_hom_to (X : C) (c : F.ι) :
    mult X c = finrank ℂ (X ⟶ F.simple c) := by
  obtain ⟨n, f, ⟨e⟩⟩ := F.semisimple X
  rw [mult_eq_card f e, (Linear.homCongr ℂ e (Iso.refl (F.simple c))).finrank_eq,
    finrank_biproduct_hom]

/-- `Σ_k g(f k) = Σ_c #{k | f k = c} g(c)`. -/
theorem sum_fiber {n : ℕ} (f : Fin n → F.ι) (g : F.ι → ℂ) :
    ∑ k, g (f k) = ∑ c, ((Finset.univ.filter fun k => f k = c).card : ℂ) * g c := by
  rw [← Finset.sum_fiberwise Finset.univ f (fun k => g (f k))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => g c), Finset.sum_const, nsmul_eq_mul]
  intro k hk
  rw [(Finset.mem_filter.mp hk).2]

/-- **Trace of a natural family acting on simples by scalars.** If `φ` is natural and
`φ_{X_c} = λ_c • 𝟙`, then `tr(φ_X) = Σ_c N_X^c λ_c dim X_c`. -/
theorem toScalar_trL_eigen (P : PivotalStructure C) (φ : ∀ X : C, X ⟶ X)
    (hφ : ∀ {X Y : C} (f : X ⟶ Y), f ≫ φ Y = φ X ≫ f) (lam : F.ι → ℂ)
    (hlam : ∀ c, φ (F.simple c) = lam c • 𝟙 (F.simple c)) (X : C) :
    toScalar (P.trL (φ X)) = ∑ c, (mult X c : ℂ) * (lam c * P.qdim (F.simple c)) := by
  obtain ⟨n, f, ⟨e⟩⟩ := F.semisimple X
  have hX : φ X = e.hom ≫ φ _ ≫ e.inv := by
    rw [← Category.assoc, hφ e.hom, Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [hX, trL_conj, trL_biproduct, toScalar_sum]
  have hk : ∀ k, biproduct.ι (fun k => F.simple (f k)) k ≫ φ _ ≫
      biproduct.π (fun k => F.simple (f k)) k = lam (f k) • 𝟙 (F.simple (f k)) := by
    intro k
    rw [← Category.assoc, hφ, hlam, Category.assoc, biproduct.ι_π_self, Category.comp_id]
  simp_rw [hk, P.trL_smul, toScalar_smul', PivotalStructure.qdim]
  rw [sum_fiber f (fun c => lam c * toScalar (P.trL (𝟙 (F.simple c))))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mult_eq_card f e c]

/-- **Pivotal dimension through the decomposition**: `dim X = Σ_c N_X^c dim X_c`. -/
theorem qdim_eq_sum (P : PivotalStructure C) (X : C) :
    P.qdim X = ∑ c, (mult X c : ℂ) * P.qdim (F.simple c) := by
  have h := toScalar_trL_eigen P (fun X => 𝟙 X) (fun f => by simp) (fun _ => 1)
    (fun c => by simp) X
  simpa [PivotalStructure.qdim] using h

/-- `dim(X_i ⊗ X_j) = Σ_c N_{ij}^c dim X_c`. -/
theorem qdim_tensor_eq_sum (P : PivotalStructure C) (i j : F.ι) :
    P.qdim (F.simple i ⊗ F.simple j) = ∑ c, (F.N i j c : ℂ) * P.qdim (F.simple c) :=
  qdim_eq_sum P _

theorem smul_tensorHom_smul {X X' Y Y' : C} (a b : ℂ) (f : X ⟶ X') (g : Y ⟶ Y') :
    (a • f) ⊗ₘ (b • g) = (a * b) • (f ⊗ₘ g) := by
  rw [tensorHom_def, tensorHom_def, MonoidalLinear.smul_whiskerRight,
    MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul, smul_smul]

variable [BraidedCategory C]

theorem RibbonStructure.T_ne_zero (R : RibbonStructure C) (i : F.ι) : R.T i ≠ 0 := by
  intro h
  have h1 := R.T_spec i
  rw [h, zero_smul] at h1
  haveI := F.isSimple i
  have : 𝟙 (F.simple i) = 0 := by
    rw [← (R.twist (F.simple i)).hom_inv_id, ← h1, zero_comp]
  exact id_nonzero _ this

/-- **The balancing formula**: `S̃_ij T_i T_j = Σ_c N_{ij}^c T_c dim X_c`. -/
theorem sTilde_mul_T (R : RibbonStructure C) (i j : F.ι) :
    R.sTilde i j * (R.T i * R.T j) =
      ∑ c, (F.N i j c : ℂ) * (R.T c * R.qdim (F.simple c)) := by
  have hb := R.balance (F.simple i) (F.simple j)
  rw [← R.T_spec i, ← R.T_spec j, smul_tensorHom_smul, id_tensorHom_id, Linear.smul_comp,
    Category.id_comp] at hb
  have h := toScalar_trL_eigen R.toPivotalStructure (fun X => (R.twist X).hom)
    (fun f => R.twist_naturality f) R.T (fun c => (R.T_spec c).symm)
    (F.simple i ⊗ F.simple j)
  rw [hb, R.trL_smul, toScalar_smul'] at h
  rw [RibbonStructure.sTilde, mul_comm, h]
  rfl

end Fusion

end VOA.Huang.HuangModularity
