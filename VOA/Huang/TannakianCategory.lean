/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.TensorCategories
import VOA.Huang.TannakianMuger

/-!
# Müger's criterion in a ribbon fusion category

Over the T1 definitions (`FusionCategory`, `PivotalStructure`, `RibbonStructure`, `sTilde`):

## §1  Traces
* `PivotalStructure.trL_comp_comm` — **cyclicity** `tr(f ≫ g) = tr(g ≫ f)` for `f : X ⟶ Y`,
  `g : Y ⟶ X`.  Only naturality of the pivotal isomorphism is used (no monoidality).
* `trL_conj`, `trL_sum`, `trL_biproduct` — invariance under conjugation by an isomorphism and
  additivity over a finite biproduct decomposition.

## §2  The twist on a decomposition; the balancing formula
* `RibbonStructure.twist_eq_smul_of_iso` — if `X ≅ ⨁ X_{h k}` and every `T_{h k} = t`, then
  `θ_X = t • 𝟙`.
* `RibbonStructure.doubleBraiding_eq` — `c_{Y,X} c_{X,Y} = (θ_X ⊗ θ_Y)⁻¹ θ_{X ⊗ Y}` (balancing).
* `N_ne_zero_of_summand` — every summand of `X_i ⊗ X_j` is a fusion channel (`N_ij^c ≠ 0`).
* `FusionCategory.N_eq_card` — `N_ij^c` counts the summands isomorphic to `X_c` in any
  decomposition of `X_i ⊗ X_j` (Schur).
* `RibbonStructure.sTilde_eq_balancedS` — the **balancing formula**
  `S̃_ij = ∑_c N_ij^c (T_c / (T_i T_j)) d_c` (with `d_c = qdim X_c`).

## §3  Müger's criterion for a pair of simples (pseudo-unitary)
* `RibbonStructure.doubleBraiding_eq_id_of_channels` — if every channel `c` of `i ⊗ j` has
  `T_c = T_i T_j`, the double braiding on `X_i ⊗ X_j` is the identity;
* `RibbonStructure.muger_simple` — with `d_c > 0` real, `|T_c| = 1` and
  `qdim (X_i ⊗ X_j) = d_i d_j`:  `S̃_ij = d_i d_j ⟺ c_{j,i} c_{i,j} = 𝟙`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.TensorCat

open CategoryTheory MonoidalCategory Limits Module

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-! ## §0  `toScalar` is linear -/

section Scalar

theorem toScalar_add (h : finrank ℂ (𝟙_ C ⟶ 𝟙_ C) = 1) (f g : 𝟙_ C ⟶ 𝟙_ C) :
    toScalar (f + g) = toScalar f + toScalar g := by
  have e := toScalar_smul h (toScalar f + toScalar g)
  rw [add_smul, toScalar_smul_id h, toScalar_smul_id h] at e
  exact e

theorem toScalar_smul' (h : finrank ℂ (𝟙_ C ⟶ 𝟙_ C) = 1) (c : ℂ) (f : 𝟙_ C ⟶ 𝟙_ C) :
    toScalar (c • f) = c * toScalar f := by
  conv_lhs => rw [← toScalar_smul_id h f, smul_smul]
  exact toScalar_smul h _

theorem toScalar_zero (h : finrank ℂ (𝟙_ C ⟶ 𝟙_ C) = 1) : toScalar (0 : 𝟙_ C ⟶ 𝟙_ C) = 0 := by
  have := toScalar_smul h 0
  rwa [zero_smul] at this

theorem toScalar_sum (h : finrank ℂ (𝟙_ C ⟶ 𝟙_ C) = 1) {J : Type*} (s : Finset J)
    (f : J → (𝟙_ C ⟶ 𝟙_ C)) : toScalar (∑ j ∈ s, f j) = ∑ j ∈ s, toScalar (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [toScalar_zero h]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, toScalar_add h, ih]

end Scalar

/-! ## §1  Traces -/

section Trace

variable [RightRigidCategory C] (P : PivotalStructure C)

namespace PivotalStructure

/-- **Cyclicity of the pivotal trace**: `tr(f ≫ g) = tr(g ≫ f)`.  Uses only the naturality
of the pivotal isomorphism, the mate identities for `fᘁ` and the interchange law. -/
theorem trL_comp_comm {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : P.trL (f ≫ g) = P.trL (g ≫ f) := by
  have hnat := P.naturality f
  calc P.trL (f ≫ g)
      = η_ X Xᘁ ≫ (f ▷ Xᘁ) ≫ ((g ≫ (P.piv X).hom) ▷ Xᘁ) ≫ ε_ Xᘁ (Xᘁ)ᘁ := by
        simp [trL]
    _ = η_ Y Yᘁ ≫ (Y ◁ fᘁ) ≫ ((g ≫ (P.piv X).hom) ▷ Xᘁ) ≫ ε_ Xᘁ (Xᘁ)ᘁ := by
        rw [coevaluation_comp_rightAdjointMate_assoc]
    _ = η_ Y Yᘁ ≫ ((g ≫ (P.piv X).hom) ▷ Yᘁ) ≫ ((Xᘁ)ᘁ ◁ fᘁ) ≫ ε_ Xᘁ (Xᘁ)ᘁ := by
        rw [whisker_exchange_assoc]
    _ = η_ Y Yᘁ ≫ ((g ≫ (P.piv X).hom) ▷ Yᘁ) ≫ ((fᘁ)ᘁ ▷ Yᘁ) ≫ ε_ Yᘁ (Yᘁ)ᘁ := by
        rw [rightAdjointMate_comp_evaluation]
    _ = P.trL (g ≫ f) := by
        simp only [trL, ← comp_whiskerRight_assoc, Category.assoc, ← hnat]

/-- The trace is invariant under conjugation by an isomorphism. -/
theorem trL_conj {X Y : C} (e : X ≅ Y) (g : Y ⟶ Y) : P.trL (e.hom ≫ g ≫ e.inv) = P.trL g := by
  rw [trL_comp_comm, Category.assoc, e.inv_hom_id, Category.comp_id]

theorem trL_zero {X : C} : P.trL (0 : X ⟶ X) = 0 := by
  simp [trL]

theorem trL_sum {X : C} {J : Type*} (s : Finset J) (f : J → (X ⟶ X)) :
    P.trL (∑ j ∈ s, f j) = ∑ j ∈ s, P.trL (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [trL_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, trL_add, ih]

/-- **Additivity over a biproduct**: `tr g = ∑_j tr(ι_j ≫ g ≫ π_j)`. -/
theorem trL_biproduct {J : Type} [Fintype J] (f : J → C) [HasBiproduct f] (g : ⨁ f ⟶ ⨁ f) :
    P.trL g = ∑ j, P.trL (biproduct.ι f j ≫ g ≫ biproduct.π f j) := by
  conv_lhs => rw [← Category.id_comp g, ← biproduct.total, Preadditive.sum_comp]
  rw [trL_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Category.assoc, trL_comp_comm, Category.assoc]

end PivotalStructure

end Trace

/-! ## §2  The twist on a decomposition; the balancing formula -/

section Ribbon

variable [RightRigidCategory C] [BraidedCategory C] [HasKernels C] [HasFiniteBiproducts C]
  [F : FusionCategory C]

theorem smul_id_tensorHom_smul_id (a b : ℂ) (X Y : C) :
    (a • 𝟙 X) ⊗ₘ (b • 𝟙 Y) = (a * b) • 𝟙 (X ⊗ Y) := by
  rw [tensorHom_def]
  simp [smul_smul, mul_comm]

/-- In a decomposition `X ≅ ⨁ X_{h k}`, the composite `ι_k ≫ e⁻¹ : X_{h k} ⟶ X` is nonzero. -/
theorem iota_comp_inv_ne_zero {X : C} {n : ℕ} {h : Fin n → F.ι}
    (e : X ≅ ⨁ fun k => F.simple (h k)) (k : Fin n) :
    biproduct.ι (fun k => F.simple (h k)) k ≫ e.inv ≠ 0 := by
  intro h0
  haveI := F.isSimple (h k)
  apply id_nonzero (F.simple (h k))
  have : biproduct.ι (fun k => F.simple (h k)) k ≫ e.inv ≫ e.hom ≫
      biproduct.π (fun k => F.simple (h k)) k = 𝟙 _ := by simp
  rw [← Category.assoc, h0, zero_comp] at this
  exact this.symm

/-- A nonzero morphism `X_c ⟶ X_i ⊗ X_j` makes `c` a fusion channel. -/
theorem FusionCategory.N_ne_zero_of_ne_zero {i j c : F.ι}
    (φ : F.simple c ⟶ F.simple i ⊗ F.simple j) (hφ : φ ≠ 0) : F.N i j c ≠ 0 := by
  haveI := F.finiteDimensional (F.simple c) (F.simple i ⊗ F.simple j)
  exact (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨φ, hφ⟩).ne'

/-- Every summand of a decomposition of `X_i ⊗ X_j` is a fusion channel. -/
theorem N_ne_zero_of_summand {i j : F.ι} {n : ℕ} {h : Fin n → F.ι}
    (e : F.simple i ⊗ F.simple j ≅ ⨁ fun k => F.simple (h k)) (k : Fin n) :
    F.N i j (h k) ≠ 0 :=
  FusionCategory.N_ne_zero_of_ne_zero _ (iota_comp_inv_ne_zero e k)

/-- Schur: `dim Hom(X_c, X_d) = [c = d]`. -/
theorem FusionCategory.finrank_hom_simple (c d : F.ι) :
    finrank ℂ (F.simple c ⟶ F.simple d) = if c = d then 1 else 0 := by
  haveI := F.isSimple c
  haveI := F.isSimple d
  haveI := F.finiteDimensional (F.simple c) (F.simple c)
  haveI := F.finiteDimensional (F.simple c) (F.simple d)
  split_ifs with hcd
  · subst hcd
    exact (finrank_hom_simple_simple_eq_one_iff ℂ _ _).mpr ⟨Iso.refl _⟩
  · exact (finrank_hom_simple_simple_eq_zero_iff ℂ _ _).mpr
      ⟨fun e => hcd (F.inequivalent c d ⟨e⟩)⟩

/-- `Hom(Z, ⨁ f) ≃ ∏_k Hom(Z, f k)`, `ℂ`-linearly. -/
def homBiproductEquiv {J : Type} [Fintype J] (Z : C) (f : J → C) :
    (Z ⟶ ⨁ f) ≃ₗ[ℂ] ((k : J) → (Z ⟶ f k)) where
  toFun φ k := φ ≫ biproduct.π f k
  invFun ψ := biproduct.lift ψ
  map_add' φ ψ := by ext k; simp [Preadditive.add_comp]
  map_smul' c φ := by ext k; simp
  left_inv φ := by ext k; simp
  right_inv ψ := by ext k; simp

/-- **Multiplicities**: in any decomposition `X ≅ ⨁ X_{h k}`, the number of summands
isomorphic to `X_c` is `dim Hom(X_c, X)`. -/
theorem FusionCategory.finrank_hom_eq_card {X : C} {n : ℕ} {h : Fin n → F.ι}
    (e : X ≅ ⨁ fun k => F.simple (h k)) (c : F.ι) :
    finrank ℂ (F.simple c ⟶ X) = (Finset.univ.filter fun k => h k = c).card := by
  haveI := fun k => F.finiteDimensional (F.simple c) (F.simple (h k))
  rw [(Linear.homCongr ℂ (Iso.refl (F.simple c)) e).finrank_eq,
    (homBiproductEquiv (F.simple c) _).finrank_eq, Module.finrank_pi_fintype]
  simp only [FusionCategory.finrank_hom_simple]
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl fun k _ => by split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

/-- `N_ij^c` counts the summands `≅ X_c` of any decomposition of `X_i ⊗ X_j`. -/
theorem FusionCategory.N_eq_card {i j : F.ι} {n : ℕ} {h : Fin n → F.ι}
    (e : F.simple i ⊗ F.simple j ≅ ⨁ fun k => F.simple (h k)) (c : F.ι) :
    F.N i j c = (Finset.univ.filter fun k => h k = c).card :=
  FusionCategory.finrank_hom_eq_card e c

namespace PivotalStructure

variable (P : PivotalStructure C)

/-- The trace computed on a decomposition `X ≅ ⨁ f`. -/
theorem trL_of_iso {X : C} {J : Type} [Fintype J] {f : J → C} (e : X ≅ ⨁ f) (g : X ⟶ X) :
    P.trL g = ∑ k, P.trL (biproduct.ι f k ≫ e.inv ≫ g ≫ e.hom ≫ biproduct.π f k) := by
  rw [← P.trL_conj e.symm g, trL_biproduct]
  simp [Category.assoc]

end PivotalStructure

namespace RibbonStructure

variable (R : RibbonStructure C)

/-- If every summand of `X ≅ ⨁ X_{h k}` has twist `t`, then `θ_X = t • 𝟙`. -/
theorem twist_eq_smul_of_iso {X : C} {n : ℕ} {h : Fin n → F.ι}
    (e : X ≅ ⨁ fun k => F.simple (h k)) (t : ℂ) (ht : ∀ k, R.T (h k) = t) :
    (R.twist X).hom = t • 𝟙 X := by
  have hB : (R.twist (⨁ fun k => F.simple (h k))).hom = t • 𝟙 _ := by
    apply biproduct.hom_ext'
    intro k
    rw [R.twist_naturality, ← R.T_spec, ht k]
    simp
  have hn := R.twist_naturality e.hom
  calc (R.twist X).hom = (R.twist X).hom ≫ e.hom ≫ e.inv := by simp
    _ = e.hom ≫ (R.twist _).hom ≫ e.inv := by rw [← Category.assoc, ← hn, Category.assoc]
    _ = t • 𝟙 X := by rw [hB]; simp

theorem T_ne_zero (i : F.ι) : R.T i ≠ 0 := by
  intro h0
  haveI := F.isSimple i
  apply id_nonzero (F.simple i)
  have h1 := (R.twist (F.simple i)).hom_inv_id
  rw [← R.T_spec, h0, zero_smul, zero_comp] at h1
  exact h1.symm

/-- The **balancing** identity `c_{Y,X} c_{X,Y} = (θ_X ⊗ θ_Y)⁻¹ θ_{X ⊗ Y}`. -/
theorem doubleBraiding_eq (X Y : C) :
    (β_ X Y).hom ≫ (β_ Y X).hom = ((R.twist X).inv ⊗ₘ (R.twist Y).inv) ≫ (R.twist (X ⊗ Y)).hom := by
  rw [R.balance, ← Category.assoc, tensorHom_comp_tensorHom]
  simp

/-- For simples, `θ_{X_i ⊗ X_j} = T_i T_j • (c_{j,i} c_{i,j})`. -/
theorem twist_tensor_simple (i j : F.ι) :
    (R.twist (F.simple i ⊗ F.simple j)).hom =
      (R.T i * R.T j) • ((β_ (F.simple i) (F.simple j)).hom ≫ (β_ (F.simple j) (F.simple i)).hom) := by
  rw [R.balance, ← R.T_spec, ← R.T_spec, smul_id_tensorHom_smul_id, Linear.smul_comp,
    Category.id_comp]

/-- **Müger, sufficiency**: if every fusion channel `c` of `i ⊗ j` has `T_c = T_i T_j`, then
the double braiding on `X_i ⊗ X_j` is the identity. -/
theorem doubleBraiding_eq_id_of_channels (i j : F.ι)
    (hch : ∀ c, F.N i j c ≠ 0 → R.T c = R.T i * R.T j) :
    (β_ (F.simple i) (F.simple j)).hom ≫ (β_ (F.simple j) (F.simple i)).hom = 𝟙 _ := by
  obtain ⟨n, h, ⟨e⟩⟩ := F.semisimple (F.simple i ⊗ F.simple j)
  have htw := R.twist_eq_smul_of_iso e (R.T i * R.T j) fun k => hch _ (N_ne_zero_of_summand e k)
  rw [R.twist_tensor_simple] at htw
  exact smul_right_injective _ (mul_ne_zero (R.T_ne_zero i) (R.T_ne_zero j)) htw

/-- The quantum dimension of `X_i ⊗ X_j` is `∑_c N_ij^c d_c`. -/
theorem qdim_tensor_simple (i j : F.ι) :
    R.qdim (F.simple i ⊗ F.simple j) = ∑ c, (F.N i j c : ℂ) * R.qdim (F.simple c) := by
  obtain ⟨n, h, ⟨e⟩⟩ := F.semisimple (F.simple i ⊗ F.simple j)
  have hfin := F.finrank_end_unit
  have h1 : R.trL (𝟙 (F.simple i ⊗ F.simple j)) = ∑ k, R.trL (𝟙 (F.simple (h k))) := by
    rw [R.trL_of_iso e]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  rw [PivotalStructure.qdim, h1, toScalar_sum hfin]
  rw [← Finset.sum_fiberwise Finset.univ h (fun k => toScalar (R.trL (𝟙 (F.simple (h k)))))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.mp hk).2]), Finset.sum_const,
    nsmul_eq_mul, FusionCategory.N_eq_card e c]
  rfl

/-- **The balancing formula** `S̃_ij = ∑_c N_ij^c (T_c / (T_i T_j)) d_c`. -/
theorem sTilde_eq_sum (i j : F.ι) :
    R.sTilde i j = ∑ c, (F.N i j c : ℂ) * (R.T c / (R.T i * R.T j)) * R.qdim (F.simple c) := by
  obtain ⟨n, h, ⟨e⟩⟩ := F.semisimple (F.simple i ⊗ F.simple j)
  have hfin := F.finrank_end_unit
  have hTT : R.T i * R.T j ≠ 0 := mul_ne_zero (R.T_ne_zero i) (R.T_ne_zero j)
  have hcc : (β_ (F.simple i) (F.simple j)).hom ≫ (β_ (F.simple j) (F.simple i)).hom =
      (R.T i * R.T j)⁻¹ • (R.twist (F.simple i ⊗ F.simple j)).hom := by
    rw [R.twist_tensor_simple, smul_smul, inv_mul_cancel₀ hTT, one_smul]
  have h1 : R.trL (R.twist (F.simple i ⊗ F.simple j)).hom =
      ∑ k, R.T (h k) • R.trL (𝟙 (F.simple (h k))) := by
    rw [R.trL_of_iso e]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hn := R.twist_naturality e.inv
    rw [← Category.assoc e.inv, hn]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, R.twist_naturality, ← R.T_spec]
    simp [PivotalStructure.trL_smul]
  rw [sTilde, hcc, PivotalStructure.trL_smul, h1, toScalar_smul' hfin, toScalar_sum hfin]
  simp only [toScalar_smul' hfin]
  rw [← Finset.sum_fiberwise Finset.univ h (fun k => R.T (h k) * toScalar (R.trL (𝟙 (F.simple (h k)))))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.mp hk).2]), Finset.sum_const,
    nsmul_eq_mul, FusionCategory.N_eq_card e c]
  rw [PivotalStructure.qdim]
  field_simp

/-! ## §3  Müger's criterion for a pair of simples -/

/-- **Müger's criterion (pseudo-unitary), for a pair of simples.**  Suppose the quantum
dimensions are positive reals `d_c`, the twists are unimodular, and `qdim (X_i ⊗ X_j) = d_i d_j`.
Then `S̃_ij = d_i d_j` **iff** the double braiding on `X_i ⊗ X_j` is the identity. -/
theorem muger_simple (d : F.ι → ℝ) (hd : ∀ c, 0 < d c) (hq : ∀ c, R.qdim (F.simple c) = d c)
    (hT : ∀ c, ‖R.T c‖ = 1) (i j : F.ι)
    (hmul : R.qdim (F.simple i ⊗ F.simple j) = (d i : ℂ) * (d j : ℂ)) :
    R.sTilde i j = (d i : ℂ) * (d j : ℂ) ↔
      (β_ (F.simple i) (F.simple j)).hom ≫ (β_ (F.simple j) (F.simple i)).hom = 𝟙 _ := by
  have hbal : R.sTilde i j = VOA.Huang.Tannakian.balancedS F.N R.T d i j := by
    rw [sTilde_eq_sum, VOA.Huang.Tannakian.balancedS]
    simp only [hq]
  have hmul' : (d i : ℂ) * (d j : ℂ) = ∑ c, (F.N i j c : ℂ) * (d c : ℂ) := by
    rw [← hmul, qdim_tensor_simple]; simp only [hq]
  constructor
  · intro hS
    rw [hbal] at hS
    exact R.doubleBraiding_eq_id_of_channels i j
      ((VOA.Huang.Tannakian.muger_numeric F.N R.T d hd hT i j hmul').mp hS)
  · intro hcc
    rw [sTilde, hcc, ← hmul]
    rfl

end RibbonStructure

end Ribbon

end VOA.Huang.TensorCat
