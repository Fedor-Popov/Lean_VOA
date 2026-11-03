/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.VerlindeTransportSplit
import VOA.Huang.PentagonCloseMain
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# The genus-zero half of the Verlinde transport split, proved

`GenusZeroTransferInput` (the replacement of Huang's Thm 4.1 / (4.9) in the split of
`VOA.Huang.VerlindeTransportSplit`) holds for every nice `W`:

* `bTransfer_eq_zigzag` — in the monoidal category of ordinary modules
  (`monoidalCategoryOfStronglyRational_pbw`) the B-cycle transfer factors as
  `inc_j ≫ (Z ▷ M_x) ≫ proj_j`, with `Z = λ⁻¹ ≫ (η ▷ M_b) ≫ α ≫ (M_b ◁ ε) ≫ ρ` the zig-zag
  endomorphism of `M_b` (pure coherence: naturality, interchange, pentagon/triangle via `monoidal`);
* `endo_scalar` — Schur: every endomorphism of a family member is a scalar;
* `famFusion_eq_sum` — the trace of the identity of `Hom(M_b ⊠ M_x, M_z)` computed through any
  split presentation: `N_{bx}^z = Σ_{lab j = z} c_j` where `inc_j ≫ proj_j = c_j • 𝟙`;
* `transferTraceInput_pbw : TransferTraceInput`, `transferChoiceExists_pbw :
  TransferChoiceExists`, `genusZeroTransferInput_pbw : GenusZeroTransferInput`.

No rigidity is used: the scalar `s` of the zig-zag may a priori vanish; its nonvanishing is a
*consequence* of the genus-one input (it is Huang's Prop. 5.1 in this language).

## Status
No `sorry`, no new axioms; the `_pbw` suffix marks the corollary in which the explicit PBW datum is
discharged by the theorem `VOA.pbw`; it adds no axiom (it enters
through the monoidal structure and the fusion-product choice).
-/

noncomputable section

namespace VOA.Huang.VerlindeTransport

open VOA VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.VerlindeFusion
  VOA.Huang.VerlindeEigen VOA.Huang.VerlindeEigenMatrix VOA.Huang.VerlindeVacuum
  VOA.Huang.TensorCat VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
  MonoidalCategory

universe u w

/-! ## §1 The coherence identity in an arbitrary monoidal category -/

section Coherence

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- The partial zig-zag: `λ⁻¹ ≫ (η ▷ (b ⊗ x)) ≫ α ≫ (b ◁ (α⁻¹ ≫ (ε ▷ x) ≫ λ)) = Z ▷ x`. -/
theorem zigzag_whisker (a b x : C) (ε : a ⊗ b ⟶ 𝟙_ C) (η : 𝟙_ C ⟶ b ⊗ a) :
    (λ_ (b ⊗ x)).inv ≫ (η ▷ (b ⊗ x)) ≫ (α_ b a (b ⊗ x)).hom ≫
      (b ◁ ((α_ a b x).inv ≫ (ε ▷ x) ≫ (λ_ x).hom)) =
    (((λ_ b).inv ≫ (η ▷ b) ≫ (α_ b a b).hom ≫ (b ◁ ε) ≫ (ρ_ b).hom) ▷ x) := by
  monoidal

/-- The B-cycle transfer through a summand factors through the zig-zag (without the projection). -/
theorem transfer_zigzag_aux (a b x z : C) (ε : a ⊗ b ⟶ 𝟙_ C) (η : 𝟙_ C ⟶ b ⊗ a)
    (inc : z ⟶ b ⊗ x) :
    (λ_ z).inv ≫ (η ▷ z) ≫ (α_ b a z).hom ≫
      (b ◁ ((a ◁ inc) ≫ (α_ a b x).inv ≫ (ε ▷ x) ≫ (λ_ x).hom)) =
    inc ≫ (((λ_ b).inv ≫ (η ▷ b) ≫ (α_ b a b).hom ≫ (b ◁ ε) ≫ (ρ_ b).hom) ▷ x) := by
  rw [← zigzag_whisker, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp]
  rw [← Category.assoc (α_ b a z).hom, ← associator_naturality_right]
  rw [Category.assoc, ← Category.assoc (η ▷ z), ← whisker_exchange]
  simp only [Category.assoc]
  rw [← Category.assoc (λ_ z).inv, ← leftUnitor_inv_naturality]
  simp only [Category.assoc, MonoidalCategory.whiskerLeft_comp]

/-- The B-cycle transfer through a summand factors through the zig-zag. -/
theorem transfer_zigzag (a b x z : C) (ε : a ⊗ b ⟶ 𝟙_ C) (η : 𝟙_ C ⟶ b ⊗ a)
    (inc : z ⟶ b ⊗ x) (proj : b ⊗ x ⟶ z) :
    (λ_ z).inv ≫ (η ▷ z) ≫ (α_ b a z).hom ≫
      (b ◁ ((a ◁ inc) ≫ (α_ a b x).inv ≫ (ε ▷ x) ≫ (λ_ x).hom)) ≫ proj =
    inc ≫ (((λ_ b).inv ≫ (η ▷ b) ≫ (α_ b a b).hom ≫ (b ◁ ε) ≫ (ρ_ b).hom) ▷ x) ≫ proj := by
  have key := transfer_zigzag_aux a b x z ε η inc
  calc _ = ((λ_ z).inv ≫ (η ▷ z) ≫ (α_ b a z).hom ≫
        (b ◁ ((a ◁ inc) ≫ (α_ a b x).inv ≫ (ε ▷ x) ≫ (λ_ x).hom))) ≫ proj := by
          simp only [Category.assoc]
    _ = _ := by rw [key, Category.assoc]

end Coherence

/-! ## §2 Module-category lemmas -/

section Module

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

theorem Ordinary.sum_val_apply {X Y : Ordinary W} {κ : Type*} (s : Finset κ)
    (f : κ → (X ⟶ Y)) (v : X.carrier) :
    (∑ j ∈ s, f j).val v = ∑ j ∈ s, (f j).val v := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, ← ih]
    rfl

theorem Ordinary.smul_val_apply {X Y : Ordinary W} (c : ℂ) (f : X ⟶ Y) (v : X.carrier) :
    (c • f).val v = c • f.val v := rfl

/-- A bijective module map as a module equivalence. -/
def moduleEquivOfBijective {X Y : Ordinary W} (f : X ⟶ Y) (hf : Function.Bijective f.val) :
    ModuleEquiv W X.isMod Y.isMod where
  toLinearEquiv := LinearEquiv.ofBijective f.val hf
  map_act := fun u n v => by
    simp only [LinearEquiv.ofBijective_apply, WeakModule.act_def]
    exact f.property u n v

/-- A bijective module map is an isomorphism, with the given map as its `hom`. -/
def isoOfBijective {X Y : Ordinary W} (f : X ⟶ Y) (hf : Function.Bijective f.val) : X ≅ Y :=
  Ordinary.isoOfModuleEquiv (moduleEquivOfBijective f hf)

theorem isoOfBijective_hom {X Y : Ordinary W} (f : X ⟶ Y) (hf : Function.Bijective f.val) :
    (isoOfBijective f hf).hom = f :=
  Ordinary.hom_ext _ _ (fun _ => rfl)

/-- `tensorHom` is linear in the first argument (scalars). -/
theorem tensorHom_smul_left (F : FusionChoice W) {X X' Y Y' : Ordinary W} (c : ℂ)
    (f : X ⟶ X') (g : Y ⟶ Y') : tensorHom F (c • f) g = c • tensorHom F f g := by
  apply tensor_hom_ext F
  intro n x y
  rw [tensorHom_intertwiner, Ordinary.smul_val_apply, Ordinary.smul_val_apply,
    tensorHom_intertwiner, map_smul, LinearMap.smul_apply]
  rfl

end Module

section Family

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]

theorem famObj_id_ne_zero (D : VOA.ModularData W ι) (y : ι) : (𝟙 (famObj D y)) ≠ 0 := by
  haveI : Nontrivial (D.Mfam y).carrier := (D.Mfam y).irreducible.1
  obtain ⟨v, hv⟩ := exists_ne (0 : (D.Mfam y).carrier)
  intro h
  apply hv
  have := congrArg (fun f : famObj D y ⟶ famObj D y => f.val v) h
  simpa using this

/-- **Schur** for family members. -/
theorem endo_scalar (D : VOA.ModularData W ι) (y : ι) (f : famObj D y ⟶ famObj D y) :
    ∃ s : ℂ, f = s • 𝟙 (famObj D y) := by
  have hid0 : (LinearMap.id : (lwOf D y).carrier →ₗ[ℂ] (lwOf D y).carrier) ≠ 0 := by
    intro h
    apply famObj_id_ne_zero D y
    exact Ordinary.hom_ext _ _ (fun v => LinearMap.congr_fun h v)
  obtain ⟨s, hs⟩ := exists_smul_eq_of_hom (lwOf_irreducible D y) (lwOf_irreducible D y)
    (f := (f.val : (lwOf D y).carrier →ₗ[ℂ] (lwOf D y).carrier)) f.property
    (fun _ _ _ => rfl) hid0
  refine ⟨s, Ordinary.hom_ext _ _ (fun v => ?_)⟩
  rw [Ordinary.smul_val_apply, ← hs]
  rfl

theorem smul_id_cancel (D : VOA.ModularData W ι) (y : ι) {p q : ℂ}
    (h : p • 𝟙 (famObj D y) = q • 𝟙 (famObj D y)) : p = q := by
  by_contra hpq
  apply famObj_id_ne_zero D y
  have h2 : (p - q) • 𝟙 (famObj D y) = 0 := by rw [sub_smul, h, sub_self]
  have h3 := congrArg (fun f => (p - q)⁻¹ • f) h2
  simpa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hpq)] using h3

/-- `Hom(M_y, M_z)` has dimension `δ_{yz}` for an irredundant family. -/
theorem finrank_hom_fam (D : VOA.ModularData W ι) (hirr : Irredundant D.Mfam) (y z : ι) :
    FiniteDimensional ℂ (famObj D y ⟶ famObj D z) ∧
      Module.finrank ℂ (famObj D y ⟶ famObj D z) = if y = z then 1 else 0 := by
  obtain ⟨hfd, hle⟩ := finite_and_finrank_homSpace_le_one (lwOf_irreducible D y)
    (lwOf_irreducible D z)
  haveI : FiniteDimensional ℂ (famObj D y ⟶ famObj D z) := hfd
  refine ⟨hfd, ?_⟩
  split_ifs with hyz
  · subst hyz
    have hpos : 0 < Module.finrank ℂ (famObj D y ⟶ famObj D y) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨𝟙 _, famObj_id_ne_zero D y⟩
    exact le_antisymm hle hpos
  · rw [Module.finrank_eq_zero_iff_of_free]
    refine ⟨fun f g => ?_⟩
    have hz : ∀ f : famObj D y ⟶ famObj D z, f = 0 := by
      intro f
      by_contra hf
      have hf' : f.val ≠ 0 := fun h => hf (Ordinary.hom_ext _ _ (fun v => LinearMap.congr_fun h v))
      have hb := bijective_of_hom (D.Mfam y).irreducible (D.Mfam z).irreducible f.property hf'
      exact hyz (hirr y z ⟨moduleEquivOfBijective f hb⟩)
    rw [hz f, hz g]

end Family

/-! ## §3 The transfer is (zig-zag scalar) × (multiplicity) -/

section Transfer

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]
  (F : FusionChoice W) (H : OrdinaryFourPointInput F) {D : VOA.ModularData W ι} {a b : ι}

/-- The zig-zag endomorphism `λ⁻¹ ≫ (η ▷ M_b) ≫ α ≫ (M_b ◁ ε) ≫ ρ` of `M_b`. -/
def zigzag (c : TransferChoice F D a b) : famObj D b ⟶ famObj D b :=
  (leftUnitor F (famObj D b)).inv ≫ tensorHom F c.η (𝟙 (famObj D b)) ≫
    (evalAssoc F H (famObj D b) (famObj D a) (famObj D b)).hom ≫
    tensorHom F (𝟙 (famObj D b)) c.ε ≫ (rightUnitor F (famObj D b)).hom

/-- **The B-cycle transfer factors through the zig-zag** (monoidal coherence in the proved
monoidal category). -/
theorem bTransfer_eq_zigzag (hV : StronglyRational W) (c : TransferChoice F D a b) (x : ι)
    (j : Fin (c.r x)) :
    bTransfer F H c x j =
      c.inc x j ≫ tensorHom F (zigzag F H c) (𝟙 (famObj D x)) ≫ c.proj x j := by
  letI : MonoidalCategory (Ordinary W) := monoidalCategoryOfStronglyRational_pbw F hV
  exact transfer_zigzag (C := Ordinary W) (famObj D a) (famObj D b) (famObj D x)
    (famObj D (c.lab x j)) c.ε c.η (c.inc x j) (c.proj x j)

/-- With `Z = s • 𝟙`: `bTransfer = s • (inc ≫ proj)`. -/
theorem bTransfer_eq_smul (hV : StronglyRational W) (c : TransferChoice F D a b) (s : ℂ)
    (hs : zigzag F H c = s • 𝟙 (famObj D b)) (x : ι) (j : Fin (c.r x)) :
    bTransfer F H c x j = s • (c.inc x j ≫ c.proj x j) := by
  rw [bTransfer_eq_zigzag F H hV c x j, hs, tensorHom_smul_left, TensorCat.tensorHom_id,
    Linear.smul_comp, Category.id_comp, Linear.comp_smul]

end Transfer

/-! ## §4 The multiplicity through a split presentation -/

section Trace

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- **The fusion rule through any split presentation**: if `Σ_j proj_j ≫ inc_j = 𝟙` on
`M_b ⊠ M_x` and `inc_j ≫ proj_j = c_j • 𝟙`, then `N_{bx}^z = Σ_{lab j = z} c_j` (trace of the
identity of `Hom(M_b ⊠ M_x, M_z)`, cyclicity, Schur). -/
theorem famFusion_eq_sum (hV : Nice W) (F : FusionChoice W) (D : VOA.ModularData W ι)
    (hirr : Irredundant D.Mfam) (b x z : ι) {r : ℕ} (lab : Fin r → ι)
    (inc : ∀ j, famObj D (lab j) ⟶ tensorObj F (famObj D b) (famObj D x))
    (proj : ∀ j, tensorObj F (famObj D b) (famObj D x) ⟶ famObj D (lab j))
    (htot : ∑ j, proj j ≫ inc j = 𝟙 _) (cj : Fin r → ℂ)
    (hcj : ∀ j, inc j ≫ proj j = cj j • 𝟙 _) :
    (famFusion D b x z : ℂ) = ∑ j, if lab j = z then cj j else 0 := by
  -- `Hom(M_b ⊠ M_x, M_z)` is the intertwiner space
  let e : (tensorObj F (famObj D b) (famObj D x) ⟶ famObj D z) ≃ₗ[ℂ]
      IntertwiningOperator (D.Mfam b).isMod (D.Mfam x).isMod (D.Mfam z).isMod :=
    homEquiv ((F (famObj D b) (famObj D x)).universal (D.Mfam z).carrier (D.Mfam z).isMod)
  haveI : FiniteDimensional ℂ (intertwiningSpace (D.Mfam b).isMod (D.Mfam x).isMod
      (D.Mfam z).isMod) := VOA.Huang.ModuleC2.finiteDimensional_fusion_of_nice hV D b x z
  haveI : FiniteDimensional ℂ (tensorObj F (famObj D b) (famObj D x) ⟶ famObj D z) :=
    LinearEquiv.finiteDimensional e.symm
  have hrank : Module.finrank ℂ (tensorObj F (famObj D b) (famObj D x) ⟶ famObj D z) =
      famFusion D b x z := e.finrank_eq
  -- the decomposition of the identity
  have hid : (LinearMap.id : (tensorObj F (famObj D b) (famObj D x) ⟶ famObj D z) →ₗ[ℂ]
        (tensorObj F (famObj D b) (famObj D x) ⟶ famObj D z)) =
      ∑ j, (Linear.leftComp ℂ (famObj D z) (proj j)).comp
        (Linear.leftComp ℂ (famObj D z) (inc j)) := by
    ext1 f
    rw [LinearMap.sum_apply]
    simp only [LinearMap.comp_apply, Linear.leftComp_apply, LinearMap.id_apply]
    simp_rw [← Category.assoc]
    rw [← Preadditive.sum_comp, htot, Category.id_comp]
  have htr := congrArg
    (LinearMap.trace ℂ (tensorObj F (famObj D b) (famObj D x) ⟶ famObj D z)) hid
  rw [LinearMap.trace_id, map_sum, hrank] at htr
  rw [htr]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  obtain ⟨hfd, hfr⟩ := finrank_hom_fam D hirr (lab j) z
  haveI := hfd
  rw [LinearMap.trace_comp_comm']
  have hBA : (Linear.leftComp ℂ (famObj D z) (inc j)).comp
      (Linear.leftComp ℂ (famObj D z) (proj j)) = cj j • LinearMap.id := by
    ext1 g
    simp only [LinearMap.comp_apply, Linear.leftComp_apply, LinearMap.smul_apply,
      LinearMap.id_apply]
    rw [← Category.assoc, hcj j, Linear.smul_comp, Category.id_comp]
  rw [hBA, map_smul, LinearMap.trace_id, hfr, smul_eq_mul]
  split_ifs <;> simp

end Trace

/-! ## §5 Existence of the genus-zero choices -/

section Exists

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- Finite split presentations of any ordinary module by members of a complete family
(strong rationality; `finiteTargets_of_stronglyRational_pbw`). -/
theorem exists_split (hV : StronglyRational W) (D : VOA.ModularData W ι)
    (hcomp : Complete D.Mfam) (N : Ordinary W) :
    ∃ (r : ℕ) (lab : Fin r → ι) (inc : ∀ j, famObj D (lab j) ⟶ N)
      (proj : ∀ j, N ⟶ famObj D (lab j)), ∑ j, proj j ≫ inc j = 𝟙 N := by
  let e := Fintype.equivFin ι
  let R : ULift.{u} (Fin (Fintype.card ι)) → LWModule W := fun k => lwOf D (e.symm k.down)
  have hR : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ k, LWModule.Iso W Q (R k) := by
    intro Q hQ
    obtain ⟨i, hi⟩ := hcomp ⟨Q.carrier, Q.isMod, hQ⟩
    refine ⟨⟨e i⟩, ?_⟩
    change Nonempty (ModuleEquiv W Q.isMod (D.Mfam (e.symm (e i))).isMod)
    rw [e.symm_apply_apply]
    exact hi
  obtain ⟨r, lab, inc, proj, htot⟩ :=
    finiteTargets_of_stronglyRational_pbw hV R hR N.carrier N.isMod
  refine ⟨r, fun j => e.symm (lab j).down, fun j => inc j, fun j => proj j, ?_⟩
  apply Ordinary.hom_ext
  intro v
  rw [Ordinary.sum_val_apply]
  exact htot v

/-- A nonzero morphism `M_a ⊠ M_b → V` when `N_{ab}^{v0} ≠ 0`. -/
theorem exists_ne_zero_to_vacuum (hV : Nice W) (F : FusionChoice W) (D : VOA.ModularData W ι)
    (v0 : ι) (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))) (a b : ι)
    (h : famFusion D a b v0 ≠ 0) :
    ∃ ε : tensorObj F (famObj D a) (famObj D b) ⟶ vacuumObject, ε ≠ 0 := by
  obtain ⟨e0⟩ := hv0
  haveI := VOA.Huang.ModuleC2.finiteDimensional_fusion_of_nice hV D a b v0
  have hpos : 0 < Module.finrank ℂ
      (intertwiningSpace (D.Mfam a).isMod (D.Mfam b).isMod (D.Mfam v0).isMod) :=
    Nat.pos_of_ne_zero h
  obtain ⟨Y, hY⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hY' : intertwiningEquivRight e0 Y ≠ 0 := by
    rwa [ne_eq, LinearEquiv.map_eq_zero_iff]
  let E := homEquiv ((F (famObj D a) (famObj D b)).universal 𝒱 (adjointModule W))
  exact ⟨E.symm (intertwiningEquivRight e0 Y),
    fun h0 => hY' ((LinearEquiv.map_eq_zero_iff E.symm).mp h0)⟩

/-- A nonzero morphism `V → M_b ⊠ M_a` when `N_{ba}^{v0} ≠ 0` (split off the vacuum summand). -/
theorem exists_ne_zero_from_vacuum (hV : Nice W) (F : FusionChoice W) (D : VOA.ModularData W ι)
    (hcomp : Complete D.Mfam) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))) (b a : ι)
    (h : famFusion D b a v0 ≠ 0) :
    ∃ η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a), η ≠ 0 := by
  obtain ⟨ε, hε⟩ := exists_ne_zero_to_vacuum hV F D v0 hv0 b a h
  obtain ⟨r, lab, inc, proj, htot⟩ :=
    exists_split hV.1 D hcomp (tensorObj F (famObj D b) (famObj D a))
  have hex : ∃ j, inc j ≫ ε ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hε
    rw [← Category.id_comp ε, ← htot, Preadditive.sum_comp]
    exact Finset.sum_eq_zero (fun j _ => by rw [Category.assoc, hall j, Limits.comp_zero])
  obtain ⟨j, hj⟩ := hex
  obtain ⟨e0⟩ := hv0
  let I0 : famObj D v0 ≅ vacuumObject := Ordinary.isoOfModuleEquiv e0
  let φ : famObj D (lab j) ⟶ famObj D v0 := inc j ≫ ε ≫ I0.inv
  have hφ : φ ≠ 0 := by
    intro h0
    apply hj
    have hφI : φ ≫ I0.hom = inc j ≫ ε := by
      simp only [φ, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hφI, h0, Limits.zero_comp]
  have hφ' : φ.val ≠ 0 := fun h0 =>
    hφ (Ordinary.hom_ext _ _ (fun v => LinearMap.congr_fun h0 v))
  have hb := bijective_of_hom (D.Mfam (lab j)).irreducible (D.Mfam v0).irreducible
    φ.property hφ'
  let I := isoOfBijective φ hb
  have hI : I.inv ≫ φ = 𝟙 _ := by
    rw [← isoOfBijective_hom φ hb]
    exact I.inv_hom_id
  refine ⟨I0.inv ≫ I.inv ≫ inc j, ?_⟩
  intro h0
  apply famObj_id_ne_zero D v0
  have hcomp' : I0.hom ≫ (I0.inv ≫ I.inv ≫ inc j) ≫ ε ≫ I0.inv = 𝟙 (famObj D v0) := by
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_assoc]
    exact hI
  rw [← hcomp', h0, Limits.zero_comp, Limits.comp_zero]

end Exists

/-! ## §6 The genus-zero input -/

/-- **The B-cycle matrix is the zig-zag scalar times the fusion matrix**:
if `zigzag = s • 𝟙` then `transferMatrix c β x z = s · N_{bx}^z`. -/
theorem transferMatrix_eq_zigzag_scalar {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {W : VertexOperatorAlgebra 𝒱} {ι : Type w} [Fintype ι] [DecidableEq ι] (hNice : Nice W)
    (D : VOA.ModularData W ι) (hirr : Irredundant D.Mfam) (F : FusionChoice W)
    (H : OrdinaryFourPointInput F) {a b : ι} (c : TransferChoice F D a b)
    (β : ∀ x, Fin (c.r x) → ℂ) (hβ : IsTransferScalar F H c β) (s : ℂ)
    (hs : zigzag F H c = s • 𝟙 (famObj D b)) (x z : ι) :
    transferMatrix c β x z = s * (famFusion D b x z : ℂ) := by
  choose cj hcj using fun j => endo_scalar D (c.lab x j) (c.inc x j ≫ c.proj x j)
  have hβj : ∀ j, β x j = s * cj j := by
    intro j
    apply smul_id_cancel D (c.lab x j)
    rw [← hβ x j, bTransfer_eq_smul F H hNice.1 c s hs x j, hcj j, smul_smul]
  rw [famFusion_eq_sum hNice F D hirr b x z (c.lab x) (c.inc x) (c.proj x) (c.total x) cj hcj,
    Finset.mul_sum]
  unfold transferMatrix
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> simp [hβj]

/-- **(G0a) proved**: `transferMatrix c β x z = s · N_{bx}^z`, `s` the zig-zag scalar. -/
theorem transferTraceInput_pbw : TransferTraceInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp v0 hv0 F H a b c β hβ
  obtain ⟨s, hs⟩ := endo_scalar D b (zigzag F H c)
  exact ⟨s, transferMatrix_eq_zigzag_scalar hNice D hirr F H c β hβ s hs⟩

/-- **(G0b) proved**: the choices exist (`a = b'`, `F` the library fusion choice). -/
theorem transferChoiceExists_pbw : TransferChoiceExists.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp v0 hv0
  let F := fusionChoice_pbw hNice.1
  let H := ordinaryFourPointInput_pbw F hNice.1
  refine ⟨F, H, fun b => ?_⟩
  obtain ⟨σ, hσ⟩ := vacuumFusionInput 𝒱 W hNice ι D hZ hirr hcomp v0 hv0
  have h1 : famFusion D b (σ b) v0 ≠ 0 := by
    rw [hσ b (σ b), if_pos rfl]
    exact one_ne_zero
  have h2 : famFusion D (σ b) b v0 ≠ 0 := by
    rw [famFusion, BraidingSkew.fusionRule_swap (D.Mfam b).isMod (D.Mfam (σ b)).isMod
      (D.Mfam v0).isMod]
    exact h1
  obtain ⟨ε, hε⟩ := exists_ne_zero_to_vacuum hNice F D v0 hv0 (σ b) b h2
  obtain ⟨η, hη⟩ := exists_ne_zero_from_vacuum hNice F D hcomp v0 hv0 b (σ b) h1
  choose r lab inc proj htot using fun x =>
    exists_split hNice.1 D hcomp (tensorObj F (famObj D b) (famObj D x))
  let c : TransferChoice F D (σ b) b := ⟨ε, hε, η, hη, r, lab, inc, proj, htot⟩
  choose β hβ using fun x j => endo_scalar D (c.lab x j) (bTransfer F H c x j)
  exact ⟨σ b, c, β, hβ⟩

/-- **(G0) proved for nice `W`.** -/
theorem genusZeroTransferInput_pbw : GenusZeroTransferInput.{u, w} :=
  ⟨transferTraceInput_pbw, transferChoiceExists_pbw⟩

end VOA.Huang.VerlindeTransport
