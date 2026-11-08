import VOA.Moonshine.MoonshineCNBorcherdsTensorEnveloping
import VOA.Moonshine.MoonshineCNRelativePBW
import VOA.Moonshine.MoonshineCNTwistedTransfer
import Mathlib.LinearAlgebra.TensorAlgebra.Basis

/-!
# PBW coordinates, word coordinates, and diagonal symmetries

For a Lie algebra `L` with a linearly ordered basis `Y`, the relative PBW theorem of the repository
(induction from the zero subalgebra) gives a linear isomorphism `U(L) ≃ (Multiset A →₀ ℂ)` sending
every sorted monomial to its multiset (`pbwCoordinates`, `pbwCoordinates_sorted`).  For a subspace
`S` with a basis `Z`, the tensor algebra `T(S)` has the word basis.  When `T(S) → U(L)` is bijective
these combine into `wordPBWEquiv : (List I →₀ ℂ) ≃ (Multiset A →₀ ℂ)`.

A Lie endomorphism `φ` of `L` preserving `S` and diagonal in both bases (`φ Y_a = κ_a Y_a`,
`φ Z_i = ν_i Z_i`) acts on monomials by the products of its eigenvalues, so `wordPBWEquiv`
intertwines the two diagonal operators (`wordPBWEquiv_diag`).
-/

noncomputable section

open scoped TensorProduct

namespace VOA.Moonshine.ConwayNorton

open Finsupp Module

/-- `Π (κ a • z a) = (Π κ a) • Π z a` in an algebra. -/
theorem list_prod_map_smul {R : Type*} [Semiring R] [Algebra ℂ R] {X : Type*} (l : List X)
    (κ : X → ℂ) (z : X → R) :
    (l.map fun a => κ a • z a).prod = (l.map κ).prod • (l.map z).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, ih, mul_smul_comm, smul_mul_assoc, smul_smul]
      rw [mul_comm (List.map κ l).prod]

theorem finsuppDiag_domLCongr {X X' : Type*} (e : X ≃ X') (κ : X → ℂ) (v : X →₀ ℂ) :
    Finsupp.domLCongr (R := ℂ) e (finsuppDiag κ v) =
      finsuppDiag (κ ∘ e.symm) (Finsupp.domLCongr (R := ℂ) e v) := by
  ext y
  simp [finsuppDiag_apply, Finsupp.domLCongr_apply]

/-! ### PBW coordinates -/

section PBW

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] {A : Type*} [LinearOrder A] (Y : Basis A ℂ L)

/-- The basis of `⊤` induced by `Y`. -/
def topBasis : Basis A ℂ (⊤ : Submodule ℂ L) := Y.map (LinearEquiv.ofTop ⊤ rfl).symm

omit [LinearOrder A] in
theorem topBasis_apply (a : A) : ((topBasis Y a : (⊤ : Submodule ℂ L)) : L) = Y a := by
  simp [topBasis]

omit [LinearOrder A] in
theorem bot_isCompl_top :
    IsCompl (⊥ : LieSubalgebra ℂ L).toSubmodule (⊤ : Submodule ℂ L) := by
  rw [LieSubalgebra.bot_toSubmodule]
  exact isCompl_bot_top

/-- The zero representation of the zero subalgebra on `ℂ`. -/
abbrev zeroBottomRep : (⊥ : LieSubalgebra ℂ L) →ₗ⁅ℂ⁆ Module.End ℂ ℂ := 0

omit [LinearOrder A] in
theorem balancing_bot_eq_bot :
    PBWTheorem.balancing (⊥ : LieSubalgebra ℂ L) (zeroBottomRep (L := L)) = ⊥ := by
  rw [PBWTheorem.balancing, Submodule.span_eq_bot]
  rintro _ ⟨y, x, u, rfl⟩
  have hx : (x : L) = 0 := (LieSubalgebra.mem_bot _).mp x.2
  simp [hx]

/-- `U(L) ≃ (U(L) ⊗ ℂ) / 0`, the induced module from the zero subalgebra. -/
def envelopingInducedEquiv :
    UniversalEnvelopingAlgebra ℂ L ≃ₗ[ℂ]
      relativeInducedSpace (⊥ : LieSubalgebra ℂ L) (zeroBottomRep (L := L)) :=
  (TensorProduct.rid ℂ _).symm ≪≫ₗ (Submodule.quotEquivOfEqBot _ balancing_bot_eq_bot).symm

omit [LinearOrder A] in
theorem envelopingInducedEquiv_apply (x : UniversalEnvelopingAlgebra ℂ L) :
    envelopingInducedEquiv x = Submodule.Quotient.mk (x ⊗ₜ[ℂ] (1 : ℂ)) := by
  simp [envelopingInducedEquiv, Submodule.quotEquivOfEqBot_symm_apply]

/-- **PBW coordinates** of `U(L)` in the ordered basis `Y`. -/
def pbwCoordinates : UniversalEnvelopingAlgebra ℂ L ≃ₗ[ℂ] (Multiset A →₀ ℂ) :=
  envelopingInducedEquiv ≪≫ₗ
    relativePBWEquiv (⊥ : LieSubalgebra ℂ L) zeroBottomRep bot_isCompl_top (topBasis Y)

omit [LinearOrder A] in
theorem relativeInducedWord_bot (l : List A) (u : ℂ) :
    relativeInducedWord (⊥ : LieSubalgebra ℂ L) zeroBottomRep (topBasis Y) l u =
      Submodule.Quotient.mk
        ((l.map fun a => UniversalEnvelopingAlgebra.ι ℂ (Y a)).prod ⊗ₜ[ℂ] u) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [relativeInducedWord_cons, ih, List.map_cons, List.prod_cons, topBasis_apply]
      rfl

/-- Sorted monomials have the coordinates of their multiset. -/
theorem pbwCoordinates_sorted (l : List A) (hl : l.Pairwise (· ≤ ·)) :
    pbwCoordinates Y (l.map fun a => UniversalEnvelopingAlgebra.ι ℂ (Y a)).prod =
      single (l : Multiset A) 1 := by
  have h := relativePBWCoordinates_word (⊥ : LieSubalgebra ℂ L) zeroBottomRep bot_isCompl_top
    (topBasis Y) l hl 1
  rw [relativeInducedWord_bot] at h
  rw [← h]
  rfl

theorem pbwCoordinates_symm_single (m : Multiset A) :
    (pbwCoordinates Y).symm (single m 1) =
      ((m.sort (· ≤ ·)).map fun a => UniversalEnvelopingAlgebra.ι ℂ (Y a)).prod := by
  rw [LinearEquiv.symm_apply_eq, pbwCoordinates_sorted Y _ (Multiset.pairwise_sort m (· ≤ ·)),
    Multiset.sort_eq]

/-- A Lie endomorphism diagonal in `Y` acts on PBW coordinates diagonally. -/
theorem pbwCoordinates_envelopingMap (φ : L →ₗ⁅ℂ⁆ L) (κ : A → ℂ)
    (hY : ∀ a, φ (Y a) = κ a • Y a) (x : UniversalEnvelopingAlgebra ℂ L) :
    pbwCoordinates Y (envelopingMap φ x) =
      finsuppDiag (fun m => (m.map κ).prod) (pbwCoordinates Y x) := by
  have key : ∀ m : Multiset A, envelopingMap φ ((pbwCoordinates Y).symm (single m 1)) =
      (m.map κ).prod • (pbwCoordinates Y).symm (single m 1) := by
    intro m
    rw [pbwCoordinates_symm_single, map_list_prod, List.map_map]
    have hfun : (envelopingMap φ ∘ fun a => UniversalEnvelopingAlgebra.ι ℂ (Y a)) =
        fun a => κ a • UniversalEnvelopingAlgebra.ι ℂ (Y a) := by
      funext a
      simp [envelopingMap, hY]
    rw [hfun, list_prod_map_smul]
    congr 1
    conv_rhs => rw [← Multiset.sort_eq m (· ≤ ·)]
    rw [Multiset.map_coe, Multiset.prod_coe]
  obtain ⟨v, rfl⟩ := (pbwCoordinates Y).symm.surjective x
  rw [LinearEquiv.apply_symm_apply]
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single m c =>
      rw [show single m c = c • single m (1 : ℂ) by simp, map_smul, map_smul, key, map_smul,
        map_smul, LinearEquiv.apply_symm_apply, map_smul, finsuppDiag_single, mul_one]
      simp [Finsupp.smul_single]

end PBW

/-! ### Word coordinates -/

section Words

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {I : Type*} (Z : Basis I ℂ M)

theorem tensorAlgebra_basis_apply (w : FreeMonoid I) :
    Z.tensorAlgebra w = (w.toList.map fun i => TensorAlgebra.ι ℂ (Z i)).prod := by
  have h1 : FreeAlgebra.basisFreeMonoid ℂ I w = (w.toList.map (FreeAlgebra.ι ℂ)).prod := by
    rw [FreeAlgebra.basisFreeMonoid, Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
    change (MonoidAlgebra.lift ℂ (FreeAlgebra ℂ I) (FreeMonoid I)
      (FreeMonoid.lift (FreeAlgebra.ι ℂ))) (MonoidAlgebra.single w 1) = _
    rw [MonoidAlgebra.lift_single, one_smul, FreeMonoid.lift_apply]
  rw [Module.Basis.tensorAlgebra, Module.Basis.map_apply, h1]
  simp [map_list_prod, Function.comp_def]

/-- A linear endomorphism diagonal in `Z` acts on word coordinates diagonally. -/
theorem tensorAlgebra_repr_lift_diag (h : M →ₗ[ℂ] M) (ν : I → ℂ) (hh : ∀ i, h (Z i) = ν i • Z i)
    (x : TensorAlgebra ℂ M) :
    Z.tensorAlgebra.repr (TensorAlgebra.lift ℂ ((TensorAlgebra.ι ℂ).comp h) x) =
      finsuppDiag (fun w : FreeMonoid I => (w.toList.map ν).prod) (Z.tensorAlgebra.repr x) := by
  have hlin : Z.tensorAlgebra.repr.toLinearMap ∘ₗ
      (TensorAlgebra.lift ℂ ((TensorAlgebra.ι ℂ).comp h)).toLinearMap =
      finsuppDiag (fun w : FreeMonoid I => (w.toList.map ν).prod) ∘ₗ
        Z.tensorAlgebra.repr.toLinearMap := by
    refine Z.tensorAlgebra.ext fun w => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      LinearEquiv.coe_coe, Basis.repr_self, finsuppDiag_single, mul_one]
    rw [tensorAlgebra_basis_apply, map_list_prod, List.map_map]
    have hfun : ((TensorAlgebra.lift ℂ ((TensorAlgebra.ι ℂ).comp h)) ∘
        fun i => TensorAlgebra.ι ℂ (Z i)) = fun i => ν i • TensorAlgebra.ι ℂ (Z i) := by
      funext i
      simp [hh]
    rw [hfun, list_prod_map_smul, ← tensorAlgebra_basis_apply, map_smul, Basis.repr_self,
      Finsupp.smul_single, smul_eq_mul, mul_one]
  exact LinearMap.congr_fun hlin x

end Words

/-! ### The word–PBW isomorphism -/

section WordPBW

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] (S : Submodule ℂ L)
  (hbij : Function.Bijective (tensorGeneratorToEnveloping S))
  {A : Type*} [LinearOrder A] (Y : Basis A ℂ L) {I : Type*} (Z : Basis I ℂ S)

/-- Words in a basis of `S` to multisets in a basis of `L`, through `T(S) ≅ U(L)` and PBW. -/
def wordPBWEquiv : (List I →₀ ℂ) ≃ₗ[ℂ] (Multiset A →₀ ℂ) :=
  Finsupp.domLCongr (R := ℂ) (M := ℂ) FreeMonoid.toList.symm ≪≫ₗ Z.tensorAlgebra.repr.symm ≪≫ₗ
    LinearEquiv.ofBijective (tensorGeneratorToEnveloping S).toLinearMap hbij ≪≫ₗ pbwCoordinates Y

/-- **Diagonal intertwining.**  A Lie endomorphism preserving `S`, diagonal in both bases, is
intertwined by `wordPBWEquiv` with the products of its eigenvalues on words and on multisets. -/
theorem wordPBWEquiv_diag (φ : L →ₗ⁅ℂ⁆ L) (hφ : ∀ u ∈ S, φ u ∈ S) (κ : A → ℂ) (ν : I → ℂ)
    (hY : ∀ a, φ (Y a) = κ a • Y a) (hZ : ∀ i, φ (Z i : L) = ν i • (Z i : L))
    (v : List I →₀ ℂ) :
    wordPBWEquiv S hbij Y Z (finsuppDiag (fun w => (w.map ν).prod) v) =
      finsuppDiag (fun m => (m.map κ).prod) (wordPBWEquiv S hbij Y Z v) := by
  set h : S →ₗ[ℂ] S := φ.toLinearMap.restrict (p := S) (q := S) hφ with hhdef
  have hh : ∀ i, h (Z i) = ν i • Z i := fun i => Subtype.ext (by simp [hhdef, hZ])
  set t := Z.tensorAlgebra.repr.symm
    (Finsupp.domLCongr (R := ℂ) (M := ℂ) FreeMonoid.toList.symm v) with ht
  have h1 : Z.tensorAlgebra.repr.symm (Finsupp.domLCongr (R := ℂ) (M := ℂ) FreeMonoid.toList.symm
      (finsuppDiag (fun w => (w.map ν).prod) v)) = tensorGeneratorMap S h t := by
    rw [finsuppDiag_domLCongr, LinearEquiv.symm_apply_eq]
    rw [tensorGeneratorMap, tensorAlgebra_repr_lift_diag Z h ν hh, ht,
      LinearEquiv.apply_symm_apply]
    rfl
  simp only [wordPBWEquiv, LinearEquiv.trans_apply]
  rw [h1, ← ht, LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply,
    AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
    tensorGeneratorToEnveloping_natural S S φ hφ t, pbwCoordinates_envelopingMap Y φ κ hY]

end WordPBW

end VOA.Moonshine.ConwayNorton
