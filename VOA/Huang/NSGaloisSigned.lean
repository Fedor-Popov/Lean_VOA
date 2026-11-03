/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.NgSchauenburgSRelations
import VOA.Huang.NSFinishGalois
import VOA.Huang.DLNBridge

/-!
# Galois action on the categorical `S`-matrix: the Coste–Gannon signed permutation

For a modular category in the Ng–Schauenburg formalization (`SphericalFusion` + `Modular`), with
categorical `S`-matrix `S` (convention (1.6), `categoricalS`) and dimensions `d_k`:

* `fusionChar F k i = S_{ik} / d_k` — the fusion characters; `fusionChar_unit`, `fusionChar_mul`;
* `exists_fusionChar_eq` — **every** character of the fusion ring is a column character;
* `fusionChar_injective`; `fusionChar_dual` (`χ_{k*}(i) = χ_k(i*)`);
* `galoisPerm σ` — for a field automorphism `σ` of `ℂ`, the permutation with
  `σ ∘ χ_k = χ_{π k}` (`galoisPerm_spec`), and `galoisPerm_dual`;
* `galois_signed` — for `s = a S` with `(a² D²)² = 1` (`D² = globalDimension`), the matrix
  `G = galoisSigned σ a`, `G_{jk} = ε_j [π j = k]` with `ε_j = ±1`, is a signed permutation and
  `σ(s) = G s`, `σ(s) G = s` (DLN (4.2)–(4.4), [dBG, CG1]).

No unitarity is used; the normalization comes from `S² = D² C` (`categoricalS_sq`) and the
orthogonality `Σ_k S_{ik} S_{jk} = [j = i*] D²`.
-/

noncomputable section
set_option linter.unusedSectionVars false

namespace VOA.Huang.NSGalois

open CategoryTheory MonoidalCategory Limits BraidedCategory
open VOA.Huang.NgSchauenburg VOA.Huang.NSFinish VOA.Huang.DLNBridge Matrix

universe v u

attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

section Characters

variable (F : SphericalFusion C) (M : Modular F)

/-- The fusion character of the column `k`: `χ_k(i) = S_{ik} / d_k`. -/
def fusionChar (k i : F.Label) : ℂ := categoricalS F i k / F.dimension (F.simple k)

include M in
theorem fusionChar_unit (k : F.Label) : fusionChar F k F.unitLabel = 1 := by
  rw [fusionChar, categoricalS_unit_left F M.toRibbon, div_self (F.dimension_simple_ne_zero k)]

theorem fusionChar_mul (k i j : F.Label) :
    fusionChar F k i * fusionChar F k j =
      ∑ r, (F.fusionMultiplicity i j (F.simple r) : ℂ) * fusionChar F k r := by
  classical
  have h := congrFun (congrFun (fusionMatrix_mul_categoricalS F i) j) k
  rw [Matrix.mul_diagonal, Matrix.mul_apply] at h
  have hd := F.dimension_simple_ne_zero k
  simp only [fusionChar, fusionMatrix] at h ⊢
  calc categoricalS F i k / F.dimension (F.simple k) *
        (categoricalS F j k / F.dimension (F.simple k)) =
        (categoricalS F j k * (categoricalS F i k / F.dimension (F.simple k))) /
          F.dimension (F.simple k) := by ring
    _ = (∑ r, (F.fusionMultiplicity i j (F.simple r) : ℂ) * categoricalS F r k) /
          F.dimension (F.simple k) := by rw [h]
    _ = _ := by rw [Finset.sum_div]; exact Finset.sum_congr rfl fun r _ => by ring

include M in
/-- `χ_{k*}(i) = χ_k(i*)`. -/
theorem fusionChar_dual (k i : F.Label) :
    fusionChar F (F.dualLabel k) i = fusionChar F k (F.dualLabel i) := by
  simp only [fusionChar, F.dimension_dualLabel]
  rw [categoricalS_dual_left F M.toRibbon]

include M in
/-- **Completeness of the fusion characters**: every character of the fusion ring is a
column character. -/
theorem exists_fusionChar_eq (φ : F.Label → ℂ) (h0 : φ F.unitLabel = 1)
    (hm : ∀ i j, φ i * φ j = ∑ r, (F.fusionMultiplicity i j (F.simple r) : ℂ) * φ r) :
    ∃ k, ∀ i, φ i = fusionChar F k i := by
  classical
  set S := categoricalS F with hSdef
  have hS : IsUnit S.det := isUnit_iff_ne_zero.mpr (by convert M.nondegenerate)
  set c := S⁻¹ *ᵥ φ with hc
  have hφ : S *ᵥ c = φ := by rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hS,
    Matrix.one_mulVec]
  have hinj : ∀ u w : F.Label → ℂ, S *ᵥ u = S *ᵥ w → u = w := by
    intro u w h
    have := congrArg (fun z => S⁻¹ *ᵥ z) h
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hS, Matrix.one_mulVec] using this
  have hc0 : ∃ k, c k ≠ 0 := by
    by_contra hall
    push_neg at hall
    have : c = 0 := funext hall
    rw [this, Matrix.mulVec_zero] at hφ
    have := congrFun hφ F.unitLabel
    rw [h0] at this
    exact zero_ne_one this
  obtain ⟨k, hk⟩ := hc0
  refine ⟨k, fun i => ?_⟩
  -- `N_i φ = φ_i φ` and `N_i S = S diag(χ(i))`
  have hN : fusionMatrix F i *ᵥ φ = φ i • φ := by
    ext j
    rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hm]
    rfl
  have hD := fusionMatrix_mul_categoricalS F i
  have h1 : S *ᵥ (Matrix.diagonal (fun m => categoricalS F i m / F.dimension (F.simple m)) *ᵥ c) =
      S *ᵥ (φ i • c) := by
    calc S *ᵥ (Matrix.diagonal (fun m => categoricalS F i m / F.dimension (F.simple m)) *ᵥ c)
        = (categoricalS F * Matrix.diagonal (fun m => categoricalS F i m /
            F.dimension (F.simple m))) *ᵥ c := by rw [Matrix.mulVec_mulVec]
      _ = (fusionMatrix F i * categoricalS F) *ᵥ c := by rw [hD]
      _ = fusionMatrix F i *ᵥ φ := by rw [← Matrix.mulVec_mulVec, ← hSdef, hφ]
      _ = S *ᵥ (φ i • c) := by rw [hN, Matrix.mulVec_smul, hφ]
  have h2 := congrFun (hinj _ _ h1) k
  simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h2
  exact (mul_right_cancel₀ hk h2).symm

include M in
theorem fusionChar_injective : Function.Injective (fusionChar F) := by
  classical
  intro k l hkl
  have hdk := F.dimension_simple_ne_zero k
  have hdl := F.dimension_simple_ne_zero l
  have hcol : ∀ m, categoricalS F m l = F.dimension (F.simple l) /
      F.dimension (F.simple k) * categoricalS F m k := by
    intro m
    have := congrFun hkl m
    simp only [fusionChar] at this
    field_simp at this ⊢
    linear_combination -this
  have ho := categoricalS_orthogonality F M l (F.dualLabel k)
  have hok := categoricalS_orthogonality F M k (F.dualLabel k)
  rw [if_pos rfl] at hok
  have hsum : ∑ m, categoricalS F l m * categoricalS F (F.dualLabel k) m =
      F.dimension (F.simple l) / F.dimension (F.simple k) * F.globalDimension := by
    rw [← hok, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [categoricalS_symm F M.toRibbon l m, hcol m, categoricalS_symm F M.toRibbon k m]
    ring
  rw [hsum] at ho
  by_contra hne
  have hne' : F.dualLabel k ≠ F.dualLabel l := fun h => hne
    (by rw [← F.dualLabel_involutive k, h, F.dualLabel_involutive l])
  rw [if_neg hne'] at ho
  exact (mul_ne_zero (div_ne_zero hdl hdk) F.globalDimension_ne_zero) ho

end Characters

section Galois

variable (F : SphericalFusion C) (M : Modular F) (σ : ℂ ≃+* ℂ)

include M in
theorem exists_galois_char (k : F.Label) : ∃ l, ∀ i, σ (fusionChar F k i) = fusionChar F l i :=
  exists_fusionChar_eq F M (fun i => σ (fusionChar F k i))
    (by simp only [fusionChar_unit F M, map_one])
    (fun i j => by
      rw [← map_mul, fusionChar_mul, map_sum]
      simp only [map_mul, map_natCast])

/-- The Galois permutation `π`: `σ ∘ χ_k = χ_{π k}` (as a function). -/
def galoisFun (k : F.Label) : F.Label := (exists_galois_char F M σ k).choose

theorem galoisFun_spec (k i : F.Label) :
    σ (fusionChar F k i) = fusionChar F (galoisFun F M σ k) i :=
  (exists_galois_char F M σ k).choose_spec i

theorem galoisFun_injective : Function.Injective (galoisFun F M σ) := by
  intro k l h
  apply fusionChar_injective F M
  funext i
  apply σ.injective
  rw [galoisFun_spec F M σ k i, galoisFun_spec F M σ l i, h]

/-- The Galois permutation of the labels. -/
def galoisPerm : F.Label ≃ F.Label :=
  Equiv.ofBijective (galoisFun F M σ) (Finite.injective_iff_bijective.mp
    (galoisFun_injective F M σ))

theorem galoisPerm_spec (k i : F.Label) :
    σ (fusionChar F k i) = fusionChar F (galoisPerm F M σ k) i :=
  galoisFun_spec F M σ k i

theorem galoisPerm_dual (k : F.Label) :
    galoisPerm F M σ (F.dualLabel k) = F.dualLabel (galoisPerm F M σ k) := by
  apply fusionChar_injective F M
  funext i
  rw [← galoisPerm_spec, fusionChar_dual F M, galoisPerm_spec, fusionChar_dual F M]

/-- `Q_j = Σ_i χ_j(i) χ_j(i*)`. -/
def charNorm (j : F.Label) : ℂ :=
  ∑ i, fusionChar F j i * fusionChar F j (F.dualLabel i)

include M in
theorem dimension_sq_charNorm (j : F.Label) :
    F.dimension (F.simple j) ^ 2 * charNorm F j = F.globalDimension := by
  have ho := categoricalS_orthogonality F M j (F.dualLabel j)
  rw [if_pos rfl] at ho
  rw [← ho, charNorm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i => ?_
  intro _
  have hd := F.dimension_simple_ne_zero j
  rw [← fusionChar_dual F M]
  simp only [fusionChar, F.dimension_dualLabel]
  rw [categoricalS_symm F M.toRibbon i j, categoricalS_symm F M.toRibbon i (F.dualLabel j)]
  field_simp

theorem galois_charNorm (j : F.Label) :
    σ (charNorm F j) = charNorm F (galoisPerm F M σ j) := by
  simp only [charNorm, map_sum, map_mul, galoisPerm_spec F M σ]

variable (a : ℂ)

include M in
theorem charNorm_ne_zero (j : F.Label) : charNorm F j ≠ 0 := by
  intro h
  have := dimension_sq_charNorm F M j
  rw [h, mul_zero] at this
  exact F.globalDimension_ne_zero this.symm

theorem ne_zero_of_norm (ha : (a ^ 2 * F.globalDimension) ^ 2 = 1) : a ≠ 0 := by
  rintro rfl
  simp at ha

include M in
/-- `σ(s_{0j})² = s_{0,πj}²` for `s = a S`, `(a² D²)² = 1`. -/
theorem galois_s0_sq (ha : (a ^ 2 * F.globalDimension) ^ 2 = 1) (j : F.Label) :
    σ (a * F.dimension (F.simple j)) ^ 2 =
      (a * F.dimension (F.simple (galoisPerm F M σ j))) ^ 2 := by
  set κ := a ^ 2 * F.globalDimension with hκ
  have hκσ : σ κ = κ := by
    have : (κ - 1) * (κ + 1) = 0 := by linear_combination ha
    rcases mul_eq_zero.mp this with h | h
    · rw [show κ = 1 by linear_combination h, map_one]
    · rw [show κ = -1 by linear_combination h, map_neg, map_one]
  have e1 : (a * F.dimension (F.simple j)) ^ 2 * charNorm F j = κ := by
    rw [hκ, ← dimension_sq_charNorm F M j]; ring
  have e2 : (a * F.dimension (F.simple (galoisPerm F M σ j))) ^ 2 *
      charNorm F (galoisPerm F M σ j) = κ := by
    rw [hκ, ← dimension_sq_charNorm F M (galoisPerm F M σ j)]; ring
  have e3 := congrArg σ e1
  rw [map_mul, map_pow, galois_charNorm F M σ, hκσ, ← e2] at e3
  exact mul_right_cancel₀ (charNorm_ne_zero F M _) e3

/-- The Galois sign `ε_j = σ(s_{0j}) / s_{0,πj}`. -/
def galoisSign (j : F.Label) : ℂ :=
  σ (a * F.dimension (F.simple j)) / (a * F.dimension (F.simple (galoisPerm F M σ j)))

theorem galoisSign_mul (ha : (a ^ 2 * F.globalDimension) ^ 2 = 1) (j : F.Label) :
    galoisSign F M σ a j * (a * F.dimension (F.simple (galoisPerm F M σ j))) =
      σ (a * F.dimension (F.simple j)) := by
  have hne : a * F.dimension (F.simple (galoisPerm F M σ j)) ≠ 0 :=
    mul_ne_zero (ne_zero_of_norm F a ha) (F.dimension_simple_ne_zero _)
  rw [galoisSign, div_mul_cancel₀ _ hne]

theorem galoisSign_sq (ha : (a ^ 2 * F.globalDimension) ^ 2 = 1) (j : F.Label) :
    galoisSign F M σ a j = 1 ∨ galoisSign F M σ a j = -1 := by
  have hne : a * F.dimension (F.simple (galoisPerm F M σ j)) ≠ 0 :=
    mul_ne_zero (ne_zero_of_norm F a ha) (F.dimension_simple_ne_zero _)
  have h := galois_s0_sq F M σ a ha j
  have hsq : galoisSign F M σ a j ^ 2 = 1 := by
    rw [galoisSign, div_pow, h, div_self (pow_ne_zero 2 hne)]
  have : (galoisSign F M σ a j - 1) * (galoisSign F M σ a j + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp this with h1 | h1
  · left; linear_combination h1
  · right; linear_combination h1

/-- `σ(s_{ij}) = ε_j s_{i,πj}`. -/
theorem galois_entry (ha : (a ^ 2 * F.globalDimension) ^ 2 = 1) (i j : F.Label) :
    σ (a * categoricalS F i j) =
      galoisSign F M σ a j * (a * categoricalS F i (galoisPerm F M σ j)) := by
  have hd := F.dimension_simple_ne_zero j
  have hd' := F.dimension_simple_ne_zero (galoisPerm F M σ j)
  have e1 : a * categoricalS F i j = (a * F.dimension (F.simple j)) * fusionChar F j i := by
    rw [fusionChar]; field_simp
  have e2 : a * categoricalS F i (galoisPerm F M σ j) =
      (a * F.dimension (F.simple (galoisPerm F M σ j))) *
        fusionChar F (galoisPerm F M σ j) i := by
    rw [fusionChar]; field_simp
  rw [e1, map_mul, galoisPerm_spec F M σ, e2, ← galoisSign_mul F M σ a ha j]
  ring

open Classical in
/-- The Coste–Gannon signed permutation matrix `G_{jk} = ε_j [π j = k]`. -/
def galoisSigned : Matrix F.Label F.Label ℂ :=
  fun j k => if galoisPerm F M σ j = k then galoisSign F M σ a j else 0

open Classical in
/-- **Coste–Gannon / DLN (4.4)**: for `s = a S` with `(a² D²)² = 1`, `G = galoisSigned`
is a signed permutation matrix with `σ(s) = G s` and `σ(s) G = s`. -/
theorem galois_signed (ha : (a ^ 2 * F.globalDimension) ^ 2 = 1) :
    IsSignedPermutation (galoisSigned F M σ a) ∧
      mapσ σ (a • categoricalS F) = galoisSigned F M σ a * (a • categoricalS F) ∧
      mapσ σ (a • categoricalS F) * galoisSigned F M σ a = a • categoricalS F := by
  have hsym := categoricalS_symm F M.toRibbon
  refine ⟨⟨galoisPerm F M σ, galoisSign F M σ a, galoisSign_sq F M σ a ha, fun _ _ => rfl⟩,
    ?_, ?_⟩
  · ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, galoisSigned, RingEquiv.coe_toRingHom, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hsym i j, galois_entry F M σ a ha j i, hsym]
  · ext i k
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, galoisSigned, RingEquiv.coe_toRingHom, mul_ite, mul_zero]
    rw [Finset.sum_eq_single ((galoisPerm F M σ).symm k)]
    · rw [if_pos (Equiv.apply_symm_apply _ _), galois_entry F M σ a ha,
        Equiv.apply_symm_apply]
      rcases galoisSign_sq F M σ a ha ((galoisPerm F M σ).symm k) with h | h <;> rw [h] <;> ring
    · intro l _ hl
      rw [if_neg]
      intro h
      exact hl (by rw [← h, Equiv.symm_apply_apply])
    · simp

end Galois

end VOA.Huang.NSGalois
