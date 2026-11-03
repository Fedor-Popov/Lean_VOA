import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Galois permutations of fusion characters

This is the algebraic part of Coste–Gannon. No cyclotomic field or modular-group
action is assumed or concluded. Every automorphism of the coefficient field
permutes the normalized columns of an invertible Verlinde matrix.
-/

noncomputable section

namespace VOA.Huang.GaloisSym

open Matrix

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- The eigenvalue in the normalized column `x`. -/
def fusionCharacter (S : Matrix ι ι K) (v0 a x : ι) : K := S a x / S v0 x

/-- The precise algebraic hypotheses used by the fusion-character argument. -/
structure VerlindeSystem (N : ι → ι → ι → ℕ) (S : Matrix ι ι K) (v0 : ι) : Prop where
  invertible : IsUnit S
  vacuum_ne : ∀ x, S v0 x ≠ 0
  verlinde : ∀ a b x,
    S a x * S b x = S v0 x * ∑ c, (N a b c : K) * S c x

variable {N : ι → ι → ι → ℕ} {S : Matrix ι ι K} {v0 : ι}

theorem VerlindeSystem.eigen (H : VerlindeSystem N S v0) (a b x : ι) :
    ∑ c, (N a b c : K) * S c x = fusionCharacter S v0 a x * S b x := by
  apply (mul_left_cancel₀ (H.vacuum_ne x))
  rw [← H.verlinde]
  dsimp [fusionCharacter]
  field_simp [H.vacuum_ne x]

/-- Distinct columns give distinct fusion characters. -/
theorem VerlindeSystem.character_injective (H : VerlindeSystem N S v0) :
    Function.Injective (fun x => fun a => fusionCharacter S v0 a x) := by
  intro x y h
  have he : S *ᵥ Pi.single x (S v0 x)⁻¹ = S *ᵥ Pi.single y (S v0 y)⁻¹ := by
    ext a
    simpa [Matrix.mulVec_single, fusionCharacter, div_eq_mul_inv] using congrFun h a
  have hv := Matrix.mulVec_injective_iff_isUnit.mpr H.invertible he
  by_contra hxy
  have hz := congrFun hv x
  simp [hxy, H.vacuum_ne x] at hz

/-- Any nonzero common eigenvector has one of the listed characters as eigenvalue. -/
theorem VerlindeSystem.common_eigenvalue (H : VerlindeSystem N S v0)
    (v : ι → K) (hv : v ≠ 0) (μ : ι → K)
    (he : ∀ a b, ∑ c, (N a b c : K) * v c = μ a * v b) :
    ∃ x, ∀ a, μ a = fusionCharacter S v0 a x := by
  let w := S⁻¹ *ᵥ v
  have hw : S *ᵥ w = v := by
    dsimp [w]
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv S (H.invertible.map Matrix.detMonoidHom),
      one_mulVec]
  have hwne : w ≠ 0 := by
    intro h
    apply hv
    rw [← hw, h, mulVec_zero]
  obtain ⟨x, hx⟩ : ∃ x, w x ≠ 0 := by
    by_contra h
    apply hwne
    ext x
    simpa using not_exists.mp h x
  refine ⟨x, fun a => ?_⟩
  have hdiag : S *ᵥ (fun j => fusionCharacter S v0 a j * w j) =
      S *ᵥ (fun j => μ a * w j) := by
    ext b
    calc
      _ = ∑ c, (N a b c : K) * (S *ᵥ w) c := by
        simp only [mulVec, dotProduct, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul, H.eigen]
        ring
      _ = μ a * v b := by rw [hw]; exact he a b
      _ = _ := by rw [← hw]; simp [mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
  have hj := congrFun (Matrix.mulVec_injective_iff_isUnit.mpr H.invertible hdiag) x
  exact ((mul_right_cancel₀ hx) hj).symm

/-- Galois automorphisms permute fusion characters. No algebraicity assumption is
needed when the automorphism is already defined on the field containing `S`. -/
theorem VerlindeSystem.galois_permutation (H : VerlindeSystem N S v0)
    (σ : K ≃+* K) :
    ∃ π : Equiv.Perm ι, ∀ a x,
      σ (fusionCharacter S v0 a x) = fusionCharacter S v0 a (π x) := by
  have hex : ∀ x, ∃ y, ∀ a,
      σ (fusionCharacter S v0 a x) = fusionCharacter S v0 a y := by
    intro x
    apply H.common_eigenvalue (fun b => σ (S b x))
    · intro hz
      have := congrFun hz v0
      exact H.vacuum_ne x (σ.injective (by simpa using this))
    · intro a b
      simpa only [map_sum, map_mul, map_natCast] using congrArg σ (H.eigen a b x)
  choose p hp using hex
  have hinj : Function.Injective p := by
    intro x y hxy
    apply H.character_injective
    ext a
    apply σ.injective
    rw [hp, hp, hxy]
  exact ⟨Equiv.ofBijective p ⟨hinj, Finite.surjective_of_injective hinj⟩, fun a x => hp x a⟩

/-- The same permutation acts on unnormalized columns, with a nonzero scalar
per column. Turning these scalars into signs requires a normalization. -/
theorem VerlindeSystem.galois_columns (H : VerlindeSystem N S v0) (σ : K ≃+* K) :
    ∃ (π : Equiv.Perm ι) (d : ι → K), (∀ x, d x ≠ 0) ∧
      ∀ a x, σ (S a x) = d x * S a (π x) := by
  obtain ⟨π, hπ⟩ := H.galois_permutation σ
  refine ⟨π, fun x => σ (S v0 x) / S v0 (π x),
    fun x => div_ne_zero ((map_ne_zero σ).mpr (H.vacuum_ne x)) (H.vacuum_ne _), ?_⟩
  intro a x
  have h := hπ a x
  simp only [fusionCharacter, map_div₀] at h
  have hn : σ (S v0 x) ≠ 0 := (map_ne_zero σ).mpr (H.vacuum_ne x)
  field_simp [hn, H.vacuum_ne] at h ⊢
  linear_combination h

end VOA.Huang.GaloisSym
