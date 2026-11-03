import VOA.Huang.GaloisSymSigns
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Arithmetic of fusion eigenvalues

Each normalized S-entry satisfies the monic integral characteristic polynomial
of an actual fusion matrix. This proves integrality of the ratios, not membership
of S in the cyclotomic field of the order of T.
-/

noncomputable section

namespace VOA.Huang.GaloisSym

open Matrix

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  {N : ι → ι → ι → ℕ} {S : Matrix ι ι K} {v0 : ι}

/-- Fusion characters are algebraic integers: their monic polynomial is the
characteristic polynomial over `ℤ` of the corresponding fusion matrix. -/
theorem VerlindeSystem.isIntegral_fusionCharacter (H : VerlindeSystem N S v0) (a x : ι) :
    IsIntegral ℤ (fusionCharacter S v0 a x) := by
  let A : Matrix ι ι ℤ := fun b c => N a b c
  refine ⟨A.charpoly, Matrix.charpoly_monic A, ?_⟩
  change Polynomial.eval₂ (Int.castRingHom K) (fusionCharacter S v0 a x) A.charpoly = 0
  rw [← Polynomial.eval_map, ← Matrix.charpoly_map, Matrix.eval_charpoly]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨fun b => S b x, ?_, ?_⟩
  · intro hz
    exact H.vacuum_ne x (congrFun hz v0)
  · rw [Matrix.sub_mulVec]
    apply sub_eq_zero.mpr
    ext b
    simpa [A, Matrix.mulVec, dotProduct, Matrix.scalar, Matrix.diagonal] using
      (H.eigen a b x).symm

variable [CharZero K]

theorem VerlindeSystem.isAlgebraic_fusionCharacter (H : VerlindeSystem N S v0) (a x : ι) :
    IsAlgebraic ℚ (fusionCharacter S v0 a x) :=
  (show IsIntegral ℚ (fusionCharacter S v0 a x) from
    (H.isIntegral_fusionCharacter a x).tower_top).isAlgebraic

/-- Normalization also makes the unnormalized entries algebraic. This still
does not identify an abelian extension or its conductor. -/
theorem VerlindeSystem.isAlgebraic_entry (H : VerlindeSystem N S v0)
    (hn : IntegralColumnNormalization S) (a x : ι) : IsAlgebraic ℚ (S a x) := by
  obtain ⟨B, hB⟩ := hn
  let q : K := ∑ b, ∑ c, (B b c : K) *
    fusionCharacter S v0 b x * fusionCharacter S v0 c x
  have hq : IsIntegral ℚ q := by
    apply IsIntegral.sum
    intro b _
    apply IsIntegral.sum
    intro c _
    exact ((isAlgebraic_int (R := ℚ) (B b c)).isIntegral.mul
      (H.isAlgebraic_fusionCharacter b x).isIntegral).mul
      (H.isAlgebraic_fusionCharacter c x).isIntegral
  have he : S v0 x ^ 2 * q = 1 := by
    calc
      _ = ∑ b, ∑ c, (B b c : K) * S b x * S c x := by
        dsimp [q]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        dsimp [fusionCharacter]
        field_simp [H.vacuum_ne x]
      _ = 1 := hB x
  have hsquare : S v0 x ^ 2 = q⁻¹ := eq_inv_of_mul_eq_one_left he
  have hv : IsAlgebraic ℚ (S v0 x) := by
    apply IsAlgebraic.of_pow (n := 2) (by decide)
    rw [hsquare]
    exact hq.isAlgebraic.inv
  have hf : fusionCharacter S v0 a x * S v0 x = S a x := by
    exact div_mul_cancel₀ _ (H.vacuum_ne x)
  rw [← hf]
  exact (H.isAlgebraic_fusionCharacter a x).mul hv

end VOA.Huang.GaloisSym
