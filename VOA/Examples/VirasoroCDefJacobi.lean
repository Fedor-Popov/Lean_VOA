/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroCDefBuild
import VOA.Core.Borcherds

/-!
# Building `∂_c Y` on `V(c,0)`, part 2: the order-`t` Jacobi identity

This is step 3(C2) of the `∂_c` route (the steps are listed in `VirasoroPolyStructure`). On the constant lifts
`A, B, X` of `u, v, x`, the Borcherds identity of `V(c',0)` holds at every `c'`. It is a finite
identity in `PV`, summed over a range `S` that does not depend on `c'`; the range comes from the
energy bounds. Applying `D` and the Leibniz rule `D_tensor` gives exactly the order-`t` Jacobi
identity of `Y₁` (`Y1_jacobi`).
-/

namespace VOA.VirPoly

open VOA VOA.VirModule Polynomial

theorem Sorted.csmul {P : PV} (a : ℂ) (hP : Sorted P) : Sorted (a • P) := by
  rw [smul_eq_C_smul]; exact hP.smul _

theorem sorted_sum {ι : Type*} (s : Finset ι) (f : ι → PV) (hf : ∀ i ∈ s, Sorted (f i)) :
    Sorted (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Sorted.zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem D_lift (c : ℂ) (y : VirUniv c) : D (lift c y) = 0 := by
  ext u : 1
  simp [lift]

theorem finsum_eq_sum_of_zero {V : Type*} [AddCommMonoid V] (f : ℤ → V) (S : Finset ℤ)
    (h : ∀ i ∉ S, f i = 0) : ∑ᶠ i, f i = ∑ i ∈ S, f i :=
  finsum_eq_sum_of_support_subset f fun i hi => by
    by_contra hS; exact hi (h i hS)

section Jacobi

variable (c : ℂ) (u v x : VirUniv c) (ℓ m n : ℤ)

/-- The constant lifts. -/
local notation "𝔸" => lift c u
local notation "𝔹" => lift c v
local notation "𝕏" => lift c x

/-- The left Borcherds terms in `PV`. -/
noncomputable def τL (i : ℤ) : PV :=
  (negOnePow i * cbz ℓ i) • (tensor (ℓ + m - i) 𝔸 (tensor (n + i) 𝔹 𝕏)
    - negOnePow ℓ • tensor (ℓ + n - i) 𝔹 (tensor (m + i) 𝔸 𝕏))

/-- The right Borcherds terms in `PV`. -/
noncomputable def τR (i : ℤ) : PV :=
  cbz m i • tensor (m + n - i) (tensor (ℓ + i) 𝔸 𝔹) 𝕏

/-- The `c`-independent summation range. -/
noncomputable def rangeS : Finset ℤ :=
  let a : ℤ := ((lift c u).support.sup energyVir : ℕ)
  let b : ℤ := ((lift c v).support.sup energyVir : ℕ)
  let e : ℤ := ((lift c x).support.sup energyVir : ℕ)
  Finset.Icc 0 (max (max (b + e - n - 1) (a + e - m - 1)) (a + b - ℓ - 1))

theorem τL_zero (i : ℤ) (hi : i ∉ rangeS c u v x ℓ m n) : τL c u v x ℓ m n i = 0 := by
  simp only [rangeS, Finset.mem_Icc, not_and_or, not_le] at hi
  rcases hi with hi | hi
  · simp [τL, cbz_apply_neg ℓ hi]
  · have h1 : tensor (n + i) (lift c v) (lift c x) = 0 :=
      eq_zero_of_bounded_neg (bounded_tensor _ (bounded_sup _) (bounded_sup _)) (by omega)
    have h2 : tensor (m + i) (lift c u) (lift c x) = 0 :=
      eq_zero_of_bounded_neg (bounded_tensor _ (bounded_sup _) (bounded_sup _)) (by omega)
    simp [τL, h1, h2]

theorem τR_zero (i : ℤ) (hi : i ∉ rangeS c u v x ℓ m n) : τR c u v x ℓ m n i = 0 := by
  simp only [rangeS, Finset.mem_Icc, not_and_or, not_le] at hi
  rcases hi with hi | hi
  · simp [τR, cbz_apply_neg m hi]
  · have h3 : tensor (ℓ + i) (lift c u) (lift c v) = 0 :=
      eq_zero_of_bounded_neg (bounded_tensor _ (bounded_sup _) (bounded_sup _)) (by omega)
    simp [τR, h3]

theorem sorted_τL (i : ℤ) : Sorted (τL c u v x ℓ m n i) :=
  ((sorted_tensor _ _ _).sub ((sorted_tensor _ _ _).csmul _)).csmul _

theorem sorted_τR (i : ℤ) : Sorted (τR c u v x ℓ m n i) := (sorted_tensor _ _ _).csmul _

/-- **The Borcherds identity in `PV`**, on the constant lifts. -/
theorem borcherds_PV :
    ∑ i ∈ rangeS c u v x ℓ m n, τL c u v x ℓ m n i
      = ∑ i ∈ rangeS c u v x ℓ m n, τR c u v x ℓ m n i := by
  refine polyComb_injective (sorted_sum _ _ fun i _ => sorted_τL c u v x ℓ m n i)
    (sorted_sum _ _ fun i _ => sorted_τR c u v x ℓ m n i) fun c' => ?_
  rw [map_sum, map_sum,
    ← finsum_eq_sum_of_zero _ _ fun i hi => by rw [τL_zero c u v x ℓ m n i hi, map_zero],
    ← finsum_eq_sum_of_zero _ _ fun i hi => by rw [τR_zero c u v x ℓ m n i hi, map_zero]]
  have h := (virasoroVOA c').jacobi (polyComb c' (lift c u)) (polyComb c' (lift c v))
    (polyComb c' (lift c x)) ℓ m n
  convert h using 2 with i i
  · simp only [τL, polyComb_csmul, map_sub, polyComb_tensor]
    rfl
  · simp only [τR, polyComb_csmul, polyComb_tensor]
    rfl

theorem D_τL (i : ℤ) : D (τL c u v x ℓ m n i) = (negOnePow i * cbz ℓ i) •
    ((tensor' (ℓ + m - i) 𝔸 (tensor (n + i) 𝔹 𝕏) + tensor (ℓ + m - i) 𝔸 (tensor' (n + i) 𝔹 𝕏))
      - negOnePow ℓ • (tensor' (ℓ + n - i) 𝔹 (tensor (m + i) 𝔸 𝕏)
        + tensor (ℓ + n - i) 𝔹 (tensor' (m + i) 𝔸 𝕏))) := by
  simp only [τL, map_smul, map_sub, D_tensor, D_lift, map_zero, LinearMap.zero_apply, add_zero]

theorem D_τR (i : ℤ) : D (τR c u v x ℓ m n i) = cbz m i •
    (tensor' (m + n - i) (tensor (ℓ + i) 𝔸 𝔹) 𝕏 + tensor (m + n - i) (tensor' (ℓ + i) 𝔸 𝔹) 𝕏) := by
  simp only [τR, map_smul, D_tensor, D_lift, map_zero, LinearMap.zero_apply, add_zero]

/-- **The order-`t` Jacobi identity for `Y₁ = ∂_c Y`.** -/
theorem Y1_jacobi :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (mode (Y1 c u) (ℓ + m - i) ((virasoroVOA c).smul v (n + i) x)
          + (virasoroVOA c).smul u (ℓ + m - i) (mode (Y1 c v) (n + i) x)
          - negOnePow ℓ •
            (mode (Y1 c v) (ℓ + n - i) ((virasoroVOA c).smul u (m + i) x)
              + (virasoroVOA c).smul v (ℓ + n - i) (mode (Y1 c u) (m + i) x))))
      = ∑ᶠ i : ℤ, cbz m i •
          ((virasoroVOA c).smul (mode (Y1 c u) (ℓ + i) v) (m + n - i) x
            + mode (Y1 c ((virasoroVOA c).smul u (ℓ + i) v)) (m + n - i) x) := by
  have hS : ∀ (k : ℤ) (P Q : PV), (virasoroVOA c).smul (polyComb c P) k (polyComb c Q)
      = polyComb c (tensor k P Q) := fun k P Q => (polyComb_tensor k P Q c).symm
  have hY : ∀ (k : ℤ) (P Q : PV), Sorted P → Sorted Q →
      mode (Y1 c (polyComb c P)) k (polyComb c Q) = polyComb c (tensor' k P Q) :=
    fun k P Q hP hQ => mode_Y1_polyComb c hP hQ k
  have hA := sorted_lift c u
  have hB := sorted_lift c v
  have hX := sorted_lift c x
  have hL : ∀ i : ℤ, (negOnePow i * cbz ℓ i) •
        (mode (Y1 c u) (ℓ + m - i) ((virasoroVOA c).smul v (n + i) x)
          + (virasoroVOA c).smul u (ℓ + m - i) (mode (Y1 c v) (n + i) x)
          - negOnePow ℓ •
            (mode (Y1 c v) (ℓ + n - i) ((virasoroVOA c).smul u (m + i) x)
              + (virasoroVOA c).smul v (ℓ + n - i) (mode (Y1 c u) (m + i) x)))
      = polyComb c (D (τL c u v x ℓ m n i)) := by
    intro i
    rw [D_τL]
    conv_lhs => rw [← polyComb_lift c u, ← polyComb_lift c v, ← polyComb_lift c x]
    rw [hS, hS, hY _ _ _ hA (sorted_tensor _ _ _), hY _ _ _ hB (sorted_tensor _ _ _),
      hY _ _ _ hB hX, hY _ _ _ hA hX, hS, hS]
    simp only [polyComb_csmul, map_add, map_sub]
  have hR : ∀ i : ℤ, cbz m i •
          ((virasoroVOA c).smul (mode (Y1 c u) (ℓ + i) v) (m + n - i) x
            + mode (Y1 c ((virasoroVOA c).smul u (ℓ + i) v)) (m + n - i) x)
      = polyComb c (D (τR c u v x ℓ m n i)) := by
    intro i
    rw [D_τR]
    conv_lhs => rw [← polyComb_lift c u, ← polyComb_lift c v, ← polyComb_lift c x]
    rw [hY _ _ _ hA hB, hS, hS, hY _ _ _ (sorted_tensor _ _ _) hX]
    rw [polyComb_csmul, map_add, add_comm]
  rw [finsum_congr hL, finsum_congr hR,
    finsum_eq_sum_of_zero _ (rangeS c u v x ℓ m n) fun i hi => by
      rw [τL_zero c u v x ℓ m n i hi, map_zero, map_zero],
    finsum_eq_sum_of_zero _ (rangeS c u v x ℓ m n) fun i hi => by
      rw [τR_zero c u v x ℓ m n i hi, map_zero, map_zero],
    ← map_sum, ← map_sum, ← map_sum, ← map_sum, borcherds_PV]

end Jacobi

/-- **`∂_c Y` as a first-order deformation of `V(c,0)`**, at every central charge `c`. -/
noncomputable def cDeformation (c : ℂ) : Deform.FirstOrderDeformation (virasoroVOA c) where
  Y1 := Y1 c
  truncation := Y1_truncation c
  vacuum_Y1 := Y1_vacuum c
  creation := Y1_creation c
  jacobi := fun u v x ℓ m n => Y1_jacobi c u v x ℓ m n

end VOA.VirPoly

section AxiomAudit
#print axioms VOA.VirPoly.borcherds_PV
#print axioms VOA.VirPoly.Y1_jacobi
#print axioms VOA.VirPoly.cDeformation
end AxiomAudit
