/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.LocalSystemJacobi
import VOA.Modules.WeakModule

/-!
# The module Jacobi identity from its two boundary families (abstract)

Let `Y_M : 𝒱 → (End M)⟦z^±⟧` be any linear map whose fields are lower truncated.  The
Borcherds/Jacobi identity in mode form

`BL(ℓ,m,n) := Σᵢ (−1)ⁱC(ℓ,i) (u_{ℓ+m−i} v_{n+i} − (−1)^ℓ v_{ℓ+n−i} u_{m+i}) x`
` = Σᵢ C(m,i) (u_{ℓ+i}v)_{m+n−i} x =: BR(ℓ,m,n)`

satisfies, on **both** sides, the Pascal recurrence
`S(ℓ, m+1, n) = S(ℓ, m, n+1) + S(ℓ+1, m, n)`.  Hence it holds for all `(ℓ, m, n)` as soon as it
holds on the two boundary families

* `ℓ = 0` (the **commutator formula**), and
* `m = 0` (the **associator / iterate formula**).

`jacobi_of_boundaries`, `WeakModule.ofBoundaries`: a vacuum-normalised, lower
truncated `Y_M` satisfying the commutator and associator formulas is a weak module.

This is the packaging step of the Huang–Lepowsky `P(1)`-construction: the action on the coefficient
functionals is checked against the two boundary families
separately.  The proof follows `Core.LocalSystemJacobi` (where the product side is a field
product); here the product side is the `V`-product `u_{ℓ+i} v` fed into `Y_M`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.AssocJacobiBoundary

open VOA
open Module (End)
open scoped BigOperators

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)
variable {M : Type v} [AddCommGroup M] [Module ℂ M]

/-! ## The two sides -/

/-- The first ordered-composition sum. -/
noncomputable def Puv (YM : 𝒱 →ₗ[ℂ] (End ℂ M)⟦z^±⟧) (u v : 𝒱) (x : M) (ell m n : ℤ) : M :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ell i) • mode (YM u) (ell + m - i) (mode (YM v) (n + i) x)

/-- The exchanged ordered-composition sum. -/
noncomputable def Pvu (YM : 𝒱 →ₗ[ℂ] (End ℂ M)⟦z^±⟧) (u v : 𝒱) (x : M) (ell m n : ℤ) : M :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ell i) • mode (YM v) (ell + n - i) (mode (YM u) (m + i) x)

/-- The commutator side of the Borcherds identity. -/
noncomputable def BL (YM : 𝒱 →ₗ[ℂ] (End ℂ M)⟦z^±⟧) (u v : 𝒱) (x : M) (ell m n : ℤ) : M :=
  Puv YM u v x ell m n - negOnePow ell • Pvu YM u v x ell m n

/-- The product side of the Borcherds identity. -/
noncomputable def BR (YM : 𝒱 →ₗ[ℂ] (End ℂ M)⟦z^±⟧) (u v : 𝒱) (x : M) (ell m n : ℤ) : M :=
  ∑ᶠ i : ℤ, cbz m i • mode (YM (W.smul u (ell + i) v)) (m + n - i) x

/-- Lower truncation of a family of fields. -/
def Truncated (YM : 𝒱 →ₗ[ℂ] (End ℂ M)⟦z^±⟧) : Prop :=
  ∀ (u : 𝒱) (x : M), ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (YM u) n x = 0

variable {W}
variable {YM : 𝒱 →ₗ[ℂ] (End ℂ M)⟦z^±⟧}

/-! ## Finite supports -/

theorem BR_fin (u v : 𝒱) (x : M) (ell m n : ℤ) :
    (Function.support fun i : ℤ =>
      cbz m i • mode (YM (W.smul u (ell + i) v)) (m + n - i) x).Finite := by
  obtain ⟨N, hN⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
  apply Set.Finite.subset (Set.finite_Icc 0 (N - ell))
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun hneg => hi ?_, not_lt.mp fun hlarge => hi ?_⟩
  · rw [cbz_apply_neg m hneg, zero_smul]
  · rw [show W.smul u (ell + i) v = 0 from hN (ell + i) (by omega), map_zero]
    change cbz m i • mode (0 : (End ℂ M)⟦z^±⟧) (m + n - i) x = 0
    rw [mode_zero, LinearMap.zero_apply, smul_zero]

theorem BR_fin' (u v : 𝒱) (x : M) (ell m n : ℤ) :
    (Function.support fun i : ℤ =>
      cbz m (i - 1) • mode (YM (W.smul u (ell + i) v)) (m + 1 + n - i) x).Finite := by
  obtain ⟨N, hN⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
  apply Set.Finite.subset (Set.finite_Icc 1 (N - ell))
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun hsmall => hi ?_, not_lt.mp fun hlarge => hi ?_⟩
  · rw [cbz_apply_neg m (by omega), zero_smul]
  · rw [show W.smul u (ell + i) v = 0 from hN (ell + i) (by omega), map_zero]
    change cbz m (i - 1) • mode (0 : (End ℂ M)⟦z^±⟧) (m + 1 + n - i) x = 0
    rw [mode_zero, LinearMap.zero_apply, smul_zero]

section Trunc

variable (htr : Truncated YM)
include htr

theorem Puv_fin (u v : 𝒱) (x : M) (ell m n : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ell i) •
      mode (YM u) (ell + m - i) (mode (YM v) (n + i) x)).Finite := by
  obtain ⟨Nb, hNb⟩ := htr v x
  apply Set.Finite.subset (Set.finite_Icc 0 (Nb - n))
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun hneg => hi ?_, not_lt.mp fun hlarge => hi ?_⟩
  · rw [cbz_apply_neg ell hneg, mul_zero, zero_smul]
  · rw [hNb (n + i) (by omega), map_zero, smul_zero]

theorem Pvu_fin (u v : 𝒱) (x : M) (ell m n : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ell i) •
      mode (YM v) (ell + n - i) (mode (YM u) (m + i) x)).Finite := by
  obtain ⟨Na, hNa⟩ := htr u x
  apply Set.Finite.subset (Set.finite_Icc 0 (Na - m))
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun hneg => hi ?_, not_lt.mp fun hlarge => hi ?_⟩
  · rw [cbz_apply_neg ell hneg, mul_zero, zero_smul]
  · rw [hNa (m + i) (by omega), map_zero, smul_zero]

theorem Puv_fin' (u v : 𝒱) (x : M) (ell m n : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ell (i - 1)) •
      mode (YM u) (ell + 1 + m - i) (mode (YM v) (n + i) x)).Finite := by
  obtain ⟨Nb, hNb⟩ := htr v x
  apply Set.Finite.subset (Set.finite_Icc 1 (Nb - n))
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun hsmall => hi ?_, not_lt.mp fun hlarge => hi ?_⟩
  · rw [cbz_apply_neg ell (by omega), mul_zero, zero_smul]
  · rw [hNb (n + i) (by omega), map_zero, smul_zero]

theorem Pvu_fin' (u v : 𝒱) (x : M) (ell m n : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ell (i - 1)) •
      mode (YM v) (ell + 1 + n - i) (mode (YM u) (m + i) x)).Finite := by
  obtain ⟨Na, hNa⟩ := htr u x
  apply Set.Finite.subset (Set.finite_Icc 1 (Na - m))
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun hsmall => hi ?_, not_lt.mp fun hlarge => hi ?_⟩
  · rw [cbz_apply_neg ell (by omega), mul_zero, zero_smul]
  · rw [hNa (m + i) (by omega), map_zero, smul_zero]

end Trunc

/-! ## Pascal recurrences -/

omit [Module ℂ M] in
theorem finsum_neg_distrib' {ι : Type*} (f : ι → M) : (∑ᶠ i, -f i) = -∑ᶠ i, f i := by
  by_cases h : (Function.support f).Finite
  · rw [← neg_one_zsmul (∑ᶠ i, f i), smul_finsum' (-1 : ℤ) h]
    exact finsum_congr fun i => (neg_one_zsmul (f i)).symm
  · have h' : ¬ (Function.support fun i => -f i).Finite := by
      rwa [show (Function.support fun i => -f i) = Function.support f from by
        ext i
        simp [Function.mem_support]]
    rw [finsum_of_infinite_support h', finsum_of_infinite_support h, neg_zero]

theorem BR_rec (u v : 𝒱) (x : M) (ell m n : ℤ) :
    BR W YM u v x ell (m + 1) n = BR W YM u v x ell m (n + 1) + BR W YM u v x (ell + 1) m n := by
  rw [BR, BR, BR,
    show (∑ᶠ i : ℤ, cbz (m + 1) i • mode (YM (W.smul u (ell + i) v)) (m + 1 + n - i) x) =
        ∑ᶠ i : ℤ, (cbz m i • mode (YM (W.smul u (ell + i) v)) (m + 1 + n - i) x +
          cbz m (i - 1) • mode (YM (W.smul u (ell + i) v)) (m + 1 + n - i) x) from
      finsum_congr fun i => by rw [cbz_pascal_up, add_smul],
    finsum_add_distrib (by
      have hf := BR_fin (W := W) (YM := YM) u v x ell m (n + 1)
      refine hf.subset fun i hi => ?_
      simp only [Function.mem_support] at hi ⊢
      rw [show m + 1 + n - i = m + (n + 1) - i by ring] at hi
      exact hi) (BR_fin' u v x ell m n)]
  congr 1
  · exact finsum_congr fun i => by rw [show m + 1 + n - i = m + (n + 1) - i by ring]
  · rw [← finsum_int_succ_shift (fun i : ℤ =>
      cbz m (i - 1) • mode (YM (W.smul u (ell + i) v)) (m + 1 + n - i) x)]
    exact finsum_congr fun i => by
      rw [show i + 1 - 1 = i by ring, show ell + (i + 1) = (ell + 1) + i by ring,
        show m + 1 + n - (i + 1) = m + n - i by ring]

section Trunc2

variable (htr : Truncated YM)
include htr

theorem Puv_rec (u v : 𝒱) (x : M) (ell m n : ℤ) :
    Puv YM u v x ell (m + 1) n = Puv YM u v x ell m (n + 1) + Puv YM u v x (ell + 1) m n := by
  have e1 : Puv YM u v x (ell + 1) m n =
      (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
        mode (YM u) (ell + (m + 1) - i) (mode (YM v) (n + i) x)) +
      ∑ᶠ i : ℤ, (negOnePow i * cbz ell (i - 1)) •
        mode (YM u) (ell + 1 + m - i) (mode (YM v) (n + i) x) := by
    rw [Puv,
      show (∑ᶠ i : ℤ, (negOnePow i * cbz (ell + 1) i) •
          mode (YM u) (ell + 1 + m - i) (mode (YM v) (n + i) x)) =
        ∑ᶠ i : ℤ, ((negOnePow i * cbz ell i) •
            mode (YM u) (ell + (m + 1) - i) (mode (YM v) (n + i) x) +
          (negOnePow i * cbz ell (i - 1)) •
            mode (YM u) (ell + 1 + m - i) (mode (YM v) (n + i) x)) from
        finsum_congr fun i => by
          rw [cbz_pascal_up, mul_add, add_smul,
            show ell + 1 + m - i = ell + (m + 1) - i by ring],
      finsum_add_distrib (Puv_fin htr u v x ell (m + 1) n) (Puv_fin' htr u v x ell m n)]
  have e3 : (∑ᶠ i : ℤ, (negOnePow i * cbz ell (i - 1)) •
      mode (YM u) (ell + 1 + m - i) (mode (YM v) (n + i) x)) =
      -Puv YM u v x ell m (n + 1) := by
    have step : (∑ᶠ i : ℤ, (negOnePow i * cbz ell (i - 1)) •
        mode (YM u) (ell + 1 + m - i) (mode (YM v) (n + i) x)) =
        ∑ᶠ i : ℤ, -((negOnePow i * cbz ell i) •
          mode (YM u) (ell + m - i) (mode (YM v) (n + 1 + i) x)) := by
      rw [← finsum_int_succ_shift (fun i : ℤ =>
        (negOnePow i * cbz ell (i - 1)) •
          mode (YM u) (ell + 1 + m - i) (mode (YM v) (n + i) x))]
      exact finsum_congr fun i => by
        rw [show i + 1 - 1 = i by ring, negOnePow_succ,
          show ell + 1 + m - (i + 1) = ell + m - i by ring,
          show n + (i + 1) = n + 1 + i by ring, neg_mul, neg_smul]
    rw [step, finsum_neg_distrib', Puv]
  have e2 : (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
      mode (YM u) (ell + (m + 1) - i) (mode (YM v) (n + i) x)) =
      Puv YM u v x ell (m + 1) n := by rw [Puv]
  rw [e1, e2, e3]
  abel

theorem Pvu_rec (u v : 𝒱) (x : M) (ell m n : ℤ) :
    Pvu YM u v x ell (m + 1) n = Pvu YM u v x ell m (n + 1) - Pvu YM u v x (ell + 1) m n := by
  have e1 : Pvu YM u v x (ell + 1) m n =
      (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
        mode (YM v) (ell + (n + 1) - i) (mode (YM u) (m + i) x)) +
      ∑ᶠ i : ℤ, (negOnePow i * cbz ell (i - 1)) •
        mode (YM v) (ell + 1 + n - i) (mode (YM u) (m + i) x) := by
    rw [Pvu,
      show (∑ᶠ i : ℤ, (negOnePow i * cbz (ell + 1) i) •
          mode (YM v) (ell + 1 + n - i) (mode (YM u) (m + i) x)) =
        ∑ᶠ i : ℤ, ((negOnePow i * cbz ell i) •
            mode (YM v) (ell + (n + 1) - i) (mode (YM u) (m + i) x) +
          (negOnePow i * cbz ell (i - 1)) •
            mode (YM v) (ell + 1 + n - i) (mode (YM u) (m + i) x)) from
        finsum_congr fun i => by
          rw [cbz_pascal_up, mul_add, add_smul,
            show ell + 1 + n - i = ell + (n + 1) - i by ring],
      finsum_add_distrib (Pvu_fin htr u v x ell m (n + 1)) (Pvu_fin' htr u v x ell m n)]
  have e3 : (∑ᶠ i : ℤ, (negOnePow i * cbz ell (i - 1)) •
      mode (YM v) (ell + 1 + n - i) (mode (YM u) (m + i) x)) =
      -Pvu YM u v x ell (m + 1) n := by
    have step : (∑ᶠ i : ℤ, (negOnePow i * cbz ell (i - 1)) •
        mode (YM v) (ell + 1 + n - i) (mode (YM u) (m + i) x)) =
        ∑ᶠ i : ℤ, -((negOnePow i * cbz ell i) •
          mode (YM v) (ell + n - i) (mode (YM u) (m + 1 + i) x)) := by
      rw [← finsum_int_succ_shift (fun i : ℤ =>
        (negOnePow i * cbz ell (i - 1)) •
          mode (YM v) (ell + 1 + n - i) (mode (YM u) (m + i) x))]
      exact finsum_congr fun i => by
        rw [show i + 1 - 1 = i by ring, negOnePow_succ,
          show ell + 1 + n - (i + 1) = ell + n - i by ring,
          show m + (i + 1) = m + 1 + i by ring, neg_mul, neg_smul]
    rw [step, finsum_neg_distrib', Pvu]
  have e2 : (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
      mode (YM v) (ell + (n + 1) - i) (mode (YM u) (m + i) x)) =
      Pvu YM u v x ell m (n + 1) := by rw [Pvu]
  rw [e1, e2, e3]
  abel

theorem BL_rec (u v : 𝒱) (x : M) (ell m n : ℤ) :
    BL YM u v x ell (m + 1) n = BL YM u v x ell m (n + 1) + BL YM u v x (ell + 1) m n := by
  simp only [BL, Puv_rec htr u v x ell m n, Pvu_rec htr u v x ell m n, negOnePow_succ]
  module

/-- `BL` as a single `finsum` (the form appearing in `WeakModule.jacobi`). -/
theorem BL_as_finsum (u v : 𝒱) (x : M) (ell m n : ℤ) :
    BL YM u v x ell m n = ∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
      (mode (YM u) (ell + m - i) (mode (YM v) (n + i) x) -
        negOnePow ell • mode (YM v) (ell + n - i) (mode (YM u) (m + i) x)) := by
  have hf : (Function.support fun i : ℤ =>
      -((negOnePow i * cbz ell i) •
        (negOnePow ell • mode (YM v) (ell + n - i) (mode (YM u) (m + i) x)))).Finite := by
    refine (Pvu_fin htr u v x ell m n).subset fun i hi => ?_
    simp only [Function.mem_support] at hi ⊢
    intro hz
    exact hi (by rw [smul_comm, hz, smul_zero, neg_zero])
  symm
  rw [show (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
        (mode (YM u) (ell + m - i) (mode (YM v) (n + i) x) -
          negOnePow ell • mode (YM v) (ell + n - i) (mode (YM u) (m + i) x))) =
      ∑ᶠ i : ℤ, ((negOnePow i * cbz ell i) •
          mode (YM u) (ell + m - i) (mode (YM v) (n + i) x) +
        -((negOnePow i * cbz ell i) •
          (negOnePow ell • mode (YM v) (ell + n - i) (mode (YM u) (m + i) x)))) from
      finsum_congr fun i => by rw [smul_sub, sub_eq_add_neg],
    finsum_add_distrib (Puv_fin htr u v x ell m n) hf,
    finsum_neg_distrib',
    show (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
        (negOnePow ell • mode (YM v) (ell + n - i) (mode (YM u) (m + i) x))) =
        negOnePow ell • Pvu YM u v x ell m n from by
      rw [Pvu, smul_finsum' (negOnePow ell) (Pvu_fin htr u v x ell m n)]
      exact finsum_congr fun i => by rw [smul_comm],
    BL, Puv, ← sub_eq_add_neg]

end Trunc2

/-! ## Reduction to homogeneous states -/

section Homog

variable (htr : Truncated YM)
include htr

theorem Puv_add_left (u u' v : 𝒱) (x : M) (ell m n : ℤ) :
    Puv YM (u + u') v x ell m n = Puv YM u v x ell m n + Puv YM u' v x ell m n := by
  unfold Puv
  rw [← finsum_add_distrib (Puv_fin htr u v x ell m n) (Puv_fin htr u' v x ell m n)]
  refine finsum_congr fun i => ?_
  rw [map_add, mode_add, LinearMap.add_apply, smul_add]

theorem Puv_add_right (u v v' : 𝒱) (x : M) (ell m n : ℤ) :
    Puv YM u (v + v') x ell m n = Puv YM u v x ell m n + Puv YM u v' x ell m n := by
  unfold Puv
  rw [← finsum_add_distrib (Puv_fin htr u v x ell m n) (Puv_fin htr u v' x ell m n)]
  refine finsum_congr fun i => ?_
  rw [map_add, mode_add, LinearMap.add_apply, map_add, smul_add]

theorem Pvu_add_left (u u' v : 𝒱) (x : M) (ell m n : ℤ) :
    Pvu YM (u + u') v x ell m n = Pvu YM u v x ell m n + Pvu YM u' v x ell m n := by
  unfold Pvu
  rw [← finsum_add_distrib (Pvu_fin htr u v x ell m n) (Pvu_fin htr u' v x ell m n)]
  refine finsum_congr fun i => ?_
  rw [map_add, mode_add, LinearMap.add_apply, map_add, smul_add]

theorem Pvu_add_right (u v v' : 𝒱) (x : M) (ell m n : ℤ) :
    Pvu YM u (v + v') x ell m n = Pvu YM u v x ell m n + Pvu YM u v' x ell m n := by
  unfold Pvu
  rw [← finsum_add_distrib (Pvu_fin htr u v x ell m n) (Pvu_fin htr u v' x ell m n)]
  refine finsum_congr fun i => ?_
  rw [map_add, mode_add, LinearMap.add_apply, smul_add]

theorem BL_add_left (u u' v : 𝒱) (x : M) (ell m n : ℤ) :
    BL YM (u + u') v x ell m n = BL YM u v x ell m n + BL YM u' v x ell m n := by
  simp only [BL, Puv_add_left htr, Pvu_add_left htr, smul_add]
  abel

theorem BL_add_right (u v v' : 𝒱) (x : M) (ell m n : ℤ) :
    BL YM u (v + v') x ell m n = BL YM u v x ell m n + BL YM u v' x ell m n := by
  simp only [BL, Puv_add_right htr, Pvu_add_right htr, smul_add]
  abel

omit htr in
theorem BR_add_left (u u' v : 𝒱) (x : M) (ell m n : ℤ) :
    BR W YM (u + u') v x ell m n = BR W YM u v x ell m n + BR W YM u' v x ell m n := by
  unfold BR
  rw [← finsum_add_distrib (BR_fin u v x ell m n) (BR_fin u' v x ell m n)]
  refine finsum_congr fun i => ?_
  rw [PreVertexAlgebra.smul_add_left, map_add, mode_add, LinearMap.add_apply, smul_add]

omit htr in
theorem BR_add_right (u v v' : 𝒱) (x : M) (ell m n : ℤ) :
    BR W YM u (v + v') x ell m n = BR W YM u v x ell m n + BR W YM u v' x ell m n := by
  unfold BR
  rw [← finsum_add_distrib (BR_fin u v x ell m n) (BR_fin u v' x ell m n)]
  refine finsum_congr fun i => ?_
  rw [PreVertexAlgebra.smul_add_right, map_add, mode_add, LinearMap.add_apply, smul_add]

omit htr in
theorem BL_zero_left (v : 𝒱) (x : M) (ell m n : ℤ) : BL YM 0 v x ell m n = 0 := by
  simp only [BL, Puv, Pvu, map_zero, mode_zero, LinearMap.zero_apply, smul_zero, finsum_zero,
    sub_zero]

omit htr in
theorem BL_zero_right (u : 𝒱) (x : M) (ell m n : ℤ) : BL YM u 0 x ell m n = 0 := by
  simp only [BL, Puv, Pvu, map_zero, mode_zero, LinearMap.zero_apply, smul_zero, finsum_zero,
    sub_zero]

omit htr in
theorem BR_zero_left (v : 𝒱) (x : M) (ell m n : ℤ) : BR W YM 0 v x ell m n = 0 := by
  simp only [BR, PreVertexAlgebra.smul_zero_left, map_zero, mode_zero, LinearMap.zero_apply,
    smul_zero, finsum_zero]

omit htr in
theorem BR_zero_right (u : 𝒱) (x : M) (ell m n : ℤ) : BR W YM u 0 x ell m n = 0 := by
  simp only [BR, PreVertexAlgebra.smul_zero_right, map_zero, mode_zero, LinearMap.zero_apply,
    smul_zero, finsum_zero]

/-- **One Borcherds instance for all states from the homogeneous ones.** -/
theorem borcherdsAt_of_homogeneous (x : M) (ell m n : ℤ)
    (h : ∀ (β γ : ℤ) (u v : 𝒱), u ∈ W.grading β → v ∈ W.grading γ →
      BL YM u v x ell m n = BR W YM u v x ell m n) (u v : 𝒱) :
    BL YM u v x ell m n = BR W YM u v x ell m n := by
  have hu : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; trivial
  have hv : v ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; trivial
  induction hu using Submodule.iSup_induction' with
  | mem β u hu =>
    induction hv using Submodule.iSup_induction' with
    | mem γ v hv => exact h β γ u v hu hv
    | zero => rw [BL_zero_right, BR_zero_right]
    | add v v' _ _ ih ih' => rw [BL_add_right htr, BR_add_right, ih, ih']
  | zero => rw [BL_zero_left, BR_zero_left]
  | add u u' _ _ ih ih' => rw [BL_add_left htr, BR_add_left, ih, ih']

end Homog

/-! ## The boundary instances in closed form -/

theorem negOnePow_zero' : negOnePow 0 = 1 := by simp [negOnePow]

/-- `BL` at `ℓ = 0` is the commutator. -/
theorem BL_ell_zero (u v : 𝒱) (x : M) (m n : ℤ) :
    BL YM u v x 0 m n
      = mode (YM u) m (mode (YM v) n x) - mode (YM v) n (mode (YM u) m x) := by
  rw [BL, Puv, Pvu,
    finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul]),
    finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])]
  simp only [negOnePow_zero', cbz_zero_left, if_pos, mul_one, one_smul, add_zero, zero_add,
    sub_zero]

/-- `BR` at `m = 0` is the iterate mode `(u_ℓ v)_n x`. -/
theorem BR_m_zero (u v : 𝒱) (x : M) (ell n : ℤ) :
    BR W YM u v x ell 0 n = mode (YM (W.smul u ell v)) n x := by
  rw [BR, finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul])]
  simp only [cbz_zero_left, if_pos, one_smul, add_zero, zero_add, sub_zero]

/-! ## Propagation from the two boundaries -/

omit [Module ℂ M] in
theorem antidiag_pin (D : ℤ → ℤ → M) (hrec : ∀ ell n : ℤ, D ell (n + 1) = -D (ell + 1) n)
    (hbd : ∀ n : ℤ, D 0 n = 0) : ∀ ell n : ℤ, D ell n = 0 := by
  have hpos : ∀ (j : ℕ) (n : ℤ), D (j : ℤ) n = 0 := by
    intro j
    induction j with
    | zero => intro n; simpa using hbd n
    | succ k ih =>
        intro n
        rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring]
        have hz : -D ((k : ℤ) + 1) n = 0 := by
          rw [← hrec (k : ℤ) n]
          exact ih (n + 1)
        exact neg_eq_zero.mp hz
  have hneg : ∀ (j : ℕ) (n : ℤ), D (-(j : ℤ)) n = 0 := by
    intro j
    induction j with
    | zero => intro n; simpa using hbd n
    | succ k ih =>
        intro n
        rw [show (-((k + 1 : ℕ) : ℤ)) = -(k : ℤ) - 1 by push_cast; ring]
        have hr := hrec (-(k : ℤ) - 1) (n - 1)
        rw [show (n - 1) + 1 = n by ring, show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring] at hr
        rw [hr, ih (n - 1), neg_zero]
  intro ell n
  rcases lt_or_ge ell 0 with hell | hell
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, ell = -(j : ℤ) := ⟨(-ell).toNat, by omega⟩
    exact hneg j n
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, ell = (j : ℤ) := ⟨ell.toNat, (Int.toNat_of_nonneg hell).symm⟩
    exact hpos j n

/-- The **commutator boundary** (`ℓ = 0`). -/
def CommutatorBoundary (W : VertexOperatorAlgebra 𝒱) (YM : 𝒱 →ₗ[ℂ] (End ℂ M)⟦z^±⟧) : Prop :=
  ∀ (u v : 𝒱) (x : M) (m n : ℤ), BL YM u v x 0 m n = BR W YM u v x 0 m n

/-- The **associator boundary** (`m = 0`). -/
def AssociatorBoundary (W : VertexOperatorAlgebra 𝒱) (YM : 𝒱 →ₗ[ℂ] (End ℂ M)⟦z^±⟧) : Prop :=
  ∀ (u v : 𝒱) (x : M) (ell n : ℤ), BL YM u v x ell 0 n = BR W YM u v x ell 0 n

/-- **The Borcherds identity from its two boundary families.** -/
theorem borcherds_of_boundaries (htr : Truncated YM) (hC : CommutatorBoundary W YM)
    (hA : AssociatorBoundary W YM) (u v : 𝒱) (x : M) (ell m n : ℤ) :
    BL YM u v x ell m n = BR W YM u v x ell m n := by
  induction m using Int.induction_on generalizing ell n with
  | zero => exact hA u v x ell n
  | succ k ih => rw [BL_rec htr, BR_rec, ih ell (n + 1), ih (ell + 1) n]
  | pred k ih =>
      have key := antidiag_pin
        (fun ell' n' => BL YM u v x ell' (-(k : ℤ) - 1) n' - BR W YM u v x ell' (-(k : ℤ) - 1) n')
        (fun ell' n' => by
          dsimp only
          have hbl := BL_rec htr u v x ell' (-(k : ℤ) - 1) n'
          have hbr := BR_rec (W := W) (YM := YM) u v x ell' (-(k : ℤ) - 1) n'
          rw [show (-(k : ℤ) - 1) + 1 = -(k : ℤ) by ring] at hbl hbr
          have hih := ih ell' n'
          rw [hbl, hbr] at hih
          rw [neg_sub, sub_eq_sub_iff_add_eq_add]
          exact hih.trans (add_comm _ _))
        (fun n' => by
          dsimp only
          rw [hC u v x (-(k : ℤ) - 1) n', sub_self])
        ell n
      exact sub_eq_zero.mp key

/-- **The module Jacobi identity (mode form of `WeakModule.jacobi`) from the boundaries.** -/
theorem jacobi_of_boundaries (htr : Truncated YM) (hC : CommutatorBoundary W YM)
    (hA : AssociatorBoundary W YM) (u v : 𝒱) (x : M) (ell m n : ℤ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
        (mode (YM u) (ell + m - i) (mode (YM v) (n + i) x)
          - negOnePow ell • mode (YM v) (ell + n - i) (mode (YM u) (m + i) x)))
      = ∑ᶠ i : ℤ, cbz m i • mode (YM (W.smul u (ell + i) v)) (m + n - i) x := by
  rw [← BL_as_finsum htr]
  exact borcherds_of_boundaries htr hC hA u v x ell m n

/-- **A weak module from the vacuum axiom, lower truncation, the commutator formula and the
associator formula.** -/
def ofBoundaries (YM : 𝒱 →ₗ[ℂ] (End ℂ M)⟦z^±⟧) (hvac : YM W.vacuum = 1)
    (htr : Truncated YM) (hC : CommutatorBoundary W YM) (hA : AssociatorBoundary W YM) :
    WeakModule W M where
  YM := YM
  vacuum_YM := hvac
  truncation := htr
  jacobi := jacobi_of_boundaries htr hC hA

@[simp] theorem ofBoundaries_YM (YM : 𝒱 →ₗ[ℂ] (End ℂ M)⟦z^±⟧) (hvac : YM W.vacuum = 1)
    (htr : Truncated YM) (hC : CommutatorBoundary W YM) (hA : AssociatorBoundary W YM) :
    (ofBoundaries YM hvac htr hC hA).YM = YM := rfl

/-- Conversely every weak module satisfies both boundary families. -/
theorem boundaries_of_weakModule (A : WeakModule W M) :
    Truncated A.YM ∧ CommutatorBoundary W A.YM ∧ AssociatorBoundary W A.YM := by
  refine ⟨A.truncation, fun u v x m n => ?_, fun u v x ell n => ?_⟩
  · rw [BL_as_finsum A.truncation]; exact A.jacobi u v x 0 m n
  · rw [BL_as_finsum A.truncation]; exact A.jacobi u v x ell 0 n

end VOA.Huang.AssocJacobiBoundary
