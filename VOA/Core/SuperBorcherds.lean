/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.SuperBorcherdsIdentity

/-!
# The super Borcherds / Jacobi identity

The final result of the super Borcherds chain: **`superJacobi`**, the Borcherds identity 5.1.7b for
a super vertex algebra, derived from super-locality (VA4) alone — no new axiom, no `sorry`.

`∑ᶠ i, (-1)ⁱ C(ℓ,i)·(u₍ℓ₊ₘ₋ᵢ₎(v₍ₙ₊ᵢ₎x) − ε(u,v)(-1)^ℓ·v₍ℓ₊ₙ₋ᵢ₎(u₍ₘ₊ᵢ₎x))`
`  = ∑ᶠ i, C(m,i)·(u₍ℓ₊ᵢ₎v)₍ₘ₊ₙ₋ᵢ₎x`,  `ε(u,v) = koszul |u| |v|`,

for parity-homogeneous `u, v`, all `x` and **all** integers `ℓ, m, n`.  This is *verbatim* the
`Modules.SuperWeakModule.jacobi` field, with the single exchanged-term scalar written as
`koszul p q * negOnePow ℓ`; the adjoint module instance is therefore immediate.

## Method — the bosonic architecture with one constant scalar

Exactly as in `Core.Borcherds`: the two sides satisfy a Pascal recursion
`B(ℓ,m+1,n) = B(ℓ,m,n+1) + B(ℓ+1,m,n)`, so Borcherds follows by a single `Int.induction_on`
with two bases — `m = 0` (the iterate formula `mode_iterateε`, `Core.SuperBorcherdsIdentity`)
and `ℓ = 0` (the commutator formula `commBoundε`, `Core.SuperNthProduct`) — the `m < 0` step
being pinned to the `ℓ = 0` column by `antidiag_pin`, which is reused verbatim.

The Koszul sign never interferes with the recursion: it is a **constant in `ℓ, m, n`**, so
`BL_recε` is the bosonic `BL_rec` with `negOnePow ℓ` replaced by `ε * negOnePow ℓ` and
`negOnePow_succ` applied to the same factor.  All the finiteness bookkeeping
(`BRs_fin`, `Puvs_fin`, …) is literally sign-free.

## Status
`sorry`-free, axiom-free: `#print axioms superJacobi = [propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

open Module (End)
open scoped BigOperators
open VertexOperatorAlgebra (negOnePow_eq_zpow finsum_nat_to_int)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperNearVOA

/-! ## §0  Two `n`-th-product triviality lemmas -/

theorem smul_zero_rightε (V : SuperNearVOA 𝒱) (u : 𝒱) (n : ℤ) : V.smul u n (0 : 𝒱) = 0 :=
  map_zero (mode (V.Y u) n)

theorem smul_zero_leftε (V : SuperNearVOA 𝒱) (n : ℤ) (x : 𝒱) : V.smul (0 : 𝒱) n x = 0 := by
  have h : V.Y (0 : 𝒱) = 0 := map_zero V.Y
  rw [SuperVertexAlgebra.smul_def, mode_apply, h]
  rfl

/-! ## §1  The two sides of the super Borcherds identity -/

/-- The right-hand side `∑ᶠ i, C(m,i)·(u₍ℓ₊ᵢ₎v)₍ₘ₊ₙ₋ᵢ₎x`.  Sign-free. -/
noncomputable def BRs (V : SuperNearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) : 𝒱 :=
  ∑ᶠ i : ℤ, cbz m i • V.smul (V.smul u (ℓ + i) v) (m + n - i) x

/-- The unexchanged half of the left-hand side.  Sign-free. -/
noncomputable def Puvs (V : SuperNearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) : 𝒱 :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • V.smul u (ℓ + m - i) (V.smul v (n + i) x)

/-- The exchanged half of the left-hand side.  Sign-free; the Koszul factor sits in `BLε`. -/
noncomputable def Pvus (V : SuperNearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) : 𝒱 :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • V.smul v (ℓ + n - i) (V.smul u (m + i) x)

/-- The left-hand side, with the single exchanged-term scalar `ε * (-1)^ℓ`. -/
noncomputable def BLε (V : SuperNearVOA 𝒱) (ε : ℂ) (u v x : 𝒱) (ℓ m n : ℤ) : 𝒱 :=
  Puvs V u v x ℓ m n - (ε * negOnePow ℓ) • Pvus V u v x ℓ m n

/-! ## §2  Support finiteness (sign-free, straight off VA5) -/

theorem BRs_fin (V : SuperNearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      cbz m i • V.smul (V.smul u (ℓ + i) v) (m + n - i) x).Finite := by
  obtain ⟨N, hN⟩ := V.regularity u v
  apply Set.Finite.subset (Set.finite_Icc 0 (N - ℓ))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg m h, zero_smul]
  · rw [show V.smul u (ℓ + i) v = mode (V.Y u) (ℓ + i) v from rfl, hN (ℓ + i) (by omega),
      smul_zero_leftε, smul_zero]

theorem Puvs_fin (V : SuperNearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ i) • V.smul u (ℓ + m - i) (V.smul v (n + i) x)).Finite := by
  obtain ⟨Nv, hNv⟩ := V.regularity v x
  apply Set.Finite.subset (Set.finite_Icc 0 (Nv - n))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · rw [show V.smul v (n + i) x = mode (V.Y v) (n + i) x from rfl, hNv (n + i) (by omega),
      smul_zero_rightε, smul_zero]

theorem Pvus_fin (V : SuperNearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ i) • V.smul v (ℓ + n - i) (V.smul u (m + i) x)).Finite := by
  obtain ⟨Nu, hNu⟩ := V.regularity u x
  apply Set.Finite.subset (Set.finite_Icc 0 (Nu - m))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · rw [show V.smul u (m + i) x = mode (V.Y u) (m + i) x from rfl, hNu (m + i) (by omega),
      smul_zero_rightε, smul_zero]

theorem Puvs_fin' (V : SuperNearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ (i - 1)) • V.smul u (ℓ + 1 + m - i) (V.smul v (n + i) x)).Finite := by
  obtain ⟨Nv, hNv⟩ := V.regularity v x
  apply Set.Finite.subset (Set.finite_Icc 1 (Nv - n))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ (by omega), mul_zero, zero_smul]
  · rw [show V.smul v (n + i) x = mode (V.Y v) (n + i) x from rfl, hNv (n + i) (by omega),
      smul_zero_rightε, smul_zero]

theorem Pvus_fin' (V : SuperNearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ (i - 1)) • V.smul v (ℓ + 1 + n - i) (V.smul u (m + i) x)).Finite := by
  obtain ⟨Nu, hNu⟩ := V.regularity u x
  apply Set.Finite.subset (Set.finite_Icc 1 (Nu - m))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ (by omega), mul_zero, zero_smul]
  · rw [show V.smul u (m + i) x = mode (V.Y u) (m + i) x from rfl, hNu (m + i) (by omega),
      smul_zero_rightε, smul_zero]

/-! ## §3  The Pascal recursions -/

theorem BRs_rec (V : SuperNearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    BRs V u v x ℓ (m + 1) n = BRs V u v x ℓ m (n + 1) + BRs V u v x (ℓ + 1) m n := by
  have fin2 : (Function.support fun i : ℤ =>
      cbz m (i - 1) • V.smul (V.smul u (ℓ + i) v) (m + 1 + n - i) x).Finite := by
    obtain ⟨N, hN⟩ := V.regularity u v
    apply Set.Finite.subset (Set.finite_Icc 1 (N - ℓ))
    intro i hi
    rw [Function.mem_support] at hi; rw [Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
    · rw [cbz_apply_neg m (by omega), zero_smul]
    · rw [show V.smul u (ℓ + i) v = mode (V.Y u) (ℓ + i) v from rfl, hN (ℓ + i) (by omega),
        smul_zero_leftε, smul_zero]
  rw [BRs, BRs, BRs,
    show (∑ᶠ i : ℤ, cbz (m + 1) i • V.smul (V.smul u (ℓ + i) v) (m + 1 + n - i) x)
        = ∑ᶠ i : ℤ, (cbz m i • V.smul (V.smul u (ℓ + i) v) (m + 1 + n - i) x
            + cbz m (i - 1) • V.smul (V.smul u (ℓ + i) v) (m + 1 + n - i) x) from
      finsum_congr fun i => by rw [cbz_pascal_up, add_smul],
    finsum_add_distrib (by
      have := BRs_fin V u v x ℓ m (n + 1)
      refine this.subset (fun i hi => ?_)
      simp only [Function.mem_support] at hi ⊢
      rw [show m + 1 + n - i = m + (n + 1) - i from by ring] at hi
      exact hi) fin2]
  congr 1
  · exact finsum_congr fun i => by rw [show m + 1 + n - i = m + (n + 1) - i from by ring]
  · rw [← finsum_int_succ_shift
      (fun i : ℤ => cbz m (i - 1) • V.smul (V.smul u (ℓ + i) v) (m + 1 + n - i) x)]
    exact finsum_congr fun i => by
      rw [show i + 1 - 1 = i from by ring, show ℓ + (i + 1) = (ℓ + 1) + i from by ring,
        show m + 1 + n - (i + 1) = m + n - i from by ring]

theorem Puvs_rec (V : SuperNearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    Puvs V u v x ℓ (m + 1) n = Puvs V u v x ℓ m (n + 1) + Puvs V u v x (ℓ + 1) m n := by
  have e1 : Puvs V u v x (ℓ + 1) m n
      = (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • V.smul u (ℓ + (m + 1) - i) (V.smul v (n + i) x))
        + ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
            V.smul u (ℓ + 1 + m - i) (V.smul v (n + i) x) := by
    rw [Puvs, show (∑ᶠ i : ℤ, (negOnePow i * cbz (ℓ + 1) i) •
            V.smul u (ℓ + 1 + m - i) (V.smul v (n + i) x))
          = ∑ᶠ i : ℤ, ((negOnePow i * cbz ℓ i) • V.smul u (ℓ + (m + 1) - i) (V.smul v (n + i) x)
              + (negOnePow i * cbz ℓ (i - 1)) •
                  V.smul u (ℓ + 1 + m - i) (V.smul v (n + i) x)) from
        finsum_congr fun i => by
          rw [cbz_pascal_up, mul_add, add_smul, show ℓ + 1 + m - i = ℓ + (m + 1) - i from by ring],
      finsum_add_distrib (Puvs_fin V u v x ℓ (m + 1) n) (Puvs_fin' V u v x ℓ m n)]
  have e2 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • V.smul u (ℓ + (m + 1) - i) (V.smul v (n + i) x))
      = Puvs V u v x ℓ (m + 1) n := by rw [Puvs]
  have e3 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
        V.smul u (ℓ + 1 + m - i) (V.smul v (n + i) x))
      = -Puvs V u v x ℓ m (n + 1) := by
    have step1 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
          V.smul u (ℓ + 1 + m - i) (V.smul v (n + i) x))
        = ∑ᶠ i : ℤ, -((negOnePow i * cbz ℓ i) •
            V.smul u (ℓ + m - i) (V.smul v (n + 1 + i) x)) := by
      rw [← finsum_int_succ_shift (fun i : ℤ => (negOnePow i * cbz ℓ (i - 1)) •
        V.smul u (ℓ + 1 + m - i) (V.smul v (n + i) x))]
      exact finsum_congr fun i => by
        rw [show i + 1 - 1 = i from by ring, negOnePow_succ,
          show ℓ + 1 + m - (i + 1) = ℓ + m - i from by ring,
          show n + (i + 1) = n + 1 + i from by ring, neg_mul, neg_smul]
    rw [step1, finsum_neg_distrib
      (fun i : ℤ => (negOnePow i * cbz ℓ i) • V.smul u (ℓ + m - i) (V.smul v (n + 1 + i) x)),
      Puvs]
  rw [e1, e2, e3]; abel

theorem Pvus_rec (V : SuperNearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    Pvus V u v x ℓ (m + 1) n = Pvus V u v x ℓ m (n + 1) - Pvus V u v x (ℓ + 1) m n := by
  have e1 : Pvus V u v x (ℓ + 1) m n
      = (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • V.smul v (ℓ + (n + 1) - i) (V.smul u (m + i) x))
        + ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
            V.smul v (ℓ + 1 + n - i) (V.smul u (m + i) x) := by
    rw [Pvus, show (∑ᶠ i : ℤ, (negOnePow i * cbz (ℓ + 1) i) •
            V.smul v (ℓ + 1 + n - i) (V.smul u (m + i) x))
          = ∑ᶠ i : ℤ, ((negOnePow i * cbz ℓ i) • V.smul v (ℓ + (n + 1) - i) (V.smul u (m + i) x)
              + (negOnePow i * cbz ℓ (i - 1)) •
                  V.smul v (ℓ + 1 + n - i) (V.smul u (m + i) x)) from
        finsum_congr fun i => by
          rw [cbz_pascal_up, mul_add, add_smul, show ℓ + 1 + n - i = ℓ + (n + 1) - i from by ring],
      finsum_add_distrib (Pvus_fin V u v x ℓ m (n + 1)) (Pvus_fin' V u v x ℓ m n)]
  have e2 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • V.smul v (ℓ + (n + 1) - i) (V.smul u (m + i) x))
      = Pvus V u v x ℓ m (n + 1) := by rw [Pvus]
  have e3 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
        V.smul v (ℓ + 1 + n - i) (V.smul u (m + i) x))
      = -Pvus V u v x ℓ (m + 1) n := by
    have step1 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
          V.smul v (ℓ + 1 + n - i) (V.smul u (m + i) x))
        = ∑ᶠ i : ℤ, -((negOnePow i * cbz ℓ i) •
            V.smul v (ℓ + n - i) (V.smul u (m + 1 + i) x)) := by
      rw [← finsum_int_succ_shift (fun i : ℤ => (negOnePow i * cbz ℓ (i - 1)) •
        V.smul v (ℓ + 1 + n - i) (V.smul u (m + i) x))]
      exact finsum_congr fun i => by
        rw [show i + 1 - 1 = i from by ring, negOnePow_succ,
          show ℓ + 1 + n - (i + 1) = ℓ + n - i from by ring,
          show m + (i + 1) = m + 1 + i from by ring, neg_mul, neg_smul]
    rw [step1, finsum_neg_distrib
      (fun i : ℤ => (negOnePow i * cbz ℓ i) • V.smul v (ℓ + n - i) (V.smul u (m + 1 + i) x)),
      Pvus]
  rw [e1, e2, e3]; abel

/-- **The Pascal recursion for the left-hand side.**  The Koszul factor is constant in
`ℓ, m, n`, so this is the bosonic recursion with `negOnePow ℓ` replaced by `ε * negOnePow ℓ`. -/
theorem BL_recε (V : SuperNearVOA 𝒱) (ε : ℂ) (u v x : 𝒱) (ℓ m n : ℤ) :
    BLε V ε u v x ℓ (m + 1) n = BLε V ε u v x ℓ m (n + 1) + BLε V ε u v x (ℓ + 1) m n := by
  simp only [BLε, Puvs_rec V u v x ℓ m n, Pvus_rec V u v x ℓ m n, negOnePow_succ, mul_neg]
  module

/-! ## §4  `BL` as a single `finsum`, and the two bases -/

theorem BRs_zero (V : SuperNearVOA 𝒱) (u v x : 𝒱) (ℓ n : ℤ) :
    BRs V u v x ℓ 0 n = V.smul (V.smul u ℓ v) n x := by
  rw [BRs, finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul])]
  rw [cbz_zero_left, if_pos rfl, one_smul, show ℓ + (0 : ℤ) = ℓ from by ring,
    show (0 : ℤ) + n - 0 = n from by ring]

/-- `BLε` as a single `finsum` — the exact left-hand side of `SuperWeakModule.jacobi`. -/
theorem BL_as_finsumε (V : SuperNearVOA 𝒱) (ε : ℂ) (u v x : 𝒱) (ℓ m n : ℤ) :
    BLε V ε u v x ℓ m n = ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
      (V.smul u (ℓ + m - i) (V.smul v (n + i) x)
        - (ε * negOnePow ℓ) • V.smul v (ℓ + n - i) (V.smul u (m + i) x)) := by
  have hfQn : (Function.support fun i : ℤ =>
      -((negOnePow i * cbz ℓ i) •
        ((ε * negOnePow ℓ) • V.smul v (ℓ + n - i) (V.smul u (m + i) x)))).Finite := by
    refine (Pvus_fin V u v x ℓ m n).subset (fun i hi => ?_)
    simp only [Function.mem_support] at hi ⊢
    intro h; exact hi (by rw [smul_comm, h, smul_zero, neg_zero])
  symm
  rw [show (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
            (V.smul u (ℓ + m - i) (V.smul v (n + i) x)
              - (ε * negOnePow ℓ) • V.smul v (ℓ + n - i) (V.smul u (m + i) x)))
        = ∑ᶠ i : ℤ, ((negOnePow i * cbz ℓ i) • V.smul u (ℓ + m - i) (V.smul v (n + i) x)
            + -((negOnePow i * cbz ℓ i) •
                ((ε * negOnePow ℓ) • V.smul v (ℓ + n - i) (V.smul u (m + i) x))))
      from finsum_congr fun i => by rw [smul_sub, sub_eq_add_neg],
    finsum_add_distrib (Puvs_fin V u v x ℓ m n) hfQn, finsum_neg_distrib,
    show (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
            ((ε * negOnePow ℓ) • V.smul v (ℓ + n - i) (V.smul u (m + i) x)))
        = (ε * negOnePow ℓ) • Pvus V u v x ℓ m n from by
        rw [Pvus, smul_finsum' (ε * negOnePow ℓ) (Pvus_fin V u v x ℓ m n)]
        exact finsum_congr fun i => by rw [smul_comm],
    BLε, Puvs, ← sub_eq_add_neg]

/-- **Base case (`m = 0`)**: the super iterate formula `mode_iterateε`. -/
theorem borcherds_baseε (V : SuperNearVOA 𝒱) {p q : ZMod 2} {u v : 𝒱} (hu : u ∈ V.parity p)
    (hv : v ∈ V.parity q) (x : 𝒱) (ℓ n : ℤ) :
    BLε V (koszul p q) u v x ℓ 0 n = BRs V u v x ℓ 0 n := by
  rw [BRs_zero, BL_as_finsumε, mode_iterateε V hu hv ℓ n x,
    finsum_nat_to_int _
      (fun t : ℤ => (negOnePow t * cbz ℓ t) •
        (V.smul u (ℓ - t) (V.smul v (n + t) x)
          - (koszul p q * negOnePow ℓ) • V.smul v (ℓ + n - t) (V.smul u t x)))
      (fun t ht => by simp only [cbz_apply_neg ℓ ht, mul_zero, zero_smul])
      (fun j => by
        simp only [negOnePow_eq_zpow, cbz_apply_nonneg ℓ (Int.natCast_nonneg j),
          Int.toNat_natCast, zpow_natCast])]
  exact finsum_congr fun i => by
    rw [show ℓ + (0 : ℤ) - i = ℓ - i from by ring, show (0 : ℤ) + i = i from by ring]

/-- **Boundary case (`ℓ = 0`)**: the super commutator formula `commBoundε`. -/
theorem borcherds_boundaryε (V : SuperNearVOA 𝒱) {p q : ZMod 2} {u v : 𝒱} (hu : u ∈ V.parity p)
    (hv : v ∈ V.parity q) (x : 𝒱) (m n : ℤ) :
    BLε V (koszul p q) u v x 0 m n = BRs V u v x 0 m n := by
  obtain ⟨N, hzero, hcomm⟩ := commBoundε V hu hv m n
  have e0 : negOnePow (0 : ℤ) = 1 := by rw [negOnePow_eq_zpow]; norm_num
  have hBL : BLε V (koszul p q) u v x 0 m n
      = (modeBracketε (koszul p q) (V.Y u) (V.Y v) m n) x := by
    rw [BLε, Puvs, Pvus,
      finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul]),
      finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])]
    simp only [e0, cbz_zero_left, if_pos, mul_one, one_mul, one_smul, add_zero, zero_add, sub_zero]
    rw [modeBracketε_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Module.End.mul_apply]
    rfl
  have hcommx : (modeBracketε (koszul p q) (V.Y u) (V.Y v) m n) x
      = ∑ j : Fin N, gBinom m (j : ℕ) • V.smul (V.smul u (j : ℕ) v) (m + n - (j : ℕ)) x := by
    rw [hcomm, LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => by rw [LinearMap.smul_apply]; rfl)
  have hBR : BRs V u v x 0 m n
      = ∑ j : Fin N, gBinom m (j : ℕ) • V.smul (V.smul u (j : ℕ) v) (m + n - (j : ℕ)) x := by
    rw [BRs, show (∑ᶠ i : ℤ, cbz m i • V.smul (V.smul u (0 + i) v) (m + n - i) x)
          = ∑ᶠ i : ℤ, cbz m i • V.smul (V.smul u i v) (m + n - i) x
        from finsum_congr fun i => by rw [zero_add],
      show (∑ᶠ i : ℤ, cbz m i • V.smul (V.smul u i v) (m + n - i) x)
          = ∑ᶠ j : ℕ, cbz m (j : ℤ) • V.smul (V.smul u (j : ℤ) v) (m + n - (j : ℤ)) x
        from (finsum_nat_to_int _ _
          (fun t ht => by simp only [cbz_apply_neg m ht, zero_smul]) (fun j => rfl)).symm,
      finsum_eq_finsetSum_of_support_subset _ (s := Finset.range N) (by
        intro i hi
        rw [Function.mem_support] at hi
        by_contra hc
        rw [Finset.coe_range, Set.mem_Iio, not_lt] at hc
        exact hi (by rw [hzero i hc, smul_zero_leftε, smul_zero])),
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun j _ => by
      rw [cbz_apply_nonneg m (Int.natCast_nonneg _), Int.toNat_natCast])
  rw [hBL, hcommx, hBR]

/-! ## §5  The super Borcherds identity -/

/-- **The super Borcherds identity 5.1.7b**, for arbitrary `ℓ, m, n`, in `BL = BR` form. -/
theorem superBorcherds (V : SuperNearVOA 𝒱) {p q : ZMod 2} {u v : 𝒱} (hu : u ∈ V.parity p)
    (hv : v ∈ V.parity q) (x : 𝒱) (ℓ m n : ℤ) :
    BLε V (koszul p q) u v x ℓ m n = BRs V u v x ℓ m n := by
  induction m using Int.induction_on generalizing ℓ n with
  | zero => exact borcherds_baseε V hu hv x ℓ n
  | succ k ih => rw [BL_recε, BRs_rec, ih ℓ (n + 1), ih (ℓ + 1) n]
  | pred k ih =>
      have key := antidiag_pin
        (fun ℓ' n' => BLε V (koszul p q) u v x ℓ' (-(k : ℤ) - 1) n'
          - BRs V u v x ℓ' (-(k : ℤ) - 1) n')
        (fun ℓ' n' => by
          dsimp only
          have hbl := BL_recε V (koszul p q) u v x ℓ' (-(k : ℤ) - 1) n'
          have hbr := BRs_rec V u v x ℓ' (-(k : ℤ) - 1) n'
          rw [show (-(k : ℤ) - 1) + 1 = -(k : ℤ) from by ring] at hbl hbr
          have hih := ih ℓ' n'
          rw [hbl, hbr] at hih
          rw [neg_sub, sub_eq_sub_iff_add_eq_add]
          exact hih.trans (add_comm _ _))
        (fun n' => by
          dsimp only
          rw [borcherds_boundaryε V hu hv x (-(k : ℤ) - 1) n', sub_self])
        ℓ n
      exact sub_eq_zero.mp key

/-- **The super Jacobi / Borcherds master identity**, in fully explicit mode form.

For parity-homogeneous `u ∈ 𝒱_p`, `v ∈ 𝒱_q`, every `x` and **all** integers `ℓ, m, n`:

`∑ᶠ i, (-1)ⁱ C(ℓ,i)·(u₍ℓ₊ₘ₋ᵢ₎(v₍ₙ₊ᵢ₎x) − (ε·(-1)^ℓ)·v₍ℓ₊ₙ₋ᵢ₎(u₍ₘ₊ᵢ₎x))`
`  = ∑ᶠ i, C(m,i)·(u₍ℓ₊ᵢ₎v)₍ₘ₊ₙ₋ᵢ₎x`,  `ε = koszul p q`.

This is verbatim the `Modules.SuperWeakModule.jacobi` shape (with `V.smul u n x` in place of
`mode (YM u) n x`, which is definitionally the same for `YM := V.Y`).  It is derived from
super-locality VA4 alone; at trivial parity `koszul 0 q = 1` it is the bosonic
`Core.Borcherds.jacobi` on the nose. -/
theorem superJacobi (V : SuperNearVOA 𝒱) {p q : ZMod 2} {u v : 𝒱} (hu : u ∈ V.parity p)
    (hv : v ∈ V.parity q) (x : 𝒱) (ℓ m n : ℤ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (V.smul u (ℓ + m - i) (V.smul v (n + i) x)
          - (koszul p q * negOnePow ℓ) • V.smul v (ℓ + n - i) (V.smul u (m + i) x)))
      = ∑ᶠ i : ℤ, cbz m i • V.smul (V.smul u (ℓ + i) v) (m + n - i) x := by
  have h := superBorcherds V hu hv x ℓ m n
  rwa [BL_as_finsumε, BRs] at h

/-- Sanity check: at trivial parity on the left the Koszul factor disappears and the identity
is literally the bosonic Jacobi identity. -/
theorem superJacobi_even_left (V : SuperNearVOA 𝒱) {q : ZMod 2} {u v : 𝒱}
    (hu : u ∈ V.parity 0) (hv : v ∈ V.parity q) (x : 𝒱) (ℓ m n : ℤ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (V.smul u (ℓ + m - i) (V.smul v (n + i) x)
          - negOnePow ℓ • V.smul v (ℓ + n - i) (V.smul u (m + i) x)))
      = ∑ᶠ i : ℤ, cbz m i • V.smul (V.smul u (ℓ + i) v) (m + n - i) x := by
  have h := superJacobi V hu hv x ℓ m n
  rwa [koszul_zero_left, one_mul] at h

end SuperNearVOA

end VOA
