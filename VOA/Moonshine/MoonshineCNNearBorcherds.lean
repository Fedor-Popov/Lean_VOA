import VOA.Moonshine.MoonshineCNNearIterate
import VOA.Core.SuperBorcherds

/-! Borcherds identity for every near-VOA, from finite-support Pascal recursion. -/

namespace VOA
open Module (End)
open scoped BigOperators
open VertexOperatorAlgebra (negOnePow_eq_zpow finsum_nat_to_int)
universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace NearVOA

theorem smul_zero_right (V : NearVOA 𝒱) (u : 𝒱) (n : ℤ) : V.smul u n (0 : 𝒱) = 0 :=
  map_zero (mode (V.Y u) n)

theorem smul_zero_left (V : NearVOA 𝒱) (n : ℤ) (x : 𝒱) : V.smul (0 : 𝒱) n x = 0 := by
  have h : V.Y (0 : 𝒱) = 0 := map_zero V.Y
  rw [smul_def, mode_apply, h]
  rfl

noncomputable def borcherdsIterateSum (V : NearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) : 𝒱 :=
  ∑ᶠ i : ℤ, cbz m i • V.smul (V.smul u (ℓ + i) v) (m + n - i) x

noncomputable def borcherdsForwardSum (V : NearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) : 𝒱 :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • V.smul u (ℓ + m - i) (V.smul v (n + i) x)

noncomputable def borcherdsReverseSum (V : NearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) : 𝒱 :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • V.smul v (ℓ + n - i) (V.smul u (m + i) x)

noncomputable def borcherdsProductSum (V : NearVOA 𝒱) (ε : ℂ) (u v x : 𝒱) (ℓ m n : ℤ) : 𝒱 :=
  borcherdsForwardSum V u v x ℓ m n - (ε * negOnePow ℓ) • borcherdsReverseSum V u v x ℓ m n

theorem borcherdsIterateSum_fin (V : NearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      cbz m i • V.smul (V.smul u (ℓ + i) v) (m + n - i) x).Finite := by
  obtain ⟨N, hN⟩ := V.regularity u v
  apply Set.Finite.subset (Set.finite_Icc 0 (N - ℓ))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg m h, zero_smul]
  · rw [show V.smul u (ℓ + i) v = mode (V.Y u) (ℓ + i) v from rfl, hN (ℓ + i) (by omega),
      smul_zero_left, smul_zero]

theorem borcherdsForwardSum_fin (V : NearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ i) • V.smul u (ℓ + m - i) (V.smul v (n + i) x)).Finite := by
  obtain ⟨Nv, hNv⟩ := V.regularity v x
  apply Set.Finite.subset (Set.finite_Icc 0 (Nv - n))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · rw [show V.smul v (n + i) x = mode (V.Y v) (n + i) x from rfl, hNv (n + i) (by omega),
      smul_zero_right, smul_zero]

theorem borcherdsReverseSum_fin (V : NearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ i) • V.smul v (ℓ + n - i) (V.smul u (m + i) x)).Finite := by
  obtain ⟨Nu, hNu⟩ := V.regularity u x
  apply Set.Finite.subset (Set.finite_Icc 0 (Nu - m))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · rw [show V.smul u (m + i) x = mode (V.Y u) (m + i) x from rfl, hNu (m + i) (by omega),
      smul_zero_right, smul_zero]

theorem borcherdsForwardSum_fin' (V : NearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ (i - 1)) • V.smul u (ℓ + 1 + m - i) (V.smul v (n + i) x)).Finite := by
  obtain ⟨Nv, hNv⟩ := V.regularity v x
  apply Set.Finite.subset (Set.finite_Icc 1 (Nv - n))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ (by omega), mul_zero, zero_smul]
  · rw [show V.smul v (n + i) x = mode (V.Y v) (n + i) x from rfl, hNv (n + i) (by omega),
      smul_zero_right, smul_zero]

theorem borcherdsReverseSum_fin' (V : NearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ (i - 1)) • V.smul v (ℓ + 1 + n - i) (V.smul u (m + i) x)).Finite := by
  obtain ⟨Nu, hNu⟩ := V.regularity u x
  apply Set.Finite.subset (Set.finite_Icc 1 (Nu - m))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ (by omega), mul_zero, zero_smul]
  · rw [show V.smul u (m + i) x = mode (V.Y u) (m + i) x from rfl, hNu (m + i) (by omega),
      smul_zero_right, smul_zero]

theorem borcherdsIterateSum_rec (V : NearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    borcherdsIterateSum V u v x ℓ (m + 1) n = borcherdsIterateSum V u v x ℓ m (n + 1) + borcherdsIterateSum V u v x (ℓ + 1) m n := by
  have fin2 : (Function.support fun i : ℤ =>
      cbz m (i - 1) • V.smul (V.smul u (ℓ + i) v) (m + 1 + n - i) x).Finite := by
    obtain ⟨N, hN⟩ := V.regularity u v
    apply Set.Finite.subset (Set.finite_Icc 1 (N - ℓ))
    intro i hi
    rw [Function.mem_support] at hi; rw [Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
    · rw [cbz_apply_neg m (by omega), zero_smul]
    · rw [show V.smul u (ℓ + i) v = mode (V.Y u) (ℓ + i) v from rfl, hN (ℓ + i) (by omega),
        smul_zero_left, smul_zero]
  rw [borcherdsIterateSum, borcherdsIterateSum, borcherdsIterateSum,
    show (∑ᶠ i : ℤ, cbz (m + 1) i • V.smul (V.smul u (ℓ + i) v) (m + 1 + n - i) x)
        = ∑ᶠ i : ℤ, (cbz m i • V.smul (V.smul u (ℓ + i) v) (m + 1 + n - i) x
            + cbz m (i - 1) • V.smul (V.smul u (ℓ + i) v) (m + 1 + n - i) x) from
      finsum_congr fun i => by rw [cbz_pascal_up, add_smul],
    finsum_add_distrib (by
      have := borcherdsIterateSum_fin V u v x ℓ m (n + 1)
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

theorem borcherdsForwardSum_rec (V : NearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    borcherdsForwardSum V u v x ℓ (m + 1) n = borcherdsForwardSum V u v x ℓ m (n + 1) + borcherdsForwardSum V u v x (ℓ + 1) m n := by
  have e1 : borcherdsForwardSum V u v x (ℓ + 1) m n
      = (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • V.smul u (ℓ + (m + 1) - i) (V.smul v (n + i) x))
        + ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
            V.smul u (ℓ + 1 + m - i) (V.smul v (n + i) x) := by
    rw [borcherdsForwardSum, show (∑ᶠ i : ℤ, (negOnePow i * cbz (ℓ + 1) i) •
            V.smul u (ℓ + 1 + m - i) (V.smul v (n + i) x))
          = ∑ᶠ i : ℤ, ((negOnePow i * cbz ℓ i) • V.smul u (ℓ + (m + 1) - i) (V.smul v (n + i) x)
              + (negOnePow i * cbz ℓ (i - 1)) •
                  V.smul u (ℓ + 1 + m - i) (V.smul v (n + i) x)) from
        finsum_congr fun i => by
          rw [cbz_pascal_up, mul_add, add_smul, show ℓ + 1 + m - i = ℓ + (m + 1) - i from by ring],
      finsum_add_distrib (borcherdsForwardSum_fin V u v x ℓ (m + 1) n) (borcherdsForwardSum_fin' V u v x ℓ m n)]
  have e2 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • V.smul u (ℓ + (m + 1) - i) (V.smul v (n + i) x))
      = borcherdsForwardSum V u v x ℓ (m + 1) n := by rw [borcherdsForwardSum]
  have e3 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
        V.smul u (ℓ + 1 + m - i) (V.smul v (n + i) x))
      = -borcherdsForwardSum V u v x ℓ m (n + 1) := by
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
      borcherdsForwardSum]
  rw [e1, e2, e3]; abel

theorem borcherdsReverseSum_rec (V : NearVOA 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    borcherdsReverseSum V u v x ℓ (m + 1) n = borcherdsReverseSum V u v x ℓ m (n + 1) - borcherdsReverseSum V u v x (ℓ + 1) m n := by
  have e1 : borcherdsReverseSum V u v x (ℓ + 1) m n
      = (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • V.smul v (ℓ + (n + 1) - i) (V.smul u (m + i) x))
        + ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
            V.smul v (ℓ + 1 + n - i) (V.smul u (m + i) x) := by
    rw [borcherdsReverseSum, show (∑ᶠ i : ℤ, (negOnePow i * cbz (ℓ + 1) i) •
            V.smul v (ℓ + 1 + n - i) (V.smul u (m + i) x))
          = ∑ᶠ i : ℤ, ((negOnePow i * cbz ℓ i) • V.smul v (ℓ + (n + 1) - i) (V.smul u (m + i) x)
              + (negOnePow i * cbz ℓ (i - 1)) •
                  V.smul v (ℓ + 1 + n - i) (V.smul u (m + i) x)) from
        finsum_congr fun i => by
          rw [cbz_pascal_up, mul_add, add_smul, show ℓ + 1 + n - i = ℓ + (n + 1) - i from by ring],
      finsum_add_distrib (borcherdsReverseSum_fin V u v x ℓ m (n + 1)) (borcherdsReverseSum_fin' V u v x ℓ m n)]
  have e2 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • V.smul v (ℓ + (n + 1) - i) (V.smul u (m + i) x))
      = borcherdsReverseSum V u v x ℓ m (n + 1) := by rw [borcherdsReverseSum]
  have e3 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
        V.smul v (ℓ + 1 + n - i) (V.smul u (m + i) x))
      = -borcherdsReverseSum V u v x ℓ (m + 1) n := by
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
      borcherdsReverseSum]
  rw [e1, e2, e3]; abel

theorem borcherdsProductSum_rec (V : NearVOA 𝒱) (ε : ℂ) (u v x : 𝒱) (ℓ m n : ℤ) :
    borcherdsProductSum V ε u v x ℓ (m + 1) n = borcherdsProductSum V ε u v x ℓ m (n + 1) + borcherdsProductSum V ε u v x (ℓ + 1) m n := by
  simp only [borcherdsProductSum, borcherdsForwardSum_rec V u v x ℓ m n, borcherdsReverseSum_rec V u v x ℓ m n, negOnePow_succ, mul_neg]
  module

theorem borcherdsIterateSum_zero (V : NearVOA 𝒱) (u v x : 𝒱) (ℓ n : ℤ) :
    borcherdsIterateSum V u v x ℓ 0 n = V.smul (V.smul u ℓ v) n x := by
  rw [borcherdsIterateSum, finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul])]
  rw [cbz_zero_left, if_pos rfl, one_smul, show ℓ + (0 : ℤ) = ℓ from by ring,
    show (0 : ℤ) + n - 0 = n from by ring]

theorem borcherdsProductSum_as_finsum (V : NearVOA 𝒱) (ε : ℂ) (u v x : 𝒱) (ℓ m n : ℤ) :
    borcherdsProductSum V ε u v x ℓ m n = ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
      (V.smul u (ℓ + m - i) (V.smul v (n + i) x)
        - (ε * negOnePow ℓ) • V.smul v (ℓ + n - i) (V.smul u (m + i) x)) := by
  have hfQn : (Function.support fun i : ℤ =>
      -((negOnePow i * cbz ℓ i) •
        ((ε * negOnePow ℓ) • V.smul v (ℓ + n - i) (V.smul u (m + i) x)))).Finite := by
    refine (borcherdsReverseSum_fin V u v x ℓ m n).subset (fun i hi => ?_)
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
    finsum_add_distrib (borcherdsForwardSum_fin V u v x ℓ m n) hfQn, finsum_neg_distrib,
    show (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
            ((ε * negOnePow ℓ) • V.smul v (ℓ + n - i) (V.smul u (m + i) x)))
        = (ε * negOnePow ℓ) • borcherdsReverseSum V u v x ℓ m n from by
        rw [borcherdsReverseSum, smul_finsum' (ε * negOnePow ℓ) (borcherdsReverseSum_fin V u v x ℓ m n)]
        exact finsum_congr fun i => by rw [smul_comm],
    borcherdsProductSum, borcherdsForwardSum, ← sub_eq_add_neg]

theorem borcherds_base (V : NearVOA 𝒱) (u v : 𝒱) (x : 𝒱) (ℓ n : ℤ) :
    borcherdsProductSum V ((1 : ℂ)) u v x ℓ 0 n = borcherdsIterateSum V u v x ℓ 0 n := by
  rw [borcherdsIterateSum_zero, borcherdsProductSum_as_finsum, mode_iterate V u v ℓ n x,
    finsum_nat_to_int _
      (fun t : ℤ => (negOnePow t * cbz ℓ t) •
        (V.smul u (ℓ - t) (V.smul v (n + t) x)
          - ((1 : ℂ) * negOnePow ℓ) • V.smul v (ℓ + n - t) (V.smul u t x)))
      (fun t ht => by simp only [cbz_apply_neg ℓ ht, mul_zero, zero_smul])
      (fun j => by
        simp only [negOnePow_eq_zpow, cbz_apply_nonneg ℓ (Int.natCast_nonneg j),
          Int.toNat_natCast, zpow_natCast])]
  exact finsum_congr fun i => by
    rw [show ℓ + (0 : ℤ) - i = ℓ - i from by ring, show (0 : ℤ) + i = i from by ring]

theorem borcherds_boundary (V : NearVOA 𝒱) (u v : 𝒱) (x : 𝒱) (m n : ℤ) :
    borcherdsProductSum V ((1 : ℂ)) u v x 0 m n = borcherdsIterateSum V u v x 0 m n := by
  obtain ⟨N, hzero, hcomm⟩ := commutator_bound V u v m n
  have e0 : negOnePow (0 : ℤ) = 1 := by rw [negOnePow_eq_zpow]; norm_num
  have hBL : borcherdsProductSum V ((1 : ℂ)) u v x 0 m n
      = (modeBracketε ((1 : ℂ)) (V.Y u) (V.Y v) m n) x := by
    rw [borcherdsProductSum, borcherdsForwardSum, borcherdsReverseSum,
      finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul]),
      finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])]
    simp only [e0, cbz_zero_left, if_pos, mul_one, one_mul, one_smul, add_zero, zero_add, sub_zero]
    rw [modeBracketε_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Module.End.mul_apply, one_smul]
    rfl
  have hcommx : (modeBracketε ((1 : ℂ)) (V.Y u) (V.Y v) m n) x
      = ∑ j : Fin N, gBinom m (j : ℕ) • V.smul (V.smul u (j : ℕ) v) (m + n - (j : ℕ)) x := by
    rw [hcomm, LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => by rw [LinearMap.smul_apply]; rfl)
  have hBR : borcherdsIterateSum V u v x 0 m n
      = ∑ j : Fin N, gBinom m (j : ℕ) • V.smul (V.smul u (j : ℕ) v) (m + n - (j : ℕ)) x := by
    rw [borcherdsIterateSum, show (∑ᶠ i : ℤ, cbz m i • V.smul (V.smul u (0 + i) v) (m + n - i) x)
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
        exact hi (by rw [hzero i hc, smul_zero_left, smul_zero])),
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun j _ => by
      rw [cbz_apply_nonneg m (Int.natCast_nonneg _), Int.toNat_natCast])
  rw [hBL, hcommx, hBR]

theorem borcherds (V : NearVOA 𝒱) (u v : 𝒱) (x : 𝒱) (ℓ m n : ℤ) :
    borcherdsProductSum V ((1 : ℂ)) u v x ℓ m n = borcherdsIterateSum V u v x ℓ m n := by
  induction m using Int.induction_on generalizing ℓ n with
  | zero => exact borcherds_base V u v x ℓ n
  | succ k ih => rw [borcherdsProductSum_rec, borcherdsIterateSum_rec, ih ℓ (n + 1), ih (ℓ + 1) n]
  | pred k ih =>
      have key := antidiag_pin
        (fun ℓ' n' => borcherdsProductSum V ((1 : ℂ)) u v x ℓ' (-(k : ℤ) - 1) n'
          - borcherdsIterateSum V u v x ℓ' (-(k : ℤ) - 1) n')
        (fun ℓ' n' => by
          dsimp only
          have hbl := borcherdsProductSum_rec V ((1 : ℂ)) u v x ℓ' (-(k : ℤ) - 1) n'
          have hbr := borcherdsIterateSum_rec V u v x ℓ' (-(k : ℤ) - 1) n'
          rw [show (-(k : ℤ) - 1) + 1 = -(k : ℤ) from by ring] at hbl hbr
          have hih := ih ℓ' n'
          rw [hbl, hbr] at hih
          rw [neg_sub, sub_eq_sub_iff_add_eq_add]
          exact hih.trans (add_comm _ _))
        (fun n' => by
          dsimp only
          rw [borcherds_boundary V u v x (-(k : ℤ) - 1) n', sub_self])
        ℓ n
      exact sub_eq_zero.mp key

theorem jacobi (V : NearVOA 𝒱) (u v : 𝒱) (x : 𝒱) (ℓ m n : ℤ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (V.smul u (ℓ + m - i) (V.smul v (n + i) x)
          - ((1 : ℂ) * negOnePow ℓ) • V.smul v (ℓ + n - i) (V.smul u (m + i) x)))
      = ∑ᶠ i : ℤ, cbz m i • V.smul (V.smul u (ℓ + i) v) (m + n - i) x := by
  have h := borcherds V u v x ℓ m n
  rwa [borcherdsProductSum_as_finsum, borcherdsIterateSum] at h

end NearVOA
end VOA
