import VOA.Core.BorcherdsIdentity

/-!
# Borcherds' identity 5.1.7b — full arbitrary `(ℓ, m, n)`  (Gannon §5.1.3, p. 321)

This file proves the **Borcherds identity** (Gannon 5.1.7b), applied to a vector `x`:
`∑ᶠ i, (-1)ⁱ C(ℓ,i)·(u₍ℓ₊ₘ₋ᵢ₎(v₍ₙ₊ᵢ₎x) − (-1)^ℓ·v₍ℓ₊ₙ₋ᵢ₎(u₍ₘ₊ᵢ₎x)) = ∑ᶠ i, C(m,i)·(u₍ℓ₊ᵢ₎v)₍ₘ₊ₙ₋ᵢ₎x`,
for ALL integers `ℓ, m, n` — encoded as `borcherds : BL = BR`.

## Method (no δ-functions, fully finite)

The two sides `BL`, `BR` (ℤ-`finsum`s with the integer binomial `cbz`) satisfy a Pascal recursion
`B(ℓ,m+1,n) = B(ℓ,m,n+1) + B(ℓ+1,m,n)` (`BL_rec`/`BR_rec`).  Borcherds is then a single induction on
`m` (`Int.induction_on`) with **two** bases:

* `m = 0` — `borcherds_base`, from the iterate formula `mode_iterate` (5.1.7d, all `ℓ`);
* `ℓ = 0` — `borcherds_boundary`, the commutator formula (5.1.7c, via `mode_commutator`).

For `m ≥ 0` the recursion + the `m=0` base close directly.  For `m < 0` the recursion gives an
anti-diagonal relation `D(ℓ,n+1) = −D(ℓ+1,n)` on the discrepancy `D = BL − BR`; the `ℓ=0` boundary
`D(0,·)=0` then pins `D ≡ 0` by stepping each point along its anti-diagonal to the `ℓ=0` column
(`antidiag_pin`).  This is exactly the "Vandermonde resummation combining `mode_iterate` +
`jacobi_commutator`" anticipated in `Core.BorcherdsIdentity` — with no formal-distribution
δ-calculus, no Fubini on divergent sums, and no new axioms.

`#print axioms borcherds = [propext, Classical.choice, Quot.sound]`.

## Dependencies
`Core.BorcherdsIdentity` (`mode_iterate`), `Core.Reconstruction` (`mode_commutator`,
`nth_product`), `Core.OPE` (`bracket_deltaSum`), `Core.WeakAssoc` (`finsum_nat_to_int`).
-/

namespace VOA
open Module (End)
open scoped BigOperators
universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

theorem finsum_neg_distrib {ι : Type*} {M : Type*} [AddCommGroup M] (f : ι → M) :
    (∑ᶠ i, -f i) = -∑ᶠ i, f i := by
  by_cases h : (Function.support f).Finite
  · rw [← neg_one_zsmul (∑ᶠ i, f i), smul_finsum' (-1 : ℤ) h]
    exact finsum_congr fun i => (neg_one_zsmul (f i)).symm
  · have h' : ¬ (Function.support fun i => -f i).Finite := by
      rwa [show (Function.support fun i => -f i) = Function.support f from by
        ext i; simp [Function.mem_support]]
    rw [finsum_of_infinite_support h', finsum_of_infinite_support h, neg_zero]

/-- **The anti-diagonal pin.**  A two-index family satisfying the anti-diagonal recursion
`D ℓ (n+1) = -D (ℓ+1) n` and vanishing on the `ℓ=0` column vanishes identically: each point
steps along its anti-diagonal to the `ℓ=0` boundary. -/
theorem antidiag_pin {M : Type*} [AddCommGroup M] (D : ℤ → ℤ → M)
    (hrec : ∀ ℓ n : ℤ, D ℓ (n + 1) = -D (ℓ + 1) n) (hbd : ∀ n : ℤ, D 0 n = 0) :
    ∀ ℓ n : ℤ, D ℓ n = 0 := by
  have hpos : ∀ (j : ℕ) (n : ℤ), D (j : ℤ) n = 0 := by
    intro j
    induction j with
    | zero => intro n; simpa using hbd n
    | succ k ih =>
        intro n
        rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 from by push_cast; ring]
        have hneg0 : -D ((k : ℤ) + 1) n = 0 := by rw [← hrec (k : ℤ) n]; exact ih (n + 1)
        exact neg_eq_zero.mp hneg0
  have hneg : ∀ (j : ℕ) (n : ℤ), D (-(j : ℤ)) n = 0 := by
    intro j
    induction j with
    | zero => intro n; simpa using hbd n
    | succ k ih =>
        intro n
        rw [show (-((k + 1 : ℕ) : ℤ)) = -(k : ℤ) - 1 from by push_cast; ring]
        have h := hrec (-(k : ℤ) - 1) (n - 1)
        rw [show (n - 1) + 1 = n from by ring, show -(k : ℤ) - 1 + 1 = -(k : ℤ) from by ring] at h
        rw [h, ih (n - 1), neg_zero]
  intro ℓ n
  rcases lt_or_ge ℓ 0 with hℓ | hℓ
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, ℓ = -(j : ℤ) := ⟨(-ℓ).toNat, by omega⟩
    exact hneg j n
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, ℓ = (j : ℤ) := ⟨ℓ.toNat, (Int.toNat_of_nonneg hℓ).symm⟩
    exact hpos j n

namespace VertexOperatorAlgebra

/-! ## The two sides of Borcherds (applied to `x`, `ℤ`-finsums with `cbz`). -/

noncomputable def BR (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) : 𝒱 :=
  ∑ᶠ i : ℤ, cbz m i • W.smul (W.smul u (ℓ + i) v) (m + n - i) x

noncomputable def Puv (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) : 𝒱 :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • W.smul u (ℓ + m - i) (W.smul v (n + i) x)

noncomputable def Pvu (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) : 𝒱 :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • W.smul v (ℓ + n - i) (W.smul u (m + i) x)

noncomputable def BL (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) : 𝒱 :=
  Puv W u v x ℓ m n - negOnePow ℓ • Pvu W u v x ℓ m n

theorem BR_fin (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ => cbz m i • W.smul (W.smul u (ℓ + i) v) (m + n - i) x).Finite := by
  obtain ⟨N, hN⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
  apply Set.Finite.subset (Set.finite_Icc 0 (N - ℓ))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg m h, zero_smul]
  · rw [hN (ℓ + i) (by omega), W.smul_zero_left, smul_zero]

theorem Puv_fin (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ i) • W.smul u (ℓ + m - i) (W.smul v (n + i) x)).Finite := by
  obtain ⟨Nv, hNv⟩ := W.toPreVertexAlgebra.smul_eventually_zero v x
  apply Set.Finite.subset (Set.finite_Icc 0 (Nv - n))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · rw [hNv (n + i) (by omega), W.smul_zero_right, smul_zero]

theorem Pvu_fin (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ i) • W.smul v (ℓ + n - i) (W.smul u (m + i) x)).Finite := by
  obtain ⟨Nu, hNu⟩ := W.toPreVertexAlgebra.smul_eventually_zero u x
  apply Set.Finite.subset (Set.finite_Icc 0 (Nu - m))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · rw [hNu (m + i) (by omega), W.smul_zero_right, smul_zero]

theorem Puv_fin' (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ (i - 1)) • W.smul u (ℓ + 1 + m - i) (W.smul v (n + i) x)).Finite := by
  obtain ⟨Nv, hNv⟩ := W.toPreVertexAlgebra.smul_eventually_zero v x
  apply Set.Finite.subset (Set.finite_Icc 1 (Nv - n))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ (by omega), mul_zero, zero_smul]
  · rw [hNv (n + i) (by omega), W.smul_zero_right, smul_zero]

theorem Pvu_fin' (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ (i - 1)) • W.smul v (ℓ + 1 + n - i) (W.smul u (m + i) x)).Finite := by
  obtain ⟨Nu, hNu⟩ := W.toPreVertexAlgebra.smul_eventually_zero u x
  apply Set.Finite.subset (Set.finite_Icc 1 (Nu - m))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ (by omega), mul_zero, zero_smul]
  · rw [hNu (m + i) (by omega), W.smul_zero_right, smul_zero]

theorem BR_rec (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    BR W u v x ℓ (m + 1) n = BR W u v x ℓ m (n + 1) + BR W u v x (ℓ + 1) m n := by
  have fin2 : (Function.support fun i : ℤ =>
      cbz m (i - 1) • W.smul (W.smul u (ℓ + i) v) (m + 1 + n - i) x).Finite := by
    obtain ⟨N, hN⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
    apply Set.Finite.subset (Set.finite_Icc 1 (N - ℓ))
    intro i hi
    rw [Function.mem_support] at hi; rw [Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
    · rw [cbz_apply_neg m (by omega), zero_smul]
    · rw [hN (ℓ + i) (by omega), W.smul_zero_left, smul_zero]
  rw [BR, BR, BR,
    show (∑ᶠ i : ℤ, cbz (m + 1) i • W.smul (W.smul u (ℓ + i) v) (m + 1 + n - i) x)
        = ∑ᶠ i : ℤ, (cbz m i • W.smul (W.smul u (ℓ + i) v) (m + 1 + n - i) x
            + cbz m (i - 1) • W.smul (W.smul u (ℓ + i) v) (m + 1 + n - i) x) from
      finsum_congr fun i => by rw [cbz_pascal_up, add_smul],
    finsum_add_distrib (by
      have := BR_fin W u v x ℓ m (n + 1)
      refine this.subset (fun i hi => ?_)
      simp only [Function.mem_support] at hi ⊢
      rw [show m + 1 + n - i = m + (n + 1) - i from by ring] at hi
      exact hi) fin2]
  congr 1
  · exact finsum_congr fun i => by rw [show m + 1 + n - i = m + (n + 1) - i from by ring]
  · rw [← finsum_int_succ_shift
      (fun i : ℤ => cbz m (i - 1) • W.smul (W.smul u (ℓ + i) v) (m + 1 + n - i) x)]
    exact finsum_congr fun i => by
      rw [show i + 1 - 1 = i from by ring, show ℓ + (i + 1) = (ℓ + 1) + i from by ring,
        show m + 1 + n - (i + 1) = m + n - i from by ring]

theorem Puv_rec (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    Puv W u v x ℓ (m + 1) n = Puv W u v x ℓ m (n + 1) + Puv W u v x (ℓ + 1) m n := by
  have e1 : Puv W u v x (ℓ + 1) m n
      = (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • W.smul u (ℓ + (m + 1) - i) (W.smul v (n + i) x))
        + ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) • W.smul u (ℓ + 1 + m - i) (W.smul v (n + i) x) := by
    rw [Puv, show (∑ᶠ i : ℤ, (negOnePow i * cbz (ℓ + 1) i) •
            W.smul u (ℓ + 1 + m - i) (W.smul v (n + i) x))
          = ∑ᶠ i : ℤ, ((negOnePow i * cbz ℓ i) • W.smul u (ℓ + (m + 1) - i) (W.smul v (n + i) x)
              + (negOnePow i * cbz ℓ (i - 1)) • W.smul u (ℓ + 1 + m - i) (W.smul v (n + i) x)) from
        finsum_congr fun i => by
          rw [cbz_pascal_up, mul_add, add_smul, show ℓ + 1 + m - i = ℓ + (m + 1) - i from by ring],
      finsum_add_distrib (Puv_fin W u v x ℓ (m + 1) n) (Puv_fin' W u v x ℓ m n)]
  have e2 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • W.smul u (ℓ + (m + 1) - i) (W.smul v (n + i) x))
      = Puv W u v x ℓ (m + 1) n := by rw [Puv]
  have e3 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) • W.smul u (ℓ + 1 + m - i) (W.smul v (n + i) x))
      = -Puv W u v x ℓ m (n + 1) := by
    have step1 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) • W.smul u (ℓ + 1 + m - i) (W.smul v (n + i) x))
        = ∑ᶠ i : ℤ, -((negOnePow i * cbz ℓ i) • W.smul u (ℓ + m - i) (W.smul v (n + 1 + i) x)) := by
      rw [← finsum_int_succ_shift
        (fun i : ℤ => (negOnePow i * cbz ℓ (i - 1)) • W.smul u (ℓ + 1 + m - i) (W.smul v (n + i) x))]
      exact finsum_congr fun i => by
        rw [show i + 1 - 1 = i from by ring, negOnePow_succ,
          show ℓ + 1 + m - (i + 1) = ℓ + m - i from by ring, show n + (i + 1) = n + 1 + i from by ring,
          neg_mul, neg_smul]
    rw [step1, finsum_neg_distrib
      (fun i : ℤ => (negOnePow i * cbz ℓ i) • W.smul u (ℓ + m - i) (W.smul v (n + 1 + i) x)), Puv]
  rw [e1, e2, e3]; abel

theorem Pvu_rec (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    Pvu W u v x ℓ (m + 1) n = Pvu W u v x ℓ m (n + 1) - Pvu W u v x (ℓ + 1) m n := by
  have e1 : Pvu W u v x (ℓ + 1) m n
      = (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • W.smul v (ℓ + (n + 1) - i) (W.smul u (m + i) x))
        + ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) • W.smul v (ℓ + 1 + n - i) (W.smul u (m + i) x) := by
    rw [Pvu, show (∑ᶠ i : ℤ, (negOnePow i * cbz (ℓ + 1) i) •
            W.smul v (ℓ + 1 + n - i) (W.smul u (m + i) x))
          = ∑ᶠ i : ℤ, ((negOnePow i * cbz ℓ i) • W.smul v (ℓ + (n + 1) - i) (W.smul u (m + i) x)
              + (negOnePow i * cbz ℓ (i - 1)) • W.smul v (ℓ + 1 + n - i) (W.smul u (m + i) x)) from
        finsum_congr fun i => by
          rw [cbz_pascal_up, mul_add, add_smul, show ℓ + 1 + n - i = ℓ + (n + 1) - i from by ring],
      finsum_add_distrib (Pvu_fin W u v x ℓ m (n + 1)) (Pvu_fin' W u v x ℓ m n)]
  have e2 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • W.smul v (ℓ + (n + 1) - i) (W.smul u (m + i) x))
      = Pvu W u v x ℓ m (n + 1) := by rw [Pvu]
  have e3 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) • W.smul v (ℓ + 1 + n - i) (W.smul u (m + i) x))
      = -Pvu W u v x ℓ (m + 1) n := by
    have step1 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) • W.smul v (ℓ + 1 + n - i) (W.smul u (m + i) x))
        = ∑ᶠ i : ℤ, -((negOnePow i * cbz ℓ i) • W.smul v (ℓ + n - i) (W.smul u (m + 1 + i) x)) := by
      rw [← finsum_int_succ_shift
        (fun i : ℤ => (negOnePow i * cbz ℓ (i - 1)) • W.smul v (ℓ + 1 + n - i) (W.smul u (m + i) x))]
      exact finsum_congr fun i => by
        rw [show i + 1 - 1 = i from by ring, negOnePow_succ,
          show ℓ + 1 + n - (i + 1) = ℓ + n - i from by ring, show m + (i + 1) = m + 1 + i from by ring,
          neg_mul, neg_smul]
    rw [step1, finsum_neg_distrib
      (fun i : ℤ => (negOnePow i * cbz ℓ i) • W.smul v (ℓ + n - i) (W.smul u (m + 1 + i) x)), Pvu]
  rw [e1, e2, e3]; abel

theorem BL_rec (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    BL W u v x ℓ (m + 1) n = BL W u v x ℓ m (n + 1) + BL W u v x (ℓ + 1) m n := by
  simp only [BL, Puv_rec W u v x ℓ m n, Pvu_rec W u v x ℓ m n, negOnePow_succ]
  module

/-! ## Sign / binomial bridges between `negOnePow`/`cbz` and `(-1)^·`/`gBinom`.
(`negOnePow_natCast` and `negOnePow_neg'` already exist in Foundations/Core.) -/

theorem negOnePow_eq_zpow (ℓ : ℤ) : negOnePow ℓ = (-1 : ℂ) ^ ℓ := by
  rcases lt_or_ge ℓ 0 with hℓ | hℓ
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ℓ = -(k : ℤ) := ⟨(-ℓ).toNat, by omega⟩
    rw [negOnePow_neg', negOnePow_natCast, zpow_neg, zpow_natCast]
    rcases Nat.even_or_odd k with hk | hk
    · rw [hk.neg_one_pow, inv_one]
    · rw [hk.neg_one_pow]; norm_num
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ℓ = (k : ℤ) := ⟨ℓ.toNat, (Int.toNat_of_nonneg hℓ).symm⟩
    rw [negOnePow_natCast, zpow_natCast]

/-! ## Base case (`m=0`, via `mode_iterate`). -/

theorem BR_zero (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ n : ℤ) :
    BR W u v x ℓ 0 n = W.smul (W.smul u ℓ v) n x := by
  rw [BR, finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul])]
  rw [cbz_zero_left, if_pos rfl, one_smul, show ℓ + (0:ℤ) = ℓ from by ring,
    show (0:ℤ) + n - 0 = n from by ring]

/-- `BL` as a single `finsum` (combine `Puv − negOnePow ℓ • Pvu`). -/
theorem BL_as_finsum (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    BL W u v x ℓ m n = ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
      (W.smul u (ℓ + m - i) (W.smul v (n + i) x)
        - negOnePow ℓ • W.smul v (ℓ + n - i) (W.smul u (m + i) x)) := by
  have hfQn : (Function.support fun i : ℤ =>
      -((negOnePow i * cbz ℓ i) • (negOnePow ℓ • W.smul v (ℓ + n - i) (W.smul u (m + i) x)))).Finite := by
    refine (Pvu_fin W u v x ℓ m n).subset (fun i hi => ?_)
    simp only [Function.mem_support] at hi ⊢
    intro h; exact hi (by rw [smul_comm, h, smul_zero, neg_zero])
  symm
  rw [show (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
            (W.smul u (ℓ + m - i) (W.smul v (n + i) x)
              - negOnePow ℓ • W.smul v (ℓ + n - i) (W.smul u (m + i) x)))
        = ∑ᶠ i : ℤ, ((negOnePow i * cbz ℓ i) • W.smul u (ℓ + m - i) (W.smul v (n + i) x)
            + -((negOnePow i * cbz ℓ i) • (negOnePow ℓ • W.smul v (ℓ + n - i) (W.smul u (m + i) x))))
      from finsum_congr fun i => by rw [smul_sub, sub_eq_add_neg],
    finsum_add_distrib (Puv_fin W u v x ℓ m n) hfQn, finsum_neg_distrib,
    show (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • (negOnePow ℓ • W.smul v (ℓ + n - i) (W.smul u (m + i) x)))
        = negOnePow ℓ • Pvu W u v x ℓ m n from by
        rw [Pvu, smul_finsum' (negOnePow ℓ) (Pvu_fin W u v x ℓ m n)]
        exact finsum_congr fun i => by rw [smul_comm],
    BL, Puv, ← sub_eq_add_neg]

/-- **Borcherds base case (`m=0`)**: `BL = BR` at `m=0`, via `mode_iterate` (5.1.7d). -/
theorem borcherds_base (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ n : ℤ) :
    BL W u v x ℓ 0 n = BR W u v x ℓ 0 n := by
  rw [BR_zero, BL_as_finsum, mode_iterate W u v ℓ n x,
    finsum_nat_to_int _
      (fun p : ℤ => (negOnePow p * cbz ℓ p) •
        (W.smul u (ℓ - p) (W.smul v (n + p) x)
          - negOnePow ℓ • W.smul v (ℓ + n - p) (W.smul u p x)))
      (fun p hp => by simp only [cbz_apply_neg ℓ hp, mul_zero, zero_smul])
      (fun j => by
        simp only [negOnePow_eq_zpow, cbz_apply_nonneg ℓ (Int.natCast_nonneg j),
          Int.toNat_natCast, zpow_natCast])]
  exact finsum_congr fun i => by
    rw [show ℓ + (0:ℤ) - i = ℓ - i from by ring, show (0:ℤ) + i = i from by ring]

/-! ## Boundary case (`ℓ=0`, via `mode_commutator`).
We re-derive the commutator value AND the vanishing `u₍ₖ₎v=0 for k≥N` from ONE `bracket_deltaSum`,
so the two share the same bound `N`. -/

theorem commBound (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (m n : ℤ) :
    ∃ N : ℕ, (∀ k : ℕ, N ≤ k → W.smul u k v = 0)
      ∧ ⁅mode (W.Y u) m, mode (W.Y v) n⁆
        = ∑ j : Fin N, gBinom m (j : ℕ) • mode (W.Y (W.smul u (j : ℕ) v)) (m + n - (j : ℕ)) := by
  obtain ⟨N, c, hdecomp⟩ := bracket_deltaSum W.toPreVertexAlgebra u v
  refine ⟨N, ?_, ?_⟩
  · intro k hk
    have h1 : W.Y (W.smul u k v) = cCoeff k (bracketDist (W.Y u) (W.Y v)) := (nth_product W u v k).symm
    rw [hdecomp, cCoeff_sum, Finset.sum_eq_zero (fun j _ => by
        rw [cCoeff_deltaDeriv, if_neg (by have h := j.2; omega)])] at h1
    have h2 : W.smul u k v = mode (W.Y (W.smul u k v)) (-1) W.vacuum := by
      rw [← PreVertexAlgebra.smul_def]
      exact (PreVertexAlgebra.smul_vacuum_neg_one W.toPreVertexAlgebra (W.smul u k v)).symm
    rw [h2, h1, mode_apply]; rfl
  · rw [mode_bracket_ope W.toPreVertexAlgebra u v hdecomp m n]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hne : ((j : ℕ).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hcj : c j = (((j : ℕ).factorial : ℂ)⁻¹) • W.Y (W.smul u (j : ℕ) v) := by
      have hrec := cCoeff_deltaSum c j
      rw [← hdecomp, nth_product] at hrec
      rw [hrec, ← Int.cast_smul_eq_zsmul ℂ ((j : ℕ).factorial : ℤ), Int.cast_natCast, smul_smul,
        inv_mul_cancel₀ hne, one_smul]
    rw [hcj, mode_smul,
      ← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range (j : ℕ), (m - (i : ℤ))), smul_smul]
    congr 1
    rw [gBinom, div_eq_mul_inv]
    congr 1
    push_cast
    rfl

/-- **Borcherds boundary case (`ℓ=0`)**: `BL = BR` at `ℓ=0`, i.e. the commutator formula 5.1.7c. -/
theorem borcherds_boundary (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (m n : ℤ) :
    BL W u v x 0 m n = BR W u v x 0 m n := by
  obtain ⟨N, hzero, hcomm⟩ := commBound W u v m n
  have e0 : negOnePow (0 : ℤ) = 1 := by rw [negOnePow_eq_zpow]; norm_num
  have hBL : BL W u v x 0 m n = ⁅mode (W.Y u) m, mode (W.Y v) n⁆ x := by
    rw [BL, Puv, Pvu,
      finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul]),
      finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])]
    simp only [e0, cbz_zero_left, if_pos, mul_one, one_mul, one_smul, add_zero, zero_add, sub_zero]
    rw [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
    rfl
  have hcommx : ⁅mode (W.Y u) m, mode (W.Y v) n⁆ x
      = ∑ j : Fin N, gBinom m (j : ℕ) • W.smul (W.smul u (j : ℕ) v) (m + n - (j : ℕ)) x := by
    rw [hcomm, LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => by rw [LinearMap.smul_apply, ← PreVertexAlgebra.smul_def])
  have hBR : BR W u v x 0 m n
      = ∑ j : Fin N, gBinom m (j : ℕ) • W.smul (W.smul u (j : ℕ) v) (m + n - (j : ℕ)) x := by
    rw [BR, show (∑ᶠ i : ℤ, cbz m i • W.smul (W.smul u (0 + i) v) (m + n - i) x)
          = ∑ᶠ i : ℤ, cbz m i • W.smul (W.smul u i v) (m + n - i) x
        from finsum_congr fun i => by rw [zero_add],
      show (∑ᶠ i : ℤ, cbz m i • W.smul (W.smul u i v) (m + n - i) x)
          = ∑ᶠ j : ℕ, cbz m (j : ℤ) • W.smul (W.smul u (j : ℤ) v) (m + n - (j : ℤ)) x
        from (finsum_nat_to_int _ _
          (fun p hp => by simp only [cbz_apply_neg m hp, zero_smul]) (fun j => rfl)).symm,
      finsum_eq_finsetSum_of_support_subset _ (s := Finset.range N) (by
        intro i hi
        rw [Function.mem_support] at hi
        by_contra hc
        rw [Finset.coe_range, Set.mem_Iio, not_lt] at hc
        exact hi (by rw [hzero i hc, W.smul_zero_left, smul_zero])),
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun j _ => by
      rw [cbz_apply_nonneg m (Int.natCast_nonneg _), Int.toNat_natCast])
  rw [hBL, hcommx, hBR]

/-- **Borcherds identity 5.1.7b** (arbitrary `ℓ, m, n`), applied to `x`.
The two bases are `mode_iterate` (`m=0`) and `mode_commutator` (`ℓ=0`); the `m<0` step is pinned to
the `ℓ=0` boundary by `antidiag_pin`. -/
theorem borcherds (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    BL W u v x ℓ m n = BR W u v x ℓ m n := by
  induction m using Int.induction_on generalizing ℓ n with
  | zero => exact borcherds_base W u v x ℓ n
  | succ k ih => rw [BL_rec, BR_rec, ih ℓ (n + 1), ih (ℓ + 1) n]
  | pred k ih =>
      have key := antidiag_pin
        (fun ℓ' n' => BL W u v x ℓ' (-(k : ℤ) - 1) n' - BR W u v x ℓ' (-(k : ℤ) - 1) n')
        (fun ℓ' n' => by
          dsimp only
          have hbl := BL_rec W u v x ℓ' (-(k : ℤ) - 1) n'
          have hbr := BR_rec W u v x ℓ' (-(k : ℤ) - 1) n'
          rw [show (-(k : ℤ) - 1) + 1 = -(k : ℤ) from by ring] at hbl hbr
          have hih := ih ℓ' n'
          rw [hbl, hbr] at hih
          rw [neg_sub, sub_eq_sub_iff_add_eq_add]
          exact hih.trans (add_comm _ _))
        (fun n' => by dsimp only; rw [borcherds_boundary W u v x (-(k : ℤ) - 1) n', sub_self])
        ℓ n
      exact sub_eq_zero.mp key

/-- **The Jacobi / Borcherds master identity 5.1.7b**, in fully explicit mode form — the
`z₀^ℓ z₁^m z₂^n` coefficient of the δ-function Jacobi identity 5.1.7a, applied to `x`, for ALL
integers `ℓ, m, n`:
`∑ᶠ i, (-1)ⁱ C(ℓ,i)·(u₍ℓ₊ₘ₋ᵢ₎(v₍ₙ₊ᵢ₎x) − (-1)^ℓ·v₍ℓ₊ₙ₋ᵢ₎(u₍ₘ₊ᵢ₎x)) = ∑ᶠ i, C(m,i)·(u₍ℓ₊ᵢ₎v)₍ₘ₊ₙ₋ᵢ₎x`.
This is `borcherds` with `BL`/`BR` unfolded (`cbz = C`, `negOnePow = (-1)^·`).  Its `ℓ=0` slice is
`jacobi_commutator` (5.1.7c) and its `m=0` slice is `mode_iterate` (5.1.7d), so it is the single
master identity that packages the whole 5.1.7 cluster — the mode content of "VA4 ⇔ Jacobi". -/
theorem jacobi (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (ℓ m n : ℤ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (W.smul u (ℓ + m - i) (W.smul v (n + i) x)
          - negOnePow ℓ • W.smul v (ℓ + n - i) (W.smul u (m + i) x)))
      = ∑ᶠ i : ℤ, cbz m i • W.smul (W.smul u (ℓ + i) v) (m + n - i) x := by
  have h := borcherds W u v x ℓ m n
  rwa [BL_as_finsum, BR] at h

end VertexOperatorAlgebra
end VOA
