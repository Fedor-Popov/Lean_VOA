import VOA.Moonshine.MoonshineCNNearOppositeLeft

/-! The product side of the opposite Borcherds identity. The opposite mode of a product
`u₍ℓ₊ᵢ₎ v` is expanded by the `L₁ᵗ`-comultiplication of the product; the triangle of
tower indices is moved into the box `A < A₀, B < B₀` given by arbitrary nilpotence
exponents of `u` and `v`, and every remaining mode index is controlled by the
near-VOA truncation of the actual product. Both this side and the opposite-pair side
are reduced to one antidiagonal tower, whose coefficients agree by Vandermonde. -/

noncomputable section
namespace VOA.NearVOA

open Module (End)
open scoped BigOperators

variable {H : Type*} [AddCommGroup H] [Module ℂ H] (V : NearVOA H)

/-- A mode of `L₁ᵗ (u₍ₛ₎ v)`, reindexed by the powers `A` of `L₁` on `u` and `B` on `v`. -/
theorem smul_virasoroOne_pow_smul_eq_sum {p : ℤ} {u : H} (hu : u ∈ V.grading p)
    (v : H) (s : ℤ) (t : ℕ) (kk : ℤ) (y : H) :
    V.smul ((V.L 1 ^ t) (V.smul u s v)) kk y
      = ∑ B ∈ Finset.range (t + 1), ∑ A ∈ Finset.range (t - B + 1),
          ((t.factorial : ℂ) * ((A.factorial : ℂ)⁻¹) * ((B.factorial : ℂ)⁻¹)
            * gBinom (2 * p - s - 2 - (A : ℤ)) (t - A - B)) •
            V.smul (V.smul ((V.L 1 ^ A) u) (s + ((t - A - B : ℕ) : ℤ)) ((V.L 1 ^ B) v)) kk y := by
  change V.smulLeftLinear kk y _ = _
  rw [V.virasoroOne_pow_smul_eq_sum hu v s t]
  rw [show (∑ B' ∈ Finset.range (t + 1), ∑ A ∈ Finset.range (B' + 1),
            ((t.choose B' : ℂ) * K p s B' A) •
              V.smul ((V.L 1 ^ A) u) (s + ((B' - A : ℕ) : ℤ)) ((V.L 1 ^ (t - B')) v))
          = ∑ B ∈ Finset.range (t + 1), ∑ A ∈ Finset.range ((t - B) + 1),
            ((t.choose (t - B) : ℂ) * K p s (t - B) A) •
              V.smul ((V.L 1 ^ A) u) (s + (((t - B) - A : ℕ) : ℤ)) ((V.L 1 ^ B) v) from by
        rw [← Finset.sum_range_reflect
              (fun B => ∑ A ∈ Finset.range ((t - B) + 1),
                ((t.choose (t - B) : ℂ) * K p s (t - B) A) •
                  V.smul ((V.L 1 ^ A) u) (s + (((t - B) - A : ℕ) : ℤ)) ((V.L 1 ^ B) v)) (t + 1)]
        refine Finset.sum_congr rfl (fun B' hB' => ?_)
        rw [Finset.mem_range] at hB'
        rw [show (t + 1 - 1 - B') = t - B' from by omega,
            show (t - (t - B')) = B' from by omega]]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun B hB => ?_)
  rw [Finset.mem_range] at hB
  rw [map_sum]
  refine Finset.sum_congr rfl (fun A hA => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hA
  rw [map_smul, smulLeftLinear_apply, show ((t - B) - A : ℕ) = (t - A - B : ℕ) from by omega]
  congr 1
  have hcomb : ((t.choose (t - B) : ℂ))
      = ((t.factorial : ℂ)) * (((t - B).factorial : ℂ)⁻¹) * ((B.factorial : ℂ)⁻¹) := by
    have h2 := Nat.choose_mul_factorial_mul_factorial (show t - B ≤ t from by omega)
    rw [show t - (t - B) = B from by omega] at h2
    have h2' : ((t.choose (t - B) : ℂ)) * ((((t - B).factorial : ℂ)) * (B.factorial : ℂ))
        = (t.factorial : ℂ) := by push_cast [← h2]; ring
    have htBf : (((t - B).factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (t - B)
    have hBf : ((B.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero B
    field_simp
    linear_combination h2'
  rw [hcomb]
  have hKc := K_closed p s (t - B) A (by omega)
  have hAfac : ((A.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero A
  have htBfac : (((t - B).factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (t - B)
  rw [show ((t - B) - A : ℕ) = (t - A - B : ℕ) from by omega] at hKc
  have hKval : K p s (t - B) A
      = (((t - B).factorial : ℂ)) * ((A.factorial : ℂ)⁻¹)
          * gBinom (2 * p - s - 2 - (A : ℤ)) (t - A - B) := by
    field_simp at hKc ⊢
    linear_combination hKc
  rw [hKval]
  have hBf : ((B.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero B
  have htf : ((t.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  field_simp

/-- The triangle `A + B ≤ t` of a summand vanishing outside the box `A < P, B < Q`
equals the box sum with an indicator. -/
theorem triangle_sum_eq_box {M : Type*} [AddCommMonoid M] {G : ℕ → ℕ → M} (P Q t : ℕ)
    (hG : ∀ A B, (P ≤ A ∨ Q ≤ B) → G A B = 0) :
    (∑ B ∈ Finset.range (t + 1), ∑ A ∈ Finset.range (t - B + 1), G A B)
      = ∑ B ∈ Finset.range Q, ∑ A ∈ Finset.range P,
          (if A + B ≤ t then G A B else 0) := by
  classical
  set R : ℕ := t + Q + P + 1 with hR
  set F : ℕ → ℕ → M := fun B A => if A + B ≤ t ∧ A < P ∧ B < Q then G A B else 0 with hF
  have hrow : ∀ B : ℕ, (∑ A ∈ Finset.range R, F B A)
      = if B ≤ t then (∑ A ∈ Finset.range (t - B + 1), G A B) else 0 := by
    intro B
    by_cases hBt : B ≤ t
    · rw [if_pos hBt, ← Finset.sum_subset
        (Finset.range_subset_range.mpr (by omega : t - B + 1 ≤ R))
        (fun A _ hA => by rw [Finset.mem_range] at hA; simp only [hF]; rw [if_neg (by omega)])]
      refine Finset.sum_congr rfl (fun A hA => ?_)
      rw [Finset.mem_range] at hA; simp only [hF]
      rcases Nat.lt_or_ge A P with hAP | hAP
      · rcases Nat.lt_or_ge B Q with hBQ | hBQ
        · rw [if_pos ⟨by omega, hAP, hBQ⟩]
        · rw [if_neg (by omega), hG A B (Or.inr hBQ)]
      · rw [if_neg (by omega), hG A B (Or.inl hAP)]
    · rw [if_neg hBt]
      refine Finset.sum_eq_zero (fun A _ => ?_)
      simp only [hF]; rw [if_neg (by omega)]
  have hrow2 : ∀ B : ℕ, (∑ A ∈ Finset.range R, F B A)
      = if B < Q then (∑ A ∈ Finset.range P, (if A + B ≤ t then G A B else 0)) else 0 := by
    intro B
    by_cases hBQ : B < Q
    · rw [if_pos hBQ, ← Finset.sum_subset
        (Finset.range_subset_range.mpr (by omega : P ≤ R))
        (fun A _ hA => by rw [Finset.mem_range] at hA; simp only [hF]; rw [if_neg (by omega)])]
      refine Finset.sum_congr rfl (fun A hA => ?_)
      rw [Finset.mem_range] at hA; simp only [hF]
      by_cases hc : A + B ≤ t
      · rw [if_pos hc, if_pos ⟨hc, hA, hBQ⟩]
      · rw [if_neg hc, if_neg (by omega)]
    · rw [if_neg hBQ]
      refine Finset.sum_eq_zero (fun A _ => ?_)
      simp only [hF]; rw [if_neg (by omega)]
  have hLHS : (∑ B ∈ Finset.range (t + 1), ∑ A ∈ Finset.range (t - B + 1), G A B)
      = ∑ B ∈ Finset.range R, ∑ A ∈ Finset.range R, F B A := by
    rw [Finset.sum_congr rfl (fun B _ => hrow B), ← Finset.sum_subset
      (Finset.range_subset_range.mpr (by omega : t + 1 ≤ R))
      (fun B _ hB => by simp only [Finset.mem_range, not_lt] at hB; rw [if_neg (by omega)])]
    refine Finset.sum_congr rfl (fun B hB => ?_)
    rw [Finset.mem_range] at hB; rw [if_pos (by omega)]
  have hRHS : (∑ B ∈ Finset.range Q, ∑ A ∈ Finset.range P,
          (if A + B ≤ t then G A B else 0))
      = ∑ B ∈ Finset.range R, ∑ A ∈ Finset.range R, F B A := by
    rw [Finset.sum_congr rfl (fun B _ => hrow2 B), ← Finset.sum_subset
      (Finset.range_subset_range.mpr (by omega : Q ≤ R))
      (fun B _ hB => by simp only [Finset.mem_range, not_lt] at hB; rw [if_neg (by omega)])]
    refine Finset.sum_congr rfl (fun B hB => ?_)
    rw [Finset.mem_range] at hB; rw [if_pos hB]
  rw [hLHS, hRHS]

/-- Shift a finsum over `ℕ` whose terms vanish below `c`. -/
theorem finsum_nat_shift {M : Type*} [AddCommMonoid M] (c : ℕ) (F : ℕ → M)
    (hF : ∀ t : ℕ, t < c → F t = 0) :
    (∑ᶠ t : ℕ, F t) = ∑ᶠ j : ℕ, F (c + j) := by
  have hsub : Function.support F ⊆ Set.range (fun j : ℕ => c + j) := by
    intro t ht
    rw [Function.mem_support] at ht
    have htc : c ≤ t := by by_contra hlt; exact ht (hF t (by omega))
    exact ⟨t - c, by change c + (t - c) = t; omega⟩
  have hinj : Function.Injective (fun j : ℕ => c + j) := add_right_injective c
  rw [← finsum_mem_range hinj (f := F),
    ← finsum_mem_inter_support F (Set.range (fun j : ℕ => c + j)),
    ← finsum_mem_univ (f := F), ← finsum_mem_inter_support F Set.univ, Set.univ_inter,
    Set.inter_eq_right.mpr hsub]

/-- The common tower vector `((L₁ᴬ u)₍ℓ₊ᵣ₎ (L₁ᴮ v))₍D−A−B−r₎ y`, `D = 2p+2q−2ℓ−m−n−4`. -/
def oppositeTowerVector (u v y : H) (p q ℓ m n : ℤ) (A B : ℕ) (r : ℤ) : H :=
  V.smul (V.smul ((V.L 1 ^ A) u) (ℓ + r) ((V.L 1 ^ B) v))
    ((2 * p + 2 * q - 2 * ℓ - m - n - 4) - (A : ℤ) - (B : ℤ) - r) y

/-- The common coefficient `(−1)^{ℓ+1} C(2p−ℓ−m−2−A, r)`, zero for `r < 0`. -/
def oppositeTowerCoeff (p ℓ m : ℤ) (A : ℕ) (r : ℤ) : ℂ :=
  if 0 ≤ r then (-1 : ℂ) ^ (ℓ + 1) * gBinom (2 * p - ℓ - m - 2 - (A : ℤ)) r.toNat else 0

/-- The product-side coefficient before the antidiagonal collapse. -/
def oppositeProductCoeff (p q ℓ m : ℤ) (A B : ℕ) (i : ℤ) (j : ℕ) : ℂ :=
  cbz m i * (-1 : ℂ) ^ (p + q - (ℓ + i) - 1) * (((A.factorial : ℂ)⁻¹) * ((B.factorial : ℂ)⁻¹))
    * gBinom (2 * p - (ℓ + i) - 2 - (A : ℤ)) j

/-- Vandermonde collapse for the skew-transported pair blocks. -/
theorem oppositePairCoeff_collapse (p q ℓ m n : ℤ) (A B : ℕ) (r : ℕ) :
    (∑ᶠ j : ℕ, cbz (2 * q - ℓ - n - 2 - (B : ℤ)) (r - (j : ℤ)) * (-(-1 : ℂ) ^ (ℓ + (r - (j : ℤ))))
        * gBinom ((2 * p + 2 * q - 2 * ℓ - m - n - 4 - (A : ℤ) - (B : ℤ)) - (r - (j : ℤ))) j)
      = oppositeTowerCoeff p ℓ m A (r : ℤ) := by
  have hcongr : ∀ j : ℕ,
      cbz (2 * q - ℓ - n - 2 - (B : ℤ)) ((r : ℤ) - (j : ℤ))
        * (-(-1 : ℂ) ^ (ℓ + ((r : ℤ) - (j : ℤ))))
        * gBinom ((2 * p + 2 * q - 2 * ℓ - m - n - 4 - (A : ℤ) - (B : ℤ)) - ((r : ℤ) - (j : ℤ))) j
      = (-(-1 : ℂ) ^ (ℓ + (r : ℤ))) *
          ((-1 : ℂ) ^ j * cbz (2 * q - ℓ - n - 2 - (B : ℤ)) ((r : ℤ) - (j : ℤ))
            * gBinom ((2 * p + 2 * q - 2 * ℓ - m - n - 4 - (A : ℤ) - (B : ℤ))
                - ((r : ℤ) - (j : ℤ))) j) := by
    intro j
    rw [show (ℓ + ((r : ℤ) - (j : ℤ))) = (ℓ + (r : ℤ)) - (j : ℤ) from by ring,
      signSplit (ℓ + (r : ℤ)) j]
    ring
  rw [finsum_congr hcongr, ← mul_finsum,
    vand_finsum (2 * q - ℓ - n - 2 - (B : ℤ))
      (2 * p + 2 * q - 2 * ℓ - m - n - 4 - (A : ℤ) - (B : ℤ)) r,
    oppositeTowerCoeff, if_pos (by positivity), Int.toNat_natCast,
    show (2 * p + 2 * q - 2 * ℓ - m - n - 4 - (A : ℤ) - (B : ℤ)) - (2 * q - ℓ - n - 2 - (B : ℤ))
        = 2 * p - ℓ - m - 2 - (A : ℤ) from by ring,
    ← negOne_zpow_natCast r,
    show (-(-1 : ℂ) ^ (ℓ + (r : ℤ))) * ((-1 : ℂ) ^ (r : ℤ) * gBinom (2 * p - ℓ - m - 2 - (A : ℤ)) r)
      = (-((-1 : ℂ) ^ (ℓ + (r : ℤ)) * (-1 : ℂ) ^ (r : ℤ)))
          * gBinom (2 * p - ℓ - m - 2 - (A : ℤ)) r from by ring]
  congr 1
  rw [← negOne_zpow_add, negOne_neg_zpow]
  exact negOne_zpow_eq _ _ ⟨(r : ℤ), by ring⟩

/-- Vandermonde collapse for the comultiplied product side. -/
theorem oppositeProductCoeff_collapse (p q ℓ m : ℤ) (A : ℕ) (r : ℕ) :
    (∑ᶠ j : ℕ, cbz m (r - (j : ℤ))
        * ((-1 : ℂ) ^ (p + q - (ℓ + (r - (j : ℤ))) - 1)
          * gBinom (2 * p - (ℓ + (r - (j : ℤ))) - 2 - (A : ℤ)) j))
      = (-1 : ℂ) ^ (p + q) * oppositeTowerCoeff p ℓ m A (r : ℤ) := by
  have hcongr : ∀ j : ℕ,
      cbz m ((r : ℤ) - (j : ℤ))
        * ((-1 : ℂ) ^ (p + q - (ℓ + ((r : ℤ) - (j : ℤ))) - 1)
          * gBinom (2 * p - (ℓ + ((r : ℤ) - (j : ℤ))) - 2 - (A : ℤ)) j)
      = (-1 : ℂ) ^ (p + q - ℓ - (r : ℤ) - 1) *
          ((-1 : ℂ) ^ j * cbz m ((r : ℤ) - (j : ℤ))
            * gBinom ((2 * p - ℓ - 2 - (A : ℤ)) - ((r : ℤ) - (j : ℤ))) j) := by
    intro j
    rw [show (p + q - (ℓ + ((r : ℤ) - (j : ℤ))) - 1) = (p + q - ℓ - (r : ℤ) - 1) + (j : ℤ) from by
        ring,
      negOne_zpow_add, negOne_zpow_natCast,
      show (2 * p - (ℓ + ((r : ℤ) - (j : ℤ))) - 2 - (A : ℤ))
        = (2 * p - ℓ - 2 - (A : ℤ)) - ((r : ℤ) - (j : ℤ)) from by ring]
    ring
  rw [finsum_congr hcongr, ← mul_finsum, vand_finsum m (2 * p - ℓ - 2 - (A : ℤ)) r,
    oppositeTowerCoeff, if_pos (by positivity), Int.toNat_natCast,
    show (2 * p - ℓ - 2 - (A : ℤ)) - m = 2 * p - ℓ - m - 2 - (A : ℤ) from by ring,
    ← negOne_zpow_natCast r,
    show ((-1 : ℂ) ^ (p + q - ℓ - (r : ℤ) - 1) * ((-1 : ℂ) ^ (r : ℤ)
        * gBinom (2 * p - ℓ - m - 2 - (A : ℤ)) r))
      = ((-1 : ℂ) ^ (p + q - ℓ - (r : ℤ) - 1) * (-1 : ℂ) ^ (r : ℤ))
          * gBinom (2 * p - ℓ - m - 2 - (A : ℤ)) r from by ring,
    show (-1 : ℂ) ^ (p + q) * ((-1 : ℂ) ^ (ℓ + 1) * gBinom (2 * p - ℓ - m - 2 - (A : ℤ)) r)
      = ((-1 : ℂ) ^ (p + q) * (-1 : ℂ) ^ (ℓ + 1)) * gBinom (2 * p - ℓ - m - 2 - (A : ℤ)) r from by
        ring]
  congr 1
  rw [← negOne_zpow_add, ← negOne_zpow_add]
  exact negOne_zpow_eq _ _ ⟨-ℓ - 1, by ring⟩

/-- The tower vector vanishes once the first mode index passes the truncation bound. -/
theorem oppositeTowerVector_eventually_zero (u v y : H) (p q ℓ m n : ℤ) (A B : ℕ) :
    ∃ Ns : ℤ, ∀ r : ℤ, Ns - ℓ ≤ r → V.oppositeTowerVector u v y p q ℓ m n A B r = 0 := by
  obtain ⟨Ns, hNs⟩ := V.regularity ((V.L 1 ^ A) u) ((V.L 1 ^ B) v)
  refine ⟨Ns, fun r hr => ?_⟩
  rw [oppositeTowerVector, show V.smul ((V.L 1 ^ A) u) (ℓ + r) ((V.L 1 ^ B) v) = 0 from
    hNs (ℓ + r) (by omega), V.smul_zero_left]

/-- One opposite-pair block, skewed to the common tower and collapsed antidiagonally. -/
theorem oppositePairIterate_eq_tower (u v y : H) (p q ℓ m n : ℤ) (a b : ℕ) :
    (∑ᶠ i : ℤ, cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i •
        V.smul (V.smul ((V.L 1 ^ b) v) (ℓ + i) ((V.L 1 ^ a) u))
          ((2 * q - ℓ - n - 2 - (b : ℤ)) + (2 * p - ℓ - m - 2 - (a : ℤ)) - i) y)
      = ∑ᶠ r : ℤ, oppositeTowerCoeff p ℓ m a r • V.oppositeTowerVector u v y p q ℓ m n a b r := by
  set D : ℤ := 2 * p + 2 * q - 2 * ℓ - m - n - 4 with hD
  obtain ⟨Ns, hVzero⟩ := V.oppositeTowerVector_eventually_zero u v y p q ℓ m n a b
  set g : ℤ → ℕ → ℂ := fun i j =>
    cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i * (-(-1 : ℂ) ^ (ℓ + i))
      * gBinom (D - (a : ℤ) - (b : ℤ) - i) j with hg
  have hskew : (∑ᶠ i : ℤ, cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i •
        V.smul (V.smul ((V.L 1 ^ b) v) (ℓ + i) ((V.L 1 ^ a) u))
          ((2 * q - ℓ - n - 2 - (b : ℤ)) + (2 * p - ℓ - m - 2 - (a : ℤ)) - i) y)
      = ∑ᶠ (i : ℤ), ∑ᶠ (j : ℕ), g i j • V.oppositeTowerVector u v y p q ℓ m n a b
          (i + (j : ℤ)) := by
    refine finsum_congr (fun i => ?_)
    rw [show (2 * q - ℓ - n - 2 - (b : ℤ)) + (2 * p - ℓ - m - 2 - (a : ℤ)) - i
          = D - (a : ℤ) - (b : ℤ) - i from by rw [hD]; ring,
      V.smul_smul_skew ((V.L 1 ^ a) u) ((V.L 1 ^ b) v) (ℓ + i) (D - (a : ℤ) - (b : ℤ) - i) y,
      smul_finsum]
    refine finsum_congr (fun j : ℕ => ?_)
    rw [hg, oppositeTowerVector,
      show (ℓ + (i + (j : ℤ))) = (ℓ + i) + (j : ℤ) from by ring,
      show (2 * p + 2 * q - 2 * ℓ - m - n - 4) - (a : ℤ) - (b : ℤ) - (i + (j : ℤ))
        = (D - (a : ℤ) - (b : ℤ) - i) - (j : ℤ) from by rw [hD]; ring,
      smul_smul]
    ring_nf
  rw [hskew]
  obtain ⟨hfin, hfin2, hfinr⟩ := antidiag_fins g
    (fun r => V.oppositeTowerVector u v y p q ℓ m n a b r) (Ns - ℓ)
    (fun i hi j => by rw [hg]; simp only []; rw [cbz_apply_neg _ hi]; ring) hVzero
  rw [antidiag_reindex g (fun r => V.oppositeTowerVector u v y p q ℓ m n a b r) hfin hfin2 hfinr]
  refine finsum_congr (fun r => ?_)
  rcases lt_or_ge r 0 with hr | hr
  · rw [show (∑ᶠ j : ℕ, g (r - (j : ℤ)) j) = (∑ᶠ _j : ℕ, (0 : ℂ)) from
        finsum_congr (fun j => by
          rw [hg]; simp only []
          rw [cbz_apply_neg (2 * q - ℓ - n - 2 - (b : ℤ)) (by omega : r - (j : ℤ) < 0)]; ring)]
    rw [finsum_zero, zero_smul, oppositeTowerCoeff, if_neg (by omega), zero_smul]
  · obtain ⟨rn, rfl⟩ : ∃ rn : ℕ, r = (rn : ℤ) := ⟨r.toNat, (Int.toNat_of_nonneg hr).symm⟩
    congr 1
    rw [← oppositePairCoeff_collapse p q ℓ m n a b rn]

/-- One summand of the product side, expanded into the box of tower vectors. -/
theorem cbz_smul_oppositeModeAtWeight_product_eq {p q : ℤ} {u v : H} (hu : u ∈ V.grading p)
    {A₀ B₀ : ℕ} (hA : (V.L 1 ^ A₀) u = 0) (hB : (V.L 1 ^ B₀) v = 0)
    (hNil : ∀ w : H, ∃ k : ℕ, (V.L 1 ^ k) w = 0) (ℓ m n : ℤ) (y : H) (i : ℤ) :
    cbz m i • V.oppositeModeAtWeight (p + q - (ℓ + i) - 1) (m + n - i) (V.smul u (ℓ + i) v) y
      = ∑ B ∈ Finset.range B₀, ∑ A ∈ Finset.range A₀,
          ∑ᶠ j : ℕ, oppositeProductCoeff p q ℓ m A B i j •
            V.oppositeTowerVector u v y p q ℓ m n A B (i + (j : ℤ)) := by
  set P : ℤ := p + q - (ℓ + i) - 1 with hP
  have hGzero : ∀ (A B : ℕ) (j : ℕ), (A₀ ≤ A ∨ B₀ ≤ B) →
      oppositeProductCoeff p q ℓ m A B i j •
        V.oppositeTowerVector u v y p q ℓ m n A B (i + (j : ℤ)) = 0 := by
    rintro A B j (hA' | hB')
    · rw [oppositeTowerVector, Module.End.pow_map_zero_of_le hA' hA, V.smul_zero_left,
        V.smul_zero_left, smul_zero]
    · rw [oppositeTowerVector, Module.End.pow_map_zero_of_le hB' hB, V.smul_zero_right,
        V.smul_zero_left, smul_zero]
  have hterm : ∀ t : ℕ,
      cbz m i • ((-1 : ℂ) ^ P • (((t.factorial : ℂ)⁻¹) •
        V.smul ((V.L 1 ^ t) (V.smul u (ℓ + i) v)) (2 * P - (m + n - i) - 2 - (t : ℤ)) y))
        = ∑ B ∈ Finset.range B₀, ∑ A ∈ Finset.range A₀,
            (if A + B ≤ t then
              oppositeProductCoeff p q ℓ m A B i (t - A - B) •
                V.oppositeTowerVector u v y p q ℓ m n A B (i + ((t - A - B : ℕ) : ℤ))
             else 0) := by
    intro t
    rw [V.smul_virasoroOne_pow_smul_eq_sum hu v (ℓ + i) t (2 * P - (m + n - i) - 2 - (t : ℤ)) y,
      ← triangle_sum_eq_box A₀ B₀ t (G := fun A B =>
          oppositeProductCoeff p q ℓ m A B i (t - A - B) •
            V.oppositeTowerVector u v y p q ℓ m n A B (i + ((t - A - B : ℕ) : ℤ)))
        (fun A B h => hGzero A B (t - A - B) h),
      smul_smul, smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun B hB' => ?_)
    rw [Finset.mem_range] at hB'
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun A hA' => ?_)
    rw [Finset.mem_range, Nat.lt_succ_iff] at hA'
    have htAB : ((t - A - B : ℕ) : ℤ) = (t : ℤ) - (A : ℤ) - (B : ℤ) := by omega
    rw [smul_smul, oppositeProductCoeff, oppositeTowerVector,
      show (ℓ + i) + ((t - A - B : ℕ) : ℤ) = ℓ + (i + ((t - A - B : ℕ) : ℤ)) from by ring,
      show (2 * P - (m + n - i) - 2 - (t : ℤ))
        = (2 * p + 2 * q - 2 * ℓ - m - n - 4) - (A : ℤ) - (B : ℤ) - (i + ((t - A - B : ℕ) : ℤ))
        from by rw [hP, htAB]; ring]
    congr 1
    have htf : ((t.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
    rw [hP]
    field_simp
  have hfinAB : ∀ B A : ℕ, (Function.support (fun t : ℕ =>
      (if A + B ≤ t then
        oppositeProductCoeff p q ℓ m A B i (t - A - B) •
          V.oppositeTowerVector u v y p q ℓ m n A B (i + ((t - A - B : ℕ) : ℤ))
       else 0))).Finite := by
    intro B A
    obtain ⟨Ns, hNs⟩ := V.oppositeTowerVector_eventually_zero u v y p q ℓ m n A B
    apply Set.Finite.subset (Set.finite_Icc 0 ((Ns - ℓ - i + (A : ℤ) + (B : ℤ)).toNat))
    intro t ht
    rw [Function.mem_support] at ht
    rw [Set.mem_Icc]
    refine ⟨Nat.zero_le _, ?_⟩
    by_contra hge
    apply ht
    by_cases hc : A + B ≤ t
    · have htAB : ((t - A - B : ℕ) : ℤ) = (t : ℤ) - (A : ℤ) - (B : ℤ) := by omega
      rw [if_pos hc, hNs _ (by rw [htAB]; omega), smul_zero]
    · rw [if_neg hc]
  obtain ⟨k, hk⟩ := hNil (V.smul u (ℓ + i) v)
  rw [V.oppositeModeAtWeight_apply_eq_sum P (m + n - i) hk y,
    ← finsum_eq_finsetSum_of_support_subset _ (s := Finset.range k) (by
      intro t ht
      rw [Function.mem_support] at ht
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hge
      exact ht (by rw [Module.End.pow_map_zero_of_le (Nat.le_of_not_gt hge) hk,
        V.smul_zero_left, smul_zero])),
    smul_finsum, smul_finsum, finsum_congr hterm,
    finsum_sum_sum_comm _ _ _ hfinAB]
  refine Finset.sum_congr rfl (fun B _ => Finset.sum_congr rfl (fun A _ => ?_))
  rw [finsum_nat_shift (A + B) _ (fun t htlt => by rw [if_neg (by omega)])]
  refine finsum_congr (fun j => ?_)
  rw [if_pos (by omega), show (A + B + j) - A - B = j from by omega]

/-- **Product side.** The Borcherds sum of opposite modes of products equals the same block
sum of ordinary iterates as the opposite-pair side. -/
theorem oppositeProduct_borcherds_eq_blocks {p q : ℤ} {u v : H} (hu : u ∈ V.grading p)
    {A₀ B₀ : ℕ} (hA : (V.L 1 ^ A₀) u = 0) (hB : (V.L 1 ^ B₀) v = 0)
    (hNil : ∀ w : H, ∃ k : ℕ, (V.L 1 ^ k) w = 0) (ℓ m n : ℤ) (y : H) :
    (∑ᶠ i : ℤ, cbz m i •
        V.oppositeModeAtWeight (p + q - (ℓ + i) - 1) (m + n - i) (V.smul u (ℓ + i) v) y)
      = (-1 : ℂ) ^ (p + q) • ∑ b ∈ Finset.range B₀, ∑ a ∈ Finset.range A₀,
          (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) •
            ∑ᶠ i : ℤ, cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i •
              V.smul (V.smul ((V.L 1 ^ b) v) (ℓ + i) ((V.L 1 ^ a) u))
                ((2 * q - ℓ - n - 2 - (b : ℤ)) + (2 * p - ℓ - m - 2 - (a : ℤ)) - i) y := by
  rw [Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => by
    rw [V.oppositePairIterate_eq_tower u v y p q ℓ m n a b]))]
  simp only [Finset.smul_sum, smul_smul]
  rw [finsum_congr (fun i => V.cbz_smul_oppositeModeAtWeight_product_eq hu hA hB hNil ℓ m n y i)]
  have hifin : ∀ B A : ℕ, (Function.support (fun i : ℤ =>
      ∑ᶠ j : ℕ, oppositeProductCoeff p q ℓ m A B i j •
        V.oppositeTowerVector u v y p q ℓ m n A B (i + (j : ℤ)))).Finite := by
    intro B A
    obtain ⟨Ns, hNs⟩ := V.oppositeTowerVector_eventually_zero u v y p q ℓ m n A B
    apply Set.Finite.subset (Set.finite_Icc 0 (Ns - ℓ))
    intro i hi
    rw [Function.mem_support] at hi; rw [Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
    · refine finsum_eq_zero_of_forall_eq_zero (fun j => ?_)
      simp only [oppositeProductCoeff]; rw [cbz_apply_neg _ h]; simp
    · refine finsum_eq_zero_of_forall_eq_zero (fun j => ?_)
      rw [hNs _ (by omega), smul_zero]
  rw [finsum_sum_sum_comm _ _ _ hifin]
  refine Finset.sum_congr rfl (fun B _ => Finset.sum_congr rfl (fun A _ => ?_))
  obtain ⟨Ns, hNs⟩ := V.oppositeTowerVector_eventually_zero u v y p q ℓ m n A B
  obtain ⟨hfin, hfin2, hfinr⟩ := antidiag_fins (fun i j => oppositeProductCoeff p q ℓ m A B i j)
    (fun r => V.oppositeTowerVector u v y p q ℓ m n A B r) (Ns - ℓ)
    (fun i hi j => by simp only [oppositeProductCoeff]; rw [cbz_apply_neg _ hi]; ring) hNs
  rw [antidiag_reindex (fun i j => oppositeProductCoeff p q ℓ m A B i j)
    (fun r => V.oppositeTowerVector u v y p q ℓ m n A B r) hfin hfin2 hfinr]
  have hffin : (Function.support (fun r : ℤ =>
      oppositeTowerCoeff p ℓ m A r • V.oppositeTowerVector u v y p q ℓ m n A B r)).Finite := by
    apply Set.Finite.subset (Set.finite_Icc 0 (Ns - ℓ))
    intro r hr
    rw [Function.mem_support] at hr; rw [Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hr ?_, not_lt.mp fun h => hr ?_⟩
    · rw [oppositeTowerCoeff, if_neg (by omega), zero_smul]
    · rw [hNs _ (by omega), smul_zero]
  rw [smul_finsum' ((-1 : ℂ) ^ (p + q) * (((A.factorial : ℂ)⁻¹) * ((B.factorial : ℂ)⁻¹))) hffin]
  refine finsum_congr (fun r => ?_)
  rw [smul_smul]
  congr 1
  rcases lt_or_ge r 0 with hr | hr
  · rw [oppositeTowerCoeff, if_neg (by omega), mul_zero]
    refine finsum_eq_zero_of_forall_eq_zero (fun j => ?_)
    rw [oppositeProductCoeff, cbz_apply_neg _ (by omega : r - (j : ℤ) < 0)]; ring
  · obtain ⟨rn, rfl⟩ : ∃ rn : ℕ, r = (rn : ℤ) := ⟨r.toNat, (Int.toNat_of_nonneg hr).symm⟩
    have hpull : (∑ᶠ j : ℕ, oppositeProductCoeff p q ℓ m A B ((rn : ℤ) - (j : ℤ)) j)
        = (((A.factorial : ℂ)⁻¹) * ((B.factorial : ℂ)⁻¹)) *
            (∑ᶠ j : ℕ, cbz m ((rn : ℤ) - (j : ℤ))
              * ((-1 : ℂ) ^ (p + q - (ℓ + ((rn : ℤ) - (j : ℤ))) - 1)
                * gBinom (2 * p - (ℓ + ((rn : ℤ) - (j : ℤ))) - 2 - (A : ℤ)) j)) := by
      rw [mul_finsum]
      refine finsum_congr (fun j => ?_)
      rw [oppositeProductCoeff]; ring
    rw [hpull, oppositeProductCoeff_collapse p q ℓ m A rn]
    ring

end VOA.NearVOA
