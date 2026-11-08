import VOA.Moonshine.MoonshineCNNearOppositeComul

/-! The opposite-pair side of the opposite Borcherds identity. Both opposite modes are
expanded with arbitrary nilpotence exponents for `L₁`, and each pair of tower terms is
rewritten by the near-VOA Jacobi identity. No homogeneity is used in this file: the
weights `p q` only enter as the parameters of the opposite modes. -/

noncomputable section
namespace VOA.NearVOA

open Module (End)
open scoped BigOperators

variable {H : Type*} [AddCommGroup H] [Module ℂ H] (V : NearVOA H)

/-- Exchange a finsum with two finite sums, given termwise finite support. -/
theorem finsum_sum_sum_comm {M ι : Type*} [AddCommMonoid M] (s t : Finset ℕ)
    (f : ℕ → ℕ → ι → M) (hf : ∀ b a, (Function.support (f b a)).Finite) :
    ∑ᶠ i, ∑ b ∈ s, ∑ a ∈ t, f b a i = ∑ b ∈ s, ∑ a ∈ t, ∑ᶠ i, f b a i := by
  rw [finsum_sum_comm s (fun i b => ∑ a ∈ t, f b a i)
    (fun b _ => hasFiniteSupport_finsetSum t (fun a i => f b a i) (fun a _ => hf b a))]
  exact Finset.sum_congr rfl
    (fun b _ => finsum_sum_comm t (fun i a => f b a i) (fun a _ => hf b a))

/-- An opposite mode applied to a vector, as a finite tower with any nilpotence cutoff. -/
theorem oppositeModeAtWeight_apply_eq_sum (N n : ℤ) {u : H} {k : ℕ}
    (hk : (V.L 1 ^ k) u = 0) (y : H) :
    V.oppositeModeAtWeight N n u y = (-1 : ℂ) ^ N •
      ∑ j ∈ Finset.range k, ((j.factorial : ℂ)⁻¹) •
        V.smul ((V.L 1 ^ j) u) (2 * N - n - 2 - (j : ℤ)) y := by
  rw [V.oppositeModeAtWeight_eq_sum N n k hk, LinearMap.smul_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  rfl

/-- Two nested opposite modes as a finite double tower of ordinary modes. -/
theorem oppositeModeAtWeight_comp_eq_sum {p q : ℤ} {u v : H} {A₀ B₀ : ℕ}
    (hA : (V.L 1 ^ A₀) u = 0) (hB : (V.L 1 ^ B₀) v = 0) (k₁ k₂ : ℤ) (y : H) :
    V.oppositeModeAtWeight q k₂ v (V.oppositeModeAtWeight p k₁ u y) =
      (-1 : ℂ) ^ (p + q) • ∑ b ∈ Finset.range B₀, ∑ a ∈ Finset.range A₀,
        (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) •
          V.smul ((V.L 1 ^ b) v) (2 * q - k₂ - 2 - (b : ℤ))
            (V.smul ((V.L 1 ^ a) u) (2 * p - k₁ - 2 - (a : ℤ)) y) := by
  rw [V.oppositeModeAtWeight_apply_eq_sum p k₁ hA, V.oppositeModeAtWeight_apply_eq_sum q k₂ hB]
  simp only [smul_def, map_smul, map_sum, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
  congr 1
  rw [show (-1 : ℂ) ^ (p + q) = (-1 : ℂ) ^ q * (-1 : ℂ) ^ p from by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), add_comm q p]]
  ring

/-- The Jacobi identity for one pair of tower terms, written in opposite-mode indices. -/
theorem oppositePair_jacobi_term (u v y : H) (ℓ m n p q : ℤ) (a b : ℕ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (V.smul ((V.L 1 ^ b) v) (2 * q - (n + i) - 2 - (b : ℤ))
            (V.smul ((V.L 1 ^ a) u) (2 * p - (ℓ + m - i) - 2 - (a : ℤ)) y)
          - negOnePow ℓ • V.smul ((V.L 1 ^ a) u) (2 * p - (m + i) - 2 - (a : ℤ))
              (V.smul ((V.L 1 ^ b) v) (2 * q - (ℓ + n - i) - 2 - (b : ℤ)) y)))
      = ∑ᶠ i : ℤ, cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i •
          V.smul (V.smul ((V.L 1 ^ b) v) (ℓ + i) ((V.L 1 ^ a) u))
            ((2 * q - ℓ - n - 2 - (b : ℤ)) + (2 * p - ℓ - m - 2 - (a : ℤ)) - i) y := by
  rw [← V.jacobi ((V.L 1 ^ b) v) ((V.L 1 ^ a) u) y ℓ
    (2 * q - ℓ - n - 2 - (b : ℤ)) (2 * p - ℓ - m - 2 - (a : ℤ))]
  refine finsum_congr (fun i => ?_)
  rw [one_mul,
    show 2 * q - (n + i) - 2 - (b : ℤ) = ℓ + (2 * q - ℓ - n - 2 - (b : ℤ)) - i from by ring,
    show 2 * p - (ℓ + m - i) - 2 - (a : ℤ) = (2 * p - ℓ - m - 2 - (a : ℤ)) + i from by ring,
    show 2 * p - (m + i) - 2 - (a : ℤ) = ℓ + (2 * p - ℓ - m - 2 - (a : ℤ)) - i from by ring,
    show 2 * q - (ℓ + n - i) - 2 - (b : ℤ) = (2 * q - ℓ - n - 2 - (b : ℤ)) + i from by ring]

/-- Each pair of tower terms has finite support in the summation index. -/
theorem oppositePair_term_finite (u v y : H) (ℓ m n p q : ℤ) (a b : ℕ) :
    (Function.support (fun i : ℤ => (negOnePow i * cbz ℓ i) •
        (V.smul ((V.L 1 ^ b) v) (2 * q - (n + i) - 2 - (b : ℤ))
            (V.smul ((V.L 1 ^ a) u) (2 * p - (ℓ + m - i) - 2 - (a : ℤ)) y)
          - negOnePow ℓ • V.smul ((V.L 1 ^ a) u) (2 * p - (m + i) - 2 - (a : ℤ))
              (V.smul ((V.L 1 ^ b) v) (2 * q - (ℓ + n - i) - 2 - (b : ℤ)) y)))).Finite := by
  obtain ⟨Ku, hKu⟩ := V.regularity ((V.L 1 ^ a) u) y
  obtain ⟨Kv, hKv⟩ := V.regularity ((V.L 1 ^ b) v) y
  apply Set.Finite.subset (Set.finite_Icc 0
    (max (Ku - (2 * p - (ℓ + m) - 2 - (a : ℤ))) (Kv - (2 * q - (ℓ + n) - 2 - (b : ℤ)))))
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · have h1 : V.smul ((V.L 1 ^ a) u) (2 * p - (ℓ + m - i) - 2 - (a : ℤ)) y = 0 :=
      hKu _ (by omega)
    have h2 : V.smul ((V.L 1 ^ b) v) (2 * q - (ℓ + n - i) - 2 - (b : ℤ)) y = 0 :=
      hKv _ (by omega)
    rw [h1, h2, V.smul_zero_right, V.smul_zero_right, smul_zero, sub_zero, smul_zero]

/-- **Opposite-pair side.** The opposite-mode Borcherds sum equals the block sum of
ordinary iterates `(L₁ᵇ v)₍ℓ₊ᵢ₎ (L₁ᵃ u)`, for any nilpotence exponents of `u` and `v`. -/
theorem oppositePair_borcherds_eq_blocks {p q : ℤ} {u v : H} {A₀ B₀ : ℕ}
    (hA : (V.L 1 ^ A₀) u = 0) (hB : (V.L 1 ^ B₀) v = 0) (ℓ m n : ℤ) (y : H) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (V.oppositeModeAtWeight q (n + i) v (V.oppositeModeAtWeight p (ℓ + m - i) u y)
          - negOnePow ℓ • V.oppositeModeAtWeight p (m + i) u
              (V.oppositeModeAtWeight q (ℓ + n - i) v y)))
      = (-1 : ℂ) ^ (p + q) • ∑ b ∈ Finset.range B₀, ∑ a ∈ Finset.range A₀,
          (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) •
            ∑ᶠ i : ℤ, cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i •
              V.smul (V.smul ((V.L 1 ^ b) v) (ℓ + i) ((V.L 1 ^ a) u))
                ((2 * q - ℓ - n - 2 - (b : ℤ)) + (2 * p - ℓ - m - 2 - (a : ℤ)) - i) y := by
  set T : ℕ → ℕ → ℤ → H := fun b a i => (negOnePow i * cbz ℓ i) •
    (V.smul ((V.L 1 ^ b) v) (2 * q - (n + i) - 2 - (b : ℤ))
        (V.smul ((V.L 1 ^ a) u) (2 * p - (ℓ + m - i) - 2 - (a : ℤ)) y)
      - negOnePow ℓ • V.smul ((V.L 1 ^ a) u) (2 * p - (m + i) - 2 - (a : ℤ))
          (V.smul ((V.L 1 ^ b) v) (2 * q - (ℓ + n - i) - 2 - (b : ℤ)) y)) with hT
  have hsummand : ∀ i : ℤ, (negOnePow i * cbz ℓ i) •
      (V.oppositeModeAtWeight q (n + i) v (V.oppositeModeAtWeight p (ℓ + m - i) u y)
        - negOnePow ℓ • V.oppositeModeAtWeight p (m + i) u
            (V.oppositeModeAtWeight q (ℓ + n - i) v y))
      = (-1 : ℂ) ^ (p + q) • ∑ b ∈ Finset.range B₀, ∑ a ∈ Finset.range A₀,
          (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) • T b a i := by
    intro i
    rw [V.oppositeModeAtWeight_comp_eq_sum hA hB (ℓ + m - i) (n + i) y,
      V.oppositeModeAtWeight_comp_eq_sum hB hA (ℓ + n - i) (m + i) y,
      Finset.sum_comm (s := Finset.range A₀), add_comm q p]
    simp only [hT, smul_sub, Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
    module
  have hfin : ∀ b a, (Function.support (fun i : ℤ =>
      (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) • T b a i)).Finite := by
    intro b a
    refine (V.oppositePair_term_finite u v y ℓ m n p q a b).subset (fun i hi => ?_)
    rw [Function.mem_support] at hi ⊢
    intro h
    exact hi (by simp only [hT] at h ⊢; rw [h, smul_zero])
  rw [finsum_congr hsummand, ← smul_finsum,
    finsum_sum_sum_comm _ _ (fun b a i => (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) •
      T b a i) hfin]
  congr 1
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
  rw [← smul_finsum]
  congr 1
  exact V.oppositePair_jacobi_term u v y ℓ m n p q a b

end VOA.NearVOA
