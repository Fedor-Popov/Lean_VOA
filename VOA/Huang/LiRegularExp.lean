import VOA.Huang.LiRegularD

/-! # Exponentials of locally nilpotent operators and translation of mode families

For a locally nilpotent `A ∈ End M` (every vector is killed by a power of `A`), the
exponential `e^{cA} = Σⱼ (cʲ/j!) Aʲ` is a well-defined linear map (finite on each vector),
`e^{cA} e^{dA} = e^{(c+d)A}` (`expOp_add`), so `e^{cA}` is invertible.

If a family of operators `Xₙ` (`n ∈ ℤ`) satisfies `[A, Xₙ] = n Xₙ₋₁` and is upper truncated,
then the Leibniz formula `Aᴺ Xₙ = Σₖ C(N,k) n(n−1)⋯(n−k+1) Xₙ₋ₖ Aᴺ⁻ᵏ` (`pow_comm_formula`)
gives the translation formula

  `e^{cA} Xₙ = (Σₖ C(n,k) cᵏ Xₙ₋ₖ) e^{cA}`        (`expOp_conj`).

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiRegular

open VOA
open scoped BigOperators

universe v

variable {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- `A` is locally nilpotent. -/
def LocNil (A : Module.End ℂ M) : Prop := ∀ x : M, ∃ J : ℕ, (A ^ J) x = 0

theorem pow_apply_eq_zero_of_le {A : Module.End ℂ M} {x : M} {J m : ℕ} (hJ : (A ^ J) x = 0)
    (hm : J ≤ m) : (A ^ m) x = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [add_comm, pow_add, Module.End.mul_apply, hJ, map_zero]

/-- The `j`-th term of the exponential series. -/
noncomputable def expTerm (A : Module.End ℂ M) (c : ℂ) (x : M) (j : ℕ) : M :=
  ((c ^ j / (j.factorial : ℂ))) • (A ^ j) x

theorem expTerm_eq_zero {A : Module.End ℂ M} {c : ℂ} {x : M} {J : ℕ} (hJ : (A ^ J) x = 0)
    {j : ℕ} (hj : J ≤ j) : expTerm A c x j = 0 := by
  rw [expTerm, pow_apply_eq_zero_of_le hJ hj, smul_zero]

theorem expTerm_support_subset {A : Module.End ℂ M} {c : ℂ} {x : M} {J : ℕ}
    (hJ : (A ^ J) x = 0) : Function.support (expTerm A c x) ⊆ ↑(Finset.range J) := by
  intro j hj
  rw [Function.mem_support] at hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact hj (expTerm_eq_zero hJ (not_lt.mp h))

theorem expTerm_support_finite {A : Module.End ℂ M} (hA : LocNil A) (c : ℂ) (x : M) :
    (Function.support (expTerm A c x)).Finite := by
  obtain ⟨J, hJ⟩ := hA x
  exact (Finset.range J).finite_toSet.subset (expTerm_support_subset hJ)

/-- The exponential `e^{cA}` of a locally nilpotent operator. -/
noncomputable def expOp {A : Module.End ℂ M} (hA : LocNil A) (c : ℂ) : Module.End ℂ M where
  toFun x := ∑ᶠ j : ℕ, expTerm A c x j
  map_add' x y := by
    rw [← finsum_add_distrib (expTerm_support_finite hA c x) (expTerm_support_finite hA c y)]
    exact finsum_congr fun j => by simp [expTerm, smul_add]
  map_smul' d x := by
    rw [RingHom.id_apply, smul_finsum]
    exact finsum_congr fun j => by simp [expTerm, smul_comm d]

theorem expOp_eq_sum {A : Module.End ℂ M} (hA : LocNil A) (c : ℂ) {x : M} {J : ℕ}
    (hJ : (A ^ J) x = 0) :
    expOp hA c x = ∑ j ∈ Finset.range J, ((c ^ j / (j.factorial : ℂ))) • (A ^ j) x :=
  finsum_eq_sum_of_support_subset _ (expTerm_support_subset hJ)

theorem expOp_zero {A : Module.End ℂ M} (hA : LocNil A) (x : M) : expOp hA 0 x = x := by
  obtain ⟨J, hJ⟩ := hA x
  rcases Nat.eq_zero_or_pos J with rfl | hpos
  · simp only [pow_zero, Module.End.one_apply] at hJ
    subst hJ; exact map_zero _
  rw [expOp_eq_sum hA 0 hJ, Finset.sum_eq_single 0 (fun j _ hj => by simp [zero_pow hj])
    (fun h => absurd (Finset.mem_range.2 hpos) h)]
  simp

/-- Triangle reindexing. -/
theorem tri_reindex {X : Type*} [AddCommMonoid X] (B : ℕ) (g : ℕ → ℕ → X) :
    ∑ N ∈ Finset.range B, ∑ k ∈ Finset.range (N + 1), g k (N - k)
      = ∑ k ∈ Finset.range B, ∑ i ∈ Finset.range (B - k), g k i := by
  rw [Finset.sum_comm' (t' := Finset.range B) (s' := fun k => Finset.Ico k B)
    (fun N k => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_Ico_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by rw [show k + i - k = i by omega]

/-- `e^{cA} e^{dA} = e^{(c+d)A}`. -/
theorem expOp_add {A : Module.End ℂ M} (hA : LocNil A) (c d : ℂ) (x : M) :
    expOp hA c (expOp hA d x) = expOp hA (c + d) x := by
  obtain ⟨J, hJ⟩ := hA x
  have hJ' : (A ^ J) (expOp hA d x) = 0 := by
    rw [expOp_eq_sum hA d hJ, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, ← Module.End.mul_apply, ← pow_add, pow_apply_eq_zero_of_le hJ (by omega),
      smul_zero]
  rw [expOp_eq_sum hA c hJ', expOp_eq_sum hA (c + d) hJ, expOp_eq_sum hA d hJ]
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul, ← Module.End.mul_apply, ← pow_add]
  have hL : ∀ N ∈ Finset.range J, ((c + d) ^ N / (N.factorial : ℂ)) • (A ^ N) x
      = ∑ k ∈ Finset.range (N + 1), ((c ^ k / (k.factorial : ℂ)) * (d ^ (N - k) /
          ((N - k).factorial : ℂ))) • (A ^ (N - k + k)) x := by
    intro N _
    rw [add_pow, div_eq_mul_inv, Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [show N - k + k = N by omega]
    congr 1
    have h1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ N by omega)
    have hk' : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hNk : ((N - k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N - k)
    have hN : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
    have h1' : (N.choose k : ℂ) * k.factorial * (N - k).factorial = N.factorial := by
      exact_mod_cast h1
    field_simp
    rw [← h1']
    ring
  rw [Finset.sum_congr rfl hL]
  have htri := tri_reindex J (fun k i =>
    ((c ^ k / (k.factorial : ℂ)) * (d ^ i / (i.factorial : ℂ))) • (A ^ (i + k)) x)
  simp only at htri
  rw [htri]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  -- extend the inner sum from `range (J - k)` to `range J`: extra terms vanish
  rw [← Finset.sum_range_add_sum_Ico _ (show J - k ≤ J by omega)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (J - k) J) (fun i hi => by
    rw [Finset.mem_Ico] at hi
    rw [pow_apply_eq_zero_of_le hJ (by omega), smul_zero]), add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm i k]

theorem expOp_neg_cancel {A : Module.End ℂ M} (hA : LocNil A) (c : ℂ) (x : M) :
    expOp hA c (expOp hA (-c) x) = x := by
  rw [expOp_add, add_neg_cancel, expOp_zero]

theorem expOp_cancel_neg {A : Module.End ℂ M} (hA : LocNil A) (c : ℂ) (x : M) :
    expOp hA (-c) (expOp hA c x) = x := by
  rw [expOp_add, neg_add_cancel, expOp_zero]

/-! ## Translation of mode families -/

/-- The falling factorial `n(n−1)⋯(n−k+1)`. -/
noncomputable def ff (n : ℤ) (k : ℕ) : ℂ := ∏ i ∈ Finset.range k, ((n : ℂ) - (i : ℂ))

theorem ff_succ (n : ℤ) (k : ℕ) : ff n (k + 1) = ff n k * ((n : ℂ) - k) := by
  rw [ff, Finset.prod_range_succ]; rfl

theorem ff_div_factorial (n : ℤ) (k : ℕ) : ff n k / (k.factorial : ℂ) = cbz n k := by
  rw [cbz_apply_nonneg _ (by positivity), Int.toNat_natCast, gBinom, ff]

/-- **The Leibniz formula** for `[A, Xₙ] = n Xₙ₋₁`:
`Aᴺ Xₙ = Σₖ C(N,k) n⁽ᵏ⁾ Xₙ₋ₖ Aᴺ⁻ᵏ`. -/
theorem pow_comm_formula (A : Module.End ℂ M) (X : ℤ → Module.End ℂ M)
    (hX : ∀ (n : ℤ) (y : M), A (X n y) - X n (A y) = (n : ℂ) • X (n - 1) y)
    (N : ℕ) (n : ℤ) (y : M) :
    (A ^ N) (X n y) = ∑ k ∈ Finset.range (N + 1),
      ((N.choose k : ℂ) * ff n k) • X (n - k) ((A ^ (N - k)) y) := by
  induction N with
  | zero => simp [ff]
  | succ N ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_sum]
    have hstep : ∀ k ∈ Finset.range (N + 1),
        A (((N.choose k : ℂ) * ff n k) • X (n - k) ((A ^ (N - k)) y))
          = ((N.choose k : ℂ) * ff n k) • X (n - k) ((A ^ (N + 1 - k)) y)
            + ((N.choose k : ℂ) * ff n (k + 1)) • X (n - (k + 1 : ℕ)) ((A ^ (N - k)) y) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have h := hX (n - k) ((A ^ (N - k)) y)
      have hpow : A ((A ^ (N - k)) y) = (A ^ (N + 1 - k)) y := by
        rw [← Module.End.mul_apply, ← pow_succ', show N - k + 1 = N + 1 - k by omega]
      rw [map_smul, eq_add_of_sub_eq h, hpow, ff_succ, smul_add, add_comm]
      congr 1
      rw [smul_smul, show ((n - (k : ℤ) : ℤ) : ℂ) = (n : ℂ) - k by push_cast; ring,
        show n - (k : ℤ) - 1 = n - ((k + 1 : ℕ) : ℤ) by push_cast; ring, mul_assoc]
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
    -- Pascal splitting of the target
    have hP : ∀ k ∈ Finset.range (N + 1),
        (((N + 1).choose (k + 1) : ℂ) * ff n (k + 1)) •
            X (n - ((k + 1 : ℕ) : ℤ)) ((A ^ (N + 1 - (k + 1))) y)
          = ((N.choose k : ℂ) * ff n (k + 1)) • X (n - ((k + 1 : ℕ) : ℤ)) ((A ^ (N - k)) y)
            + ((N.choose (k + 1) : ℂ) * ff n (k + 1)) •
              X (n - ((k + 1 : ℕ) : ℤ)) ((A ^ (N + 1 - (k + 1))) y) := by
      intro k _
      rw [Nat.choose_succ_succ, Nat.cast_add, add_mul, add_smul,
        show N + 1 - (k + 1) = N - k by omega]
    have hB : ∑ k ∈ Finset.range (N + 1),
          ((N.choose (k + 1) : ℂ) * ff n (k + 1)) •
            X (n - ((k + 1 : ℕ) : ℤ)) ((A ^ (N + 1 - (k + 1))) y)
        + (((N.choose 0 : ℕ) : ℂ) * ff n 0) • X (n - ((0 : ℕ) : ℤ)) ((A ^ (N + 1 - 0)) y)
        = ∑ k ∈ Finset.range (N + 1),
          ((N.choose k : ℂ) * ff n k) • X (n - k) ((A ^ (N + 1 - k)) y) := by
      have := Finset.sum_range_succ' (fun k => ((N.choose k : ℂ) * ff n k) •
        X (n - (k : ℤ)) ((A ^ (N + 1 - k)) y)) (N + 1)
      rw [← this, Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul,
        zero_smul, add_zero]
    rw [Finset.sum_range_succ' _ (N + 1), Finset.sum_congr rfl hP, Finset.sum_add_distrib, ← hB]
    simp only [Nat.choose_zero_right, Nat.cast_one]
    abel

/-- **Translation by conjugation**: `e^{cA} Xₙ = (Σₖ C(n,k) cᵏ Xₙ₋ₖ) e^{cA}` for a
locally nilpotent `A` with `[A, Xₙ] = n Xₙ₋₁` and an upper truncated family `X`. -/
theorem expOp_conj {A : Module.End ℂ M} (hA : LocNil A) (X : ℤ → Module.End ℂ M)
    (hX : ∀ (n : ℤ) (y : M), A (X n y) - X n (A y) = (n : ℂ) • X (n - 1) y)
    (htr : ∀ y : M, ∃ K : ℤ, ∀ n : ℤ, n ≤ K → X n y = 0) (c : ℂ) (n : ℤ) (x : M) :
    expOp hA c (X n x) = ∑ᶠ k : ℕ, (cbz n k * c ^ k) • X (n - k) (expOp hA c x) := by
  obtain ⟨J₀, hJ₀⟩ := hA x
  obtain ⟨J₁, hJ₁⟩ := hA (X n x)
  choose Kf hKf using fun i : ℕ => htr ((A ^ i) x)
  obtain ⟨B₀, hB₀⟩ := OppBase.exists_bound_range J₀ (fun i => -Kf i)
  set kmax : ℕ := (n + B₀).toNat + 1
  have hvan : ∀ k : ℕ, kmax ≤ k → ∀ i < J₀, X (n - k) ((A ^ i) x) = 0 := by
    intro k hk i hi
    exact hKf i _ (by have := hB₀ i hi; omega)
  set B := max J₁ (J₀ + kmax)
  have hJB : (A ^ B) (X n x) = 0 := pow_apply_eq_zero_of_le hJ₁ (le_max_left _ _)
  rw [expOp_eq_sum hA c hJB, expOp_eq_sum hA c hJ₀]
  simp only [pow_comm_formula A X hX, Finset.smul_sum, smul_smul]
  have htri := tri_reindex B (fun k i => ((c ^ (k + i) / ((k + i).factorial : ℂ)) *
    (((k + i).choose k : ℂ) * ff n k)) • X (n - k) ((A ^ i) x))
  simp only at htri
  have hre : ∀ N ∈ Finset.range B, ∑ k ∈ Finset.range (N + 1),
      ((c ^ N / (N.factorial : ℂ)) * ((N.choose k : ℂ) * ff n k)) •
        X (n - k) ((A ^ (N - k)) x)
      = ∑ k ∈ Finset.range (N + 1), ((c ^ (k + (N - k)) / ((k + (N - k)).factorial : ℂ)) *
        (((k + (N - k)).choose k : ℂ) * ff n k)) • X (n - k) ((A ^ (N - k)) x) := by
    intro N _
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [show k + (N - k) = N by omega]
  rw [Finset.sum_congr rfl hre, htri]
  -- the right-hand side as a finite double sum
  have hsupp : Function.support (fun k : ℕ => (cbz n k * c ^ k) •
      X (n - k) (∑ i ∈ Finset.range J₀, (c ^ i / (i.factorial : ℂ)) • (A ^ i) x))
      ⊆ ↑(Finset.range B) := by
    intro k hk
    rw [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hk
    rw [map_sum, Finset.sum_eq_zero (fun i hi => by
      rw [map_smul, hvan k (by omega) i (Finset.mem_range.1 hi), smul_zero]), smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [map_sum, Finset.smul_sum]
  simp only [map_smul, smul_smul]
  have hcoef : ∀ i : ℕ, (c ^ (k + i) / ((k + i).factorial : ℂ)) * (((k + i).choose k : ℂ) * ff n k)
      = cbz n k * c ^ k * (c ^ i / (i.factorial : ℂ)) := by
    intro i
    rw [← ff_div_factorial]
    have h1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ k + i by omega)
    rw [show k + i - k = i by omega] at h1
    have h1' : ((k + i).choose k : ℂ) * k.factorial * i.factorial = (k + i).factorial := by
      exact_mod_cast h1
    have hk' : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hi' : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have hki : ((k + i).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k + i)
    field_simp
    rw [← h1', pow_add]
    ring
  simp only [hcoef]
  by_cases hkm : k < kmax
  · -- extend `range (B - k)` to `range J₀`: here `J₀ ≤ B - k`
    have hle : J₀ ≤ B - k := by omega
    rw [← Finset.sum_range_add_sum_Ico _ hle, Finset.sum_eq_zero (s := Finset.Ico J₀ (B - k))
      (fun i hi => by
        rw [Finset.mem_Ico] at hi
        rw [pow_apply_eq_zero_of_le hJ₀ hi.1, map_zero, smul_zero]), add_zero]
  · -- both sides vanish
    rw [Finset.sum_eq_zero (fun i hi => ?_), Finset.sum_eq_zero (fun i hi => ?_)]
    · rw [hvan k (by omega) i (Finset.mem_range.1 hi), smul_zero]
    · by_cases hi' : i < J₀
      · rw [hvan k (by omega) i hi', smul_zero]
      · rw [pow_apply_eq_zero_of_le hJ₀ (not_lt.mp hi'), map_zero, smul_zero]

end VOA.Huang.LiRegular
