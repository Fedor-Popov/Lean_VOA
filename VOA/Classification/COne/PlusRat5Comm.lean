import VOA.Classification.COne.PlusRat5Spec

/-! # Abe's commutation relations and the `M(1)⁺` chain in `V_{2m}⁺`

Abe (Math. Z. 249 (2005)), (4.6)-(4.9) and Lemma 4.5, on any weak `V_{2m}⁺`-module, with
`A = o(H⁴)`, `B = o(H⁶)`, `H^{2r}(n) = H^{2r}₍₂ᵣ₋₁₊ₙ₎`:

* `[A, L(1)] = -L(1) - 3H⁴(1)`, `[A, L(2)] = -6L(2) - 6H⁴(2)`, `[A, H⁴(1)] = -5/2 H⁴(1) - 3H⁶(1)`,
  `[B, L(1)] = -L(1) - 15/2 H⁴(1) - 5H⁶(1)`, `[A, B] = 0`,
  `[H⁴(1), L(k)] = -(3k-1) H⁴(k+1) - k(k+1)(3k+1)/6 L(k+1)`.
* `m1plus_chain`: if `A u = B u = 0`, and the two spectral implications
  `(5A² - 5A + 9B - 1) L(1)u = 0 ⇒ L(1)u = 0` and `(A + 2) L(2)u = 0 ⇒ L(2)u = 0` hold, then every
  positive `L(k)` and `H⁴(k)` kills `u` (Abe, Lemma 4.8).
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat5
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3 PlusRat4

theorem cert4w_4 : normR (polyActW H4R (-4 - 1) omR) = normR (combR []) := by decide +kernel

section Comm
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus m hm) M)

theorem H4w_four : (V2mPlus m hm).smul (HP m hm 2) ((4 : ℕ) : ℤ) (HP m hm 1) = 0 := by
  have := smul_HP_eq m hm 2 1 (by norm_num) (by norm_num) 4 [] (by decide) cert4w_4
  exact this.trans rfl

/-- `[A, L(1)] = -L(1) - 3H⁴(1)`. -/
theorem comm_A_L1 (y : M) :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 1)) 2 y) =
      mode (A.YM (HP m hm 1)) 2 (mode (A.YM (HP m hm 2)) 3 y) -
        mode (A.YM (HP m hm 1)) 2 y - (3 : ℂ) • mode (A.YM (HP m hm 2)) 4 y := by
  have h := zero_mode_comm A 3 (HP m hm 2) (HP m hm 1) 2 y
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H4w_eq m hm 0 (by norm_num), H4w_eq m hm 1 (by norm_num), H4w_eq m hm 2 (by norm_num),
    H4w_eq m hm 3 (by norm_num)]
  simp only [mode_combV, T4w, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num
  module

/-- `[A, L(2)] = -6L(2) - 6H⁴(2)`. -/
theorem comm_A_L2 (y : M) :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 1)) 3 y) =
      mode (A.YM (HP m hm 1)) 3 (mode (A.YM (HP m hm 2)) 3 y) -
        (6 : ℂ) • mode (A.YM (HP m hm 1)) 3 y - (6 : ℂ) • mode (A.YM (HP m hm 2)) 5 y := by
  have h := zero_mode_comm A 3 (HP m hm 2) (HP m hm 1) 3 y
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H4w_eq m hm 0 (by norm_num), H4w_eq m hm 1 (by norm_num), H4w_eq m hm 2 (by norm_num),
    H4w_eq m hm 3 (by norm_num)]
  simp only [mode_combV, T4w, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num
  module

/-- `[A, H⁴(1)] = -5/2 H⁴(1) - 3H⁶(1)`. -/
theorem comm_A_H41 (y : M) :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 2)) 4 y) =
      mode (A.YM (HP m hm 2)) 4 (mode (A.YM (HP m hm 2)) 3 y) -
        (5 / 2 : ℂ) • mode (A.YM (HP m hm 2)) 4 y - (3 : ℂ) • mode (A.YM (HP m hm 3)) 6 y := by
  have h := zero_mode_comm A 3 (HP m hm 2) (HP m hm 2) 4 y
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H44_eq m hm 0 (by norm_num), H44_eq m hm 1 (by norm_num), H44_eq m hm 2 (by norm_num),
    H44_eq m hm 3 (by norm_num)]
  simp only [mode_combV, T44, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num
  module

/-- `[B, L(1)] = -L(1) - 15/2 H⁴(1) - 5H⁶(1)`. -/
theorem comm_B_L1 (y : M) :
    mode (A.YM (HP m hm 3)) 5 (mode (A.YM (HP m hm 1)) 2 y) =
      mode (A.YM (HP m hm 1)) 2 (mode (A.YM (HP m hm 3)) 5 y) -
        mode (A.YM (HP m hm 1)) 2 y - (15 / 2 : ℂ) • mode (A.YM (HP m hm 2)) 4 y -
        (5 : ℂ) • mode (A.YM (HP m hm 3)) 6 y := by
  have h := zero_mode_comm A 5 (HP m hm 3) (HP m hm 1) 2 y
  rw [show ((5 : ℕ) : ℤ) = 5 by rfl] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H6w_eq m hm 0 (by norm_num), H6w_eq m hm 1 (by norm_num), H6w_eq m hm 2 (by norm_num),
    H6w_eq m hm 3 (by norm_num), H6w_eq m hm 4 (by norm_num), H6w_eq m hm 5 (by norm_num)]
  simp only [mode_combV, T6w, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  simp only [show Nat.choose 5 0 = 1 from rfl, show Nat.choose 5 1 = 5 from rfl,
    show Nat.choose 5 2 = 10 from rfl, show Nat.choose 5 3 = 10 from rfl,
    show Nat.choose 5 4 = 5 from rfl, show Nat.choose 5 5 = 1 from rfl]
  norm_num
  module

/-- `[A, B] = 0`. -/
theorem comm_A_B (y : M) :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 3)) 5 y) =
      mode (A.YM (HP m hm 3)) 5 (mode (A.YM (HP m hm 2)) 3 y) := by
  have h := zero_mode_comm A 3 (HP m hm 2) (HP m hm 3) 5 y
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H46_eq m hm 0 (by norm_num), H46_eq m hm 1 (by norm_num), H46_eq m hm 2 (by norm_num),
    H46_eq m hm 3 (by norm_num)]
  simp only [mode_combV, T46, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num
  module

/-- `[H⁴(1), L(k)] = -(3k-1) H⁴(k+1) - k(k+1)(3k+1)/6 L(k+1)`. -/
theorem comm_H41_L (k : ℤ) (y : M) :
    mode (A.YM (HP m hm 2)) 4 (mode (A.YM (HP m hm 1)) (k + 1) y) =
      mode (A.YM (HP m hm 1)) (k + 1) (mode (A.YM (HP m hm 2)) 4 y) -
        ((3 : ℂ) * k - 1) • mode (A.YM (HP m hm 2)) (k + 4) y -
        ((k : ℂ) * (k + 1) * (3 * k + 1) / 6) • mode (A.YM (HP m hm 1)) (k + 2) y := by
  have h := zero_mode_comm A 4 (HP m hm 2) (HP m hm 1) (k + 1) y
  rw [show ((4 : ℕ) : ℤ) = 4 by rfl] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H4w_eq m hm 0 (by norm_num), H4w_eq m hm 1 (by norm_num), H4w_eq m hm 2 (by norm_num),
    H4w_eq m hm 3 (by norm_num), H4w_four m hm]
  simp only [mode_combV, T4w, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC,
    map_zero, mode_zero, LinearMap.zero_apply, smul_zero, add_zero]
  simp only [show Nat.choose 4 0 = 1 from rfl, show Nat.choose 4 1 = 4 from rfl,
    show Nat.choose 4 2 = 6 from rfl, show Nat.choose 4 3 = 4 from rfl]
  push_cast
  rw [show (4 : ℤ) + (k + 1) - 0 - 3 = k + 2 by ring, show (4 : ℤ) + (k + 1) - 0 - 1 = k + 4 by ring,
    show (4 : ℤ) + (k + 1) - 1 - 2 = k + 2 by ring, show (4 : ℤ) + (k + 1) - 1 - 0 = k + 4 by ring,
    show (4 : ℤ) + (k + 1) - 2 - 1 = k + 2 by ring, show (4 : ℤ) + (k + 1) - 3 - 0 = k + 2 by ring]
  module

end Comm

/-! ## The `M(1)⁺` chain (Abe, Lemma 4.8) -/

section Chain
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus m hm) M)

include hm2 in
/-- **Abe's Lemma 4.8, abstract form.** -/
theorem m1plus_chain {u : M}
    (hA : mode (A.YM (HP m hm 2)) 3 u = 0) (hB : mode (A.YM (HP m hm 3)) 5 u = 0)
    (hinj1 : ∀ y : M, y = mode (A.YM (HP m hm 1)) 2 u →
      (5 : ℂ) • mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 2)) 3 y) -
        (5 : ℂ) • mode (A.YM (HP m hm 2)) 3 y + (9 : ℂ) • mode (A.YM (HP m hm 3)) 5 y - y = 0 →
      y = 0)
    (hinj2 : ∀ y : M, y = mode (A.YM (HP m hm 1)) 3 u →
      mode (A.YM (HP m hm 2)) 3 y + (2 : ℂ) • y = 0 → y = 0) :
    (∀ k : ℕ, 1 ≤ k → mode (A.YM (HP m hm 1)) ((k : ℤ) + 1) u = 0) ∧
      (∀ k : ℕ, 1 ≤ k → mode (A.YM (HP m hm 2)) ((k : ℤ) + 3) u = 0) := by
  set y := mode (A.YM (HP m hm 1)) 2 u with hy
  -- the three relations at `u`
  have e1 := comm_A_L1 m hm A u
  have e2 := comm_B_L1 m hm A u
  have e3 := comm_A_H41 m hm A u
  rw [hA, map_zero] at e1 e3
  rw [hB, map_zero] at e2
  rw [← hy] at e1 e2
  -- `H⁴(1)u` and `H⁶(1)u` in terms of `y`
  have hH4 : mode (A.YM (HP m hm 2)) 4 u =
      (-1 / 3 : ℂ) • (mode (A.YM (HP m hm 2)) 3 y + y) := by
    rw [e1]; module
  have hH6 : mode (A.YM (HP m hm 3)) 6 u =
      (-1 / 5 : ℂ) • (mode (A.YM (HP m hm 3)) 5 y + y) - (3 / 2 : ℂ) • mode (A.YM (HP m hm 2)) 4 u := by
    rw [e2]; module
  have hy0 : y = 0 := by
    apply hinj1 y rfl
    have e3' := e3
    rw [hH4, map_smul, map_add, hH6, hH4] at e3'
    linear_combination (norm := module) (-15 : ℂ) • e3'
  have hH40 : mode (A.YM (HP m hm 2)) 4 u = 0 := by rw [hH4, hy0]; simp
  -- `L(2)u`
  have e4 := comm_H41_L m hm A 1 u
  rw [show (1 : ℤ) + 1 = 2 by norm_num, ← hy, hy0, hH40, map_zero, map_zero] at e4
  have hH42 : mode (A.YM (HP m hm 2)) 5 u = (-2 / 3 : ℂ) • mode (A.YM (HP m hm 1)) 3 u := by
    rw [show (1 : ℤ) + 4 = 5 by norm_num, show (1 : ℤ) + 2 = 3 by norm_num] at e4
    push_cast at e4
    linear_combination (norm := module) (1 / 2 : ℂ) • e4
  have e5 := comm_A_L2 m hm A u
  rw [hA, map_zero, hH42] at e5
  have hL2 : mode (A.YM (HP m hm 1)) 3 u = 0 := by
    apply hinj2 _ rfl
    rw [e5]; module
  -- all `L(k)`
  have hL : ∀ k : ℕ, 1 ≤ k → mode (A.YM (HP m hm 1)) ((k : ℤ) + 1) u = 0 := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · interval_cases k
        · simpa [← hy] using hy0
        · simpa using hL2
      · have hv := vir2 m hm hm2 A ((k : ℤ) + 1) u
        rw [HP_one] at ih
        rw [HP_one]
        rw [ih (by omega), map_zero, ← HP_one, ← hy, hy0, map_zero, zero_add] at hv
        rw [HP_one] at hv
        have hc : ((2 : ℂ) - ((k : ℤ) + 1 : ℤ)) ≠ 0 := by
          push_cast
          intro h
          have : (k : ℂ) = 1 := by linear_combination -h
          have : k = 1 := by exact_mod_cast this
          omega
        have := hv.symm
        rw [smul_eq_zero] at this
        rcases this with h | h
        · exact absurd h hc
        · push_cast at h ⊢
          rw [show (k : ℤ) + 1 + 1 = ((k + 1 : ℕ) : ℤ) + 1 by push_cast; ring] at h
          exact h
  refine ⟨hL, ?_⟩
  -- all `H⁴(k)`
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 1 with hk1 | hk1
    · interval_cases k
      simpa using hH40
    · have h6 := comm_H41_L m hm A (k : ℤ) u
      have hLk : mode (A.YM (HP m hm 1)) ((k : ℤ) + 2) u = 0 := by
        have := hL (k + 1) (by omega)
        push_cast at this
        rw [show (k : ℤ) + 1 + 1 = k + 2 by ring] at this
        exact this
      rw [hL k hk1, map_zero, hH40, map_zero, hLk] at h6
      have hX : ((3 : ℂ) * k - 1) • mode (A.YM (HP m hm 2)) ((k : ℤ) + 4) u = 0 := by
        linear_combination (norm := module) h6
      have hc : ((3 : ℂ) * k - 1) ≠ 0 := by
        intro h
        have : (3 : ℂ) * k = 1 := by linear_combination h
        have : 3 * k = 1 := by exact_mod_cast this
        omega
      rcases smul_eq_zero.mp hX with h | h
      · exact absurd h hc
      · push_cast
        rw [show (k : ℤ) + 1 + 3 = k + 4 by ring]
        exact h

end Chain

end VOA.Classification.COne.PlusRat5
