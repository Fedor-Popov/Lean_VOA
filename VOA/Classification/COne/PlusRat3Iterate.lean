import VOA.Classification.COne.PlusRat3Raise

/-! # Mode identities on top vectors (general VOA)

* `omega_neg_mode`: for a top vector `x` (`x ∈ Ω`, `L(0)x = h x`), `a ∈ V_α`, `k ≥ 1`,
  `(ω₍₋ₖ₎a)₍α+k-1₎ x = -(-1)^k (a₍α-1₎ L(-1)x + k h a₍α-2₎ x)`.
* `zero_mode_comm`: `X₍ₖ₎ b₍ₙ₎ y = b₍ₙ₎ X₍ₖ₎ y + Σ_{j ≤ k} C(k,j) (X₍ⱼ₎b)₍ₖ₊ₙ₋ⱼ₎ y`.
* `Tpow_mode`: modes of `L(-1)^k a`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRat3
open VOA VertexOperatorAlgebra PlusSplitting PlusRatTelescope VOA.Huang.LogRemovalAdmissible
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V} (A : WeakModule W M)

theorem cbz_one' (n : ℤ) : cbz n 1 = (n : ℂ) := by
  rw [cbz_apply_nonneg n (by norm_num)]
  simp [gBinom]

theorem negOnePow_one' : negOnePow 1 = -1 := by
  have h := negOnePow_succ 0
  rw [zero_add] at h
  rw [h, show negOnePow 0 = 1 by simp [negOnePow]]

/-- The iterate formula for `ω₍₋ₖ₎a` on a top vector. -/
theorem omega_neg_mode {x : M} (hx : x ∈ Omega A) {h : ℂ} (hL : L0 A x = h • x)
    {α : ℤ} {a : V} (ha : a ∈ W.grading α) (k : ℤ) (hk : 1 ≤ k) :
    mode (A.YM (W.smul W.conformalVector (-k) a)) (α + k - 1) x =
      (-negOnePow (-k)) • (mode (A.YM a) (α - 1) (mode (A.YM W.conformalVector) 0 x)
        + ((k : ℂ) * h) • mode (A.YM a) (α - 2) x) := by
  rw [module_iterate0 A W.conformalVector a x (-k) (α + k - 1)]
  rw [finsum_eq_sum_of_support_subset (s := {0, 1})]
  · rw [Finset.sum_pair (by norm_num)]
    have h1 : mode (A.YM a) (α + k - 1 + 0) x = 0 := Omega_mode_vanish hx ha (by omega)
    have h2 : mode (A.YM a) (α + k - 1 + 1) x = 0 := Omega_mode_vanish hx ha (by omega)
    have hω1 : mode (A.YM W.conformalVector) 1 x = h • x := hL
    rw [h1, h2, map_zero, map_zero, cbz_zero, cbz_one', show negOnePow 0 = 1 by simp [negOnePow],
      negOnePow_one', hω1, map_smul,
      show -k + (α + k - 1) - 0 = α - 1 by ring, show -k + (α + k - 1) - 1 = α - 2 by ring]
    push_cast
    module
  · intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra hne
    apply hi
    by_cases hneg : i < 0
    · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
    · rw [Omega_mode_vanish hx ha (show α ≤ α + k - 1 + i by omega), map_zero, zero_sub,
        Omega_mode_vanish hx W.conformal_mem (show (2 : ℤ) ≤ i by omega), map_zero,
        smul_zero, neg_zero, smul_zero]

/-- The zero-mode commutator, truncated. -/
theorem zero_mode_comm (k : ℕ) (X b : V) (n : ℤ) (y : M) :
    mode (A.YM X) k (mode (A.YM b) n y) = mode (A.YM b) n (mode (A.YM X) k y) +
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) •
        mode (A.YM (W.smul X j b)) ((k : ℤ) + n - j) y := by
  have hc := mode_commutator A X b y (k : ℤ) n
  rw [finsum_cbz_nat] at hc
  rw [← hc]
  abel

/-- `(L(-1)a)₍ₙ₎ = -n a₍ₙ₋₁₎`. -/
theorem T_mode (a : V) (n : ℤ) (y : M) :
    mode (A.YM (W.L (-1) a)) n y = (-(n : ℂ)) • mode (A.YM a) (n - 1) y := by
  have := act_T_covariance A a n y
  simpa only [WeakModule.act_def] using this

/-- `(L(-1)^k a)₍ₙ₎ = fall n k · a₍ₙ₋ₖ₎` with `fall n k = Π_{i<k} (-(n - i))`. -/
def fallC (n : ℤ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => (-(n : ℂ)) * fallC (n - 1) k

theorem Tpow_mode (a : V) (y : M) : ∀ (k : ℕ) (n : ℤ),
    mode (A.YM ((W.L (-1))^[k] a)) n y = fallC n k • mode (A.YM a) (n - k) y
  | 0, n => by simp [fallC]
  | k + 1, n => by
    rw [Function.iterate_succ_apply', T_mode, Tpow_mode a y k (n - 1), smul_smul, fallC]
    congr 2
    push_cast; ring_nf

/-- `a₍ₙ₎ L(-1) y = L(-1) a₍ₙ₎ y + n a₍ₙ₋₁₎ y`. -/
theorem mode_translation (a : V) (n : ℤ) (y : M) :
    mode (A.YM a) n (mode (A.YM W.conformalVector) 0 y) =
      mode (A.YM W.conformalVector) 0 (mode (A.YM a) n y) + (n : ℂ) • mode (A.YM a) (n - 1) y :=
  mode_translation_defect A a n y

end VOA.Classification.COne.PlusRat3
