import VOA.Classification.COne.PlusRat4Quad
import VOA.Classification.COne.PlusRat4Transfer

/-! # Degree-two computations on a top vector of a `V_{2m}⁺`-module

Notation (`x` a top vector, `L(0)x = h x`, `o(H⁴)x = a₄x`, `o(H⁶)x = a₆x`):
`Lx = L(-1)x`, `R = L(-1)²x`, `Q₁ = L(-2)x = ω₍₋₁₎x`, `Q₂ = H⁴₍₁₎x`, `Q₃ = H⁶₍₃₎x`, `Q₄ = H⁸₍₅₎x`,
`v = E₍ₘ₋₃₎x`.  Degree one: `p₂ = H⁴₍₂₎x = c₂ Lx`, `p₃ = H⁶₍₄₎x = c₃ Lx`.

* `o(H⁴), o(H⁶)` on `Q₁, Q₂, Q₃, R` (commutator formula and the product tables);
* `L(1), L(2)` on `Q₁, Q₂, Q₃, R, v`;
* the `E`-virtual eigenvalue at degree two:
  `(2K²-5K+2) o(H⁴) v = ((2K²-5K+2) a₄ + 4((m-2)² - 4mh)) v`, `K = 2m`
  (given `o(E)x = 0` and `E₍ₘ₋₂₎x = 0`).
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3

/-! ## §1  General VOA: the degree-two iterate formula -/

section General
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V} (A : WeakModule W M)

/-- `(ω₍₋ₖ₎a)₍α+k-2₎x` on a top vector. -/
theorem omega_neg_mode2 {x : M} (hx : x ∈ Omega A) {h : ℂ} (hL : L0 A x = h • x)
    {α : ℤ} {a : V} (ha : a ∈ W.grading α) (k : ℤ) (hk : 1 ≤ k) :
    mode (A.YM (W.smul W.conformalVector (-k) a)) (α + k - 2) x =
      mode (A.YM W.conformalVector) (-k) (mode (A.YM a) (α + k - 2) x) -
        negOnePow (-k) • (mode (A.YM a) (α - 2) (mode (A.YM W.conformalVector) 0 x)
          + ((k : ℂ) * h) • mode (A.YM a) (α - 3) x) := by
  rw [module_iterate0 A W.conformalVector a x (-k) (α + k - 2)]
  rw [finsum_eq_sum_of_support_subset (s := {0, 1})]
  · rw [Finset.sum_pair (by norm_num)]
    have h2 : mode (A.YM a) (α + k - 2 + 1) x = 0 := Omega_mode_vanish hx ha (by omega)
    have hω1 : mode (A.YM W.conformalVector) 1 x = h • x := hL
    rw [h2, map_zero, cbz_zero, cbz_one', show negOnePow 0 = 1 by simp [negOnePow],
      negOnePow_one', hω1, map_smul, add_zero,
      show -k + (α + k - 2) - 0 = α - 2 by ring, show -k + (α + k - 2) - 1 = α - 3 by ring,
      show -k - 0 = -k by ring]
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
    · rw [Omega_mode_vanish hx ha (show α ≤ α + k - 2 + i by omega), map_zero, zero_sub,
        Omega_mode_vanish hx W.conformal_mem (show (2 : ℤ) ≤ i by omega), map_zero,
        smul_zero, neg_zero, smul_zero]

/-- `L(2)` on a single mode applied to a top vector. -/
theorem L2_on {x : M} (hx : x ∈ Omega A) (u : V) (n : ℤ) :
    mode (A.YM W.conformalVector) 3 (mode (A.YM u) n x) =
      ∑ j ∈ Finset.range 4, ((Nat.choose 3 j : ℕ) : ℂ) •
        mode (A.YM (W.smul W.conformalVector j u)) ((3 : ℤ) + n - j) x := by
  have h := zero_mode_comm A 3 W.conformalVector u n x
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl,
    Omega_mode_vanish hx W.conformal_mem (show (2 : ℤ) ≤ 3 by norm_num), map_zero, zero_add] at h
  exact h

/-- `L(1)` on a single mode applied to a top vector. -/
theorem L1_on' {x : M} (hx : x ∈ Omega A) (u : V) (n : ℤ) :
    mode (A.YM W.conformalVector) 2 (mode (A.YM u) n x) =
      ∑ j ∈ Finset.range 3, ((Nat.choose 2 j : ℕ) : ℂ) •
        mode (A.YM (W.smul W.conformalVector j u)) ((2 : ℤ) + n - j) x := by
  have h := zero_mode_comm A 2 W.conformalVector u n x
  rw [show ((2 : ℕ) : ℤ) = 2 by rfl,
    Omega_mode_vanish hx W.conformal_mem (show (2 : ℤ) ≤ 2 by norm_num), map_zero, zero_add] at h
  exact h


theorem omega_zero_smul {wt : ℤ} {u : V} (hu : u ∈ W.grading wt) :
    W.smul W.conformalVector 1 u = (wt : ℂ) • u := by
  rw [← VertexOperatorAlgebra.L_zero_grading W u hu, VertexOperatorAlgebra.L_def]; rfl

theorem omega_neg_smul (u : V) : W.smul W.conformalVector 0 u = W.L (-1) u := by
  rw [VertexOperatorAlgebra.L_def]; rfl

/-- `L(2)(u₍ₙ₎x) = (3wt - n - 3) u₍ₙ₊₂₎x + 3 (L(1)u)₍ₙ₊₁₎x + (ω₍₃₎u)₍ₙ₎x` on a top vector. -/
theorem L2_on3 {x : M} (hx : x ∈ Omega A) {wt : ℤ} {u : V} (hu : u ∈ W.grading wt) (n : ℤ) :
    mode (A.YM W.conformalVector) 3 (mode (A.YM u) n x) =
      ((3 * wt - n - 3 : ℤ) : ℂ) • mode (A.YM u) (n + 2) x +
        (3 : ℂ) • mode (A.YM (W.L 1 u)) (n + 1) x +
        mode (A.YM (W.smul W.conformalVector 3 u)) n x := by
  rw [L2_on A hx]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat]
  rw [omega_neg_smul, omega_zero_smul hu, show W.smul W.conformalVector 2 u = W.L 1 u by
    rw [VertexOperatorAlgebra.L_def]; rfl, T_mode, map_smul, mode_smul, LinearMap.smul_apply,
    show (3 : ℤ) + n - 0 - 1 = n + 2 by ring, show (3 : ℤ) + n - 1 = n + 2 by ring,
    show (3 : ℤ) + n - 2 = n + 1 by ring, show (3 : ℤ) + n - 3 = n by ring]
  simp only [show Nat.choose 3 0 = 1 from rfl, show Nat.choose 3 1 = 3 from rfl,
    show Nat.choose 3 2 = 3 from rfl, show Nat.choose 3 3 = 1 from rfl]
  push_cast
  module


theorem L1_L {x : M} (hx : x ∈ Omega A) {h : ℂ} (hL : L0 A x = h • x) :
    mode (A.YM W.conformalVector) 2 (mode (A.YM W.conformalVector) 0 x) = (2 * h) • x := by
  have hω1 : mode (A.YM W.conformalVector) 1 x = h • x := hL
  rw [mode_translation A W.conformalVector 2 x, Omega_mode_vanish hx W.conformal_mem
    (show (2 : ℤ) ≤ 2 by norm_num), map_zero, zero_add, show (2 : ℤ) - 1 = 1 by norm_num, hω1,
    smul_smul]
  norm_num

theorem L0_L {x : M} {h : ℂ} (hL : L0 A x = h • x) :
    mode (A.YM W.conformalVector) 1 (mode (A.YM W.conformalVector) 0 x) =
      (h + 1) • mode (A.YM W.conformalVector) 0 x := by
  have hω1 : mode (A.YM W.conformalVector) 1 x = h • x := hL
  rw [mode_translation A W.conformalVector 1 x, hω1, map_smul, show (1 : ℤ) - 1 = 0 by norm_num]
  push_cast
  module

/-- `L(1)L(-1)²y` on a top vector. -/
theorem L1_R {x : M} (hx : x ∈ Omega A) {h : ℂ} (hL : L0 A x = h • x) :
    mode (A.YM W.conformalVector) 2
        (mode (A.YM W.conformalVector) 0 (mode (A.YM W.conformalVector) 0 x)) =
      (4 * h + 2) • mode (A.YM W.conformalVector) 0 x := by
  rw [mode_translation A W.conformalVector 2 (mode (A.YM W.conformalVector) 0 x),
    L1_L A hx hL, show (2 : ℤ) - 1 = 1 by norm_num, L0_L A hL, map_smul]
  push_cast
  module

/-- `L(2)L(-1)²y` on a top vector. -/
theorem L2_R {x : M} (hx : x ∈ Omega A) {h : ℂ} (hL : L0 A x = h • x) :
    mode (A.YM W.conformalVector) 3
        (mode (A.YM W.conformalVector) 0 (mode (A.YM W.conformalVector) 0 x)) =
      (6 * h) • x := by
  have h3 : mode (A.YM W.conformalVector) 3 (mode (A.YM W.conformalVector) 0 x) = 0 := by
    rw [mode_translation A W.conformalVector 3 x, Omega_mode_vanish hx W.conformal_mem
      (show (2 : ℤ) ≤ 3 by norm_num), Omega_mode_vanish hx W.conformal_mem
      (show (2 : ℤ) ≤ 3 - 1 by norm_num), map_zero, smul_zero, add_zero]
  rw [mode_translation A W.conformalVector 3 (mode (A.YM W.conformalVector) 0 x), h3, map_zero,
    zero_add, show (3 : ℤ) - 1 = 2 by norm_num, L1_L A hx hL, smul_smul]
  push_cast
  ring_nf

end General

/-! ## §2  `V⁺`: degree-two formulas -/

section Formulas
variable (m : ℕ) (hm : 1 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus m hm) M) {x : M} {h a4 a6 c2 c3 : ℂ}
  (hxΩ : x ∈ Omega A) (hxL : L0 A x = h • x)
  (h4 : mode (A.YM (HP m hm 2)) 3 x = a4 • x) (h6 : mode (A.YM (HP m hm 3)) 5 x = a6 • x)
  (hp2 : mode (A.YM (HP m hm 2)) 2 x = c2 • mode (A.YM (HP m hm 1)) 0 x)
  (hp3 : mode (A.YM (HP m hm 3)) 4 x = c3 • mode (A.YM (HP m hm 1)) 0 x)

theorem HP_one : HP m hm 1 = (V2mPlus m hm).conformalVector := rfl

include h4 in
/-- `o(H⁴)Q₂ = (a₄ - 1)Q₂ + 6Q₃`. -/
theorem oH4_Q2 :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 2)) 1 x) =
      (a4 - 1) • mode (A.YM (HP m hm 2)) 1 x + (6 : ℂ) • mode (A.YM (HP m hm 3)) 3 x := by
  have h := zero_mode_comm A 3 (HP m hm 2) (HP m hm 2) 1 x
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, h4, map_smul] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H44_eq m hm 0 (by norm_num), H44_eq m hm 1 (by norm_num), H44_eq m hm 2 (by norm_num),
    H44_eq m hm 3 (by norm_num)]
  simp only [mode_combV, T44, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num
  module

include h4 in
/-- `o(H⁴)Q₃ = (3/2)Q₂ + (a₄ - 5)Q₃ + 6Q₄`. -/
theorem oH4_Q3 :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 3)) 3 x) =
      (3 / 2 : ℂ) • mode (A.YM (HP m hm 2)) 1 x + (a4 - 5) • mode (A.YM (HP m hm 3)) 3 x +
        (6 : ℂ) • mode (A.YM (HP m hm 4)) 5 x := by
  have h := zero_mode_comm A 3 (HP m hm 2) (HP m hm 3) 3 x
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, h4, map_smul] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H46_eq m hm 0 (by norm_num), H46_eq m hm 1 (by norm_num), H46_eq m hm 2 (by norm_num),
    H46_eq m hm 3 (by norm_num)]
  simp only [mode_combV, T46, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num
  module

include h6 in
/-- `o(H⁶)Q₂ = (a₆ - 3)Q₂ + (10/3)Q₃ + 10Q₄`. -/
theorem oH6_Q2 :
    mode (A.YM (HP m hm 3)) 5 (mode (A.YM (HP m hm 2)) 1 x) =
      (a6 - 3) • mode (A.YM (HP m hm 2)) 1 x + (10 / 3 : ℂ) • mode (A.YM (HP m hm 3)) 3 x +
        (10 : ℂ) • mode (A.YM (HP m hm 4)) 5 x := by
  have h := zero_mode_comm A 5 (HP m hm 3) (HP m hm 2) 1 x
  rw [show ((5 : ℕ) : ℤ) = 5 by rfl, h6, map_smul] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H64_eq m hm 0 (by norm_num), H64_eq m hm 1 (by norm_num), H64_eq m hm 2 (by norm_num),
    H64_eq m hm 3 (by norm_num), H64_eq m hm 4 (by norm_num), H64_eq m hm 5 (by norm_num)]
  simp only [mode_combV, T64, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  simp only [show Nat.choose 5 0 = 1 from rfl, show Nat.choose 5 1 = 5 from rfl,
    show Nat.choose 5 2 = 10 from rfl, show Nat.choose 5 3 = 10 from rfl,
    show Nat.choose 5 4 = 5 from rfl, show Nat.choose 5 5 = 1 from rfl]
  norm_num
  module

include h4 in
/-- `o(H⁴)Q₁ = (a₄ + 2)Q₁ + 6Q₂`. -/
theorem oH4_Q1 :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 1)) (-1) x) =
      (a4 + 2) • mode (A.YM (HP m hm 1)) (-1) x + (6 : ℂ) • mode (A.YM (HP m hm 2)) 1 x := by
  have h := zero_mode_comm A 3 (HP m hm 2) (HP m hm 1) (-1) x
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, h4, map_smul] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H4w_eq m hm 0 (by norm_num), H4w_eq m hm 1 (by norm_num), H4w_eq m hm 2 (by norm_num),
    H4w_eq m hm 3 (by norm_num)]
  simp only [mode_combV, T4w, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num
  module

include h6 in
/-- `o(H⁶)Q₁ = (a₆ + 2)Q₁ + 15Q₂ + 10Q₃`. -/
theorem oH6_Q1 :
    mode (A.YM (HP m hm 3)) 5 (mode (A.YM (HP m hm 1)) (-1) x) =
      (a6 + 2) • mode (A.YM (HP m hm 1)) (-1) x + (15 : ℂ) • mode (A.YM (HP m hm 2)) 1 x +
        (10 : ℂ) • mode (A.YM (HP m hm 3)) 3 x := by
  have h := zero_mode_comm A 5 (HP m hm 3) (HP m hm 1) (-1) x
  rw [show ((5 : ℕ) : ℤ) = 5 by rfl, h6, map_smul] at h
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

include h4 hp2 in
/-- `o(H⁴)R = (a₄ + 6c₂)R + 6Q₂`. -/
theorem oH4_R :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 1)) 0 x)) =
      (a4 + 6 * c2) • mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 1)) 0 x) +
        (6 : ℂ) • mode (A.YM (HP m hm 2)) 1 x := by
  rw [HP_one] at hp2 ⊢
  set L := mode (A.YM (V2mPlus m hm).conformalVector) 0 x
  have e1 : mode (A.YM (HP m hm 2)) 3 L = (a4 + 3 * c2) • L := by
    rw [mode_translation A (HP m hm 2) 3 x, h4, show (3 : ℤ) - 1 = 2 by norm_num, hp2, map_smul,
      smul_smul, ← add_smul]
    push_cast; ring_nf; rfl
  have e2 : mode (A.YM (HP m hm 2)) 2 L = c2 • mode (A.YM (V2mPlus m hm).conformalVector) 0 L +
      (2 : ℂ) • mode (A.YM (HP m hm 2)) 1 x := by
    rw [mode_translation A (HP m hm 2) 2 x, hp2, map_smul, show (2 : ℤ) - 1 = 1 by norm_num]
    push_cast; ring_nf
  rw [mode_translation A (HP m hm 2) 3 L, e1, map_smul, show (3 : ℤ) - 1 = 2 by norm_num, e2]
  push_cast
  module

include h6 hp3 in
/-- `o(H⁶)R = (a₆ + 10c₃)R + 20Q₃`. -/
theorem oH6_R :
    mode (A.YM (HP m hm 3)) 5 (mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 1)) 0 x)) =
      (a6 + 10 * c3) • mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 1)) 0 x) +
        (20 : ℂ) • mode (A.YM (HP m hm 3)) 3 x := by
  rw [HP_one] at hp3 ⊢
  set L := mode (A.YM (V2mPlus m hm).conformalVector) 0 x
  have e1 : mode (A.YM (HP m hm 3)) 5 L = (a6 + 5 * c3) • L := by
    rw [mode_translation A (HP m hm 3) 5 x, h6, show (5 : ℤ) - 1 = 4 by norm_num, hp3, map_smul,
      smul_smul, ← add_smul]
    push_cast; ring_nf; rfl
  have e2 : mode (A.YM (HP m hm 3)) 4 L = c3 • mode (A.YM (V2mPlus m hm).conformalVector) 0 L +
      (4 : ℂ) • mode (A.YM (HP m hm 3)) 3 x := by
    rw [mode_translation A (HP m hm 3) 4 x, hp3, map_smul, show (4 : ℤ) - 1 = 3 by norm_num]
    push_cast; ring_nf
  rw [mode_translation A (HP m hm 3) 5 L, e1, map_smul, show (5 : ℤ) - 1 = 4 by norm_num, e2]
  push_cast
  module

/-! ### `L(1)` and `L(2)` -/

theorem sm_two_eq_L1 (u : VP m hm) :
    (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 2 u = (V2mPlus m hm).L 1 u := by
  rw [VertexOperatorAlgebra.L_def]; rfl

theorem vac_mode_neg_one (y : M) : mode (A.YM (V2mPlus m hm).vacuum) (-1) y = y := by
  have := A.act_vacuum (-1) y
  rw [WeakModule.act_def] at this
  rw [this, if_pos rfl]

include hxΩ in
/-- `L(1)Q₁ = 3 Lx`. -/
theorem L1_Q1 (hm2 : 2 ≤ m) :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (HP m hm 1)) (-1) x) =
      (3 : ℂ) • mode (A.YM (HP m hm 1)) 0 x := by
  rw [HP_one, L1_on_gen m hm A hxΩ (V2mPlus m hm).conformal_mem (-1), L1_omega_zero_gen m hm hm2,
    map_zero, mode_zero, LinearMap.zero_apply, add_zero, show (-1 : ℤ) + 1 = 0 by norm_num]
  norm_num

include hxΩ hxL in
/-- `L(2)Q₁ = (4h + 1/2) x`. -/
theorem L2_Q1 (hm2 : 2 ≤ m) :
    mode (A.YM (V2mPlus m hm).conformalVector) 3 (mode (A.YM (HP m hm 1)) (-1) x) =
      (4 * h + 1 / 2) • x := by
  have hω1 : mode (A.YM (V2mPlus m hm).conformalVector) 1 x = h • x := hxL
  have e3 : (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 3 (V2mPlus m hm).conformalVector =
      (1 / 2 : ℂ) • (V2mPlus m hm).vacuum := L2_omega m hm
  rw [HP_one, L2_on3 A hxΩ (V2mPlus m hm).conformal_mem (-1), L1_omega_zero_gen m hm hm2, e3,
    map_zero, mode_zero, LinearMap.zero_apply, smul_zero, add_zero, map_smul, mode_smul,
    LinearMap.smul_apply, vac_mode_neg_one m hm A, show (-1 : ℤ) + 2 = 1 by norm_num, hω1,
    smul_smul, ← add_smul]
  norm_num

include hxΩ hp2 in
/-- `L(1)Q₂ = (5c₂ + 1/3) Lx`. -/
theorem L1_Q2 :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (HP m hm 2)) 1 x) =
      (5 * c2 + 1 / 3) • mode (A.YM (HP m hm 1)) 0 x := by
  have hg := HP_mem_grading m hm 2 (by norm_num) (by norm_num)
  rw [L1_on_gen m hm A hxΩ hg 1, L1_H4]
  simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  have e1 : mode (A.YM (HP m hm 2)) (1 + 1) x = c2 • mode (A.YM (HP m hm 1)) 0 x := hp2
  have e2 : mode (A.YM (HP m hm 1)) (1 - ((1 : ℕ) : ℤ)) x = mode (A.YM (HP m hm 1)) 0 x := rfl
  rw [e1, e2]
  push_cast
  module

include hxΩ hxL h4 in
/-- `L(2)Q₂ = (8a₄ + 4h) x`. -/
theorem L2_Q2 :
    mode (A.YM (V2mPlus m hm).conformalVector) 3 (mode (A.YM (HP m hm 2)) 1 x) =
      (8 * a4 + 4 * h) • x := by
  have hg := HP_mem_grading m hm 2 (by norm_num) (by norm_num)
  have e3 : (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 3 (HP m hm 2) =
      combV m hm [(2, 0, 1)] := L2_H4 m hm
  rw [L2_on3 A hxΩ hg 1, L1_H4, e3]
  simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  have e1 : mode (A.YM (HP m hm 2)) (1 + 2) x = a4 • x := h4
  have e2 : mode (A.YM (HP m hm 1)) (1 + 1 - ((1 : ℕ) : ℤ)) x = h • x := hxL
  have e4 : mode (A.YM (HP m hm 1)) (1 - ((0 : ℕ) : ℤ)) x = h • x := hxL
  rw [e1, e2, e4]
  push_cast
  module

include hxΩ hp2 hp3 in
/-- `L(1)Q₃ = (7c₃ + 9c₂/2 + 1/10) Lx`. -/
theorem L1_Q3 :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (HP m hm 3)) 3 x) =
      (7 * c3 + 9 / 2 * c2 + 1 / 10) • mode (A.YM (HP m hm 1)) 0 x := by
  have hg := HP_mem_grading m hm 3 (by norm_num) (by norm_num)
  rw [L1_on_gen m hm A hxΩ hg 3, L1_H6]
  simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  have e1 : mode (A.YM (HP m hm 3)) (3 + 1) x = c3 • mode (A.YM (HP m hm 1)) 0 x := hp3
  have e2 : mode (A.YM (HP m hm 1)) (3 - ((3 : ℕ) : ℤ)) x = mode (A.YM (HP m hm 1)) 0 x := rfl
  have e3 : mode (A.YM (HP m hm 2)) (3 - ((1 : ℕ) : ℤ)) x = c2 • mode (A.YM (HP m hm 1)) 0 x := hp2
  rw [e1, e2, e3]
  push_cast
  module

include hxΩ hxL h4 h6 in
/-- `L(2)Q₃ = (12a₆ + 36a₄ + 6h) x`. -/
theorem L2_Q3 :
    mode (A.YM (V2mPlus m hm).conformalVector) 3 (mode (A.YM (HP m hm 3)) 3 x) =
      (12 * a6 + 36 * a4 + 6 * h) • x := by
  have hg := HP_mem_grading m hm 3 (by norm_num) (by norm_num)
  have e3 : (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 3 (HP m hm 3) =
      combV m hm [(4 / 5, 2, 1), (18, 0, 2)] := L2_H6 m hm
  rw [L2_on3 A hxΩ hg 3, L1_H6, e3]
  simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  have e1 : mode (A.YM (HP m hm 3)) (3 + 2) x = a6 • x := h6
  have e2 : mode (A.YM (HP m hm 1)) (3 + 1 - ((3 : ℕ) : ℤ)) x = h • x := hxL
  have e4 : mode (A.YM (HP m hm 2)) (3 + 1 - ((1 : ℕ) : ℤ)) x = a4 • x := h4
  have e5 : mode (A.YM (HP m hm 1)) (3 - ((2 : ℕ) : ℤ)) x = h • x := hxL
  have e6 : mode (A.YM (HP m hm 2)) (3 - ((0 : ℕ) : ℤ)) x = a4 • x := h4
  rw [e1, e2, e4, e5, e6]
  push_cast
  module

end Formulas

/-! ## §3  The `E`-part at degree two -/

section EPart
variable (m : ℕ) (hm : 1 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus m hm) M) {x : M} {h a4 : ℂ}
  (hxΩ : x ∈ Omega A) (hxL : L0 A x = h • x)
  (h4 : mode (A.YM (HP m hm 2)) 3 x = a4 • x)
  (hE0 : mode (A.YM (EP m hm)) ((m : ℤ) - 1) x = 0)
  (hE1 : mode (A.YM (EP m hm)) ((m : ℤ) - 2) x = 0)

include hE1 in
theorem E2_Lx :
    mode (A.YM (EP m hm)) ((m : ℤ) - 2) (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) =
      (((m : ℤ) - 2 : ℤ) : ℂ) • mode (A.YM (EP m hm)) ((m : ℤ) - 3) x := by
  rw [mode_translation, hE1, map_zero, zero_add, show (m : ℤ) - 2 - 1 = (m : ℤ) - 3 by ring]

include hxΩ hE1 in
theorem L1_v :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (EP m hm)) ((m : ℤ) - 3) x) = 0 := by
  rw [L1_on_gen m hm A hxΩ (EP_mem_grading m hm) _, L1_E m hm, map_zero, mode_zero,
    LinearMap.zero_apply, add_zero, show (m : ℤ) - 3 + 1 = (m : ℤ) - 2 by ring, hE1, smul_zero]

include hxΩ hE0 in
theorem L2_v :
    mode (A.YM (V2mPlus m hm).conformalVector) 3 (mode (A.YM (EP m hm)) ((m : ℤ) - 3) x) = 0 := by
  have e3 : (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 3 (EP m hm) = 0 := L2_E m hm
  rw [L2_on3 A hxΩ (EP_mem_grading m hm) _, L1_E m hm, e3,
    show (m : ℤ) - 3 + 2 = (m : ℤ) - 1 by ring, hE0]
  simp

include hxΩ hxL h4 hE0 hE1 in
/-- The `E`-virtual eigenvalue at degree two:
`(2K²-5K+2) o(H⁴) v = ((2K²-5K+2) a₄ + 4((m-2)² - 4mh)) v`, `K = 2m`, `v = E₍ₘ₋₃₎x`. -/
theorem oH4_v2 :
    ((2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2)) •
        mode (A.YM (HP m hm 2)) 3 (mode (A.YM (EP m hm)) ((m : ℤ) - 3) x) =
      ((2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2) * a4 + 4 * (((m : ℂ) - 2) ^ 2 - 4 * m * h)) •
        mode (A.YM (EP m hm)) ((m : ℤ) - 3) x := by
  have hLx := E2_Lx m hm A hE1
  have e3 : mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) 3 (EP m hm))) ((m : ℤ) - 3) x = 0 := by
    rw [H4_3_E]; simp
  have e2 : (3 : ℂ) • mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) 2 (EP m hm))) ((m : ℤ) - 2) x =
      (-(((m : ℤ) - 2 : ℤ) : ℂ)) • mode (A.YM (EP m hm)) ((m : ℤ) - 3) x := by
    have h2 := congrArg (fun y => mode (A.YM y) ((m : ℤ) - 2) x) (H4_2_E m hm)
    simp only [map_smul, mode_smul, LinearMap.smul_apply] at h2
    rw [T_mode, show (m : ℤ) - 2 - 1 = (m : ℤ) - 3 by ring] at h2
    exact h2
  have e1 : (2 * (2 * (m : ℂ)) - 1) •
      mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) 1 (EP m hm))) ((m : ℤ) - 1) x =
      (2 * (2 * (m : ℂ)) * ((m : ℂ) - 2 + h) - ((m : ℂ) - 1) * ((m : ℂ) - 2)) •
        mode (A.YM (EP m hm)) ((m : ℤ) - 3) x := by
    have h1 := congrArg (fun y => mode (A.YM y) ((m : ℤ) - 1) x) (H4_1_E m hm)
    simp only [map_smul, map_sub, mode_smul, mode_sub, LinearMap.smul_apply,
      LinearMap.sub_apply] at h1
    have hω := omega_neg_mode2 A hxΩ hxL (EP_mem_grading m hm) 1 le_rfl
    rw [show ((m : ℕ) : ℤ) + 1 - 2 = (m : ℤ) - 1 by ring, hE0, map_zero, zero_sub, hLx,
      negOnePow_neg_one', show ((m : ℕ) : ℤ) - 3 = (m : ℤ) - 3 by rfl] at hω
    rw [show (-1 : ℤ) = -1 by rfl] at hω
    rw [hω, T_mode, T_mode, show (m : ℤ) - 1 - 1 = (m : ℤ) - 2 by ring,
      show (m : ℤ) - 2 - 1 = (m : ℤ) - 3 by ring] at h1
    rw [h1]
    push_cast
    module
  have e0 : (2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2) •
      mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) 0 (EP m hm))) (m : ℤ) x =
      ((4 * (2 * (m : ℂ)) ^ 2 - 6 * (2 * (m : ℂ))) * (-((m : ℂ) - 2 + 2 * h)) +
        4 * (2 * (m : ℂ)) * (((m : ℂ) - 2) * ((m : ℂ) - 1 + h)) -
        2 * ((m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ) - 2))) •
        mode (A.YM (EP m hm)) ((m : ℤ) - 3) x := by
    have h0 := congrArg (fun y => mode (A.YM y) (m : ℤ) x) (H4_0_E m hm)
    simp only [map_smul, map_sub, map_add, mode_smul, mode_sub, mode_add, LinearMap.smul_apply,
      LinearMap.sub_apply, LinearMap.add_apply] at h0
    have hω2 := omega_neg_mode2 A hxΩ hxL (EP_mem_grading m hm) 2 (by norm_num)
    rw [show ((m : ℕ) : ℤ) + 2 - 2 = (m : ℤ) by ring,
      Omega_mode_vanish hxΩ (EP_mem_grading m hm) (le_refl (m : ℤ)), map_zero, zero_sub, hLx,
      negOnePow_neg_two'] at hω2
    have hω1 := omega_neg_mode2 A hxΩ hxL (LE_mem_grading_gen m hm) 1 le_rfl
    rw [show (m : ℤ) + 1 + 1 - 2 = (m : ℤ) by ring, show (m : ℤ) + 1 - 2 = (m : ℤ) - 1 by ring,
      show (m : ℤ) + 1 - 3 = (m : ℤ) - 2 by ring, T_mode, T_mode, T_mode,
      show (m : ℤ) - 1 = (m : ℤ) - 1 by rfl, negOnePow_neg_one', hE0,
      show (m : ℤ) - 1 - 1 = (m : ℤ) - 2 by ring, hLx, show (m : ℤ) - 2 - 1 = (m : ℤ) - 3 by ring]
      at hω1
    rw [hω2, hω1, T_mode, T_mode, T_mode, show (m : ℤ) - 1 - 1 = (m : ℤ) - 2 by ring,
      show (m : ℤ) - 2 - 1 = (m : ℤ) - 3 by ring] at h0
    rw [h0]
    simp only [smul_zero, map_zero]
    push_cast
    module
  have hc := zero_mode_comm A 3 (HP m hm 2) (EP m hm) ((m : ℤ) - 3) x
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, h4, map_smul] at hc
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, show Nat.choose 3 0 = 1 from rfl, show Nat.choose 3 1 = 3 from rfl,
    show Nat.choose 3 2 = 3 from rfl, show Nat.choose 3 3 = 1 from rfl] at hc
  rw [show (3 : ℤ) + ((m : ℤ) - 3) - 0 = (m : ℤ) by ring,
    show (3 : ℤ) + ((m : ℤ) - 3) - 1 = (m : ℤ) - 1 by ring,
    show (3 : ℤ) + ((m : ℤ) - 3) - 2 = (m : ℤ) - 2 by ring,
    show (3 : ℤ) + ((m : ℤ) - 3) - 3 = (m : ℤ) - 3 by ring, e3] at hc
  rw [hc]
  linear_combination (norm := module) e0 +
    (3 * (2 * (m : ℂ) - 2)) • e1 + ((2 * (2 * (m : ℂ)) - 1) * (2 * (m : ℂ) - 2)) • e2

end EPart

end VOA.Classification.COne.PlusRat4
