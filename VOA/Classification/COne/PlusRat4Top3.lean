import VOA.Classification.COne.PlusRat4Vir3

/-! # Degree-three computations on a top vector of a `V_{2m}⁺`-module

Notation: `T₂ = H⁴₍₀₎x`, `T₃ = H⁶₍₂₎x`, `T₄ = H⁸₍₄₎x`, `V₁ = L(-1)³x`, `V₂ = L(-1)L(-2)x`,
`V₃ = L(-3)x`, `Q₂ = H⁴₍₁₎x`, `Q₃ = H⁶₍₃₎x`; `o(H⁴)x = a₄x`, `o(H⁶)x = a₆x`, `H⁴₍₂₎x = c₂L(-1)x`,
`H⁶₍₄₎x = c₃L(-1)x`.  Coefficients cross-checked against the Fock model (`gap3.py`,
`xside3.py`, `xside3o.py`).
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3

/-! ## §1  `L(3)` on a single mode (general VOA) -/

section General
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V} (A : WeakModule W M)

theorem L3_on4 {x : M} (hx : x ∈ Omega A) {wt : ℤ} {u : V} (hu : u ∈ W.grading wt) (n : ℤ) :
    mode (A.YM W.conformalVector) 4 (mode (A.YM u) n x) =
      ((4 * wt - n - 4 : ℤ) : ℂ) • mode (A.YM u) (n + 3) x +
        (6 : ℂ) • mode (A.YM (W.L 1 u)) (n + 2) x +
        (4 : ℂ) • mode (A.YM (W.smul W.conformalVector 3 u)) (n + 1) x +
        mode (A.YM (W.smul W.conformalVector 4 u)) n x := by
  have h := zero_mode_comm A 4 W.conformalVector u n x
  rw [show ((4 : ℕ) : ℤ) = 4 by rfl,
    Omega_mode_vanish hx W.conformal_mem (show (2 : ℤ) ≤ 4 by norm_num), map_zero, zero_add] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat]
  rw [omega_neg_smul, omega_zero_smul hu, show W.smul W.conformalVector 2 u = W.L 1 u by
    rw [VertexOperatorAlgebra.L_def]; rfl, T_mode, map_smul, mode_smul, LinearMap.smul_apply,
    show (4 : ℤ) + n - 0 - 1 = n + 3 by ring, show (4 : ℤ) + n - 1 = n + 3 by ring,
    show (4 : ℤ) + n - 2 = n + 2 by ring, show (4 : ℤ) + n - 3 = n + 1 by ring,
    show (4 : ℤ) + n - 4 = n by ring]
  simp only [show Nat.choose 4 0 = 1 from rfl, show Nat.choose 4 1 = 4 from rfl,
    show Nat.choose 4 2 = 6 from rfl, show Nat.choose 4 3 = 4 from rfl,
    show Nat.choose 4 4 = 1 from rfl]
  push_cast
  module

end General

/-! ## §2  Certificates -/

theorem certL3H6 : normR (polyActW omR (-4 - 1) H6R) = normR (combR [(-21 / 5, 1, 1)]) := by
  decide +kernel

section Certs3
variable (m : ℕ) (hm : 1 ≤ m)

theorem L3_H6 : (V2mPlus m hm).smul (HP m hm 1) 4 (HP m hm 3) = combV m hm [(-21 / 5, 1, 1)] :=
  smul_HP_eq m hm 1 3 (by norm_num) (by norm_num) 4 _ (by decide) certL3H6

theorem L3_H4 (hm2 : 2 ≤ m) : (V2mPlus m hm).smul (HP m hm 1) 4 (HP m hm 2) = 0 := by
  have hg : (V2mPlus m hm).smul (HP m hm 1) 4 (HP m hm 2) ∈ (V2mPlus m hm).grading 1 := by
    have := (V2mPlus m hm).toPreVertexAlgebra.smul_mem_grading (V2mPlus m hm).conformal_mem
      (HP_mem_grading m hm 2 (by norm_num) (by norm_num)) 4
    simpa using this
  rw [grading_one_eq_bot m hm hm2, Submodule.mem_bot] at hg
  exact hg

end Certs3

/-! ## §3  Formulas -/

section Formulas3
variable (m : ℕ) (hm : 1 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus m hm) M) {x : M} {h a4 a6 c2 c3 : ℂ}
  (hxΩ : x ∈ Omega A) (hxL : L0 A x = h • x)
  (h4 : mode (A.YM (HP m hm 2)) 3 x = a4 • x) (h6 : mode (A.YM (HP m hm 3)) 5 x = a6 • x)
  (hp2 : mode (A.YM (HP m hm 2)) 2 x = c2 • mode (A.YM (HP m hm 1)) 0 x)
  (hp3 : mode (A.YM (HP m hm 3)) 4 x = c3 • mode (A.YM (HP m hm 1)) 0 x)

include h4 in
theorem oH4_T2 :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 2)) 0 x) =
      (a4 + 9 / 2) • mode (A.YM (HP m hm 2)) 0 x + (9 : ℂ) • mode (A.YM (HP m hm 3)) 2 x := by
  have h := zero_mode_comm A 3 (HP m hm 2) (HP m hm 2) 0 x
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, h4, map_smul] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H44_eq m hm 0 (by norm_num), H44_eq m hm 1 (by norm_num), H44_eq m hm 2 (by norm_num),
    H44_eq m hm 3 (by norm_num)]
  simp only [mode_combV, T44, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num
  module

include h4 in
theorem oH4_T3 :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 3)) 2 x) =
      (27 / 20 : ℂ) • mode (A.YM (HP m hm 2)) 0 x + (a4 - 9 / 2) • mode (A.YM (HP m hm 3)) 2 x +
        (9 : ℂ) • mode (A.YM (HP m hm 4)) 4 x := by
  have h := zero_mode_comm A 3 (HP m hm 2) (HP m hm 3) 2 x
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, h4, map_smul] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H46_eq m hm 0 (by norm_num), H46_eq m hm 1 (by norm_num), H46_eq m hm 2 (by norm_num),
    H46_eq m hm 3 (by norm_num)]
  simp only [mode_combV, T46, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num
  module

include h6 in
theorem oH6_T2 :
    mode (A.YM (HP m hm 3)) 5 (mode (A.YM (HP m hm 2)) 0 x) =
      (a6 + 3 / 2) • mode (A.YM (HP m hm 2)) 0 x + (45 : ℂ) • mode (A.YM (HP m hm 3)) 2 x +
        (15 : ℂ) • mode (A.YM (HP m hm 4)) 4 x := by
  have h := zero_mode_comm A 5 (HP m hm 3) (HP m hm 2) 0 x
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
theorem oH4_V3 :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 1)) (-2) x) =
      (a4 + 9) • mode (A.YM (HP m hm 1)) (-2) x + (9 : ℂ) • mode (A.YM (HP m hm 2)) 0 x := by
  have h := zero_mode_comm A 3 (HP m hm 2) (HP m hm 1) (-2) x
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, h4, map_smul] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H4w_eq m hm 0 (by norm_num), H4w_eq m hm 1 (by norm_num), H4w_eq m hm 2 (by norm_num),
    H4w_eq m hm 3 (by norm_num)]
  simp only [mode_combV, T4w, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num
  module

include h6 in
theorem oH6_V3 :
    mode (A.YM (HP m hm 3)) 5 (mode (A.YM (HP m hm 1)) (-2) x) =
      (a6 + 33) • mode (A.YM (HP m hm 1)) (-2) x + (135 / 2 : ℂ) • mode (A.YM (HP m hm 2)) 0 x +
        (15 : ℂ) • mode (A.YM (HP m hm 3)) 2 x := by
  have h := zero_mode_comm A 5 (HP m hm 3) (HP m hm 1) (-2) x
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
theorem oH4_V1 :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 1)) 0
      (mode (A.YM (HP m hm 1)) 0 x))) =
      (a4 + 9 * c2) • mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 1)) 0
        (mode (A.YM (HP m hm 1)) 0 x)) +
        (18 : ℂ) • mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 2)) 1 x) +
        (6 : ℂ) • mode (A.YM (HP m hm 2)) 0 x := by
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
  have e3 : mode (A.YM (HP m hm 2)) 1 L = mode (A.YM (V2mPlus m hm).conformalVector) 0
      (mode (A.YM (HP m hm 2)) 1 x) + mode (A.YM (HP m hm 2)) 0 x := by
    rw [mode_translation A (HP m hm 2) 1 x, show (1 : ℤ) - 1 = 0 by norm_num]
    push_cast; rw [one_smul]
  have e4 : mode (A.YM (HP m hm 2)) 3 (mode (A.YM (V2mPlus m hm).conformalVector) 0 L) =
      (a4 + 6 * c2) • mode (A.YM (V2mPlus m hm).conformalVector) 0 L +
        (6 : ℂ) • mode (A.YM (HP m hm 2)) 1 x := by
    rw [mode_translation A (HP m hm 2) 3 L, e1, map_smul, show (3 : ℤ) - 1 = 2 by norm_num, e2]
    push_cast
    module
  have e5 : mode (A.YM (HP m hm 2)) 2 (mode (A.YM (V2mPlus m hm).conformalVector) 0 L) =
      mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (HP m hm 2)) 2 L) +
        (2 : ℂ) • mode (A.YM (HP m hm 2)) 1 L := by
    rw [mode_translation A (HP m hm 2) 2 L, show (2 : ℤ) - 1 = 1 by norm_num]
    push_cast; rfl
  rw [mode_translation A (HP m hm 2) 3 (mode (A.YM (V2mPlus m hm).conformalVector) 0 L), e4,
    show (3 : ℤ) - 1 = 2 by norm_num, e5, e2, e3]
  simp only [map_add, map_smul]
  push_cast
  module

include h6 hp3 in
theorem oH6_V1 :
    mode (A.YM (HP m hm 3)) 5 (mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 1)) 0
      (mode (A.YM (HP m hm 1)) 0 x))) =
      (a6 + 15 * c3) • mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 1)) 0
        (mode (A.YM (HP m hm 1)) 0 x)) +
        (60 : ℂ) • mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 3)) 3 x) +
        (60 : ℂ) • mode (A.YM (HP m hm 3)) 2 x := by
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
  have e3 : mode (A.YM (HP m hm 3)) 3 L = mode (A.YM (V2mPlus m hm).conformalVector) 0
      (mode (A.YM (HP m hm 3)) 3 x) + (3 : ℂ) • mode (A.YM (HP m hm 3)) 2 x := by
    rw [mode_translation A (HP m hm 3) 3 x, show (3 : ℤ) - 1 = 2 by norm_num]
    push_cast; rfl
  have e4 : mode (A.YM (HP m hm 3)) 5 (mode (A.YM (V2mPlus m hm).conformalVector) 0 L) =
      (a6 + 10 * c3) • mode (A.YM (V2mPlus m hm).conformalVector) 0 L +
        (20 : ℂ) • mode (A.YM (HP m hm 3)) 3 x := by
    rw [mode_translation A (HP m hm 3) 5 L, e1, map_smul, show (5 : ℤ) - 1 = 4 by norm_num, e2]
    push_cast
    module
  have e5 : mode (A.YM (HP m hm 3)) 4 (mode (A.YM (V2mPlus m hm).conformalVector) 0 L) =
      mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (HP m hm 3)) 4 L) +
        (4 : ℂ) • mode (A.YM (HP m hm 3)) 3 L := by
    rw [mode_translation A (HP m hm 3) 4 L, show (4 : ℤ) - 1 = 3 by norm_num]
    push_cast; rfl
  rw [mode_translation A (HP m hm 3) 5 (mode (A.YM (V2mPlus m hm).conformalVector) 0 L), e4,
    show (5 : ℤ) - 1 = 4 by norm_num, e5, e2, e3]
  simp only [map_add, map_smul]
  push_cast
  module

include h4 hp2 in
theorem oH4_V2 :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 1)) (-1) x)) =
      (a4 + 2 + 3 * c2) • mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 1)) (-1) x) +
        (6 : ℂ) • mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 2)) 1 x) +
        (7 - 3 * c2) • mode (A.YM (HP m hm 1)) (-2) x +
        (15 : ℂ) • mode (A.YM (HP m hm 2)) 0 x := by
  have eQ1 := oH4_Q1 m hm A h4
  have e2 : mode (A.YM (HP m hm 2)) 2 (mode (A.YM (HP m hm 1)) (-1) x) =
      c2 • mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 1)) (-1) x) +
        (7 / 3 - c2) • mode (A.YM (HP m hm 1)) (-2) x + (5 : ℂ) • mode (A.YM (HP m hm 2)) 0 x := by
    have h := zero_mode_comm A 2 (HP m hm 2) (HP m hm 1) (-1) x
    rw [show ((2 : ℕ) : ℤ) = 2 by rfl, hp2, map_smul] at h
    rw [h]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [H4w_eq m hm 0 (by norm_num), H4w_eq m hm 1 (by norm_num), H4w_eq m hm 2 (by norm_num)]
    simp only [mode_combV, T4w, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
    have et : mode (A.YM (HP m hm 1)) (-1) (mode (A.YM (HP m hm 1)) 0 x) =
        mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 1)) (-1) x) -
          mode (A.YM (HP m hm 1)) (-2) x := by
      rw [HP_one, mode_translation, show (-1 : ℤ) - 1 = -2 by norm_num]
      push_cast; module
    rw [et]
    norm_num
    module
  rw [HP_one] at eQ1 e2 ⊢
  rw [mode_translation, eQ1, show (3 : ℤ) - 1 = 2 by norm_num, e2]
  simp only [map_add, map_smul]
  push_cast
  module

include h6 hp3 in
theorem oH6_V2 :
    mode (A.YM (HP m hm 3)) 5 (mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 1)) (-1) x)) =
      (a6 + 2 + 5 * c3) • mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 1)) (-1) x) +
        (15 : ℂ) • mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 2)) 1 x) +
        (10 : ℂ) • mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 3)) 3 x) +
        (31 - 5 * c3) • mode (A.YM (HP m hm 1)) (-2) x +
        (165 / 2 : ℂ) • mode (A.YM (HP m hm 2)) 0 x + (45 : ℂ) • mode (A.YM (HP m hm 3)) 2 x := by
  have eQ1 := oH6_Q1 m hm A h6
  have e2 : mode (A.YM (HP m hm 3)) 4 (mode (A.YM (HP m hm 1)) (-1) x) =
      c3 • mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 1)) (-1) x) +
        (31 / 5 - c3) • mode (A.YM (HP m hm 1)) (-2) x +
        (33 / 2 : ℂ) • mode (A.YM (HP m hm 2)) 0 x + (9 : ℂ) • mode (A.YM (HP m hm 3)) 2 x := by
    have h := zero_mode_comm A 4 (HP m hm 3) (HP m hm 1) (-1) x
    rw [show ((4 : ℕ) : ℤ) = 4 by rfl, hp3, map_smul] at h
    rw [h]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [H6w_eq m hm 0 (by norm_num), H6w_eq m hm 1 (by norm_num), H6w_eq m hm 2 (by norm_num),
      H6w_eq m hm 3 (by norm_num), H6w_eq m hm 4 (by norm_num)]
    simp only [mode_combV, T6w, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
    have et : mode (A.YM (HP m hm 1)) (-1) (mode (A.YM (HP m hm 1)) 0 x) =
        mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 1)) (-1) x) -
          mode (A.YM (HP m hm 1)) (-2) x := by
      rw [HP_one, mode_translation, show (-1 : ℤ) - 1 = -2 by norm_num]
      push_cast; module
    rw [et]
    simp only [show Nat.choose 4 0 = 1 from rfl, show Nat.choose 4 1 = 4 from rfl,
      show Nat.choose 4 2 = 6 from rfl, show Nat.choose 4 3 = 4 from rfl,
      show Nat.choose 4 4 = 1 from rfl]
    norm_num
    module
  rw [HP_one] at eQ1 e2 ⊢
  rw [mode_translation, eQ1, show (5 : ℤ) - 1 = 4 by norm_num, e2]
  simp only [map_add, map_smul]
  push_cast
  module

include hxΩ in
theorem L1_T2 :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (HP m hm 2)) 0 x) =
      (6 : ℂ) • mode (A.YM (HP m hm 2)) 1 x := by
  have hg := HP_mem_grading m hm 2 (by norm_num) (by norm_num)
  rw [L1_on_gen m hm A hxΩ hg 0, L1_H4]
  simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num

include hxΩ hxL hp2 in
theorem L2_T2 (hm2 : 2 ≤ m) :
    mode (A.YM (V2mPlus m hm).conformalVector) 3 (mode (A.YM (HP m hm 2)) 0 x) =
      (9 * c2 + 3) • mode (A.YM (HP m hm 1)) 0 x := by
  have hg := HP_mem_grading m hm 2 (by norm_num) (by norm_num)
  have e3 : (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 3 (HP m hm 2) =
      combV m hm [(2, 0, 1)] := L2_H4 m hm
  rw [L2_on3 A hxΩ hg 0, L1_H4, e3]
  simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  have e1 : mode (A.YM (HP m hm 2)) (0 + 2) x = c2 • mode (A.YM (HP m hm 1)) 0 x := hp2
  have e2 : mode (A.YM (HP m hm 1)) (0 + 1 - ((1 : ℕ) : ℤ)) x = mode (A.YM (HP m hm 1)) 0 x := rfl
  have e4 : mode (A.YM (HP m hm 1)) (0 - ((0 : ℕ) : ℤ)) x = mode (A.YM (HP m hm 1)) 0 x := rfl
  rw [e1, e2, e4]
  push_cast
  module

include hxΩ hxL h4 in
theorem L3_T2 (hm2 : 2 ≤ m) :
    mode (A.YM (V2mPlus m hm).conformalVector) 4 (mode (A.YM (HP m hm 2)) 0 x) =
      (12 * a4 + 12 * h) • x := by
  have hg := HP_mem_grading m hm 2 (by norm_num) (by norm_num)
  have e3 : (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 3 (HP m hm 2) =
      combV m hm [(2, 0, 1)] := L2_H4 m hm
  have e4 : (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 4 (HP m hm 2) = 0 := L3_H4 m hm hm2
  rw [L3_on4 A hxΩ hg 0, L1_H4, e3, e4]
  simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC,
    map_zero, mode_zero, LinearMap.zero_apply, add_zero]
  have e1 : mode (A.YM (HP m hm 2)) (0 + 3) x = a4 • x := h4
  have e2 : mode (A.YM (HP m hm 1)) (0 + 2 - ((1 : ℕ) : ℤ)) x = h • x := hxL
  have e5 : mode (A.YM (HP m hm 1)) (0 + 1 - ((0 : ℕ) : ℤ)) x = h • x := hxL
  rw [e1, e2, e5]
  push_cast
  module

include hxΩ hp2 in
theorem L1_T3 :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (HP m hm 3)) 2 x) =
      (8 : ℂ) • mode (A.YM (HP m hm 3)) 3 x + (3 : ℂ) • mode (A.YM (HP m hm 2)) 1 x := by
  have hg := HP_mem_grading m hm 3 (by norm_num) (by norm_num)
  rw [L1_on_gen m hm A hxΩ hg 2, L1_H6]
  simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num

include hxΩ hxL hp2 hp3 in
theorem L2_T3 :
    mode (A.YM (V2mPlus m hm).conformalVector) 3 (mode (A.YM (HP m hm 3)) 2 x) =
      (13 * c3 + 63 / 2 * c2 + 19 / 10) • mode (A.YM (HP m hm 1)) 0 x := by
  have hg := HP_mem_grading m hm 3 (by norm_num) (by norm_num)
  have e3 : (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 3 (HP m hm 3) =
      combV m hm [(4 / 5, 2, 1), (18, 0, 2)] := L2_H6 m hm
  rw [L2_on3 A hxΩ hg 2, L1_H6, e3]
  simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  have e1 : mode (A.YM (HP m hm 3)) (2 + 2) x = c3 • mode (A.YM (HP m hm 1)) 0 x := hp3
  have e2 : mode (A.YM (HP m hm 1)) (2 + 1 - ((3 : ℕ) : ℤ)) x = mode (A.YM (HP m hm 1)) 0 x := rfl
  have e4 : mode (A.YM (HP m hm 2)) (2 + 1 - ((1 : ℕ) : ℤ)) x = c2 • mode (A.YM (HP m hm 1)) 0 x :=
    hp2
  have e5 : mode (A.YM (HP m hm 1)) (2 - ((2 : ℕ) : ℤ)) x = mode (A.YM (HP m hm 1)) 0 x := rfl
  have e6 : mode (A.YM (HP m hm 2)) (2 - ((0 : ℕ) : ℤ)) x = c2 • mode (A.YM (HP m hm 1)) 0 x := hp2
  rw [e1, e2, e4, e5, e6]
  push_cast
  module

include hxΩ hxL h4 h6 in
theorem L3_T3 :
    mode (A.YM (V2mPlus m hm).conformalVector) 4 (mode (A.YM (HP m hm 3)) 2 x) =
      (18 * a6 + 108 * a4 + 30 * h) • x := by
  have hg := HP_mem_grading m hm 3 (by norm_num) (by norm_num)
  have e3 : (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 3 (HP m hm 3) =
      combV m hm [(4 / 5, 2, 1), (18, 0, 2)] := L2_H6 m hm
  have e4 : (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 4 (HP m hm 3) =
      combV m hm [(-21 / 5, 1, 1)] := L3_H6 m hm
  rw [L3_on4 A hxΩ hg 2, L1_H6, e3, e4]
  simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  have e1 : mode (A.YM (HP m hm 3)) (2 + 3) x = a6 • x := h6
  have e2 : mode (A.YM (HP m hm 1)) (2 + 2 - ((3 : ℕ) : ℤ)) x = h • x := hxL
  have e5 : mode (A.YM (HP m hm 2)) (2 + 2 - ((1 : ℕ) : ℤ)) x = a4 • x := h4
  have e6 : mode (A.YM (HP m hm 1)) (2 + 1 - ((2 : ℕ) : ℤ)) x = h • x := hxL
  have e7 : mode (A.YM (HP m hm 2)) (2 + 1 - ((0 : ℕ) : ℤ)) x = a4 • x := h4
  have e8 : mode (A.YM (HP m hm 1)) (2 - ((1 : ℕ) : ℤ)) x = h • x := hxL
  rw [e1, e2, e5, e6, e7, e8]
  push_cast
  module

end Formulas3

end VOA.Classification.COne.PlusRat4
