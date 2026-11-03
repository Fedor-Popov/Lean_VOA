import VOA.Classification.COne.PlusRat4Gap2

/-! # Virasoro at level three on a top vector of a `V_{2m}⁺`-module (`c = 1`)

`[L(k-1), L(n-1)]` on any vector (`vir2`, `vir3`, `vir4`), and on a top vector `y`
(`L(0)y = h y`) with `V₁ = L(-1)³y`, `V₂ = L(-1)L(-2)y`, `V₃ = L(-3)y`, `R = L(-1)²y`,
`Q₁ = L(-2)y`:
`L(1)V₁ = (6h+6)R`, `L(1)V₂ = 3R + (2h+4)Q₁`, `L(1)V₃ = 4Q₁`,
`L(2)V₁ = (18h+6)L(-1)y`, `L(2)V₂ = (4h+19/2)L(-1)y`, `L(2)V₃ = 5L(-1)y`,
`L(3)V₁ = 24h y`, `L(3)V₂ = (16h+2) y`, `L(3)V₃ = (6h+2) y`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3

section Vir
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus m hm) M)


theorem omega4_omega : (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 4 (V2mPlus m hm).conformalVector = 0 := by
  have hg := (V2mPlus m hm).toPreVertexAlgebra.smul_mem_grading (V2mPlus m hm).conformal_mem
    (V2mPlus m hm).conformal_mem 4
  rw [(V2mPlus m hm).positivity _ (by norm_num), Submodule.mem_bot] at hg
  exact hg

include hm2 in
theorem vir2 (n : ℤ) (z : M) :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (V2mPlus m hm).conformalVector) n z) =
      mode (A.YM (V2mPlus m hm).conformalVector) n (mode (A.YM (V2mPlus m hm).conformalVector) 2 z) + ((2 : ℂ) - n) • mode (A.YM (V2mPlus m hm).conformalVector) (n + 1) z := by
  have h := zero_mode_comm A 2 (V2mPlus m hm).conformalVector (V2mPlus m hm).conformalVector n z
  rw [show ((2 : ℕ) : ℤ) = 2 by rfl] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat]
  rw [omega_neg_smul, omega_zero_smul (V2mPlus m hm).conformal_mem, sm_two_eq_L1,
    L1_omega_zero_gen m hm hm2, T_mode]
  simp only [map_zero, mode_zero, LinearMap.zero_apply, map_smul, mode_smul, LinearMap.smul_apply,
    smul_zero, add_zero]
  rw [show (2 : ℤ) + n - 0 - 1 = n + 1 by ring, show (2 : ℤ) + n - 1 = n + 1 by ring]
  simp only [show Nat.choose 2 0 = 1 from rfl, show Nat.choose 2 1 = 2 from rfl]
  push_cast
  module

include hm2 in
theorem vir3 (n : ℤ) (z : M) :
    mode (A.YM (V2mPlus m hm).conformalVector) 3 (mode (A.YM (V2mPlus m hm).conformalVector) n z) =
      mode (A.YM (V2mPlus m hm).conformalVector) n (mode (A.YM (V2mPlus m hm).conformalVector) 3 z) + ((3 : ℂ) - n) • mode (A.YM (V2mPlus m hm).conformalVector) (n + 2) z +
        (1 / 2 : ℂ) • mode (A.YM (V2mPlus m hm).vacuum) (n) z := by
  have h := zero_mode_comm A 3 (V2mPlus m hm).conformalVector (V2mPlus m hm).conformalVector n z
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat]
  have e3 : (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 3 (V2mPlus m hm).conformalVector = (1 / 2 : ℂ) • (V2mPlus m hm).vacuum := L2_omega m hm
  rw [omega_neg_smul, omega_zero_smul (V2mPlus m hm).conformal_mem, sm_two_eq_L1,
    L1_omega_zero_gen m hm hm2, T_mode, e3]
  simp only [map_zero, mode_zero, LinearMap.zero_apply, map_smul, mode_smul, LinearMap.smul_apply,
    smul_zero, add_zero]
  rw [show (3 : ℤ) + n - 0 - 1 = n + 2 by ring, show (3 : ℤ) + n - 1 = n + 2 by ring,
    show (3 : ℤ) + n - 3 = n by ring]
  simp only [show Nat.choose 3 0 = 1 from rfl, show Nat.choose 3 1 = 3 from rfl,
    show Nat.choose 3 3 = 1 from rfl]
  push_cast
  module

include hm2 in
theorem vir4 (n : ℤ) (z : M) :
    mode (A.YM (V2mPlus m hm).conformalVector) 4 (mode (A.YM (V2mPlus m hm).conformalVector) n z) =
      mode (A.YM (V2mPlus m hm).conformalVector) n (mode (A.YM (V2mPlus m hm).conformalVector) 4 z) + ((4 : ℂ) - n) • mode (A.YM (V2mPlus m hm).conformalVector) (n + 3) z +
        (2 : ℂ) • mode (A.YM (V2mPlus m hm).vacuum) (n + 1) z := by
  have h := zero_mode_comm A 4 (V2mPlus m hm).conformalVector (V2mPlus m hm).conformalVector n z
  rw [show ((4 : ℕ) : ℤ) = 4 by rfl] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat]
  have e3 : (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 3 (V2mPlus m hm).conformalVector = (1 / 2 : ℂ) • (V2mPlus m hm).vacuum := L2_omega m hm
  rw [omega_neg_smul, omega_zero_smul (V2mPlus m hm).conformal_mem, sm_two_eq_L1,
    L1_omega_zero_gen m hm hm2, T_mode, e3, omega4_omega m hm]
  simp only [map_zero, mode_zero, LinearMap.zero_apply, map_smul, mode_smul, LinearMap.smul_apply,
    smul_zero, add_zero]
  rw [show (4 : ℤ) + n - 0 - 1 = n + 3 by ring, show (4 : ℤ) + n - 1 = n + 3 by ring,
    show (4 : ℤ) + n - 3 = n + 1 by ring]
  simp only [show Nat.choose 4 0 = 1 from rfl, show Nat.choose 4 1 = 4 from rfl,
    show Nat.choose 4 3 = 4 from rfl]
  push_cast
  module

variable {y : M} {h : ℂ} (hyΩ : y ∈ Omega A) (hyL : L0 A y = h • y)

include hyL in
theorem L0_Rv : mode (A.YM (V2mPlus m hm).conformalVector) 1 (mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 y)) =
    (h + 2) • mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 y) := by
  have := L0_mode_eigen A (L0_mode_eigen A hyL (V2mPlus m hm).conformal_mem 0)
    (V2mPlus m hm).conformal_mem 0
  change mode (A.YM (V2mPlus m hm).conformalVector) 1 _ = _ at this
  rw [this]; congr 1
  all_goals (push_cast; ring)

include hyL in
theorem L0_Q1v : mode (A.YM (V2mPlus m hm).conformalVector) 1 (mode (A.YM (V2mPlus m hm).conformalVector) (-1) y) = (h + 2) • mode (A.YM (V2mPlus m hm).conformalVector) (-1) y := by
  have := L0_mode_eigen A hyL (V2mPlus m hm).conformal_mem (-1)
  change mode (A.YM (V2mPlus m hm).conformalVector) 1 _ = _ at this
  rw [this]; congr 1
  all_goals (push_cast; ring)

include hyL in
theorem L0_Lv : mode (A.YM (V2mPlus m hm).conformalVector) 1 (mode (A.YM (V2mPlus m hm).conformalVector) 0 y) = (h + 1) • mode (A.YM (V2mPlus m hm).conformalVector) 0 y := by
  have := L0_mode_eigen A hyL (V2mPlus m hm).conformal_mem 0
  change mode (A.YM (V2mPlus m hm).conformalVector) 1 _ = _ at this
  rw [this]; congr 1
  all_goals (push_cast; ring)

theorem vac_mode (n : ℤ) (z : M) :
    mode (A.YM (V2mPlus m hm).vacuum) n z = if n = -1 then z else 0 := by
  have := A.act_vacuum n z
  rw [WeakModule.act_def] at this
  exact this

include hm2 hyΩ hyL in
theorem L1_V1 : mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 y))) =
    (6 * h + 6) • mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 y) := by
  rw [vir2 m hm hm2 A 0, L1_R A hyΩ hyL, show (0 : ℤ) + 1 = 1 by norm_num, L0_Rv m hm A hyL,
    map_smul]
  push_cast
  module

include hm2 hyΩ hyL in
theorem L1_V2 : mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) (-1) y)) =
    (3 : ℂ) • mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 y) + (2 * h + 4) • mode (A.YM (V2mPlus m hm).conformalVector) (-1) y := by
  have q1 := L1_Q1 m hm A hyΩ hm2
  rw [HP_one] at q1
  rw [vir2 m hm hm2 A 0, q1, show (0 : ℤ) + 1 = 1 by norm_num, L0_Q1v m hm A hyL, map_smul]
  push_cast
  module

include hm2 hyΩ hyL in
theorem L1_V3 : mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (V2mPlus m hm).conformalVector) (-2) y) = (4 : ℂ) • mode (A.YM (V2mPlus m hm).conformalVector) (-1) y := by
  rw [vir2 m hm hm2 A (-2), Omega_mode_vanish hyΩ (V2mPlus m hm).conformal_mem
    (show (2 : ℤ) ≤ 2 by norm_num), map_zero, zero_add, show (-2 : ℤ) + 1 = -1 by norm_num]
  norm_num

include hm2 hyΩ hyL in
theorem L2_V1 : mode (A.YM (V2mPlus m hm).conformalVector) 3 (mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 y))) =
    (18 * h + 6) • mode (A.YM (V2mPlus m hm).conformalVector) 0 y := by
  rw [vir3 m hm hm2 A 0, L2_R A hyΩ hyL, show (0 : ℤ) + 2 = 2 by norm_num, L1_R A hyΩ hyL,
    vac_mode m hm A, if_neg (by norm_num), map_smul]
  push_cast
  module

include hm2 hyΩ hyL in
theorem L2_V2 : mode (A.YM (V2mPlus m hm).conformalVector) 3 (mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) (-1) y)) =
    (4 * h + 19 / 2) • mode (A.YM (V2mPlus m hm).conformalVector) 0 y := by
  have q1 := L1_Q1 m hm A hyΩ hm2
  have q2 := L2_Q1 m hm A hyΩ hyL hm2
  rw [HP_one] at q1 q2
  rw [vir3 m hm hm2 A 0, q2, show (0 : ℤ) + 2 = 2 by norm_num, q1, vac_mode m hm A,
    if_neg (by norm_num), map_smul]
  push_cast
  module

include hm2 hyΩ hyL in
theorem L2_V3 : mode (A.YM (V2mPlus m hm).conformalVector) 3 (mode (A.YM (V2mPlus m hm).conformalVector) (-2) y) = (5 : ℂ) • mode (A.YM (V2mPlus m hm).conformalVector) 0 y := by
  rw [vir3 m hm hm2 A (-2), Omega_mode_vanish hyΩ (V2mPlus m hm).conformal_mem
    (show (2 : ℤ) ≤ 3 by norm_num), map_zero, zero_add, show (-2 : ℤ) + 2 = 0 by norm_num,
    vac_mode m hm A, if_neg (by norm_num)]
  norm_num

include hm2 hyΩ hyL in
theorem L3_V1 : mode (A.YM (V2mPlus m hm).conformalVector) 4 (mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 y))) =
    (24 * h) • y := by
  have h4R : mode (A.YM (V2mPlus m hm).conformalVector) 4 (mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 y)) = 0 := by
    rw [vir4 m hm hm2 A 0, vir4 m hm hm2 A 0 y, Omega_mode_vanish hyΩ (V2mPlus m hm).conformal_mem
      (show (2 : ℤ) ≤ 4 by norm_num), Omega_mode_vanish hyΩ (V2mPlus m hm).conformal_mem
      (show (2 : ℤ) ≤ 0 + 3 by norm_num), vac_mode m hm A, vac_mode m hm A, if_neg (by norm_num),
      if_neg (by norm_num), show (0 : ℤ) + 3 = 3 by norm_num, vir3 m hm hm2 A 0 y,
      Omega_mode_vanish hyΩ (V2mPlus m hm).conformal_mem (show (2 : ℤ) ≤ 3 by norm_num),
      Omega_mode_vanish hyΩ (V2mPlus m hm).conformal_mem (show (2 : ℤ) ≤ 0 + 2 by norm_num),
      vac_mode m hm A, if_neg (by norm_num)]
    simp
  rw [vir4 m hm hm2 A 0, h4R, map_zero, zero_add, show (0 : ℤ) + 3 = 3 by norm_num, L2_R A hyΩ hyL,
    vac_mode m hm A,
    if_neg (by norm_num)]
  push_cast
  module

include hm2 hyΩ hyL in
theorem L3_V2 : mode (A.YM (V2mPlus m hm).conformalVector) 4 (mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) (-1) y)) =
    (16 * h + 2) • y := by
  have q2 := L2_Q1 m hm A hyΩ hyL hm2
  rw [HP_one] at q2
  have h4Q : mode (A.YM (V2mPlus m hm).conformalVector) 4 (mode (A.YM (V2mPlus m hm).conformalVector) (-1) y) = 0 := by
    rw [vir4 m hm hm2 A (-1), Omega_mode_vanish hyΩ (V2mPlus m hm).conformal_mem
      (show (2 : ℤ) ≤ 4 by norm_num), Omega_mode_vanish hyΩ (V2mPlus m hm).conformal_mem
      (show (2 : ℤ) ≤ -1 + 3 by norm_num), vac_mode m hm A, if_neg (by norm_num)]
    simp
  rw [vir4 m hm hm2 A 0, h4Q, map_zero, zero_add, show (0 : ℤ) + 3 = 3 by norm_num, q2,
    vac_mode m hm A,
    if_neg (by norm_num)]
  push_cast
  module

include hm2 hyΩ hyL in
theorem L3_V3 : mode (A.YM (V2mPlus m hm).conformalVector) 4 (mode (A.YM (V2mPlus m hm).conformalVector) (-2) y) = (6 * h + 2) • y := by
  have hω1 : mode (A.YM (V2mPlus m hm).conformalVector) 1 y = h • y := hyL
  rw [vir4 m hm hm2 A (-2), Omega_mode_vanish hyΩ (V2mPlus m hm).conformal_mem
    (show (2 : ℤ) ≤ 4 by norm_num), map_zero, zero_add, show (-2 : ℤ) + 3 = 1 by norm_num, hω1,
    vac_mode m hm A, if_pos (by norm_num), smul_smul]
  push_cast
  module

end Vir

end VOA.Classification.COne.PlusRat4
