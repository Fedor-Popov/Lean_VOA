/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesArakawaPositive
import VOA.Examples.LeeYangSingular

/-!
# The lifts `Q₀, Q₁, Q₂` intertwine the slice map with `L₀, L₁, L₂`

Continuation of `TwoSeriesArakawaPositive`.  We prove

* `W1_Q0` — `W₁ (Q₀ y) = L₀ (W₁ y)` for every `y` and every `c`;
* `W1_Q1` — `W₁ (Q₁ y) = L₁ (W₁ y)` for every `y` and every `c`;
* `W1_Q2` — `W₁ (Q₂ y) = L₂ (W₁ y)` for every `y`, at the Drinfeld–Sokolov central charge
  `c = cDS k`.

Method: both sides kill the Whittaker ideal (`Q_i` normalise it); on Sugawara words
`L_{-n₁-2} ⋯ L_{-n_b-2}|0⟩` the identity is an induction on the word using
`[Q_i, L_{-N}] ≡ (i+N) Q_{i-N}` (`Q0_Lm`, `Q1_Lm`, `Q2_Lm`); and Sugawara words span `V^k`
modulo the Whittaker ideal (`sub_xi_mem_whit`).  The only place the central charge enters is
`(i, N) = (2, 2)`, where `c_sug/2 - 3k - 1 = c_DS/2` (`cSug_half`).

Everything here is proved; no new axiom.
-/

namespace VOA.TwoSeries.SliceMap

open VOA.AffineVOA VOA.AffineVOA.SugawaraCov VOA.AffineVOA.Strong MvPolynomial
open VOA.VirModule VOA.TwoSeries.DSSlice VOA.VirSimple VOA.LeeYangCharacter
open scoped BigOperators

noncomputable section

variable (c k : ℂ) (hk : k + 2 ≠ 0)

/-! ## §1  Sugawara words -/

/-- The Sugawara creation word `L_{-n₁-2} ⋯ L_{-n_b-2} |0⟩`. -/
def sugWord : List ℕ → WakModule k
  | [] => vacuumA k
  | n :: w => Lm k hk (-(n : ℤ) - 2) (sugWord w)

theorem W1_sugWord (w : List ℕ) : W1 c k hk (sugWord k hk w) = negWordVir c w := by
  induction w with
  | nil => exact W1_vac c k hk
  | cons n w ih => rw [sugWord, W1_Lm c k hk (by omega), ih, negWordVir_cons]

/-- The linear section `ξ : Vir^c → V^k` sending a sorted Virasoro word to its Sugawara word. -/
def xi : VirUniv c →ₗ[ℂ] WakModule k := (virBasis c).constr ℂ fun w => sugWord k hk w.1

theorem W1_xi (v : VirUniv c) : W1 c k hk (xi c k hk v) = v := by
  have h : (W1 c k hk).comp (xi c k hk) = LinearMap.id := by
    refine (virBasis c).ext fun w => ?_
    rw [LinearMap.comp_apply, xi, Module.Basis.constr_basis, W1_sugWord, LinearMap.id_apply,
      virBasis_apply]
  exact LinearMap.congr_fun h v

theorem mem_whit_of_W1_eq_zero {z : WakModule k} (hz : W1 c k hk z = 0) : z ∈ whitIdeal k := by
  have h0 : W0 k hk z = 0 := by
    simp only [W1, LinearMap.comp_apply, LinearEquiv.coe_coe] at hz
    exact (psi c k hk).injective (by rw [hz, map_zero])
  have := sub_sE_W0_mem k hk z
  rwa [h0, map_zero, sub_zero] at this

/-- Sugawara words span `V^k` modulo the Whittaker ideal. -/
theorem sub_xi_mem_whit (y : WakModule k) : y - xi c k hk (W1 c k hk y) ∈ whitIdeal k := by
  apply mem_whit_of_W1_eq_zero c k hk
  rw [map_sub, W1_xi, sub_self]

/-- **Extension principle.**  Two linear maps `V^k → Vir^c` that vanish on the Whittaker ideal
and agree on all Sugawara words agree everywhere. -/
theorem ext_of_whit_sugWord {F G : WakModule k →ₗ[ℂ] VirUniv c}
    (hF : ∀ z ∈ whitIdeal k, F z = 0) (hG : ∀ z ∈ whitIdeal k, G z = 0)
    (hw : ∀ w : List ℕ, F (sugWord k hk w) = G (sugWord k hk w)) : F = G := by
  have hxi : F.comp (xi c k hk) = G.comp (xi c k hk) := by
    refine (virBasis c).ext fun w => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, xi, Module.Basis.constr_basis]
    exact hw w.1
  refine LinearMap.ext fun y => ?_
  have hy := sub_xi_mem_whit c k hk y
  have e1 : F y = F (xi c k hk (W1 c k hk y)) := by
    rw [← sub_eq_zero, ← map_sub]; exact hF _ hy
  have e2 : G y = G (xi c k hk (W1 c k hk y)) := by
    rw [← sub_eq_zero, ← map_sub]; exact hG _ hy
  rw [e1, e2]
  exact LinearMap.congr_fun hxi _

/-! ## §2  Commutators with the Sugawara creation modes -/

theorem J0_Lm (a : Fin 3) (n : ℤ) (y : WakModule k) :
    J k a 0 (Lm k hk n y) = Lm k hk n (J k a 0 y) := by
  rw [J_Lm]; simp

theorem Lm_comm_apply (m n : ℤ) (hmn : m + n ≠ 0) (y : WakModule k) :
    Lm k hk m (Lm k hk n y) = Lm k hk n (Lm k hk m y) + ((m : ℂ) - n) • Lm k hk (m + n) y :=
  Lm_comm k hk m n hmn y

theorem Q0_Lm (N : ℕ) (y : WakModule k) :
    Q0 k hk (Lm k hk (-(N : ℤ) - 2) y) =
      Lm k hk (-(N : ℤ) - 2) (Q0 k hk y) + ((N : ℂ) + 2) • Lm k hk (-(N : ℤ) - 2) y := by
  simp only [Q0]
  rw [Lm_comm_apply k hk 0 _ (by omega), J0_Lm, map_add, map_smul, zero_add]
  push_cast
  module

theorem Q1_Lm (N : ℕ) (y : WakModule k) :
    Q1 k hk (Lm k hk (-(N : ℤ) - 2) y) =
      Lm k hk (-(N : ℤ) - 2) (Q1 k hk y) + ((N : ℂ) + 3) • Lm k hk (-(N : ℤ) - 1) y +
        J k 2 (-(N : ℤ) - 1) y := by
  simp only [Q1]
  rw [Lm_comm_apply k hk 1 _ (by omega), J_Lm k hk _ 2 1, J0_Lm, J0_Lm, J0_Lm]
  simp only [map_add, map_smul]
  rw [show (1 : ℤ) + (-(N : ℤ) - 2) = -(N : ℤ) - 1 by ring,
    show (-(N : ℤ) - 2) + 1 = -(N : ℤ) - 1 by ring]
  push_cast
  module

/-- The Sugawara central charge `3k/(k+2)`, through `[L₂, L₋₂] = 4 L₀ + c_sug/2`. -/
theorem Lm_two_neg_two (y : WakModule k) :
    Lm k hk 2 (Lm k hk (-2) y) = Lm k hk (-2) (Lm k hk 2 y) + (4 : ℂ) • Lm k hk 0 y +
      (centralChargeA k / 2) • y := by
  have h := congrArg (fun T : Module.End ℂ (WakModule k) => T y) (Vir.hYA_virasoro k hk 2 (-2))
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, if_pos (show (2 : ℤ) + -2 = 0 by norm_num),
    Module.End.one_apply] at h
  rw [sub_eq_iff_eq_add] at h
  change Lm k hk 2 (Lm k hk (-2) y) = _
  simp only [Lm] at h ⊢
  rw [show (2 : ℤ) + -2 + 1 = 0 + 1 by norm_num] at h
  rw [h]
  norm_num
  module

theorem Q2_Lm (N : ℕ) (y : WakModule k) :
    Q2 k hk (Lm k hk (-(N : ℤ) - 2) y) =
      Lm k hk (-(N : ℤ) - 2) (Q2 k hk y) + ((N : ℂ) + 4) • Lm k hk (-(N : ℤ)) y +
        (if N = 0 then (centralChargeA k / 2) • y else 0) + (3 : ℂ) • J k 2 (-(N : ℤ)) y +
        (3 * k) • J k 1 (-(N : ℤ) - 1) y + (1 / 2 : ℂ) • J k 1 0 (J k 2 (-(N : ℤ) - 1) y) +
        J k 1 (-(N : ℤ) - 1) (J k 2 0 y) := by
  have hL : Lm k hk 2 (Lm k hk (-(N : ℤ) - 2) y) = Lm k hk (-(N : ℤ) - 2) (Lm k hk 2 y) +
      ((N : ℂ) + 4) • Lm k hk (-(N : ℤ)) y +
        (if N = 0 then (centralChargeA k / 2) • y else 0) := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0
      simp only [Nat.cast_zero, neg_zero, zero_sub, if_true]
      rw [Lm_two_neg_two]
      norm_num
    · rw [if_neg (by omega), add_zero, Lm_comm_apply k hk 2 _ (by omega)]
      rw [show (2 : ℤ) + (-(N : ℤ) - 2) = -(N : ℤ) by ring]
      push_cast
      module
  have e1 : J k 1 0 (J k 2 1 (Lm k hk (-(N : ℤ) - 2) y)) =
      Lm k hk (-(N : ℤ) - 2) (J k 1 0 (J k 2 1 y)) + J k 1 0 (J k 2 (-(N : ℤ) - 1) y) := by
    rw [J_Lm k hk _ 2 1, map_add, J0_Lm, map_smul,
      show (-(N : ℤ) - 2) + 1 = -(N : ℤ) - 1 by ring]
    push_cast; module
  have e2 : J k 1 1 (J k 2 0 (Lm k hk (-(N : ℤ) - 2) y)) =
      Lm k hk (-(N : ℤ) - 2) (J k 1 1 (J k 2 0 y)) + J k 1 (-(N : ℤ) - 1) (J k 2 0 y) := by
    rw [J0_Lm, J_Lm k hk _ 1 1, show (-(N : ℤ) - 2) + 1 = -(N : ℤ) - 1 by ring]
    push_cast; module
  have e3 : J k 1 0 (J k 1 0 (J k 2 0 (Lm k hk (-(N : ℤ) - 2) y))) =
      Lm k hk (-(N : ℤ) - 2) (J k 1 0 (J k 1 0 (J k 2 0 y))) := by
    rw [J0_Lm, J0_Lm, J0_Lm]
  have e4 : J k 1 0 (J k 1 0 (Lm k hk (-(N : ℤ) - 2) y)) =
      Lm k hk (-(N : ℤ) - 2) (J k 1 0 (J k 1 0 y)) := by
    rw [J0_Lm, J0_Lm]
  have e5 : J k 2 2 (Lm k hk (-(N : ℤ) - 2) y) =
      Lm k hk (-(N : ℤ) - 2) (J k 2 2 y) + (2 : ℂ) • J k 2 (-(N : ℤ)) y := by
    rw [J_Lm k hk _ 2 2, show (-(N : ℤ) - 2) + 2 = -(N : ℤ) by ring]; push_cast; rfl
  have e6 : J k 1 1 (Lm k hk (-(N : ℤ) - 2) y) =
      Lm k hk (-(N : ℤ) - 2) (J k 1 1 y) + J k 1 (-(N : ℤ) - 1) y := by
    rw [J_Lm k hk _ 1 1, show (-(N : ℤ) - 2) + 1 = -(N : ℤ) - 1 by ring]; push_cast; module
  simp only [Q2]
  rw [hL, e1, e2, e3, e4, e5, e6]
  simp only [map_add, map_smul]
  split_ifs <;> module

/-! ## §3  The intertwining on Sugawara words -/

theorem Q0_vac : Q0 k hk (vacuumA k) = 0 := by
  simp only [Q0, Lm_vac k hk (by norm_num : (-1 : ℤ) ≤ 0), J_vacuum_nonneg k 2 le_rfl,
    smul_zero, add_zero]

theorem Q1_vac : Q1 k hk (vacuumA k) = 0 := by
  simp only [Q1, Lm_vac k hk (by norm_num : (-1 : ℤ) ≤ 1),
    J_vacuum_nonneg k 2 (by norm_num : (0 : ℤ) ≤ 1), J_vacuum_nonneg k 2 le_rfl,
    J_vacuum_nonneg k 1 le_rfl, map_zero, smul_zero, add_zero]

theorem Q2_vac : Q2 k hk (vacuumA k) = 0 := by
  simp only [Q2, Lm_vac k hk (by norm_num : (-1 : ℤ) ≤ 2),
    J_vacuum_nonneg k 2 (by norm_num : (0 : ℤ) ≤ 2), J_vacuum_nonneg k 2 (by norm_num : (0 : ℤ) ≤ 1),
    J_vacuum_nonneg k 1 (by norm_num : (0 : ℤ) ≤ 1), J_vacuum_nonneg k 2 le_rfl,
    J_vacuum_nonneg k 1 le_rfl, map_zero, smul_zero, add_zero]

theorem W1_Q0_sugWord (w : List ℕ) :
    W1 c k hk (Q0 k hk (sugWord k hk w)) = Lop c 0 (W1 c k hk (sugWord k hk w)) := by
  induction w with
  | nil => rw [sugWord, Q0_vac, map_zero, W1_vac, Lop_vacuum c (by norm_num)]
  | cons n w ih =>
      rw [sugWord, Q0_Lm, map_add, map_smul, W1_Lm c k hk (by omega), W1_Lm c k hk (by omega), ih,
        LeeYang.Lop_apply_comm c 0, if_neg (by omega)]
      rw [show (0 : ℤ) + (-(n : ℤ) - 2) = -(n : ℤ) - 2 by ring]
      push_cast
      module

theorem W1_Q1_sugWord (w : List ℕ) :
    W1 c k hk (Q1 k hk (sugWord k hk w)) = Lop c 1 (W1 c k hk (sugWord k hk w)) := by
  induction w with
  | nil => rw [sugWord, Q1_vac, map_zero, W1_vac, Lop_vacuum c (by norm_num)]
  | cons n w ih =>
      rw [sugWord, Q1_Lm, map_add, map_add, map_smul, W1_Lm c k hk (by omega),
        W1_Lm c k hk (by omega), ih, W1_h_le c k hk (by omega), W1_Lm c k hk (by omega),
        LeeYang.Lop_apply_comm c 1, if_neg (by omega)]
      rw [show (1 : ℤ) + (-(n : ℤ) - 2) = -(n : ℤ) - 1 by ring]
      push_cast
      module

/-- `c_sug/2 - 3k - 1 = c_DS/2`. -/
theorem cSug_half (hk : k + 2 ≠ 0) : centralChargeA k / 2 - 3 * k - 1 = cDS k / 2 := by
  rw [centralChargeA, cDS, dimSl2, dualCoxeter]
  field_simp
  ring

/-- `W₁ (Q₀ y) = L₀ (W₁ y)` for every `y`. -/
theorem W1_Q0 (y : WakModule k) : W1 c k hk (Q0 k hk y) = Lop c 0 (W1 c k hk y) := by
  have h := ext_of_whit_sugWord c k hk (F := (W1 c k hk).comp (Q0L k hk))
    (G := (Lop c 0).comp (W1 c k hk))
    (fun z hz => W1_whit c k hk (Q0_whitIdeal k hk hz))
    (fun z hz => by simp [W1_whit c k hk hz])
    (fun w => W1_Q0_sugWord c k hk w)
  exact LinearMap.congr_fun h y

/-- `W₁ (Q₁ y) = L₁ (W₁ y)` for every `y`. -/
theorem W1_Q1 (y : WakModule k) : W1 c k hk (Q1 k hk y) = Lop c 1 (W1 c k hk y) := by
  have h := ext_of_whit_sugWord c k hk (F := (W1 c k hk).comp (Q1L k hk))
    (G := (Lop c 1).comp (W1 c k hk))
    (fun z hz => W1_whit c k hk (Q1_whitIdeal k hk hz))
    (fun z hz => by simp [W1_whit c k hk hz])
    (fun w => W1_Q1_sugWord c k hk w)
  exact LinearMap.congr_fun h y

theorem W1_Q2_sugWord (w : List ℕ) :
    W1 (cDS k) k hk (Q2 k hk (sugWord k hk w)) =
      Lop (cDS k) 2 (W1 (cDS k) k hk (sugWord k hk w)) := by
  induction w with
  | nil => rw [sugWord, Q2_vac, map_zero, W1_vac, Lop_vacuum _ (by norm_num)]
  | cons n w ih =>
      set C := cDS k with hC
      set y := sugWord k hk w with hy
      rw [sugWord, Q2_Lm]
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        rw [if_pos rfl]
        simp only [neg_zero, zero_sub, CharP.cast_eq_zero, zero_add]
        have hfh : W1 C k hk (J k 1 0 (J k 2 (-1) y)) = (-2 : ℂ) • W1 C k hk y := by
          rw [f_h_comm k 0, map_add, map_smul, W1_h_le C k hk (by norm_num), zero_add,
            show (0 : ℤ) + -1 = -1 by norm_num, W1_fOne]
          module
        have hQ0 := W1_Q0 C k hk y
        simp only [Q0, map_add, map_smul] at hQ0
        have hL0 : W1 C k hk (Lm k hk 0 y) =
            Lop C 0 (W1 C k hk y) - (1 / 2 : ℂ) • W1 C k hk (J k 2 0 y) := by
          rw [← hQ0]; abel
        have hcs : centralChargeA k / 2 = C / 2 + 3 * k + 1 := by
          have := cSug_half k hk
          rw [← hC] at this
          linear_combination this
        simp only [map_add, map_smul]
        rw [W1_Lm C k hk (by norm_num), ih, hL0, hfh, W1_fOne, W1_fOne, W1_Lm C k hk (by norm_num),
          LeeYang.Lop_apply_comm C 2 (-2), if_pos (by norm_num), hcs]
        norm_num
        module
      · rw [if_neg (by omega), add_zero]
        have hfh : W1 C k hk (J k 1 0 (J k 2 (-(n : ℤ) - 1) y)) = 0 := by
          rw [f_h_comm k 0, map_add, map_smul, W1_h_le C k hk (by omega), zero_add,
            W1_f_le C k hk (by omega), smul_zero]
        simp only [map_add, map_smul]
        rw [W1_Lm C k hk (by omega), ih, hfh, W1_h_le C k hk (by omega), W1_f_le C k hk (by omega),
          W1_f_le C k hk (by omega), W1_Lm C k hk (by omega), W1_Lm C k hk (by omega),
          LeeYang.Lop_apply_comm C 2, if_neg (by omega),
          show (2 : ℤ) + (-(n : ℤ) - 2) = -(n : ℤ) by ring]
        push_cast
        module

/-- `W₁ (Q₂ y) = L₂ (W₁ y)` for every `y`, at the Drinfeld–Sokolov central charge. -/
theorem W1_Q2 (y : WakModule k) :
    W1 (cDS k) k hk (Q2 k hk y) = Lop (cDS k) 2 (W1 (cDS k) k hk y) := by
  have h := ext_of_whit_sugWord (cDS k) k hk (F := (W1 (cDS k) k hk).comp (Q2L k hk))
    (G := (Lop (cDS k) 2).comp (W1 (cDS k) k hk))
    (fun z hz => W1_whit _ k hk (Q2_whitIdeal k hk hz))
    (fun z hz => by simp [W1_whit _ k hk hz])
    (fun w => W1_Q2_sugWord k hk w)
  exact LinearMap.congr_fun h y

end

end VOA.TwoSeries.SliceMap
