/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorStable

/-!
# `E₈` sector data: `c₀ = 247` (weight `-θ`), raising/Cartan/lowering tables, weights

Port of the `E7SectorWeyl`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E8

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6SectorSparse
open VOA.AffineGeneral.SCLie VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.DeligneSector

noncomputable section

theorem entryMatrix_toEntries_diag (l : List (ℕ × ℕ × ℤ)) (hl : inRange248 l = true)
    (h : l.all (fun t => !(t.1 == 247 && t.2.1 == 247)) = true) :
    A2.entryMatrix (toEntries l) ((247 : Fin 248), (247 : Fin 248)) = 0 := by
  unfold A2.entryMatrix toEntries
  rw [List.map_map]
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
  have h1 := List.all_eq_true.mp h t ht
  have h2 := List.all_eq_true.mp hl t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  simp only [Function.comp_apply, ite_eq_right_iff, Prod.mk.injEq, and_imp]
  intro e1 e2
  exfalso
  have e1' : t.1 = 247 := by
    have := congrArg Fin.val e1; simpa [Fin.ofNat, Nat.mod_eq_of_lt h2.1] using this
  have e2' : t.2.1 = 247 := by
    have := congrArg Fin.val e2; simpa [Fin.ofNat, Nat.mod_eq_of_lt h2.2] using this
  simp [e1', e2'] at h1

theorem e8_diag : ∀ r, E8data.fullMatrix r ((247 : Fin 248), (247 : Fin 248)) = 0 := by
  intro r
  cases r with
  | none =>
    show A2.entryMatrix (toEntries qQ) _ = 0
    exact entryMatrix_toEntries_diag _ qQ_inRange diag_q_ok
  | some r =>
    show A2.entryMatrix (toEntries (relQ (show Fin 3875 from r).val)) _ = 0
    have hall := diag_rel_ok
    have hr : (show Fin 3875 from r).val < 3875 := (show Fin 3875 from r).2
    exact entryMatrix_toEntries_diag _ (List.all_eq_true.mp rel_inRange _ (List.mem_range.mpr hr))
      (List.all_eq_true.mp hall _ (List.mem_range.mpr hr))

theorem fE8_eq (x y c : Fin 248) : fE8 x y c = (coef (entry e8T x y) c : ℂ) := rfl

theorem e8_raising : ∀ e : Fin 248, (8 ≤ e.val ∧ e.val < 128) → ∀ y, fE8 e y 247 = 0 := by
  intro e he y
  have h : ∃ lo, lo ≤ e.val ∧ e.val < lo + 8 ∧ (List.range' lo 8).all (fun e => (List.range 248).all fun y =>
      coef (entry e8T e y) 247 == 0) = true := by
    by_cases c0 : e.val < 16; · exact ⟨8, by omega, by omega, raising_ok0⟩
    by_cases c1 : e.val < 24; · exact ⟨16, by omega, by omega, raising_ok1⟩
    by_cases c2 : e.val < 32; · exact ⟨24, by omega, by omega, raising_ok2⟩
    by_cases c3 : e.val < 40; · exact ⟨32, by omega, by omega, raising_ok3⟩
    by_cases c4 : e.val < 48; · exact ⟨40, by omega, by omega, raising_ok4⟩
    by_cases c5 : e.val < 56; · exact ⟨48, by omega, by omega, raising_ok5⟩
    by_cases c6 : e.val < 64; · exact ⟨56, by omega, by omega, raising_ok6⟩
    by_cases c7 : e.val < 72; · exact ⟨64, by omega, by omega, raising_ok7⟩
    by_cases c8 : e.val < 80; · exact ⟨72, by omega, by omega, raising_ok8⟩
    by_cases c9 : e.val < 88; · exact ⟨80, by omega, by omega, raising_ok9⟩
    by_cases c10 : e.val < 96; · exact ⟨88, by omega, by omega, raising_ok10⟩
    by_cases c11 : e.val < 104; · exact ⟨96, by omega, by omega, raising_ok11⟩
    by_cases c12 : e.val < 112; · exact ⟨104, by omega, by omega, raising_ok12⟩
    by_cases c13 : e.val < 120; · exact ⟨112, by omega, by omega, raising_ok13⟩
    exact ⟨120, by omega, by omega, raising_ok14⟩
  obtain ⟨lo, h1, h2, h⟩ := h
  have := List.all_eq_true.mp (List.all_eq_true.mp h e (List.mem_range'_1.mpr ⟨h1, h2⟩)) y
    (List.mem_range.mpr y.2)
  rw [fE8_eq]; simpa using this

theorem e8_cartan : ∀ h : Fin 248, h.val < 8 → ∀ y : Fin 248,
    fE8 h y 247 = if y = (247 : Fin 248) then -(thetaH h : ℂ) else 0 := by
  have hc := cartan_ok
  intro h hh y
  have := List.all_eq_true.mp (List.all_eq_true.mp hc h (List.mem_range.mpr hh)) y (List.mem_range.mpr y.2)
  simp only [beq_iff_eq] at this
  have hmod : (⟨h.val % 248, Nat.mod_lt _ (by norm_num)⟩ : Fin 248) = h := Fin.ext (Nat.mod_eq_of_lt h.2)
  rw [hmod] at this
  rw [fE8_eq, show ((247 : Fin 248) : ℕ) = 247 from rfl, this]
  by_cases hy : y = (247 : Fin 248)
  · subst hy; simp
  · have : (y : ℕ) ≠ 247 := fun h' => hy (Fin.ext h')
    simp [hy, this]

/-! ## Weights -/

theorem e8_table_wt : ∀ x y c, E8Lie.wt c ≠ E8Lie.wt x + E8Lie.wt y → fE8 x y c = 0 := by
  intro x y c hne
  have hx : x.val < 248 := x.2
  have hchunk : ∃ lo hi, lo ≤ x.val ∧ x.val < hi ∧ wtChunk lo hi = true := by
    by_cases c0 : x.val < 4; · exact ⟨0, 4, by omega, by omega, wtChunk_0⟩
    by_cases c1 : x.val < 8; · exact ⟨4, 8, by omega, by omega, wtChunk_1⟩
    by_cases c2 : x.val < 12; · exact ⟨8, 12, by omega, by omega, wtChunk_2⟩
    by_cases c3 : x.val < 16; · exact ⟨12, 16, by omega, by omega, wtChunk_3⟩
    by_cases c4 : x.val < 20; · exact ⟨16, 20, by omega, by omega, wtChunk_4⟩
    by_cases c5 : x.val < 24; · exact ⟨20, 24, by omega, by omega, wtChunk_5⟩
    by_cases c6 : x.val < 28; · exact ⟨24, 28, by omega, by omega, wtChunk_6⟩
    by_cases c7 : x.val < 32; · exact ⟨28, 32, by omega, by omega, wtChunk_7⟩
    by_cases c8 : x.val < 36; · exact ⟨32, 36, by omega, by omega, wtChunk_8⟩
    by_cases c9 : x.val < 40; · exact ⟨36, 40, by omega, by omega, wtChunk_9⟩
    by_cases c10 : x.val < 44; · exact ⟨40, 44, by omega, by omega, wtChunk_10⟩
    by_cases c11 : x.val < 48; · exact ⟨44, 48, by omega, by omega, wtChunk_11⟩
    by_cases c12 : x.val < 52; · exact ⟨48, 52, by omega, by omega, wtChunk_12⟩
    by_cases c13 : x.val < 56; · exact ⟨52, 56, by omega, by omega, wtChunk_13⟩
    by_cases c14 : x.val < 60; · exact ⟨56, 60, by omega, by omega, wtChunk_14⟩
    by_cases c15 : x.val < 64; · exact ⟨60, 64, by omega, by omega, wtChunk_15⟩
    by_cases c16 : x.val < 68; · exact ⟨64, 68, by omega, by omega, wtChunk_16⟩
    by_cases c17 : x.val < 72; · exact ⟨68, 72, by omega, by omega, wtChunk_17⟩
    by_cases c18 : x.val < 76; · exact ⟨72, 76, by omega, by omega, wtChunk_18⟩
    by_cases c19 : x.val < 80; · exact ⟨76, 80, by omega, by omega, wtChunk_19⟩
    by_cases c20 : x.val < 84; · exact ⟨80, 84, by omega, by omega, wtChunk_20⟩
    by_cases c21 : x.val < 88; · exact ⟨84, 88, by omega, by omega, wtChunk_21⟩
    by_cases c22 : x.val < 92; · exact ⟨88, 92, by omega, by omega, wtChunk_22⟩
    by_cases c23 : x.val < 96; · exact ⟨92, 96, by omega, by omega, wtChunk_23⟩
    by_cases c24 : x.val < 100; · exact ⟨96, 100, by omega, by omega, wtChunk_24⟩
    by_cases c25 : x.val < 104; · exact ⟨100, 104, by omega, by omega, wtChunk_25⟩
    by_cases c26 : x.val < 108; · exact ⟨104, 108, by omega, by omega, wtChunk_26⟩
    by_cases c27 : x.val < 112; · exact ⟨108, 112, by omega, by omega, wtChunk_27⟩
    by_cases c28 : x.val < 116; · exact ⟨112, 116, by omega, by omega, wtChunk_28⟩
    by_cases c29 : x.val < 120; · exact ⟨116, 120, by omega, by omega, wtChunk_29⟩
    by_cases c30 : x.val < 124; · exact ⟨120, 124, by omega, by omega, wtChunk_30⟩
    by_cases c31 : x.val < 128; · exact ⟨124, 128, by omega, by omega, wtChunk_31⟩
    by_cases c32 : x.val < 132; · exact ⟨128, 132, by omega, by omega, wtChunk_32⟩
    by_cases c33 : x.val < 136; · exact ⟨132, 136, by omega, by omega, wtChunk_33⟩
    by_cases c34 : x.val < 140; · exact ⟨136, 140, by omega, by omega, wtChunk_34⟩
    by_cases c35 : x.val < 144; · exact ⟨140, 144, by omega, by omega, wtChunk_35⟩
    by_cases c36 : x.val < 148; · exact ⟨144, 148, by omega, by omega, wtChunk_36⟩
    by_cases c37 : x.val < 152; · exact ⟨148, 152, by omega, by omega, wtChunk_37⟩
    by_cases c38 : x.val < 156; · exact ⟨152, 156, by omega, by omega, wtChunk_38⟩
    by_cases c39 : x.val < 160; · exact ⟨156, 160, by omega, by omega, wtChunk_39⟩
    by_cases c40 : x.val < 164; · exact ⟨160, 164, by omega, by omega, wtChunk_40⟩
    by_cases c41 : x.val < 168; · exact ⟨164, 168, by omega, by omega, wtChunk_41⟩
    by_cases c42 : x.val < 172; · exact ⟨168, 172, by omega, by omega, wtChunk_42⟩
    by_cases c43 : x.val < 176; · exact ⟨172, 176, by omega, by omega, wtChunk_43⟩
    by_cases c44 : x.val < 180; · exact ⟨176, 180, by omega, by omega, wtChunk_44⟩
    by_cases c45 : x.val < 184; · exact ⟨180, 184, by omega, by omega, wtChunk_45⟩
    by_cases c46 : x.val < 188; · exact ⟨184, 188, by omega, by omega, wtChunk_46⟩
    by_cases c47 : x.val < 192; · exact ⟨188, 192, by omega, by omega, wtChunk_47⟩
    by_cases c48 : x.val < 196; · exact ⟨192, 196, by omega, by omega, wtChunk_48⟩
    by_cases c49 : x.val < 200; · exact ⟨196, 200, by omega, by omega, wtChunk_49⟩
    by_cases c50 : x.val < 204; · exact ⟨200, 204, by omega, by omega, wtChunk_50⟩
    by_cases c51 : x.val < 208; · exact ⟨204, 208, by omega, by omega, wtChunk_51⟩
    by_cases c52 : x.val < 212; · exact ⟨208, 212, by omega, by omega, wtChunk_52⟩
    by_cases c53 : x.val < 216; · exact ⟨212, 216, by omega, by omega, wtChunk_53⟩
    by_cases c54 : x.val < 220; · exact ⟨216, 220, by omega, by omega, wtChunk_54⟩
    by_cases c55 : x.val < 224; · exact ⟨220, 224, by omega, by omega, wtChunk_55⟩
    by_cases c56 : x.val < 228; · exact ⟨224, 228, by omega, by omega, wtChunk_56⟩
    by_cases c57 : x.val < 232; · exact ⟨228, 232, by omega, by omega, wtChunk_57⟩
    by_cases c58 : x.val < 236; · exact ⟨232, 236, by omega, by omega, wtChunk_58⟩
    by_cases c59 : x.val < 240; · exact ⟨236, 240, by omega, by omega, wtChunk_59⟩
    by_cases c60 : x.val < 244; · exact ⟨240, 244, by omega, by omega, wtChunk_60⟩
    exact ⟨244, 248, by omega, by omega, wtChunk_61⟩
  obtain ⟨lo, hi, h1, h2, hc⟩ := hchunk
  unfold wtChunk at hc
  have hrow := List.all_eq_true.mp (List.all_eq_true.mp hc x (List.mem_range'_1.mpr ⟨h1, by omega⟩)) y
    (List.mem_range.mpr y.2)
  rw [fE8_eq]
  norm_cast
  unfold coef
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
  have hpp := List.all_eq_true.mp hrow p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpp
  split_ifs with hpc
  · exfalso; apply hne
    obtain ⟨_, hp2⟩ := hpp
    have hw := wtLink
    unfold wtLinkOK at hw
    have wx := beq_iff_eq.mp (List.all_eq_true.mp hw x (List.mem_finRange x))
    have wy := beq_iff_eq.mp (List.all_eq_true.mp hw y (List.mem_finRange y))
    have wc := beq_iff_eq.mp (List.all_eq_true.mp hw c (List.mem_finRange c))
    have e2 := beq_iff_eq.mp hp2
    rw [hpc, ← wx, ← wy, ← wc] at e2
    funext k
    have := congrArg (fun l => l.getD k.val 0) e2
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, List.getElem?_zipWith] at this
    simpa [Fin.is_lt] using this
  · rfl

/-- **No `m`-fold weight sum hits `m·wt c₀ - (m e + 1)·wt i`**. -/
theorem noweight_of (c₀ : Fin 248) (hc₀ : E8Lie.wt c₀ = -thetaV)
    (hpos : ∀ y k, 0 ≤ E8Lie.wt y k + thetaV k)
    (i : Fin 248) (k₀ : Fin 8) (hi : E8Lie.wt i = -Pi.single k₀ 1) (e : ℕ)
    (hstr : ∀ y, (∀ k, k ≠ k₀ → E8Lie.wt y k + thetaV k = 0) → E8Lie.wt y k₀ + thetaV k₀ ≤ e)
    (m : ℕ) (t : Fin m → Fin 248) :
    ∑ j, E8Lie.wt (t j) ≠ m • E8Lie.wt c₀ - (m * e + 1) • E8Lie.wt i := by
  intro h
  have hk : ∀ k, ∑ j, (E8Lie.wt (t j) k + thetaV k) = (m * e + 1 : ℕ) * (Pi.single k₀ 1 : Fin 8 → ℤ) k := by
    intro k
    have := congrFun h k
    rw [hc₀, hi] at this
    simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, nsmul_eq_mul, Pi.mul_apply,
      Pi.natCast_apply] at this
    rw [Finset.sum_add_distrib, this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hzero : ∀ j, ∀ k, k ≠ k₀ → E8Lie.wt (t j) k + thetaV k = 0 := by
    intro j k hkk
    have h0 := hk k
    rw [Pi.single_eq_of_ne hkk, mul_zero] at h0
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hpos (t j) k)).mp h0 j (Finset.mem_univ _)
  have hle : ∑ j, (E8Lie.wt (t j) k₀ + thetaV k₀) ≤ ∑ _j : Fin m, (e : ℤ) :=
    Finset.sum_le_sum fun j _ => hstr (t j) (hzero j)
  rw [hk k₀, Pi.single_eq_same, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  push_cast at hle
  nlinarith

theorem e8_noweight : ∀ i : Fin 248, (i.val ∈ [135, 134, 133, 132, 131, 130, 129, 128]) → ∀ (m : ℕ) (t : Fin m → Fin 248),
    ∑ j, E8Lie.wt (t j) ≠ m • E8Lie.wt 247 - (m * lowExpE8 i + 1) • E8Lie.wt i := by
  intro i hi m t
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h | h | h | h | h
  · have : i = 135 := Fin.ext h
    subst this
    exact noweight_of 247 (by decide +kernel) e8_wt_pos 135 0 (by decide +kernel) 0 (by decide +kernel) m t
  · have : i = 134 := Fin.ext h
    subst this
    exact noweight_of 247 (by decide +kernel) e8_wt_pos 134 1 (by decide +kernel) 0 (by decide +kernel) m t
  · have : i = 133 := Fin.ext h
    subst this
    exact noweight_of 247 (by decide +kernel) e8_wt_pos 133 2 (by decide +kernel) 0 (by decide +kernel) m t
  · have : i = 132 := Fin.ext h
    subst this
    exact noweight_of 247 (by decide +kernel) e8_wt_pos 132 3 (by decide +kernel) 0 (by decide +kernel) m t
  · have : i = 131 := Fin.ext h
    subst this
    exact noweight_of 247 (by decide +kernel) e8_wt_pos 131 4 (by decide +kernel) 0 (by decide +kernel) m t
  · have : i = 130 := Fin.ext h
    subst this
    exact noweight_of 247 (by decide +kernel) e8_wt_pos 130 5 (by decide +kernel) 0 (by decide +kernel) m t
  · have : i = 129 := Fin.ext h
    subst this
    exact noweight_of 247 (by decide +kernel) e8_wt_pos 129 6 (by decide +kernel) 0 (by decide +kernel) m t
  · have : i = 128 := Fin.ext h
    subst this
    exact noweight_of 247 (by decide +kernel) e8_wt_pos 128 7 (by decide +kernel) 1 (by decide +kernel) m t

end

end VOA.DeligneAudit.DeligneCarrier.E8
