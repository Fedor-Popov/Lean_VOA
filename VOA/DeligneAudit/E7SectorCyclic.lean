/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorWeyl
import VOA.DeligneAudit.E7SectorCycChk

/-!
# `E₇` sector data: coadjoint cyclicity (depth 2 from `δ_{132}`)
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E7

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6SectorSparse
open VOA.AffineGeneral.SCLie VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.DeligneSector

noncomputable section

set_option linter.style.longLine false

theorem wordA_single (l : List (Fin 133)) :
    wordA fE7 l (Pi.single (132 : Fin 133) 1) = vecC 133 (wordS e7T 133 (l.map Fin.val) [(132, 1)]) := by
  rw [single_eq_vecC]
  exact wordA_vecC l _ (by simp)

theorem map_ofNat_val (l : List ℕ) (hl : l.all (fun x => decide (x < 133)) = true) :
    (l.map (Fin.ofNat 133)).map Fin.val = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro x hx
  have := List.all_eq_true.mp hl x hx
  simp only [decide_eq_true_eq] at this
  simp [Fin.ofNat, Nat.mod_eq_of_lt this]

theorem word_mem (l : List ℕ) (hl : l.all (fun x => decide (x < 133)) = true) (hlen : l.length ≤ 2) :
    vecC 133 (wordS e7T 133 l [(132, 1)]) ∈ slotWords fE7 132 2 := by
  have h := wordA_single (l.map (Fin.ofNat 133))
  rw [map_ofNat_val l hl] at h
  rw [← h]
  exact Submodule.subset_span ⟨_, by simpa using hlen, rfl⟩

theorem mem_of_word (l : List ℕ) (hl : l.all (fun x => decide (x < 133)) = true ∧ l.length ≤ 2)
    {c : Fin 133} (lam : ℤ) (hlam : lam ≠ 0)
    (h : zeroL (wordS e7T 133 l [(132, 1)] ++ scale (-lam) [((c : ℕ), 1)]) = true) :
    (Pi.single c 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 := by
  have hw := word_mem l hl.1 hl.2
  rw [vecC_eq_of_zeroL lam h, ← single_eq_vecC] at hw
  have := Submodule.smul_mem _ ((lam : ℂ)⁻¹) hw
  rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hlam), one_smul] at this

theorem combo_mem (ws : List (List ℕ × ℤ))
    (hws : ws.all (fun w => w.1.all (fun x => decide (x < 133)) && decide (w.1.length ≤ 2)) = true) :
    vecC 133 (ws.flatMap (fun w => scale w.2 (wordS e7T 133 w.1 [(132, 1)]))) ∈ slotWords fE7 132 2 := by
  induction ws with
  | nil =>
    have : vecC 133 ([] : List (ℕ × ℤ)) = 0 := by funext k; simp [vecC, coef]
    simp only [List.flatMap_nil, this]
    exact Submodule.zero_mem _
  | cons w ws ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hws
    rw [List.flatMap_cons, vecC_append, vecC_scale]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (word_mem w.1 hws.1.1 hws.1.2)) (ih hws.2)

theorem mem_of_combo (ws : List (List ℕ × ℤ))
    (hws : ws.all (fun w => w.1.all (fun x => decide (x < 133)) && decide (w.1.length ≤ 2)) = true)
    {c : Fin 133} (D : ℤ) (hD : D ≠ 0)
    (h : zeroL (ws.flatMap (fun w => scale w.2 (wordS e7T 133 w.1 [(132, 1)])) ++
      scale (-D) [((c : ℕ), 1)]) = true) :
    (Pi.single c 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 := by
  have hsum := combo_mem ws hws
  rw [vecC_eq_of_zeroL D h, ← single_eq_vecC] at hsum
  have := Submodule.smul_mem _ ((D : ℂ)⁻¹) hsum
  rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hD), one_smul] at this

theorem cyc0 : (Pi.single (0 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132] (by decide) (-1 : ℤ) (by norm_num) cycChk0

theorem cyc1 : (Pi.single (1 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_combo [([129, 88], (1 : ℤ)), ([130, 82], (-1 : ℤ)), ([131, 76], (-1 : ℤ)), ([132, 0], (-1 : ℤ)), ([127, 94], (-1 : ℤ))] (by decide) (2 : ℤ) (by norm_num) cycChk1

theorem cyc2 : (Pi.single (2 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_combo [([131, 76], (-1 : ℤ)), ([132, 0], (-1 : ℤ))] (by decide) (1 : ℤ) (by norm_num) cycChk2

theorem cyc3 : (Pi.single (3 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_combo [([130, 82], (-1 : ℤ)), ([131, 76], (-1 : ℤ)), ([132, 0], (-1 : ℤ))] (by decide) (1 : ℤ) (by norm_num) cycChk3

theorem cyc4 : (Pi.single (4 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_combo [([129, 88], (1 : ℤ)), ([130, 82], (-1 : ℤ)), ([131, 76], (-1 : ℤ)), ([132, 0], (-1 : ℤ)), ([127, 94], (1 : ℤ))] (by decide) (2 : ℤ) (by norm_num) cycChk4

theorem cyc5 : (Pi.single (5 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_combo [([127, 94], (1 : ℤ)), ([128, 93], (-1 : ℤ))] (by decide) (1 : ℤ) (by norm_num) cycChk5

theorem cyc6 : (Pi.single (6 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_combo [([126, 99], (2 : ℤ)), ([129, 88], (-1 : ℤ)), ([130, 82], (1 : ℤ)), ([131, 76], (1 : ℤ)), ([132, 0], (1 : ℤ)), ([128, 93], (-2 : ℤ)), ([127, 94], (3 : ℤ))] (by decide) (2 : ℤ) (by norm_num) cycChk6

theorem cyc7 : (Pi.single (7 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [126, 103] (by decide) (-1 : ℤ) (by norm_num) cycChk7

theorem cyc8 : (Pi.single (8 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [128, 99] (by decide) (1 : ℤ) (by norm_num) cycChk8

theorem cyc9 : (Pi.single (9 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [129, 93] (by decide) (-1 : ℤ) (by norm_num) cycChk9

theorem cyc10 : (Pi.single (10 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [130, 88] (by decide) (1 : ℤ) (by norm_num) cycChk10

theorem cyc11 : (Pi.single (11 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [131, 82] (by decide) (-1 : ℤ) (by norm_num) cycChk11

theorem cyc12 : (Pi.single (12 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [129, 94] (by decide) (1 : ℤ) (by norm_num) cycChk12

theorem cyc13 : (Pi.single (13 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 76] (by decide) (-1 : ℤ) (by norm_num) cycChk13

theorem cyc14 : (Pi.single (14 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [128, 103] (by decide) (1 : ℤ) (by norm_num) cycChk14

theorem cyc15 : (Pi.single (15 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [129, 99] (by decide) (-1 : ℤ) (by norm_num) cycChk15

theorem cyc16 : (Pi.single (16 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [130, 93] (by decide) (1 : ℤ) (by norm_num) cycChk16

theorem cyc17 : (Pi.single (17 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [131, 88] (by decide) (-1 : ℤ) (by norm_num) cycChk17

theorem cyc18 : (Pi.single (18 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [130, 94] (by decide) (1 : ℤ) (by norm_num) cycChk18

theorem cyc19 : (Pi.single (19 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 82] (by decide) (1 : ℤ) (by norm_num) cycChk19

theorem cyc20 : (Pi.single (20 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [129, 103] (by decide) (-1 : ℤ) (by norm_num) cycChk20

theorem cyc21 : (Pi.single (21 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [130, 99] (by decide) (1 : ℤ) (by norm_num) cycChk21

theorem cyc22 : (Pi.single (22 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [131, 93] (by decide) (-1 : ℤ) (by norm_num) cycChk22

theorem cyc23 : (Pi.single (23 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [130, 100] (by decide) (1 : ℤ) (by norm_num) cycChk23

theorem cyc24 : (Pi.single (24 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [131, 94] (by decide) (-1 : ℤ) (by norm_num) cycChk24

theorem cyc25 : (Pi.single (25 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 88] (by decide) (1 : ℤ) (by norm_num) cycChk25

theorem cyc26 : (Pi.single (26 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [130, 103] (by decide) (1 : ℤ) (by norm_num) cycChk26

theorem cyc27 : (Pi.single (27 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [131, 99] (by decide) (-1 : ℤ) (by norm_num) cycChk27

theorem cyc28 : (Pi.single (28 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [130, 104] (by decide) (1 : ℤ) (by norm_num) cycChk28

theorem cyc29 : (Pi.single (29 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [131, 100] (by decide) (-1 : ℤ) (by norm_num) cycChk29

theorem cyc30 : (Pi.single (30 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 93] (by decide) (1 : ℤ) (by norm_num) cycChk30

theorem cyc31 : (Pi.single (31 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 94] (by decide) (1 : ℤ) (by norm_num) cycChk31

theorem cyc32 : (Pi.single (32 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [131, 103] (by decide) (-1 : ℤ) (by norm_num) cycChk32

theorem cyc33 : (Pi.single (33 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [130, 108] (by decide) (1 : ℤ) (by norm_num) cycChk33

theorem cyc34 : (Pi.single (34 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [131, 104] (by decide) (-1 : ℤ) (by norm_num) cycChk34

theorem cyc35 : (Pi.single (35 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [131, 105] (by decide) (-1 : ℤ) (by norm_num) cycChk35

theorem cyc36 : (Pi.single (36 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 99] (by decide) (1 : ℤ) (by norm_num) cycChk36

theorem cyc37 : (Pi.single (37 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 100] (by decide) (1 : ℤ) (by norm_num) cycChk37

theorem cyc38 : (Pi.single (38 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [131, 108] (by decide) (-1 : ℤ) (by norm_num) cycChk38

theorem cyc39 : (Pi.single (39 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [131, 109] (by decide) (-1 : ℤ) (by norm_num) cycChk39

theorem cyc40 : (Pi.single (40 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 103] (by decide) (1 : ℤ) (by norm_num) cycChk40

theorem cyc41 : (Pi.single (41 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 104] (by decide) (1 : ℤ) (by norm_num) cycChk41

theorem cyc42 : (Pi.single (42 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 105] (by decide) (1 : ℤ) (by norm_num) cycChk42

theorem cyc43 : (Pi.single (43 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [131, 112] (by decide) (-1 : ℤ) (by norm_num) cycChk43

theorem cyc44 : (Pi.single (44 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [131, 113] (by decide) (-1 : ℤ) (by norm_num) cycChk44

theorem cyc45 : (Pi.single (45 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 108] (by decide) (1 : ℤ) (by norm_num) cycChk45

theorem cyc46 : (Pi.single (46 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 109] (by decide) (1 : ℤ) (by norm_num) cycChk46

theorem cyc47 : (Pi.single (47 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 110] (by decide) (1 : ℤ) (by norm_num) cycChk47

theorem cyc48 : (Pi.single (48 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [131, 116] (by decide) (-1 : ℤ) (by norm_num) cycChk48

theorem cyc49 : (Pi.single (49 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 112] (by decide) (1 : ℤ) (by norm_num) cycChk49

theorem cyc50 : (Pi.single (50 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 113] (by decide) (1 : ℤ) (by norm_num) cycChk50

theorem cyc51 : (Pi.single (51 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 114] (by decide) (1 : ℤ) (by norm_num) cycChk51

theorem cyc52 : (Pi.single (52 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [131, 119] (by decide) (-1 : ℤ) (by norm_num) cycChk52

theorem cyc53 : (Pi.single (53 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 116] (by decide) (1 : ℤ) (by norm_num) cycChk53

theorem cyc54 : (Pi.single (54 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 117] (by decide) (1 : ℤ) (by norm_num) cycChk54

theorem cyc55 : (Pi.single (55 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 118] (by decide) (1 : ℤ) (by norm_num) cycChk55

theorem cyc56 : (Pi.single (56 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 119] (by decide) (1 : ℤ) (by norm_num) cycChk56

theorem cyc57 : (Pi.single (57 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 120] (by decide) (1 : ℤ) (by norm_num) cycChk57

theorem cyc58 : (Pi.single (58 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 121] (by decide) (1 : ℤ) (by norm_num) cycChk58

theorem cyc59 : (Pi.single (59 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 122] (by decide) (1 : ℤ) (by norm_num) cycChk59

theorem cyc60 : (Pi.single (60 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 123] (by decide) (1 : ℤ) (by norm_num) cycChk60

theorem cyc61 : (Pi.single (61 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 124] (by decide) (1 : ℤ) (by norm_num) cycChk61

theorem cyc62 : (Pi.single (62 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 125] (by decide) (1 : ℤ) (by norm_num) cycChk62

theorem cyc63 : (Pi.single (63 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 126] (by decide) (1 : ℤ) (by norm_num) cycChk63

theorem cyc64 : (Pi.single (64 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 127] (by decide) (1 : ℤ) (by norm_num) cycChk64

theorem cyc65 : (Pi.single (65 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 128] (by decide) (1 : ℤ) (by norm_num) cycChk65

theorem cyc66 : (Pi.single (66 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 129] (by decide) (1 : ℤ) (by norm_num) cycChk66

theorem cyc67 : (Pi.single (67 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 130] (by decide) (1 : ℤ) (by norm_num) cycChk67

theorem cyc68 : (Pi.single (68 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 131] (by decide) (1 : ℤ) (by norm_num) cycChk68

theorem cyc69 : (Pi.single (69 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [132, 132] (by decide) (2 : ℤ) (by norm_num) cycChk69

theorem cyc70 : (Pi.single (70 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [124, 99] (by decide) (1 : ℤ) (by norm_num) cycChk70

theorem cyc71 : (Pi.single (71 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [126, 93] (by decide) (-1 : ℤ) (by norm_num) cycChk71

theorem cyc72 : (Pi.single (72 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [128, 88] (by decide) (1 : ℤ) (by norm_num) cycChk72

theorem cyc73 : (Pi.single (73 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [129, 82] (by decide) (-1 : ℤ) (by norm_num) cycChk73

theorem cyc74 : (Pi.single (74 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [130, 76] (by decide) (-1 : ℤ) (by norm_num) cycChk74

theorem cyc75 : (Pi.single (75 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [127, 88] (by decide) (1 : ℤ) (by norm_num) cycChk75

theorem cyc76 : (Pi.single (76 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [131] (by decide) (-1 : ℤ) (by norm_num) cycChk76

theorem cyc77 : (Pi.single (77 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [124, 93] (by decide) (-1 : ℤ) (by norm_num) cycChk77

theorem cyc78 : (Pi.single (78 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [126, 88] (by decide) (1 : ℤ) (by norm_num) cycChk78

theorem cyc79 : (Pi.single (79 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [128, 82] (by decide) (-1 : ℤ) (by norm_num) cycChk79

theorem cyc80 : (Pi.single (80 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [129, 76] (by decide) (-1 : ℤ) (by norm_num) cycChk80

theorem cyc81 : (Pi.single (81 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [127, 82] (by decide) (1 : ℤ) (by norm_num) cycChk81

theorem cyc82 : (Pi.single (82 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [130] (by decide) (-1 : ℤ) (by norm_num) cycChk82

theorem cyc83 : (Pi.single (83 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [124, 88] (by decide) (-1 : ℤ) (by norm_num) cycChk83

theorem cyc84 : (Pi.single (84 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [126, 82] (by decide) (1 : ℤ) (by norm_num) cycChk84

theorem cyc85 : (Pi.single (85 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [128, 76] (by decide) (1 : ℤ) (by norm_num) cycChk85

theorem cyc86 : (Pi.single (86 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [125, 82] (by decide) (-1 : ℤ) (by norm_num) cycChk86

theorem cyc87 : (Pi.single (87 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [127, 76] (by decide) (-1 : ℤ) (by norm_num) cycChk87

theorem cyc88 : (Pi.single (88 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [129] (by decide) (1 : ℤ) (by norm_num) cycChk88

theorem cyc89 : (Pi.single (89 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [124, 82] (by decide) (-1 : ℤ) (by norm_num) cycChk89

theorem cyc90 : (Pi.single (90 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [126, 76] (by decide) (-1 : ℤ) (by norm_num) cycChk90

theorem cyc91 : (Pi.single (91 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [123, 82] (by decide) (1 : ℤ) (by norm_num) cycChk91

theorem cyc92 : (Pi.single (92 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [125, 76] (by decide) (1 : ℤ) (by norm_num) cycChk92

theorem cyc93 : (Pi.single (93 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [128] (by decide) (-1 : ℤ) (by norm_num) cycChk93

theorem cyc94 : (Pi.single (94 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [127] (by decide) (1 : ℤ) (by norm_num) cycChk94

theorem cyc95 : (Pi.single (95 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [124, 76] (by decide) (1 : ℤ) (by norm_num) cycChk95

theorem cyc96 : (Pi.single (96 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [121, 82] (by decide) (-1 : ℤ) (by norm_num) cycChk96

theorem cyc97 : (Pi.single (97 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [123, 76] (by decide) (-1 : ℤ) (by norm_num) cycChk97

theorem cyc98 : (Pi.single (98 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [122, 76] (by decide) (-1 : ℤ) (by norm_num) cycChk98

theorem cyc99 : (Pi.single (99 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [126] (by decide) (1 : ℤ) (by norm_num) cycChk99

theorem cyc100 : (Pi.single (100 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [125] (by decide) (-1 : ℤ) (by norm_num) cycChk100

theorem cyc101 : (Pi.single (101 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [121, 76] (by decide) (1 : ℤ) (by norm_num) cycChk101

theorem cyc102 : (Pi.single (102 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [120, 76] (by decide) (1 : ℤ) (by norm_num) cycChk102

theorem cyc103 : (Pi.single (103 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [124] (by decide) (-1 : ℤ) (by norm_num) cycChk103

theorem cyc104 : (Pi.single (104 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [123] (by decide) (1 : ℤ) (by norm_num) cycChk104

theorem cyc105 : (Pi.single (105 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [122] (by decide) (1 : ℤ) (by norm_num) cycChk105

theorem cyc106 : (Pi.single (106 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [118, 76] (by decide) (-1 : ℤ) (by norm_num) cycChk106

theorem cyc107 : (Pi.single (107 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [117, 76] (by decide) (-1 : ℤ) (by norm_num) cycChk107

theorem cyc108 : (Pi.single (108 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [121] (by decide) (-1 : ℤ) (by norm_num) cycChk108

theorem cyc109 : (Pi.single (109 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [120] (by decide) (-1 : ℤ) (by norm_num) cycChk109

theorem cyc110 : (Pi.single (110 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [119] (by decide) (-1 : ℤ) (by norm_num) cycChk110

theorem cyc111 : (Pi.single (111 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [114, 76] (by decide) (1 : ℤ) (by norm_num) cycChk111

theorem cyc112 : (Pi.single (112 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [118] (by decide) (1 : ℤ) (by norm_num) cycChk112

theorem cyc113 : (Pi.single (113 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [117] (by decide) (1 : ℤ) (by norm_num) cycChk113

theorem cyc114 : (Pi.single (114 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [116] (by decide) (1 : ℤ) (by norm_num) cycChk114

theorem cyc115 : (Pi.single (115 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [110, 76] (by decide) (-1 : ℤ) (by norm_num) cycChk115

theorem cyc116 : (Pi.single (116 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [114] (by decide) (-1 : ℤ) (by norm_num) cycChk116

theorem cyc117 : (Pi.single (117 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [113] (by decide) (-1 : ℤ) (by norm_num) cycChk117

theorem cyc118 : (Pi.single (118 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [112] (by decide) (-1 : ℤ) (by norm_num) cycChk118

theorem cyc119 : (Pi.single (119 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [110] (by decide) (1 : ℤ) (by norm_num) cycChk119

theorem cyc120 : (Pi.single (120 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [109] (by decide) (1 : ℤ) (by norm_num) cycChk120

theorem cyc121 : (Pi.single (121 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [108] (by decide) (1 : ℤ) (by norm_num) cycChk121

theorem cyc122 : (Pi.single (122 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [105] (by decide) (-1 : ℤ) (by norm_num) cycChk122

theorem cyc123 : (Pi.single (123 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [104] (by decide) (-1 : ℤ) (by norm_num) cycChk123

theorem cyc124 : (Pi.single (124 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [103] (by decide) (1 : ℤ) (by norm_num) cycChk124

theorem cyc125 : (Pi.single (125 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [100] (by decide) (1 : ℤ) (by norm_num) cycChk125

theorem cyc126 : (Pi.single (126 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [99] (by decide) (-1 : ℤ) (by norm_num) cycChk126

theorem cyc127 : (Pi.single (127 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [94] (by decide) (-1 : ℤ) (by norm_num) cycChk127

theorem cyc128 : (Pi.single (128 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [93] (by decide) (1 : ℤ) (by norm_num) cycChk128

theorem cyc129 : (Pi.single (129 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [88] (by decide) (-1 : ℤ) (by norm_num) cycChk129

theorem cyc130 : (Pi.single (130 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [82] (by decide) (1 : ℤ) (by norm_num) cycChk130

theorem cyc131 : (Pi.single (131 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [76] (by decide) (1 : ℤ) (by norm_num) cycChk131

theorem cyc132 : (Pi.single (132 : Fin 133) 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 :=
  mem_of_word [0] (by decide) (1 : ℤ) (by norm_num) cycChk132

theorem e7_cyclic : ∀ c : Fin 133, (Pi.single c 1 : Fin 133 → ℂ) ∈ slotWords fE7 132 2 := by
  intro c
  fin_cases c
  · exact cyc0
  · exact cyc1
  · exact cyc2
  · exact cyc3
  · exact cyc4
  · exact cyc5
  · exact cyc6
  · exact cyc7
  · exact cyc8
  · exact cyc9
  · exact cyc10
  · exact cyc11
  · exact cyc12
  · exact cyc13
  · exact cyc14
  · exact cyc15
  · exact cyc16
  · exact cyc17
  · exact cyc18
  · exact cyc19
  · exact cyc20
  · exact cyc21
  · exact cyc22
  · exact cyc23
  · exact cyc24
  · exact cyc25
  · exact cyc26
  · exact cyc27
  · exact cyc28
  · exact cyc29
  · exact cyc30
  · exact cyc31
  · exact cyc32
  · exact cyc33
  · exact cyc34
  · exact cyc35
  · exact cyc36
  · exact cyc37
  · exact cyc38
  · exact cyc39
  · exact cyc40
  · exact cyc41
  · exact cyc42
  · exact cyc43
  · exact cyc44
  · exact cyc45
  · exact cyc46
  · exact cyc47
  · exact cyc48
  · exact cyc49
  · exact cyc50
  · exact cyc51
  · exact cyc52
  · exact cyc53
  · exact cyc54
  · exact cyc55
  · exact cyc56
  · exact cyc57
  · exact cyc58
  · exact cyc59
  · exact cyc60
  · exact cyc61
  · exact cyc62
  · exact cyc63
  · exact cyc64
  · exact cyc65
  · exact cyc66
  · exact cyc67
  · exact cyc68
  · exact cyc69
  · exact cyc70
  · exact cyc71
  · exact cyc72
  · exact cyc73
  · exact cyc74
  · exact cyc75
  · exact cyc76
  · exact cyc77
  · exact cyc78
  · exact cyc79
  · exact cyc80
  · exact cyc81
  · exact cyc82
  · exact cyc83
  · exact cyc84
  · exact cyc85
  · exact cyc86
  · exact cyc87
  · exact cyc88
  · exact cyc89
  · exact cyc90
  · exact cyc91
  · exact cyc92
  · exact cyc93
  · exact cyc94
  · exact cyc95
  · exact cyc96
  · exact cyc97
  · exact cyc98
  · exact cyc99
  · exact cyc100
  · exact cyc101
  · exact cyc102
  · exact cyc103
  · exact cyc104
  · exact cyc105
  · exact cyc106
  · exact cyc107
  · exact cyc108
  · exact cyc109
  · exact cyc110
  · exact cyc111
  · exact cyc112
  · exact cyc113
  · exact cyc114
  · exact cyc115
  · exact cyc116
  · exact cyc117
  · exact cyc118
  · exact cyc119
  · exact cyc120
  · exact cyc121
  · exact cyc122
  · exact cyc123
  · exact cyc124
  · exact cyc125
  · exact cyc126
  · exact cyc127
  · exact cyc128
  · exact cyc129
  · exact cyc130
  · exact cyc131
  · exact cyc132

end

end VOA.DeligneAudit.DeligneCarrier.E7
