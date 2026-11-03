/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorWeyl
import VOA.DeligneAudit.E8SectorCycChkA
import VOA.DeligneAudit.E8SectorCycChkB
import VOA.DeligneAudit.E8SectorCycChkC
import VOA.DeligneAudit.E8SectorCycChkD
import VOA.DeligneAudit.E8SectorCycChkE
import VOA.DeligneAudit.E8SectorCycChkF

/-!
# `E₈` sector data: coadjoint cyclicity (depth 2 from `δ_{247}`)

Port of the `E7SectorCyclic`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E8

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6SectorSparse
open VOA.AffineGeneral.SCLie VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.DeligneSector

noncomputable section

set_option linter.style.longLine false

theorem wordA_single (l : List (Fin 248)) :
    wordA fE8 l (Pi.single (247 : Fin 248) 1) = vecC 248 (wordS e8T 248 (l.map Fin.val) [(247, 1)]) := by
  rw [single_eq_vecC]
  exact wordA_vecC l _ (by simp)

theorem map_ofNat_val (l : List ℕ) (hl : l.all (fun x => decide (x < 248)) = true) :
    (l.map (Fin.ofNat 248)).map Fin.val = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro x hx
  have := List.all_eq_true.mp hl x hx
  simp only [decide_eq_true_eq] at this
  simp [Fin.ofNat, Nat.mod_eq_of_lt this]

theorem word_mem (l : List ℕ) (hl : l.all (fun x => decide (x < 248)) = true) (hlen : l.length ≤ 2) :
    vecC 248 (wordS e8T 248 l [(247, 1)]) ∈ slotWords fE8 247 2 := by
  have h := wordA_single (l.map (Fin.ofNat 248))
  rw [map_ofNat_val l hl] at h
  rw [← h]
  exact Submodule.subset_span ⟨_, by simpa using hlen, rfl⟩

theorem mem_of_word (l : List ℕ) (hl : l.all (fun x => decide (x < 248)) = true ∧ l.length ≤ 2)
    {c : Fin 248} (lam : ℤ) (hlam : lam ≠ 0)
    (h : zeroL (wordS e8T 248 l [(247, 1)] ++ scale (-lam) [((c : ℕ), 1)]) = true) :
    (Pi.single c 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 := by
  have hw := word_mem l hl.1 hl.2
  rw [vecC_eq_of_zeroL lam h, ← single_eq_vecC] at hw
  have := Submodule.smul_mem _ ((lam : ℂ)⁻¹) hw
  rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hlam), one_smul] at this

theorem combo_mem (ws : List (List ℕ × ℤ))
    (hws : ws.all (fun w => w.1.all (fun x => decide (x < 248)) && decide (w.1.length ≤ 2)) = true) :
    vecC 248 (ws.flatMap (fun w => scale w.2 (wordS e8T 248 w.1 [(247, 1)]))) ∈ slotWords fE8 247 2 := by
  induction ws with
  | nil =>
    have : vecC 248 ([] : List (ℕ × ℤ)) = 0 := by funext k; simp [vecC, coef]
    simp only [List.flatMap_nil, this]
    exact Submodule.zero_mem _
  | cons w ws ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hws
    rw [List.flatMap_cons, vecC_append, vecC_scale]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (word_mem w.1 hws.1.1 hws.1.2)) (ih hws.2)

theorem mem_of_combo (ws : List (List ℕ × ℤ))
    (hws : ws.all (fun w => w.1.all (fun x => decide (x < 248)) && decide (w.1.length ≤ 2)) = true)
    {c : Fin 248} (D : ℤ) (hD : D ≠ 0)
    (h : zeroL (ws.flatMap (fun w => scale w.2 (wordS e8T 248 w.1 [(247, 1)])) ++
      scale (-D) [((c : ℕ), 1)]) = true) :
    (Pi.single c 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 := by
  have hsum := combo_mem ws hws
  rw [vecC_eq_of_zeroL D h, ← single_eq_vecC] at hsum
  have := Submodule.smul_mem _ ((D : ℂ)⁻¹) hsum
  rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hD), one_smul] at this

theorem cyc0 : (Pi.single (0 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_combo [([241, 164], (-1 : ℤ)), ([240, 165], (1 : ℤ))] (by decide) (1 : ℤ) (by norm_num) cycChk0

theorem cyc1 : (Pi.single (1 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_combo [([242, 157], (-1 : ℤ)), ([243, 150], (1 : ℤ)), ([244, 143], (-1 : ℤ)), ([245, 136], (1 : ℤ)), ([246, 128], (1 : ℤ)), ([247, 7], (-1 : ℤ)), ([240, 165], (-1 : ℤ))] (by decide) (2 : ℤ) (by norm_num) cycChk1

theorem cyc2 : (Pi.single (2 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_combo [([240, 165], (1 : ℤ)), ([242, 157], (-1 : ℤ)), ([243, 150], (1 : ℤ)), ([244, 143], (-1 : ℤ)), ([245, 136], (1 : ℤ)), ([246, 128], (1 : ℤ)), ([247, 7], (-1 : ℤ))] (by decide) (2 : ℤ) (by norm_num) cycChk2

theorem cyc3 : (Pi.single (3 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_combo [([243, 150], (1 : ℤ)), ([244, 143], (-1 : ℤ)), ([245, 136], (1 : ℤ)), ([246, 128], (1 : ℤ)), ([247, 7], (-1 : ℤ))] (by decide) (1 : ℤ) (by norm_num) cycChk3

theorem cyc4 : (Pi.single (4 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_combo [([244, 143], (-1 : ℤ)), ([245, 136], (1 : ℤ)), ([246, 128], (1 : ℤ)), ([247, 7], (-1 : ℤ))] (by decide) (1 : ℤ) (by norm_num) cycChk4

theorem cyc5 : (Pi.single (5 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_combo [([245, 136], (1 : ℤ)), ([246, 128], (1 : ℤ)), ([247, 7], (-1 : ℤ))] (by decide) (1 : ℤ) (by norm_num) cycChk5

theorem cyc6 : (Pi.single (6 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_combo [([246, 128], (1 : ℤ)), ([247, 7], (-1 : ℤ))] (by decide) (1 : ℤ) (by norm_num) cycChk6

theorem cyc7 : (Pi.single (7 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247] (by decide) (-1 : ℤ) (by norm_num) cycChk7

theorem cyc8 : (Pi.single (8 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk8

theorem cyc9 : (Pi.single (9 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 136] (by decide) (-1 : ℤ) (by norm_num) cycChk9

theorem cyc10 : (Pi.single (10 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245, 143] (by decide) (1 : ℤ) (by norm_num) cycChk10

theorem cyc11 : (Pi.single (11 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [244, 150] (by decide) (-1 : ℤ) (by norm_num) cycChk11

theorem cyc12 : (Pi.single (12 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [243, 157] (by decide) (1 : ℤ) (by norm_num) cycChk12

theorem cyc13 : (Pi.single (13 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [242, 164] (by decide) (-1 : ℤ) (by norm_num) cycChk13

theorem cyc14 : (Pi.single (14 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [242, 165] (by decide) (-1 : ℤ) (by norm_num) cycChk14

theorem cyc15 : (Pi.single (15 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [241, 174] (by decide) (-1 : ℤ) (by norm_num) cycChk15

theorem cyc16 : (Pi.single (16 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 136] (by decide) (1 : ℤ) (by norm_num) cycChk16

theorem cyc17 : (Pi.single (17 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 143] (by decide) (-1 : ℤ) (by norm_num) cycChk17

theorem cyc18 : (Pi.single (18 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245, 150] (by decide) (1 : ℤ) (by norm_num) cycChk18

theorem cyc19 : (Pi.single (19 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [244, 157] (by decide) (-1 : ℤ) (by norm_num) cycChk19

theorem cyc20 : (Pi.single (20 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [243, 164] (by decide) (1 : ℤ) (by norm_num) cycChk20

theorem cyc21 : (Pi.single (21 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [243, 165] (by decide) (1 : ℤ) (by norm_num) cycChk21

theorem cyc22 : (Pi.single (22 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [242, 174] (by decide) (-1 : ℤ) (by norm_num) cycChk22

theorem cyc23 : (Pi.single (23 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 143] (by decide) (1 : ℤ) (by norm_num) cycChk23

theorem cyc24 : (Pi.single (24 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 150] (by decide) (-1 : ℤ) (by norm_num) cycChk24

theorem cyc25 : (Pi.single (25 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245, 157] (by decide) (1 : ℤ) (by norm_num) cycChk25

theorem cyc26 : (Pi.single (26 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [244, 164] (by decide) (-1 : ℤ) (by norm_num) cycChk26

theorem cyc27 : (Pi.single (27 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [244, 165] (by decide) (-1 : ℤ) (by norm_num) cycChk27

theorem cyc28 : (Pi.single (28 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [243, 171] (by decide) (1 : ℤ) (by norm_num) cycChk28

theorem cyc29 : (Pi.single (29 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [243, 174] (by decide) (1 : ℤ) (by norm_num) cycChk29

theorem cyc30 : (Pi.single (30 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 150] (by decide) (1 : ℤ) (by norm_num) cycChk30

theorem cyc31 : (Pi.single (31 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 157] (by decide) (-1 : ℤ) (by norm_num) cycChk31

theorem cyc32 : (Pi.single (32 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245, 164] (by decide) (1 : ℤ) (by norm_num) cycChk32

theorem cyc33 : (Pi.single (33 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245, 165] (by decide) (1 : ℤ) (by norm_num) cycChk33

theorem cyc34 : (Pi.single (34 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [244, 171] (by decide) (-1 : ℤ) (by norm_num) cycChk34

theorem cyc35 : (Pi.single (35 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [244, 174] (by decide) (-1 : ℤ) (by norm_num) cycChk35

theorem cyc36 : (Pi.single (36 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [243, 180] (by decide) (1 : ℤ) (by norm_num) cycChk36

theorem cyc37 : (Pi.single (37 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 157] (by decide) (1 : ℤ) (by norm_num) cycChk37

theorem cyc38 : (Pi.single (38 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 164] (by decide) (-1 : ℤ) (by norm_num) cycChk38

theorem cyc39 : (Pi.single (39 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 165] (by decide) (-1 : ℤ) (by norm_num) cycChk39

theorem cyc40 : (Pi.single (40 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245, 171] (by decide) (1 : ℤ) (by norm_num) cycChk40

theorem cyc41 : (Pi.single (41 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [244, 178] (by decide) (-1 : ℤ) (by norm_num) cycChk41

theorem cyc42 : (Pi.single (42 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245, 174] (by decide) (1 : ℤ) (by norm_num) cycChk42

theorem cyc43 : (Pi.single (43 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [244, 180] (by decide) (-1 : ℤ) (by norm_num) cycChk43

theorem cyc44 : (Pi.single (44 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 164] (by decide) (1 : ℤ) (by norm_num) cycChk44

theorem cyc45 : (Pi.single (45 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 165] (by decide) (1 : ℤ) (by norm_num) cycChk45

theorem cyc46 : (Pi.single (46 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 171] (by decide) (-1 : ℤ) (by norm_num) cycChk46

theorem cyc47 : (Pi.single (47 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245, 178] (by decide) (1 : ℤ) (by norm_num) cycChk47

theorem cyc48 : (Pi.single (48 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 174] (by decide) (-1 : ℤ) (by norm_num) cycChk48

theorem cyc49 : (Pi.single (49 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245, 180] (by decide) (1 : ℤ) (by norm_num) cycChk49

theorem cyc50 : (Pi.single (50 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [244, 186] (by decide) (-1 : ℤ) (by norm_num) cycChk50

theorem cyc51 : (Pi.single (51 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 171] (by decide) (1 : ℤ) (by norm_num) cycChk51

theorem cyc52 : (Pi.single (52 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 178] (by decide) (-1 : ℤ) (by norm_num) cycChk52

theorem cyc53 : (Pi.single (53 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245, 184] (by decide) (1 : ℤ) (by norm_num) cycChk53

theorem cyc54 : (Pi.single (54 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 174] (by decide) (1 : ℤ) (by norm_num) cycChk54

theorem cyc55 : (Pi.single (55 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 180] (by decide) (-1 : ℤ) (by norm_num) cycChk55

theorem cyc56 : (Pi.single (56 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245, 186] (by decide) (1 : ℤ) (by norm_num) cycChk56

theorem cyc57 : (Pi.single (57 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [244, 193] (by decide) (-1 : ℤ) (by norm_num) cycChk57

theorem cyc58 : (Pi.single (58 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 178] (by decide) (1 : ℤ) (by norm_num) cycChk58

theorem cyc59 : (Pi.single (59 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 184] (by decide) (-1 : ℤ) (by norm_num) cycChk59

theorem cyc60 : (Pi.single (60 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 180] (by decide) (1 : ℤ) (by norm_num) cycChk60

theorem cyc61 : (Pi.single (61 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 186] (by decide) (-1 : ℤ) (by norm_num) cycChk61

theorem cyc62 : (Pi.single (62 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245, 191] (by decide) (1 : ℤ) (by norm_num) cycChk62

theorem cyc63 : (Pi.single (63 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245, 193] (by decide) (1 : ℤ) (by norm_num) cycChk63

theorem cyc64 : (Pi.single (64 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 184] (by decide) (1 : ℤ) (by norm_num) cycChk64

theorem cyc65 : (Pi.single (65 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 190] (by decide) (-1 : ℤ) (by norm_num) cycChk65

theorem cyc66 : (Pi.single (66 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 186] (by decide) (1 : ℤ) (by norm_num) cycChk66

theorem cyc67 : (Pi.single (67 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 191] (by decide) (-1 : ℤ) (by norm_num) cycChk67

theorem cyc68 : (Pi.single (68 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 193] (by decide) (-1 : ℤ) (by norm_num) cycChk68

theorem cyc69 : (Pi.single (69 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245, 198] (by decide) (1 : ℤ) (by norm_num) cycChk69

theorem cyc70 : (Pi.single (70 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 190] (by decide) (1 : ℤ) (by norm_num) cycChk70

theorem cyc71 : (Pi.single (71 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 191] (by decide) (1 : ℤ) (by norm_num) cycChk71

theorem cyc72 : (Pi.single (72 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 197] (by decide) (-1 : ℤ) (by norm_num) cycChk72

theorem cyc73 : (Pi.single (73 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 193] (by decide) (1 : ℤ) (by norm_num) cycChk73

theorem cyc74 : (Pi.single (74 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 198] (by decide) (-1 : ℤ) (by norm_num) cycChk74

theorem cyc75 : (Pi.single (75 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245, 204] (by decide) (1 : ℤ) (by norm_num) cycChk75

theorem cyc76 : (Pi.single (76 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 196] (by decide) (1 : ℤ) (by norm_num) cycChk76

theorem cyc77 : (Pi.single (77 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 197] (by decide) (1 : ℤ) (by norm_num) cycChk77

theorem cyc78 : (Pi.single (78 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 198] (by decide) (1 : ℤ) (by norm_num) cycChk78

theorem cyc79 : (Pi.single (79 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 203] (by decide) (-1 : ℤ) (by norm_num) cycChk79

theorem cyc80 : (Pi.single (80 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 204] (by decide) (-1 : ℤ) (by norm_num) cycChk80

theorem cyc81 : (Pi.single (81 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245, 210] (by decide) (1 : ℤ) (by norm_num) cycChk81

theorem cyc82 : (Pi.single (82 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 202] (by decide) (1 : ℤ) (by norm_num) cycChk82

theorem cyc83 : (Pi.single (83 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 203] (by decide) (1 : ℤ) (by norm_num) cycChk83

theorem cyc84 : (Pi.single (84 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 204] (by decide) (1 : ℤ) (by norm_num) cycChk84

theorem cyc85 : (Pi.single (85 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 208] (by decide) (-1 : ℤ) (by norm_num) cycChk85

theorem cyc86 : (Pi.single (86 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 210] (by decide) (-1 : ℤ) (by norm_num) cycChk86

theorem cyc87 : (Pi.single (87 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 207] (by decide) (1 : ℤ) (by norm_num) cycChk87

theorem cyc88 : (Pi.single (88 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 208] (by decide) (1 : ℤ) (by norm_num) cycChk88

theorem cyc89 : (Pi.single (89 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 213] (by decide) (-1 : ℤ) (by norm_num) cycChk89

theorem cyc90 : (Pi.single (90 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 210] (by decide) (1 : ℤ) (by norm_num) cycChk90

theorem cyc91 : (Pi.single (91 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 214] (by decide) (-1 : ℤ) (by norm_num) cycChk91

theorem cyc92 : (Pi.single (92 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 212] (by decide) (1 : ℤ) (by norm_num) cycChk92

theorem cyc93 : (Pi.single (93 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 213] (by decide) (1 : ℤ) (by norm_num) cycChk93

theorem cyc94 : (Pi.single (94 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 214] (by decide) (1 : ℤ) (by norm_num) cycChk94

theorem cyc95 : (Pi.single (95 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 218] (by decide) (-1 : ℤ) (by norm_num) cycChk95

theorem cyc96 : (Pi.single (96 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 216] (by decide) (1 : ℤ) (by norm_num) cycChk96

theorem cyc97 : (Pi.single (97 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 217] (by decide) (1 : ℤ) (by norm_num) cycChk97

theorem cyc98 : (Pi.single (98 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 218] (by decide) (1 : ℤ) (by norm_num) cycChk98

theorem cyc99 : (Pi.single (99 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 222] (by decide) (-1 : ℤ) (by norm_num) cycChk99

theorem cyc100 : (Pi.single (100 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 220] (by decide) (1 : ℤ) (by norm_num) cycChk100

theorem cyc101 : (Pi.single (101 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 221] (by decide) (1 : ℤ) (by norm_num) cycChk101

theorem cyc102 : (Pi.single (102 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 222] (by decide) (1 : ℤ) (by norm_num) cycChk102

theorem cyc103 : (Pi.single (103 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 226] (by decide) (-1 : ℤ) (by norm_num) cycChk103

theorem cyc104 : (Pi.single (104 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 224] (by decide) (1 : ℤ) (by norm_num) cycChk104

theorem cyc105 : (Pi.single (105 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 225] (by decide) (1 : ℤ) (by norm_num) cycChk105

theorem cyc106 : (Pi.single (106 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 226] (by decide) (1 : ℤ) (by norm_num) cycChk106

theorem cyc107 : (Pi.single (107 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246, 230] (by decide) (-1 : ℤ) (by norm_num) cycChk107

theorem cyc108 : (Pi.single (108 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 228] (by decide) (1 : ℤ) (by norm_num) cycChk108

theorem cyc109 : (Pi.single (109 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 229] (by decide) (1 : ℤ) (by norm_num) cycChk109

theorem cyc110 : (Pi.single (110 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 230] (by decide) (1 : ℤ) (by norm_num) cycChk110

theorem cyc111 : (Pi.single (111 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 231] (by decide) (1 : ℤ) (by norm_num) cycChk111

theorem cyc112 : (Pi.single (112 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 232] (by decide) (1 : ℤ) (by norm_num) cycChk112

theorem cyc113 : (Pi.single (113 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 233] (by decide) (1 : ℤ) (by norm_num) cycChk113

theorem cyc114 : (Pi.single (114 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 234] (by decide) (1 : ℤ) (by norm_num) cycChk114

theorem cyc115 : (Pi.single (115 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 235] (by decide) (1 : ℤ) (by norm_num) cycChk115

theorem cyc116 : (Pi.single (116 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 236] (by decide) (1 : ℤ) (by norm_num) cycChk116

theorem cyc117 : (Pi.single (117 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 237] (by decide) (1 : ℤ) (by norm_num) cycChk117

theorem cyc118 : (Pi.single (118 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 238] (by decide) (1 : ℤ) (by norm_num) cycChk118

theorem cyc119 : (Pi.single (119 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 239] (by decide) (1 : ℤ) (by norm_num) cycChk119

theorem cyc120 : (Pi.single (120 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 240] (by decide) (1 : ℤ) (by norm_num) cycChk120

theorem cyc121 : (Pi.single (121 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 241] (by decide) (1 : ℤ) (by norm_num) cycChk121

theorem cyc122 : (Pi.single (122 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 242] (by decide) (1 : ℤ) (by norm_num) cycChk122

theorem cyc123 : (Pi.single (123 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 243] (by decide) (1 : ℤ) (by norm_num) cycChk123

theorem cyc124 : (Pi.single (124 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 244] (by decide) (1 : ℤ) (by norm_num) cycChk124

theorem cyc125 : (Pi.single (125 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 245] (by decide) (1 : ℤ) (by norm_num) cycChk125

theorem cyc126 : (Pi.single (126 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 246] (by decide) (1 : ℤ) (by norm_num) cycChk126

theorem cyc127 : (Pi.single (127 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [247, 247] (by decide) (2 : ℤ) (by norm_num) cycChk127

theorem cyc128 : (Pi.single (128 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [246] (by decide) (1 : ℤ) (by norm_num) cycChk128

theorem cyc129 : (Pi.single (129 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk129

theorem cyc130 : (Pi.single (130 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [244, 136] (by decide) (-1 : ℤ) (by norm_num) cycChk130

theorem cyc131 : (Pi.single (131 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [243, 143] (by decide) (1 : ℤ) (by norm_num) cycChk131

theorem cyc132 : (Pi.single (132 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [242, 150] (by decide) (-1 : ℤ) (by norm_num) cycChk132

theorem cyc133 : (Pi.single (133 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [241, 157] (by decide) (-1 : ℤ) (by norm_num) cycChk133

theorem cyc134 : (Pi.single (134 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [240, 157] (by decide) (1 : ℤ) (by norm_num) cycChk134

theorem cyc135 : (Pi.single (135 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [238, 164] (by decide) (-1 : ℤ) (by norm_num) cycChk135

theorem cyc136 : (Pi.single (136 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [245] (by decide) (1 : ℤ) (by norm_num) cycChk136

theorem cyc137 : (Pi.single (137 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [244, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk137

theorem cyc138 : (Pi.single (138 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [243, 136] (by decide) (-1 : ℤ) (by norm_num) cycChk138

theorem cyc139 : (Pi.single (139 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [242, 143] (by decide) (1 : ℤ) (by norm_num) cycChk139

theorem cyc140 : (Pi.single (140 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [241, 150] (by decide) (1 : ℤ) (by norm_num) cycChk140

theorem cyc141 : (Pi.single (141 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [240, 150] (by decide) (-1 : ℤ) (by norm_num) cycChk141

theorem cyc142 : (Pi.single (142 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [238, 157] (by decide) (1 : ℤ) (by norm_num) cycChk142

theorem cyc143 : (Pi.single (143 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [244] (by decide) (-1 : ℤ) (by norm_num) cycChk143

theorem cyc144 : (Pi.single (144 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [243, 128] (by decide) (1 : ℤ) (by norm_num) cycChk144

theorem cyc145 : (Pi.single (145 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [242, 136] (by decide) (1 : ℤ) (by norm_num) cycChk145

theorem cyc146 : (Pi.single (146 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [241, 143] (by decide) (1 : ℤ) (by norm_num) cycChk146

theorem cyc147 : (Pi.single (147 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [240, 143] (by decide) (-1 : ℤ) (by norm_num) cycChk147

theorem cyc148 : (Pi.single (148 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [239, 150] (by decide) (-1 : ℤ) (by norm_num) cycChk148

theorem cyc149 : (Pi.single (149 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [238, 150] (by decide) (1 : ℤ) (by norm_num) cycChk149

theorem cyc150 : (Pi.single (150 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [243] (by decide) (1 : ℤ) (by norm_num) cycChk150

theorem cyc151 : (Pi.single (151 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [242, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk151

theorem cyc152 : (Pi.single (152 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [241, 136] (by decide) (1 : ℤ) (by norm_num) cycChk152

theorem cyc153 : (Pi.single (153 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [240, 136] (by decide) (-1 : ℤ) (by norm_num) cycChk153

theorem cyc154 : (Pi.single (154 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [239, 143] (by decide) (-1 : ℤ) (by norm_num) cycChk154

theorem cyc155 : (Pi.single (155 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [238, 143] (by decide) (1 : ℤ) (by norm_num) cycChk155

theorem cyc156 : (Pi.single (156 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [236, 150] (by decide) (-1 : ℤ) (by norm_num) cycChk156

theorem cyc157 : (Pi.single (157 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [242] (by decide) (-1 : ℤ) (by norm_num) cycChk157

theorem cyc158 : (Pi.single (158 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [241, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk158

theorem cyc159 : (Pi.single (159 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [240, 128] (by decide) (1 : ℤ) (by norm_num) cycChk159

theorem cyc160 : (Pi.single (160 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [239, 136] (by decide) (-1 : ℤ) (by norm_num) cycChk160

theorem cyc161 : (Pi.single (161 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [237, 143] (by decide) (1 : ℤ) (by norm_num) cycChk161

theorem cyc162 : (Pi.single (162 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [238, 136] (by decide) (1 : ℤ) (by norm_num) cycChk162

theorem cyc163 : (Pi.single (163 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [236, 143] (by decide) (-1 : ℤ) (by norm_num) cycChk163

theorem cyc164 : (Pi.single (164 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [241] (by decide) (-1 : ℤ) (by norm_num) cycChk164

theorem cyc165 : (Pi.single (165 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [240] (by decide) (1 : ℤ) (by norm_num) cycChk165

theorem cyc166 : (Pi.single (166 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [239, 128] (by decide) (1 : ℤ) (by norm_num) cycChk166

theorem cyc167 : (Pi.single (167 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [237, 136] (by decide) (1 : ℤ) (by norm_num) cycChk167

theorem cyc168 : (Pi.single (168 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [238, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk168

theorem cyc169 : (Pi.single (169 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [236, 136] (by decide) (-1 : ℤ) (by norm_num) cycChk169

theorem cyc170 : (Pi.single (170 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [234, 143] (by decide) (1 : ℤ) (by norm_num) cycChk170

theorem cyc171 : (Pi.single (171 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [239] (by decide) (1 : ℤ) (by norm_num) cycChk171

theorem cyc172 : (Pi.single (172 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [237, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk172

theorem cyc173 : (Pi.single (173 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [235, 136] (by decide) (-1 : ℤ) (by norm_num) cycChk173

theorem cyc174 : (Pi.single (174 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [238] (by decide) (-1 : ℤ) (by norm_num) cycChk174

theorem cyc175 : (Pi.single (175 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [236, 128] (by decide) (1 : ℤ) (by norm_num) cycChk175

theorem cyc176 : (Pi.single (176 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [234, 136] (by decide) (1 : ℤ) (by norm_num) cycChk176

theorem cyc177 : (Pi.single (177 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [231, 143] (by decide) (1 : ℤ) (by norm_num) cycChk177

theorem cyc178 : (Pi.single (178 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [237] (by decide) (-1 : ℤ) (by norm_num) cycChk178

theorem cyc179 : (Pi.single (179 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [235, 128] (by decide) (1 : ℤ) (by norm_num) cycChk179

theorem cyc180 : (Pi.single (180 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [236] (by decide) (1 : ℤ) (by norm_num) cycChk180

theorem cyc181 : (Pi.single (181 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [234, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk181

theorem cyc182 : (Pi.single (182 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [232, 136] (by decide) (-1 : ℤ) (by norm_num) cycChk182

theorem cyc183 : (Pi.single (183 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [231, 136] (by decide) (1 : ℤ) (by norm_num) cycChk183

theorem cyc184 : (Pi.single (184 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [235] (by decide) (1 : ℤ) (by norm_num) cycChk184

theorem cyc185 : (Pi.single (185 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [233, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk185

theorem cyc186 : (Pi.single (186 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [234] (by decide) (-1 : ℤ) (by norm_num) cycChk186

theorem cyc187 : (Pi.single (187 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [232, 128] (by decide) (1 : ℤ) (by norm_num) cycChk187

theorem cyc188 : (Pi.single (188 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [231, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk188

theorem cyc189 : (Pi.single (189 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [228, 136] (by decide) (-1 : ℤ) (by norm_num) cycChk189

theorem cyc190 : (Pi.single (190 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [233] (by decide) (-1 : ℤ) (by norm_num) cycChk190

theorem cyc191 : (Pi.single (191 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [232] (by decide) (1 : ℤ) (by norm_num) cycChk191

theorem cyc192 : (Pi.single (192 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [229, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk192

theorem cyc193 : (Pi.single (193 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [231] (by decide) (-1 : ℤ) (by norm_num) cycChk193

theorem cyc194 : (Pi.single (194 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [228, 128] (by decide) (1 : ℤ) (by norm_num) cycChk194

theorem cyc195 : (Pi.single (195 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [224, 136] (by decide) (1 : ℤ) (by norm_num) cycChk195

theorem cyc196 : (Pi.single (196 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [230] (by decide) (1 : ℤ) (by norm_num) cycChk196

theorem cyc197 : (Pi.single (197 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [229] (by decide) (-1 : ℤ) (by norm_num) cycChk197

theorem cyc198 : (Pi.single (198 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [228] (by decide) (1 : ℤ) (by norm_num) cycChk198

theorem cyc199 : (Pi.single (199 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [225, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk199

theorem cyc200 : (Pi.single (200 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [224, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk200

theorem cyc201 : (Pi.single (201 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [220, 136] (by decide) (-1 : ℤ) (by norm_num) cycChk201

theorem cyc202 : (Pi.single (202 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [226] (by decide) (1 : ℤ) (by norm_num) cycChk202

theorem cyc203 : (Pi.single (203 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [225] (by decide) (-1 : ℤ) (by norm_num) cycChk203

theorem cyc204 : (Pi.single (204 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [224] (by decide) (-1 : ℤ) (by norm_num) cycChk204

theorem cyc205 : (Pi.single (205 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [221, 128] (by decide) (1 : ℤ) (by norm_num) cycChk205

theorem cyc206 : (Pi.single (206 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [220, 128] (by decide) (1 : ℤ) (by norm_num) cycChk206

theorem cyc207 : (Pi.single (207 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [222] (by decide) (1 : ℤ) (by norm_num) cycChk207

theorem cyc208 : (Pi.single (208 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [221] (by decide) (1 : ℤ) (by norm_num) cycChk208

theorem cyc209 : (Pi.single (209 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [217, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk209

theorem cyc210 : (Pi.single (210 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [220] (by decide) (1 : ℤ) (by norm_num) cycChk210

theorem cyc211 : (Pi.single (211 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [216, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk211

theorem cyc212 : (Pi.single (212 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [218] (by decide) (-1 : ℤ) (by norm_num) cycChk212

theorem cyc213 : (Pi.single (213 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [217] (by decide) (-1 : ℤ) (by norm_num) cycChk213

theorem cyc214 : (Pi.single (214 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [216] (by decide) (-1 : ℤ) (by norm_num) cycChk214

theorem cyc215 : (Pi.single (215 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [212, 128] (by decide) (1 : ℤ) (by norm_num) cycChk215

theorem cyc216 : (Pi.single (216 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [214] (by decide) (1 : ℤ) (by norm_num) cycChk216

theorem cyc217 : (Pi.single (217 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [213] (by decide) (1 : ℤ) (by norm_num) cycChk217

theorem cyc218 : (Pi.single (218 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [212] (by decide) (1 : ℤ) (by norm_num) cycChk218

theorem cyc219 : (Pi.single (219 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [207, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk219

theorem cyc220 : (Pi.single (220 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [210] (by decide) (-1 : ℤ) (by norm_num) cycChk220

theorem cyc221 : (Pi.single (221 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [208] (by decide) (-1 : ℤ) (by norm_num) cycChk221

theorem cyc222 : (Pi.single (222 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [207] (by decide) (-1 : ℤ) (by norm_num) cycChk222

theorem cyc223 : (Pi.single (223 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [202, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk223

theorem cyc224 : (Pi.single (224 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [204] (by decide) (1 : ℤ) (by norm_num) cycChk224

theorem cyc225 : (Pi.single (225 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [203] (by decide) (1 : ℤ) (by norm_num) cycChk225

theorem cyc226 : (Pi.single (226 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [202] (by decide) (-1 : ℤ) (by norm_num) cycChk226

theorem cyc227 : (Pi.single (227 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [196, 128] (by decide) (-1 : ℤ) (by norm_num) cycChk227

theorem cyc228 : (Pi.single (228 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [198] (by decide) (-1 : ℤ) (by norm_num) cycChk228

theorem cyc229 : (Pi.single (229 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [197] (by decide) (1 : ℤ) (by norm_num) cycChk229

theorem cyc230 : (Pi.single (230 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [196] (by decide) (-1 : ℤ) (by norm_num) cycChk230

theorem cyc231 : (Pi.single (231 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [193] (by decide) (1 : ℤ) (by norm_num) cycChk231

theorem cyc232 : (Pi.single (232 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [191] (by decide) (-1 : ℤ) (by norm_num) cycChk232

theorem cyc233 : (Pi.single (233 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [190] (by decide) (1 : ℤ) (by norm_num) cycChk233

theorem cyc234 : (Pi.single (234 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [186] (by decide) (1 : ℤ) (by norm_num) cycChk234

theorem cyc235 : (Pi.single (235 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [184] (by decide) (-1 : ℤ) (by norm_num) cycChk235

theorem cyc236 : (Pi.single (236 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [180] (by decide) (-1 : ℤ) (by norm_num) cycChk236

theorem cyc237 : (Pi.single (237 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [178] (by decide) (1 : ℤ) (by norm_num) cycChk237

theorem cyc238 : (Pi.single (238 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [174] (by decide) (1 : ℤ) (by norm_num) cycChk238

theorem cyc239 : (Pi.single (239 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [171] (by decide) (-1 : ℤ) (by norm_num) cycChk239

theorem cyc240 : (Pi.single (240 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [165] (by decide) (-1 : ℤ) (by norm_num) cycChk240

theorem cyc241 : (Pi.single (241 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [164] (by decide) (1 : ℤ) (by norm_num) cycChk241

theorem cyc242 : (Pi.single (242 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [157] (by decide) (1 : ℤ) (by norm_num) cycChk242

theorem cyc243 : (Pi.single (243 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [150] (by decide) (-1 : ℤ) (by norm_num) cycChk243

theorem cyc244 : (Pi.single (244 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [143] (by decide) (1 : ℤ) (by norm_num) cycChk244

theorem cyc245 : (Pi.single (245 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [136] (by decide) (-1 : ℤ) (by norm_num) cycChk245

theorem cyc246 : (Pi.single (246 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [128] (by decide) (-1 : ℤ) (by norm_num) cycChk246

theorem cyc247 : (Pi.single (247 : Fin 248) 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 :=
  mem_of_word [7] (by decide) (1 : ℤ) (by norm_num) cycChk247

theorem e8_cyclic : ∀ c : Fin 248, (Pi.single c 1 : Fin 248 → ℂ) ∈ slotWords fE8 247 2 := by
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
  · exact cyc133
  · exact cyc134
  · exact cyc135
  · exact cyc136
  · exact cyc137
  · exact cyc138
  · exact cyc139
  · exact cyc140
  · exact cyc141
  · exact cyc142
  · exact cyc143
  · exact cyc144
  · exact cyc145
  · exact cyc146
  · exact cyc147
  · exact cyc148
  · exact cyc149
  · exact cyc150
  · exact cyc151
  · exact cyc152
  · exact cyc153
  · exact cyc154
  · exact cyc155
  · exact cyc156
  · exact cyc157
  · exact cyc158
  · exact cyc159
  · exact cyc160
  · exact cyc161
  · exact cyc162
  · exact cyc163
  · exact cyc164
  · exact cyc165
  · exact cyc166
  · exact cyc167
  · exact cyc168
  · exact cyc169
  · exact cyc170
  · exact cyc171
  · exact cyc172
  · exact cyc173
  · exact cyc174
  · exact cyc175
  · exact cyc176
  · exact cyc177
  · exact cyc178
  · exact cyc179
  · exact cyc180
  · exact cyc181
  · exact cyc182
  · exact cyc183
  · exact cyc184
  · exact cyc185
  · exact cyc186
  · exact cyc187
  · exact cyc188
  · exact cyc189
  · exact cyc190
  · exact cyc191
  · exact cyc192
  · exact cyc193
  · exact cyc194
  · exact cyc195
  · exact cyc196
  · exact cyc197
  · exact cyc198
  · exact cyc199
  · exact cyc200
  · exact cyc201
  · exact cyc202
  · exact cyc203
  · exact cyc204
  · exact cyc205
  · exact cyc206
  · exact cyc207
  · exact cyc208
  · exact cyc209
  · exact cyc210
  · exact cyc211
  · exact cyc212
  · exact cyc213
  · exact cyc214
  · exact cyc215
  · exact cyc216
  · exact cyc217
  · exact cyc218
  · exact cyc219
  · exact cyc220
  · exact cyc221
  · exact cyc222
  · exact cyc223
  · exact cyc224
  · exact cyc225
  · exact cyc226
  · exact cyc227
  · exact cyc228
  · exact cyc229
  · exact cyc230
  · exact cyc231
  · exact cyc232
  · exact cyc233
  · exact cyc234
  · exact cyc235
  · exact cyc236
  · exact cyc237
  · exact cyc238
  · exact cyc239
  · exact cyc240
  · exact cyc241
  · exact cyc242
  · exact cyc243
  · exact cyc244
  · exact cyc245
  · exact cyc246
  · exact cyc247

end

end VOA.DeligneAudit.DeligneCarrier.E8
