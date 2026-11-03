/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroGram4
import VOA.Examples.VirasoroPartitionBasis

/-!
# The canonical level-`5` and level-`6` Gram matrices of `V(c,0)`

`Examples/VirasoroGram4` derives the level-4 matrix of the **canonical normalised fully invariant
form** `B = canonicalInvariantForm hne hqp` — the form whose radical Li's theorem identifies with
`maxGradedIdeal` — and gets `canGram4 c = !![c(c+8)/2, 3c; 3c, 5c]`, `det = c²(5c+22)/2`.
This file does levels `5` and `6` by the same route, and **only** by that route: nothing here is
imported from `LeeYangKac.gram4`, which is the matrix of the *top-mode* form `RigidBridge.shapForm`
and is a matrix of a different bilinear form (see the ⚠ in `Core/GradedFormMatrix`).

## Why level 6

Levels `4` and `5` are both **two**-dimensional, so at a shared determinant zero a `2 × 2` matrix
has very little room.  Level `6` is the first level of dimension `4`
(`VirModule.finrank_gradingVir_six`), and the first level at which two *new* central charges
appear in the degenerate locus:

  `det canGram6 c = (3/4)·c⁴·(2c-1)·(5c+22)²·(7c+68)`.

`c = 1/2` is the **Ising** model `M(3,4)` and `c = -68/7` is `M(2,7)`; neither is degenerate at
levels `2,3,4,5`, whose determinants are `c/2`, `2c`, `c²(5c+22)/2`, `2c²(5c+22)`.  So level 6
supplies the first genuinely new instances of the graded-dimension jump of
`Core/GradedFormMatrix.finrank_maxQuotient_grading_lt_of_det_eq_zero`.

## The derivation

Exactly the two inputs of `VirasoroGram4`, and nothing else:

* **Virasoro adjointness** `B(Lₙa, b) = B(a, L₋ₙb)` — the structure field
  `InvariantForm.virasoro_adj` (repackaged as `VirGram4.canB_adj'`);
* **the normalisation** `B(𝟙,𝟙) = +1` — `InvariantForm.Normalized`.

Peeling creation modes off the left slot reduces every entry to a multiple of `B(𝟙,𝟙)`.  The
twenty-odd `Lop`-on-a-word identities that this needs are derived here in §2–§3 from
`VirModule.Lop_apply_bracket` alone, through the three helpers `br`, `brNe`, `brEq`.

## The sign

Because `(𝟙|𝟙) = +1`, the entries agree with the textbook contravariant form, and the
textbook Kac determinants are recovered on the nose.

## Contents

* §1  `L5vac`, `L3L2vac`, `L6vac`, `L4L2vac`, `L3L3vac`, `L222vac` and their identification with
  the sorted creation words `negWordVir c [3]`, `[1,0]`, `[4]`, `[2,0]`, `[1,1]`, `[0,0,0]`.
* §2  The modes of `L₋₃|0⟩` (`Lop_one_L3vac`, `Lop_two_L3vac`, `Lop_zero_L3vac`,
  `Lop_ge_four_L3vac`) — the auxiliary family `VirasoroGram4` did not need.
* §3  The twenty mode identities at levels 5 and 6.
* §4  `canGram5_eq`, `det_canGram5 = 2c²(5c+22)`.
* §5  `canGram6_eq`, `det_canGram6 = (3/4)c⁴(2c-1)(5c+22)²(7c+68)`.
* §6  Honest bases `basis5`, `basis6` and the identification with `GramMat.canGram`.
* §7  `det_canGram5_ne_zero`, `det_canGram6_ne_zero` — **D3 at levels 5 and 6**: the
  determinant is a *nonzero* polynomial in `c`, exhibited by a value.
-/

set_option linter.style.longLine false

namespace VOA.VirGram56

open VOA VOA.LeeYang VOA.LeeYangKac VOA.VirModule
open VOA.VertexOperatorAlgebra
open Module (Basis finrank)

variable (c : ℂ)

/-! ## §0  The three commutation helpers

`VirModule.Lop_apply_bracket` in the three shapes actually used: raw, with `m + n ≠ 0`
(no central term), and with `m + n = 0` (central term present).  The `p` argument carries the
*normalised* value of `m + n`, which keeps the elaborator from having to decide `1 + -3 =?= -2`
underneath an application of `Lop`. -/

/-- The Virasoro commutator moves a positive mode through a creation mode. Opposite indices additionally contribute the central charge term. -/
private theorem br (m n : ℤ) (w : VirUniv c) :
    Lop c m (Lop c n w)
      = Lop c n (Lop c m w) + ((m : ℂ) - n) • Lop c (m + n) w
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 * c else 0) • w :=
  Lop_apply_bracket c m n w

/-- When the two mode indices do not add to zero, the commutator has no central term. Actions already computed on the shorter word can then be substituted directly. -/
private theorem brNe (m n p : ℤ) (hp : m + n = p) (hmn : p ≠ 0) (w x y : VirUniv c)
    (hx : Lop c m w = x) (hy : Lop c p w = y) :
    Lop c m (Lop c n w) = Lop c n x + ((m : ℂ) - n) • y := by
  have h := br c m n w
  rw [hp, hx, hy, if_neg hmn, zero_smul, add_zero] at h
  exact h

/-- For opposite indices, commuting the modes produces both the grading operator L0 and the central scalar. This is the source of the charge dependence in Gram entries. -/
private theorem brEq (m n : ℤ) (hp : m + n = 0) (w x z : VirUniv c)
    (hx : Lop c m w = x) (hz : Lop c 0 w = z) :
    Lop c m (Lop c n w)
      = Lop c n x + ((m : ℂ) - n) • z + (((m : ℂ) ^ 3 - m) / 12 * c) • w := by
  have h := br c m n w
  rw [hp, hx, hz, if_pos rfl] at h
  exact h

/-! ## §1  The six creation monomials of levels 5 and 6 -/

/-- `L₋₅|0⟩` — the partition `5`. -/
noncomputable def L5vac : VirUniv c := Lop c (-5) (vacVec c)
/-- `L₋₃L₋₂|0⟩` — the partition `3+2`. -/
noncomputable def L3L2vac : VirUniv c := Lop c (-3) (L2vac c)
/-- `L₋₆|0⟩` — the partition `6`. -/
noncomputable def L6vac : VirUniv c := Lop c (-6) (vacVec c)
/-- `L₋₄L₋₂|0⟩` — the partition `4+2`. -/
noncomputable def L4L2vac : VirUniv c := Lop c (-4) (L2vac c)
/-- `L₋₃L₋₃|0⟩` — the partition `3+3`. -/
noncomputable def L3L3vac : VirUniv c := Lop c (-3) (L3vac c)
/-- `L₋₂³|0⟩` — the partition `2+2+2`. -/
noncomputable def L222vac : VirUniv c := Lop c (-2) (L2L2vac c)

/-- The partition word indexed by [3] means L-minus-five on the vacuum: vacuum creation indices are shifted by two. -/
theorem negWordVir_L5vac : negWordVir c [3] = L5vac c := by
  have h : (-((3 : ℕ) : ℤ) - 2) = -5 := by norm_num
  rw [negWordVir_cons, negWordVir_nil, h, L5vac]

/-- The word [1,0] is the weight-five state L-minus-three followed by L-minus-two. This connects the named state with its partition-basis coordinate. -/
theorem negWordVir_L3L2vac : negWordVir c [1, 0] = L3L2vac c := by
  have h1 : (-((1 : ℕ) : ℤ) - 2) = -3 := by norm_num
  have h0 : (-((0 : ℕ) : ℤ) - 2) = -2 := by norm_num
  rw [negWordVir_cons, negWordVir_cons, negWordVir_nil, h1, h0, L3L2vac]
  rfl

/-- The singleton partition word [4] is L-minus-six on the vacuum, one of the four weight-six basis states. -/
theorem negWordVir_L6vac : negWordVir c [4] = L6vac c := by
  have h : (-((4 : ℕ) : ℤ) - 2) = -6 := by norm_num
  rw [negWordVir_cons, negWordVir_nil, h, L6vac]

/-- The word [2,0] is the weight-six partition 4+2, namely L-minus-four acting on the conformal vector. -/
theorem negWordVir_L4L2vac : negWordVir c [2, 0] = L4L2vac c := by
  have h2 : (-((2 : ℕ) : ℤ) - 2) = -4 := by norm_num
  have h0 : (-((0 : ℕ) : ℤ) - 2) = -2 := by norm_num
  rw [negWordVir_cons, negWordVir_cons, negWordVir_nil, h2, h0, L4L2vac]
  rfl

/-- The word [1,1] is the weight-six partition 3+3. Both creation operators have index minus three. -/
theorem negWordVir_L3L3vac : negWordVir c [1, 1] = L3L3vac c := by
  have h1 : (-((1 : ℕ) : ℤ) - 2) = -3 := by norm_num
  rw [negWordVir_cons, negWordVir_cons, negWordVir_nil, h1, L3L3vac]
  rfl

/-- The word [0,0,0] is the weight-six partition 2+2+2, or the third power of L-minus-two acting on the vacuum. -/
theorem negWordVir_L222vac : negWordVir c [0, 0, 0] = L222vac c := by
  have h0 : (-((0 : ℕ) : ℤ) - 2) = -2 := by norm_num
  rw [negWordVir_cons, negWordVir_cons, negWordVir_cons, negWordVir_nil, h0, L222vac]
  rfl

/-- Membership of a sorted creation word in its graded piece. -/
theorem negWordVir_mem_grading (n : ℕ) (w : List ℕ) (hw : SortedWord w) (he : energyVir w = n) :
    negWordVir c w ∈ (virasoroVOA c).grading (n : ℤ) := by
  have h : negWordVir c w ∈ gradingVir c (n : ℤ) := by
    rw [gradingVir_eq_sortedSpanVir]
    exact negWordVir_mem_sortedSpanVir_of_sorted c hw he
  exact h

/-- The single creation mode L-minus-five raises the vacuum to weight five. This places the first weight-five Gram vector in the correct homogeneous space. -/
theorem L5vac_mem : L5vac c ∈ (virasoroVOA c).grading 5 := by
  have h5 : ((5 : ℕ) : ℤ) = (5 : ℤ) := by norm_num
  rw [← negWordVir_L5vac, ← h5]
  exact negWordVir_mem_grading c 5 [3] (by decide) rfl

/-- The successive creation energies three and two add to five. Thus the second weight-five Gram vector can be compared with L-minus-five using the form on that weight space. -/
theorem L3L2vac_mem : L3L2vac c ∈ (virasoroVOA c).grading 5 := by
  have h5 : ((5 : ℕ) : ℤ) = (5 : ℤ) := by norm_num
  rw [← negWordVir_L3L2vac, ← h5]
  exact negWordVir_mem_grading c 5 [1, 0] (by decide) rfl

/-- The state created by L-minus-six is homogeneous of weight six, the first partition vector used for the level-six determinant. -/
theorem L6vac_mem : L6vac c ∈ (virasoroVOA c).grading 6 := by
  have h6 : ((6 : ℕ) : ℤ) = (6 : ℤ) := by norm_num
  rw [← negWordVir_L6vac, ← h6]
  exact negWordVir_mem_grading c 6 [4] (by decide) rfl

/-- The partition four plus two gives a homogeneous weight-six state. This checks the grading of the second vector in the level-six Gram matrix. -/
theorem L4L2vac_mem : L4L2vac c ∈ (virasoroVOA c).grading 6 := by
  have h6 : ((6 : ℕ) : ℤ) = (6 : ℤ) := by norm_num
  rw [← negWordVir_L4L2vac, ← h6]
  exact negWordVir_mem_grading c 6 [2, 0] (by decide) rfl

/-- Two L-minus-three modes have total creation energy six. Their state belongs to the same weight space as the other level-six partition vectors. -/
theorem L3L3vac_mem : L3L3vac c ∈ (virasoroVOA c).grading 6 := by
  have h6 : ((6 : ℕ) : ℤ) = (6 : ℤ) := by norm_num
  rw [← negWordVir_L3L3vac, ← h6]
  exact negWordVir_mem_grading c 6 [1, 1] (by decide) rfl

/-- Three L-minus-two modes raise the vacuum by six units. This is the all-conformal-state partition vector in the weight-six Gram calculation. -/
theorem L222vac_mem : L222vac c ∈ (virasoroVOA c).grading 6 := by
  have h6 : ((6 : ℕ) : ℤ) = (6 : ℤ) := by norm_num
  rw [← negWordVir_L222vac, ← h6]
  exact negWordVir_mem_grading c 6 [0, 0, 0] (by decide) rfl

/-! ## §2  The modes of `L₋₃|0⟩`

`VirasoroGram4` needed only the modes of `L₋₂|0⟩`, `L₋₄|0⟩`, `L₋₂²|0⟩`, all of which are in
`LeeYangSingular` / `LeeYangGram` / `LeeYangKac`.  Level 6 needs `L₋₃|0⟩` too. -/

/-- `L₁L₋₃|0⟩ = 4L₋₂|0⟩`. -/
theorem Lop_one_L3vac : Lop c 1 (L3vac c) = (4 : ℂ) • L2vac c := by
  rw [L3vac, brNe c 1 (-3) (-2) (by norm_num) (by norm_num) (vacVec c) 0 (L2vac c)
      (Lop_vacuum c (by norm_num : (-1:ℤ) ≤ (1:ℤ))) rfl, map_zero, zero_add]
  norm_num

/-- `L₂L₋₃|0⟩ = 5L₋₁|0⟩ = 0`. -/
theorem Lop_two_L3vac : Lop c 2 (L3vac c) = 0 := by
  rw [L3vac, brNe c 2 (-3) (-1) (by norm_num) (by norm_num) (vacVec c) 0 0
      (Lop_vacuum c (by norm_num : (-1:ℤ) ≤ (2:ℤ)))
      (Lop_vacuum c (by norm_num : (-1:ℤ) ≤ (-1:ℤ))), map_zero, smul_zero, add_zero]

/-- `L₀L₋₃|0⟩ = 3L₋₃|0⟩` — the weight. -/
theorem Lop_zero_L3vac : Lop c 0 (L3vac c) = (3 : ℂ) • L3vac c := by
  rw [L3vac, brNe c 0 (-3) (-3) (by norm_num) (by norm_num) (vacVec c) 0 (L3vac c)
      (Lop_vacuum c (by norm_num : (-1:ℤ) ≤ (0:ℤ))) rfl, map_zero, zero_add]
  norm_num [L3vac]

/-- `LₙL₋₃|0⟩ = 0` for `n ≥ 4`. -/
theorem Lop_ge_four_L3vac {n : ℤ} (hn : 4 ≤ n) : Lop c n (L3vac c) = 0 := by
  rw [L3vac, brNe c n (-3) (n - 3) (by omega) (by omega) (vacVec c) 0 0
      (Lop_vacuum c (by omega : (-1:ℤ) ≤ n))
      (Lop_vacuum c (by omega : (-1:ℤ) ≤ n - 3)), map_zero, smul_zero, add_zero]

/-- `B(L₋₃|0⟩, L₋₃|0⟩) = 2c` — the level-3 Gram matrix, a `1 × 1`. -/
theorem canB_L3_L3 : (VirGram4.canB c).form (L3vac c) (L3vac c) = 2 * c := by
  have h := VirGram4.canB_adj' c 3 (vacVec c) (L3vac c)
  rw [show Lop c (-3) (vacVec c) = L3vac c from rfl] at h
  rw [h, Lop_three_L3vac, VirGram4.canB_vac_smul]

/-! ## §3  The mode identities at levels 5 and 6 -/

/-- `L₅L₋₅|0⟩ = 10c·|0⟩` — the central term `(c/12)(5³-5)`. -/
theorem Lop_five_L5vac : Lop c 5 (L5vac c) = (10 * c) • vacVec c := by
  rw [L5vac, brEq c 5 (-5) (by norm_num) (vacVec c) 0 0
      (Lop_vacuum c (by norm_num : (-1:ℤ) ≤ (5:ℤ)))
      (Lop_vacuum c (by norm_num : (-1:ℤ) ≤ (0:ℤ))), map_zero, smul_zero, add_zero, zero_add]
  norm_num

/-- `L₃L₋₅|0⟩ = 8L₋₂|0⟩`. -/
theorem Lop_three_L5vac : Lop c 3 (L5vac c) = (8 : ℂ) • L2vac c := by
  rw [L5vac, brNe c 3 (-5) (-2) (by norm_num) (by norm_num) (vacVec c) 0 (L2vac c)
      (Lop_vacuum c (by norm_num : (-1:ℤ) ≤ (3:ℤ))) rfl, map_zero, zero_add]
  norm_num

/-- `L₅L₋₃L₋₂|0⟩ = 4c·|0⟩`. -/
theorem Lop_five_L3L2vac : Lop c 5 (L3L2vac c) = (4 * c) • vacVec c := by
  rw [L3L2vac, brNe c 5 (-3) 2 (by norm_num) (by norm_num) (L2vac c) 0 ((c / 2) • vacVec c)
      (Lop_ge_three_L2vac c (by norm_num)) (Lop_two_L2vac c), map_zero, zero_add, smul_smul]
  norm_num
  ring_nf

/-- `L₃L₋₃L₋₂|0⟩ = (2c+12)L₋₂|0⟩`. -/
theorem Lop_three_L3L2vac : Lop c 3 (L3L2vac c) = (2 * c + 12) • L2vac c := by
  rw [L3L2vac, brEq c 3 (-3) (by norm_num) (L2vac c) 0 ((2 : ℂ) • L2vac c)
      (Lop_ge_three_L2vac c (by norm_num)) (Lop_zero_L2vac c), map_zero, zero_add, smul_smul,
      ← add_smul]
  norm_num
  ring_nf

/-- `L₆L₋₆|0⟩ = (35/2)c·|0⟩` — the central term `(c/12)(6³-6)`. -/
theorem Lop_six_L6vac : Lop c 6 (L6vac c) = (35 / 2 * c) • vacVec c := by
  rw [L6vac, brEq c 6 (-6) (by norm_num) (vacVec c) 0 0
      (Lop_vacuum c (by norm_num : (-1:ℤ) ≤ (6:ℤ)))
      (Lop_vacuum c (by norm_num : (-1:ℤ) ≤ (0:ℤ))), map_zero, smul_zero, add_zero, zero_add]
  norm_num

/-- `L₆L₋₄L₋₂|0⟩ = 5c·|0⟩`. -/
theorem Lop_six_L4L2vac : Lop c 6 (L4L2vac c) = (5 * c) • vacVec c := by
  rw [L4L2vac, brNe c 6 (-4) 2 (by norm_num) (by norm_num) (L2vac c) 0 ((c / 2) • vacVec c)
      (Lop_ge_three_L2vac c (by norm_num)) (Lop_two_L2vac c), map_zero, zero_add, smul_smul]
  norm_num
  ring_nf

/-- `L₆L₋₃L₋₃|0⟩ = 18c·|0⟩`. -/
theorem Lop_six_L3L3vac : Lop c 6 (L3L3vac c) = (18 * c) • vacVec c := by
  rw [L3L3vac, brNe c 6 (-3) 3 (by norm_num) (by norm_num) (L3vac c) 0 ((2 * c) • vacVec c)
      (Lop_ge_four_L3vac c (by norm_num)) (Lop_three_L3vac c), map_zero, zero_add, smul_smul]
  norm_num
  ring_nf

/-- `L₆L₋₂³|0⟩ = 24c·|0⟩`. -/
theorem Lop_six_L222vac : Lop c 6 (L222vac c) = (24 * c) • vacVec c := by
  rw [L222vac, brNe c 6 (-2) 4 (by norm_num) (by norm_num) (L2L2vac c) 0 ((3 * c) • vacVec c)
      (Lop_ge_five_L2L2vac c (by norm_num)) (Lop_four_L2L2vac c), map_zero, zero_add, smul_smul]
  norm_num
  ring_nf

/-- `L₄L₋₆|0⟩ = 10L₋₂|0⟩`. -/
theorem Lop_four_L6vac : Lop c 4 (L6vac c) = (10 : ℂ) • L2vac c := by
  rw [L6vac, brNe c 4 (-6) (-2) (by norm_num) (by norm_num) (vacVec c) 0 (L2vac c)
      (Lop_vacuum c (by norm_num : (-1:ℤ) ≤ (4:ℤ))) rfl, map_zero, zero_add]
  norm_num

/-- `L₄L₋₄L₋₂|0⟩ = (5c+16)L₋₂|0⟩`. -/
theorem Lop_four_L4L2vac : Lop c 4 (L4L2vac c) = (5 * c + 16) • L2vac c := by
  rw [L4L2vac, brEq c 4 (-4) (by norm_num) (L2vac c) 0 ((2 : ℂ) • L2vac c)
      (Lop_ge_three_L2vac c (by norm_num)) (Lop_zero_L2vac c), map_zero, zero_add, smul_smul,
      ← add_smul]
  norm_num
  ring_nf

/-- `L₄L₋₃L₋₃|0⟩ = 28L₋₂|0⟩`. -/
theorem Lop_four_L3L3vac : Lop c 4 (L3L3vac c) = (28 : ℂ) • L2vac c := by
  rw [L3L3vac, brNe c 4 (-3) 1 (by norm_num) (by norm_num) (L3vac c) 0 ((4 : ℂ) • L2vac c)
      (Lop_ge_four_L3vac c (by norm_num)) (Lop_one_L3vac c), map_zero, zero_add, smul_smul]
  norm_num

/-- `L₄L₋₂³|0⟩ = (9c+48)L₋₂|0⟩`. -/
theorem Lop_four_L222vac : Lop c 4 (L222vac c) = (9 * c + 48) • L2vac c := by
  rw [L222vac, brNe c 4 (-2) 2 (by norm_num) (by norm_num) (L2L2vac c) ((3 * c) • vacVec c)
      ((c + 8) • L2vac c) (Lop_four_L2L2vac c) (Lop_two_L2L2vac c), map_smul,
      show Lop c (-2) (vacVec c) = L2vac c from rfl, smul_smul, ← add_smul]
  norm_num
  ring_nf

/-- `L₃L₋₆|0⟩ = 9L₋₃|0⟩`. -/
theorem Lop_three_L6vac : Lop c 3 (L6vac c) = (9 : ℂ) • L3vac c := by
  rw [L6vac, brNe c 3 (-6) (-3) (by norm_num) (by norm_num) (vacVec c) 0 (L3vac c)
      (Lop_vacuum c (by norm_num : (-1:ℤ) ≤ (3:ℤ))) rfl, map_zero, zero_add]
  norm_num

/-- `L₃L₋₄L₋₂|0⟩ = 7L₋₃|0⟩`. -/
theorem Lop_three_L4L2vac : Lop c 3 (L4L2vac c) = (7 : ℂ) • L3vac c := by
  rw [L4L2vac, brNe c 3 (-4) (-1) (by norm_num) (by norm_num) (L2vac c) 0 (L3vac c)
      (Lop_ge_three_L2vac c (by norm_num)) (Lop_neg_one_L2vac c), map_zero, zero_add]
  norm_num

/-- `L₃L₋₃L₋₃|0⟩ = (4c+18)L₋₃|0⟩`. -/
theorem Lop_three_L3L3vac : Lop c 3 (L3L3vac c) = (4 * c + 18) • L3vac c := by
  rw [L3L3vac, brEq c 3 (-3) (by norm_num) (L3vac c) ((2 * c) • vacVec c) ((3 : ℂ) • L3vac c)
      (Lop_three_L3vac c) (Lop_zero_L3vac c), map_smul,
      show Lop c (-3) (vacVec c) = L3vac c from rfl, smul_smul, ← add_smul, ← add_smul]
  norm_num
  ring_nf

/-- `L₃L₋₂³|0⟩ = 15L₋₃|0⟩`. -/
theorem Lop_three_L222vac : Lop c 3 (L222vac c) = (15 : ℂ) • L3vac c := by
  rw [L222vac, brNe c 3 (-2) 1 (by norm_num) (by norm_num) (L2L2vac c) 0 ((3 : ℂ) • L3vac c)
      (Lop_three_L2L2vac c) (Lop_one_L2L2vac c), map_zero, zero_add, smul_smul]
  norm_num

/-- `L₂L₋₆|0⟩ = 8L₋₄|0⟩`. -/
theorem Lop_two_L6vac : Lop c 2 (L6vac c) = (8 : ℂ) • L4vac c := by
  rw [L6vac, brNe c 2 (-6) (-4) (by norm_num) (by norm_num) (vacVec c) 0 (L4vac c)
      (Lop_vacuum c (by norm_num : (-1:ℤ) ≤ (2:ℤ))) rfl, map_zero, zero_add]
  norm_num

/-- `L₂L₋₄L₋₂|0⟩ = 6L₋₂²|0⟩ + (c/2)L₋₄|0⟩` — the one entry with two terms. -/
theorem Lop_two_L4L2vac :
    Lop c 2 (L4L2vac c) = (6 : ℂ) • L2L2vac c + (c / 2) • L4vac c := by
  rw [L4L2vac, brNe c 2 (-4) (-2) (by norm_num) (by norm_num) (L2vac c) ((c / 2) • vacVec c)
      (L2L2vac c) (Lop_two_L2vac c) rfl, map_smul,
      show Lop c (-4) (vacVec c) = L4vac c from rfl]
  rw [add_comm]
  norm_num

/-- `L₂L₋₃L₋₃|0⟩ = 10L₋₄|0⟩`. -/
theorem Lop_two_L3L3vac : Lop c 2 (L3L3vac c) = (10 : ℂ) • L4vac c := by
  rw [L3L3vac, brNe c 2 (-3) (-1) (by norm_num) (by norm_num) (L3vac c) 0 ((2 : ℂ) • L4vac c)
      (Lop_two_L3vac c) (Lop_neg_one_L3vac c), map_zero, zero_add, smul_smul]
  norm_num

/-- `L₂L₋₂³|0⟩ = ((3/2)c+24)L₋₂²|0⟩`. -/
theorem Lop_two_L222vac : Lop c 2 (L222vac c) = (3 * c / 2 + 24) • L2L2vac c := by
  rw [L222vac, brEq c 2 (-2) (by norm_num) (L2L2vac c) ((c + 8) • L2vac c)
      ((4 : ℂ) • L2L2vac c) (Lop_two_L2L2vac c) (Lop_zero_L2L2vac c), map_smul,
      show Lop c (-2) (L2vac c) = L2L2vac c from rfl, smul_smul, ← add_smul, ← add_smul]
  norm_num
  ring_nf


/-! ## §4  The level-5 Gram matrix and its determinant

Basis order `(L₋₅|0⟩, L₋₃L₋₂|0⟩)` — the partitions `5` and `3+2` in decreasing order. -/

/-- The norm of the single-mode weight-five state is 10c. Moving its creation mode to the other argument reduces the pairing to the central term of the Virasoro commutator. -/
theorem canB_L5_L5 : (VirGram4.canB c).form (L5vac c) (L5vac c) = 10 * c := by
  have h := VirGram4.canB_adj' c 5 (vacVec c) (L5vac c)
  rw [show Lop c (-5) (vacVec c) = L5vac c from rfl] at h
  rw [h, Lop_five_L5vac, VirGram4.canB_vac_smul]

/-- The mixed pairing of the partitions 5 and 3+2 is 4c. Applying the positive fifth mode to the two-mode state reduces it to a scalar multiple of the vacuum. -/
theorem canB_L5_L3L2 : (VirGram4.canB c).form (L5vac c) (L3L2vac c) = 4 * c := by
  have h := VirGram4.canB_adj' c 5 (vacVec c) (L3L2vac c)
  rw [show Lop c (-5) (vacVec c) = L5vac c from rfl] at h
  rw [h, Lop_five_L3L2vac, VirGram4.canB_vac_smul]

/-- The reversed mixed pairing is also 4c. This direct adjoint calculation checks the second off-diagonal entry without assuming a separate symmetry theorem. -/
theorem canB_L3L2_L5 : (VirGram4.canB c).form (L3L2vac c) (L5vac c) = 4 * c := by
  have h := VirGram4.canB_adj' c 3 (L2vac c) (L5vac c)
  rw [show Lop c (-3) (L2vac c) = L3L2vac c from rfl] at h
  rw [h, Lop_three_L5vac, map_smul, VirGram4.canB_L2_L2, smul_eq_mul]
  ring

/-- The norm of the two-mode weight-five state is c(c+6). The quadratic term comes from successive central contractions; the linear term records the noncentral commutators. -/
theorem canB_L3L2_L3L2 :
    (VirGram4.canB c).form (L3L2vac c) (L3L2vac c) = c * (c + 6) := by
  have h := VirGram4.canB_adj' c 3 (L2vac c) (L3L2vac c)
  rw [show Lop c (-3) (L2vac c) = L3L2vac c from rfl] at h
  rw [h, Lop_three_L3L2vac, map_smul, VirGram4.canB_L2_L2, smul_eq_mul]
  ring

/-- **The level-5 Gram matrix** of `V(c,0)`, in the basis `(L₋₅|0⟩, L₋₃L₋₂|0⟩)`. -/
noncomputable def canGram5 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(VirGram4.canB c).form (L5vac c) (L5vac c), (VirGram4.canB c).form (L5vac c) (L3L2vac c);
     (VirGram4.canB c).form (L3L2vac c) (L5vac c),
       (VirGram4.canB c).form (L3L2vac c) (L3L2vac c)]

/-- `canGram5 c = !![10c, 4c; 4c, c²+6c]`. -/
theorem canGram5_eq : canGram5 c = !![10 * c, 4 * c; 4 * c, c * (c + 6)] := by
  rw [canGram5, canB_L5_L5, canB_L5_L3L2, canB_L3L2_L5, canB_L3L2_L3L2]

/-- **The level-5 Kac determinant**: `det (canGram5 c) = 2c²(5c+22)`.

Same zero set as level 4 (`c = 0` and the Lee–Yang charge `-22/5`), which is why level 5 alone
adds no new degenerate central charge — see §5. -/
theorem det_canGram5 : (canGram5 c).det = 2 * c ^ 2 * (5 * c + 22) := by
  rw [canGram5_eq, Matrix.det_fin_two_of]
  ring

/-- The weight-five canonical Gram matrix is singular exactly at charge zero or the Lee–Yang charge. This describes its ordinary zero set, without asserting root simplicity or rigidity. -/
theorem det_canGram5_eq_zero_iff : (canGram5 c).det = 0 ↔ c = 0 ∨ c = leeYangC := by
  rw [det_canGram5, leeYangC]
  constructor
  · intro h
    have h' : c ^ 2 * (5 * c + 22) = 0 := by linear_combination h / 2
    rcases mul_eq_zero.mp h' with h1 | h2
    · exact Or.inl (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1)
    · right; linear_combination h2 / 5
  · rintro (rfl | rfl) <;> norm_num

/-! ## §5  The level-6 Gram matrix and its determinant

Basis order `(L₋₆|0⟩, L₋₄L₋₂|0⟩, L₋₃L₋₃|0⟩, L₋₂³|0⟩)` — the partitions `6`, `4+2`, `3+3`,
`2+2+2` in decreasing order. -/

/-- The squared canonical norm of L₋₆1 is 35c/2. Move L₋₆ across the form as L₆; its commutator with
L₋₆ contributes (6³−6)c/12 on the vacuum. -/
theorem canB_L6_L6 : (VirGram4.canB c).form (L6vac c) (L6vac c) = 35 / 2 * c := by
  have h := VirGram4.canB_adj' c 6 (vacVec c) (L6vac c)
  rw [show Lop c (-6) (vacVec c) = L6vac c from rfl] at h
  rw [h, Lop_six_L6vac, VirGram4.canB_vac_smul]

/-- The pairing of L₋₆1 with L₋₄L₋₂1 is 5c. Adjointness turns the first state into L₆ acting on the
second; the remaining positive mode reduces it to a vacuum multiple. -/
theorem canB_L6_L4L2 : (VirGram4.canB c).form (L6vac c) (L4L2vac c) = 5 * c := by
  have h := VirGram4.canB_adj' c 6 (vacVec c) (L4L2vac c)
  rw [show Lop c (-6) (vacVec c) = L6vac c from rfl] at h
  rw [h, Lop_six_L4L2vac, VirGram4.canB_vac_smul]

/-- The pairing of L₋₆1 with L₋₃²1 is 18c. The commutator first produces 9L₃, whose action on L₋₃1
produces the central vacuum coefficient 2c. -/
theorem canB_L6_L3L3 : (VirGram4.canB c).form (L6vac c) (L3L3vac c) = 18 * c := by
  have h := VirGram4.canB_adj' c 6 (vacVec c) (L3L3vac c)
  rw [show Lop c (-6) (vacVec c) = L6vac c from rfl] at h
  rw [h, Lop_six_L3L3vac, VirGram4.canB_vac_smul]

/-- The pairing of the single mode L₋₆1 with the three-mode state L₋₂³1 is 24c. This is a cross term
in the canonical level-six matrix, computed by moving L₋₆ to the other side of the form. -/
theorem canB_L6_L222 : (VirGram4.canB c).form (L6vac c) (L222vac c) = 24 * c := by
  have h := VirGram4.canB_adj' c 6 (vacVec c) (L222vac c)
  rw [show Lop c (-6) (vacVec c) = L6vac c from rfl] at h
  rw [h, Lop_six_L222vac, VirGram4.canB_vac_smul]

/-- The reverse-order pairing of L₋₄L₋₂1 with L₋₆1 is again 5c. Its proof independently moves L₋₄
across and reduces to the norm of L₋₂1, checking the corresponding symmetric matrix entry. -/
theorem canB_L4L2_L6 : (VirGram4.canB c).form (L4L2vac c) (L6vac c) = 5 * c := by
  have h := VirGram4.canB_adj' c 4 (L2vac c) (L6vac c)
  rw [show Lop c (-4) (L2vac c) = L4L2vac c from rfl] at h
  rw [h, Lop_four_L6vac, map_smul, VirGram4.canB_L2_L2, smul_eq_mul]
  ring

/-- The squared norm of L₋₄L₋₂1 is (5c²+16c)/2. After adjointness, L₄ acting on the right state
leaves a multiple of L₋₂1; multiplying by its norm c/2 gives the stated quadratic polynomial. -/
theorem canB_L4L2_L4L2 :
    (VirGram4.canB c).form (L4L2vac c) (L4L2vac c) = (5 * c ^ 2 + 16 * c) / 2 := by
  have h := VirGram4.canB_adj' c 4 (L2vac c) (L4L2vac c)
  rw [show Lop c (-4) (L2vac c) = L4L2vac c from rfl] at h
  rw [h, Lop_four_L4L2vac, map_smul, VirGram4.canB_L2_L2, smul_eq_mul]
  ring

/-- The pairing of L₋₄L₋₂1 with L₋₃²1 is 14c. Moving L₋₄ across reduces this cross term to a scalar
multiple of the weight-two norm. -/
theorem canB_L4L2_L3L3 : (VirGram4.canB c).form (L4L2vac c) (L3L3vac c) = 14 * c := by
  have h := VirGram4.canB_adj' c 4 (L2vac c) (L3L3vac c)
  rw [show Lop c (-4) (L2vac c) = L4L2vac c from rfl] at h
  rw [h, Lop_four_L3L3vac, map_smul, VirGram4.canB_L2_L2, smul_eq_mul]
  ring

/-- The pairing of L₋₄L₋₂1 with L₋₂³1 is (9c²+48c)/2. The positive-mode reduction has both a central
contribution and a contribution from the grading term in the Virasoro bracket. -/
theorem canB_L4L2_L222 :
    (VirGram4.canB c).form (L4L2vac c) (L222vac c) = (9 * c ^ 2 + 48 * c) / 2 := by
  have h := VirGram4.canB_adj' c 4 (L2vac c) (L222vac c)
  rw [show Lop c (-4) (L2vac c) = L4L2vac c from rfl] at h
  rw [h, Lop_four_L222vac, map_smul, VirGram4.canB_L2_L2, smul_eq_mul]
  ring

/-- The reverse-order pairing of L₋₃²1 with L₋₆1 is 18c. Moving one L₋₃ across leaves the known norm
of L₋₃1, rather than assuming matrix symmetry as an extra input. -/
theorem canB_L3L3_L6 : (VirGram4.canB c).form (L3L3vac c) (L6vac c) = 18 * c := by
  have h := VirGram4.canB_adj' c 3 (L3vac c) (L6vac c)
  rw [show Lop c (-3) (L3vac c) = L3L3vac c from rfl] at h
  rw [h, Lop_three_L6vac, map_smul, canB_L3_L3, smul_eq_mul]
  ring

/-- The reverse-order cross term for L₋₃²1 and L₋₄L₋₂1 is 14c. Adjointness and the explicit L₃
action reduce it to the weight-three canonical norm. -/
theorem canB_L3L3_L4L2 : (VirGram4.canB c).form (L3L3vac c) (L4L2vac c) = 14 * c := by
  have h := VirGram4.canB_adj' c 3 (L3vac c) (L4L2vac c)
  rw [show Lop c (-3) (L3vac c) = L3L3vac c from rfl] at h
  rw [h, Lop_three_L4L2vac, map_smul, canB_L3_L3, smul_eq_mul]
  ring

/-- The squared norm of L₋₃²1 is 8c²+36c. This polynomial records the central and grading
contributions obtained when a positive L₃ is commuted through the two negative modes. -/
theorem canB_L3L3_L3L3 :
    (VirGram4.canB c).form (L3L3vac c) (L3L3vac c) = 8 * c ^ 2 + 36 * c := by
  have h := VirGram4.canB_adj' c 3 (L3vac c) (L3L3vac c)
  rw [show Lop c (-3) (L3vac c) = L3L3vac c from rfl] at h
  rw [h, Lop_three_L3L3vac, map_smul, canB_L3_L3, smul_eq_mul]
  ring

/-- The pairing of L₋₃²1 with L₋₂³1 is 30c. A single adjointness step reduces it to the already
calculated L₃ action and the weight-three norm. -/
theorem canB_L3L3_L222 : (VirGram4.canB c).form (L3L3vac c) (L222vac c) = 30 * c := by
  have h := VirGram4.canB_adj' c 3 (L3vac c) (L222vac c)
  rw [show Lop c (-3) (L3vac c) = L3L3vac c from rfl] at h
  rw [h, Lop_three_L222vac, map_smul, canB_L3_L3, smul_eq_mul]
  ring

/-- The reverse-order pairing of L₋₂³1 with L₋₆1 is 24c. Moving the first L₋₂ across reduces it to
the known weight-four pairing between L₋₂²1 and L₋₄1. -/
theorem canB_L222_L6 : (VirGram4.canB c).form (L222vac c) (L6vac c) = 24 * c := by
  have h := VirGram4.canB_adj' c 2 (L2L2vac c) (L6vac c)
  rw [show Lop c (-2) (L2L2vac c) = L222vac c from rfl] at h
  rw [h, Lop_two_L6vac, map_smul, VirGram4.canB_L2L2_L4, smul_eq_mul]
  ring

/-- The pairing of L₋₂³1 with L₋₄L₋₂1 is (9c²+48c)/2. After moving one L₋₂ across, the right state
becomes a sum of two weight-four descendants; bilinearity combines their two known pairings. -/
theorem canB_L222_L4L2 :
    (VirGram4.canB c).form (L222vac c) (L4L2vac c) = (9 * c ^ 2 + 48 * c) / 2 := by
  have h := VirGram4.canB_adj' c 2 (L2L2vac c) (L4L2vac c)
  rw [show Lop c (-2) (L2L2vac c) = L222vac c from rfl] at h
  rw [h, Lop_two_L4L2vac, map_add, map_smul, map_smul, VirGram4.canB_L2L2_L2L2,
    VirGram4.canB_L2L2_L4, smul_eq_mul, smul_eq_mul]
  ring

/-- The pairing of L₋₂³1 with L₋₃²1 is 30c. The L₂ action reduces the right state to a multiple of
L₋₄1, so the answer follows from the canonical weight-four cross term. -/
theorem canB_L222_L3L3 : (VirGram4.canB c).form (L222vac c) (L3L3vac c) = 30 * c := by
  have h := VirGram4.canB_adj' c 2 (L2L2vac c) (L3L3vac c)
  rw [show Lop c (-2) (L2L2vac c) = L222vac c from rfl] at h
  rw [h, Lop_two_L3L3vac, map_smul, VirGram4.canB_L2L2_L4, smul_eq_mul]
  ring

/-- The squared norm of L₋₂³1 factors as 3c(c+8)(c+16)/4. Removing one L₋₂ by adjointness leaves the
weight-four squared norm and a further linear factor. This is a bilinear norm; no positivity is
asserted. -/
theorem canB_L222_L222 :
    (VirGram4.canB c).form (L222vac c) (L222vac c) = 3 * c * (c + 8) * (c + 16) / 4 := by
  have h := VirGram4.canB_adj' c 2 (L2L2vac c) (L222vac c)
  rw [show Lop c (-2) (L2L2vac c) = L222vac c from rfl] at h
  rw [h, Lop_two_L222vac, map_smul, VirGram4.canB_L2L2_L2L2, smul_eq_mul]
  ring

/-- **The level-6 Gram matrix** of `V(c,0)`, in the basis
`(L₋₆|0⟩, L₋₄L₋₂|0⟩, L₋₃L₋₃|0⟩, L₋₂³|0⟩)`. -/
noncomputable def canGram6 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(VirGram4.canB c).form (L6vac c) (L6vac c),
       (VirGram4.canB c).form (L6vac c) (L4L2vac c),
       (VirGram4.canB c).form (L6vac c) (L3L3vac c),
       (VirGram4.canB c).form (L6vac c) (L222vac c);
     (VirGram4.canB c).form (L4L2vac c) (L6vac c),
       (VirGram4.canB c).form (L4L2vac c) (L4L2vac c),
       (VirGram4.canB c).form (L4L2vac c) (L3L3vac c),
       (VirGram4.canB c).form (L4L2vac c) (L222vac c);
     (VirGram4.canB c).form (L3L3vac c) (L6vac c),
       (VirGram4.canB c).form (L3L3vac c) (L4L2vac c),
       (VirGram4.canB c).form (L3L3vac c) (L3L3vac c),
       (VirGram4.canB c).form (L3L3vac c) (L222vac c);
     (VirGram4.canB c).form (L222vac c) (L6vac c),
       (VirGram4.canB c).form (L222vac c) (L4L2vac c),
       (VirGram4.canB c).form (L222vac c) (L3L3vac c),
       (VirGram4.canB c).form (L222vac c) (L222vac c)]

/-- **The level-6 matrix**, at arbitrary central charge. -/
theorem canGram6_eq :
    canGram6 c =
      !![35 / 2 * c, 5 * c, 18 * c, 24 * c;
         5 * c, (5 * c ^ 2 + 16 * c) / 2, 14 * c, (9 * c ^ 2 + 48 * c) / 2;
         18 * c, 14 * c, 8 * c ^ 2 + 36 * c, 30 * c;
         24 * c, (9 * c ^ 2 + 48 * c) / 2, 30 * c,
           3 * c * (c + 8) * (c + 16) / 4] := by
  rw [canGram6, canB_L6_L6, canB_L6_L4L2, canB_L6_L3L3, canB_L6_L222,
    canB_L4L2_L6, canB_L4L2_L4L2, canB_L4L2_L3L3, canB_L4L2_L222,
    canB_L3L3_L6, canB_L3L3_L4L2, canB_L3L3_L3L3, canB_L3L3_L222,
    canB_L222_L6, canB_L222_L4L2, canB_L222_L3L3, canB_L222_L222]

/-- The `4 × 4` cofactor expansion.  Mathlib stops at `Matrix.det_fin_three`. -/
private theorem det_fin_four_of {R : Type*} [CommRing R] (a b d e f g h i j k l m n o p q : R) :
    (!![a, b, d, e; f, g, h, i; j, k, l, m; n, o, p, q] : Matrix (Fin 4) (Fin 4) R).det
      = a * g * l * q - a * g * m * p - a * h * k * q + a * h * m * o + a * i * k * p
        - a * i * l * o - b * f * l * q + b * f * m * p + b * h * j * q - b * h * m * n
        - b * i * j * p + b * i * l * n + d * f * k * q - d * f * m * o - d * g * j * q
        + d * g * m * n + d * i * j * o - d * i * k * n - e * f * k * p + e * f * l * o
        + e * g * j * p - e * g * l * n - e * h * j * o + e * h * k * n := by
  simp +decide [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.cons_val_two,
    Matrix.tail_cons, Fin.succAbove]
  ring

/-- **THE LEVEL-6 KAC DETERMINANT**, for the canonical form:

  `det (canGram6 c) = (3/4)·c⁴·(2c-1)·(5c+22)²·(7c+68)`.

Two central charges appear here that levels `2,3,4,5` do not see: `c = 1/2` (the **Ising** model
`M(3,4)`, `VirasoroVOA.minimalCentralCharge_ising`) and `c = -68/7` (the model `M(2,7)`). -/
theorem det_canGram6 :
    (canGram6 c).det = 3 / 4 * c ^ 4 * (2 * c - 1) * (5 * c + 22) ^ 2 * (7 * c + 68) := by
  rw [canGram6_eq, det_fin_four_of]
  ring

/-- The Ising central charge `c = 1/2`. -/
noncomputable def isingC : ℂ := 1 / 2

/-- The `M(2,7)` central charge `c = -68/7`. -/
noncomputable def m27C : ℂ := -68 / 7

/-- The concrete charge 1/2 is the minimal-model charge for (p,q)=(3,4).
This identifies the finite matrix calculation with the Ising model convention. -/
theorem isingC_eq_minimalCentralCharge :
    isingC = ((minimalCentralCharge 3 4 : ℚ) : ℂ) := by
  rw [isingC, minimalCentralCharge]
  norm_num

/-- The concrete charge −68/7 is the minimal-model charge for (p,q)=(2,7).
The rational formula is transported to the complex coefficient field. -/
theorem m27C_eq_minimalCentralCharge :
    m27C = ((minimalCentralCharge 2 7 : ℚ) : ℂ) := by
  rw [m27C, minimalCentralCharge]
  norm_num

/-- **The level-6 degenerate locus**: exactly four points. -/
theorem det_canGram6_eq_zero_iff :
    (canGram6 c).det = 0 ↔ c = 0 ∨ c = isingC ∨ c = leeYangC ∨ c = m27C := by
  rw [det_canGram6, isingC, leeYangC, m27C]
  constructor
  · intro hh
    have h' : c ^ 4 * ((2 * c - 1) * ((5 * c + 22) ^ 2 * (7 * c + 68))) = 0 := by
      linear_combination 4 / 3 * hh
    rcases mul_eq_zero.mp h' with h1 | h2
    · exact Or.inl (pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h1)
    · rcases mul_eq_zero.mp h2 with h3 | h4
      · exact Or.inr (Or.inl (by linear_combination h3 / 2))
      · rcases mul_eq_zero.mp h4 with h5 | h6
        · have h5' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h5
          exact Or.inr (Or.inr (Or.inl (by linear_combination h5' / 5)))
        · exact Or.inr (Or.inr (Or.inr (by linear_combination h6 / 7)))
  · rintro (rfl | rfl | rfl | rfl) <;> norm_num

/-! ## §6  Honest bases of `𝒱₅` and `𝒱₆`, and the `GramMat` identification -/

/-- Linear independence of an explicitly indexed family of sorted creation words, transported
into any submodule containing them.  The content is
`VirModule.negWordVir_coef_zero'` (independence at *every* central charge, via the linear-dilaton
free boson). -/
theorem indep_of_words {ι : Type*} (v : ι → List ℕ) (hinj : Function.Injective v)
    (hsort : ∀ i, SortedWord (v i)) {M : Submodule ℂ (VirUniv c)} (f : ι → M)
    (hf : ∀ i, (f i : VirUniv c) = negWordVir c (v i)) :
    LinearIndependent ℂ f := by
  classical
  refine LinearIndependent.of_comp M.subtype ?_
  rw [linearIndependent_iff']
  intro s g hsum i hi
  refine negWordVir_coef_zero' v hinj hsort c s g ?_ i hi
  have heq : ∑ j ∈ s, g j • negWordVir c (v j) = ∑ j ∈ s, g j • (M.subtype ∘ f) j :=
    Finset.sum_congr rfl fun j _ => by
      simp only [Function.comp_apply, Submodule.subtype_apply, hf j]
  rw [heq, hsum]

/-- `(L₋₅|0⟩, L₋₃L₋₂|0⟩)` inside `𝒱₅`. -/
noncomputable def vec5 : Fin 2 → (virasoroVOA c).grading 5 :=
  ![⟨L5vac c, L5vac_mem c⟩, ⟨L3L2vac c, L3L2vac_mem c⟩]

/-- The two weight-five partition states are independent at every charge in the universal vacuum module. Their distinct ordered words have independent Fock symbols; degeneracy of the canonical form does not make these universal states dependent. -/
theorem vec5_linearIndependent : LinearIndependent ℂ (vec5 c) := by
  refine indep_of_words c ![[3], [1, 0]] ?_ ?_ (vec5 c) ?_
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  · intro i; fin_cases i <;> decide
  · intro i
    fin_cases i
    · exact (negWordVir_L5vac c).symm
    · exact (negWordVir_L3L2vac c).symm

/-- There are exactly two partitions of five with parts at least two. The established weight-space dimension therefore matches the two explicit vectors, allowing independence to be promoted to a basis. -/
theorem card_fin_two_eq : Fintype.card (Fin 2) = finrank ℂ ((virasoroVOA c).grading 5) := by
  rw [Fintype.card_fin]
  exact (finrank_gradingVir_five c).symm

/-- An honest basis of `𝒱₅`. -/
noncomputable def basis5 : Basis (Fin 2) ℂ ((virasoroVOA c).grading 5) :=
  haveI := (virasoroVOA c).finrank 5
  Basis.mk (vec5_linearIndependent c)
    (((vec5_linearIndependent c).span_eq_top_of_card_eq_finrank (card_fin_two_eq c)).ge)

/-- The abstract weight-five basis consists of the two displayed partition
states; the basis constructor changes no vectors. -/
@[simp] theorem basis5_apply (i : Fin 2) : basis5 c i = vec5 c i := Basis.mk_apply _ _ i

/-- `(L₋₆|0⟩, L₋₄L₋₂|0⟩, L₋₃L₋₃|0⟩, L₋₂³|0⟩)` inside `𝒱₆`. -/
noncomputable def vec6 : Fin 4 → (virasoroVOA c).grading 6 :=
  ![⟨L6vac c, L6vac_mem c⟩, ⟨L4L2vac c, L4L2vac_mem c⟩,
    ⟨L3L3vac c, L3L3vac_mem c⟩, ⟨L222vac c, L222vac_mem c⟩]

/-- The four weight-six descendants are independent in the UNIVERSAL module.
They correspond to four distinct sorted partition words; this does not claim
their images stay independent in a minimal-model quotient. -/
theorem vec6_linearIndependent : LinearIndependent ℂ (vec6 c) := by
  refine indep_of_words c ![[4], [2, 0], [1, 1], [0, 0, 0]] ?_ ?_ (vec6 c) ?_
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  · intro i; fin_cases i <;> decide
  · intro i
    fin_cases i
    · exact (negWordVir_L6vac c).symm
    · exact (negWordVir_L4L2vac c).symm
    · exact (negWordVir_L3L3vac c).symm
    · exact (negWordVir_L222vac c).symm

/-- Weight six in the universal vacuum module has dimension four. Together
with independence, this makes the four listed descendants a complete basis. -/
theorem card_fin_four_eq : Fintype.card (Fin 4) = finrank ℂ ((virasoroVOA c).grading 6) := by
  rw [Fintype.card_fin]
  exact (finrank_gradingVir_six c).symm

/-- An honest basis of `𝒱₆`. -/
noncomputable def basis6 : Basis (Fin 4) ℂ ((virasoroVOA c).grading 6) :=
  haveI := (virasoroVOA c).finrank 6
  Basis.mk (vec6_linearIndependent c)
    (((vec6_linearIndependent c).span_eq_top_of_card_eq_finrank (card_fin_four_eq c)).ge)

/-- The abstract basis evaluates to the concrete four descendant states,
so matrix kernel coefficients translate into actual state relations. -/
@[simp] theorem basis6_apply (i : Fin 4) : basis6 c i = vec6 c i := Basis.mk_apply _ _ i

/-- `canGram5` **is** the canonical Gram matrix of `Core/GradedFormMatrix` at level `5`. -/
theorem canGram_basis5 :
    GramMat.canGram (vacVec_ne_zero c) (virasoroVOA_qp c) 5 (basis5 c) = canGram5 c := by
  ext i j
  rw [GramMat.canGram_apply, canGram5]
  fin_cases i <;> fin_cases j <;> simp [vec5, VirGram4.canB]

/-- `canGram6` **is** the canonical Gram matrix of `Core/GradedFormMatrix` at level `6`. -/
theorem canGram_basis6 :
    GramMat.canGram (vacVec_ne_zero c) (virasoroVOA_qp c) 6 (basis6 c) = canGram6 c := by
  ext i j
  rw [GramMat.canGram_apply, canGram6]
  fin_cases i <;> fin_cases j <;> simp [vec6, VirGram4.canB]

/-! ## §7  **D3 at levels 5 and 6**: the determinant is a *nonzero* polynomial in `c`

`Core/GradedFormMatrix.finrank_maxQuotient_grading_lt_of_det_eq_zero` needs, at a degenerate
parameter `c₀`, a *comparison* point where the determinant does not vanish.  That is exactly the
statement that the level-`n` determinant is not identically zero — "the universal Virasoro VOA is
simple at level `n` for generic `c`".  At levels `2,3,4,5,6` it is a computation:

| `n` | `det canGram_n c` | vanishes at |
|---|---|---|
| 2 | `-c/2` | `0` |
| 3 | `-2c` | `0` |
| 4 | `c²(5c+22)/2` | `0`, `-22/5` |
| 5 | `2c²(5c+22)` | `0`, `-22/5` |
| 6 | `(3/4)c⁴(2c-1)(5c+22)²(7c+68)` | `0`, `1/2`, `-22/5`, `-68/7` |

⚠ There is **no** uniform-in-`n` version of this in the repository, and the file claims none: see
the `⚠` in `Examples/VirasoroSimpleGram` §5. -/

/-- **D3 at level 5.**  `det canGram5` is not the zero polynomial: it is `54 ≠ 0` at `c = 1`. -/
theorem det_canGram5_ne_zero_at_one : (canGram5 1).det ≠ 0 := by
  rw [det_canGram5]
  norm_num

/-- **D3 at level 6.**  `det canGram6` is not the zero polynomial. -/
theorem det_canGram6_ne_zero_at_one : (canGram6 1).det ≠ 0 := by
  rw [det_canGram6]
  norm_num

/-- The level-6 determinant vanishes at the Ising charge. -/
theorem det_canGram6_ising : (canGram6 isingC).det = 0 :=
  (det_canGram6_eq_zero_iff isingC).mpr (Or.inr (Or.inl rfl))

/-- The level-6 determinant vanishes at the `M(2,7)` charge. -/
theorem det_canGram6_m27 : (canGram6 m27C).det = 0 :=
  (det_canGram6_eq_zero_iff m27C).mpr (Or.inr (Or.inr (Or.inr rfl)))

/-- The level-6 determinant vanishes at the Lee–Yang charge. -/
theorem det_canGram6_leeYang : (canGram6 leeYangC).det = 0 :=
  (det_canGram6_eq_zero_iff leeYangC).mpr (Or.inr (Or.inr (Or.inl rfl)))

/-- ⚠ **Level 5 sees nothing new**: the Ising and `M(2,7)` charges are *not* degenerate at
level 5.  This is why level 6 is the first informative level beyond `VirasoroGram4`. -/
theorem det_canGram5_ising_ne_zero : (canGram5 isingC).det ≠ 0 := by
  rw [det_canGram5, isingC]
  norm_num

/-- At charge -68/7, the weight-five canonical Gram matrix is invertible. The M(2,7) singular relation first appears at the next weight, so weight five alone cannot detect that model. -/
theorem det_canGram5_m27_ne_zero : (canGram5 m27C).det ≠ 0 := by
  rw [det_canGram5, m27C]
  norm_num

end VOA.VirGram56
