/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.RootEnumNodup
import VOA.AffineGeneral.CartanLatticeSimple

/-!
# Root counts of `D₄`, `E₆`, `E₇`, `E₈` and the dimensions of their Lie algebras

The `LDLᵀ` decompositions of `CartanLattices` (`sos_D4`, …) feed the pruned enumeration of
`RootEnum`: `card_normEq_eq` identifies the roots of `ofCartan G` with the enumerated norm-`2` lists.
The counts `24, 72, 126, 240` are then checked by `decide +kernel` on the pruned search tree
(kernel reduction only), and `finrank_V1` gives `dim 𝔰𝔬₈ = 28`, `dim 𝔢₆ = 78`, `dim 𝔢₇ = 133`
(and again `dim 𝔢₈ = 248`, independently of the modular-form count in `E8Dimension`).
-/

namespace VOA.AffineGeneral.RootCounts

open VOA.CartanLattices VOA.LatGen VOA.AffineGeneral.RootEnum VOA.AffineGeneral.LatticeLie
  VOA.AffineGeneral.CartanSimple

noncomputable section

/-- The enumerated roots. -/
def rootList (rows : List Row) : List (List ℤ) :=
  (enum 2 rows).filter fun s => decide (tailSum rows s = 2)

/-- **Roots of `ofCartan G` = enumerated norm-`2` lists**, as finsets. -/
theorem image_normEq_eq {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hG : G.IsSymm)
    (hPos : (ofCartan G hG).PosDef) (rows : List Row) (hlen : rows.length = n)
    (hadm : Admissible 2 rows)
    (hid : ∀ v : Fin n → ℤ, ((Matrix.toBilin' G v v : ℤ) : ℚ) = tailSum rows (List.ofFn v)) :
    (normEq (ofCartan G hG) hPos 2).image (fun v : (ofCartan G hG).carrier => List.ofFn (n := n) v)
      = (rootList rows).toFinset := by
  classical
  ext s
  rw [Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_normEq] at hv
    have h2 : tailSum rows (List.ofFn v) = 2 := by
      rw [← hid]; exact_mod_cast hv
    unfold rootList
    rw [List.mem_filter]
    exact ⟨mem_enum 2 rows hadm _ (by rw [List.length_ofFn, hlen]) h2.le, decide_eq_true h2⟩
  · intro hs
    unfold rootList at hs
    rw [List.mem_filter] at hs
    obtain ⟨hs1, hs2⟩ := hs
    have hl : s.length = n := (length_of_mem_enum 2 rows s hs1).trans hlen
    subst hl
    refine ⟨fun i => s[i], ?_, List.ofFn_getElem⟩
    rw [mem_normEq]
    have h2 : tailSum rows s = 2 := of_decide_eq_true hs2
    have hs : List.ofFn (fun i : Fin s.length => s[i]) = s := List.ofFn_getElem
    have := hid (fun i => s[i])
    rw [hs, h2] at this
    exact_mod_cast this

/-- **Roots of `ofCartan G` = enumerated norm-`2` lists**, counted. -/
theorem card_normEq_eq {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hG : G.IsSymm)
    (hPos : (ofCartan G hG).PosDef) (rows : List Row) (hlen : rows.length = n)
    (hadm : Admissible 2 rows)
    (hid : ∀ v : Fin n → ℤ, ((Matrix.toBilin' G v v : ℤ) : ℚ) = tailSum rows (List.ofFn v))
    (hnd : (rootList rows).Nodup) :
    (normEq (ofCartan G hG) hPos 2).card = (rootList rows).length := by
  classical
  have hinj : Function.Injective (fun v : (ofCartan G hG).carrier => List.ofFn (n := n) v) :=
    fun a b h => List.ofFn_injective h
  rw [← Finset.card_image_of_injective (normEq (ofCartan G hG) hPos 2) hinj,
    image_normEq_eq G hG hPos rows hlen hadm hid, List.toFinset_card_of_nodup hnd]

/-! ## The rows -/

def a2Rows : List Row := [⟨2, [-1/2], 1⟩, ⟨3/2, [], 2⟩]

def d4Rows : List Row :=
  [⟨2, [-1/2, 0, 0], 1⟩, ⟨3/2, [-2/3, -2/3], 2⟩, ⟨4/3, [-1/2], 2⟩, ⟨1, [], 2⟩]

def e6Rows : List Row :=
  [⟨2, [0, -1/2, 0, 0, 0], 1⟩, ⟨2, [0, -1/2, 0, 0], 1⟩, ⟨3/2, [-2/3, 0, 0], 2⟩,
   ⟨5/6, [-6/5, 0], 2⟩, ⟨4/5, [-5/4], 2⟩, ⟨3/4, [], 2⟩]

def e7Rows : List Row :=
  [⟨2, [0, -1/2, 0, 0, 0, 0], 1⟩, ⟨2, [0, -1/2, 0, 0, 0], 1⟩, ⟨3/2, [-2/3, 0, 0, 0], 2⟩,
   ⟨5/6, [-6/5, 0, 0], 2⟩, ⟨4/5, [-5/4, 0], 2⟩, ⟨3/4, [-4/3], 2⟩, ⟨2/3, [], 2⟩]

def e8Rows : List Row :=
  [⟨2, [0, -1/2, 0, 0, 0, 0, 0], 1⟩, ⟨2, [0, -1/2, 0, 0, 0, 0], 1⟩, ⟨3/2, [-2/3, 0, 0, 0, 0], 2⟩,
   ⟨5/6, [-6/5, 0, 0, 0], 2⟩, ⟨4/5, [-5/4, 0, 0], 2⟩, ⟨3/4, [-4/3, 0], 2⟩, ⟨2/3, [-3/2], 2⟩,
   ⟨1/2, [], 2⟩]

theorem a2_id (v : Fin 2 → ℤ) :
    ((Matrix.toBilin' (CartanMatrix.A 2) v v : ℤ) : ℚ) = tailSum a2Rows (List.ofFn v) := by
  rw [sos_A2]; simp [tailSum, term, dotQ, a2Rows, List.ofFn_succ]

theorem d4_id (v : Fin 4 → ℤ) :
    ((Matrix.toBilin' (CartanMatrix.D 4) v v : ℤ) : ℚ) = tailSum d4Rows (List.ofFn v) := by
  rw [sos_D4]; simp [tailSum, term, dotQ, d4Rows, List.ofFn_succ]; ring

theorem e6_id (v : Fin 6 → ℤ) :
    ((Matrix.toBilin' CartanMatrix.E₆ v v : ℤ) : ℚ) = tailSum e6Rows (List.ofFn v) := by
  rw [sos_E6]; simp [tailSum, term, dotQ, e6Rows, List.ofFn_succ]; ring

theorem e7_id (v : Fin 7 → ℤ) :
    ((Matrix.toBilin' CartanMatrix.E₇ v v : ℤ) : ℚ) = tailSum e7Rows (List.ofFn v) := by
  rw [sos_E7]; simp [tailSum, term, dotQ, e7Rows, List.ofFn_succ]; ring

theorem e8_id (v : Fin 8 → ℤ) :
    ((Matrix.toBilin' CartanMatrix.E₈ v v : ℤ) : ℚ) = tailSum e8Rows (List.ofFn v) := by
  rw [sos_E8]; simp [tailSum, term, dotQ, e8Rows, List.ofFn_succ]; ring

theorem a2_adm : Admissible 2 a2Rows := by unfold Admissible; decide +kernel
theorem d4_adm : Admissible 2 d4Rows := by unfold Admissible; decide +kernel
theorem e6_adm : Admissible 2 e6Rows := by unfold Admissible; decide +kernel
theorem e7_adm : Admissible 2 e7Rows := by unfold Admissible; decide +kernel
theorem e8_adm : Admissible 2 e8Rows := by unfold Admissible; decide +kernel

theorem a2_nodup : (rootList a2Rows).Nodup :=
  List.Pairwise.filter _ (enum_nodup 2 a2Rows)
theorem d4_nodup : (rootList d4Rows).Nodup :=
  List.Pairwise.filter _ (enum_nodup 2 d4Rows)
theorem e6_nodup : (rootList e6Rows).Nodup :=
  List.Pairwise.filter _ (enum_nodup 2 e6Rows)
theorem e7_nodup : (rootList e7Rows).Nodup :=
  List.Pairwise.filter _ (enum_nodup 2 e7Rows)
theorem e8_nodup : (rootList e8Rows).Nodup :=
  List.Pairwise.filter _ (enum_nodup 2 e8Rows)

theorem a2_length : (rootList a2Rows).length = 6 := by decide +kernel
theorem d4_length : (rootList d4Rows).length = 24 := by decide +kernel
theorem e6_length : (rootList e6Rows).length = 72 := by decide +kernel
theorem e7_length : (rootList e7Rows).length = 126 := by decide +kernel
theorem e8_length : (rootList e8Rows).length = 240 := by decide +kernel

/-! ## Counts and dimensions -/

theorem card_roots_d4 : (normEq d4 d4_posDef 2).card = 24 := by
  exact (card_normEq_eq (CartanMatrix.D 4) _ d4_posDef d4Rows rfl d4_adm d4_id d4_nodup).trans d4_length

theorem card_roots_e6 : (normEq e6 e6_posDef 2).card = 72 := by
  exact (card_normEq_eq CartanMatrix.E₆ _ e6_posDef e6Rows rfl e6_adm e6_id e6_nodup).trans e6_length

theorem card_roots_e7 : (normEq e7 e7_posDef 2).card = 126 := by
  exact (card_normEq_eq CartanMatrix.E₇ _ e7_posDef e7Rows rfl e7_adm e7_id e7_nodup).trans e7_length

theorem card_roots_e8' : (normEq e8 e8_posDef 2).card = 240 := by
  exact (card_normEq_eq CartanMatrix.E₈ _ e8_posDef e8Rows rfl e8_adm e8_id e8_nodup).trans e8_length

/-- **`dim 𝔰𝔬₈ = 28`.** -/
theorem finrank_d4Lie : Module.finrank ℂ d4Lie = 28 := by
  rw [finrank_V1, card_roots_d4, show d4.rank = 4 from DeligneLatticeLie.rank_ofCartan _ _]

/-- **`dim 𝔢₆ = 78`.** -/
theorem finrank_e6Lie : Module.finrank ℂ e6Lie = 78 := by
  rw [finrank_V1, card_roots_e6, show e6.rank = 6 from DeligneLatticeLie.rank_ofCartan _ _]

/-- **`dim 𝔢₇ = 133`.** -/
theorem finrank_e7Lie : Module.finrank ℂ e7Lie = 133 := by
  rw [finrank_V1, card_roots_e7, show e7.rank = 7 from DeligneLatticeLie.rank_ofCartan _ _]

/-- **`dim 𝔢₈ = 248`**, by enumeration. -/
theorem finrank_e8Lie' : Module.finrank ℂ e8Lie = 248 := by
  rw [finrank_V1, card_roots_e8', show e8.rank = 8 from DeligneLatticeLie.rank_ofCartan _ _]

end

end VOA.AffineGeneral.RootCounts
