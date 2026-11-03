/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTConjIdentityCubicStep

/-!
# The step operator for a `c` creation mode

For `X = c^a_{-k}` (`k ≥ 1`, vertex index `-k-1`) the step operator `K_p` of
`BRSTConjIdentityCubicStep` is a combination of the canonical bilinears
`T b c j = c^c_{(-k-j-1)} b^b_{(j)} y` and `U b c = c^c_{(-k-1)} c^b_{(-1)} y` with coefficients
that vanish by three colour identities of `sl₂` with the weights `w = (1, 1, 2)`
(`colour_id1`, `colour_id2`); hence `K_p = 0` (`Kp_c_zero`).

Everything is proved outright.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open VOA.SympFerm VOA.Ghost AffineVOA
open scoped TensorProduct

noncomputable section

local notation "adjC" => AffineVOA.HighestModule.adjointColour

/-! ### Colour identities -/

theorem colour_id1 (a b c : Fin 3) :
    fabc a b c * (colourW c : ℂ) + (colourW a : ℂ) * fabc (adjC b) c a = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [fabc, colourW, AffineVOA.HighestModule.adjointColour]

theorem colour_id2 (a b c : Fin 3) :
    fabc (adjC a) c b * (colourW b : ℂ) = fabc a b c * (colourW c : ℂ) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [fabc, colourW, AffineVOA.HighestModule.adjointColour]

theorem colour_id3 (a b i : Fin 3) :
    fabc (adjC b) a i * (colourW i : ℂ) = (colourW a : ℂ) * fabc b i a := by
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    simp [fabc, colourW, AffineVOA.HighestModule.adjointColour]

theorem casimir_contract (b c a : Fin 3) :
    ∑ q : Fin 3, casimir b q * fabc q c a = fabc (adjC b) c a / (colourW b : ℂ) := by
  fin_cases b <;> simp [Fin.sum_univ_three, casimir, colourW,
    AffineVOA.HighestModule.adjointColour] <;> ring

theorem casimir_contract' (b c a : Fin 3) :
    ∑ p : Fin 3, casimir p b * fabc p c a = fabc (adjC b) c a / (colourW b : ℂ) := by
  rw [← casimir_contract]
  exact Finset.sum_congr rfl fun q _ => by rw [casimir_symm]

theorem casimir_current (a : Fin 3) (n : ℤ) (z : Sl2GhostSpace) :
    ∑ p : Fin 3, casimir p a • ghostJ p n z = (1 / (colourW a : ℂ)) • ghostJ (adjC a) n z := by
  fin_cases a <;> simp [Fin.sum_univ_three, casimir, colourW,
    AffineVOA.HighestModule.adjointColour]

/-! ### Reordering -/

theorem gMode_anti (a b : Fin 3) (e1 e2 : Fin 2) (m n : ℤ)
    (h : ¬ (a = b ∧ e1 + 1 = e2 ∧ m + n + 1 = 0)) (z : Sl2GhostSpace) :
    gMode a e1 m (gMode b e2 n z) = -gMode b e2 n (gMode a e1 m z) := by
  have h' := gMode_anticomm_apply a b e1 e2 m n z
  rw [if_neg h] at h'
  exact eq_neg_of_add_eq_zero_left h'

theorem bc_anti (b c : Fin 3) (j t : ℤ) (h : j + t + 1 ≠ 0) (z : Sl2GhostSpace) :
    gMode b 0 j (gMode c 1 t z) = -gMode c 1 t (gMode b 0 j z) :=
  gMode_anti b c 0 1 j t (fun h' => h h'.2.2) z

theorem cb_anti (c b : Fin 3) (t j : ℤ) (h : t + j + 1 ≠ 0) (z : Sl2GhostSpace) :
    gMode c 1 t (gMode b 0 j z) = -gMode b 0 j (gMode c 1 t z) :=
  gMode_anti c b 1 0 t j (fun h' => h h'.2.2) z

theorem cc_anti (c b : Fin 3) (t s : ℤ) (z : Sl2GhostSpace) :
    gMode c 1 t (gMode b 1 s z) = -gMode b 1 s (gMode c 1 t z) :=
  gMode_anti c b 1 1 t s (fun h' => absurd h'.2.1 (by decide)) z

theorem bb_anti (c b : Fin 3) (t s : ℤ) (z : Sl2GhostSpace) :
    gMode c 0 t (gMode b 0 s z) = -gMode b 0 s (gMode c 0 t z) :=
  gMode_anti c b 0 0 t s (fun h' => absurd h'.2.1 (by decide)) z

/-- For nonzero total index, the normal-ordered `bc` term is `-c b`. -/
theorem NOterm_bc (c b : Fin 3) {n : ℤ} (hn : n ≠ 0) (j : ℤ) (z : Sl2GhostSpace) :
    NOterm c 0 b 1 n j z = -(gMode b 1 (n - j - 1) (gMode c 0 j z)) := by
  unfold NOterm
  split_ifs with hj
  · exact bc_anti c b j (n - j - 1) (by omega) z
  · rfl

/-! ### The canonical bilinears -/

/-- `c^c_{(-k-j-1)} b^b_{(j)} y`. -/
abbrev Tc (k : ℕ) (y : Sl2GhostSpace) (b c : Fin 3) (j : ℤ) : Sl2GhostSpace :=
  gMode c 1 (-(k : ℤ) - j - 1) (gMode b 0 j y)

/-- `c^c_{(-k-1)} c^b_{(-1)} y`. -/
abbrev Uc (k : ℕ) (y : Sl2GhostSpace) (b c : Fin 3) : Sl2GhostSpace :=
  gMode c 1 (-(k : ℤ) - 1) (gMode b 1 (-1) y)

theorem Tc_zero {k : ℕ} {y : Sl2GhostSpace} (hC : C0 y) (b c : Fin 3) : Tc k y b c 0 = 0 := by
  have h : gMode b 0 0 y = 0 := by
    have := b0_P0 b y; rwa [show P0 y = y from hC] at this
  simp only [Tc, h, map_zero]

theorem Tc_out {k N W : ℕ} (hk : 1 ≤ k) (hWN : W + k ≤ N) {y : Sl2GhostSpace}
    (hy : y ∈ sl2GhostSVA.grading (W : ℂ)) (b c : Fin 3) {j : ℤ}
    (hj : j ∉ Finset.Icc (-(N : ℤ)) N) : Tc k y b c j = 0 := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hj
  rcases hj with hj | hj
  · rw [Tc, cb_anti c b _ j (by omega), cMode_kill c hy (by omega), map_zero, neg_zero]
  · rw [Tc, bMode_kill b hy (by omega), map_zero]

theorem triple_sum_swap {V : Type*} [AddCommMonoid V] (S : Finset ℤ) (f : Fin 3 → Fin 3 → ℤ → V) :
    ∑ b : Fin 3, ∑ c : Fin 3, ∑ j ∈ S, f b c j = ∑ j ∈ S, ∑ c : Fin 3, ∑ b : Fin 3, f b c j := by
  calc ∑ b : Fin 3, ∑ c : Fin 3, ∑ j ∈ S, f b c j
      = ∑ b : Fin 3, ∑ j ∈ S, ∑ c : Fin 3, f b c j :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ j ∈ S, ∑ b : Fin 3, ∑ c : Fin 3, f b c j := Finset.sum_comm
    _ = ∑ j ∈ S, ∑ c : Fin 3, ∑ b : Fin 3, f b c j :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm

/-- The current in canonical form. -/
theorem ghostJ_canon (a : Fin 3) {k N W : ℕ} (hk : 1 ≤ k) (hWN : W + k ≤ N) {y : Sl2GhostSpace}
    (hy : y ∈ sl2GhostSVA.grading (W : ℂ)) :
    ghostJ a (-(k : ℤ)) y = ∑ j ∈ Finset.Icc (-(N : ℤ)) N, ∑ b : Fin 3, ∑ c : Fin 3,
      (-fabc a c b) • Tc k y b c j := by
  rw [ghostJ_window a (-(k : ℤ)) hy N (by omega) (by omega)]
  have hk0 : (-(k : ℤ)) ≠ 0 := by omega
  simp only [NOterm_bc _ _ hk0, Finset.smul_sum]
  rw [triple_sum_swap (Finset.Icc (-(N : ℤ)) N)
    (fun b' c' j => fabc a b' c' • -gMode b' 1 (-(k : ℤ) - j - 1) (gMode c' 0 j y))]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  rw [smul_neg, ← neg_smul]

/-! ### The conjugated current -/

theorem C0_ghostConj {y : Sl2GhostSpace} (hC : C0 y) : C0 (ghostConj y) := by
  unfold C0 at *; rw [← ghostConj_P0, hC]

/-- The coefficient of the conjugated current, by the original `b` index `j0`. -/
def CiA (k : ℕ) (b c : Fin 3) (j0 : ℤ) : ℂ :=
  if j0 = 0 ∨ j0 = -(k : ℤ) then 0
  else (((j0 : ℝ) * colourW c / (((k : ℝ) + j0) * colourW b) : ℝ) : ℂ)

theorem conj_NO {k : ℕ} (hk : 1 ≤ k) {y : Sl2GhostSpace} (hC : C0 y) (b c : Fin 3) (j0 : ℤ) :
    ghostConj (NOterm c 0 b 1 (-(k : ℤ)) j0 (ghostConj y)) =
      (if j0 = -(k : ℤ) then ((((k : ℝ) * colourW c) : ℝ) : ℂ) • Uc k y b c else 0) +
        CiA k b c j0 • Tc k y b c (-(k : ℤ) - j0) := by
  have hk0 : (-(k : ℤ)) ≠ 0 := by omega
  have hCr : C0 (ghostConj y) := C0_ghostConj hC
  rw [NOterm_bc _ _ hk0, map_neg]
  by_cases h0 : j0 = 0
  · subst h0
    have h : gMode c 0 0 (ghostConj y) = 0 := by
      have := b0_P0 c (ghostConj y); rwa [show P0 (ghostConj y) = ghostConj y from hCr] at this
    rw [h, map_zero, map_zero, neg_zero, if_neg (by omega), CiA, if_pos (Or.inl rfl), zero_smul,
      add_zero]
  by_cases hk' : j0 = -(k : ℤ)
  · subst hk'
    rw [if_pos rfl, CiA, if_pos (Or.inr rfl), zero_smul, add_zero,
      show -(k : ℤ) - -(k : ℤ) - 1 = -1 by ring, ghostConj_c0, ghostConj_bmode c hk0, ghostConj_sq,
      map_smul, Ppar_gMode, Ppar_Ppar, map_smul, map_neg, smul_neg, Uc, cc_anti c b]
    rw [show (((((-(k : ℤ) : ℤ) : ℝ) * colourW c : ℝ)) : ℂ) = -((((k : ℝ) * colourW c) : ℝ) : ℂ) by
      push_cast; ring, neg_smul]
    simp only [neg_neg, smul_neg]
  · have ht : -(k : ℤ) - j0 - 1 ≠ -1 := by omega
    rw [if_neg hk', zero_add, CiA, if_neg (by tauto), ghostConj_cmode b ht, ghostConj_bmode c h0,
      ghostConj_sq, map_smul, Ppar_gMode, Ppar_Ppar, map_smul, map_neg,
      show -(k : ℤ) - j0 - 1 + 1 = -(k : ℤ) - j0 by ring,
      bc_anti b c _ _ (by omega), Tc,
      show -(k : ℤ) - (-(k : ℤ) - j0) - 1 = j0 - 1 by ring]
    have hkj : ((k : ℝ) + j0) ≠ 0 := by
      intro h; apply hk'; have : ((k : ℤ) + j0 : ℝ) = 0 := by push_cast; exact h
      exact_mod_cast (by linarith [this] : (j0 : ℝ) = -(k : ℝ))
    have hw : colourW b ≠ 0 := (colourW_pos b).ne'
    have hs : (((1 / ((((-(k : ℤ) - j0 - 1 : ℤ) : ℝ) + 1) * colourW b)) : ℝ) : ℂ) *
        (((j0 : ℝ) * colourW c : ℝ) : ℂ) =
        -((((j0 : ℝ) * colourW c / (((k : ℝ) + j0) * colourW b)) : ℝ) : ℂ) := by
      push_cast
      rw [show (-(k : ℂ) - j0 - 1 + 1) = -((k : ℂ) + j0) by ring]
      have hkj' : ((k : ℂ) + j0) ≠ 0 := by exact_mod_cast hkj
      have hw' : (colourW b : ℂ) ≠ 0 := by exact_mod_cast hw
      field_simp
      try ring
    simp only [smul_neg, neg_neg, smul_smul, hs, neg_smul]

theorem sum_reflect {V : Type*} [AddCommMonoid V] (N k : ℤ) (hk : 0 ≤ k) (H : ℤ → V)
    (hH : ∀ j, j ∉ Finset.Icc (-N) (N - k) → H j = 0) :
    ∑ j0 ∈ Finset.Icc (-N) N, H (-k - j0) = ∑ j ∈ Finset.Icc (-N) N, H j := by
  have himg : (Finset.Icc (-N) N).image (fun j0 => -k - j0) = Finset.Icc (-N - k) (N - k) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨j0, ⟨h1, h2⟩, rfl⟩; omega
    · intro h; exact ⟨-k - j, by omega, by ring⟩
  rw [← Finset.sum_image (f := H) (fun x _ y _ h => by simpa using h), himg]
  have h1 : ∑ j ∈ Finset.Icc (-N) (N - k), H j = ∑ j ∈ Finset.Icc (-N - k) (N - k), H j :=
    Finset.sum_subset (fun j hj => by simp only [Finset.mem_Icc] at hj ⊢; omega)
      (fun j _ hj => hH j hj)
  have h2 : ∑ j ∈ Finset.Icc (-N) (N - k), H j = ∑ j ∈ Finset.Icc (-N) N, H j :=
    Finset.sum_subset (fun j hj => by simp only [Finset.mem_Icc] at hj ⊢; omega)
      (fun j _ hj => hH j hj)
  rw [← h1, h2]

theorem sum_ite_single {V : Type*} [AddCommMonoid V] (S : Finset ℤ) (j1 : ℤ) (h : j1 ∈ S) (v : V) :
    ∑ j0 ∈ S, (if j0 = j1 then v else 0) = v := by
  rw [Finset.sum_ite_eq' S j1 (fun _ => v), if_pos h]

/-- **The conjugated current in canonical form.** -/
theorem conjJ_canon (a : Fin 3) {k N W : ℕ} (hk : 1 ≤ k) (hWN : W + k ≤ N) {y : Sl2GhostSpace}
    (hy : y ∈ sl2GhostSVA.grading (W : ℂ)) (hC : C0 y) :
    ghostConj (ghostJ a (-(k : ℤ)) (ghostConj y)) =
      (∑ j ∈ Finset.Icc (-(N : ℤ)) N, ∑ b : Fin 3, ∑ c : Fin 3,
        (fabc a b c * CiA k b c (-(k : ℤ) - j)) • Tc k y b c j) +
      ∑ b : Fin 3, ∑ c : Fin 3, (fabc a b c * ((((k : ℝ) * colourW c) : ℝ) : ℂ)) • Uc k y b c := by
  rw [ghostJ_window a (-(k : ℤ)) (ghostConj_grading hy) N (by omega) (by omega)]
  simp only [map_sum, LinearMap.map_smulₛₗ, conj_fabc, conj_NO hk hC, Finset.sum_add_distrib,
    smul_add]
  have hmem : -(k : ℤ) ∈ Finset.Icc (-(N : ℤ)) N := by simp only [Finset.mem_Icc]; omega
  simp only [sum_ite_single _ _ hmem]
  have hrefl : ∀ b c : Fin 3, ∑ j0 ∈ Finset.Icc (-(N : ℤ)) N, CiA k b c j0 • Tc k y b c (-(k : ℤ) - j0) =
      ∑ j ∈ Finset.Icc (-(N : ℤ)) N, CiA k b c (-(k : ℤ) - j) • Tc k y b c j := by
    intro b c
    have := sum_reflect (N : ℤ) (k : ℤ) (by omega)
      (fun j => CiA k b c (-(k : ℤ) - j) • Tc k y b c j) (fun j hj => by
        by_cases hj' : j ∈ Finset.Icc (-(N : ℤ)) N
        · simp only [Finset.mem_Icc] at hj hj'
          have hjW : (W : ℤ) < j := by omega
          simp only [Tc, bMode_kill b hy hjW, map_zero, smul_zero]
        · simp only [Tc_out hk hWN hy b c hj', smul_zero])
    simpa only [show ∀ j0 : ℤ, -(k : ℤ) - (-(k : ℤ) - j0) = j0 from fun j0 => by ring] using this
  simp only [hrefl, Finset.smul_sum, smul_smul]
  rw [add_comm]
  congr 1
  rw [triple_sum_swap]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Finset.sum_comm

/-! ### The zero-mode and `E` pieces -/

/-- The zero-mode piece. -/
theorem zero_piece (a : Fin 3) (k : ℕ) (y : Sl2GhostSpace) :
    (∑ b : Fin 3, gMode b 1 (-1) (ghostJ (adjC b) 0 (gMode a 1 (-(k : ℤ) - 1) y) -
      gMode a 1 (-(k : ℤ) - 1) (ghostJ (adjC b) 0 y))) =
      ∑ b : Fin 3, ∑ c : Fin 3, fabc (adjC b) c a • Uc k y b c := by
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ghostJ_gMode (adjC b) a 1 0 (-(k : ℤ) - 1) y, add_sub_cancel_left, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, coefJ, if_neg (by decide), add_zero, cc_anti b c, smul_neg, ← neg_smul, neg_neg]

theorem A1_piece (a p q : Fin 3) {k : ℕ} (hk : 1 ≤ k) (m : ℤ) (hm : 1 ≤ m) (y : Sl2GhostSpace) :
    gMode p 0 (-m) (ghostJ q m (gMode a 1 (-(k : ℤ) - 1) y)) +
      gMode a 1 (-(k : ℤ) - 1) (gMode p 0 (-m) (ghostJ q m y)) =
      ∑ i : Fin 3, fabc q i a • Tc k y p i (-m) := by
  have hS : gMode p 0 (-m) (∑ i : Fin 3, coefJ q a i 1 • gMode i 1 (-(k : ℤ) - 1 + m) y) =
      ∑ i : Fin 3, fabc q i a • Tc k y p i (-m) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, coefJ, if_neg (by decide), Tc,
      show -(k : ℤ) - 1 + m = -(k : ℤ) - -m - 1 by ring, bc_anti p i (-m) _ (by omega), smul_neg,
      ← neg_smul, neg_neg]
  rw [ghostJ_gMode q a 1 m (-(k : ℤ) - 1) y, map_add, bc_anti p a (-m) _ (by omega), hS]
  abel

theorem A2_piece (a p q : Fin 3) (k : ℕ) (m : ℤ) (y : Sl2GhostSpace) :
    ghostJ p (-m) (gMode q 0 m (gMode a 1 (-(k : ℤ) - 1) y)) +
      gMode a 1 (-(k : ℤ) - 1) (ghostJ p (-m) (gMode q 0 m y)) =
      (∑ i : Fin 3, fabc p i a • Tc k y q i m) +
        (if q = a ∧ m = (k : ℤ) then ghostJ p (-m) y else 0) := by
  have hqa := gMode_anticomm_apply q a 0 1 m (-(k : ℤ) - 1) y
  have hc : (q = a ∧ (0 : Fin 2) + 1 = 1 ∧ m + (-(k : ℤ) - 1) + 1 = 0) ↔ (q = a ∧ m = (k : ℤ)) := by
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, rfl, by omega⟩
  have hβ : gMode q 0 m (gMode a 1 (-(k : ℤ) - 1) y) =
      -gMode a 1 (-(k : ℤ) - 1) (gMode q 0 m y) + (if q = a ∧ m = (k : ℤ) then y else 0) := by
    rw [eq_neg_add_iff_add_eq, add_comm, hqa]
    by_cases h : q = a ∧ m = (k : ℤ)
    · rw [if_pos (hc.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]
  have hS : (∑ i : Fin 3, coefJ p a i 1 • gMode i 1 (-(k : ℤ) - 1 + -m) (gMode q 0 m y)) =
      -∑ i : Fin 3, fabc p i a • Tc k y q i m := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coefJ, if_neg (by decide), Tc, show -(k : ℤ) - 1 + -m = -(k : ℤ) - m - 1 by ring,
      neg_smul]
  have hI : ghostJ p (-m) (if q = a ∧ m = (k : ℤ) then y else 0) =
      (if q = a ∧ m = (k : ℤ) then ghostJ p (-m) y else 0) := by
    split_ifs <;> simp
  rw [hβ, map_add, map_neg, ghostJ_gMode p a 1 (-m) (-(k : ℤ) - 1), hS, hI]
  abel

/-- The contracted colour coefficient. -/
def DA (a b c : Fin 3) : ℂ := fabc (adjC b) c a / (colourW b : ℂ)

theorem Egh_apply (N : ℕ) (z : Sl2GhostSpace) :
    Egh N z = ∑ m ∈ Finset.Icc 1 N, (1 / (m : ℂ)) •
      ((∑ p : Fin 3, ∑ q : Fin 3, casimir p q • gMode p 0 (-(m : ℤ)) (ghostJ q m z)) -
        ∑ p : Fin 3, ∑ q : Fin 3, casimir p q • ghostJ p (-(m : ℤ)) (gMode q 0 m z)) := by
  simp only [Egh, closedE, casContract, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.mul_apply]

theorem sum2_add_map {V : Type*} [AddCommGroup V] [Module ℂ V] (L : V →ₗ[ℂ] V)
    (K : Fin 3 → Fin 3 → ℂ) (X Y : Fin 3 → Fin 3 → V) :
    (∑ p : Fin 3, ∑ q : Fin 3, K p q • X p q) + L (∑ p : Fin 3, ∑ q : Fin 3, K p q • Y p q) =
      ∑ p : Fin 3, ∑ q : Fin 3, K p q • (X p q + L (Y p q)) := by
  simp only [map_sum, map_smul, ← Finset.sum_add_distrib, smul_add]

/-- One level of the anticommutator of `E` with `c^a_{-k}`. -/
theorem E_level (a : Fin 3) {k : ℕ} (hk : 1 ≤ k) (m : ℕ) (hm : 1 ≤ m) (y : Sl2GhostSpace) :
    ((∑ p : Fin 3, ∑ q : Fin 3, casimir p q •
        gMode p 0 (-(m : ℤ)) (ghostJ q m (gMode a 1 (-(k : ℤ) - 1) y))) -
      ∑ p : Fin 3, ∑ q : Fin 3, casimir p q •
        ghostJ p (-(m : ℤ)) (gMode q 0 m (gMode a 1 (-(k : ℤ) - 1) y))) +
    gMode a 1 (-(k : ℤ) - 1) ((∑ p : Fin 3, ∑ q : Fin 3, casimir p q •
        gMode p 0 (-(m : ℤ)) (ghostJ q m y)) -
      ∑ p : Fin 3, ∑ q : Fin 3, casimir p q • ghostJ p (-(m : ℤ)) (gMode q 0 m y)) =
    (∑ b : Fin 3, ∑ c : Fin 3, DA a b c • Tc k y b c (-(m : ℤ))) -
      (∑ b : Fin 3, ∑ c : Fin 3, DA a b c • Tc k y b c m) -
      ∑ p : Fin 3, ∑ q : Fin 3, casimir p q • (if q = a ∧ (m : ℤ) = (k : ℤ) then
        ghostJ p (-(m : ℤ)) y else 0) := by
  have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have h1 := sum2_add_map (gMode a 1 (-(k : ℤ) - 1)) casimir
    (fun p q => gMode p 0 (-(m : ℤ)) (ghostJ q m (gMode a 1 (-(k : ℤ) - 1) y)))
    (fun p q => gMode p 0 (-(m : ℤ)) (ghostJ q m y))
  have h2 := sum2_add_map (gMode a 1 (-(k : ℤ) - 1)) casimir
    (fun p q => ghostJ p (-(m : ℤ)) (gMode q 0 m (gMode a 1 (-(k : ℤ) - 1) y)))
    (fun p q => ghostJ p (-(m : ℤ)) (gMode q 0 m y))
  simp only [A1_piece a _ _ hk _ hm1] at h1
  simp only [A2_piece] at h2
  have e1 : (∑ p : Fin 3, ∑ q : Fin 3, casimir p q • ∑ i : Fin 3, fabc q i a • Tc k y p i (-(m : ℤ))) =
      ∑ b : Fin 3, ∑ c : Fin 3, DA a b c • Tc k y b c (-(m : ℤ)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul, casimir_contract, DA]
  have e2 : (∑ p : Fin 3, ∑ q : Fin 3, casimir p q •
      ((∑ i : Fin 3, fabc p i a • Tc k y q i m) +
        (if q = a ∧ (m : ℤ) = (k : ℤ) then ghostJ p (-(m : ℤ)) y else 0))) =
      (∑ b : Fin 3, ∑ c : Fin 3, DA a b c • Tc k y b c m) +
      ∑ p : Fin 3, ∑ q : Fin 3, casimir p q • (if q = a ∧ (m : ℤ) = (k : ℤ) then
        ghostJ p (-(m : ℤ)) y else 0) := by
    simp only [smul_add, Finset.sum_add_distrib]
    rw [add_left_inj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul, casimir_contract', DA]
  rw [e1] at h1
  rw [e2] at h2
  rw [map_sub, show ∀ A B C D : Sl2GhostSpace, (A - B) + (C - D) = (A + C) - (B + D) from
    fun A B C D => by abel, h1, h2]
  abel

theorem ite_level (a : Fin 3) (k N : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (y : Sl2GhostSpace) :
    ∑ m ∈ Finset.Icc 1 N, (1 / (m : ℂ)) • ∑ p : Fin 3, ∑ q : Fin 3, casimir p q •
      (if q = a ∧ (m : ℤ) = (k : ℤ) then ghostJ p (-(m : ℤ)) y else 0) =
      (1 / ((k : ℂ) * (colourW a : ℂ))) • ghostJ (adjC a) (-(k : ℤ)) y := by
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_Icc.mpr ⟨hk, hkN⟩) (fun m _ hmk => by
    simp only [show ¬ ((m : ℤ) = (k : ℤ)) from fun h => hmk (by exact_mod_cast h), and_false,
      if_false, smul_zero, Finset.sum_const_zero])]
  have h2 : ∀ p : Fin 3, (∑ q : Fin 3, casimir p q •
      (if q = a ∧ (k : ℤ) = (k : ℤ) then ghostJ p (-(k : ℤ)) y else 0)) =
      casimir p a • ghostJ p (-(k : ℤ)) y := by
    intro p
    rw [Finset.sum_eq_single a (fun q _ hq => by rw [if_neg (fun h => hq h.1), smul_zero])
      (by simp), if_pos ⟨rfl, rfl⟩]
  rw [Finset.sum_congr rfl fun p _ => h2 p, casimir_current, smul_smul, one_div_mul_one_div]

/-- **The `E` piece in canonical form.** -/
theorem E_piece (a : Fin 3) {k N : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) (y : Sl2GhostSpace) :
    -(Egh N (gMode a 1 (-(k : ℤ) - 1) y) + gMode a 1 (-(k : ℤ) - 1) (Egh N y)) =
      (∑ j ∈ Finset.Icc (-(N : ℤ)) N, ∑ b : Fin 3, ∑ c : Fin 3,
        (DA a b c / (j : ℂ)) • Tc k y b c j) +
      (1 / ((k : ℂ) * (colourW a : ℂ))) • ghostJ (adjC a) (-(k : ℤ)) y := by
  rw [Egh_apply, Egh_apply, map_sum]
  simp only [map_smul]
  rw [← Finset.sum_add_distrib]
  simp only [← smul_add]
  rw [Finset.sum_congr rfl fun m hm => by
    rw [E_level a hk m (Finset.mem_Icc.mp hm).1 y]]
  rw [← ite_level a k N hk hkN y, sum_Icc_symm]
  simp only [Int.cast_zero, div_zero, zero_smul, Finset.sum_const_zero, zero_add]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : (m : ℂ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hm).1; exact_mod_cast (show m ≠ 0 by omega)
  simp only [smul_sub, Finset.smul_sum, smul_smul, Int.cast_neg, Int.cast_natCast,
    one_div_mul_eq_div, div_neg, neg_smul, Finset.sum_neg_distrib]
  abel

/-! ### The coefficients vanish -/

theorem colour_id1' (a b c : Fin 3) :
    fabc (adjC b) c a = -(fabc a b c * (colourW c : ℂ)) / (colourW a : ℂ) := by
  have hw : (colourW a : ℂ) ≠ 0 := by exact_mod_cast (colourW_pos a).ne'
  have h := colour_id1 a b c
  field_simp
  linear_combination h

theorem colour_id2' (a b c : Fin 3) :
    fabc (adjC a) c b = fabc a b c * (colourW c : ℂ) / (colourW b : ℂ) := by
  have hw : (colourW b : ℂ) ≠ 0 := by exact_mod_cast (colourW_pos b).ne'
  have h := colour_id2 a b c
  field_simp
  linear_combination h

theorem coeffT_zero (a b c : Fin 3) {k : ℕ} (hk : 1 ≤ k) (j : ℤ) (hj0 : j ≠ 0) :
    1 / ((k : ℂ) * (colourW a : ℂ)) * (fabc a b c * CiA k b c (-(k : ℤ) - j)) +
      DA a b c / (j : ℂ) + 1 / ((k : ℂ) * (colourW a : ℂ)) * (-fabc (adjC a) c b) = 0 := by
  have hwa : (colourW a : ℂ) ≠ 0 := by exact_mod_cast (colourW_pos a).ne'
  have hwb : (colourW b : ℂ) ≠ 0 := by exact_mod_cast (colourW_pos b).ne'
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hj : (j : ℂ) ≠ 0 := by exact_mod_cast hj0
  rw [DA, colour_id1', colour_id2', CiA]
  by_cases hjk : j = -(k : ℤ)
  · rw [if_pos (by omega)]
    subst hjk
    push_cast
    field_simp
    ring
  · rw [if_neg (by omega)]
    have hkj : ((k : ℂ) + j) ≠ 0 := by
      intro h
      apply hjk
      have : ((k : ℤ) + j : ℂ) = 0 := by push_cast; exact h
      exact_mod_cast (show (j : ℂ) = -(k : ℂ) by linear_combination this)
    push_cast
    have hkj' : (k : ℂ) + (-(k : ℂ) - j) ≠ 0 := by
      rw [show (k : ℂ) + (-(k : ℂ) - j) = -j by ring]; exact neg_ne_zero.mpr hj
    field_simp
    ring

theorem coeffU_zero (a b c : Fin 3) {k : ℕ} (hk : 1 ≤ k) :
    1 / ((k : ℂ) * (colourW a : ℂ)) * (fabc a b c * ((((k : ℝ) * colourW c) : ℝ) : ℂ)) +
      fabc (adjC b) c a = 0 := by
  have hwa : (colourW a : ℂ) ≠ 0 := by exact_mod_cast (colourW_pos a).ne'
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [colour_id1']
  push_cast
  field_simp
  ring

/-! ### The step operator for a `c` creation mode vanishes -/

/-- **`K_p = 0` for `X = c^a_{-k}`** on `c₀`-free states of weight `W` with `W + k ≤ N`. -/
theorem Kp_c_zero (N : ℕ) (a : Fin 3) {k : ℕ} (hk : 1 ≤ k) {W : ℕ} (hWN : W + k ≤ N)
    {y : Sl2GhostSpace} (hy : y ∈ sl2GhostSVA.grading (W : ℂ)) (hC : C0 y) :
    Kp N a (k, 1) y = 0 := by
  have hkN : k ≤ N := by omega
  have hX' : Cr a (swapMode (k, 1)) = gMode a 0 (-(k : ℤ)) := by
    rw [show swapMode (k, 1) = (k - 1, 0) by
      simp only [swapMode, Fin.isValue, one_ne_zero, if_false]; rw [if_neg (by omega)]]
    simp only [Cr]; congr 1; push_cast; omega
  have hX : Cr a (k, 1) = gMode a 1 (-(k : ℤ) - 1) := rfl
  have hmc : ((modeCoef a (k, 1) : ℝ) : ℂ) = -(1 / ((k : ℂ) * (colourW a : ℂ))) := by
    simp only [modeCoef, Fin.isValue, one_ne_zero, if_false]
    rw [if_neg (by omega)]
    push_cast; ring
  set cc : ℂ := 1 / ((k : ℂ) * (colourW a : ℂ)) with hcc
  rw [Kp, hX', hX, Qgh_bMode, hmc, sub_eq_add_neg, E_piece a hk hkN y, conjJ_canon a hk hWN hy hC,
    zero_piece, ghostJ_canon (adjC a) hk hWN hy, neg_smul, neg_neg]
  -- the target in collected form
  have hT : ∀ j ∈ Finset.Icc (-(N : ℤ)) N, ∀ b c : Fin 3,
      (cc * (fabc a b c * CiA k b c (-(k : ℤ) - j)) + DA a b c / (j : ℂ) +
        cc * (-fabc (adjC a) c b)) • Tc k y b c j = 0 := by
    intro j _ b c
    by_cases hj0 : j = 0
    · subst hj0; rw [Tc_zero hC, smul_zero]
    · rw [hcc, coeffT_zero a b c hk j hj0, zero_smul]
  have hU : ∀ b c : Fin 3, (cc * (fabc a b c * ((((k : ℝ) * colourW c) : ℝ) : ℂ)) +
      fabc (adjC b) c a) • Uc k y b c = 0 := by
    intro b c
    rw [hcc, coeffU_zero a b c hk, zero_smul]
  have hzero : (∑ j ∈ Finset.Icc (-(N : ℤ)) N, ∑ b : Fin 3, ∑ c : Fin 3,
      (cc * (fabc a b c * CiA k b c (-(k : ℤ) - j)) + DA a b c / (j : ℂ) +
        cc * (-fabc (adjC a) c b)) • Tc k y b c j) +
      ∑ b : Fin 3, ∑ c : Fin 3, (cc * (fabc a b c * ((((k : ℝ) * colourW c) : ℝ) : ℂ)) +
        fabc (adjC b) c a) • Uc k y b c = 0 := by
    rw [Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun c _ => hT j hj b c, zero_add]
    exact Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => hU b c
  rw [← hzero]
  simp only [add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum, smul_smul]
  abel

end

end VOA.ConcreteHodge
