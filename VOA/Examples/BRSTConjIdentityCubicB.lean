/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTConjIdentityCubicA

/-!
# The step operator for a `b` creation mode

For `X = b^a_{-k}` (`k ≥ 1`) the step operator `K_p` is a combination of the canonical bilinears
`V p q σ = b^p_{(σ)} b^q_{(-k-σ)} y` and `Y p q = c^p_{(-1)} b^q_{(-k)} y`; its coefficients vanish
by the colour identity `colour_id3` after a symmetrization `σ ↔ -k-σ` (`Kp_b_zero`).

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

/-- `b^p_{(σ)} b^q_{(-k-σ)} y`. -/
abbrev VB (k : ℕ) (y : Sl2GhostSpace) (p q : Fin 3) (σ : ℤ) : Sl2GhostSpace :=
  gMode p 0 σ (gMode q 0 (-(k : ℤ) - σ) y)

/-- `c^p_{(-1)} b^q_{(-k)} y`. -/
abbrev YB (k : ℕ) (y : Sl2GhostSpace) (p q : Fin 3) : Sl2GhostSpace :=
  gMode p 1 (-1) (gMode q 0 (-(k : ℤ)) y)

theorem b0_C0 {y : Sl2GhostSpace} (hC : C0 y) (p : Fin 3) : gMode p 0 0 y = 0 := by
  have := b0_P0 p y; rwa [show P0 y = y from hC] at this

theorem VB_zero {k : ℕ} (hk : 1 ≤ k) {y : Sl2GhostSpace} (hC : C0 y) (p q : Fin 3) :
    VB k y p q 0 = 0 := by
  have hz : ¬ IsZeroMode 0 (-(k : ℤ) - 0) := by
    unfold IsZeroMode; rintro (⟨-, h⟩ | ⟨h, -⟩)
    · omega
    · exact absurd h (by decide)
  exact b0_C0 (C0_gMode (b := q) hz hC) p

theorem VB_negk {k : ℕ} {y : Sl2GhostSpace} (hC : C0 y) (p q : Fin 3) :
    VB k y p q (-(k : ℤ)) = 0 := by
  simp only [VB, show -(k : ℤ) - -(k : ℤ) = 0 by ring, b0_C0 hC, map_zero]

theorem VB_out {k N W : ℕ} (hWN : W + k ≤ N) {y : Sl2GhostSpace}
    (hy : y ∈ sl2GhostSVA.grading (W : ℂ)) (p q : Fin 3) {σ : ℤ}
    (hσ : σ ∉ Finset.Icc (-(N : ℤ)) (N - k)) : VB k y p q σ = 0 := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hσ
  rcases hσ with hσ | hσ
  · rw [VB, bMode_kill q hy (by omega), map_zero]
  · rw [VB, bb_anti p q, bMode_kill p hy (by omega), map_zero, neg_zero]

theorem VB_swap (k : ℕ) (y : Sl2GhostSpace) (p q : Fin 3) (σ : ℤ) :
    VB k y q p (-(k : ℤ) - σ) = -VB k y p q σ := by
  simp only [VB, show -(k : ℤ) - (-(k : ℤ) - σ) = σ by ring]
  exact bb_anti q p _ _ _

/-- For `cc`, the normal-ordered term is the plain product. -/
theorem NOterm_cc (p q : Fin 3) (n s : ℤ) (z : Sl2GhostSpace) :
    NOterm p 1 q 1 n s z = gMode p 1 s (gMode q 1 (n - s - 1) z) := by
  unfold NOterm
  split_ifs
  · rfl
  · rw [cc_anti q p, neg_neg]

/-- The coefficient of the conjugated CE quadratic, by the first `c` index `s`. -/
def CBs (k : ℕ) (p q : Fin 3) (s : ℤ) : ℂ :=
  if s = -1 ∨ s = -(k : ℤ) - 1 then 0
  else -(1 / (((s : ℂ) + 1) * (-(k : ℂ) - s - 1) * (colourW p : ℂ) * (colourW q : ℂ)))

theorem conj_CE {k : ℕ} (hk : 1 ≤ k) (y : Sl2GhostSpace) (p q : Fin 3) (s : ℤ) :
    ghostConj (NOterm p 1 q 1 (-(k : ℤ) - 1) s (ghostConj y)) =
      (if s = -1 then (1 / ((k : ℂ) * (colourW q : ℂ))) • YB k y p q else 0) +
      (if s = -(k : ℤ) - 1 then (-(1 / ((k : ℂ) * (colourW p : ℂ)))) • YB k y q p else 0) +
      CBs k p q s • VB k y p q (s + 1) := by
  have hwp : (colourW p : ℂ) ≠ 0 := by exact_mod_cast (colourW_pos p).ne'
  have hwq : (colourW q : ℂ) ≠ 0 := by exact_mod_cast (colourW_pos q).ne'
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [NOterm_cc]
  by_cases h1 : s = -1
  · subst h1
    rw [if_pos rfl, if_neg (by omega), CBs, if_pos (Or.inl rfl), zero_smul, add_zero, add_zero]
    simp only [show -(k : ℤ) - 1 - -1 - 1 = -(k : ℤ) - 1 by ring]
    rw [ghostConj_c0, ghostConj_cmode q (show -(k : ℤ) - 1 ≠ -1 by omega), ghostConj_sq, map_smul,
      Ppar_gMode, Ppar_Ppar, map_smul, map_neg, smul_neg]
    simp only [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring]
    rw [YB, ← neg_smul]
    congr 1
    push_cast
    rw [show (-(k : ℂ) - 1 + 1) = -(k : ℂ) by ring]
    field_simp
  by_cases h2 : s = -(k : ℤ) - 1
  · subst h2
    rw [if_neg (by omega), if_pos rfl, CBs, if_pos (Or.inr rfl), zero_smul, add_zero, zero_add]
    simp only [show -(k : ℤ) - 1 - (-(k : ℤ) - 1) - 1 = -1 by ring]
    rw [ghostConj_cmode p (show -(k : ℤ) - 1 ≠ -1 by omega), ghostConj_c0, ghostConj_sq, Ppar_gMode,
      Ppar_Ppar, map_neg]
    simp only [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring]
    rw [bc_anti p q (-(k : ℤ)) (-1) (by omega), neg_neg, YB]
    congr 1
    push_cast
    rw [show (-(k : ℂ) - 1 + 1) = -(k : ℂ) by ring]
    field_simp
  · rw [if_neg h1, if_neg h2, zero_add, zero_add, CBs, if_neg (by tauto),
      ghostConj_cmode p h1, ghostConj_cmode q (show -(k : ℤ) - 1 - s - 1 ≠ -1 by omega),
      ghostConj_sq, map_smul, Ppar_gMode, Ppar_Ppar, map_smul, map_neg, smul_neg]
    simp only [show -(k : ℤ) - 1 - s - 1 + 1 = -(k : ℤ) - (s + 1) by ring]
    rw [VB, smul_neg, smul_smul, ← neg_smul]
    congr 1
    have hs1 : ((s : ℂ) + 1) ≠ 0 := by
      intro h; apply h1; exact_mod_cast (show (s : ℂ) = -1 by linear_combination h)
    have hs2 : (-(k : ℂ) - s - 1) ≠ 0 := by
      intro h; apply h2; exact_mod_cast (show (s : ℂ) = -(k : ℂ) - 1 by linear_combination -h)
    push_cast
    rw [show (-(k : ℂ) - 1 - s - 1 + 1) = -(k : ℂ) - s - 1 by ring]
    field_simp

theorem sum_shift {V : Type*} [AddCommMonoid V] (N : ℤ) (H : ℤ → V)
    (hH : ∀ σ, σ ∉ Finset.Icc (-N) N → H σ = 0) :
    ∑ s ∈ Finset.Icc (-(N + 1)) (N + 1), H (s + 1) = ∑ σ ∈ Finset.Icc (-N) N, H σ := by
  have himg : (Finset.Icc (-(N + 1)) (N + 1)).image (fun s => s + 1) = Finset.Icc (-N) (N + 2) := by
    ext σ
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨s, ⟨h1, h2⟩, rfl⟩; omega
    · intro h; exact ⟨σ - 1, by omega, by ring⟩
  rw [← Finset.sum_image (f := H) (fun x _ y _ h => by simpa using h), himg]
  exact (Finset.sum_subset (fun σ hσ => by simp only [Finset.mem_Icc] at hσ ⊢; omega)
    (fun σ _ hσ => hH σ hσ)).symm

/-- **The conjugated CE quadratic in canonical form.** -/
theorem conjCE_canon (a : Fin 3) {k N W : ℕ} (hk : 1 ≤ k) (hWN : W + k ≤ N) {y : Sl2GhostSpace}
    (hy : y ∈ sl2GhostSVA.grading (W : ℂ)) :
    ghostConj (CEm a (-(k : ℤ) - 1) (ghostConj y)) =
      (∑ σ ∈ Finset.Icc (-(N : ℤ)) N, ∑ p : Fin 3, ∑ q : Fin 3,
        (fabc p q a * CBs k p q (σ - 1)) • VB k y p q σ) +
      ∑ p : Fin 3, ∑ q : Fin 3, fabc p q a •
        ((1 / ((k : ℂ) * (colourW q : ℂ))) • YB k y p q +
          (-(1 / ((k : ℂ) * (colourW p : ℂ)))) • YB k y q p) := by
  rw [CEm_window a (-(k : ℤ) - 1) (ghostConj_grading hy) ((N : ℤ) + 1) (by omega) (by omega)]
  simp only [map_sum, LinearMap.map_smulₛₗ, conj_fabc, conj_CE hk, Finset.sum_add_distrib]
  have hm1 : (-1 : ℤ) ∈ Finset.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1) := by
    simp only [Finset.mem_Icc]; omega
  have hm2 : (-(k : ℤ) - 1) ∈ Finset.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1) := by
    simp only [Finset.mem_Icc]; omega
  simp only [sum_ite_single _ _ hm1, sum_ite_single _ _ hm2]
  have hsh : ∀ p q : Fin 3, ∑ s ∈ Finset.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1),
      CBs k p q s • VB k y p q (s + 1) =
      ∑ σ ∈ Finset.Icc (-(N : ℤ)) N, CBs k p q (σ - 1) • VB k y p q σ := by
    intro p q
    have := sum_shift (N : ℤ) (fun σ => CBs k p q (σ - 1) • VB k y p q σ) (fun σ hσ => by
      have hσ' : σ ∉ Finset.Icc (-(N : ℤ)) (N - k) := by
        simp only [Finset.mem_Icc] at hσ ⊢; omega
      simp only [VB_out hWN hy p q hσ', smul_zero])
    simpa only [add_sub_cancel_right] using this
  simp only [hsh, Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib]
  have h : (∑ p : Fin 3, ∑ q : Fin 3, ∑ σ ∈ Finset.Icc (-(N : ℤ)) N,
      (fabc p q a * CBs k p q (σ - 1)) • VB k y p q σ) =
      ∑ σ ∈ Finset.Icc (-(N : ℤ)) N, ∑ p : Fin 3, ∑ q : Fin 3,
        (fabc p q a * CBs k p q (σ - 1)) • VB k y p q σ := by
    rw [triple_sum_swap]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_comm
  rw [h, add_comm]

/-! ### The zero-mode and `E` pieces for a `b` mode -/

theorem zero_piece_B (a : Fin 3) (k : ℕ) (y : Sl2GhostSpace) :
    (∑ b : Fin 3, gMode b 1 (-1) (ghostJ (adjC b) 0 (gMode a 0 (-(k : ℤ)) y) -
      gMode a 0 (-(k : ℤ)) (ghostJ (adjC b) 0 y))) =
      ∑ b : Fin 3, ∑ i : Fin 3, fabc (adjC b) a i • YB k y b i := by
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ghostJ_gMode (adjC b) a 0 0 (-(k : ℤ)) y, add_sub_cancel_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, coefJ, if_pos rfl, add_zero]

theorem B1_piece (a p q : Fin 3) (k : ℕ) (m : ℤ) (y : Sl2GhostSpace) :
    gMode p 0 (-m) (ghostJ q m (gMode a 0 (-(k : ℤ)) y)) +
      gMode a 0 (-(k : ℤ)) (gMode p 0 (-m) (ghostJ q m y)) =
      ∑ i : Fin 3, fabc q a i • VB k y p i (-m) := by
  have hS : gMode p 0 (-m) (∑ i : Fin 3, coefJ q a i 0 • gMode i 0 (-(k : ℤ) + m) y) =
      ∑ i : Fin 3, fabc q a i • VB k y p i (-m) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, coefJ, if_pos rfl, VB, show -(k : ℤ) - -m = -(k : ℤ) + m by ring]
  rw [ghostJ_gMode q a 0 m (-(k : ℤ)) y, map_add, bb_anti p a (-m), hS]
  abel

theorem B2_piece (a p q : Fin 3) (k : ℕ) (m : ℤ) (y : Sl2GhostSpace) :
    ghostJ p (-m) (gMode q 0 m (gMode a 0 (-(k : ℤ)) y)) +
      gMode a 0 (-(k : ℤ)) (ghostJ p (-m) (gMode q 0 m y)) =
      ∑ i : Fin 3, fabc p a i • VB k y q i m := by
  have hS : (∑ i : Fin 3, coefJ p a i 0 • gMode i 0 (-(k : ℤ) + -m) (gMode q 0 m y)) =
      -∑ i : Fin 3, fabc p a i • VB k y q i m := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coefJ, if_pos rfl, VB, bb_anti i q, show -(k : ℤ) + -m = -(k : ℤ) - m by ring, smul_neg]
  rw [bb_anti q a, map_neg, ghostJ_gMode p a 0 (-m) (-(k : ℤ)), hS]
  abel

/-- The contracted colour coefficient for a `b` mode. -/
def DB (a b i : Fin 3) : ℂ := fabc (adjC b) a i / (colourW b : ℂ)

theorem E_level_B (a : Fin 3) (k : ℕ) (m : ℕ) (y : Sl2GhostSpace) :
    ((∑ p : Fin 3, ∑ q : Fin 3, casimir p q •
        gMode p 0 (-(m : ℤ)) (ghostJ q m (gMode a 0 (-(k : ℤ)) y))) -
      ∑ p : Fin 3, ∑ q : Fin 3, casimir p q •
        ghostJ p (-(m : ℤ)) (gMode q 0 m (gMode a 0 (-(k : ℤ)) y))) +
    gMode a 0 (-(k : ℤ)) ((∑ p : Fin 3, ∑ q : Fin 3, casimir p q •
        gMode p 0 (-(m : ℤ)) (ghostJ q m y)) -
      ∑ p : Fin 3, ∑ q : Fin 3, casimir p q • ghostJ p (-(m : ℤ)) (gMode q 0 m y)) =
    (∑ b : Fin 3, ∑ i : Fin 3, DB a b i • VB k y b i (-(m : ℤ))) -
      ∑ b : Fin 3, ∑ i : Fin 3, DB a b i • VB k y b i m := by
  have h1 := sum2_add_map (gMode a 0 (-(k : ℤ))) casimir
    (fun p q => gMode p 0 (-(m : ℤ)) (ghostJ q m (gMode a 0 (-(k : ℤ)) y)))
    (fun p q => gMode p 0 (-(m : ℤ)) (ghostJ q m y))
  have h2 := sum2_add_map (gMode a 0 (-(k : ℤ))) casimir
    (fun p q => ghostJ p (-(m : ℤ)) (gMode q 0 m (gMode a 0 (-(k : ℤ)) y)))
    (fun p q => ghostJ p (-(m : ℤ)) (gMode q 0 m y))
  simp only [B1_piece] at h1
  simp only [B2_piece] at h2
  have e1 : (∑ p : Fin 3, ∑ q : Fin 3, casimir p q • ∑ i : Fin 3, fabc q a i • VB k y p i (-(m : ℤ))) =
      ∑ b : Fin 3, ∑ i : Fin 3, DB a b i • VB k y b i (-(m : ℤ)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul, casimir_contract, DB]
  have e2 : (∑ p : Fin 3, ∑ q : Fin 3, casimir p q • ∑ i : Fin 3, fabc p a i • VB k y q i m) =
      ∑ b : Fin 3, ∑ i : Fin 3, DB a b i • VB k y b i m := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul, casimir_contract', DB]
  rw [e1] at h1
  rw [e2] at h2
  rw [map_sub, show ∀ A B C D : Sl2GhostSpace, (A - B) + (C - D) = (A + C) - (B + D) from
    fun A B C D => by abel, h1, h2]

/-- **The `E` piece for a `b` mode in canonical form.** -/
theorem E_piece_B (a : Fin 3) (k N : ℕ) (y : Sl2GhostSpace) :
    -(Egh N (gMode a 0 (-(k : ℤ)) y) + gMode a 0 (-(k : ℤ)) (Egh N y)) =
      ∑ σ ∈ Finset.Icc (-(N : ℤ)) N, ∑ b : Fin 3, ∑ i : Fin 3,
        (DB a b i / (σ : ℂ)) • VB k y b i σ := by
  rw [Egh_apply, Egh_apply, map_sum]
  simp only [map_smul]
  rw [← Finset.sum_add_distrib]
  simp only [← smul_add]
  rw [Finset.sum_congr rfl fun m _ => by rw [E_level_B a k m y], sum_Icc_symm]
  simp only [Int.cast_zero, div_zero, zero_smul, Finset.sum_const_zero, zero_add]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [smul_sub, Finset.smul_sum, smul_smul, Int.cast_neg, Int.cast_natCast,
    one_div_mul_eq_div, div_neg, neg_smul, Finset.sum_neg_distrib]
  abel

/-! ### Assembly for a `b` mode -/

/-- The total coefficient of `V p q σ`. -/
def cV (a : Fin 3) (k : ℕ) (p q : Fin 3) (σ : ℤ) : ℂ :=
  -((k : ℂ) * (colourW a : ℂ) / 2) * (fabc p q a * CBs k p q (σ - 1)) + DB a p q / (σ : ℂ)

theorem colour_id3' (a b i : Fin 3) :
    fabc (adjC b) a i = (colourW a : ℂ) * fabc b i a / (colourW i : ℂ) := by
  have hw : (colourW i : ℂ) ≠ 0 := by exact_mod_cast (colourW_pos i).ne'
  have h := colour_id3 a b i
  field_simp
  linear_combination h

theorem cV_swap (a : Fin 3) {k : ℕ} (hk : 1 ≤ k) (p q : Fin 3) (σ : ℤ) (h0 : σ ≠ 0)
    (hk' : σ ≠ -(k : ℤ)) : cV a k q p (-(k : ℤ) - σ) = cV a k p q σ := by
  have hwp : (colourW p : ℂ) ≠ 0 := by exact_mod_cast (colourW_pos p).ne'
  have hwq : (colourW q : ℂ) ≠ 0 := by exact_mod_cast (colourW_pos q).ne'
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hσ : (σ : ℂ) ≠ 0 := by exact_mod_cast h0
  have hkσ : ((k : ℂ) + σ) ≠ 0 := by
    intro h; apply hk'; exact_mod_cast (show (σ : ℂ) = -(k : ℂ) by linear_combination h)
  unfold cV CBs DB
  rw [if_neg (by omega), if_neg (by omega), colour_id3', colour_id3', fabc_antisymm q p a]
  push_cast
  have e1 : (-(k : ℂ) - σ - 1 + 1) = -((k : ℂ) + σ) := by ring
  have e2 : (-(k : ℂ) - (-(k : ℂ) - σ - 1) - 1) = σ := by ring
  have e3 : ((σ : ℂ) - 1 + 1) = σ := by ring
  have e4 : (-(k : ℂ) - (σ - 1) - 1) = -((k : ℂ) + σ) := by ring
  rw [e1, e2, e3, e4]
  have hkσ' : (-(k : ℂ) - σ) ≠ 0 := by
    rw [show (-(k : ℂ) - σ) = -((k : ℂ) + σ) by ring]; exact neg_ne_zero.mpr hkσ
  have hkσ'' : -((k : ℂ) + σ) ≠ 0 := neg_ne_zero.mpr hkσ
  field_simp
  ring

theorem cV_V_swap (a : Fin 3) {k : ℕ} (hk : 1 ≤ k) {y : Sl2GhostSpace} (hC : C0 y)
    (p q : Fin 3) (σ : ℤ) :
    cV a k q p (-(k : ℤ) - σ) • VB k y q p (-(k : ℤ) - σ) = -(cV a k p q σ • VB k y p q σ) := by
  by_cases h0 : σ = 0
  · subst h0
    rw [VB_zero hk hC, smul_zero, show -(k : ℤ) - 0 = -(k : ℤ) by ring, VB_negk hC, smul_zero,
      neg_zero]
  by_cases hk' : σ = -(k : ℤ)
  · subst hk'
    rw [VB_negk hC, smul_zero, show -(k : ℤ) - -(k : ℤ) = 0 by ring, VB_zero hk hC, smul_zero,
      neg_zero]
  rw [cV_swap a hk p q σ h0 hk', VB_swap, smul_neg]

/-- The `V` part vanishes by the involution `(p, q, σ) ↦ (q, p, -k-σ)`. -/
theorem V_part_zero (a : Fin 3) {k N W : ℕ} (hk : 1 ≤ k) (hWN : W + k ≤ N) {y : Sl2GhostSpace}
    (hy : y ∈ sl2GhostSVA.grading (W : ℂ)) (hC : C0 y) :
    ∑ σ ∈ Finset.Icc (-(N : ℤ)) N, ∑ p : Fin 3, ∑ q : Fin 3, cV a k p q σ • VB k y p q σ = 0 := by
  set S := ∑ σ ∈ Finset.Icc (-(N : ℤ)) N, ∑ p : Fin 3, ∑ q : Fin 3, cV a k p q σ • VB k y p q σ
  have hrefl := sum_reflect (N : ℤ) (k : ℤ) (by omega)
    (fun σ => ∑ p : Fin 3, ∑ q : Fin 3, cV a k p q σ • VB k y p q σ) (fun σ hσ => by
      simp only [VB_out hWN hy _ _ hσ, smul_zero, Finset.sum_const_zero])
  have hneg : S = -S := by
    calc S = ∑ σ ∈ Finset.Icc (-(N : ℤ)) N, ∑ p : Fin 3, ∑ q : Fin 3,
          cV a k p q (-(k : ℤ) - σ) • VB k y p q (-(k : ℤ) - σ) := hrefl.symm
      _ = ∑ σ ∈ Finset.Icc (-(N : ℤ)) N, ∑ p : Fin 3, ∑ q : Fin 3,
          cV a k q p (-(k : ℤ) - σ) • VB k y q p (-(k : ℤ) - σ) :=
          Finset.sum_congr rfl fun σ _ => Finset.sum_comm
      _ = ∑ σ ∈ Finset.Icc (-(N : ℤ)) N, ∑ p : Fin 3, ∑ q : Fin 3,
          -(cV a k p q σ • VB k y p q σ) := by
          simp only [cV_V_swap a hk hC]
      _ = -S := by simp only [Finset.sum_neg_distrib, S]
  have h2 : (2 : ℂ) • S = 0 := by rw [two_smul]; nth_rewrite 1 [hneg]; exact neg_add_cancel S
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem YB_part_zero (a : Fin 3) {k : ℕ} (hk : 1 ≤ k) (y : Sl2GhostSpace) :
    (-((k : ℂ) * (colourW a : ℂ) / 2)) • (∑ p : Fin 3, ∑ q : Fin 3, fabc p q a •
        ((1 / ((k : ℂ) * (colourW q : ℂ))) • YB k y p q +
          (-(1 / ((k : ℂ) * (colourW p : ℂ)))) • YB k y q p)) +
      ∑ b : Fin 3, ∑ i : Fin 3, fabc (adjC b) a i • YB k y b i = 0 := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hswap : (∑ p : Fin 3, ∑ q : Fin 3, fabc p q a •
      (-(1 / ((k : ℂ) * (colourW p : ℂ)))) • YB k y q p) =
      ∑ p : Fin 3, ∑ q : Fin 3, (fabc p q a * (1 / ((k : ℂ) * (colourW q : ℂ)))) • YB k y p q := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [smul_smul, fabc_antisymm q p a]
    congr 1
    ring
  simp only [smul_add, Finset.sum_add_distrib, hswap]
  simp only [smul_smul, Finset.smul_sum, ← Finset.sum_add_distrib, ← add_smul]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  have hwq : (colourW q : ℂ) ≠ 0 := by exact_mod_cast (colourW_pos q).ne'
  rw [colour_id3']
  convert zero_smul ℂ (YB k y p q) using 2
  field_simp
  ring

/-- **`K_p = 0` for `X = b^a_{-k}`** on `c₀`-free states of weight `W` with `W + k ≤ N`. -/
theorem Kp_b_zero (N : ℕ) (a : Fin 3) {k : ℕ} (hk : 1 ≤ k) {W : ℕ} (hWN : W + k ≤ N)
    {y : Sl2GhostSpace} (hy : y ∈ sl2GhostSVA.grading (W : ℂ)) (hC : C0 y) :
    Kp N a (k - 1, 0) y = 0 := by
  have hX : Cr a (k - 1, 0) = gMode a 0 (-(k : ℤ)) := by
    simp only [Cr]; congr 1; omega
  have hX' : Cr a (swapMode (k - 1, 0)) = gMode a 1 (-(k : ℤ) - 1) := by
    rw [show swapMode (k - 1, 0) = (k - 1 + 1, 1) by simp [swapMode]]
    simp only [Cr]; congr 1; omega
  have hmc : ((modeCoef a (k - 1, 0) : ℝ) : ℂ) = -((k : ℂ) * (colourW a : ℂ)) := by
    simp only [modeCoef, if_true]
    rw [show (((k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) by
      rw [Nat.cast_sub hk]; ring]
    push_cast; ring
  rw [Kp, hX, hX', Qgh_cMode, hmc, sub_eq_add_neg, E_piece_B a k N y, LinearMap.map_smulₛₗ,
    conjCE_canon a hk hWN hy, zero_piece_B]
  have hconj : (starRingEnd ℂ) (-(1 / 2 : ℂ)) = -(1 / 2 : ℂ) := by
    rw [map_neg, map_div₀, map_one, map_ofNat]
  rw [hconj, smul_add, smul_add]
  set Vs := ∑ σ ∈ Finset.Icc (-(N : ℤ)) N, ∑ p : Fin 3, ∑ q : Fin 3,
    (fabc p q a * CBs k p q (σ - 1)) • VB k y p q σ
  set Ys := ∑ p : Fin 3, ∑ q : Fin 3, fabc p q a •
    ((1 / ((k : ℂ) * (colourW q : ℂ))) • YB k y p q +
      (-(1 / ((k : ℂ) * (colourW p : ℂ)))) • YB k y q p)
  set Zs := ∑ b : Fin 3, ∑ i : Fin 3, fabc (adjC b) a i • YB k y b i
  set Es := ∑ σ ∈ Finset.Icc (-(N : ℤ)) N, ∑ b : Fin 3, ∑ i : Fin 3,
    (DB a b i / (σ : ℂ)) • VB k y b i σ
  have hsc : ∀ X : Sl2GhostSpace, -(-((k : ℂ) * (colourW a : ℂ)) • -(1 / 2 : ℂ) • X) =
      (-((k : ℂ) * (colourW a : ℂ) / 2)) • X := by
    intro X; rw [smul_smul, ← neg_smul]; congr 1; ring
  have hVE : (-((k : ℂ) * (colourW a : ℂ) / 2)) • Vs + Es =
      ∑ σ ∈ Finset.Icc (-(N : ℤ)) N, ∑ p : Fin 3, ∑ q : Fin 3, cV a k p q σ • VB k y p q σ := by
    simp only [Vs, Es, cV, add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  rw [neg_add, hsc, hsc]
  have hV := V_part_zero a hk hWN hy hC
  have hY := YB_part_zero a hk y
  calc (-((k : ℂ) * (colourW a : ℂ) / 2)) • Vs + (-((k : ℂ) * (colourW a : ℂ) / 2)) • Ys + Zs + Es
      = ((-((k : ℂ) * (colourW a : ℂ) / 2)) • Vs + Es) +
        ((-((k : ℂ) * (colourW a : ℂ) / 2)) • Ys + Zs) := by abel
    _ = 0 := by rw [hVE, hV, hY, add_zero]

end

end VOA.ConcreteHodge
