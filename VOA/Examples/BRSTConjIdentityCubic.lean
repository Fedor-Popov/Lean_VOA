/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTConjIdentityRhoD

/-!
# The cubic ghost charge: mode algebra

Ingredients for `GhostCubicConj`:

* `Qgh_bMode` — `{Q_gh, b^a_m} = J^a_{gh,m}`;
* `Qgh_cMode` — `{Q_gh, c^a_{(m)}} = -(1/2) CE^a_{(m)}` with `CE^a` the Chevalley–Eilenberg
  quadratic `Σ f^{pq}{}_a c^p_{(-1)} c^q`;
* explicit locally finite expansions of `J^a_{gh,(n)}` and `CE^a_{(n)}` on states of bounded
  weight (`ghostJ_window`, `CEm_window`);
* weight shifts and weight kills for the ghost modes;
* the conjugation of every ghost mode in uniform form (`ghostConj_bMode`, `ghostConj_cMode'`).

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

/-! ### The cubic charge and the ghost modes -/

theorem Qgh_bMode (a : Fin 3) (m : ℤ) (x : Sl2GhostSpace) :
    Qgh (gMode a 0 m x) + gMode a 0 m (Qgh x) = ghostJ a m x := by
  have h := translationCovariant_sl2GhostSVA.mode_commutator_bound (bGhost_odd a)
    ghostBRSTState_odd 1 (fun j hj => bGhost_high_ghostBRSTState a j (by omega)) m 0
  simp only [koszul_one_one, neg_smul, one_smul, sub_neg_eq_add, Finset.sum_range_one,
    gBinom_zero, Nat.cast_zero, sub_zero, add_zero] at h
  rw [bGhost_zero_ghostBRSTState] at h
  have h' := LinearMap.congr_fun h x
  simp only [LinearMap.add_apply, Module.End.mul_apply] at h'
  rw [add_comm]
  exact h'

/-- The modes of the Chevalley–Eilenberg quadratic. -/
abbrev CEm (a : Fin 3) (n : ℤ) : Module.End ℂ Sl2GhostSpace :=
  mode (sl2GhostSVA.Y (ghostCEQuadratic a)) n

theorem cGhost_high_ghostBRSTState (b : Fin 3) (j : ℤ) (hj : 1 ≤ j) :
    mode (sl2GhostSVA.Y (cGhost b)) j ghostBRSTState = 0 := by
  have h := sl2GhostSVA.grading_mode (cGhost b) (cGhost_weight b) ghostBRSTState
    ghostBRSTState_weight j
  rw [natSupported_sl2GhostSVA _ (fun ⟨k, hk⟩ => by
    have : ((k : ℤ) : ℂ) = ((-j : ℤ) : ℂ) := by rw [Int.cast_natCast, hk]; push_cast; ring
    have := Int.cast_injective this
    omega), Submodule.mem_bot] at h
  exact h

theorem Qgh_cMode (a : Fin 3) (m : ℤ) (x : Sl2GhostSpace) :
    Qgh (gMode a 1 m x) + gMode a 1 m (Qgh x) = (-(1 / 2 : ℂ)) • CEm a m x := by
  have h := translationCovariant_sl2GhostSVA.mode_commutator_bound (cGhost_odd a)
    ghostBRSTState_odd 1 (fun j hj => cGhost_high_ghostBRSTState a j (by omega)) m 0
  simp only [koszul_one_one, neg_smul, one_smul, sub_neg_eq_add, Finset.sum_range_one,
    gBinom_zero, Nat.cast_zero, sub_zero, add_zero] at h
  rw [cGhost_zero_ghostBRSTState, map_smul, mode_smul] at h
  have h' := LinearMap.congr_fun h x
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply] at h'
  rw [add_comm]
  exact h'

theorem Qgh_gvac : Qgh gvac = 0 := by
  rw [gvac_eq]
  exact (sl2GhostSVA.creation ghostBRSTState).2 0 le_rfl

/-! ### Weights -/

theorem gMode_weight (a : Fin 3) (e : Fin 2) (m : ℤ) {h : ℂ} {y : Sl2GhostSpace}
    (hy : y ∈ sl2GhostSVA.grading h) :
    gMode a e m y ∈ sl2GhostSVA.grading (h - m - (if e = 0 then 0 else 1)) := by
  match e with
  | 0 =>
    have := sl2GhostSVA.grading_mode (bGhost a) (bGhost_weight a) y hy m
    convert this using 2; simp; try ring
  | 1 =>
    have := sl2GhostSVA.grading_mode (cGhost a) (cGhost_weight a) y hy m
    convert this using 2; simp; try ring

theorem eq_zero_of_grading_neg {y : Sl2GhostSpace} {z : ℤ} (hz : z < 0)
    (hy : y ∈ sl2GhostSVA.grading (z : ℂ)) : y = 0 := by
  rw [natSupported_sl2GhostSVA _ (fun ⟨k, hk⟩ => by
    have : ((k : ℤ) : ℂ) = (z : ℂ) := by rw [Int.cast_natCast, hk]
    have := Int.cast_injective this
    omega), Submodule.mem_bot] at hy
  exact hy

/-- A `b` mode of index above the weight kills the state. -/
theorem bMode_kill (a : Fin 3) {W : ℕ} {y : Sl2GhostSpace} (hy : y ∈ sl2GhostSVA.grading (W : ℂ))
    {m : ℤ} (hm : (W : ℤ) < m) : gMode a 0 m y = 0 := by
  have h := gMode_weight a 0 m hy
  simp only [if_true, sub_zero] at h
  exact eq_zero_of_grading_neg (z := (W : ℤ) - m) (by omega) (by push_cast; exact h)

/-- A `c` mode (vertex index `m`, conformal `m + 1`) of conformal index above the weight kills
the state. -/
theorem cMode_kill (a : Fin 3) {W : ℕ} {y : Sl2GhostSpace} (hy : y ∈ sl2GhostSVA.grading (W : ℂ))
    {m : ℤ} (hm : (W : ℤ) ≤ m) : gMode a 1 m y = 0 := by
  have h := gMode_weight a 1 m hy
  simp only [one_ne_zero, if_false] at h
  exact eq_zero_of_grading_neg (z := (W : ℤ) - m - 1) (by omega) (by push_cast; exact h)

/-! ### Explicit expansions of the bilinear fields -/

theorem gmode_sum {ι : Type*} (S : Finset ι) (f : ι → Sl2GhostSpace) (n : ℤ) (z : Sl2GhostSpace) :
    mode (sl2GhostSVA.Y (∑ i ∈ S, f i)) n z = ∑ i ∈ S, mode (sl2GhostSVA.Y (f i)) n z := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, map_add, mode_add, LinearMap.add_apply, ih]

theorem gmode_smul (c : ℂ) (u : Sl2GhostSpace) (n : ℤ) (z : Sl2GhostSpace) :
    mode (sl2GhostSVA.Y (c • u)) n z = c • mode (sl2GhostSVA.Y u) n z := by
  rw [map_smul, mode_smul, LinearMap.smul_apply]

/-- The normal-ordered term of a product of two odd ghost generators, by the mode index `j` of
the first factor. -/
def NOterm (c : Fin 3) (e1 : Fin 2) (b : Fin 3) (e2 : Fin 2) (n j : ℤ) (z : Sl2GhostSpace) :
    Sl2GhostSpace :=
  if j ≤ -1 then gMode c e1 j (gMode b e2 (n - j - 1) z)
  else -(gMode b e2 (n - j - 1) (gMode c e1 j z))

/-- **The modes of `u_{(-1)} v` for two odd ghost generators**, as a finite sum over any
window outside which the normal-ordered terms vanish. -/
theorem bilin_mode_expand (c : Fin 3) (e1 : Fin 2) (b : Fin 3) (e2 : Fin 2) (n : ℤ)
    (z : Sl2GhostSpace) (S : Finset ℤ) (hS : ∀ j ∉ S, NOterm c e1 b e2 n j z = 0) :
    mode (sl2GhostSVA.Y (mode (sl2GhostSVA.Y (ghostGenerator c e1)) (-1) (ghostGenerator b e2)))
      n z = ∑ j ∈ S, NOterm c e1 b e2 n j z := by
  rw [TranslationCovariant.normal_product_mode translationCovariant_sl2GhostSVA
    (ghostGenerator_odd c e1) (ghostGenerator_odd b e2) n z]
  let e : ℤ ≃ ℤ :=
    { toFun := fun m => -m - 1
      invFun := fun j => -j - 1
      left_inv := by intro m; dsimp; omega
      right_inv := by intro j; dsimp; omega }
  have hterm : ∀ m : ℤ, normalOrderedε (koszul 1 1) (sl2GhostSVA.Y (ghostGenerator c e1))
      (sl2GhostSVA.Y (ghostGenerator b e2)) m (-n - 1 - m) z = NOterm c e1 b e2 n (e m) z := by
    intro m
    simp only [normalOrderedε_apply, NOterm, e, Equiv.coe_fn_mk, koszul_one_one, neg_one_smul]
    by_cases hm : 0 ≤ m
    · rw [if_pos hm, if_pos (by omega)]
      simp only [Module.End.mul_apply]
      rw [show sl2GhostSVA.Y (ghostGenerator c e1) m = gMode c e1 (-m - 1) by
          rw [gMode, mode_apply]; ring_nf,
        show sl2GhostSVA.Y (ghostGenerator b e2) (-n - 1 - m) = gMode b e2 (n - (-m - 1) - 1) by
          rw [gMode, mode_apply]; ring_nf]
    · rw [if_neg hm, if_neg (by omega)]
      simp only [Module.End.mul_apply, LinearMap.neg_apply]
      rw [show sl2GhostSVA.Y (ghostGenerator c e1) m = gMode c e1 (-m - 1) by
          rw [gMode, mode_apply]; ring_nf,
        show sl2GhostSVA.Y (ghostGenerator b e2) (-n - 1 - m) = gMode b e2 (n - (-m - 1) - 1) by
          rw [gMode, mode_apply]; ring_nf]
  simp_rw [hterm]
  rw [finsum_comp_equiv e (f := fun j => NOterm c e1 b e2 n j z)]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra h
  exact hj (hS j h)

/-- **The ghost current modes on a state of weight `≤ W`**, as a finite window sum. -/
theorem ghostJ_window (a : Fin 3) (n : ℤ) {W : ℕ} {z : Sl2GhostSpace}
    (hz : z ∈ sl2GhostSVA.grading (W : ℂ)) (M : ℤ) (hM1 : (W : ℤ) ≤ M) (hM2 : (W : ℤ) - n ≤ M) :
    ghostJ a n z = ∑ b : Fin 3, ∑ c : Fin 3, fabc a b c •
      ∑ j ∈ Finset.Icc (-M) M, NOterm c 0 b 1 n j z := by
  rw [show ghostJ a n z = mode (sl2GhostSVA.Y (ghostCurrent a)) n z from rfl, ghostCurrent,
    gmode_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [gmode_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [gmode_smul, ghostCurrentCoefficient, ghostBilinear,
    show bGhost c = ghostGenerator c 0 from rfl, show cGhost b = ghostGenerator b 1 from rfl,
    bilin_mode_expand c 0 b 1 n z _ (fun j hj => ?_)]
  simp only [Finset.mem_Icc, not_and_or, not_le] at hj
  unfold NOterm
  rcases hj with hj | hj
  · rw [if_pos (by omega), cMode_kill b hz (by omega), map_zero]
  · rw [if_neg (by omega), bMode_kill c hz (by omega), map_zero, neg_zero]

/-- **The Chevalley–Eilenberg modes on a state of weight `≤ W`**, as a finite window sum. -/
theorem CEm_window (a : Fin 3) (n : ℤ) {W : ℕ} {z : Sl2GhostSpace}
    (hz : z ∈ sl2GhostSVA.grading (W : ℂ)) (M : ℤ) (hM1 : (W : ℤ) ≤ M) (hM2 : (W : ℤ) - n ≤ M) :
    CEm a n z = ∑ p : Fin 3, ∑ q : Fin 3, fabc p q a •
      ∑ s ∈ Finset.Icc (-M) M, NOterm p 1 q 1 n s z := by
  rw [CEm, ghostCEQuadratic, gmode_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [gmode_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [gmode_smul, show cGhost p = ghostGenerator p 1 from rfl,
    show cGhost q = ghostGenerator q 1 from rfl,
    bilin_mode_expand p 1 q 1 n z _ (fun s hs => ?_)]
  simp only [Finset.mem_Icc, not_and_or, not_le] at hs
  unfold NOterm
  rcases hs with hs | hs
  · rw [if_pos (by omega), cMode_kill q hz (by omega), map_zero]
  · rw [if_neg (by omega), cMode_kill p hz (by omega), map_zero, neg_zero]

/-! ### The conjugation of the modes, uniformly -/

theorem ghostConj_bmode (a : Fin 3) {t : ℤ} (ht : t ≠ 0) (y : Sl2GhostSpace) :
    ghostConj (gMode a 0 t y) =
      (((t : ℝ) * colourW a : ℝ) : ℂ) • gMode a 1 (t - 1) (Ppar (ghostConj y)) := by
  rcases lt_or_gt_of_ne ht with h | h
  · have e1 : gMode a 0 t = Cr a ((-t - 1).toNat, 0) := by
      simp only [Cr]; congr 1; omega
    have e2 : Cr a (swapMode ((-t - 1).toNat, 0)) = gMode a 1 (t - 1) := by
      rw [show swapMode ((-t - 1).toNat, 0) = ((-t - 1).toNat + 1, 1) by simp [swapMode]]
      simp only [Cr]; congr 1; push_cast; omega
    rw [e1, ghostConj_Cr, e2]
    congr 2
    simp only [modeCoef, if_true]
    rw [show (((-t - 1).toNat : ℕ) : ℝ) = ((-t - 1 : ℤ) : ℝ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]]
    push_cast; ring
  · have e1 : gMode a 0 t = An a (t.toNat, 1) := by
      simp only [An]; congr 1; omega
    have e2 : An a (swapMode (t.toNat, 1)) = gMode a 1 (t - 1) := by
      rw [show swapMode (t.toNat, 1) = (t.toNat - 1, 0) by
        simp only [swapMode, Fin.isValue, one_ne_zero, if_false]; rw [if_neg (by omega)]]
      simp only [An]; congr 1; omega
    rw [e1, ghostConj_An, e2]
    congr 2
    have hw : colourW a ≠ 0 := (colourW_pos a).ne'
    simp only [anCoef, modeCoef, Fin.isValue, one_ne_zero, if_false]
    rw [if_neg (by omega)]
    rw [show ((t.toNat : ℕ) : ℝ) = (t : ℝ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]]
    have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    field_simp

theorem ghostConj_b0 (a : Fin 3) (y : Sl2GhostSpace) :
    ghostConj (gMode a 0 0 y) = -gMode a 0 0 (Ppar (ghostConj y)) := by
  have h := ghostConj_An a (0, 1) y
  rw [show swapMode (0, 1) = (0, 1) by simp [swapMode]] at h
  rw [show gMode a 0 0 = An a (0, 1) from rfl, h]
  simp only [anCoef, show modeCoef a (0, 1) = 1 by unfold modeCoef; simp, inv_one]
  push_cast
  simp

theorem ghostConj_cmode (a : Fin 3) {t : ℤ} (ht : t ≠ -1) (y : Sl2GhostSpace) :
    ghostConj (gMode a 1 t y) =
      ((1 / (((t : ℝ) + 1) * colourW a) : ℝ) : ℂ) • gMode a 0 (t + 1) (Ppar (ghostConj y)) := by
  have h := ghostConj_cMode a (n := -t - 1) (by omega) y
  rw [show -(-t - 1) - 1 = t by ring, show -(-t - 1) = t + 1 by ring] at h
  rw [h]
  congr 2
  push_cast
  rw [show (-(t : ℝ) - 1) * colourW a = -(((t : ℝ) + 1) * colourW a) by ring,
    one_div_neg_eq_neg_one_div, neg_neg]

end

end VOA.ConcreteHodge
