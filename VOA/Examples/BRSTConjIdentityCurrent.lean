/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTConjIdentityGhost

/-!
# The `c₀`-free projection and skewness of the ghost current under `B_G`

* `P0 = Π_a b^a_0 c^a_0` — the projection onto the `c₀`-free ghost states, built from the zero
  modes. It is idempotent, commutes with every nonzero mode and with `Ppar`, kills `b^a_0` from
  the left and `c^a_0` from the right, fixes every state killed by all `b^a_0`, and is symmetric
  for `B_G` (`ghostB_P0`).
* `ghostJ_gMode` — the commutator of an arbitrary ghost-current mode with an arbitrary ghost mode.
* `ghostB_ghostJ_skew` — **the ghost current is `B_G`-skew on `c₀`-free states**:
  `B_G(J^a_m P0 x, P0 x') = -B_G(P0 x, J^a_{-m} P0 x')`. (On states with `c₀` this fails; numerical
  certificate in the layer report: `B_G(J^h_0 c^e_0|0⟩, c^e_0|0⟩) + B_G(c^e_0|0⟩, J^h_0 c^e_0|0⟩) = 4`.)

Proof: by induction on states built from the vacuum by creation operators, using the mode
transposes of `GhostConjBE`'s ghost layer (`ghostB_gMode`), the commutators, and, for the vacuum
pair, weight orthogonality of the fine grading.

Everything is proved outright.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open VOA.SympFerm VOA.Ghost AffineVOA
open scoped TensorProduct

noncomputable section

/-! ### Zero modes and the projection `P0` -/

/-- `b^a_0`. -/
abbrev b0 (a : Fin 3) : Module.End ℂ Sl2GhostSpace := gMode a 0 0
/-- `c^a_0`. -/
abbrev c0 (a : Fin 3) : Module.End ℂ Sl2GhostSpace := gMode a 1 (-1)

/-- `b^a_0 c^a_0`. -/
def pc (a : Fin 3) : Module.End ℂ Sl2GhostSpace := b0 a * c0 a

/-- The projection onto the `c₀`-free ghost states. -/
def P0 : Module.End ℂ Sl2GhostSpace := pc 0 * pc 1 * pc 2

theorem gMode_sq (a : Fin 3) (e : Fin 2) (m : ℤ) (x : Sl2GhostSpace) :
    gMode a e m (gMode a e m x) = 0 := by
  have h := gMode_anticomm_apply a a e e m m x
  rw [if_neg (by fin_cases e <;> simp)] at h
  have h2 : (2 : ℂ) • gMode a e m (gMode a e m x) = 0 := by rw [two_smul]; exact h
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- A mode anticommuting with both factors commutes with `pc a`. -/
theorem comm_pc_of_anticomm {X : Module.End ℂ Sl2GhostSpace} {a : Fin 3}
    (hb : ∀ x, X (b0 a x) = -b0 a (X x)) (hc : ∀ x, X (c0 a x) = -c0 a (X x)) (x : Sl2GhostSpace) :
    X (pc a x) = pc a (X x) := by
  simp only [pc, Module.End.mul_apply, hb, hc, map_neg, neg_neg]

theorem gMode_anticomm_b0 {a b : Fin 3} {e : Fin 2} {n : ℤ}
    (h : ¬ (a = b ∧ e = 1 ∧ n = -1)) (x : Sl2GhostSpace) :
    gMode b e n (b0 a x) = -b0 a (gMode b e n x) := by
  have h' := gMode_anticomm_apply a b 0 e 0 n x
  rw [if_neg (by
    rintro ⟨rfl, he, hn⟩
    exact h ⟨rfl, by rw [← he]; rfl, by omega⟩)] at h'
  exact eq_neg_of_add_eq_zero_right h'

theorem gMode_anticomm_c0 {a b : Fin 3} {e : Fin 2} {n : ℤ}
    (h : ¬ (a = b ∧ e = 0 ∧ n = 0)) (x : Sl2GhostSpace) :
    gMode b e n (c0 a x) = -c0 a (gMode b e n x) := by
  have h' := gMode_anticomm_apply a b 1 e (-1) n x
  rw [if_neg (by
    rintro ⟨rfl, he, hn⟩
    exact h ⟨rfl, by rw [← he]; rfl, by omega⟩)] at h'
  exact eq_neg_of_add_eq_zero_right h'

/-- A nonzero mode commutes with every `pc a`. -/
theorem gMode_comm_pc (a b : Fin 3) {e : Fin 2} {n : ℤ} (hn : ¬ IsZeroMode e n)
    (x : Sl2GhostSpace) : gMode b e n (pc a x) = pc a (gMode b e n x) := by
  unfold IsZeroMode at hn
  refine comm_pc_of_anticomm (fun x => gMode_anticomm_b0 ?_ x) (fun x => gMode_anticomm_c0 ?_ x) x
  · rintro ⟨-, rfl, rfl⟩; exact hn (Or.inr ⟨rfl, rfl⟩)
  · rintro ⟨-, rfl, rfl⟩; exact hn (Or.inl ⟨rfl, rfl⟩)

/-- A zero mode of another colour commutes with `pc a`. -/
theorem gMode_comm_pc_ne {a b : Fin 3} (hab : a ≠ b) (e : Fin 2) (n : ℤ) (x : Sl2GhostSpace) :
    gMode b e n (pc a x) = pc a (gMode b e n x) :=
  comm_pc_of_anticomm (fun x => gMode_anticomm_b0 (fun h => hab h.1) x)
    (fun x => gMode_anticomm_c0 (fun h => hab h.1) x) x

theorem pc_comm (a b : Fin 3) (x : Sl2GhostSpace) : pc a (pc b x) = pc b (pc a x) := by
  by_cases hab : a = b
  · subst hab; rfl
  · rw [show pc b x = b0 b (c0 b x) from rfl, ← gMode_comm_pc_ne hab, ← gMode_comm_pc_ne hab]
    rfl

theorem pc_idem (a : Fin 3) (x : Sl2GhostSpace) : pc a (pc a x) = pc a x := by
  have h := gMode_anticomm_apply a a 1 0 (-1) 0 (c0 a x)
  rw [if_pos ⟨rfl, rfl, by ring⟩, show gMode a 0 0 (gMode a 1 (-1) (c0 a x)) = 0 from
    gMode_sq a 1 (-1) x ▸ by rw [show gMode a 1 (-1) (c0 a x) = 0 from gMode_sq a 1 (-1) x,
      map_zero], add_zero] at h
  simp only [pc, Module.End.mul_apply]
  change b0 a (c0 a (b0 a (c0 a x))) = b0 a (c0 a x)
  rw [show c0 a (b0 a (c0 a x)) = c0 a x from h]

theorem b0_pc (a : Fin 3) (x : Sl2GhostSpace) : b0 a (pc a x) = 0 := by
  simp only [pc, Module.End.mul_apply, gMode_sq]

theorem pc_c0 (a : Fin 3) (x : Sl2GhostSpace) : pc a (c0 a x) = 0 := by
  simp only [pc, Module.End.mul_apply, gMode_sq, map_zero]

theorem pc_of_b0 {a : Fin 3} {x : Sl2GhostSpace} (hx : b0 a x = 0) : pc a x = x := by
  have h := gMode_anticomm_apply a a 0 1 0 (-1) x
  rw [if_pos ⟨rfl, rfl, by ring⟩, hx, map_zero, add_zero] at h
  simpa only [pc, Module.End.mul_apply] using h

theorem P0_apply (x : Sl2GhostSpace) : P0 x = pc 0 (pc 1 (pc 2 x)) := rfl

/-- The product of the two other `pc`'s. -/
def Rest : Fin 3 → Module.End ℂ Sl2GhostSpace
  | 0 => pc 1 * pc 2
  | 1 => pc 0 * pc 2
  | 2 => pc 0 * pc 1

theorem P0_eq_Rest (a : Fin 3) (x : Sl2GhostSpace) : P0 x = pc a (Rest a x) := by
  match a with
  | 0 => rfl
  | 1 => simp only [P0_apply, Rest, Module.End.mul_apply]; rw [pc_comm 0 1]
  | 2 => simp only [P0_apply, Rest, Module.End.mul_apply]; rw [pc_comm 1 2, pc_comm 0 2]

theorem Rest_c0 (a : Fin 3) (x : Sl2GhostSpace) : Rest a (c0 a x) = c0 a (Rest a x) := by
  match a with
  | 0 =>
    simp only [Rest, Module.End.mul_apply]
    rw [← gMode_comm_pc_ne (by decide), ← gMode_comm_pc_ne (by decide)]
  | 1 =>
    simp only [Rest, Module.End.mul_apply]
    rw [← gMode_comm_pc_ne (by decide), ← gMode_comm_pc_ne (by decide)]
  | 2 =>
    simp only [Rest, Module.End.mul_apply]
    rw [← gMode_comm_pc_ne (by decide), ← gMode_comm_pc_ne (by decide)]

theorem b0_P0 (a : Fin 3) (x : Sl2GhostSpace) : b0 a (P0 x) = 0 := by
  rw [P0_eq_Rest a, b0_pc]

theorem P0_c0 (a : Fin 3) (x : Sl2GhostSpace) : P0 (c0 a x) = 0 := by
  rw [P0_eq_Rest a, Rest_c0, pc_c0]

theorem P0_of_b0 {x : Sl2GhostSpace} (hx : ∀ a, b0 a x = 0) : P0 x = x := by
  have h2 := pc_of_b0 (hx 2)
  have h1 : pc 1 x = x := pc_of_b0 (hx 1)
  have h0 : pc 0 x = x := pc_of_b0 (hx 0)
  rw [P0_apply, h2, h1, h0]

theorem P0_idem (x : Sl2GhostSpace) : P0 (P0 x) = P0 x := by
  refine P0_of_b0 fun a => b0_P0 a x

theorem gMode_comm_P0 (b : Fin 3) {e : Fin 2} {n : ℤ} (hn : ¬ IsZeroMode e n)
    (x : Sl2GhostSpace) : gMode b e n (P0 x) = P0 (gMode b e n x) := by
  simp only [P0_apply, gMode_comm_pc _ _ hn]

theorem Ppar_pc (a : Fin 3) (x : Sl2GhostSpace) : Ppar (pc a x) = pc a (Ppar x) := by
  simp only [pc, Module.End.mul_apply, Ppar_gMode, map_neg, neg_neg]

theorem Ppar_P0 (x : Sl2GhostSpace) : Ppar (P0 x) = P0 (Ppar x) := by
  simp only [P0_apply, Ppar_pc]

theorem P0_gvac : P0 gvac = gvac := P0_of_b0 fun a => gMode_gvac a 0 le_rfl

/-! ### `P0` is `B_G`-symmetric -/

theorem nrm_c0_ne (a : Fin 3) : (nrm a (0, 1) : ℂ) ≠ 0 := by
  exact_mod_cast (bgColourNorm_pos a (0, 1)).ne'

theorem ghostB_pc (a : Fin 3) (z y : Sl2GhostSpace) :
    ghostB (pc a z) y = ghostB z (pc a y) := by
  have hs : swapMode (0, 1) = (0, 1) := by simp [swapMode]
  have hb : b0 a = An a (0, 1) := rfl
  have hc : c0 a = Cr a (0, 1) := rfl
  simp only [pc, Module.End.mul_apply]
  rw [hb, hc, ghostB_An, hs, Ppar_gMode, LinearMap.map_neg, LinearMap.neg_apply, ghostB_Cr, hs,
    Ppar_Ppar]
  have hm : modeCoef a (0, 1) = 1 := by unfold modeCoef; simp
  have hr : modeR (0, 1) = 0 := by unfold modeR; simp
  have hk : anConst a (0, 1) * crConst a (0, 1) = -1 := by
    simp only [anConst, crConst, anCoef, hs, hm, hr, neg_zero, zpow_zero, map_one, mul_one,
      inv_one]
    push_cast
    field_simp [nrm_c0_ne a]
  linear_combination (-(ghostB z) ((An a (0, 1)) ((Cr a (0, 1)) y))) * hk

theorem ghostB_P0 (z y : Sl2GhostSpace) : ghostB (P0 z) y = ghostB z (P0 y) := by
  calc ghostB (P0 z) y = ghostB (pc 0 (pc 1 (pc 2 z))) y := by rw [P0_apply]
    _ = ghostB z (pc 2 (pc 1 (pc 0 y))) := by rw [ghostB_pc, ghostB_pc, ghostB_pc]
    _ = ghostB z (P0 y) := by
      rw [P0_apply, pc_comm 1 0, pc_comm 2 0, pc_comm 2 1]

/-- `c₀`-free states. -/
def C0 (y : Sl2GhostSpace) : Prop := P0 y = y

theorem ghostB_zeroMode_left {a : Fin 3} {e : Fin 2} {n : ℤ} (hn : IsZeroMode e n)
    {y y' : Sl2GhostSpace} (hy : C0 y) (hy' : C0 y') : ghostB (gMode a e n y) y' = 0 := by
  rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h : gMode a 0 0 y = 0 := by
      have := b0_P0 a y
      rwa [show P0 y = y from hy] at this
    rw [h, map_zero, LinearMap.zero_apply]
  · calc ghostB (c0 a y) y' = ghostB (c0 a y) (P0 y') := by rw [show P0 y' = y' from hy']
      _ = ghostB (P0 (c0 a y)) y' := (ghostB_P0 _ _).symm
      _ = 0 := by rw [P0_c0, map_zero, LinearMap.zero_apply]

theorem ghostB_zeroMode_right {a : Fin 3} {e : Fin 2} {n : ℤ} (hn : IsZeroMode e n)
    {y y' : Sl2GhostSpace} (hy : C0 y) (hy' : C0 y') : ghostB y (gMode a e n y') = 0 := by
  rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h : gMode a 0 0 y' = 0 := by
      have := b0_P0 a y'
      rwa [show P0 y' = y' from hy'] at this
    rw [h, map_zero]
  · calc ghostB y (c0 a y') = ghostB (P0 y) (c0 a y') := by rw [show P0 y = y from hy]
      _ = ghostB y (P0 (c0 a y')) := ghostB_P0 _ _
      _ = 0 := by rw [P0_c0, map_zero]

/-! ### The ghost current and the modes -/

theorem ghostJ_bMode (a c : Fin 3) (n m : ℤ) (x : Sl2GhostSpace) :
    ghostJ a n (gMode c 0 m x) =
      gMode c 0 m (ghostJ a n x) + ∑ i, fabc a c i • gMode i 0 (m + n) x := by
  have h := translationCovariant_sl2GhostSVA.mode_commutator_bound (bGhost_odd c)
    (ghostCurrent_even a) 1 (fun j hj => bGhost_high_ghostCurrent c a j (by omega)) m n
  simp only [koszul_zero_right, one_smul, Finset.sum_range_one, gBinom_zero, Nat.cast_zero,
    sub_zero, one_smul] at h
  rw [bGhost_zero_ghostCurrent c a] at h
  have e : mode (sl2GhostSVA.Y (-∑ i : Fin 3, fabc a c i • bGhost i)) (m + n) =
      -∑ i, fabc a c i • gMode i 0 (m + n) := by
    simp only [Fin.sum_univ_three, map_neg, map_add, map_smul, mode_neg, mode_add, mode_smul]
    rfl
  rw [e] at h
  have h' := LinearMap.congr_fun h x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply,
    LinearMap.sum_apply, LinearMap.smul_apply] at h'
  change gMode c 0 m (ghostJ a n x) - ghostJ a n (gMode c 0 m x) = _ at h'
  rw [← sub_eq_zero]
  rw [← sub_eq_zero] at h'
  rw [← neg_eq_zero, ← h']
  abel

theorem ghostJ_cMode (a c : Fin 3) (n m : ℤ) (x : Sl2GhostSpace) :
    ghostJ a n (gMode c 1 m x) =
      gMode c 1 m (ghostJ a n x) + ∑ i, (-fabc a i c) • gMode i 1 (m + n) x := by
  have h := translationCovariant_sl2GhostSVA.mode_commutator_bound (cGhost_odd c)
    (ghostCurrent_even a) 1 (fun j hj => cGhost_high_ghostCurrent c a j (by omega)) m n
  simp only [koszul_zero_right, one_smul, Finset.sum_range_one, gBinom_zero, Nat.cast_zero,
    sub_zero, one_smul] at h
  rw [cGhost_zero_ghostCurrent c a] at h
  have e : mode (sl2GhostSVA.Y (∑ i : Fin 3, fabc a i c • cGhost i)) (m + n) =
      ∑ i, fabc a i c • gMode i 1 (m + n) := by
    simp only [Fin.sum_univ_three, map_add, map_smul, mode_add, mode_smul]
    rfl
  rw [e] at h
  have h' := LinearMap.congr_fun h x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
    LinearMap.smul_apply] at h'
  change gMode c 1 m (ghostJ a n x) - ghostJ a n (gMode c 1 m x) = _ at h'
  simp only [neg_smul, Finset.sum_neg_distrib]
  rw [← h']
  abel

/-- The commutator coefficients of the ghost current with the ghost modes. -/
def coefJ (a c i : Fin 3) (e : Fin 2) : ℂ := if e = 0 then fabc a c i else -fabc a i c

theorem ghostJ_gMode (a c : Fin 3) (e : Fin 2) (n m : ℤ) (x : Sl2GhostSpace) :
    ghostJ a n (gMode c e m x) =
      gMode c e m (ghostJ a n x) + ∑ i, coefJ a c i e • gMode i e (m + n) x := by
  match e with
  | 0 => simp only [coefJ, if_true]; exact ghostJ_bMode a c n m x
  | 1 => simp only [coefJ, one_ne_zero, if_false]; exact ghostJ_cMode a c n m x

theorem ghostJ_gvac (a : Fin 3) {n : ℤ} (hn : 0 ≤ n) : ghostJ a n gvac = 0 := by
  rw [gvac_eq]
  exact (sl2GhostSVA.creation (ghostCurrent a)).2 n hn

theorem Ppar_ghostJ (a : Fin 3) (n : ℤ) (y : Sl2GhostSpace) :
    Ppar (ghostJ a n y) = ghostJ a n (Ppar y) := by
  obtain ⟨y0, hy0, y1, hy1, rfl⟩ := (TensorVA.parGr sl2GhostSVA).exists_parity_decomp y
  have h0 : ghostJ a n y0 ∈ sl2GhostSVA.parity (0 + 0) :=
    sl2GhostSVA.parity_mode (ghostCurrent a) (ghostCurrent_even a) y0 hy0 n
  have h1 : ghostJ a n y1 ∈ sl2GhostSVA.parity (0 + 1) :=
    sl2GhostSVA.parity_mode (ghostCurrent a) (ghostCurrent_even a) y1 hy1 n
  rw [zero_add] at h0 h1
  rw [map_add, map_add, map_add, ParityGrading.koszulOp_homog _ 1 h0,
    ParityGrading.koszulOp_homog _ 1 h1, ParityGrading.koszulOp_homog _ 1 hy0,
    ParityGrading.koszulOp_homog _ 1 hy1, map_add, map_smul, map_smul]

/-! ### Skewness of the ghost current on `c₀`-free states -/

/-- The skewness defect `B_G(J_m y, y') + B_G(y, J_{-m} y')`. -/
def Jdef (a : Fin 3) (m : ℤ) (y y' : Sl2GhostSpace) : ℂ :=
  ghostB (ghostJ a m y) y' + ghostB y (ghostJ a (-m) y')

theorem Jdef_add (a : Fin 3) (m : ℤ) (y z y' : Sl2GhostSpace) :
    Jdef a m (y + z) y' = Jdef a m y y' + Jdef a m z y' := by
  simp only [Jdef, map_add, LinearMap.add_apply]; ring

theorem Jdef_smul (a : Fin 3) (m : ℤ) (c : ℂ) (y y' : Sl2GhostSpace) :
    Jdef a m (c • y) y' = c * Jdef a m y y' := by
  simp only [Jdef, map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

theorem Jdef_zero (a : Fin 3) (m : ℤ) (y' : Sl2GhostSpace) : Jdef a m 0 y' = 0 := by
  simp [Jdef]

theorem Jdef_right_add (a : Fin 3) (m : ℤ) (y y' z' : Sl2GhostSpace) :
    Jdef a m y (y' + z') = Jdef a m y y' + Jdef a m y z' := by
  simp only [Jdef, map_add]; ring

theorem Jdef_right_smul (a : Fin 3) (m : ℤ) (c : ℂ) (y y' : Sl2GhostSpace) :
    Jdef a m y (c • y') = c * Jdef a m y y' := by
  simp only [Jdef, map_smul, smul_eq_mul]; ring

theorem C0_P0 (x : Sl2GhostSpace) : C0 (P0 x) := P0_idem x

theorem C0_gvac : C0 gvac := P0_gvac

theorem C0_Ppar {y : Sl2GhostSpace} (hy : C0 y) : C0 (Ppar y) := by
  unfold C0 at *; rw [← Ppar_P0, hy]

theorem C0_gMode {b : Fin 3} {e : Fin 2} {n : ℤ} (hn : ¬ IsZeroMode e n) {y : Sl2GhostSpace}
    (hy : C0 y) : C0 (gMode b e n y) := by
  unfold C0 at *; rw [← gMode_comm_P0 b hn, hy]

theorem isZeroMode_trIdx_iff {e : Fin 2} {m : ℤ} : IsZeroMode e (trIdx e m) ↔ IsZeroMode e m := by
  constructor
  · intro h
    by_contra h'
    exact not_isZeroMode_trIdx h' h
  · intro h
    by_contra h'
    have := not_isZeroMode_trIdx h'
    rw [trIdx_trIdx] at this
    exact this h

/-- The transposes from the vacuum (any mode). -/
theorem ghostB_gMode_gvac (i : Fin 3) (e : Fin 2) (n : ℤ) {y : Sl2GhostSpace} (hy : C0 y) :
    ghostB (gMode i e n gvac) y = Complex.I * ghostB gvac (gMode i e (trIdx e n) y) := by
  by_cases hn : IsZeroMode e n
  · rw [ghostB_zeroMode_left hn C0_gvac hy,
      ghostB_zeroMode_right (isZeroMode_trIdx_iff.mpr hn) C0_gvac hy, mul_zero]
  · rw [ghostB_gMode i e n hn, Ppar_gvac]

theorem trIdx_add (e : Fin 2) (k m : ℤ) : trIdx e (k + m) = trIdx e k - m := by
  unfold trIdx; split_ifs <;> ring

/-- A creation mode other than `c₀` has an annihilating transpose. -/
theorem trIdx_nonneg_of_cr {q : ℕ × Fin 2} (hq : q ≠ (0, 1)) : 0 ≤ trIdx q.2 (-(q.1 : ℤ) - 1) := by
  obtain ⟨k, e⟩ := q
  unfold trIdx
  match e with
  | 0 => simp; omega
  | 1 =>
    simp only [one_ne_zero, if_false]
    rcases k with _ | k
    · exact absurd rfl hq
    · push_cast; omega

theorem not_isZeroMode_cr {q : ℕ × Fin 2} (hq : q ≠ (0, 1)) :
    ¬ IsZeroMode q.2 (-(q.1 : ℤ) - 1) := by
  obtain ⟨k, e⟩ := q
  unfold IsZeroMode
  rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
  · omega
  · exact hq (Prod.ext (by simp only at h ⊢; omega) rfl)

/-- The pairing of the current from the vacuum against the vacuum (weight orthogonality);
proved below. -/
def JvacVac : Prop := ∀ (a : Fin 3) (m : ℤ), Jdef a m gvac gvac = 0

/-- The vacuum against every `c₀`-free state. -/
theorem Jdef_gvac (hvv : JvacVac) (a : Fin 3) (m : ℤ) (x : Sl2GhostSpace) :
    Jdef a m gvac (P0 x) = 0 := by
  revert m
  refine ghost_induction (fun x => ∀ m, Jdef a m gvac (P0 x) = 0)
    (fun m => by simp [Jdef]) (fun x y hx hy m => by rw [map_add, Jdef_right_add, hx, hy, add_zero])
    (fun c x hx m => by rw [map_smul, Jdef_right_smul, hx, mul_zero])
    (fun m => by rw [P0_gvac]; exact hvv a m) ?_ x
  intro c q x _ m
  by_cases hq : q = (0, 1)
  · subst hq
    rw [show Cr c (0, 1) x = c0 c x from rfl, P0_c0]
    simp [Jdef]
  have hX := not_isZeroMode_cr hq
  set e := q.2
  set k : ℤ := -(q.1 : ℤ) - 1
  have hCr : Cr c q = gMode c e k := rfl
  rw [hCr, ← gMode_comm_P0 c hX]
  set y := P0 x
  have hy : C0 y := C0_P0 x
  have hk' := trIdx_nonneg_of_cr hq
  have hXv : gMode c e (trIdx e k) gvac = 0 := gMode_gvac c e hk'
  -- `X' (J_m |0⟩) = -Σ coefJ • mode |0⟩`
  have hc : gMode c e (trIdx e k) (ghostJ a m gvac) =
      -∑ i, coefJ a c i e • gMode i e (trIdx e k + m) gvac := by
    have h := ghostJ_gMode a c e m (trIdx e k) gvac
    rw [hXv, map_zero] at h
    rw [eq_neg_iff_add_eq_zero, ← h]
  have t1 : ghostB (ghostJ a m gvac) (gMode c e k y) =
      -∑ i, coefJ a c i e * ghostB gvac (gMode i e (k - m) y) := by
    rw [ghostB_gMode_right c e k hX, Ppar_ghostJ, Ppar_gvac, hc]
    simp only [map_neg, map_sum, map_smul, LinearMap.neg_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, mul_neg]
    rw [neg_inj]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ghostB_gMode_gvac i e _ hy, trIdx_add, trIdx_trIdx]
    linear_combination (-(coefJ a c i e * ghostB gvac (gMode i e (k - m) y))) * Complex.I_mul_I
  have t2 : ghostB gvac (ghostJ a (-m) (gMode c e k y)) =
      ∑ i, coefJ a c i e * ghostB gvac (gMode i e (k - m) y) := by
    rw [ghostJ_gMode, map_add, ghostB_gMode_right c e k hX, Ppar_gvac, hXv, map_zero,
      LinearMap.zero_apply, mul_zero, zero_add, map_sum]
    simp only [map_smul, smul_eq_mul, sub_eq_add_neg]
  rw [Jdef, t1, t2, neg_add_cancel]

/-- The induction step: a nonzero mode applied to a `c₀`-free state. -/
theorem Jdef_step (a c : Fin 3) (e : Fin 2) (k : ℤ) (hX : ¬ IsZeroMode e k) {y0 : Sl2GhostSpace}
    (hy0 : C0 y0) (ih : ∀ m y'', C0 y'' → Jdef a m (Ppar y0) y'' = 0) (m : ℤ)
    {y' : Sl2GhostSpace} (hy' : C0 y') : Jdef a m (gMode c e k y0) y' = 0 := by
  have hX' : ¬ IsZeroMode e (trIdx e k) := not_isZeroMode_trIdx hX
  have hP := C0_Ppar hy0
  -- the three pieces
  have t1 : ghostB (gMode c e k (ghostJ a m y0)) y' =
      -(Complex.I * ghostB (Ppar y0) (ghostJ a (-m) (gMode c e (trIdx e k) y'))) := by
    rw [ghostB_gMode c e k hX, Ppar_ghostJ]
    have h := ih m (gMode c e (trIdx e k) y') (C0_gMode (b := c) hX' hy')
    rw [Jdef] at h
    rw [eq_neg_of_add_eq_zero_left h, mul_neg]
  have t2 : ghostB (ghostJ a m (gMode c e k y0)) y' =
      ghostB (gMode c e k (ghostJ a m y0)) y' +
        ∑ i, coefJ a c i e * ghostB (gMode i e (k + m) y0) y' := by
    rw [ghostJ_gMode, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have t3 : ghostB (gMode c e k y0) (ghostJ a (-m) y') =
      Complex.I * ghostB (Ppar y0) (ghostJ a (-m) (gMode c e (trIdx e k) y')) -
        Complex.I * ∑ i, coefJ a c i e * ghostB (Ppar y0) (gMode i e (trIdx e k + -m) y') := by
    rw [ghostB_gMode c e k hX, ghostJ_gMode a c e (-m) (trIdx e k) y', map_add, map_sum]
    simp only [map_smul, smul_eq_mul]
    ring
  have t4 : ∀ i, coefJ a c i e * ghostB (gMode i e (k + m) y0) y' =
      Complex.I * (coefJ a c i e * ghostB (Ppar y0) (gMode i e (trIdx e k + -m) y')) := by
    intro i
    have hidx : trIdx e k + -m = trIdx e (k + m) := by rw [trIdx_add]; ring
    rw [hidx]
    by_cases hz : IsZeroMode e (k + m)
    · rw [ghostB_zeroMode_left hz hy0 hy',
        ghostB_zeroMode_right (isZeroMode_trIdx_iff.mpr hz) hP hy']
      ring
    · rw [ghostB_gMode i e _ hz]; ring
  rw [Jdef, t2, t1, t3, Finset.mul_sum, Finset.sum_congr rfl fun i _ => t4 i]
  ring

/-- **Skewness of the ghost current on `c₀`-free states**, from the vacuum pairing. -/
theorem Jdef_P0 (hvv : JvacVac) (a : Fin 3) (x : Sl2GhostSpace) :
    ∀ m y', C0 y' → Jdef a m (P0 x) y' = 0 ∧ Jdef a m (Ppar (P0 x)) y' = 0 := by
  refine ghost_induction (fun x => ∀ m y', C0 y' → Jdef a m (P0 x) y' = 0 ∧
      Jdef a m (Ppar (P0 x)) y' = 0) ?_ ?_ ?_ ?_ ?_ x
  · intro m y' _; simp [Jdef_zero]
  · intro x z hx hz m y' hy'
    obtain ⟨h1, h2⟩ := hx m y' hy'
    obtain ⟨h3, h4⟩ := hz m y' hy'
    simp only [map_add, Jdef_add, h1, h2, h3, h4, add_zero, and_self]
  · intro c x hx m y' hy'
    obtain ⟨h1, h2⟩ := hx m y' hy'
    simp only [map_smul, Jdef_smul, h1, h2, mul_zero, and_self]
  · intro m y' hy'
    rw [P0_gvac, Ppar_gvac]
    have h := Jdef_gvac hvv a m y'
    rw [show P0 y' = y' from hy'] at h
    exact ⟨h, h⟩
  · intro c q x hx m y' hy'
    by_cases hq : q = (0, 1)
    · subst hq
      rw [show Cr c (0, 1) x = c0 c x from rfl, P0_c0, map_zero]
      exact ⟨Jdef_zero a m y', Jdef_zero a m y'⟩
    have hX := not_isZeroMode_cr hq
    rw [show Cr c q x = gMode c q.2 (-(q.1 : ℤ) - 1) x from rfl, ← gMode_comm_P0 c hX]
    have hy0 : C0 (P0 x) := C0_P0 x
    refine ⟨Jdef_step a c _ _ hX hy0 (fun m y'' hy'' => (hx m y'' hy'').2) m hy', ?_⟩
    rw [Ppar_gMode, ← neg_one_smul ℂ (gMode c q.2 (-(q.1 : ℤ) - 1) (Ppar (P0 x))), Jdef_smul,
      Jdef_step a c _ _ hX (C0_Ppar hy0) (fun m y'' hy'' => by
        rw [Ppar_Ppar]; exact (hx m y'' hy'').1) m hy', mul_zero]

/-- **The ghost current is `B_G`-skew on `c₀`-free states** (from the vacuum pairing). -/
theorem ghostB_ghostJ_skew_of (hvv : JvacVac) (a : Fin 3) (m : ℤ) {y y' : Sl2GhostSpace}
    (hy : C0 y) (hy' : C0 y') : ghostB (ghostJ a m y) y' = -ghostB y (ghostJ a (-m) y') := by
  have h := (Jdef_P0 hvv a y m y' hy').1
  rw [show P0 y = y from hy, Jdef] at h
  exact eq_neg_of_add_eq_zero_left h

/-! ### The vacuum pairing: weight orthogonality -/

theorem bgPG_orthF : ∀ k k', k ≠ k' → ∀ x ∈ ghostDegF k, ∀ y ∈ ghostDegF k', bgPG x y = 0 :=
  tensorDeg_orth _ _ _ _ (tensorDeg_orth _ _ _ _ (fockDegF_orth (bgColourWeight 0))
    (fockDegF_orth (bgColourWeight 1))) (fockDegF_orth (bgColourWeight 2))

theorem gvac_mem : gvac ∈ ghostDegF 0 := by
  have h := W3_mem_ghostDegF [] [] []
  simpa [wordIdxF, wordIdx, wordR, ghNum, ghWeight] using h

theorem ghModeWt_swapMode (p : ℕ × Fin 2) : ghModeWt (swapMode p) = ghModeWt p := by
  obtain ⟨k, e⟩ := p
  match e with
  | 0 => simp [swapMode, ghModeWt, ghWt]
  | 1 =>
    rcases k with _ | k
    · simp [swapMode]
    · simp [swapMode, ghModeWt, ghWt]

theorem ghWeight_swapRev (l : SFWord) : ghWeight (swapRev l) = ghWeight l := by
  unfold ghWeight swapRev
  rw [List.map_reverse, List.sum_reverse, List.map_map]
  congr 1
  exact List.map_congr_left fun p _ => ghModeWt_swapMode p

theorem wordIdxF_wt (l : SFWord) : (wordIdxF l).1.2 = ((ghWeight l : ℕ) : ℂ) := rfl

/-- The weight-`h` part of the ghost space. -/
def gWt (h : ℂ) : Submodule ℂ Sl2GhostSpace := ⨆ (k : KF) (_ : k.1.2 = h), ghostDegF k

theorem mem_gWt {k : KF} {y : Sl2GhostSpace} (hy : y ∈ ghostDegF k) : y ∈ gWt k.1.2 :=
  Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem rfl hy)

theorem ghostConj_gWt {k : KF} {y : Sl2GhostSpace} (hy : y ∈ ghostDegF k) :
    ghostConj y ∈ gWt k.1.2 := by
  refine ghostDegF_induction (fun y => ghostConj y ∈ gWt k.1.2) (by simp)
    (fun x y hx hy => by simpa only [map_add] using Submodule.add_mem _ hx hy)
    (fun c x hx => by simpa only [LinearMap.map_smulₛₗ] using Submodule.smul_mem _ _ hx) ?_ hy
  intro i hi
  rw [ghostBasis_eq_W3, ghostConj_W]
  refine Submodule.smul_mem _ _ ?_
  have h := mem_gWt (W3_mem_ghostDegF (swapRev (fockWord i.1.1)) (swapRev (fockWord i.1.2))
    (swapRev (fockWord i.2)))
  convert h using 2
  rw [← hi]
  simp only [ghostIdx, fockIndexF, Prod.fst_add, Prod.snd_add, wordIdxF_wt, ghWeight_swapRev]

theorem ghostIR_mem {k : KF} {y : Sl2GhostSpace} (hy : y ∈ ghostDegF k) : ghostIR y ∈ ghostDegF k := by
  rw [ghostIR_eigen hy]; exact Submodule.smul_mem _ _ hy

theorem ghostIR_gWt {h : ℂ} {y : Sl2GhostSpace} (hy : y ∈ gWt h) : ghostIR y ∈ gWt h := by
  refine Submodule.iSup_induction _ (motive := fun y => ghostIR y ∈ gWt h) hy ?_ (by simp)
    (fun x y hx hy => by simpa only [map_add] using Submodule.add_mem _ hx hy)
  intro k y hy
  refine Submodule.iSup_induction _ (motive := fun y => ghostIR y ∈ gWt h) hy ?_ (by simp)
    (fun x y hx hy => by simpa only [map_add] using Submodule.add_mem _ hx hy)
  intro hk y hy
  rw [← hk]; exact mem_gWt (ghostIR_mem hy)

theorem bgPG_gvac_gWt {h : ℂ} (hh : h ≠ 0) {y : Sl2GhostSpace} (hy : y ∈ gWt h) :
    bgPG gvac y = 0 ∧ bgPG y gvac = 0 := by
  refine Submodule.iSup_induction _ (motive := fun y => bgPG gvac y = 0 ∧ bgPG y gvac = 0) hy
    ?_ (by simp [SesqForm.zero_left, SesqForm.zero_right]) ?_
  · intro k y hy
    refine Submodule.iSup_induction _ (motive := fun y => bgPG gvac y = 0 ∧ bgPG y gvac = 0) hy
      ?_ (by simp [SesqForm.zero_left, SesqForm.zero_right]) ?_
    · intro hk y hy
      have hne : (0 : KF) ≠ k := by
        intro h0; apply hh; rw [← hk, ← h0]; rfl
      exact ⟨bgPG_orthF 0 k hne _ gvac_mem _ hy, bgPG_orthF k 0 (Ne.symm hne) _ hy _ gvac_mem⟩
    · rintro x y ⟨h1, h2⟩ ⟨h3, h4⟩
      exact ⟨by rw [SesqForm.add_right, h1, h3, add_zero],
        by rw [SesqForm.add_left, h2, h4, add_zero]⟩
  · rintro x y ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by rw [SesqForm.add_right, h1, h3, add_zero],
      by rw [SesqForm.add_left, h2, h4, add_zero]⟩

theorem ghostConj_gWt' {h : ℂ} {y : Sl2GhostSpace} (hy : y ∈ gWt h) : ghostConj y ∈ gWt h := by
  refine Submodule.iSup_induction _ (motive := fun y => ghostConj y ∈ gWt h) hy ?_ (by simp)
    (fun x y hx hy => by simpa only [map_add] using Submodule.add_mem _ hx hy)
  intro k y hy
  refine Submodule.iSup_induction _ (motive := fun y => ghostConj y ∈ gWt h) hy ?_ (by simp)
    (fun x y hx hy => by simpa only [map_add] using Submodule.add_mem _ hx hy)
  intro hk y hy
  rw [← hk]; exact ghostConj_gWt hy

theorem natCast_toNat_C {j : ℤ} (hj : 0 ≤ j) : ((j.toNat : ℕ) : ℂ) = (j : ℂ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hj]

theorem modeIdxF_wt (p : ℕ × Fin 2) : (modeIdxF p).1.2 = (p.1 : ℂ) + ((ghWt p.2 : ℕ) : ℂ) := by
  simp [modeIdxF, modeIdx, ghModeWt]

theorem ghShiftF_wt (e : Fin 2) (j : ℤ) : (ghShiftF e j).1.2 = ((ghWt e : ℕ) : ℂ) + j := by
  unfold ghShiftF
  by_cases hj : 0 ≤ j
  · rw [if_pos hj, modeIdxF_wt]
    simp only
    rw [natCast_toNat_C hj]; ring
  · rw [if_neg hj, Prod.fst_neg, Prod.snd_neg, modeIdxF_wt]
    simp only
    rw [natCast_toNat_C (by omega : 0 ≤ -j - 1)]
    match e with
    | 0 => simp [ghWt]
    | 1 => simp [ghWt]

theorem bilinPred_wt {s : ℤ} {δ : KF} (h : bilinPred s δ) : δ.1.2 = (s : ℂ) + 1 := by
  obtain ⟨m, rfl⟩ := h
  rw [Prod.fst_add, Prod.snd_add, ghShiftF_wt, ghShiftF_wt]
  simp [ghWt]; push_cast; ring

theorem ghostJ_gvac_gWt (a : Fin 3) (n : ℤ) : ghostJ a n gvac ∈ gWt (-(n : ℂ)) := by
  have h := ghostCurrentCoeff_shifts a (-n - 1) 0 gvac gvac_mem
  rw [show ghostJ a n gvac = sl2GhostSVA.Y (ghostCurrent a) (-n - 1) gvac from rfl]
  refine Submodule.iSup_induction _ (motive := fun y => y ∈ gWt (-(n : ℂ))) h ?_ (by simp)
    (fun x y hx hy => Submodule.add_mem _ hx hy)
  intro δ y hy
  refine Submodule.iSup_induction _ (motive := fun y => y ∈ gWt (-(n : ℂ))) hy ?_ (by simp)
    (fun x y hx hy => Submodule.add_mem _ hx hy)
  intro hδ y hy
  have hw := mem_gWt hy
  rwa [zero_add, bilinPred_wt hδ, show ((-n - 1 : ℤ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring] at hw

/-- **The vacuum pairing of the ghost current vanishes.** -/
theorem jvacVac : JvacVac := by
  intro a m
  have hB : ∀ y, ghostB gvac y = bgPG gvac y := by
    intro y
    rw [ghostB_apply, ghostConj_gvac, ghostIR_eigen gvac_mem]
    simp
  rw [Jdef]
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · rw [ghostJ_gvac a (by omega : (0 : ℤ) ≤ -m), map_zero, add_zero, ghostB_apply]
    have h1 := ghostIR_gWt (ghostConj_gWt' (ghostJ_gvac_gWt a m))
    exact (bgPG_gvac_gWt (by exact_mod_cast neg_ne_zero.mpr hm.ne) h1).2
  · rw [ghostJ_gvac a le_rfl, neg_zero, ghostJ_gvac a le_rfl, map_zero, map_zero,
      LinearMap.zero_apply, add_zero]
  · rw [ghostJ_gvac a hm.le, map_zero, LinearMap.zero_apply, zero_add, hB]
    have h1 := ghostJ_gvac_gWt a (-m)
    exact (bgPG_gvac_gWt (by push_cast; simp; exact_mod_cast hm.ne') h1).1

/-- **The ghost current is `B_G`-skew on `c₀`-free states.** -/
theorem ghostB_ghostJ_skew (a : Fin 3) (m : ℤ) {y y' : Sl2GhostSpace} (hy : C0 y) (hy' : C0 y') :
    ghostB (ghostJ a m y) y' = -ghostB y (ghostJ a (-m) y') :=
  ghostB_ghostJ_skew_of jvacVac a m hy hy'

end

end VOA.ConcreteHodge
