/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.GhostConjFock

/-!
# Compact conjugation of the ghost current zero modes, and the ghost factor

* `ghostConj_Cr` — `ρ_G` intertwines every ghost creation operator:
  `ρ_G C_a(p) = c_a(p) C_a(σ p) (-1)^F ρ_G` (checked on word tensors, where all signs are
  explicit, then extended by antilinearity);
* `ghostCurrent_cMode` — the ghost current zero mode acts on the `c` modes by the coadjoint action
  (the antighost counterpart `ghostCurrent_antiMode` is in `BGPackageLambda`);
* `ghostConj_J0` — **`ρ_G J^a_0 = -J^{ā}_0 ρ_G` on every `c₀`-free fine ghost piece**, by
  induction on word tensors built from the vacuum by creation operators; the step is the finite
  `sl₂` identity `f^{ac}{}_i w_i = w_c f^{ā i}{}_c` (`gen_b`, `gen_c`), which is where the colour
  factor `w_h = 2` is forced. (On `c₀`-states the identity fails, as expected.)
* `bgGhostData : GhostBGData bgPG` — **the ghost factor of the Beem–Garner data, with no
  hypothesis**.

Everything is proved outright.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open VOA.SympFerm VOA.Ghost AffineVOA
open scoped TensorProduct

noncomputable section

/-! ### Creation operators and the intertwining -/

/-- The creation operator of the mode `p` in colour `a`. -/
abbrev Cr (a : Fin 3) (p : ℕ × Fin 2) : Module.End ℂ Sl2GhostSpace :=
  gMode a p.2 (-(p.1 : ℤ) - 1)

theorem ghField_cr (p : ℕ × Fin 2) (l : SFWord) :
    ghField p.2 (-(-(p.1 : ℤ) - 1) - 1) (stWordSF l) = stWordSF (p :: l) := by
  rw [show -(-(p.1 : ℤ) - 1) - 1 = (p.1 : ℤ) by ring]
  simp only [ghField, Nat.cast_nonneg, if_true, Int.toNat_natCast, creGh, creBase,
    LinearMap.mulLeft_apply, stWordSF_cons]

theorem len2_cons (p : ℕ × Fin 2) (l : SFWord) : len2 (p :: l) = len2 l + 1 := by
  simp [len2]

/-- The parity operator of the three-pair space. -/
abbrev Ppar : Module.End ℂ Sl2GhostSpace := (TensorVA.parGr sl2GhostSVA).koszulOp 1

theorem pair_mem_parity (l0 l1 : SFWord) :
    stWordSF l0 ⊗ₜ[ℂ] stWordSF l1 ∈ ghostPairSVA.parity (len2 l0 + len2 l1) :=
  TensorVA.tmul_mem_tenParity _ _ (stWordSF_mem_evenOdd l0)
    (by rw [add_sub_cancel_left]; exact stWordSF_mem_evenOdd l1)

theorem W3_mem_parity (l0 l1 l2 : SFWord) :
    W3 l0 l1 l2 ∈ sl2GhostSVA.parity (len2 l0 + len2 l1 + len2 l2) :=
  TensorVA.tmul_mem_tenParity _ _ (pair_mem_parity l0 l1)
    (by rw [add_sub_cancel_left]; exact stWordSF_mem_evenOdd l2)

theorem Ppar_W (l0 l1 l2 : SFWord) :
    Ppar (W3 l0 l1 l2) = koszul 1 (len2 l0 + len2 l1 + len2 l2) • W3 l0 l1 l2 :=
  ParityGrading.koszulOp_homog _ 1 (W3_mem_parity l0 l1 l2)

theorem Cr0_W (p : ℕ × Fin 2) (l0 l1 l2 : SFWord) : Cr 0 p (W3 l0 l1 l2) = W3 (p :: l0) l1 l2 := by
  rw [Cr, W3, gMode_tmul_zero, ghField_cr]; rfl

theorem Cr1_W (p : ℕ × Fin 2) (l0 l1 l2 : SFWord) :
    Cr 1 p (W3 l0 l1 l2) = koszul 1 (len2 l0) • W3 l0 (p :: l1) l2 := by
  rw [Cr, W3, gMode_tmul_one, ghField_cr, Kf_stWordSF, W3, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul']

theorem Cr2_W (p : ℕ × Fin 2) (l0 l1 l2 : SFWord) :
    Cr 2 p (W3 l0 l1 l2) = koszul 1 (len2 l0 + len2 l1) • W3 l0 l1 (p :: l2) := by
  rw [Cr, W3, gMode_tmul_two, ghField_cr,
    ParityGrading.koszulOp_homog _ 1 (pair_mem_parity l0 l1), W3]
  simp only [TensorProduct.smul_tmul']

theorem koszul_one_succ (n : ZMod 2) : koszul 1 (n + 1) = -koszul 1 n := by
  rcases zmod2_cases n with rfl | rfl <;> norm_num [koszul, parSign]
  decide

theorem stWordSF_append_single (l : SFWord) (q : ℕ × Fin 2) :
    stWordSF (l ++ [q]) = koszul 1 (len2 l) • stWordSF (q :: l) := by
  induction l with
  | nil => simp [len2]
  | cons p l ih =>
      have hac : CliffordAlgebra.ι QSF (Finsupp.single p (1 : ℂ)) *
          CliffordAlgebra.ι QSF (Finsupp.single q 1) =
          -(CliffordAlgebra.ι QSF (Finsupp.single q 1) *
            CliffordAlgebra.ι QSF (Finsupp.single p 1)) := by
        have h := creBase_anticomm p q (1 : FockSF)
        simp only [creBase, LinearMap.mulLeft_apply, mul_one] at h
        exact eq_neg_of_add_eq_zero_left h
      rw [List.cons_append, stWordSF_cons, ih, mul_smul_comm, stWordSF_cons, ← mul_assoc, hac,
        neg_mul, mul_assoc, ← stWordSF_cons p l, ← stWordSF_cons q (p :: l), smul_neg,
        len2_cons, koszul_one_succ, neg_smul]

theorem swapRev_cons (p : ℕ × Fin 2) (l : SFWord) :
    swapRev (p :: l) = swapRev l ++ [swapMode p] := by simp [swapRev]

theorem coefProd_cons (a : Fin 3) (p : ℕ × Fin 2) (l : SFWord) :
    coefProd a (p :: l) = modeCoef a p * coefProd a l := by simp [coefProd]

theorem W3_append0 (l0 l1 l2 : SFWord) (q : ℕ × Fin 2) :
    W3 (l0 ++ [q]) l1 l2 = koszul 1 (len2 l0) • W3 (q :: l0) l1 l2 := by
  rw [W3, stWordSF_append_single, W3, TensorProduct.smul_tmul', TensorProduct.smul_tmul']

theorem W3_append1 (l0 l1 l2 : SFWord) (q : ℕ × Fin 2) :
    W3 l0 (l1 ++ [q]) l2 = koszul 1 (len2 l1) • W3 l0 (q :: l1) l2 := by
  rw [W3, stWordSF_append_single, W3, TensorProduct.tmul_smul]
  simp only [TensorProduct.smul_tmul']

theorem W3_append2 (l0 l1 l2 : SFWord) (q : ℕ × Fin 2) :
    W3 l0 l1 (l2 ++ [q]) = koszul 1 (len2 l2) • W3 l0 l1 (q :: l2) := by
  rw [W3, stWordSF_append_single, W3, TensorProduct.tmul_smul]

@[simp] theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := rfl
@[simp] theorem zmod2_one_add_one_add_one : (1 : ZMod 2) + 1 + 1 = 1 := rfl

theorem cross_shift0 (n0 n1 n2 : ZMod 2) :
    cross3 (n0 + 1) n1 n2 * koszul 1 n0 = cross3 n0 n1 n2 * koszul 1 (n0 + n1 + n2) := by
  rcases zmod2_cases n0 with rfl | rfl <;> rcases zmod2_cases n1 with rfl | rfl <;>
    rcases zmod2_cases n2 with rfl | rfl <;> simp [cross3, koszul, parSign, zmod2_one_add_one]

theorem cross_shift1 (n0 n1 n2 : ZMod 2) :
    koszul 1 n0 * cross3 n0 (n1 + 1) n2 * koszul 1 n1 =
      koszul 1 (n0 + n1 + n2) * cross3 n0 n1 n2 * koszul 1 n0 := by
  rcases zmod2_cases n0 with rfl | rfl <;> rcases zmod2_cases n1 with rfl | rfl <;>
    rcases zmod2_cases n2 with rfl | rfl <;> simp [cross3, koszul, parSign, zmod2_one_add_one]

theorem cross_shift2 (n0 n1 n2 : ZMod 2) :
    koszul 1 (n0 + n1) * cross3 n0 n1 (n2 + 1) * koszul 1 n2 =
      koszul 1 (n0 + n1 + n2) * cross3 n0 n1 n2 * koszul 1 (n0 + n1) := by
  rcases zmod2_cases n0 with rfl | rfl <;> rcases zmod2_cases n1 with rfl | rfl <;>
    rcases zmod2_cases n2 with rfl | rfl <;> simp [cross3, koszul, parSign, zmod2_one_add_one]

theorem ghostConj_Cr_W (a : Fin 3) (p : ℕ × Fin 2) (l0 l1 l2 : SFWord) :
    ghostConj (Cr a p (W3 l0 l1 l2)) =
      ((modeCoef a p : ℝ) : ℂ) • Cr a (swapMode p) (Ppar (ghostConj (W3 l0 l1 l2))) := by
  rw [ghostConj_W, map_smul, Ppar_W, map_smul, map_smul, smul_smul, smul_smul]
  simp only [len2_swapRev]
  fin_cases a
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [Cr0_W, ghostConj_W, Cr0_W, swapRev_cons, W3_append0, smul_smul]
    congr 1
    simp only [wcoef, coefProd_cons, len2_cons, len2_swapRev]
    have h := cross_shift0 (len2 l0) (len2 l1) (len2 l2)
    push_cast
    linear_combination (((modeCoef 0 p : ℝ) : ℂ) * ((coefProd 0 l0 : ℝ) : ℂ) *
      ((coefProd 1 l1 : ℝ) : ℂ) * ((coefProd 2 l2 : ℝ) : ℂ)) * h
  · simp only [Fin.mk_one, Fin.isValue]
    rw [Cr1_W, LinearMap.map_smulₛₗ, ghostConj_W, Cr1_W, swapRev_cons, W3_append1, smul_smul,
      smul_smul, smul_smul, conj_koszul]
    simp only [len2_swapRev]
    congr 1
    simp only [wcoef, coefProd_cons, len2_cons]
    have h := cross_shift1 (len2 l0) (len2 l1) (len2 l2)
    push_cast
    linear_combination (((modeCoef 1 p : ℝ) : ℂ) * ((coefProd 0 l0 : ℝ) : ℂ) *
      ((coefProd 1 l1 : ℝ) : ℂ) * ((coefProd 2 l2 : ℝ) : ℂ)) * h
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [Cr2_W, LinearMap.map_smulₛₗ, ghostConj_W, Cr2_W, swapRev_cons, W3_append2, smul_smul,
      smul_smul, smul_smul, conj_koszul]
    simp only [len2_swapRev]
    congr 1
    simp only [wcoef, coefProd_cons, len2_cons]
    have h := cross_shift2 (len2 l0) (len2 l1) (len2 l2)
    push_cast
    linear_combination (((modeCoef 2 p : ℝ) : ℂ) * ((coefProd 0 l0 : ℝ) : ℂ) *
      ((coefProd 1 l1 : ℝ) : ℂ) * ((coefProd 2 l2 : ℝ) : ℂ)) * h

/-- **`ρ_G` intertwines the creation operators**: `ρ C_a(p) = c_a(p) C_a(σ p) (-1)^F ρ`. -/
theorem ghostConj_Cr (a : Fin 3) (p : ℕ × Fin 2) (x : Sl2GhostSpace) :
    ghostConj (Cr a p x) =
      ((modeCoef a p : ℝ) : ℂ) • Cr a (swapMode p) (Ppar (ghostConj x)) := by
  have hx : x ∈ Submodule.span ℂ (Set.range ghostBasis) := by
    rw [ghostBasis.span_eq]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [ghostBasis_eq_W3]
      exact ghostConj_Cr_W a p _ _ _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, map_add, smul_add]
  | smul c x _ hx =>
      rw [map_smul, LinearMap.map_smulₛₗ, hx, LinearMap.map_smulₛₗ, map_smul, map_smul,
        smul_comm]

/-! ### The ghost current zero modes -/

/-- The ghost current zero mode. -/
abbrev Jz (a : Fin 3) : Module.End ℂ Sl2GhostSpace := ghostJ a 0

theorem cGhost_high_ghostCurrent (b a : Fin 3) (n : ℤ) (hn : 1 ≤ n) :
    mode (sl2GhostSVA.Y (cGhost b)) n (ghostCurrent a) = 0 := by
  have h := sl2GhostSVA.grading_mode (cGhost b) (cGhost_weight b)
    (ghostCurrent a) (ghostCurrent_weight a) n
  have hbot : sl2GhostSVA.grading (0 + 1 - (n : ℂ) - 1) = ⊥ := by
    apply natSupported_sl2GhostSVA
    rintro ⟨m, hm⟩
    have hm' : ((m : ℤ) : ℂ) = ((-n : ℤ) : ℂ) := by
      push_cast
      linear_combination hm
    have : (m : ℤ) = -n := by exact_mod_cast hm'
    omega
  rw [hbot] at h
  exact h

/-- The ghost current zero mode acts on the ghost modes by the coadjoint action. -/
theorem ghostCurrent_cMode (a c : Fin 3) (m : ℤ) :
    mode (ghostCurrentField a) 0 * gMode c 1 m =
      gMode c 1 m * mode (ghostCurrentField a) 0 - ∑ i, fabc a i c • gMode i 1 m := by
  have h := translationCovariant_sl2GhostSVA.mode_commutator_bound (cGhost_odd c)
    (ghostCurrent_even a) 1 (fun j hj => cGhost_high_ghostCurrent c a j (by omega)) m 0
  simp only [koszul_zero_right, one_smul, Finset.sum_range_one, gBinom_zero, Nat.cast_zero,
    sub_zero, add_zero, one_smul] at h
  rw [cGhost_zero_ghostCurrent c a] at h
  have e : mode (sl2GhostSVA.Y (∑ i : Fin 3, fabc a i c • cGhost i)) m =
      ∑ i, fabc a i c • gMode i 1 m := by
    simp only [Fin.sum_univ_three, map_add, map_smul, mode_add, mode_smul]
    rfl
  rw [e] at h
  change gMode c 1 m * mode (ghostCurrentField a) 0 -
    mode (ghostCurrentField a) 0 * gMode c 1 m = _ at h
  rw [← h]
  abel

theorem Jz_Cr_b (a c : Fin 3) (k : ℕ) (x : Sl2GhostSpace) :
    Jz a (Cr c (k, 0) x) = Cr c (k, 0) (Jz a x) + ∑ i, fabc a c i • Cr i (k, 0) x := by
  have h := LinearMap.congr_fun (ghostCurrent_antiMode a c (-(k : ℤ) - 1)) x
  simpa [Module.End.mul_apply, LinearMap.sum_apply] using h

theorem Jz_Cr_c (a c : Fin 3) (k : ℕ) (x : Sl2GhostSpace) :
    Jz a (Cr c (k, 1) x) = Cr c (k, 1) (Jz a x) - ∑ i, fabc a i c • Cr i (k, 1) x := by
  have h := LinearMap.congr_fun (ghostCurrent_cMode a c (-(k : ℤ) - 1)) x
  simpa [Module.End.mul_apply, LinearMap.sum_apply] using h

theorem Jz_vacuum (a : Fin 3) : Jz a (W3 [] [] []) = 0 :=
  (sl2GhostSVA.creation (ghostCurrent a)).2 0 le_rfl

theorem Jz_Ppar (a : Fin 3) (y : Sl2GhostSpace) : Ppar (Jz a y) = Jz a (Ppar y) := by
  obtain ⟨y0, hy0, y1, hy1, rfl⟩ := (TensorVA.parGr sl2GhostSVA).exists_parity_decomp y
  have h0 : Jz a y0 ∈ sl2GhostSVA.parity (0 + 0) :=
    sl2GhostSVA.parity_mode (ghostCurrent a) (ghostCurrent_even a) y0 hy0 0
  have h1 : Jz a y1 ∈ sl2GhostSVA.parity (0 + 1) :=
    sl2GhostSVA.parity_mode (ghostCurrent a) (ghostCurrent_even a) y1 hy1 0
  rw [zero_add] at h0 h1
  rw [map_add, map_add, map_add, ParityGrading.koszulOp_homog _ 1 h0,
    ParityGrading.koszulOp_homog _ 1 h1, ParityGrading.koszulOp_homog _ 1 hy0,
    ParityGrading.koszulOp_homog _ 1 hy1, map_add, map_smul, map_smul]

/-! ### Compact conjugation of the ghost current zero modes -/

local notation "adjC" => AffineVOA.HighestModule.adjointColour

theorem gen_b (a c i : Fin 3) :
    fabc a c i * (colourW i : ℂ) = (colourW c : ℂ) * fabc (adjC a) i c := by
  fin_cases a <;> fin_cases c <;> fin_cases i <;>
    simp [fabc, colourW, AffineVOA.HighestModule.adjointColour, Fin.ext_iff]

theorem gen_c (a c i : Fin 3) :
    fabc a i c * (colourW c : ℂ) = (colourW i : ℂ) * fabc (adjC a) c i := by
  fin_cases a <;> fin_cases c <;> fin_cases i <;>
    simp [fabc, colourW, AffineVOA.HighestModule.adjointColour, Fin.ext_iff]

theorem conj_fabc (a c i : Fin 3) : (starRingEnd ℂ) (fabc a c i) = fabc a c i := by
  fin_cases a <;> fin_cases c <;> fin_cases i <;> simp [fabc, map_ofNat]

/-- The compact-conjugation property of the ghost current zero mode at one vector. -/
def JzCompactAt (a : Fin 3) (x : Sl2GhostSpace) : Prop :=
  ghostConj (Jz a x) = -Jz (adjC a) (ghostConj x)

theorem JzCompactAt_Cr (a c : Fin 3) (p : ℕ × Fin 2) (hp : p ≠ (0, 1)) {x : Sl2GhostSpace}
    (hx : JzCompactAt a x) : JzCompactAt a (Cr c p x) := by
  unfold JzCompactAt at hx ⊢
  obtain ⟨k, e⟩ := p
  fin_cases e
  · -- an antighost creation mode
    simp only [Fin.zero_eta, Fin.isValue]
    have hs : swapMode (k, 0) = (k + 1, 1) := by simp [swapMode]
    rw [Jz_Cr_b, map_add, ghostConj_Cr, hx, hs, map_sum, ghostConj_Cr, hs, map_smul, Jz_Cr_c]
    simp only [LinearMap.map_smulₛₗ, conj_fabc, ghostConj_Cr, hs, map_neg, Jz_Ppar,
      smul_sub, Finset.smul_sum, smul_smul, neg_sub, smul_neg]
    have hsum : ∑ i, (fabc a c i * ((modeCoef i (k, 0) : ℝ) : ℂ)) •
        Cr i (k + 1, 1) (Ppar (ghostConj x)) =
        ∑ i, (((modeCoef c (k, 0) : ℝ) : ℂ) * fabc (adjC a) i c) •
          Cr i (k + 1, 1) (Ppar (ghostConj x)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      have hw := gen_b a c i
      simp only [modeCoef, if_true]
      push_cast
      linear_combination (-((k : ℂ) + 1)) * hw
    rw [hsum]
    abel
  · -- a ghost creation mode `c_{-k}`, `k ≥ 1`
    simp only [Fin.mk_one, Fin.isValue]
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := by
      rcases k with _ | k
      · exact absurd rfl hp
      · exact ⟨k, rfl⟩
    have hs : swapMode (k + 1, 1) = (k, 0) := by simp [swapMode]
    rw [Jz_Cr_c, map_sub, ghostConj_Cr, hx, hs, map_sum, ghostConj_Cr, hs, map_smul, Jz_Cr_b]
    simp only [LinearMap.map_smulₛₗ, conj_fabc, ghostConj_Cr, hs, map_neg, Jz_Ppar,
      smul_add, Finset.smul_sum, smul_smul, neg_add, smul_neg]
    have hsum : ∑ i, (fabc a i c * ((modeCoef i (k + 1, 1) : ℝ) : ℂ)) •
        Cr i (k, 0) (Ppar (ghostConj x)) =
        ∑ i, (((modeCoef c (k + 1, 1) : ℝ) : ℂ) * fabc (adjC a) c i) •
          Cr i (k, 0) (Ppar (ghostConj x)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      have hw := gen_c a c i
      have hci : (colourW c : ℂ) ≠ 0 := by exact_mod_cast (colourW_pos c).ne'
      have hii : (colourW i : ℂ) ≠ 0 := by exact_mod_cast (colourW_pos i).ne'
      have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      simp only [modeCoef, one_ne_zero, if_false, Nat.add_eq_zero_iff, and_false]
      push_cast
      field_simp
      linear_combination (-1 : ℂ) * hw
    rw [hsum]
    abel

theorem JzCompactAt_smul (a : Fin 3) (c : ℂ) {x : Sl2GhostSpace} (hx : JzCompactAt a x) :
    JzCompactAt a (c • x) := by
  unfold JzCompactAt at hx ⊢
  rw [map_smul, LinearMap.map_smulₛₗ, hx, LinearMap.map_smulₛₗ, map_smul, smul_neg]

theorem JzCompactAt_vacuum (a : Fin 3) : JzCompactAt a (W3 [] [] []) := by
  unfold JzCompactAt
  rw [Jz_vacuum, map_zero, ghostConj_W]
  simp only [swapRev, List.map_nil, List.reverse_nil, map_smul, Jz_vacuum, smul_zero, neg_zero]

/-- **Compact conjugation of the ghost current zero modes on every `c₀`-free word tensor.** -/
theorem JzCompactAt_W3 (a : Fin 3) (l0 l1 l2 : SFWord) (h0 : ∀ p ∈ l0, p ≠ (0, 1))
    (h1 : ∀ p ∈ l1, p ≠ (0, 1)) (h2 : ∀ p ∈ l2, p ≠ (0, 1)) : JzCompactAt a (W3 l0 l1 l2) := by
  induction l0 with
  | nil =>
      induction l1 with
      | nil =>
          induction l2 with
          | nil => exact JzCompactAt_vacuum a
          | cons p l2 ih =>
              have e : W3 [] [] (p :: l2) = Cr 2 p (W3 [] [] l2) := by
                rw [Cr2_W]; simp [len2]
              rw [e]
              exact JzCompactAt_Cr a 2 p (h2 p (by simp))
                (ih fun q hq => h2 q (by simp [hq]))
      | cons p l1 ih =>
          have e : W3 [] (p :: l1) l2 = Cr 1 p (W3 [] l1 l2) := by
            rw [Cr1_W]; simp [len2]
          rw [e]
          exact JzCompactAt_Cr a 1 p (h1 p (by simp)) (ih fun q hq => h1 q (by simp [hq]))
  | cons p l0 ih =>
      rw [← Cr0_W]
      exact JzCompactAt_Cr a 0 p (h0 p (by simp)) (ih fun q hq => h0 q (by simp [hq]))

/-- **`GhostJ0Compact` for the algebraic conjugation.** -/
theorem ghostConj_J0 (k : KF) (hk : k.2 = 0) (y : Sl2GhostSpace) (hy : y ∈ ghostDegF k)
    (a : Fin 3) : ghostConj (ghostJ a 0 y) = -ghostJ (adjC a) 0 (ghostConj y) := by
  refine ghostDegF_induction (fun y => JzCompactAt a y) ?_ ?_ ?_ ?_ hy
  · simp [JzCompactAt]
  · intro x y hx hy
    unfold JzCompactAt at hx hy ⊢
    rw [map_add, map_add, hx, hy, map_add, map_add, neg_add]
  · intro c x hx
    exact JzCompactAt_smul a c hx
  · intro i hi
    obtain ⟨h0, h1, h2⟩ := ghostIdx_snd_zero (hi ▸ hk)
    rw [ghostBasis_eq_W3]
    exact JzCompactAt_W3 a _ _ _ (fockWord_c0free h0) (fockWord_c0free h1) (fockWord_c0free h2)

/-! ### The ghost factor of the Beem–Garner data -/

/-- **The ghost factor of the Beem–Garner data**, with no hypothesis: `ρ_G² = 1`,
`P = i^{2R} B_G(ρ_G ·, ·)`, the degree clause and compact conjugation of the ghost current zero
modes are all proved. -/
def bgGhostData : GhostBGData bgPG where
  B := ghostB
  ρ := ghostConj
  s := 1
  ρ_sq := fun _ _ y _ => by rw [ghostConj_sq, one_smul]
  P_eq := fun k _ y hy y' => ghostB_P_eq k y hy y'
  ρ_deg := fun k hk y hy => ghostConj_deg k hk y hy
  ρ_J0 := fun k hk y hy a => ghostConj_J0 k hk y hy a

theorem bgGhostData_s : bgGhostData.s ≠ 0 := one_ne_zero

end

end VOA.ConcreteHodge
