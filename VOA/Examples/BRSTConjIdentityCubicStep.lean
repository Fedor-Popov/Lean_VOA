/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTConjIdentityCubic

/-!
# The induction step for `GhostCubicConj`

With `D(y) = ρ_G Q_gh ρ_G (-1)^F y + Σ_a c^a_0 J^{ā}_{gh,0} y − E_gh^{(N)} y` (`Dp`), the identity
`GhostCubicConj` says `D = 0` on `c₀`-free ghost states of weight `≤ N`. For a creation mode
`X = Cr a p` (`p ≠ c₀`) with partner `X' = Cr a (σ p)`:

  `D(X y) = -X D(y) + K_p(y)`,   (`Dp_Cr`)

where `K_p(y) = -c_p ρ_G {Q_gh, X'} ρ_G y + Σ_b c^b_0 [J^{b̄}_0, X] y − {E_gh^{(N)}, X} y` is
quadratic in the modes (`Kp`). Hence `GhostCubicConj` follows from `K_p = 0` on `c₀`-free states
of weight `≤ N − wt(p)` (`ghostCubicConj_of_Kp`).

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

/-- The zero-mode term `Σ_a c^a_0 J^{ā}_{gh,0}`. -/
def Zop (y : Sl2GhostSpace) : Sl2GhostSpace := ∑ a : Fin 3, gMode a 1 (-1) (ghostJ (adjC a) 0 y)

/-- The defect of `GhostCubicConj`, after the substitution `y ↦ (-1)^F y`. -/
def Dp (N : ℕ) (y : Sl2GhostSpace) : Sl2GhostSpace := AQ (Ppar y) + Zop y - Egh N y

/-- The quadratic step operator. -/
def Kp (N : ℕ) (a : Fin 3) (p : ℕ × Fin 2) (y : Sl2GhostSpace) : Sl2GhostSpace :=
  -(((modeCoef a p : ℝ) : ℂ) • ghostConj (Qgh (Cr a (swapMode p) (ghostConj y)) +
      Cr a (swapMode p) (Qgh (ghostConj y)))) +
    (∑ b : Fin 3, gMode b 1 (-1) (ghostJ (adjC b) 0 (Cr a p y) - Cr a p (ghostJ (adjC b) 0 y))) -
    (Egh N (Cr a p y) + Cr a p (Egh N y))

theorem Ppar_Qgh (y : Sl2GhostSpace) : Ppar (Qgh y) = -Qgh (Ppar y) := by
  obtain ⟨y0, hy0, y1, hy1, rfl⟩ := (TensorVA.parGr sl2GhostSVA).exists_parity_decomp y
  have h0 : Qgh y0 ∈ sl2GhostSVA.parity (1 + 0) :=
    sl2GhostSVA.parity_mode ghostBRSTState ghostBRSTState_odd y0 hy0 0
  have h1 : Qgh y1 ∈ sl2GhostSVA.parity (1 + 1) :=
    sl2GhostSVA.parity_mode ghostBRSTState ghostBRSTState_odd y1 hy1 0
  rw [add_zero] at h0
  rw [zmod2_one_add_one] at h1
  rw [map_add, map_add, map_add, ParityGrading.koszulOp_homog _ 1 h0,
    ParityGrading.koszulOp_homog _ 1 h1, ParityGrading.koszulOp_homog _ 1 hy0,
    ParityGrading.koszulOp_homog _ 1 hy1, map_add, map_smul, map_smul]
  simp only [koszul, parSign]
  norm_num
  abel

theorem Ppar_AQ (y : Sl2GhostSpace) : Ppar (AQ y) = -AQ (Ppar y) := by
  rw [AQ_apply, AQ_apply, ← ghostConj_Ppar, Ppar_Qgh, map_neg, ← ghostConj_Ppar]

theorem c0_Cr_anticomm (b a : Fin 3) (p : ℕ × Fin 2) (x : Sl2GhostSpace) :
    gMode b 1 (-1) (Cr a p x) = -Cr a p (gMode b 1 (-1) x) := by
  have h := gMode_anticomm_apply b a 1 p.2 (-1) (-(p.1 : ℤ) - 1) x
  rw [if_neg] at h
  · exact eq_neg_of_add_eq_zero_left h
  · rintro ⟨-, -, hm⟩
    omega

/-- **The induction step**: `D(X y) = -X D(y) + K_p(y)`. -/
theorem Dp_Cr (N : ℕ) (a : Fin 3) {p : ℕ × Fin 2} (_hp : p ≠ (0, 1)) (y : Sl2GhostSpace) :
    Dp N (Cr a p y) = -Cr a p (Dp N y) + Kp N a p y := by
  have hc : ((modeCoef a p : ℝ) : ℂ) * ((modeCoef a (swapMode p) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_comm, modeCoef_swap_mul, Complex.ofReal_one]
  -- the cubic term
  have hA : AQ (Ppar (Cr a p y)) =
      -(((modeCoef a p : ℝ) : ℂ) • ghostConj (Qgh (Cr a (swapMode p) (ghostConj y)) +
        Cr a (swapMode p) (Qgh (ghostConj y)))) - Cr a p (AQ (Ppar y)) := by
    have hX : ∀ u, ghostConj (Cr a (swapMode p) u) =
        ((modeCoef a p : ℝ) : ℂ)⁻¹ • Cr a p (Ppar (ghostConj u)) := by
      intro u
      rw [ghostConj_Cr, swapMode_swapMode, modeCoef_swap, Complex.ofReal_inv]
    rw [Ppar_gMode, map_neg, AQ_apply, ghostConj_Cr, ghostConj_Ppar, Ppar_Ppar, map_smul,
      LinearMap.map_smulₛₗ, Complex.conj_ofReal]
    have h2 : ghostConj (Cr a (swapMode p) (Qgh (ghostConj y))) =
        -(((modeCoef a p : ℝ) : ℂ)⁻¹ • Cr a p (AQ (Ppar y))) := by
      rw [hX, show Ppar (ghostConj (Qgh (ghostConj y))) = Ppar (AQ y) from rfl, Ppar_AQ, map_neg,
        smul_neg]
    have hc' : ((modeCoef a p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modeCoef_ne_zero a p
    rw [map_add ghostConj, h2, smul_add, smul_neg, smul_smul, mul_inv_cancel₀ hc', one_smul]
    abel
  -- the zero-mode term
  have hZ : Zop (Cr a p y) = -Cr a p (Zop y) +
      ∑ b : Fin 3, gMode b 1 (-1) (ghostJ (adjC b) 0 (Cr a p y) - Cr a p (ghostJ (adjC b) 0 y)) := by
    simp only [Zop, map_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_sub, c0_Cr_anticomm b a p]
    abel
  have e : Cr a p (AQ (Ppar y) + Zop y - Egh N y) =
      Cr a p (AQ (Ppar y)) + Cr a p (Zop y) - Cr a p (Egh N y) := by
    rw [map_sub, map_add]
  rw [Dp, Dp, Kp, hA, hZ, e]
  generalize (∑ b : Fin 3, gMode b 1 (-1) (ghostJ (adjC b) 0 (Cr a p y) -
    Cr a p (ghostJ (adjC b) 0 y))) = T1
  generalize ((modeCoef a p : ℝ) : ℂ) • ghostConj (Qgh (Cr a (swapMode p) (ghostConj y)) +
    Cr a (swapMode p) (Qgh (ghostConj y))) = T2
  generalize Cr a p (AQ (Ppar y)) = T3
  generalize Cr a p (Zop y) = T4
  generalize Cr a p (Egh N y) = T5
  generalize Egh N (Cr a p y) = T6
  abel

/-! ### Weight-tracking induction over `c₀`-free states -/

theorem W3_grading (l0 l1 l2 : SFWord) :
    W3 l0 l1 l2 ∈ sl2GhostSVA.grading (((ghWeight l0 + ghWeight l1 + ghWeight l2 : ℕ) : ℂ)) := by
  have h := ghostDegF_le_grading _ (W3_mem_ghostDegF l0 l1 l2)
  convert h using 2
  simp [wordIdxF_wt]

theorem P0_Cr (a : Fin 3) (p : ℕ × Fin 2) (x : Sl2GhostSpace) :
    P0 (Cr a p x) = if p = (0, 1) then 0 else Cr a p (P0 x) := by
  split_ifs with hp
  · subst hp; exact P0_c0 a x
  · exact (gMode_comm_P0 a (not_isZeroMode_cr hp) x).symm

/-- **Induction over `c₀`-free states with weight bookkeeping.** -/
theorem C0_weight_induction (Φ : ℕ → Sl2GhostSpace → Prop) (h0 : ∀ W, Φ W 0)
    (hadd : ∀ W x y, Φ W x → Φ W y → Φ W (x + y)) (hsmul : ∀ W (c : ℂ) x, Φ W x → Φ W (c • x))
    (hvac : Φ 0 gvac)
    (hstep : ∀ (W : ℕ) (y : Sl2GhostSpace), y ∈ sl2GhostSVA.grading (W : ℂ) → C0 y → Φ W y →
      ∀ a p, p ≠ (0, 1) → Φ (W + ghModeWt p) (Cr a p y))
    (W : ℕ) (y : Sl2GhostSpace) (hy : y ∈ sl2GhostSVA.grading (W : ℂ)) (hC : C0 y) : Φ W y := by
  -- words
  have hW : ∀ l0 l1 l2 : SFWord,
      Φ (ghWeight l0 + ghWeight l1 + ghWeight l2) (P0 (W3 l0 l1 l2)) := by
    have step : ∀ (a : Fin 3) (p : ℕ × Fin 2) (x : Sl2GhostSpace) (V : ℕ),
        x ∈ sl2GhostSVA.grading (V : ℂ) → Φ V (P0 x) →
        Φ (V + ghModeWt p) (P0 (Cr a p x)) := by
      intro a p x V hx hΦ
      rw [P0_Cr]
      split_ifs with hp
      · exact h0 _
      · exact hstep V (P0 x) (P0_grading hx) (C0_P0 x) hΦ a p hp
    intro l0 l1 l2
    induction l0 with
    | nil =>
        induction l1 with
        | nil =>
            induction l2 with
            | nil => simp only [ghWeight_nil, add_zero]; rw [P0_gvac]; exact hvac
            | cons p l2 ih =>
                have e : W3 [] [] (p :: l2) = Cr 2 p (W3 [] [] l2) := by
                  rw [Cr2_W]; simp [len2]
                have hx := W3_grading [] [] l2
                have := step 2 p _ _ hx ih
                rw [e, ghWeight_cons]
                convert this using 1
                ring
        | cons p l1 ih =>
            have e : W3 [] (p :: l1) l2 = Cr 1 p (W3 [] l1 l2) := by
              rw [Cr1_W]; simp [len2]
            have hx := W3_grading [] l1 l2
            have := step 1 p _ _ hx ih
            rw [e, ghWeight_cons]
            convert this using 1
            ring
    | cons p l0 ih =>
        have hx := W3_grading l0 l1 l2
        have := step 0 p _ _ hx ih
        rw [← Cr0_W, ghWeight_cons]
        convert this using 1
        ring
  -- pieces
  have hy' : y ∈ gWt (W : ℂ) := grading_le_gWt _ hy
  rw [← show P0 y = y from hC]
  refine Submodule.iSup_induction _ (motive := fun y => Φ W (P0 y)) hy' ?_ (by simpa using h0 W)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact hadd W _ _ hx hy)
  intro k z hz
  refine Submodule.iSup_induction _ (motive := fun y => Φ W (P0 y)) hz ?_ (by simpa using h0 W)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact hadd W _ _ hx hy)
  intro hk z hz
  refine ghostDegF_induction (fun z => Φ W (P0 z)) (by simpa using h0 W)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact hadd W _ _ hx hy)
    (fun c x hx => by beta_reduce at hx ⊢; rw [map_smul]; exact hsmul W c _ hx) ?_ hz
  intro i hi
  rw [ghostBasis_eq_W3]
  have hw := hW (fockWord i.1.1) (fockWord i.1.2) (fockWord i.2)
  have hwt : ghWeight (fockWord i.1.1) + ghWeight (fockWord i.1.2) + ghWeight (fockWord i.2) = W := by
    have h1 : (ghostIdx i).1.2 = (W : ℂ) := by rw [hi, hk]
    simp only [ghostIdx, fockIndexF, Prod.fst_add, Prod.snd_add, wordIdxF_wt] at h1
    exact_mod_cast h1
  rwa [hwt] at hw

/-! ### `GhostCubicConj` from the vanishing of the step operators -/

/-- The step operators vanish in the relevant weight range. -/
def KpZero : Prop :=
  ∀ (N : ℕ) (a : Fin 3) (p : ℕ × Fin 2), p ≠ (0, 1) → ∀ W : ℕ, W + ghModeWt p ≤ N →
    ∀ y ∈ sl2GhostSVA.grading (W : ℂ), C0 y → Kp N a p y = 0

theorem AQ_gvac : AQ gvac = 0 := by
  rw [AQ_apply, ghostConj_gvac, Qgh_gvac, map_zero]

theorem Egh_gvac (N : ℕ) : Egh N gvac = 0 := by
  simp only [Egh, closedE, casContract, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.mul_apply]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hm1 : (0 : ℤ) ≤ (m : ℤ) := by positivity
  simp only [ghostJ_gvac _ hm1, gMode_gvac _ _ hm1, map_zero, sub_zero, Finset.sum_const_zero,
    smul_zero]

theorem Dp_gvac (N : ℕ) : Dp N gvac = 0 := by
  have hZ : Zop gvac = 0 := by
    simp only [Zop, ghostJ_gvac _ le_rfl, map_zero, Finset.sum_const_zero]
  rw [Dp, Ppar_gvac, AQ_gvac, Egh_gvac, hZ, add_zero, sub_zero]

theorem Dp_zero_of_Kp (hK : KpZero) (N W : ℕ) (hW : W ≤ N) (y : Sl2GhostSpace)
    (hy : y ∈ sl2GhostSVA.grading (W : ℂ)) (hC : C0 y) : Dp N y = 0 := by
  refine C0_weight_induction (fun W y => W ≤ N → Dp N y = 0) (fun W _ => ?_)
    (fun W x y hx hy hW => ?_) (fun W c x hx hW => ?_) (fun _ => Dp_gvac N) ?_ W y hy hC hW
  · simp [Dp, Zop]
  · have h1 := hx hW; have h2 := hy hW
    simp only [Dp, Zop, map_add, Finset.sum_add_distrib] at h1 h2 ⊢
    rw [← sub_eq_zero] at h1 h2 ⊢
    calc _ = (AQ (Ppar x) + ∑ a : Fin 3, gMode a 1 (-1) (ghostJ (adjC a) 0 x) - Egh N x - 0) +
          (AQ (Ppar y) + ∑ a : Fin 3, gMode a 1 (-1) (ghostJ (adjC a) 0 y) - Egh N y - 0) := by abel
      _ = 0 := by rw [h1, h2, add_zero]
  · have h1 := hx hW
    simp only [Dp, Zop, map_smul, ← Finset.smul_sum] at h1 ⊢
    rw [← smul_add, ← smul_sub, h1, smul_zero]
  · intro V y hy hC hΦ a p hp hVp
    rw [Dp_Cr N a hp y, hΦ (by omega), map_zero, neg_zero, zero_add]
    exact hK N a p hp V hVp y hy hC

theorem Ppar_ghostDegF {k : KF} {z : Sl2GhostSpace} (hz : z ∈ ghostDegF k) : Ppar z ∈ ghostDegF k := by
  have hpar := sl2GhostGrading_le_parity _ (ghostDeg_le_ghost _ (ghostDegF_le_ghostDeg k hz))
  rw [ParityGrading.koszulOp_homog _ 1 hpar]
  exact Submodule.smul_mem _ _ hz

theorem Ppar_grading {h : ℂ} {y : Sl2GhostSpace} (hy : y ∈ sl2GhostSVA.grading h) :
    Ppar y ∈ sl2GhostSVA.grading h := by
  refine gWt_le_grading h ?_
  have hy' := grading_le_gWt h hy
  refine Submodule.iSup_induction _ (motive := fun y => Ppar y ∈ gWt h) hy' ?_ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro k z hz
  refine Submodule.iSup_induction _ (motive := fun y => Ppar y ∈ gWt h) hz ?_ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro hk z hz
  rw [← hk]; exact mem_gWt (Ppar_ghostDegF hz)

/-- **`GhostCubicConj` from the vanishing of the step operators.** -/
theorem ghostCubicConj_of_Kp (hK : KpZero) : GhostCubicConj := by
  intro N k hk y hy hC
  have hPy : Ppar y ∈ sl2GhostSVA.grading (k : ℂ) := Ppar_grading hy
  have h := Dp_zero_of_Kp hK N k hk (Ppar y) hPy (C0_Ppar hC)
  rw [Dp, Ppar_Ppar, Zop, sub_eq_zero] at h
  exact h

end

end VOA.ConcreteHodge
