/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTConjIdentityBE

/-!
# `GhostConjRhoD`: reduction to a ghost-only identity for the cubic charge

The BRST charge on a pure tensor is `Q(x ⊗ y) = Σ_a Σ_n J^a_n x ⊗ c^a_{-n} y + x ⊗ Q_gh y`
(`brstQ_tmul`, from `semiInfiniteQ_tmul`). Conjugating by `ρ = ρ_M ⊗ ρ_G`:

* `ρ_M J^a_n = -J^{ā}_n ρ_M` (`matterRho_J`, all modes);
* `ρ_G c^a_{-n} = -(n w_a)⁻¹ b^a_{-n} (-1)^F ρ_G` for `n ≠ 0`, and `ρ_G c^a_0 = c^a_0 (-1)^F ρ_G`
  (`ghostConj_cMode`, `ghostConj_c0`);

so the matter–ghost part of `ρ Q` is the matter part of `E = [Λ, Q]` (the Casimir `K^{ab}` is
`δ_{b,ā}/w_a`), up to a zero-mode term. On relative states the zero-mode term turns into a ghost
term, and what remains is a statement about the three-pair ghost system only:

* `GhostCubicConj` — `ρ_G Q_gh ρ_G y + Σ_a c^a_0 J^{ā}_{gh,0} (-1)^F y = E_gh^{(N)} (-1)^F y` on
  `c₀`-free ghost states of weight `≤ N`, where `E_gh^{(N)} = Σ_{m ≤ N} (1/m) K^{ab}
  (b^a_{-m} J^b_{gh,m} − J^a_{gh,-m} b^b_m)` (proved as `ghostCubicConj_proved` in
  `BRSTConjIdentityProved`; also checked numerically at ghost weights `1, 2, 3`).

* `ghostConjRhoD_of_cubic : GhostCubicConj → GhostConjRhoD` — **proved outright**.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open VOA.SympFerm VOA.Ghost AffineVOA
open scoped TensorProduct

noncomputable section

local notation "adjC" => AffineVOA.HighestModule.adjointColour

/-! ### The matter conjugation of all current modes -/

theorem matterRho_J (a : Fin 3) (n : ℤ) (x : MatterSpace) :
    matterRho bRealStructure (matterJ a n x) =
      -matterJ (adjC a) n (matterRho bRealStructure x) := by
  rw [matterJ_eq, matterJ_eq]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add, neg_add]
  | tmul w z =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w w' hw hw' =>
          rw [TensorProduct.add_tmul, map_add, map_add, hw, hw', map_add, map_add, neg_add]
      | tmul x y =>
          simp only [matterRho, LinearMap.add_apply, LinearMap.rTensor_tmul,
            LinearMap.lTensor_tmul, map_add, TensorProduct.map_tmul, rsLin_apply, aMode_rho,
            uMode_rho, bCompactUnitary.rho_mode, TensorProduct.neg_tmul, TensorProduct.tmul_neg,
            TensorProduct.add_tmul, neg_add]

/-! ### The charge on a pure tensor -/

/-- The cubic ghost charge. -/
abbrev Qgh : Module.End ℂ Sl2GhostSpace := mode (sl2GhostSVA.Y ghostBRSTState) 0

theorem brstQ_tmul (x : MatterSpace) (y : Sl2GhostSpace) :
    brstQ (x ⊗ₜ[ℂ] y) =
      (∑ a : Fin 3, ∑ᶠ n : ℤ, matterJ a n x ⊗ₜ[ℂ] gMode a 1 (-n - 1) y) + x ⊗ₜ[ℂ] Qgh y := by
  have h := semiInfiniteQ_tmul leeYangA x y
  rw [matter_even_invol] at h
  exact h

theorem matterJ_high (a : Fin 3) {h : ℕ} {x : MatterSpace} (hx : x ∈ matterSVA.grading (h : ℂ))
    {n : ℤ} (hn : (h : ℤ) < n) : matterJ a n x = 0 := by
  have hm := matterSVA.grading_mode (leeYangA.current a) (leeYangA.current_weight a) x hx n
  rw [matterNatSupported _ (fun ⟨k, hk⟩ => by
    have : ((k : ℤ) : ℂ) = ((h - n : ℤ) : ℂ) := by push_cast; rw [hk]; ring
    have := Int.cast_injective this
    omega), Submodule.mem_bot] at hm
  exact hm

theorem cMode_low (a : Fin 3) {h : ℕ} {y : Sl2GhostSpace} (hy : y ∈ sl2GhostSVA.grading (h : ℂ))
    {n : ℤ} (hn : n < -(h : ℤ)) : gMode a 1 (-n - 1) y = 0 := by
  have hm := sl2GhostSVA.grading_mode (cGhost a) (cGhost_weight a) y hy (-n - 1)
  rw [natSupported_sl2GhostSVA _ (fun ⟨k, hk⟩ => by
    have : ((k : ℤ) : ℂ) = ((h + n : ℤ) : ℂ) := by rw [Int.cast_natCast, hk]; push_cast; ring
    have := Int.cast_injective this
    omega), Submodule.mem_bot] at hm
  exact hm

theorem finsum_Q_eq (a : Fin 3) {N h1 h2 : ℕ} (hN1 : h1 ≤ N) (hN2 : h2 ≤ N) {x : MatterSpace}
    (hx : x ∈ matterSVA.grading (h1 : ℂ)) {y : Sl2GhostSpace}
    (hy : y ∈ sl2GhostSVA.grading (h2 : ℂ)) :
    (∑ᶠ n : ℤ, matterJ a n x ⊗ₜ[ℂ] gMode a 1 (-n - 1) y) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, matterJ a n x ⊗ₜ[ℂ] gMode a 1 (-n - 1) y := by
  apply finsum_eq_sum_of_support_subset
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn
  simp only [Finset.coe_Icc, Set.mem_Icc]
  constructor
  · by_contra h
    exact hn (by rw [cMode_low a hy (by omega), TensorProduct.tmul_zero])
  · by_contra h
    exact hn (by rw [matterJ_high a hx (by omega), TensorProduct.zero_tmul])

/-! ### The ghost conjugation of the `c` modes -/

theorem ghostConj_cMode (a : Fin 3) {n : ℤ} (hn : n ≠ 0) (y : Sl2GhostSpace) :
    ghostConj (gMode a 1 (-n - 1) y) =
      ((-(1 / ((n : ℝ) * colourW a)) : ℝ) : ℂ) • gMode a 0 (-n) (Ppar (ghostConj y)) := by
  have hw : colourW a ≠ 0 := (colourW_pos a).ne'
  rcases lt_or_gt_of_ne hn with h | h
  · -- an annihilator `c_{|n|}`
    have e1 : gMode a 1 (-n - 1) = An a ((-n - 1).toNat, 0) := by
      simp only [An]; congr 1; omega
    have e2 : An a (swapMode ((-n - 1).toNat, 0)) = gMode a 0 (-n) := by
      rw [show swapMode ((-n - 1).toNat, 0) = ((-n - 1).toNat + 1, 1) by simp [swapMode]]
      simp only [An]; congr 1; push_cast; omega
    rw [e1, ghostConj_An, e2]
    congr 2
    simp only [anCoef, modeCoef, if_true]
    have hk : (((-n - 1).toNat : ℕ) : ℝ) + 1 = -(n : ℝ) := by
      rw [show (((-n - 1).toNat : ℕ) : ℝ) = ((-n - 1 : ℤ) : ℝ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]]
      push_cast; ring
    rw [hk]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  · -- a creator `c_{-n}`
    have e1 : gMode a 1 (-n - 1) = Cr a (n.toNat, 1) := by
      simp only [Cr]; congr 1; omega
    have e2 : Cr a (swapMode (n.toNat, 1)) = gMode a 0 (-n) := by
      rw [show swapMode (n.toNat, 1) = (n.toNat - 1, 0) by
        simp only [swapMode, Fin.isValue, one_ne_zero, if_false]; rw [if_neg (by omega)]]
      simp only [Cr]; congr 1; omega
    rw [e1, ghostConj_Cr, e2]
    congr 2
    simp only [modeCoef, Fin.isValue, one_ne_zero, if_false]
    rw [if_neg (by omega)]
    rw [show (((n.toNat : ℕ)) : ℝ) = (n : ℝ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]]

theorem ghostConj_c0 (a : Fin 3) (y : Sl2GhostSpace) :
    ghostConj (gMode a 1 (-1) y) = gMode a 1 (-1) (Ppar (ghostConj y)) := by
  have h := ghostConj_Cr a (0, 1) y
  rw [show swapMode (0, 1) = (0, 1) by simp [swapMode],
    show modeCoef a (0, 1) = 1 by unfold modeCoef; simp] at h
  simpa using h

/-! ### The conjugated charge on a pure tensor -/

/-- The matter current on the BRST space. -/
abbrev JMr (a : Fin 3) (m : ℤ) : Module.End ℂ BRSTSpace := (matterJ a m).rTensor Sl2GhostSpace

/-- The ghost current on the BRST space. -/
abbrev JGl (a : Fin 3) (m : ℤ) : Module.End ℂ BRSTSpace := (ghostJ a m).lTensor MatterSpace

/-- The matter part of `E`. -/
def Emat (N : ℕ) : Module.End ℂ BRSTSpace :=
  closedE bB JMr (Finset.Icc 1 N) (fun m => 1 / (m : ℂ))

/-- `ρ_G Q_gh ρ_G` as a linear map. -/
def AQ : Module.End ℂ Sl2GhostSpace where
  toFun y := ghostConj (Qgh (ghostConj y))
  map_add' y y' := by simp only [map_add]
  map_smul' c y := by
    simp only [LinearMap.map_smulₛₗ, map_smul, Complex.conj_conj, RingHom.id_apply]

theorem AQ_apply (y : Sl2GhostSpace) : AQ y = ghostConj (Qgh (ghostConj y)) := rfl

/-- The operator whose value on `ρ x` is `ρ (Q x)` (weights `≤ N`). -/
def Rop (N : ℕ) : Module.End ℂ BRSTSpace :=
  Emat N * TB - (∑ a : Fin 3, (gMode a 1 (-1)).lTensor MatterSpace * JMr (adjC a) 0) * TB +
    AQ.lTensor MatterSpace

theorem sum_Icc_symm {E : Type*} [AddCommMonoid E] (N : ℕ) (f : ℤ → E) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N, f n = f 0 + ∑ m ∈ Finset.Icc 1 N, (f m + f (-(m : ℤ))) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have e : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
          insert ((N + 1 : ℕ) : ℤ) (insert (-((N + 1 : ℕ) : ℤ)) (Finset.Icc (-(N : ℤ)) N)) := by
        ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
      rw [e, Finset.sum_insert (by simp; try omega), Finset.sum_insert (by simp; try omega), ih,
        Finset.sum_Icc_succ_top (by omega)]
      push_cast
      try abel

theorem ghConjBRST_tmul (x : MatterSpace) (y : Sl2GhostSpace) :
    ghConjBRST (x ⊗ₜ[ℂ] y) = matterRho bRealStructure x ⊗ₜ[ℂ] ghostConj y := rfl

/-- The per-level matching of the matter–ghost terms with the matter part of `E`. -/
theorem level_match (m : ℕ) (hm : m ≠ 0) (X : MatterSpace) (Y : Sl2GhostSpace) :
    (∑ a : Fin 3, ((((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) •
        (matterJ (adjC a) m X ⊗ₜ[ℂ] gMode a 0 (-(m : ℤ)) Y) -
      (((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) •
        (matterJ (adjC a) (-(m : ℤ)) X ⊗ₜ[ℂ] gMode a 0 (m : ℤ) Y))) =
      (1 / (m : ℂ)) • (casContract (fun a => bB a (-(m : ℤ))) (fun b => JMr b m) -
        casContract (fun a => JMr a (-(m : ℤ))) (fun b => bB b m)) (X ⊗ₜ[ℂ] Y) := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  simp only [casContract, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply, bB, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, Fin.sum_univ_three]
  have c00 : casimir 0 0 = 0 := rfl
  have c01 : casimir 0 1 = 1 := rfl
  have c02 : casimir 0 2 = 0 := rfl
  have c10 : casimir 1 0 = 1 := rfl
  have c11 : casimir 1 1 = 0 := rfl
  have c12 : casimir 1 2 = 0 := rfl
  have c20 : casimir 2 0 = 0 := rfl
  have c21 : casimir 2 1 = 0 := rfl
  have c22 : casimir 2 2 = 1 / 2 := rfl
  have a0 : adjC 0 = 1 := rfl
  have a1 : adjC 1 = 0 := rfl
  have a2 : adjC 2 = 2 := rfl
  have w0 : colourW 0 = 1 := rfl
  have w1 : colourW 1 = 1 := rfl
  have w2 : colourW 2 = 2 := rfl
  simp only [c00, c01, c02, c10, c11, c12, c20, c21, c22, a0, a1, a2, w0, w1, w2, zero_smul,
    one_smul, add_zero, zero_add]
  push_cast
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
    LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, antiMode]
  module

theorem Emat_tmul (N : ℕ) (X : MatterSpace) (Y : Sl2GhostSpace) :
    Emat N (X ⊗ₜ[ℂ] Y) = ∑ m ∈ Finset.Icc 1 N, ∑ a : Fin 3,
        ((((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) •
          (matterJ (adjC a) m X ⊗ₜ[ℂ] gMode a 0 (-(m : ℤ)) Y) -
        (((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) •
          (matterJ (adjC a) (-(m : ℤ)) X ⊗ₜ[ℂ] gMode a 0 (m : ℤ) Y)) := by
  rw [Emat, closedE, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
  rw [LinearMap.smul_apply, level_match m hm0 X Y]

/-- **The conjugated charge on a pure tensor of bounded weights.** -/
theorem rhoQ_tmul {N h1 h2 : ℕ} (hN1 : h1 ≤ N) (hN2 : h2 ≤ N) {x : MatterSpace}
    (hx : x ∈ matterSVA.grading (h1 : ℂ)) {y : Sl2GhostSpace}
    (hy : y ∈ sl2GhostSVA.grading (h2 : ℂ)) :
    ghConjBRST (brstQ (x ⊗ₜ[ℂ] y)) = Rop N (ghConjBRST (x ⊗ₜ[ℂ] y)) := by
  rw [brstQ_tmul]
  simp only [finsum_Q_eq _ hN1 hN2 hx hy, sum_Icc_symm]
  set X := matterRho bRealStructure x
  set Y := ghostConj y
  have hterm : ∀ (a : Fin 3) (n : ℤ), n ≠ 0 →
      ghConjBRST (matterJ a n x ⊗ₜ[ℂ] gMode a 1 (-n - 1) y) =
        (((1 / ((n : ℝ) * colourW a)) : ℝ) : ℂ) •
          (matterJ (adjC a) n X ⊗ₜ[ℂ] gMode a 0 (-n) (Ppar Y)) := by
    intro a n hn
    rw [ghConjBRST_tmul, matterRho_J, ghostConj_cMode a hn, TensorProduct.tmul_smul,
      TensorProduct.neg_tmul, smul_neg, ← neg_smul]
    congr 1
    push_cast; ring
  have hzero : ∀ a : Fin 3, ghConjBRST (matterJ a 0 x ⊗ₜ[ℂ] gMode a 1 (-0 - 1) y) =
      -(matterJ (adjC a) 0 X ⊗ₜ[ℂ] gMode a 1 (-1) (Ppar Y)) := by
    intro a
    rw [ghConjBRST_tmul, matterRho_J, show (-0 - 1 : ℤ) = -1 by ring, ghostConj_c0,
      TensorProduct.neg_tmul]
  have hQ : ghConjBRST (x ⊗ₜ[ℂ] Qgh y) = X ⊗ₜ[ℂ] AQ Y := by
    rw [ghConjBRST_tmul, AQ_apply, ghostConj_sq]
  have hR : Rop N (ghConjBRST (x ⊗ₜ[ℂ] y)) =
      (∑ m ∈ Finset.Icc 1 N, ∑ a : Fin 3,
        ((((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) •
          (matterJ (adjC a) m X ⊗ₜ[ℂ] gMode a 0 (-(m : ℤ)) (Ppar Y)) -
        (((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) •
          (matterJ (adjC a) (-(m : ℤ)) X ⊗ₜ[ℂ] gMode a 0 (m : ℤ) (Ppar Y)))) -
      (∑ a : Fin 3, matterJ (adjC a) 0 X ⊗ₜ[ℂ] gMode a 1 (-1) (Ppar Y)) +
      X ⊗ₜ[ℂ] AQ Y := by
    rw [ghConjBRST_tmul, Rop]
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, LinearMap.sum_apply]
    rw [Emat_tmul]
  rw [hR]
  simp only [map_add, map_sum, hQ, hzero]
  have hpm : ∀ a : Fin 3, ∀ m ∈ Finset.Icc 1 N,
      ghConjBRST (matterJ a (m : ℤ) x ⊗ₜ[ℂ] gMode a 1 (-(m : ℤ) - 1) y) +
        ghConjBRST (matterJ a (-(m : ℤ)) x ⊗ₜ[ℂ] gMode a 1 (-(-(m : ℤ)) - 1) y) =
      (((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) •
          (matterJ (adjC a) m X ⊗ₜ[ℂ] gMode a 0 (-(m : ℤ)) (Ppar Y)) -
        (((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) •
          (matterJ (adjC a) (-(m : ℤ)) X ⊗ₜ[ℂ] gMode a 0 (m : ℤ) (Ppar Y)) := by
    intro a m hm
    have hm0 : (m : ℤ) ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
    have hc : (((1 / (((-(m : ℤ) : ℤ) : ℝ) * colourW a)) : ℝ) : ℂ) =
        -(((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) := by push_cast; ring
    have hc' : (((1 / ((((m : ℤ)) : ℝ) * colourW a)) : ℝ) : ℂ) =
        (((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) := by push_cast; ring
    rw [hterm a _ hm0, hterm a _ (neg_ne_zero.mpr hm0), neg_neg, hc, hc']
    module
  rw [Finset.sum_congr rfl fun a _ => by rw [Finset.sum_congr rfl (hpm a)], Finset.sum_add_distrib,
    Finset.sum_comm]
  simp only [neg_sub_neg, Finset.sum_neg_distrib]
  abel

/-! ### Commutation of the conjugation with `T`, `P0` and the current zero modes -/

theorem ghostConj_pc (a : Fin 3) (y : Sl2GhostSpace) : ghostConj (pc a y) = pc a (ghostConj y) := by
  have hs : swapMode (0, 1) = (0, 1) := by simp [swapMode]
  have hm : modeCoef a (0, 1) = 1 := by unfold modeCoef; simp
  have hb : b0 a = An a (0, 1) := rfl
  have hc : c0 a = Cr a (0, 1) := rfl
  simp only [pc, Module.End.mul_apply]
  rw [hb, hc, ghostConj_An, ghostConj_Cr, hs, hm]
  simp only [anCoef, hm, Complex.ofReal_one, one_smul, Ppar_gMode, Ppar_Ppar, map_neg, smul_neg,
    inv_one]
  push_cast
  simp

theorem ghostConj_P0 (y : Sl2GhostSpace) : ghostConj (P0 y) = P0 (ghostConj y) := by
  simp only [P0_apply, ghostConj_pc]

theorem ghConjBRST_lTensor {f g : Module.End ℂ Sl2GhostSpace}
    (h : ∀ y, ghostConj (f y) = g (ghostConj y)) (u : BRSTSpace) :
    ghConjBRST (f.lTensor MatterSpace u) = g.lTensor MatterSpace (ghConjBRST u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [LinearMap.lTensor_tmul, ghConjBRST_tmul, ghConjBRST_tmul, h,
      LinearMap.lTensor_tmul]
  | add u u' hu hu' => rw [map_add, map_add, hu, hu', map_add, map_add]

theorem ghConjBRST_TB (u : BRSTSpace) : ghConjBRST (TB u) = TB (ghConjBRST u) :=
  ghConjBRST_lTensor ghostConj_Ppar u

theorem ghConjBRST_P0B (u : BRSTSpace) : ghConjBRST (P0B u) = P0B (ghConjBRST u) :=
  ghConjBRST_lTensor ghostConj_P0 u

theorem C0B_ghConj {u : BRSTSpace} (hu : C0B u) : C0B (ghConjBRST u) := by
  unfold C0B at *; rw [← ghConjBRST_P0B, hu]

/-- Compact conjugation of the ghost current zero modes on `c₀`-free states. -/
theorem ghostConj_J0_C0 (a : Fin 3) (x : Sl2GhostSpace) :
    ghostConj (ghostJ a 0 (P0 x)) = -ghostJ (adjC a) 0 (ghostConj (P0 x)) := by
  refine ghost_induction (fun x => JzCompactAt a (P0 x)) ?_ ?_ ?_ ?_ ?_ x
  · simp [JzCompactAt]
  · intro x y hx hy
    unfold JzCompactAt at hx hy ⊢
    rw [map_add, map_add, map_add, hx, hy, map_add, map_add, neg_add]
  · intro c x hx
    rw [map_smul]; exact JzCompactAt_smul a c hx
  · beta_reduce; rw [P0_gvac]; exact JzCompactAt_vacuum a
  · intro c q x hx
    by_cases hq : q = (0, 1)
    · subst hq
      rw [show Cr c (0, 1) x = c0 c x from rfl, P0_c0]
      simp [JzCompactAt]
    · rw [show Cr c q x = gMode c q.2 (-(q.1 : ℤ) - 1) x from rfl,
        ← gMode_comm_P0 c (not_isZeroMode_cr hq)]
      exact JzCompactAt_Cr a c q hq hx

theorem ghConjBRST_JT0 (a : Fin 3) (u : BRSTSpace) :
    ghConjBRST (JT a 0 (P0B u)) = -JT (adjC a) 0 (ghConjBRST (P0B u)) := by
  rw [JT_eq, JT_eq]
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u u' hu hu' =>
      simp only [map_add, LinearMap.add_apply] at hu hu' ⊢
      rw [hu, hu']; abel
  | tmul x y =>
      simp only [P0B_tmul, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        map_add, ghConjBRST_tmul, matterRho_J, ghostConj_J0_C0, TensorProduct.neg_tmul,
        TensorProduct.tmul_neg, neg_add]

/-! ### Weights -/

theorem ghostDegF_isInternal : DirectSum.IsInternal ghostDegF := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top _ ghostDegF_span
  rw [iSupIndep_def]
  intro a
  rw [Submodule.disjoint_def]
  intro x hx hx'
  apply eq_zero_of_sesq_self_eq_zero _ bgPG_pos
  refine sesq_iSup_right' _ (fun b => ⨆ (_ : b ≠ a), ghostDegF b) (fun b y hy => ?_) x hx'
  by_cases hba : b = a
  · subst hba
    simp only [ne_eq, not_true_eq_false, iSup_false, Submodule.mem_bot] at hy
    rw [hy, SesqForm.zero_right]
  · beta_reduce at hy
    rw [iSup_pos (show b ≠ a from hba)] at hy
    exact bgPG_orthF a b (Ne.symm hba) x hx y hy

theorem ghostDegF_le_grading (k : KF) : ghostDegF k ≤ sl2GhostSVA.grading k.1.2 :=
  (ghostDegF_le_ghostDeg k).trans (ghostDeg_le_weight _)

theorem grading_le_gWt (h : ℂ) : sl2GhostSVA.grading h ≤ gWt h := by
  classical
  intro x hx
  unfold gWt
  rw [mem_iSup_pred_iff ghostDegF_isInternal]
  intro k hk
  exact iproj_eq_zero_of_weight ghostDegF_isInternal sl2GhostSVA.isInternal (fun k : KF => k.1.2)
    ghostDegF_le_grading hx hk

theorem gWt_le_grading (h : ℂ) : gWt h ≤ sl2GhostSVA.grading h := by
  unfold gWt
  refine iSup_le fun k => iSup_le fun hk => ?_
  rw [← hk]; exact ghostDegF_le_grading k

/-- The ghost conjugation preserves the conformal weight. -/
theorem ghostConj_grading {h : ℂ} {y : Sl2GhostSpace} (hy : y ∈ sl2GhostSVA.grading h) :
    ghostConj y ∈ sl2GhostSVA.grading h :=
  gWt_le_grading h (ghostConj_gWt' (grading_le_gWt h hy))

theorem gMode_grading_zero (a : Fin 3) (e : Fin 2) (m : ℤ) (hm : IsZeroMode e m) {h : ℂ}
    {y : Sl2GhostSpace} (hy : y ∈ sl2GhostSVA.grading h) : gMode a e m y ∈ sl2GhostSVA.grading h := by
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have := sl2GhostSVA.grading_mode (bGhost a) (bGhost_weight a) y hy 0
    simpa using this
  · have := sl2GhostSVA.grading_mode (cGhost a) (cGhost_weight a) y hy (-1)
    simpa using this

theorem P0_grading {h : ℂ} {y : Sl2GhostSpace} (hy : y ∈ sl2GhostSVA.grading h) :
    P0 y ∈ sl2GhostSVA.grading h := by
  have hpc : ∀ a : Fin 3, ∀ y ∈ sl2GhostSVA.grading h, pc a y ∈ sl2GhostSVA.grading h := by
    intro a y hy
    simp only [pc, Module.End.mul_apply]
    exact gMode_grading_zero a 0 0 (Or.inl ⟨rfl, rfl⟩)
      (gMode_grading_zero a 1 (-1) (Or.inr ⟨rfl, rfl⟩) hy)
  rw [P0_apply]
  exact hpc 0 _ (hpc 1 _ (hpc 2 _ hy))

/-! ### Extension to all states of a given weight -/

theorem natCast_of_grading_matter {h : ℂ} {x : MatterSpace} (hx : x ∈ matterSVA.grading h)
    (hx0 : x ≠ 0) : ∃ k : ℕ, (k : ℂ) = h := by
  by_contra hk
  rw [matterNatSupported h hk, Submodule.mem_bot] at hx
  exact hx0 hx

theorem natCast_of_grading_ghost {h : ℂ} {y : Sl2GhostSpace} (hy : y ∈ sl2GhostSVA.grading h)
    (hy0 : y ≠ 0) : ∃ k : ℕ, (k : ℂ) = h := by
  by_contra hk
  rw [natSupported_sl2GhostSVA h hk, Submodule.mem_bot] at hy
  exact hy0 hy

/-- Pure tensors of total weight `n` have factor weights `≤ n.toNat` (or vanish). -/
theorem tmul_weights {n : ℤ} {h1 : ℂ} {x : MatterSpace} (hx : x ∈ matterSVA.grading h1)
    {y : Sl2GhostSpace} (hy : y ∈ sl2GhostSVA.grading ((n : ℂ) - h1)) :
    x ⊗ₜ[ℂ] y = 0 ∨ ∃ k1 k2 : ℕ, k1 ≤ n.toNat ∧ k2 ≤ n.toNat ∧
      x ∈ matterSVA.grading (k1 : ℂ) ∧ y ∈ sl2GhostSVA.grading (k2 : ℂ) := by
  by_cases hx0 : x = 0
  · left; rw [hx0, TensorProduct.zero_tmul]
  by_cases hy0 : y = 0
  · left; rw [hy0, TensorProduct.tmul_zero]
  right
  obtain ⟨k1, hk1⟩ := natCast_of_grading_matter hx hx0
  obtain ⟨k2, hk2⟩ := natCast_of_grading_ghost hy hy0
  have hsum : ((k1 + k2 : ℕ) : ℂ) = (n : ℂ) := by push_cast; rw [hk1, hk2]; ring
  have hsum' : ((k1 + k2 : ℕ) : ℤ) = n := by exact_mod_cast hsum
  refine ⟨k1, k2, by omega, by omega, by rw [hk1]; exact hx, by rw [hk2]; exact hy⟩

theorem brstSVA_grading_eq (h : ℂ) :
    brstSVA.grading h = TensorVA.tenGrading matterSVA sl2GhostSVA h := rfl

/-- **`ρ Q = R_N ρ` on all states of weight `n`** (`N = n.toNat`). -/
theorem rhoQ_grading (n : ℤ) {x : BRSTSpace} (hx : x ∈ brstSVA.grading (n : ℂ)) :
    ghConjBRST (brstQ x) = Rop n.toNat (ghConjBRST x) := by
  rw [brstSVA_grading_eq] at hx
  refine TensorVA.tenGrading_induction matterSVA sl2GhostSVA
    (motive := fun x => ghConjBRST (brstQ x) = Rop n.toNat (ghConjBRST x)) (by simp)
    (fun x y hx hy => by simp only [map_add] at hx hy ⊢; rw [hx, hy])
    (fun c x hx => by
      simp only at hx ⊢
      rw [map_smul, LinearMap.map_smulₛₗ, hx, LinearMap.map_smulₛₗ, map_smul]) ?_ hx
  intro h1 a ha b hb
  rcases tmul_weights ha hb with h0 | ⟨k1, k2, hk1, hk2, ha', hb'⟩
  · simp only [h0, map_zero]
  · exact rhoQ_tmul hk1 hk2 ha' hb'

/-! ### The ghost-only identity -/

/-- The ghost part of `E`, on the ghost space. -/
def Egh (N : ℕ) : Module.End ℂ Sl2GhostSpace :=
  closedE (fun a m => gMode a 0 m) ghostJ (Finset.Icc 1 N) (fun m => 1 / (m : ℂ))

/-- The conjugated cubic ghost charge on `c₀`-free ghost states of weight `≤ N` (proved as
`ghostCubicConj_proved` in `BRSTConjIdentityProved`),
`ρ_G Q_gh ρ_G y + Σ_a c^a_0 J^{ā}_{gh,0} (-1)^F y = E_gh^{(N)} (-1)^F y`. A statement about the
three-pair ghost system alone (no matter, no `hA`). -/
def GhostCubicConj : Prop :=
  ∀ (N k : ℕ), k ≤ N → ∀ y ∈ sl2GhostSVA.grading (k : ℂ), C0 y →
    AQ y + ∑ a : Fin 3, gMode a 1 (-1) (ghostJ (adjC a) 0 (Ppar y)) = Egh N (Ppar y)

/-- The ghost part of `E` on the BRST space. -/
def EghB (N : ℕ) : Module.End ℂ BRSTSpace :=
  closedE bB JGl (Finset.Icc 1 N) (fun m => 1 / (m : ℂ))

theorem closedE_add_right {K : Type*} [AddCommGroup K] [Module ℂ K]
    (X Y1 Y2 : Fin 3 → ℤ → Module.End ℂ K) (S : Finset ℕ) (c : ℕ → ℂ) :
    closedE X (fun a m => Y1 a m + Y2 a m) S c = closedE X Y1 S c + closedE X Y2 S c := by
  unfold closedE casContract
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [mul_add, add_mul, smul_add, Finset.sum_add_distrib]
  rw [← smul_add]
  congr 1
  abel

theorem brstE_split (n : ℤ) : brstE n = Emat n.toNat + EghB n.toNat := by
  rw [brstE_eq, Emat, EghB, ← closedE_add_right]
  congr 1
  funext a m
  rw [JT_eq]

theorem EghB_tmul (N : ℕ) (x : MatterSpace) (y : Sl2GhostSpace) :
    EghB N (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] Egh N y := by
  simp only [EghB, Egh, closedE, casContract, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.mul_apply, bB, LinearMap.lTensor_tmul, TensorProduct.tmul_sum,
    TensorProduct.tmul_smul, TensorProduct.tmul_sub]

/-- The defect of the ghost-only identity on the BRST space. -/
def cubicDefect (N : ℕ) : Module.End ℂ BRSTSpace :=
  AQ.lTensor MatterSpace +
    (∑ a : Fin 3, (gMode a 1 (-1)).lTensor MatterSpace * JGl (adjC a) 0) * TB - EghB N * TB

theorem cubicDefect_tmul (N : ℕ) (x : MatterSpace) (y : Sl2GhostSpace) :
    cubicDefect N (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] (AQ y +
      ∑ a : Fin 3, gMode a 1 (-1) (ghostJ (adjC a) 0 (Ppar y)) - Egh N (Ppar y)) := by
  simp only [cubicDefect, LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.sum_apply, LinearMap.lTensor_tmul, EghB_tmul, ← TensorProduct.tmul_sum,
    ← TensorProduct.tmul_add, ← TensorProduct.tmul_sub]

/-- The ghost-only identity, lifted to the BRST space on `ρ`-images of states of weight `n`. -/
theorem cubic_lift (hC : GhostCubicConj) (n : ℤ) {x : BRSTSpace}
    (hx : x ∈ brstSVA.grading (n : ℂ)) : cubicDefect n.toNat (P0B (ghConjBRST x)) = 0 := by
  rw [brstSVA_grading_eq] at hx
  refine TensorVA.tenGrading_induction matterSVA sl2GhostSVA
    (motive := fun x => cubicDefect n.toNat (P0B (ghConjBRST x)) = 0) (by simp)
    (fun x y hx hy => by simp only [map_add] at hx hy ⊢; rw [hx, hy, add_zero])
    (fun c x hx => by
      simp only at hx ⊢
      rw [LinearMap.map_smulₛₗ, map_smul, map_smul, hx, smul_zero]) ?_ hx
  intro h1 a ha b hb
  rcases tmul_weights ha hb with h0 | ⟨k1, k2, hk1, hk2, ha', hb'⟩
  · simp only [h0, map_zero]
  · have hy : P0 (ghostConj b) ∈ sl2GhostSVA.grading (k2 : ℂ) :=
      P0_grading (ghostConj_grading hb')
    have h := hC n.toNat k2 hk2 _ hy (C0_P0 _)
    rw [ghConjBRST_tmul, P0B_tmul, cubicDefect_tmul, h, sub_self, TensorProduct.tmul_zero]

/-! ### `GhostConjRhoD` from the ghost-only identity -/

theorem relative_JT0_zero {n : ℤ} {x : BRSTSpace} (hx : x ∈ relativeWeight n) (a : Fin 3) :
    JT a 0 x = 0 := ((mem_relativeCarrier _ x).mp hx.1).1 a

theorem adjC_adjC (a : Fin 3) : adjC (adjC a) = a := by
  fin_cases a <;> rfl

theorem final_alg {V : Type*} [AddCommGroup V] [Module ℂ V] (Em Eg Ebr : V →ₗ[ℂ] V)
    (hE : Ebr = Em + Eg) (z Tz B' C S : V) (s : ℂ) (hT : Tz = s • z) (hB : B' = -S)
    (hC : C = Eg Tz - S) : Em Tz - B' + C = s • Ebr z := by
  subst hT hB hC hE
  rw [LinearMap.add_apply, map_smul, map_smul]
  module

theorem Rop_apply (N : ℕ) (z : BRSTSpace) :
    Rop N z = Emat N (TB z) -
      (∑ a : Fin 3, (gMode a 1 (-1)).lTensor MatterSpace * JMr (adjC a) 0) (TB z) +
      AQ.lTensor MatterSpace z := by
  simp only [Rop, LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply]

/-- **`GhostConjRhoD` from the ghost-only identity `GhostCubicConj`.** -/
theorem ghostConjRhoD_of_cubic (hC : GhostCubicConj) : GhostConjRhoD := by
  intro n j g x hxr hx
  have hC0 : C0B x := relative_C0B hxr
  have hzC : C0B (ghConjBRST x) := C0B_ghConj hC0
  have hJ : ∀ b : Fin 3, JT b 0 (ghConjBRST x) = 0 := by
    intro b
    have h := ghConjBRST_JT0 (adjC b) x
    rw [show P0B x = x from hC0, relative_JT0_zero hxr, map_zero, adjC_adjC] at h
    have := congrArg Neg.neg h
    rw [neg_zero, neg_neg] at this
    exact this.symm
  have hT : TB (ghConjBRST x) = ((-1 : ℂ) ^ g) • ghConjBRST x := by
    rw [← ghConjBRST_TB, TB_brstDeg hx, LinearMap.map_smulₛₗ]
    congr 1
    rw [map_zpow₀, map_neg, map_one]
  have hzero : (∑ a : Fin 3, (gMode a 1 (-1)).lTensor MatterSpace * JMr (adjC a) 0)
        (TB (ghConjBRST x)) =
      -(∑ a : Fin 3, (gMode a 1 (-1)).lTensor MatterSpace * JGl (adjC a) 0)
        (TB (ghConjBRST x)) := by
    simp only [LinearMap.sum_apply, Module.End.mul_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h1 : JMr (adjC a) 0 (TB (ghConjBRST x)) =
        JT (adjC a) 0 (TB (ghConjBRST x)) - JGl (adjC a) 0 (TB (ghConjBRST x)) := by
      rw [JT_eq, LinearMap.add_apply]; abel
    rw [h1, ← TB_JT, hJ, map_zero, zero_sub, map_neg]
  have hcub := cubic_lift hC n hxr.2
  rw [show P0B (ghConjBRST x) = ghConjBRST x from hzC] at hcub
  have hcub' : AQ.lTensor MatterSpace (ghConjBRST x) =
      EghB n.toNat (TB (ghConjBRST x)) -
        (∑ a : Fin 3, (gMode a 1 (-1)).lTensor MatterSpace * JGl (adjC a) 0)
          (TB (ghConjBRST x)) := by
    simp only [cubicDefect, LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply]
      at hcub
    rw [eq_sub_iff_add_eq, ← sub_eq_zero, ← hcub]
  rw [rhoQ_grading n hxr.2, Rop_apply]
  exact final_alg (Emat n.toNat) (EghB n.toNat) (brstE n) (brstE_split n) (ghConjBRST x)
    (TB (ghConjBRST x))
    ((∑ a : Fin 3, (gMode a 1 (-1)).lTensor MatterSpace * JMr (adjC a) 0) (TB (ghConjBRST x)))
    (AQ.lTensor MatterSpace (ghConjBRST x))
    ((∑ a : Fin 3, (gMode a 1 (-1)).lTensor MatterSpace * JGl (adjC a) 0) (TB (ghConjBRST x)))
    ((-1 : ℂ) ^ g) hT hzero hcub'

end

end VOA.ConcreteHodge
