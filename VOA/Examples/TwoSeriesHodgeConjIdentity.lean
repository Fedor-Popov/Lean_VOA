/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesHodgeGhostConj
import VOA.Examples.BRSTConjIdentityProved

/-!
# Level-generic port of the level-specific parts of `BRSTConjIdentity*`

The two BRST conjugation identities `GhostConjBE L` and `GhostConjRhoD L` on the actual
level-`L` complex, proved from the level-independent ghost-side identities
(`BRSTConjIdentityFock`, `…Ghost`, `…Current`, `…Cubic*`), which are reused directly.
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity
open AffineSl2BelowCritical VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer
open VOA.VertexOperatorAlgebra VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang
open VirGradedUnitarity VOA.SympFerm VOA.Ghost AffineVOA
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w

variable (L : CosetLevels)

/-! ## Port of `None` -/


/-! ### Generic algebra -/

/-! ### The BRST-level operators -/

/-- The ghost parity involution on the BRST space. -/
abbrev TB : Module.End ℂ (BRSTSpace L) := Ppar.lTensor (MatterSpace L)

/-- The `c₀`-free projection on the BRST space. -/
abbrev P0B : Module.End ℂ (BRSTSpace L) := P0.lTensor (MatterSpace L)

/-- `c₀`-free BRST states. -/
def C0B (u : (BRSTSpace L)) : Prop := (P0B L) u = u

theorem bB_eq (a : Fin 3) (m : ℤ) : (bB L) a m = (ConcreteHodge.gMode a 0 m).lTensor (MatterSpace
    L) := rfl

/-- **The antighost transposes on the BRST space.** -/
theorem bB_transpose (a : Fin 3) (k : ℤ) (hk : k ≠ 0) (u v : (BRSTSpace L)) :
    (ghBBRST L) ((bB L) a k u) v = Complex.I * (ghBBRST L) ((TB L) u) ((bB L) a (-k) v) := by
  have hz : ¬ IsZeroMode 0 k := by
    unfold IsZeroMode; rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact hk h
    · exact absurd h (by decide)
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u u' hu hu' =>
      simp only [map_add, LinearMap.add_apply, hu, hu', mul_add]
  | tmul x y =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v v' hv hv' => simp only [map_add, hv, hv', mul_add]
      | tmul x' y' =>
          simp only [bB_eq, LinearMap.lTensor_tmul, ghBBRST, bilinTmul_tmul]
          rw [ghostB_gMode a 0 k hz, show trIdx 0 k = -k by simp [trIdx]]
          ring

theorem TB_JT (a : Fin 3) (k : ℤ) (u : (BRSTSpace L)) : (TB L) ((JT L) a k u) = (JT L) a k ((TB L)
    u) := by
  rw [JT_eq]
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u u' hu hu' => simp only [map_add, LinearMap.add_apply] at hu hu' ⊢; rw [hu, hu']
  | tmul x y =>
      simp only [LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, map_add,
        Ppar_ghostJ]

theorem lTensor_comm_apply {f g : Module.End ℂ Sl2GhostSpace} (h : ∀ y, f (g y) = g (f y))
    (u : (BRSTSpace L)) : f.lTensor (MatterSpace L) (g.lTensor (MatterSpace L) u) =
      g.lTensor (MatterSpace L) (f.lTensor (MatterSpace L) u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp only [LinearMap.lTensor_tmul, h]
  | add u u' hu hu' => rw [map_add, map_add, hu, hu', map_add, map_add]

theorem C0B_TB {u : (BRSTSpace L)} (hu : (C0B L) u) : (C0B L) ((TB L) u) := by
  unfold C0B at *
  rw [(lTensor_comm_apply L) (fun y => (Ppar_P0 y).symm), hu]

theorem C0B_bB (a : Fin 3) {k : ℤ} (hk : k ≠ 0) {u : (BRSTSpace L)} (hu : (C0B L) u) :
    (C0B L) ((bB L) a k u) := by
  have hz : ¬ IsZeroMode 0 k := by
    unfold IsZeroMode; rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact hk h
    · exact absurd h (by decide)
  unfold C0B at *
  rw [bB_eq, (lTensor_comm_apply L) (fun y => (gMode_comm_P0 a hz y).symm), hu]

theorem P0B_tmul (x : (MatterSpace L)) (y : Sl2GhostSpace) : (P0B L) (x ⊗ₜ y) = x ⊗ₜ P0 y := rfl

/-- **The total current is skew on `c₀`-free BRST states.** -/
theorem JT_skew (a : Fin 3) (k : ℤ) (u v : (BRSTSpace L)) (hu : (C0B L) u) (hv : (C0B L) v) :
    (ghBBRST L) ((JT L) a k u) v = -(ghBBRST L) u ((JT L) a (-k) v) := by
  have key : ∀ u v : (BRSTSpace L),
      (ghBBRST L) ((JT L) a k ((P0B L) u)) ((P0B L) v) = -(ghBBRST L) ((P0B L) u) ((JT L) a (-k)
          ((P0B L) v)) := by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u u' hu hu' =>
        simp only [map_add, LinearMap.add_apply] at hu hu' ⊢
        rw [hu, hu']; ring
    | tmul x y =>
        induction v using TensorProduct.induction_on with
        | zero => simp
        | add v v' hv hv' =>
            simp only [map_add] at hv hv' ⊢
            rw [hv, hv']; ring
        | tmul x' y' =>
            rw [P0B_tmul, P0B_tmul, JT_eq, JT_eq]
            simp only [LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
              map_add, LinearMap.add_apply, ghBBRST, bilinTmul_tmul]
            rw [(matterB_current_skew L) bCompactUnitary,
              ghostB_ghostJ_skew a k (C0_P0 y) (C0_P0 y')]
            ring
  have h := key u v
  rwa [show (P0B L) u = u from hu, show (P0B L) v = v from hv] at h

/-! ### Relative states -/

theorem lTensor_pc_eq (a : Fin 3) (u : (BRSTSpace L)) :
    (pc a).lTensor (MatterSpace L) u =
      u - (c0 a).lTensor (MatterSpace L) ((b0 a).lTensor (MatterSpace L) u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp only [LinearMap.lTensor_tmul, pc_eq_sub, TensorProduct.tmul_sub]
  | add u u' hu hu' => rw [map_add, hu, hu', map_add, map_add]; abel

theorem lTensor_pc_of (a : Fin 3) {u : (BRSTSpace L)} (hu : (b0 a).lTensor (MatterSpace L) u = 0) :
    (pc a).lTensor (MatterSpace L) u = u := by
  rw [lTensor_pc_eq, hu, map_zero, sub_zero]

/-- Relative states are `c₀`-free. -/
theorem C0B_of_b0 {u : (BRSTSpace L)} (hu : ∀ a, (b0 a).lTensor (MatterSpace L) u = 0) : (C0B L)
    u := by
  have h2 := (lTensor_pc_of L) 2 (hu 2)
  have h1 := (lTensor_pc_of L) 1 (hu 1)
  have h0 := (lTensor_pc_of L) 0 (hu 0)
  unfold C0B
  show P0.lTensor (MatterSpace L) u = u
  rw [show P0 = pc 0 * pc 1 * pc 2 from rfl, LinearMap.lTensor_mul, LinearMap.lTensor_mul,
    Module.End.mul_apply, Module.End.mul_apply, h2, h1, h0]

theorem relative_C0B {n : ℤ} {u : (BRSTSpace L)} (hu : u ∈ (relativeWeight L) n) : (C0B L) u := by
  refine (C0B_of_b0 L) fun a => ?_
  have h := ((mem_relativeCarrier _ u).mp hu.1).2 a
  rw [antighostZero_eq] at h
  exact h

/-- `T = (-1)^g` on BRST ghost number `g`. -/
theorem TB_brstDeg {j g : ℤ} {w : ℂ} {u : (BRSTSpace L)} (hu : u ∈ (brstDeg L) bgGh ((j, g), w)) :
    (TB L) u = ((-1 : ℂ) ^ g) • u := by
  refine tensorDeg_induction (matterDeg L) ghostDeg ((j, g), w) (fun u => (TB L) u = ((-1 : ℂ) ^ g)
      • u)
    (by simp) (fun x y hx hy => by simp only at hx hy ⊢; rw [map_add, hx, hy, smul_add])
    (fun c x hx => by simp only at hx ⊢; rw [map_smul, hx, smul_comm]) ?_ u hu
  intro b x hx y hy
  by_cases hb : ghIndex b = 0
  · have hyg := ghostDeg_le_ghost _ hy
    have hgi : ghIndex (((j, g), w) - b) = g := by
      show (((j, g), w) - b).1.2 = g
      simp only [Prod.fst_sub, Prod.snd_sub]
      rw [show b.1.2 = 0 from hb, sub_zero]
    rw [hgi] at hyg
    have hpar := sl2GhostGrading_le_parity g hyg
    rw [LinearMap.lTensor_tmul, ParityGrading.koszulOp_homog _ 1 hpar, koszul_one_intCast,
      TensorProduct.tmul_smul]
  · rw [eq_zero_of_mem_zeroGhost hb ((matterDeg_le_zeroGhost L) b hx)]
    simp

/-! ### `GhostConjBE L` -/

/-- **`GhostConjBE L` is proved outright** (no hypothesis; in particular no `hA`). -/
theorem ghostConjBE_proved : (GhostConjBE L) := by
  intro n j g u hur hu v hvr
  have hC := (relative_C0B L) hur
  have hCv := (relative_C0B L) hvr
  rw [brstE_eq]
  rw [B_E_of_transposeT (ghBBRST L) (C0B L) (TB L) (bB L) (JT L) Complex.I
      (fun a k hk u hu => (C0B_bB L) a hk hu) (fun u hu => (C0B_TB L) hu) (TB_JT L)
      (bB_transpose L) (fun a k u v hu hv => (JT_skew L) a k u v hu hv)
      (Finset.Icc 1 n.toNat) (fun m hm => by
        have := (Finset.mem_Icc.mp hm).1; omega) _ u hC v hCv,
    (TB_brstDeg L) hu, LinearMap.map_smul₂, smul_eq_mul]
  ring


/-! ## Port of `None` -/


local notation "adjC" => AffineVOA.HighestModule.adjointColour

/-! ### The matter conjugation of all current modes -/

theorem matterRho_J (a : Fin 3) (n : ℤ) (x : (MatterSpace L)) :
    (matterRho L) bRealStructure ((matterJ L) a n x) =
      -(matterJ L) (adjC a) n ((matterRho L) bRealStructure x) := by
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

theorem brstQ_tmul (x : (MatterSpace L)) (y : Sl2GhostSpace) :
    (brstQ L) (x ⊗ₜ[ℂ] y) =
      (∑ a : Fin 3, ∑ᶠ n : ℤ, (matterJ L) a n x ⊗ₜ[ℂ] ConcreteHodge.gMode a 1 (-n - 1) y) + x ⊗ₜ[ℂ]
          Qgh y := by
  have h := semiInfiniteQ_tmul (matterAffineAction L) x y
  rw [matter_even_invol] at h
  exact h

theorem matterJ_high (a : Fin 3) {h : ℕ} {x : (MatterSpace L)} (hx : x ∈ (matterSVA L).grading (h :
    ℂ))
    {n : ℤ} (hn : (h : ℤ) < n) : (matterJ L) a n x = 0 := by
  have hm := (matterSVA L).grading_mode ((matterAffineAction L).current a)
      ((matterAffineAction L).current_weight a) x
      hx n
  rw [(matterNatSupported L) _ (fun ⟨k, hk⟩ => by
    have : ((k : ℤ) : ℂ) = ((h - n : ℤ) : ℂ) := by push_cast; rw [hk]; ring
    have := Int.cast_injective this
    omega), Submodule.mem_bot] at hm
  exact hm

theorem finsum_Q_eq (a : Fin 3) {N h1 h2 : ℕ} (hN1 : h1 ≤ N) (hN2 : h2 ≤ N) {x : (MatterSpace L)}
    (hx : x ∈ (matterSVA L).grading (h1 : ℂ)) {y : Sl2GhostSpace}
    (hy : y ∈ sl2GhostSVA.grading (h2 : ℂ)) :
    (∑ᶠ n : ℤ, (matterJ L) a n x ⊗ₜ[ℂ] ConcreteHodge.gMode a 1 (-n - 1) y) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (matterJ L) a n x ⊗ₜ[ℂ] ConcreteHodge.gMode a 1 (-n - 1) y :=
          by
  apply finsum_eq_sum_of_support_subset
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn
  simp only [Finset.coe_Icc, Set.mem_Icc]
  constructor
  · by_contra h
    exact hn (by rw [cMode_low a hy (by omega), TensorProduct.tmul_zero])
  · by_contra h
    exact hn (by rw [(matterJ_high L) a hx (by omega), TensorProduct.zero_tmul])

/-! ### The ghost conjugation of the `c` modes -/

/-! ### The conjugated charge on a pure tensor -/

/-- The matter current on the BRST space. -/
abbrev JMr (a : Fin 3) (m : ℤ) : Module.End ℂ (BRSTSpace L) := ((matterJ L) a m).rTensor
    Sl2GhostSpace

/-- The ghost current on the BRST space. -/
abbrev JGl (a : Fin 3) (m : ℤ) : Module.End ℂ (BRSTSpace L) := (ghostJ a m).lTensor (MatterSpace L)

/-- The matter part of `E`. -/
def Emat (N : ℕ) : Module.End ℂ (BRSTSpace L) :=
  closedE (bB L) (JMr L) (Finset.Icc 1 N) (fun m => 1 / (m : ℂ))

/-- The operator whose value on `ρ x` is `ρ (Q x)` (weights `≤ N`). -/
def Rop (N : ℕ) : Module.End ℂ (BRSTSpace L) :=
  (Emat L) N * (TB L) - (∑ a : Fin 3, (ConcreteHodge.gMode a 1 (-1)).lTensor (MatterSpace L) * (JMr
      L) (adjC a) 0) * (TB L) +
    AQ.lTensor (MatterSpace L)

theorem ghConjBRST_tmul (x : (MatterSpace L)) (y : Sl2GhostSpace) :
    (ghConjBRST L) (x ⊗ₜ[ℂ] y) = (matterRho L) bRealStructure x ⊗ₜ[ℂ] ghostConj y := rfl

/-- The per-level matching of the matter–ghost terms with the matter part of `E`. -/
theorem level_match (m : ℕ) (hm : m ≠ 0) (X : (MatterSpace L)) (Y : Sl2GhostSpace) :
    (∑ a : Fin 3, ((((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) •
        ((matterJ L) (adjC a) m X ⊗ₜ[ℂ] ConcreteHodge.gMode a 0 (-(m : ℤ)) Y) -
      (((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) •
        ((matterJ L) (adjC a) (-(m : ℤ)) X ⊗ₜ[ℂ] ConcreteHodge.gMode a 0 (m : ℤ) Y))) =
      (1 / (m : ℂ)) • (casContract (fun a => (bB L) a (-(m : ℤ))) (fun b => (JMr L) b m) -
        casContract (fun a => (JMr L) a (-(m : ℤ))) (fun b => (bB L) b m)) (X ⊗ₜ[ℂ] Y) := by
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

theorem Emat_tmul (N : ℕ) (X : (MatterSpace L)) (Y : Sl2GhostSpace) :
    (Emat L) N (X ⊗ₜ[ℂ] Y) = ∑ m ∈ Finset.Icc 1 N, ∑ a : Fin 3,
        ((((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) •
          ((matterJ L) (adjC a) m X ⊗ₜ[ℂ] ConcreteHodge.gMode a 0 (-(m : ℤ)) Y) -
        (((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) •
          ((matterJ L) (adjC a) (-(m : ℤ)) X ⊗ₜ[ℂ] ConcreteHodge.gMode a 0 (m : ℤ) Y)) := by
  rw [Emat, closedE, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
  rw [LinearMap.smul_apply, (level_match L) m hm0 X Y]

/-- **The conjugated charge on a pure tensor of bounded weights.** -/
theorem rhoQ_tmul {N h1 h2 : ℕ} (hN1 : h1 ≤ N) (hN2 : h2 ≤ N) {x : (MatterSpace L)}
    (hx : x ∈ (matterSVA L).grading (h1 : ℂ)) {y : Sl2GhostSpace}
    (hy : y ∈ sl2GhostSVA.grading (h2 : ℂ)) :
    (ghConjBRST L) ((brstQ L) (x ⊗ₜ[ℂ] y)) = (Rop L) N ((ghConjBRST L) (x ⊗ₜ[ℂ] y)) := by
  rw [brstQ_tmul]
  simp only [(finsum_Q_eq L) _ hN1 hN2 hx hy, sum_Icc_symm]
  set X := (matterRho L) bRealStructure x
  set Y := ghostConj y
  have hterm : ∀ (a : Fin 3) (n : ℤ), n ≠ 0 →
      (ghConjBRST L) ((matterJ L) a n x ⊗ₜ[ℂ] ConcreteHodge.gMode a 1 (-n - 1) y) =
        (((1 / ((n : ℝ) * colourW a)) : ℝ) : ℂ) •
          ((matterJ L) (adjC a) n X ⊗ₜ[ℂ] ConcreteHodge.gMode a 0 (-n) (Ppar Y)) := by
    intro a n hn
    rw [ghConjBRST_tmul, matterRho_J, ghostConj_cMode a hn, TensorProduct.tmul_smul,
      TensorProduct.neg_tmul, smul_neg, ← neg_smul]
    congr 1
    push_cast; ring
  have hzero : ∀ a : Fin 3, (ghConjBRST L) ((matterJ L) a 0 x ⊗ₜ[ℂ] ConcreteHodge.gMode a 1 (-0 -
      1) y) =
      -((matterJ L) (adjC a) 0 X ⊗ₜ[ℂ] ConcreteHodge.gMode a 1 (-1) (Ppar Y)) := by
    intro a
    rw [ghConjBRST_tmul, matterRho_J, show (-0 - 1 : ℤ) = -1 by ring, ghostConj_c0,
      TensorProduct.neg_tmul]
  have hQ : (ghConjBRST L) (x ⊗ₜ[ℂ] Qgh y) = X ⊗ₜ[ℂ] AQ Y := by
    rw [ghConjBRST_tmul, AQ_apply, ghostConj_sq]
  have hR : (Rop L) N ((ghConjBRST L) (x ⊗ₜ[ℂ] y)) =
      (∑ m ∈ Finset.Icc 1 N, ∑ a : Fin 3,
        ((((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) •
          ((matterJ L) (adjC a) m X ⊗ₜ[ℂ] ConcreteHodge.gMode a 0 (-(m : ℤ)) (Ppar Y)) -
        (((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) •
          ((matterJ L) (adjC a) (-(m : ℤ)) X ⊗ₜ[ℂ] ConcreteHodge.gMode a 0 (m : ℤ) (Ppar Y)))) -
      (∑ a : Fin 3, (matterJ L) (adjC a) 0 X ⊗ₜ[ℂ] ConcreteHodge.gMode a 1 (-1) (Ppar Y)) +
      X ⊗ₜ[ℂ] AQ Y := by
    rw [ghConjBRST_tmul, Rop]
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, LinearMap.sum_apply]
    rw [Emat_tmul]
  rw [hR]
  simp only [map_add, map_sum, hQ, hzero]
  have hpm : ∀ a : Fin 3, ∀ m ∈ Finset.Icc 1 N,
      (ghConjBRST L) ((matterJ L) a (m : ℤ) x ⊗ₜ[ℂ] ConcreteHodge.gMode a 1 (-(m : ℤ) - 1) y) +
        (ghConjBRST L) ((matterJ L) a (-(m : ℤ)) x ⊗ₜ[ℂ] ConcreteHodge.gMode a 1 (-(-(m : ℤ)) - 1)
            y) =
      (((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) •
          ((matterJ L) (adjC a) m X ⊗ₜ[ℂ] ConcreteHodge.gMode a 0 (-(m : ℤ)) (Ppar Y)) -
        (((1 / ((m : ℝ) * colourW a)) : ℝ) : ℂ) •
          ((matterJ L) (adjC a) (-(m : ℤ)) X ⊗ₜ[ℂ] ConcreteHodge.gMode a 0 (m : ℤ) (Ppar Y)) := by
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

theorem ghConjBRST_lTensor {f g : Module.End ℂ Sl2GhostSpace}
    (h : ∀ y, ghostConj (f y) = g (ghostConj y)) (u : (BRSTSpace L)) :
    (ghConjBRST L) (f.lTensor (MatterSpace L) u) = g.lTensor (MatterSpace L) ((ghConjBRST L) u) :=
        by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [LinearMap.lTensor_tmul, ghConjBRST_tmul, ghConjBRST_tmul, h,
      LinearMap.lTensor_tmul]
  | add u u' hu hu' => rw [map_add, map_add, hu, hu', map_add, map_add]

theorem ghConjBRST_TB (u : (BRSTSpace L)) : (ghConjBRST L) ((TB L) u) = (TB L) ((ghConjBRST L) u) :=
  (ghConjBRST_lTensor L) ghostConj_Ppar u

theorem ghConjBRST_P0B (u : (BRSTSpace L)) : (ghConjBRST L) ((P0B L) u) = (P0B L) ((ghConjBRST L)
    u) :=
  (ghConjBRST_lTensor L) ghostConj_P0 u

theorem C0B_ghConj {u : (BRSTSpace L)} (hu : (C0B L) u) : (C0B L) ((ghConjBRST L) u) := by
  unfold C0B at *; rw [← ghConjBRST_P0B, hu]

theorem ghConjBRST_JT0 (a : Fin 3) (u : (BRSTSpace L)) :
    (ghConjBRST L) ((JT L) a 0 ((P0B L) u)) = -(JT L) (adjC a) 0 ((ghConjBRST L) ((P0B L) u)) := by
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

/-! ### Extension to all states of a given weight -/

theorem natCast_of_grading_matter {h : ℂ} {x : (MatterSpace L)} (hx : x ∈ (matterSVA L).grading h)
    (hx0 : x ≠ 0) : ∃ k : ℕ, (k : ℂ) = h := by
  by_contra hk
  rw [(matterNatSupported L) h hk, Submodule.mem_bot] at hx
  exact hx0 hx

/-- Pure tensors of total weight `n` have factor weights `≤ n.toNat` (or vanish). -/
theorem tmul_weights {n : ℤ} {h1 : ℂ} {x : (MatterSpace L)} (hx : x ∈ (matterSVA L).grading h1)
    {y : Sl2GhostSpace} (hy : y ∈ sl2GhostSVA.grading ((n : ℂ) - h1)) :
    x ⊗ₜ[ℂ] y = 0 ∨ ∃ k1 k2 : ℕ, k1 ≤ n.toNat ∧ k2 ≤ n.toNat ∧
      x ∈ (matterSVA L).grading (k1 : ℂ) ∧ y ∈ sl2GhostSVA.grading (k2 : ℂ) := by
  by_cases hx0 : x = 0
  · left; rw [hx0, TensorProduct.zero_tmul]
  by_cases hy0 : y = 0
  · left; rw [hy0, TensorProduct.tmul_zero]
  right
  obtain ⟨k1, hk1⟩ := (natCast_of_grading_matter L) hx hx0
  obtain ⟨k2, hk2⟩ := natCast_of_grading_ghost hy hy0
  have hsum : ((k1 + k2 : ℕ) : ℂ) = (n : ℂ) := by push_cast; rw [hk1, hk2]; ring
  have hsum' : ((k1 + k2 : ℕ) : ℤ) = n := by exact_mod_cast hsum
  refine ⟨k1, k2, by omega, by omega, by rw [hk1]; exact hx, by rw [hk2]; exact hy⟩

theorem brstSVA_grading_eq (h : ℂ) :
    (brstSVA L).grading h = TensorVA.tenGrading (matterSVA L) sl2GhostSVA h := rfl

/-- **`ρ Q = R_N ρ` on all states of weight `n`** (`N = n.toNat`). -/
theorem rhoQ_grading (n : ℤ) {x : (BRSTSpace L)} (hx : x ∈ (brstSVA L).grading (n : ℂ)) :
    (ghConjBRST L) ((brstQ L) x) = (Rop L) n.toNat ((ghConjBRST L) x) := by
  rw [brstSVA_grading_eq] at hx
  refine TensorVA.tenGrading_induction (matterSVA L) sl2GhostSVA
    (motive := fun x => (ghConjBRST L) ((brstQ L) x) = (Rop L) n.toNat ((ghConjBRST L) x)) (by simp)
    (fun x y hx hy => by simp only [map_add] at hx hy ⊢; rw [hx, hy])
    (fun c x hx => by
      simp only at hx ⊢
      rw [map_smul, LinearMap.map_smulₛₗ, hx, LinearMap.map_smulₛₗ, map_smul]) ?_ hx
  intro h1 a ha b hb
  rcases (tmul_weights L) ha hb with h0 | ⟨k1, k2, hk1, hk2, ha', hb'⟩
  · simp only [h0, map_zero]
  · exact (rhoQ_tmul L) hk1 hk2 ha' hb'

/-! ### The ghost-only identity -/

/-- The ghost part of `E` on the BRST space. -/
def EghB (N : ℕ) : Module.End ℂ (BRSTSpace L) :=
  closedE (bB L) (JGl L) (Finset.Icc 1 N) (fun m => 1 / (m : ℂ))

theorem brstE_split (n : ℤ) : (brstE L) n = (Emat L) n.toNat + (EghB L) n.toNat := by
  rw [brstE_eq, Emat, EghB, ← closedE_add_right]
  congr 1
  funext a m
  rw [JT_eq]

theorem EghB_tmul (N : ℕ) (x : (MatterSpace L)) (y : Sl2GhostSpace) :
    (EghB L) N (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] Egh N y := by
  simp only [EghB, Egh, closedE, casContract, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.mul_apply, bB, LinearMap.lTensor_tmul, TensorProduct.tmul_sum,
    TensorProduct.tmul_smul, TensorProduct.tmul_sub]

/-- The defect of the ghost-only identity on the BRST space. -/
def cubicDefect (N : ℕ) : Module.End ℂ (BRSTSpace L) :=
  AQ.lTensor (MatterSpace L) +
    (∑ a : Fin 3, (ConcreteHodge.gMode a 1 (-1)).lTensor (MatterSpace L) * (JGl L) (adjC a) 0) *
        (TB L) - (EghB L) N * (TB L)

theorem cubicDefect_tmul (N : ℕ) (x : (MatterSpace L)) (y : Sl2GhostSpace) :
    (cubicDefect L) N (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] (AQ y +
      ∑ a : Fin 3, ConcreteHodge.gMode a 1 (-1) (ghostJ (adjC a) 0 (Ppar y)) - Egh N (Ppar y)) := by
  simp only [cubicDefect, LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.sum_apply, LinearMap.lTensor_tmul, EghB_tmul, ← TensorProduct.tmul_sum,
    ← TensorProduct.tmul_add, ← TensorProduct.tmul_sub]

/-- The ghost-only identity, lifted to the BRST space on `ρ`-images of states of weight `n`. -/
theorem cubic_lift (hC : GhostCubicConj) (n : ℤ) {x : (BRSTSpace L)}
    (hx : x ∈ (brstSVA L).grading (n : ℂ)) : (cubicDefect L) n.toNat ((P0B L) ((ghConjBRST L) x)) =
        0 := by
  rw [brstSVA_grading_eq] at hx
  refine TensorVA.tenGrading_induction (matterSVA L) sl2GhostSVA
    (motive := fun x => (cubicDefect L) n.toNat ((P0B L) ((ghConjBRST L) x)) = 0) (by simp)
    (fun x y hx hy => by simp only [map_add] at hx hy ⊢; rw [hx, hy, add_zero])
    (fun c x hx => by
      simp only at hx ⊢
      rw [LinearMap.map_smulₛₗ, map_smul, map_smul, hx, smul_zero]) ?_ hx
  intro h1 a ha b hb
  rcases (tmul_weights L) ha hb with h0 | ⟨k1, k2, hk1, hk2, ha', hb'⟩
  · simp only [h0, map_zero]
  · have hy : P0 (ghostConj b) ∈ sl2GhostSVA.grading (k2 : ℂ) :=
      P0_grading (ghostConj_grading hb')
    have h := hC n.toNat k2 hk2 _ hy (C0_P0 _)
    rw [ghConjBRST_tmul, P0B_tmul, cubicDefect_tmul, h, sub_self, TensorProduct.tmul_zero]

/-! ### `GhostConjRhoD L` from the ghost-only identity -/

theorem relative_JT0_zero {n : ℤ} {x : (BRSTSpace L)} (hx : x ∈ (relativeWeight L) n) (a : Fin 3) :
    (JT L) a 0 x = 0 := ((mem_relativeCarrier _ x).mp hx.1).1 a

theorem Rop_apply (N : ℕ) (z : (BRSTSpace L)) :
    (Rop L) N z = (Emat L) N ((TB L) z) -
      (∑ a : Fin 3, (ConcreteHodge.gMode a 1 (-1)).lTensor (MatterSpace L) * (JMr L) (adjC a) 0)
          ((TB L) z) +
      AQ.lTensor (MatterSpace L) z := by
  simp only [Rop, LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply]

/-- **`GhostConjRhoD L` from the ghost-only identity `GhostCubicConj`.** -/
theorem ghostConjRhoD_of_cubic (hC : GhostCubicConj) : (GhostConjRhoD L) := by
  intro n j g x hxr hx
  have hC0 : (C0B L) x := (relative_C0B L) hxr
  have hzC : (C0B L) ((ghConjBRST L) x) := (C0B_ghConj L) hC0
  have hJ : ∀ b : Fin 3, (JT L) b 0 ((ghConjBRST L) x) = 0 := by
    intro b
    have h := (ghConjBRST_JT0 L) (adjC b) x
    rw [show (P0B L) x = x from hC0, (relative_JT0_zero L) hxr, map_zero, adjC_adjC] at h
    have := congrArg Neg.neg h
    rw [neg_zero, neg_neg] at this
    exact this.symm
  have hT : (TB L) ((ghConjBRST L) x) = ((-1 : ℂ) ^ g) • (ghConjBRST L) x := by
    rw [← ghConjBRST_TB, (TB_brstDeg L) hx, LinearMap.map_smulₛₗ]
    congr 1
    rw [map_zpow₀, map_neg, map_one]
  have hzero : (∑ a : Fin 3, (ConcreteHodge.gMode a 1 (-1)).lTensor (MatterSpace L) * (JMr L) (adjC
      a) 0)
        ((TB L) ((ghConjBRST L) x)) =
      -(∑ a : Fin 3, (ConcreteHodge.gMode a 1 (-1)).lTensor (MatterSpace L) * (JGl L) (adjC a) 0)
        ((TB L) ((ghConjBRST L) x)) := by
    simp only [LinearMap.sum_apply, Module.End.mul_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h1 : (JMr L) (adjC a) 0 ((TB L) ((ghConjBRST L) x)) =
        (JT L) (adjC a) 0 ((TB L) ((ghConjBRST L) x)) - (JGl L) (adjC a) 0 ((TB L) ((ghConjBRST L)
            x)) := by
      rw [JT_eq, LinearMap.add_apply]; abel
    rw [h1, ← TB_JT, hJ, map_zero, zero_sub, map_neg]
  have hcub := (cubic_lift L) hC n hxr.2
  rw [show (P0B L) ((ghConjBRST L) x) = (ghConjBRST L) x from hzC] at hcub
  have hcub' : AQ.lTensor (MatterSpace L) ((ghConjBRST L) x) =
      (EghB L) n.toNat ((TB L) ((ghConjBRST L) x)) -
        (∑ a : Fin 3, (ConcreteHodge.gMode a 1 (-1)).lTensor (MatterSpace L) * (JGl L) (adjC a) 0)
          ((TB L) ((ghConjBRST L) x)) := by
    simp only [cubicDefect, LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply]
      at hcub
    rw [eq_sub_iff_add_eq, ← sub_eq_zero, ← hcub]
  rw [(rhoQ_grading L) n hxr.2, Rop_apply]
  exact final_alg ((Emat L) n.toNat) ((EghB L) n.toNat) ((brstE L) n) ((brstE_split L) n)
      ((ghConjBRST L) x)
    ((TB L) ((ghConjBRST L) x))
    ((∑ a : Fin 3, (ConcreteHodge.gMode a 1 (-1)).lTensor (MatterSpace L) * (JMr L) (adjC a) 0)
        ((TB L) ((ghConjBRST L) x)))
    (AQ.lTensor (MatterSpace L) ((ghConjBRST L) x))
    ((∑ a : Fin 3, (ConcreteHodge.gMode a 1 (-1)).lTensor (MatterSpace L) * (JGl L) (adjC a) 0)
        ((TB L) ((ghConjBRST L) x)))
    ((-1 : ℂ) ^ g) hT hzero hcub'


/-! ## Port of `None` -/


/-- **`GhostConjRhoD L` is proved outright** (no hypothesis; in particular no `hA`). -/
theorem ghostConjRhoD_proved : (GhostConjRhoD L) := (ghostConjRhoD_of_cubic L) ghostCubicConj_proved


end

end VOA.TwoSeries
