/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTConjIdentityCurrent

/-!
# `GhostConjBE` proved: super-skewness of `E = [Λ, Q]` on relative states

With `E = Σ (1/m) K^{ab} (b^a_{-m} J^b_m − J^a_{-m} b^b_m)` (`brstE_eq`), the identity
`B(E u, v) = i (-1)^{gh u} B(u, E v)` on relative states follows from:

* the antighost transposes on the BRST space,
  `B(b^a_k u, v) = i B(T u, b^a_{-k} v)` for `k ≠ 0`, with `T = 1 ⊗ (-1)^F` (`bB_transpose`,
  from the ghost-level `ghostB_gMode`);
* skewness of the total current `J = J_M ⊗ 1 + 1 ⊗ J_gh` on `c₀`-free states (`JT_skew`, from the
  proved matter skewness `matterB_current_skew` and the ghost-level `ghostB_ghostJ_skew`);
* the generic algebra `B_E_of_transposeT` (a variant of `B_E_of_transpose` with the parity twist
  and a subspace on which the current is skew);
* relative states are `c₀`-free (`relative_C0B`) and `T = (-1)^g` on ghost number `g`
  (`TB_brstDeg`).

* `ghostConjBE_proved : GhostConjBE` — **proved outright, with no hypothesis** (in particular
  without `hA`).
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open VOA.SympFerm VOA.Ghost AffineVOA
open scoped TensorProduct

noncomputable section

/-! ### Generic algebra -/

section GenericForm

variable {K : Type*} [AddCommGroup K] [Module ℂ K]

/-- **Super-skewness of `E` from parity-twisted mode transposes** (generic): if the `X` modes
satisfy `B(X_k u, v) = c B(T u, X_{-k} v)` (`k ≠ 0`) and the `Y` modes are skew on a subspace `C`
preserved by `T` and the nonzero `X` modes, with `T` commuting with `Y`, then
`B(E u, v) = c B(T u, E v)` on `C`. -/
theorem B_E_of_transposeT (B : LinearMap.BilinForm ℂ K) (Cs : K → Prop) (T : Module.End ℂ K)
    (X Y : Fin 3 → ℤ → Module.End ℂ K) (c : ℂ)
    (hXC : ∀ a k, k ≠ 0 → ∀ u, Cs u → Cs (X a k u))
    (hTC : ∀ u, Cs u → Cs (T u))
    (hTY : ∀ a k u, T (Y a k u) = Y a k (T u))
    (hX : ∀ a k, k ≠ 0 → ∀ u v, B (X a k u) v = c * B (T u) (X a (-k) v))
    (hY : ∀ a k u v, Cs u → Cs v → B (Y a k u) v = -B u (Y a (-k) v))
    (S : Finset ℕ) (hS : ∀ m ∈ S, m ≠ 0) (coef : ℕ → ℂ) (u : K) (hu : Cs u) (v : K)
    (hv : Cs v) :
    B (closedE X Y S coef u) v = c * B (T u) (closedE X Y S coef v) := by
  have t1 : ∀ p q (m : ℤ), m ≠ 0 →
      B (X p (-m) (Y q m u)) v = -c * B (T u) (Y q (-m) (X p m v)) := by
    intro p q m hm
    rw [hX p (-m) (neg_ne_zero.mpr hm), neg_neg, hTY,
      hY q m _ _ (hTC u hu) (hXC p m hm v hv)]
    ring
  have t2 : ∀ p q (m : ℤ), m ≠ 0 →
      B (Y p (-m) (X q m u)) v = -c * B (T u) (X q (-m) (Y p m v)) := by
    intro p q m hm
    rw [hY p (-m) _ _ (hXC q m hm u hu) hv, neg_neg, hX q m hm]
    ring
  unfold closedE casContract
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, map_sum, map_smul, map_sub, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hS m hm
  simp only [t1 _ _ _ hm0, t2 _ _ _ hm0]
  have c00 : casimir 0 0 = 0 := rfl
  have c01 : casimir 0 1 = 1 := rfl
  have c02 : casimir 0 2 = 0 := rfl
  have c10 : casimir 1 0 = 1 := rfl
  have c11 : casimir 1 1 = 0 := rfl
  have c12 : casimir 1 2 = 0 := rfl
  have c20 : casimir 2 0 = 0 := rfl
  have c21 : casimir 2 1 = 0 := rfl
  have c22 : casimir 2 2 = 1 / 2 := rfl
  simp only [Fin.sum_univ_three, c00, c01, c02, c10, c11, c12, c20, c21, c22]
  ring

end GenericForm

/-! ### The BRST-level operators -/

/-- The ghost parity involution on the BRST space. -/
abbrev TB : Module.End ℂ BRSTSpace := Ppar.lTensor MatterSpace

/-- The `c₀`-free projection on the BRST space. -/
abbrev P0B : Module.End ℂ BRSTSpace := P0.lTensor MatterSpace

/-- `c₀`-free BRST states. -/
def C0B (u : BRSTSpace) : Prop := P0B u = u

theorem bB_eq (a : Fin 3) (m : ℤ) : bB a m = (gMode a 0 m).lTensor MatterSpace := rfl

/-- **The antighost transposes on the BRST space.** -/
theorem bB_transpose (a : Fin 3) (k : ℤ) (hk : k ≠ 0) (u v : BRSTSpace) :
    ghBBRST (bB a k u) v = Complex.I * ghBBRST (TB u) (bB a (-k) v) := by
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

theorem TB_JT (a : Fin 3) (k : ℤ) (u : BRSTSpace) : TB (JT a k u) = JT a k (TB u) := by
  rw [JT_eq]
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u u' hu hu' => simp only [map_add, LinearMap.add_apply] at hu hu' ⊢; rw [hu, hu']
  | tmul x y =>
      simp only [LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, map_add,
        Ppar_ghostJ]

theorem lTensor_comm_apply {f g : Module.End ℂ Sl2GhostSpace} (h : ∀ y, f (g y) = g (f y))
    (u : BRSTSpace) : f.lTensor MatterSpace (g.lTensor MatterSpace u) =
      g.lTensor MatterSpace (f.lTensor MatterSpace u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp only [LinearMap.lTensor_tmul, h]
  | add u u' hu hu' => rw [map_add, map_add, hu, hu', map_add, map_add]

theorem C0B_TB {u : BRSTSpace} (hu : C0B u) : C0B (TB u) := by
  unfold C0B at *
  rw [lTensor_comm_apply (fun y => (Ppar_P0 y).symm), hu]

theorem C0B_bB (a : Fin 3) {k : ℤ} (hk : k ≠ 0) {u : BRSTSpace} (hu : C0B u) :
    C0B (bB a k u) := by
  have hz : ¬ IsZeroMode 0 k := by
    unfold IsZeroMode; rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact hk h
    · exact absurd h (by decide)
  unfold C0B at *
  rw [bB_eq, lTensor_comm_apply (fun y => (gMode_comm_P0 a hz y).symm), hu]

theorem P0B_tmul (x : MatterSpace) (y : Sl2GhostSpace) : P0B (x ⊗ₜ y) = x ⊗ₜ P0 y := rfl

/-- **The total current is skew on `c₀`-free BRST states.** -/
theorem JT_skew (a : Fin 3) (k : ℤ) (u v : BRSTSpace) (hu : C0B u) (hv : C0B v) :
    ghBBRST (JT a k u) v = -ghBBRST u (JT a (-k) v) := by
  have key : ∀ u v : BRSTSpace,
      ghBBRST (JT a k (P0B u)) (P0B v) = -ghBBRST (P0B u) (JT a (-k) (P0B v)) := by
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
            rw [matterB_current_skew bCompactUnitary,
              ghostB_ghostJ_skew a k (C0_P0 y) (C0_P0 y')]
            ring
  have h := key u v
  rwa [show P0B u = u from hu, show P0B v = v from hv] at h

/-! ### Relative states -/

theorem pc_eq_sub (a : Fin 3) (y : Sl2GhostSpace) : pc a y = y - c0 a (b0 a y) := by
  have h := gMode_anticomm_apply a a 0 1 0 (-1) y
  rw [if_pos ⟨rfl, rfl, by ring⟩] at h
  exact eq_sub_of_add_eq h

theorem lTensor_pc_eq (a : Fin 3) (u : BRSTSpace) :
    (pc a).lTensor MatterSpace u =
      u - (c0 a).lTensor MatterSpace ((b0 a).lTensor MatterSpace u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp only [LinearMap.lTensor_tmul, pc_eq_sub, TensorProduct.tmul_sub]
  | add u u' hu hu' => rw [map_add, hu, hu', map_add, map_add]; abel

theorem lTensor_pc_of (a : Fin 3) {u : BRSTSpace} (hu : (b0 a).lTensor MatterSpace u = 0) :
    (pc a).lTensor MatterSpace u = u := by
  rw [lTensor_pc_eq, hu, map_zero, sub_zero]

/-- Relative states are `c₀`-free. -/
theorem C0B_of_b0 {u : BRSTSpace} (hu : ∀ a, (b0 a).lTensor MatterSpace u = 0) : C0B u := by
  have h2 := lTensor_pc_of 2 (hu 2)
  have h1 := lTensor_pc_of 1 (hu 1)
  have h0 := lTensor_pc_of 0 (hu 0)
  unfold C0B
  show P0.lTensor MatterSpace u = u
  rw [show P0 = pc 0 * pc 1 * pc 2 from rfl, LinearMap.lTensor_mul, LinearMap.lTensor_mul,
    Module.End.mul_apply, Module.End.mul_apply, h2, h1, h0]

theorem relative_C0B {n : ℤ} {u : BRSTSpace} (hu : u ∈ relativeWeight n) : C0B u := by
  refine C0B_of_b0 fun a => ?_
  have h := ((mem_relativeCarrier _ u).mp hu.1).2 a
  rw [antighostZero_eq] at h
  exact h

theorem koszul_one_intCast (g : ℤ) : koszul 1 ((g : ℤ) : ZMod 2) = (-1 : ℂ) ^ g := by
  rcases Int.even_or_odd g with hg | hg
  · rw [(ZMod.intCast_eq_zero_iff_even).mpr hg, hg.neg_one_zpow]
    simp [koszul, parSign]
  · rw [(ZMod.intCast_eq_one_iff_odd).mpr hg, hg.neg_one_zpow]
    simp [koszul, parSign]

/-- `T = (-1)^g` on BRST ghost number `g`. -/
theorem TB_brstDeg {j g : ℤ} {w : ℂ} {u : BRSTSpace} (hu : u ∈ brstDeg bgGh ((j, g), w)) :
    TB u = ((-1 : ℂ) ^ g) • u := by
  refine tensorDeg_induction matterDeg ghostDeg ((j, g), w) (fun u => TB u = ((-1 : ℂ) ^ g) • u)
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
  · rw [eq_zero_of_mem_zeroGhost hb (matterDeg_le_zeroGhost b hx)]
    simp

/-! ### `GhostConjBE` -/

/-- **`GhostConjBE` is proved outright** (no hypothesis; in particular no `hA`). -/
theorem ghostConjBE_proved : GhostConjBE := by
  intro n j g u hur hu v hvr
  have hC := relative_C0B hur
  have hCv := relative_C0B hvr
  rw [brstE_eq]
  rw [B_E_of_transposeT ghBBRST C0B TB bB JT Complex.I
      (fun a k hk u hu => C0B_bB a hk hu) (fun u hu => C0B_TB hu) TB_JT
      bB_transpose (fun a k u v hu hv => JT_skew a k u v hu hv)
      (Finset.Icc 1 n.toNat) (fun m hm => by
        have := (Finset.mem_Icc.mp hm).1; omega) _ u hC v hCv,
    TB_brstDeg hu, LinearMap.map_smul₂, smul_eq_mul]
  ring

end

end VOA.ConcreteHodge
