/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGriessSpinForm
import VOA.Moonshine.MoonshineCNGriessUntwistedBasis
import VOA.Moonshine.AutZeroModesTwisted

/-!
# The twisted weight-two space `(T⁺)₂ = h(−½) ⊗ T` in Conway and spin coordinates

The twisted weight-two space of `V♮` is `(T⁺)₂ = h(−½) ⊗ T` (`hP v t`, `SigmaTopFrame`).  This file
writes it in the coordinates of Axiom's `W`-block: a complex `SpinIdx × 24` matrix `N` (columns in
Conway's coordinates `i`, rows in the spin index `s`) goes to

  `spinTopVec N = Σᵢ h_{fᵢ}(−½) ⊗ Ψ(N_{·i})`,

where `fᵢ = conwayVec i` is the frame vector of the Conway axis `8eᵢ` and `Ψ = spinIso`.  The
weight-one action `u₍₁₎` of the untwisted weight-two states (`topAct u`) is then a matrix
operation on `N`:

* ⭐ `topAct_conwayQuad_spinTopVec` — for symmetric `A`:
  `Q_C(A)₍₁₎ (spinTopVec N) = spinTopVec (N A + (tr A / 8) N)` (from `actT_dV_hP`);
* ⭐ `topAct_frameX0P_spinTopVec` — for `|α|² = 4` with Conway coordinates `y`:
  `x_α₍₁₎ (spinTopVec N) = ⅛ spinTopVec (S N − ¼ S N y yᵀ)`, `S = spinOp(ᾱ)`
  (from `leechYM_echg_X`, `leechYM_echg_neg_two` and `spinIso_spinOp`);
* ⭐ `TPForm_spinTopVec` — `TPForm (spinTopVec N) (spinTopVec M) = −4κ Σ N_{si} M_{si}`
  (`TForm_spinIso`, `fockForm_hvec`, `FᵀF = 8`).

It also collects the block facts of the vertex algebra `V♮` used by the dictionary:
`vnat_smul_untwisted_twisted` (`(u,0)₍₁₎(0,t) = (0, u₍₁₎t)`), `vnat_smul_twisted_twisted_snd`
(twisted × twisted lands in `V_Λ⁺`), `vnat_smul_one_comm` (commutativity on `V♮₂`) and
`natForm_smul_one_adjoint` (`⟨x₍₁₎a, b⟩ = ⟨a, x₍₁₎b⟩` for `x ∈ V♮₂`, from `natForm_fhl` and
`L₁ V♮₂ ⊆ V♮₁ = 0`).
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.GriessDictionary

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.SigmaTop VOA.Moonshine.TrialityTw
open VOA.LatGen VOA.IntegralLattice HeisenbergN
open VOA.Moonshine.InvForm VOA.Moonshine.TFormLeech
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Spin
open VOA.Moonshine.MonsterGriess.LeechMatch (vec)
open VOA.Moonshine.LatticeTwisted (echg leechTwistedModule)
open Matrix

/-! ## §1  The Conway frame vectors `fᵢ` -/

/-- The orthonormal coordinates `fᵢ` of the Conway axis `8eᵢ`. -/
noncomputable def conwayVec (i : Fin 24) : Fin (rank leech) → ℂ := chargeCoord leech (conwayAxis i)

/-- `⟨fᵢ, fⱼ⟩ = 8δᵢⱼ`. -/
theorem sum_conwayVec_mul (i j : Fin 24) :
    ∑ a, conwayVec i a * conwayVec j a = if i = j then 8 else 0 := by
  simp only [conwayVec]
  rw [sum_chargeCoord leech leech_posDef, form_conwayAxis_conwayAxis]
  split_ifs <;> norm_num

/-- `⟨fᵢ, α⟩ = (vec α)ᵢ`. -/
theorem sum_conwayVec_mul_chargeCoord (i : Fin 24) (α : leech.carrier) :
    ∑ a, conwayVec i a * chargeCoord leech α a = (LeechMatch.vec α i : ℂ) := by
  simp only [conwayVec]
  rw [sum_chargeCoord leech leech_posDef, form_conwayAxis]

/-- `Σⱼ (vec α)ⱼ fⱼ = 8 α` (frame coordinates). -/
theorem sum_vec_smul_conwayVec (α : leech.carrier) :
    ∑ j, (LeechMatch.vec α j : ℂ) • conwayVec j = (8 : ℂ) • chargeCoord leech α := by
  have h := conwayFrame_mulVec α
  funext a
  have ha := congrFun h a
  simp only [Matrix.mulVec, dotProduct, conwayFrame, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul] at ha
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, conwayVec]
  rw [← ha]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- `fₖ = Σᵢ δᵢₖ fᵢ`. -/
theorem conwayVec_eq_sum (k : Fin 24) :
    conwayVec k = ∑ i, (if i = k then (1 : ℂ) else 0) • conwayVec i := by
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-! ## §2  The top-level states `h_v(−½) ⊗ Ψ(w)` -/

/-- `h_v(−½) ⊗ Ψ(w) ∈ T⁺`, bilinear in the frame vector `v` and `w ∈ ℂ^SpinIdx`. -/
noncomputable def spinTopState : (Fin (rank leech) → ℂ) →ₗ[ℂ] (SpinIdx → ℂ) →ₗ[ℂ] TP :=
  LinearMap.mk₂ ℂ (fun v w => hP v (spinIsoC w))
    (fun v v' w => hP_add_left v v' _)
    (fun c v w => hP_smul_left c v _)
    (fun v w w' => by
      apply Subtype.ext
      simp only [hP_coe, Submodule.coe_add, map_add, TensorProduct.tmul_add])
    (fun c v w => by
      apply Subtype.ext
      simp only [hP_coe, Submodule.coe_smul, map_smul, TensorProduct.tmul_smul])

theorem spinTopState_apply (v : Fin (rank leech) → ℂ) (w : SpinIdx → ℂ) :
    spinTopState v w = hP v (spinIso w) := rfl

theorem spinTopState_mem_weight_two (v : Fin (rank leech) → ℂ) (w : SpinIdx → ℂ) :
    spinTopState v w ∈ plusModule.weight (2 : ℂ) :=
  hP_mem_weight v _

/-- **The top-level twisted state of a Conway-coordinate matrix**:
`spinTopVec N = Σᵢ h_{fᵢ}(−½) ⊗ Ψ(N_{·i})`. -/
noncomputable def spinTopVec : Matrix SpinIdx (Fin 24) ℂ →ₗ[ℂ] TP where
  toFun N := ∑ i, spinTopState (conwayVec i) (fun s => N s i)
  map_add' N M := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_add]
    rfl
  map_smul' c N := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RingHom.id_apply, ← map_smul]
    rfl

theorem spinTopVec_apply (N : Matrix SpinIdx (Fin 24) ℂ) :
    spinTopVec N = ∑ i, spinTopState (conwayVec i) (fun s => N s i) := rfl

theorem spinTopVec_mem_weight_two (N : Matrix SpinIdx (Fin 24) ℂ) :
    spinTopVec N ∈ plusModule.weight (2 : ℂ) :=
  Submodule.sum_mem _ fun i _ => spinTopState_mem_weight_two _ _

/-- **Column recombination**: if column `k` is carried by `Σᵢ Cᵢₖ fᵢ`, the state is
`spinTopVec (N Cᵀ)`. -/
theorem sum_spinTopState_recombine (C : Matrix (Fin 24) (Fin 24) ℂ) (N : Matrix SpinIdx (Fin 24) ℂ) :
    ∑ k, spinTopState (∑ i, C i k • conwayVec i) (fun s => N s k) = spinTopVec (N * Cᵀ) := by
  rw [spinTopVec_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [← map_smul, ← map_sum]
  congr 1
  funext s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-! ## §3  The weight-one action `u₍₁₎` of `V_Λ⁺` on `T⁺` -/

/-- The action `t ↦ u₍₁₎ t` of `u ∈ V_Λ⁺` on the `V_Λ⁺`-module `T⁺`. -/
noncomputable def topAct (u : VPlus) : TP →ₗ[ℂ] TP := mode (plusModule.YM u) 1

theorem topAct_add (u v : VPlus) : topAct (u + v) = topAct u + topAct v := by
  simp only [topAct, map_add, mode_add]

theorem topAct_smul (c : ℂ) (u : VPlus) : topAct (c • u) = c • topAct u := by
  simp only [topAct, map_smul, mode_smul]

theorem topAct_zero : topAct 0 = 0 := by
  simp only [topAct, map_zero, mode_zero]

theorem topAct_sum {ι : Type*} (s : Finset ι) (f : ι → VPlus) :
    topAct (∑ i ∈ s, f i) = ∑ i ∈ s, topAct (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, topAct_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, topAct_add, ih]

theorem topAct_hP_sum (u : VPlus) (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    topAct u (hP v t) = ∑ c, v c • topAct u (hP (Pi.single c 1) t) := by
  conv_lhs => rw [pi_eq_sum_single v]
  rw [hP_sum_left, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hP_smul_left, map_smul]

/-! ## §4  The `S²𝔥` channel -/

/-- `o(α(−1)β(−1)𝟙)` on `h_γ(−½)`, in lattice terms. -/
theorem dL_chargeCoord (α β γ : leech.carrier) :
    dL α β (chargeCoord leech γ) = (((leech.form α β : ℤ) : ℂ) / 8) • chargeCoord leech γ
      + (((leech.form β γ : ℤ) : ℂ) / 2) • chargeCoord leech α
      + (((leech.form α γ : ℤ) : ℂ) / 2) • chargeCoord leech β := by
  simp only [dL, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, LinearMap.sum_apply, LinearMap.proj_apply, smul_eq_mul]
  rw [sum_chargeCoord leech leech_posDef β γ, sum_chargeCoord leech leech_posDef α γ]
  module

/-- `o((8eᵢ)(−1)(8eⱼ)(−1)𝟙)` on `h_{fₖ}(−½)`. -/
theorem dL_conwayAxis (i j k : Fin 24) :
    dL (conwayAxis i) (conwayAxis j) (conwayVec k)
      = (if i = j then (1 : ℂ) else 0) • conwayVec k + (if j = k then (4 : ℂ) else 0) • conwayVec i
        + (if i = k then (4 : ℂ) else 0) • conwayVec j := by
  simp only [conwayVec]
  rw [dL_chargeCoord, form_conwayAxis_conwayAxis, form_conwayAxis_conwayAxis,
    form_conwayAxis_conwayAxis]
  split_ifs <;> norm_num

/-- `Q_C(A)₍₁₎` on `h_v(−½) ⊗ t`, through the lattice letters of `conwayQuad_eq_sum_dV`. -/
theorem topAct_conwayQuad_hP (A : Matrix (Fin 24) (Fin 24) ℂ) (v : Fin (rank leech) → ℂ)
    (t : TLeechT) :
    topAct (conwayQuad A) (hP v t)
      = hP ((8 : ℂ)⁻¹ • ∑ i, ∑ j, A i j • dL (conwayAxis i) (conwayAxis j) v) t := by
  rw [conwayQuad_eq_sum_dV, topAct_smul, topAct_sum, LinearMap.smul_apply, LinearMap.sum_apply,
    hP_smul_left, hP_sum_left]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [topAct_sum, LinearMap.sum_apply, hP_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [topAct_smul, LinearMap.smul_apply, hP_smul_left]
  congr 1
  exact actT_dV_hP _ _ v t

/-- The coefficient matrix of `Q_C(A)₍₁₎` on the frame vectors:
`C_{ik} = (tr A / 8) δᵢₖ + ½ (A_{ik} + A_{ki})`. -/
noncomputable def quadCoeff (A : Matrix (Fin 24) (Fin 24) ℂ) : Matrix (Fin 24) (Fin 24) ℂ :=
  Matrix.of fun i k => (trace A / 8) * (if i = k then 1 else 0) + (A i k + A k i) / 2

theorem conwayQuad_dL_sum (A : Matrix (Fin 24) (Fin 24) ℂ) (k : Fin 24) :
    (8 : ℂ)⁻¹ • ∑ i, ∑ j, A i j • dL (conwayAxis i) (conwayAxis j) (conwayVec k)
      = ∑ i, quadCoeff A i k • conwayVec i := by
  have T1 : ∑ i, ∑ j, A i j • ((if i = j then (1 : ℂ) else 0) • conwayVec k)
      = trace A • conwayVec k := by
    simp only [ite_smul, one_smul, zero_smul, smul_ite, smul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [← Finset.sum_smul]
    rfl
  have T2 : ∑ i, ∑ j, A i j • ((if j = k then (4 : ℂ) else 0) • conwayVec i)
      = ∑ i, (A i k * 4) • conwayVec i := by
    simp only [ite_smul, zero_smul, smul_ite, smul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, smul_smul]
  have T3 : ∑ i, ∑ j, A i j • ((if i = k then (4 : ℂ) else 0) • conwayVec j)
      = ∑ j, (A k j * 4) • conwayVec j := by
    simp only [ite_smul, zero_smul, smul_ite, smul_zero, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_smul]
  have hL : (8 : ℂ)⁻¹ • ∑ i, ∑ j, A i j • dL (conwayAxis i) (conwayAxis j) (conwayVec k)
      = ((8 : ℂ)⁻¹ * trace A) • conwayVec k + ∑ i, ((8 : ℂ)⁻¹ * (A i k * 4)) • conwayVec i
        + ∑ j, ((8 : ℂ)⁻¹ * (A k j * 4)) • conwayVec j := by
    simp only [dL_conwayAxis, smul_add, Finset.sum_add_distrib]
    rw [T1, T2, T3]
    simp only [Finset.smul_sum, smul_smul]
  have hR : ∑ i, quadCoeff A i k • conwayVec i
      = (trace A / 8) • conwayVec k + ∑ i, ((A i k + A k i) / 2) • conwayVec i := by
    simp only [quadCoeff, Matrix.of_apply, add_smul, Finset.sum_add_distrib, mul_ite, mul_one,
      mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hL, hR, add_assoc]
  congr 1
  · congr 1
    ring
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_smul]
    congr 1
    ring

/-- ⭐ **The `S²𝔥` channel on `(T⁺)₂`**: for symmetric `A`,
`Q_C(A)₍₁₎ (spinTopVec N) = spinTopVec (N A + (tr A / 8) N)`. -/
theorem topAct_conwayQuad_spinTopVec {A : Matrix (Fin 24) (Fin 24) ℂ} (hA : Aᵀ = A)
    (N : Matrix SpinIdx (Fin 24) ℂ) :
    topAct (conwayQuad A) (spinTopVec N) = spinTopVec (N * A + (trace A / 8) • N) := by
  rw [spinTopVec_apply, map_sum]
  have hk : ∀ k, topAct (conwayQuad A) (spinTopState (conwayVec k) (fun s => N s k))
      = spinTopState (∑ i, quadCoeff A i k • conwayVec i) (fun s => N s k) := by
    intro k
    rw [spinTopState_apply, topAct_conwayQuad_hP, conwayQuad_dL_sum]
    rfl
  simp only [hk]
  rw [sum_spinTopState_recombine]
  congr 1
  ext s i
  have hAs : ∀ a b, A a b = A b a := fun a b => by
    have := congrFun (congrFun hA b) a
    rwa [Matrix.transpose_apply] at this
  simp only [Matrix.mul_apply, Matrix.transpose_apply, quadCoeff, Matrix.of_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hAs i j]
    ring
  · ring

/-! ## §5  The short-vector channel -/

theorem two_zpow_neg_three : (2 : ℂ) ^ (-(3 : ℤ)) = (8 : ℂ)⁻¹ := by norm_num

/-- `o(x_α)` on `h_v(−½) ⊗ t` for `|α|² = 4`, any `α` (no frame-sector condition):
`o(e^α + e^{−α})(h_v ⊗ t) = 2⁻³ h_{v − 2⟨v,α⟩α} ⊗ e_α t`. -/
theorem topAct_frameX0P_hP {α : leech.carrier} (hα : leech.form α α = 4)
    (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    topAct (frameX0P α) (hP v t)
      = ((2 : ℂ) ^ (-(3 : ℤ))) • hP (latL α v) (eT leech leech_even leech_isUnit_det_gramMat α t) := by
  rw [topAct_hP_sum]
  conv_rhs => rw [pi_eq_sum_single v, map_sum]
  rw [hP_sum_left, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, hP_smul_left, smul_comm]
  congr 1
  apply Subtype.ext
  rw [topAct, mode_plusModule, hP_coe, Submodule.coe_smul, hP_coe, hvec_single]
  change leechTwistedModule.YM (echg leech α + echg leech (-α)) (2 * 1) _ = _
  rw [show (2 : ℤ) * 1 = 2 by norm_num, map_add, Pi.add_apply, LinearMap.add_apply,
    leechYM_echg_neg_two, leechYM_echg_X α hα]
  simp only [latL, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, LinearMap.sum_apply, LinearMap.proj_apply,
    hvec_sub, hvec_smul, hvec_single, hvec_chargeCoord]
  have hc : chT α (cc c) = chargeCoord leech α c := by simp [chT, cc]
  have hs : (∑ a, chargeCoord leech α a • Pi.single c (1 : ℂ) a) = chargeCoord leech α c := by
    simp [Pi.single_apply]
  rw [hc, hs, ← add_smul, ← smul_smul (2 : ℂ) (chargeCoord leech α c)]
  congr 1
  norm_num

/-- The coefficient matrix of the reflection part of `o(x_α)` on the frame vectors:
`C_{ik} = δᵢₖ − ¼ yᵢ yₖ`. -/
noncomputable def reflCoeff (y : Fin 24 → ℂ) : Matrix (Fin 24) (Fin 24) ℂ :=
  Matrix.of fun i k => (if i = k then (1 : ℂ) else 0) - y i * y k / 4

/-- The reflection part on a frame vector: `fₖ − 2⟨fₖ,α⟩α = Σᵢ (δᵢₖ − ¼ yᵢ yₖ) fᵢ`,
`y = vec α`. -/
theorem latL_conwayVec (α : leech.carrier) (k : Fin 24) :
    latL α (conwayVec k) = ∑ i, reflCoeff (fun j => (LeechMatch.vec α j : ℂ)) i k • conwayVec i := by
  have hp : ∑ a, chargeCoord leech α a * conwayVec k a = (LeechMatch.vec α k : ℂ) := by
    rw [← sum_conwayVec_mul_chargeCoord]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hα : chargeCoord leech α = (8 : ℂ)⁻¹ • ∑ j, (LeechMatch.vec α j : ℂ) • conwayVec j := by
    rw [sum_vec_smul_conwayVec, smul_smul]
    norm_num
  simp only [latL, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, LinearMap.sum_apply, LinearMap.proj_apply, smul_eq_mul]
  rw [hp]
  conv_lhs => rw [conwayVec_eq_sum k, hα]
  rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smul_smul]
  rw [← sub_smul, reflCoeff, Matrix.of_apply]
  congr 1
  ring

/-- `e_α (Ψ N_{·k}) = Ψ((S N)_{·k})`, `S = spinOp(ᾱ)`. -/
theorem eT_spinIso_col (α : leech.carrier) (N : Matrix SpinIdx (Fin 24) ℂ) (k : Fin 24) :
    eT leech leech_even leech_isUnit_det_gramMat α (spinIso (fun s => N s k))
      = spinIso (fun s => (spinOp (coordOfRed (red leech α)) * N) s k) :=
  (spinIso_spinOp α (fun s => N s k)).symm

/-- ⭐ **The short-vector channel on `(T⁺)₂`**: for `|α|² = 4`, with Conway coordinates `y` of `α`
and `S = spinOp(ᾱ)`: `x_α₍₁₎ (spinTopVec N) = ⅛ spinTopVec (S N − ¼ S N y yᵀ)`. -/
theorem topAct_frameX0P_spinTopVec {α : leech.carrier} (hα : leech.form α α = 4)
    (N : Matrix SpinIdx (Fin 24) ℂ) :
    topAct (frameX0P α) (spinTopVec N)
      = (8 : ℂ)⁻¹ • spinTopVec (spinOp (coordOfRed (red leech α)) * N
          - (4 : ℂ)⁻¹ • (spinOp (coordOfRed (red leech α)) * N
              * vecMulVec (fun i => (LeechMatch.vec α i : ℂ)) (fun i => (LeechMatch.vec α i : ℂ)))) := by
  rw [spinTopVec_apply, map_sum]
  have hk : ∀ k, topAct (frameX0P α) (spinTopState (conwayVec k) (fun s => N s k))
      = (8 : ℂ)⁻¹ • spinTopState (∑ i, reflCoeff (fun j => (LeechMatch.vec α j : ℂ)) i k • conwayVec i)
          (fun s => (spinOp (coordOfRed (red leech α)) * N) s k) := by
    intro k
    rw [spinTopState_apply, topAct_frameX0P_hP hα, latL_conwayVec, two_zpow_neg_three,
      eT_spinIso_col]
    rfl
  simp only [hk]
  rw [← Finset.smul_sum, sum_spinTopState_recombine]
  congr 2
  generalize spinOp (coordOfRed (red leech α)) * N = P
  ext s i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, reflCoeff, Matrix.of_apply, Matrix.sub_apply,
    Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## §6  The form on `(T⁺)₂` -/

theorem TPForm_spinTopState (v v' : Fin (rank leech) → ℂ) (w w' : SpinIdx → ℂ) :
    TPForm (spinTopState v w) (spinTopState v' w')
      = spinFormScale * (w ⬝ᵥ w') * (-(1 / 2 : ℂ) * ∑ a, v a * v' a) := by
  rw [spinTopState_apply, spinTopState_apply, SigmaAssemble.TPForm_hP, SigmaAssemble.fockForm_hvec,
    TForm_spinIso]

/-- ⭐ **The form on `(T⁺)₂` in spin coordinates**:
`TPForm (spinTopVec N) (spinTopVec M) = −4κ Σ_{s,i} N_{si} M_{si}`. -/
theorem TPForm_spinTopVec (N M : Matrix SpinIdx (Fin 24) ℂ) :
    TPForm (spinTopVec N) (spinTopVec M)
      = -4 * spinFormScale * ∑ s, ∑ i, N s i * M s i := by
  rw [spinTopVec_apply, spinTopVec_apply, map_sum]
  simp only [LinearMap.sum_apply, map_sum, TPForm_spinTopState, sum_conwayVec_mul]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm (f := fun s i => N s i * M s i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [dotProduct]
  ring

/-! ## §7  Block facts of `V♮` -/

/-- `(u, 0)₍₁₎(0, t) = (0, u₍₁₎ t)`. -/
theorem vnat_smul_untwisted_twisted (u : VPlus) (t : TP) :
    VnatVOA.smul ((u, 0) : Vnat) 1 ((0, t) : Vnat) = (0, topAct u t) :=
  AutZeroTw.VnatVOA_smul_inl_inr u 1 t

/-- The product of two twisted states lies in the untwisted block. -/
theorem vnat_smul_twisted_twisted_snd (t t' : TP) (n : ℤ) :
    (VnatVOA.smul ((0, t) : Vnat) n ((0, t') : Vnat)).2 = 0 := by
  change (mode (VnatAxioms.YN (((0 : SkewVP), t) : Vnat)) n (((0 : SkewVP), t') : Vnat)).2 = 0
  rw [VnatAxioms.mode_YN]
  simp only [map_zero, mode_zero, LinearMap.zero_apply, add_zero]

/-- The `(1)`-product is commutative on `V♮₂`. -/
theorem vnat_smul_one_comm {x y : Vnat} (hx : x ∈ gradingNat 2) (hy : y ∈ gradingNat 2) :
    VnatVOA.smul x 1 y = VnatVOA.smul y 1 x := by
  have h := vnat_griessMul_comm (⟨x, by rw [VnatVOA_grading]; exact hx⟩ : VnatVOA.grading 2)
    ⟨y, by rw [VnatVOA_grading]; exact hy⟩
  have h' := congrArg Subtype.val h
  simpa only [VertexOperatorAlgebra.griessMul_coe] using h'

/-- `L₁ V♮₂ = 0`. -/
theorem vnat_L_one_of_two {x : Vnat} (hx : x ∈ gradingNat 2) : VnatVOA.L 1 x = 0 := by
  have h := VertexOperatorAlgebra.L_one_lower VnatVOA (k := 2) (x := x)
    (by rw [VnatVOA_grading]; exact hx)
  rw [show (2 : ℤ) - 1 = 1 by norm_num, VnatVOA_grading_one] at h
  exact (Submodule.mem_bot ℂ).mp h

/-- ⭐ **The Griess product is self-adjoint for `natForm`**: `⟨x₍₁₎a, b⟩ = ⟨a, x₍₁₎b⟩` for
`x ∈ V♮₂` (FHL invariance, `natForm_fhl`, with `L₁ x = 0`). -/
theorem natForm_smul_one_adjoint {x : Vnat} (hx : x ∈ gradingNat 2) (a b : Vnat) :
    SimpleNat.natForm (VnatVOA.smul x 1 a) b = SimpleNat.natForm a (VnatVOA.smul x 1 b) := by
  have h := SimpleNat.natForm_fhl vnat_twistedLocality 2 x hx 1 a b
  change SimpleNat.natForm (VnatVOA.smul x 1 a) b = (-1 : ℂ) ^ (2 : ℤ) •
      ∑ j ∈ Finset.range ((2 : ℤ).toNat + 1), ((j.factorial : ℂ)⁻¹) •
        SimpleNat.natForm a (VnatVOA.smul ((VnatVOA.L 1 ^ j) x) (2 * 2 - 1 - 2 - (j : ℤ)) b) at h
  rw [h, show (2 : ℤ).toNat + 1 = 3 by rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  have hL := vnat_L_one_of_two hx
  have h1 : (VnatVOA.L 1 ^ 1) x = 0 := by rw [pow_one, hL]
  have h2 : (VnatVOA.L 1 ^ 2) x = 0 := by rw [pow_two, Module.End.mul_apply, hL, map_zero]
  rw [h1, h2, pow_zero, Module.End.one_apply]
  simp only [PreVertexAlgebra.smul_zero_left, map_zero, smul_zero, add_zero, zero_add]
  norm_num

end VOA.Moonshine.GriessDictionary
