/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTConjIdentityFock

/-!
# Mode transposes for the ghost bilinear form `B_G`

On the three-pair ghost space, with `Cr a p` the creation operator of the mode `p` in colour `a`
and `An a q = gMode a (q.2 + 1) q.1` the annihilation operator of the mode `q`:

* `An_Cr_anticomm` — the canonical anticommutation relations `{An a q, Cr b p} = δ_{ab} δ_{qp}`;
* `Ppar_gMode` — every ghost mode anticommutes with the parity involution `Ppar`;
* `ghost_induction` — every ghost state is built from the vacuum by creation operators;
* `ghostConj_An` — the conjugation intertwines the annihilation operators:
  `ρ_G (An a q x) = -(c_a(q))⁻¹ An a (σ q) (Ppar (ρ_G x))` (from `ghostConj_Cr` and the CAR, by
  induction on states);
* `bgPG_Cr_adj`, `bgPG_An_adj` — creation and annihilation are adjoint for the colour-weighted
  form `bgPG` up to the mode norm;
* `ghostIR_gMode` — `i^{2R}` commutes with each mode up to `i^{2R}` of the mode;
* `ghostB_Cr`, `ghostB_An` — the **mode transposes of `B_G`**: for every mode `p`,
  `B_G(Cr a p z, y) = κ B_G(Ppar z, An a (σp) y)` and
  `B_G(An a q z, y) = κ' B_G(Ppar z, Cr a (σq) y)` with explicit constants; for `p, q ≠ c₀` both
  constants are `i` (`ghostB_Cr_I`, `ghostB_An_I`).

Everything is proved outright.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open VOA.SympFerm VOA.Ghost AffineVOA
open scoped TensorProduct

noncomputable section

/-! ### The annihilation operators and the CAR -/

/-- The annihilation operator of the mode `q` in colour `a`. -/
abbrev An (a : Fin 3) (q : ℕ × Fin 2) : Module.End ℂ Sl2GhostSpace := gMode a (q.2 + 1) (q.1 : ℤ)

theorem fin2_add_one_add_one (e : Fin 2) : e + 1 + 1 = e := by fin_cases e <;> rfl

theorem An_Cr_anticomm (a b : Fin 3) (q p : ℕ × Fin 2) (x : Sl2GhostSpace) :
    An a q (Cr b p x) + Cr b p (An a q x) = if a = b ∧ q = p then x else 0 := by
  have h := LinearMap.congr_fun
    (ghostGenerator_modes_anticomm a b (q.2 + 1) p.2 (q.1 : ℤ) (-(p.1 : ℤ) - 1)) x
  simp only [LinearMap.add_apply, Module.End.mul_apply] at h
  change An a q (Cr b p x) + Cr b p (An a q x) = _ at h
  rw [h]
  have hiff : (a = b ∧ q.2 + 1 + 1 = p.2 ∧ (q.1 : ℤ) + (-(p.1 : ℤ) - 1) + 1 = 0) ↔
      (a = b ∧ q = p) := by
    rw [fin2_add_one_add_one]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, Prod.ext ?_ h2⟩
      omega
    · rintro ⟨h1, rfl⟩
      exact ⟨h1, rfl, by ring⟩
  by_cases hc : a = b ∧ q = p
  · rw [if_pos (hiff.mpr hc), if_pos hc, LinearMap.id_apply]
  · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc, LinearMap.zero_apply]

theorem An_Cr_same (a : Fin 3) (q : ℕ × Fin 2) (x : Sl2GhostSpace) :
    An a q (Cr a q x) = x - Cr a q (An a q x) := by
  have h := An_Cr_anticomm a a q q x
  rw [if_pos ⟨rfl, rfl⟩] at h
  exact eq_sub_of_add_eq h

theorem An_Cr_ne {a b : Fin 3} {q p : ℕ × Fin 2} (h : ¬ (a = b ∧ q = p)) (x : Sl2GhostSpace) :
    An a q (Cr b p x) = -Cr b p (An a q x) := by
  have h' := An_Cr_anticomm a b q p x
  rw [if_neg h] at h'
  exact eq_neg_of_add_eq_zero_left h'

theorem Cr_Cr_anticomm (a b : Fin 3) (q p : ℕ × Fin 2) (x : Sl2GhostSpace) :
    Cr a q (Cr b p x) = -Cr b p (Cr a q x) := by
  have h := LinearMap.congr_fun
    (ghostGenerator_modes_anticomm a b q.2 p.2 (-(q.1 : ℤ) - 1) (-(p.1 : ℤ) - 1)) x
  simp only [LinearMap.add_apply, Module.End.mul_apply] at h
  rw [if_neg (by omega), LinearMap.zero_apply] at h
  exact eq_neg_of_add_eq_zero_left h

theorem gMode_anticomm_apply (a b : Fin 3) (i j : Fin 2) (m n : ℤ) (x : Sl2GhostSpace) :
    gMode a i m (gMode b j n x) + gMode b j n (gMode a i m x) =
      if a = b ∧ i + 1 = j ∧ m + n + 1 = 0 then x else 0 := by
  have h := LinearMap.congr_fun (ghostGenerator_modes_anticomm a b i j m n) x
  simp only [LinearMap.add_apply, Module.End.mul_apply] at h
  rw [h]
  split_ifs <;> rfl

/-! ### The vacuum and the parity involution -/

/-- The ghost vacuum. -/
abbrev gvac : Sl2GhostSpace := W3 [] [] []

theorem gvac_eq : gvac = sl2GhostSVA.vacuum := by
  rw [sl2GhostSVA_vacuum]; rfl

theorem gMode_gvac (a : Fin 3) (e : Fin 2) {m : ℤ} (hm : 0 ≤ m) : gMode a e m gvac = 0 := by
  rw [gvac_eq]
  exact (sl2GhostSVA.creation (ghostGenerator a e)).2 m hm

theorem An_gvac (a : Fin 3) (q : ℕ × Fin 2) : An a q gvac = 0 :=
  gMode_gvac a _ (Int.natCast_nonneg _)

theorem Ppar_gMode (a : Fin 3) (e : Fin 2) (m : ℤ) (y : Sl2GhostSpace) :
    Ppar (gMode a e m y) = -gMode a e m (Ppar y) := by
  obtain ⟨y0, hy0, y1, hy1, rfl⟩ := (TensorVA.parGr sl2GhostSVA).exists_parity_decomp y
  have h0 : gMode a e m y0 ∈ sl2GhostSVA.parity (1 + 0) :=
    sl2GhostSVA.parity_mode (ghostGenerator a e) (ghostGenerator_odd a e) y0 hy0 m
  have h1 : gMode a e m y1 ∈ sl2GhostSVA.parity (1 + 1) :=
    sl2GhostSVA.parity_mode (ghostGenerator a e) (ghostGenerator_odd a e) y1 hy1 m
  rw [add_zero] at h0
  rw [zmod2_one_add_one] at h1
  rw [map_add, map_add, map_add, ParityGrading.koszulOp_homog _ 1 h0,
    ParityGrading.koszulOp_homog _ 1 h1, ParityGrading.koszulOp_homog _ 1 hy0,
    ParityGrading.koszulOp_homog _ 1 hy1, map_add, map_smul, map_smul]
  simp only [koszul, parSign]
  norm_num
  abel

theorem Ppar_gvac : Ppar gvac = gvac := by
  rw [Ppar_W]; simp [len2, koszul, parSign]

/-- **Every ghost state is built from the vacuum by creation operators.** -/
theorem ghost_induction (Φ : Sl2GhostSpace → Prop) (h0 : Φ 0)
    (hadd : ∀ x y, Φ x → Φ y → Φ (x + y)) (hsmul : ∀ (c : ℂ) x, Φ x → Φ (c • x))
    (hvac : Φ gvac) (hcr : ∀ a p x, Φ x → Φ (Cr a p x)) (x : Sl2GhostSpace) : Φ x := by
  have hW : ∀ l0 l1 l2, Φ (W3 l0 l1 l2) := by
    intro l0 l1 l2
    induction l0 with
    | nil =>
        induction l1 with
        | nil =>
            induction l2 with
            | nil => exact hvac
            | cons p l2 ih =>
                have e : W3 [] [] (p :: l2) = Cr 2 p (W3 [] [] l2) := by
                  rw [Cr2_W]; simp [len2]
                rw [e]; exact hcr 2 p _ ih
        | cons p l1 ih =>
            have e : W3 [] (p :: l1) l2 = Cr 1 p (W3 [] l1 l2) := by
              rw [Cr1_W]; simp [len2]
            rw [e]; exact hcr 1 p _ ih
    | cons p l0 ih => rw [← Cr0_W]; exact hcr 0 p _ ih
  have hx : x ∈ Submodule.span ℂ (Set.range ghostBasis) := by
    rw [ghostBasis.span_eq]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; rw [ghostBasis_eq_W3]; exact hW _ _ _
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

theorem Ppar_Ppar (x : Sl2GhostSpace) : Ppar (Ppar x) = x := by
  refine ghost_induction (fun x => Ppar (Ppar x) = x) (by simp)
    (fun x y hx hy => by simp only at hx hy ⊢; rw [map_add, map_add, hx, hy])
    (fun c x hx => by simp only at hx ⊢; rw [map_smul, map_smul, hx])
    (by beta_reduce; rw [Ppar_gvac, Ppar_gvac]) (fun a p x hx => ?_) x
  simp only at hx ⊢
  rw [Ppar_gMode, map_neg, Ppar_gMode, neg_neg, hx]

theorem ghostConj_gvac : ghostConj gvac = gvac := by
  rw [ghostConj_W]; simp [wcoef, coefProd, cross3, len2, koszul, parSign, swapRev]

theorem ghostConj_Ppar (x : Sl2GhostSpace) : ghostConj (Ppar x) = Ppar (ghostConj x) := by
  refine ghost_induction (fun x => ghostConj (Ppar x) = Ppar (ghostConj x)) (by simp)
    (fun x y hx hy => by simp only at hx hy ⊢; rw [map_add, map_add, hx, hy, map_add, map_add])
    (fun c x hx => by
      simp only at hx ⊢; rw [map_smul, LinearMap.map_smulₛₗ, hx, LinearMap.map_smulₛₗ, map_smul])
    (by beta_reduce; rw [Ppar_gvac, ghostConj_gvac, Ppar_gvac]) (fun a p x hx => ?_) x
  simp only at hx ⊢
  rw [Ppar_gMode, map_neg, ghostConj_Cr, ghostConj_Cr, hx, map_smul, Ppar_gMode, smul_neg]

/-! ### The conjugation of the annihilation operators -/

theorem modeCoef_ne_zero (a : Fin 3) (p : ℕ × Fin 2) : modeCoef a p ≠ 0 := by
  intro h
  have := modeCoef_swap_mul a p
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem modeCoef_swap (a : Fin 3) (p : ℕ × Fin 2) :
    modeCoef a (swapMode p) = (modeCoef a p)⁻¹ :=
  eq_inv_of_mul_eq_one_left (modeCoef_swap_mul a p)

theorem swapMode_inj {p q : ℕ × Fin 2} (h : swapMode p = swapMode q) : p = q := by
  rw [← swapMode_swapMode p, h, swapMode_swapMode]

/-- The intertwining constant of the annihilation operators. -/
def anCoef (a : Fin 3) (q : ℕ × Fin 2) : ℝ := -(modeCoef a q)⁻¹

/-- **The conjugation intertwines the annihilation operators.** -/
theorem ghostConj_An (a : Fin 3) (q : ℕ × Fin 2) (x : Sl2GhostSpace) :
    ghostConj (An a q x) = ((anCoef a q : ℝ) : ℂ) • An a (swapMode q) (Ppar (ghostConj x)) := by
  refine ghost_induction (fun x => ghostConj (An a q x) =
      ((anCoef a q : ℝ) : ℂ) • An a (swapMode q) (Ppar (ghostConj x))) (by simp)
    (fun x y hx hy => by
      simp only at hx hy ⊢; rw [map_add, map_add, hx, hy, map_add, map_add, map_add, smul_add])
    (fun c x hx => by
      simp only at hx ⊢
      rw [map_smul, LinearMap.map_smulₛₗ, hx, LinearMap.map_smulₛₗ, map_smul, map_smul,
        smul_comm])
    (by beta_reduce; rw [An_gvac, map_zero, ghostConj_gvac, Ppar_gvac, An_gvac, smul_zero]) ?_ x
  intro b p x hx
  simp only at hx ⊢
  have hcl : ((modeCoef b p : ℝ) : ℂ) * ((anCoef a q : ℝ) : ℂ) =
      -(((modeCoef b p : ℝ) : ℂ) * ((modeCoef a q : ℝ) : ℂ)⁻¹) := by
    simp only [anCoef]; push_cast; ring
  by_cases hc : a = b ∧ q = p
  · obtain ⟨rfl, rfl⟩ := hc
    have hq : ((modeCoef a q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modeCoef_ne_zero a q
    have hone : ((modeCoef a q : ℝ) : ℂ) * ((anCoef a q : ℝ) : ℂ) = -1 := by
      rw [hcl, mul_inv_cancel₀ hq]
    have L : ghostConj (An a q (Cr a q x)) = ghostConj x +
        (((modeCoef a q : ℝ) : ℂ) * ((anCoef a q : ℝ) : ℂ)) •
          Cr a (swapMode q) (An a (swapMode q) (ghostConj x)) := by
      rw [An_Cr_same, map_sub, ghostConj_Cr, hx]
      simp only [map_smul, Ppar_gMode, Ppar_Ppar, map_neg, smul_neg, smul_smul, sub_neg_eq_add]
    have R : ((anCoef a q : ℝ) : ℂ) • An a (swapMode q) (Ppar (ghostConj (Cr a q x))) =
        (-(((modeCoef a q : ℝ) : ℂ) * ((anCoef a q : ℝ) : ℂ))) •
          (ghostConj x - Cr a (swapMode q) (An a (swapMode q) (ghostConj x))) := by
      rw [ghostConj_Cr]
      simp only [map_smul, Ppar_gMode, Ppar_Ppar, map_neg, smul_neg, smul_smul]
      rw [An_Cr_same]
      module
    rw [L, R, hone]
    module
  · have hne : ¬ (a = b ∧ swapMode q = swapMode p) := fun h => hc ⟨h.1, swapMode_inj h.2⟩
    have L : ghostConj (An a q (Cr b p x)) =
        (((modeCoef b p : ℝ) : ℂ) * ((anCoef a q : ℝ) : ℂ)) •
          Cr b (swapMode p) (An a (swapMode q) (ghostConj x)) := by
      rw [An_Cr_ne hc, map_neg, ghostConj_Cr, hx]
      simp only [map_smul, Ppar_gMode, Ppar_Ppar, map_neg, smul_neg, smul_smul, neg_neg]
    have R : ((anCoef a q : ℝ) : ℂ) • An a (swapMode q) (Ppar (ghostConj (Cr b p x))) =
        (((modeCoef b p : ℝ) : ℂ) * ((anCoef a q : ℝ) : ℂ)) •
          Cr b (swapMode p) (An a (swapMode q) (ghostConj x)) := by
      rw [ghostConj_Cr]
      simp only [map_smul, Ppar_gMode, Ppar_Ppar, map_neg, smul_neg, smul_smul]
      rw [An_Cr_ne hne]
      module
    rw [L, R]

/-! ### Adjointness for the colour-weighted form -/

/-- Two sesquilinear forms on a triple tensor product agreeing on pure triples agree. -/
theorem sesq_ext_tmul3 {V W U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup U] [Module ℂ U] (P Q : SesqForm ((V ⊗[ℂ] W) ⊗[ℂ] U))
    (h : ∀ v w u v' w' u', P ((v ⊗ₜ w) ⊗ₜ u) ((v' ⊗ₜ w') ⊗ₜ u') =
      Q ((v ⊗ₜ w) ⊗ₜ u) ((v' ⊗ₜ w') ⊗ₜ u')) (x y : (V ⊗[ℂ] W) ⊗[ℂ] U) : P x y = Q x y := by
  have hpure : ∀ (t : V ⊗[ℂ] W) (u : U) (y : (V ⊗[ℂ] W) ⊗[ℂ] U), P (t ⊗ₜ u) y = Q (t ⊗ₜ u) y := by
    intro t u y
    induction y using TensorProduct.induction_on with
    | zero => rw [P.zero_right, Q.zero_right]
    | add y y' h1 h2 => rw [P.add_right, Q.add_right, h1, h2]
    | tmul t' u' =>
        induction t using TensorProduct.induction_on with
        | zero => rw [TensorProduct.zero_tmul, P.zero_left, Q.zero_left]
        | add t1 t2 h1 h2 => rw [TensorProduct.add_tmul, P.add_left, Q.add_left, h1, h2]
        | tmul v w =>
            induction t' using TensorProduct.induction_on with
            | zero => rw [TensorProduct.zero_tmul, P.zero_right, Q.zero_right]
            | add t1 t2 h1 h2 => rw [TensorProduct.add_tmul, P.add_right, Q.add_right, h1, h2]
            | tmul v' w' => exact h v w u v' w' u'
  induction x using TensorProduct.induction_on with
  | zero => rw [P.zero_left, Q.zero_left]
  | add x x' h1 h2 => rw [P.add_left, Q.add_left, h1, h2]
  | tmul t u => exact hpure t u y

theorem ghField_cre (p : ℕ × Fin 2) : ghField p.2 (-(-(p.1 : ℤ) - 1) - 1) = creBase p := by
  rw [show -(-(p.1 : ℤ) - 1) - 1 = (p.1 : ℤ) by ring]
  simp only [ghField, Nat.cast_nonneg, if_true, Int.toNat_natCast, creGh]

theorem ghField_ann (q : ℕ × Fin 2) : ghField (q.2 + 1) (-(q.1 : ℤ) - 1) = annBase q := by
  simp only [ghField, annGh]
  rw [if_neg (by omega), show (-(-(q.1 : ℤ) - 1) - 1).toNat = q.1 by omega,
    fin2_add_one_add_one]

theorem Kf_fockBasis (s : Finset ModeIdx) :
    Kf (fockBasis s) = koszul 1 ((s.card : ℕ) : ZMod 2) • fockBasis s := by
  rw [fockBasis_eq_word, Kf_stWordSF, fockWord_length]

theorem conj_koszul_one (n : ZMod 2) : (starRingEnd ℂ) (koszul 1 n) = koszul 1 n :=
  conj_koszul 1 n

theorem fockForm_Kf (w : Finset ModeIdx → ℝ) (x y : FockSF) :
    fockForm w (Kf x) y = fockForm w x (Kf y) := by
  have key := sesq_ext_basis fockBasis (sesqComp (fockForm w) 1 Kf LinearMap.id)
    (sesqComp (fockForm w) 1 LinearMap.id Kf) ?_ x y
  · simpa using key
  intro s t
  change 1 * _ = 1 * _
  rw [LinearMap.id_apply, LinearMap.id_apply, Kf_fockBasis, Kf_fockBasis, (fockForm w).smul_left,
    (fockForm w).smul_right, conj_koszul_one, fockForm_basis]
  by_cases hst : s = t
  · subst hst; rfl
  · rw [if_neg hst]; ring

/-- The pair Koszul operator. -/
abbrev Kpair : Module.End ℂ GhostPairSpace := (TensorVA.parGr ghostPairSVA).koszulOp 1

theorem Kpair_tmul (x y : FockSF) : Kpair (x ⊗ₜ[ℂ] y) = Kf x ⊗ₜ[ℂ] Kf y := by
  obtain ⟨x0, hx0, x1, hx1, rfl⟩ := (TensorVA.parGr bcGhostSVA).exists_parity_decomp x
  obtain ⟨y0, hy0, y1, hy1, rfl⟩ := (TensorVA.parGr bcGhostSVA).exists_parity_decomp y
  have hm : ∀ {p q : ZMod 2} {u v : FockSF}, u ∈ bcGhostSVA.parity p → v ∈ bcGhostSVA.parity q →
      Kpair (u ⊗ₜ[ℂ] v) = Kf u ⊗ₜ[ℂ] Kf v := by
    intro p q u v hu hv
    have huv : u ⊗ₜ[ℂ] v ∈ ghostPairSVA.parity (p + q) :=
      TensorVA.tmul_mem_tenParity _ _ hu (by rw [add_sub_cancel_left]; exact hv)
    rw [ParityGrading.koszulOp_homog _ 1 huv, ParityGrading.koszulOp_homog _ 1 hu,
      ParityGrading.koszulOp_homog _ 1 hv, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul',
      smul_smul]
    congr 1
    rcases zmod2_cases p with rfl | rfl <;> rcases zmod2_cases q with rfl | rfl <;>
      simp [koszul, parSign, zmod2_one_add_one]
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hm hx0 hy0, hm hx0 hy1,
    hm hx1 hy0, hm hx1 hy1]

/-- The pair form. -/
abbrev pairForm (w0 w1 : Finset ModeIdx → ℝ) : SesqForm GhostPairSpace :=
  (fockForm w0).tensor (fockForm w1)

theorem pairForm_Kpair (w0 w1 : Finset ModeIdx → ℝ) (u v : GhostPairSpace) :
    pairForm w0 w1 (Kpair u) v = pairForm w0 w1 u (Kpair v) := by
  induction u using TensorProduct.induction_on generalizing v with
  | zero => rw [map_zero, SesqForm.zero_left, SesqForm.zero_left]
  | add u u' h1 h2 => rw [map_add, SesqForm.add_left, SesqForm.add_left, h1, h2]
  | tmul x y =>
      induction v using TensorProduct.induction_on with
      | zero => rw [map_zero, SesqForm.zero_right, SesqForm.zero_right]
      | add v v' h1 h2 => rw [map_add, SesqForm.add_right, SesqForm.add_right, h1, h2]
      | tmul x' y' =>
          rw [Kpair_tmul, Kpair_tmul, SesqForm.tensor_tmul, SesqForm.tensor_tmul, fockForm_Kf,
            fockForm_Kf]

theorem bgPG_tmul3 (x0 x1 x2 y0 y1 y2 : FockSF) :
    bgPG ((x0 ⊗ₜ x1) ⊗ₜ x2) ((y0 ⊗ₜ y1) ⊗ₜ y2) =
      fockForm (bgColourWeight 0) x0 y0 * fockForm (bgColourWeight 1) x1 y1 *
        fockForm (bgColourWeight 2) x2 y2 := rfl

theorem bgColourWeight_mult (a : Fin 3) :
    MultWeight (bgColourWeight a) fun p => bgColourNorm a (ofLex p) := by
  intro p s hp
  simp only [bgColourWeight]
  rw [Finset.prod_insert hp]

theorem Cr0_tmul (p : ℕ × Fin 2) (x y z : FockSF) :
    Cr 0 p ((x ⊗ₜ y) ⊗ₜ z) = (creBase p x ⊗ₜ y) ⊗ₜ z := by
  rw [Cr, gMode_tmul_zero, ghField_cre]
theorem Cr1_tmul (p : ℕ × Fin 2) (x y z : FockSF) :
    Cr 1 p ((x ⊗ₜ y) ⊗ₜ z) = (Kf x ⊗ₜ creBase p y) ⊗ₜ z := by
  rw [Cr, gMode_tmul_one, ghField_cre]
theorem Cr2_tmul (p : ℕ × Fin 2) (w : GhostPairSpace) (z : FockSF) :
    Cr 2 p (w ⊗ₜ z) = Kpair w ⊗ₜ creBase p z := by
  rw [Cr, gMode_tmul_two, ghField_cre]
theorem An0_tmul (q : ℕ × Fin 2) (x y z : FockSF) :
    An 0 q ((x ⊗ₜ y) ⊗ₜ z) = (annBase q x ⊗ₜ y) ⊗ₜ z := by
  rw [An, gMode_tmul_zero, ghField_ann]
theorem An1_tmul (q : ℕ × Fin 2) (x y z : FockSF) :
    An 1 q ((x ⊗ₜ y) ⊗ₜ z) = (Kf x ⊗ₜ annBase q y) ⊗ₜ z := by
  rw [An, gMode_tmul_one, ghField_ann]
theorem An2_tmul (q : ℕ × Fin 2) (w : GhostPairSpace) (z : FockSF) :
    An 2 q (w ⊗ₜ z) = Kpair w ⊗ₜ annBase q z := by
  rw [An, gMode_tmul_two, ghField_ann]

/-- The mode norm in colour `a`. -/
abbrev nrm (a : Fin 3) (p : ℕ × Fin 2) : ℝ := bgColourNorm a p

/-- **Creation is adjoint to `ν ·` annihilation for `bgPG`.** -/
theorem bgPG_Cr_adj (a : Fin 3) (p : ℕ × Fin 2) (x y : Sl2GhostSpace) :
    bgPG (Cr a p x) y = (nrm a p : ℂ) * bgPG x (An a p y) := by
  have key := sesq_ext_tmul3 (sesqComp bgPG 1 (Cr a p) LinearMap.id)
    (sesqComp bgPG (nrm a p) LinearMap.id (An a p)) ?_ x y
  · simpa using key
  intro x0 x1 x2 y0 y1 y2
  change 1 * _ = _ * _
  rw [one_mul, LinearMap.id_apply, LinearMap.id_apply]
  have hc := fun b => fockForm_cre_adj (bgColourWeight_mult b) (toLex p)
  have hK := pairForm_Kpair (bgColourWeight 0) (bgColourWeight 1)
  simp only [ofLex_toLex] at hc
  fin_cases a
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [Cr0_tmul, An0_tmul, bgPG_tmul3, bgPG_tmul3, hc 0]
    ring
  · simp only [Fin.mk_one, Fin.isValue]
    rw [Cr1_tmul, An1_tmul, bgPG_tmul3, bgPG_tmul3, hc 1, fockForm_Kf]
    ring
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [Cr2_tmul, An2_tmul]
    change pairForm _ _ (Kpair (x0 ⊗ₜ x1)) (y0 ⊗ₜ y1) * fockForm (bgColourWeight 2) _ y2 =
      _ * (pairForm _ _ (x0 ⊗ₜ x1) (Kpair (y0 ⊗ₜ y1)) * fockForm (bgColourWeight 2) x2 _)
    rw [hK, hc 2]
    ring

/-- **Annihilation is adjoint to `ν⁻¹ ·` creation for `bgPG`**:
`ν ⟨An a q x, y⟩ = ⟨x, Cr a q y⟩`. -/
theorem bgPG_An_adj (a : Fin 3) (q : ℕ × Fin 2) (x y : Sl2GhostSpace) :
    (nrm a q : ℂ) * bgPG (An a q x) y = bgPG x (Cr a q y) := by
  have key := sesq_ext_tmul3 (sesqComp bgPG (nrm a q) (An a q) LinearMap.id)
    (sesqComp bgPG 1 LinearMap.id (Cr a q)) ?_ x y
  · simpa using key
  intro x0 x1 x2 y0 y1 y2
  change _ * _ = 1 * _
  rw [one_mul, LinearMap.id_apply, LinearMap.id_apply]
  have hc := fun b => fockForm_ann_adj (bgColourWeight_mult b) (toLex q)
  have hK := pairForm_Kpair (bgColourWeight 0) (bgColourWeight 1)
  simp only [ofLex_toLex] at hc
  fin_cases a
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [Cr0_tmul, An0_tmul, bgPG_tmul3, bgPG_tmul3, ← hc 0]
    ring
  · simp only [Fin.mk_one, Fin.isValue]
    rw [Cr1_tmul, An1_tmul, bgPG_tmul3, bgPG_tmul3, ← hc 1, fockForm_Kf]
    ring
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [Cr2_tmul, An2_tmul]
    change _ * (pairForm _ _ (Kpair (x0 ⊗ₜ x1)) (y0 ⊗ₜ y1) * fockForm (bgColourWeight 2) _ y2) =
      pairForm _ _ (x0 ⊗ₜ x1) (Kpair (y0 ⊗ₜ y1)) * fockForm (bgColourWeight 2) x2 _
    rw [hK, ← hc 2]
    ring

/-! ### `i^{2R}` and the modes -/

theorem ghostIR_gMode (a : Fin 3) (e : Fin 2) (m : ℤ) (x : Sl2GhostSpace) :
    ghostIR (gMode a e m x) =
      Complex.I ^ (ghShiftF e (-m - 1)).1.1.1 • gMode a e m (ghostIR x) := by
  have hx : x ∈ ⨆ k, ghostDegF k := by rw [ghostDegF_span]; exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun x => ghostIR (gMode a e m x) =
      Complex.I ^ (ghShiftF e (-m - 1)).1.1.1 • gMode a e m (ghostIR x)) hx ?_ (by simp) ?_
  · intro k y hy
    rw [ghostIR_eigen (ghostModeF_mem a e m hy), ghostIR_eigen hy, map_smul, smul_smul,
      Prod.fst_add, Prod.fst_add, Prod.fst_add, zpow_add₀ Complex.I_ne_zero, mul_comm]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]

theorem ghShiftF_cr (p : ℕ × Fin 2) : (ghShiftF p.2 (-(-(p.1 : ℤ) - 1) - 1)).1.1.1 = modeR p := by
  rw [show -(-(p.1 : ℤ) - 1) - 1 = (p.1 : ℤ) by ring]
  simp [ghShiftF, modeIdxF, modeIdx]

theorem ghShiftF_an (q : ℕ × Fin 2) : (ghShiftF (q.2 + 1) (-(q.1 : ℤ) - 1)).1.1.1 = -modeR q := by
  simp only [ghShiftF]
  rw [if_neg (by omega), show (-(-(q.1 : ℤ) - 1) - 1).toNat = q.1 by omega, fin2_add_one_add_one]
  simp [modeIdxF, modeIdx]

theorem ghostIR_Cr (a : Fin 3) (p : ℕ × Fin 2) (x : Sl2GhostSpace) :
    ghostIR (Cr a p x) = Complex.I ^ modeR p • Cr a p (ghostIR x) := by
  rw [Cr, ghostIR_gMode, ghShiftF_cr]

theorem ghostIR_An (a : Fin 3) (q : ℕ × Fin 2) (x : Sl2GhostSpace) :
    ghostIR (An a q x) = Complex.I ^ (-modeR q) • An a q (ghostIR x) := by
  rw [An, ghostIR_gMode, ghShiftF_an]

/-! ### The mode transposes of `B_G` -/

theorem ghostB_Ppar_left (z y : Sl2GhostSpace) :
    bgPG (ghostIR (Ppar (ghostConj z))) y = ghostB (Ppar z) y := by
  rw [ghostB_apply, ghostConj_Ppar]

/-- The transpose constant of a creation mode. -/
def crConst (a : Fin 3) (p : ℕ × Fin 2) : ℂ :=
  ((modeCoef a p : ℝ) : ℂ) * (starRingEnd ℂ) (Complex.I ^ modeR (swapMode p)) *
    (nrm a (swapMode p) : ℂ)

/-- The transpose constant of an annihilation mode. -/
def anConst (a : Fin 3) (q : ℕ × Fin 2) : ℂ :=
  ((anCoef a q : ℝ) : ℂ) * (starRingEnd ℂ) (Complex.I ^ (-modeR (swapMode q))) *
    ((nrm a (swapMode q) : ℂ))⁻¹

/-- **The transpose of a creation mode under `B_G`.** -/
theorem ghostB_Cr (a : Fin 3) (p : ℕ × Fin 2) (z y : Sl2GhostSpace) :
    ghostB (Cr a p z) y = crConst a p * ghostB (Ppar z) (An a (swapMode p) y) := by
  rw [ghostB_apply, ghostConj_Cr, map_smul, ghostIR_Cr, SesqForm.smul_left, SesqForm.smul_left,
    bgPG_Cr_adj, ← ghostB_Ppar_left, Complex.conj_ofReal, crConst]
  ring

/-- **The transpose of an annihilation mode under `B_G`.** -/
theorem ghostB_An (a : Fin 3) (q : ℕ × Fin 2) (z y : Sl2GhostSpace) :
    ghostB (An a q z) y = anConst a q * ghostB (Ppar z) (Cr a (swapMode q) y) := by
  have hn : (nrm a (swapMode q) : ℂ) ≠ 0 := by
    exact_mod_cast (bgColourNorm_pos a (swapMode q)).ne'
  have hA : ∀ x y', bgPG (An a (swapMode q) x) y' =
      ((nrm a (swapMode q) : ℂ))⁻¹ * bgPG x (Cr a (swapMode q) y') := by
    intro x y'
    rw [← bgPG_An_adj, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  rw [ghostB_apply, ghostConj_An, map_smul, ghostIR_An, SesqForm.smul_left, SesqForm.smul_left,
    hA, ← ghostB_Ppar_left, Complex.conj_ofReal, anConst]
  ring

theorem modeCoef_mul_nrm_swap (a : Fin 3) {p : ℕ × Fin 2} (hp : p ≠ (0, 1)) :
    modeCoef a p * nrm a (swapMode p) = -1 := by
  obtain ⟨k, e⟩ := p
  have hw : colourW a ≠ 0 := (colourW_pos a).ne'
  fin_cases e
  · simp only [Fin.zero_eta, Fin.isValue] at hp ⊢
    simp only [swapMode, modeCoef, nrm, bgColourNorm, bgModeNorm, colourW, if_true]
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    split_ifs <;> simp_all <;> (try field_simp) <;> (try ring)
  · simp only [Fin.mk_one, Fin.isValue] at hp ⊢
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := by
      rcases k with _ | k
      · exact absurd rfl hp
      · exact ⟨k, rfl⟩
    simp only [swapMode, modeCoef, nrm, bgColourNorm, bgModeNorm, colourW]
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    split_ifs <;> simp_all <;> (try field_simp) <;> (try ring)

theorem modeR_swap_of_ne {p : ℕ × Fin 2} (hp : p ≠ (0, 1)) : modeR (swapMode p) = 1 := by
  unfold modeR
  rw [if_neg]
  intro h
  apply hp
  rw [← swapMode_swapMode p, h]
  rfl

/-- For a mode other than `c₀`, the creation transpose constant is `i`. -/
theorem crConst_eq_I (a : Fin 3) {p : ℕ × Fin 2} (hp : p ≠ (0, 1)) : crConst a p = Complex.I := by
  rw [crConst, modeR_swap_of_ne hp, zpow_one, Complex.conj_I]
  have h := modeCoef_mul_nrm_swap a hp
  have h' : ((modeCoef a p : ℝ) : ℂ) * (nrm a (swapMode p) : ℂ) = -1 := by exact_mod_cast h
  linear_combination (-Complex.I) * h'

/-- For a mode other than `c₀`, the annihilation transpose constant is `i`. -/
theorem anConst_eq_I (a : Fin 3) {q : ℕ × Fin 2} (hq : q ≠ (0, 1)) : anConst a q = Complex.I := by
  rw [anConst, modeR_swap_of_ne hq, zpow_neg, zpow_one, map_inv₀, Complex.conj_I, anCoef]
  have h := modeCoef_mul_nrm_swap a hq
  have hc : ((modeCoef a q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modeCoef_ne_zero a q
  have hn : (nrm a (swapMode q) : ℂ) ≠ 0 := by
    exact_mod_cast (bgColourNorm_pos a (swapMode q)).ne'
  have h' : ((modeCoef a q : ℝ) : ℂ) * (nrm a (swapMode q) : ℂ) = -1 := by exact_mod_cast h
  have hinv : ((modeCoef a q : ℝ) : ℂ)⁻¹ * ((nrm a (swapMode q) : ℂ))⁻¹ = -1 := by
    rw [← mul_inv, h']; norm_num
  rw [inv_neg, Complex.inv_I, neg_neg]
  push_cast
  linear_combination (-Complex.I) * hinv

/-! ### The transposes in mode language -/

/-- The transposed mode index: `b_m ↔ b_{-m}`, and for `c` (vertex-algebra mode index `m`,
conformal index `m + 1`) `m ↔ -m - 2`. -/
def trIdx (e : Fin 2) (m : ℤ) : ℤ := if e = 0 then -m else -m - 2

/-- The two zero modes `b_0` (`e = 0`, `m = 0`) and `c_0` (`e = 1`, `m = -1`). -/
def IsZeroMode (e : Fin 2) (m : ℤ) : Prop := (e = 0 ∧ m = 0) ∨ (e = 1 ∧ m = -1)

theorem gMode_eq_Cr0 {m : ℤ} (hm : m < 0) (a : Fin 3) :
    gMode a 0 m = Cr a ((-m - 1).toNat, 0) := by
  simp only [Cr]; congr 1; omega

theorem gMode_eq_An0 {m : ℤ} (hm : 0 ≤ m) (a : Fin 3) :
    gMode a 0 m = An a (m.toNat, 1) := by
  simp only [An]; congr 1; omega

theorem gMode_eq_Cr1 {m : ℤ} (hm : m < 0) (a : Fin 3) :
    gMode a 1 m = Cr a ((-m - 1).toNat, 1) := by
  simp only [Cr]; congr 1; omega

theorem gMode_eq_An1 {m : ℤ} (hm : 0 ≤ m) (a : Fin 3) :
    gMode a 1 m = An a (m.toNat, 0) := by
  simp only [An]; congr 1; omega

/-- **The mode transposes of `B_G`**: for every ghost mode other than `b_0`, `c_0`,
`B_G(X z, y) = i B_G(Ppar z, X' y)` with `X'` the transposed mode. -/
theorem ghostB_gMode (a : Fin 3) (e : Fin 2) (m : ℤ) (hm : ¬ IsZeroMode e m)
    (z y : Sl2GhostSpace) :
    ghostB (gMode a e m z) y = Complex.I * ghostB (Ppar z) (gMode a e (trIdx e m) y) := by
  unfold IsZeroMode at hm
  match e, hm with
  | 0, hm =>
    have hz : m ≠ 0 := fun h0 => hm (Or.inl ⟨rfl, h0⟩)
    rw [show trIdx 0 m = -m by simp [trIdx]]
    rcases lt_or_ge m 0 with h | h
    · have e1 : An a (swapMode ((-m - 1).toNat, 0)) = gMode a 0 (-m) := by
        rw [show swapMode ((-m - 1).toNat, 0) = ((-m - 1).toNat + 1, 1) by simp [swapMode]]
        simp only [An]; congr 1; push_cast; omega
      rw [gMode_eq_Cr0 h, ghostB_Cr, crConst_eq_I a (by simp), e1]
    · have h' : 0 < m := lt_of_le_of_ne h (Ne.symm hz)
      have e1 : Cr a (swapMode (m.toNat, 1)) = gMode a 0 (-m) := by
        rw [show swapMode (m.toNat, 1) = (m.toNat - 1, 0) by
          simp only [swapMode, Fin.isValue, one_ne_zero, if_false]; rw [if_neg (by omega)]]
        simp only [Cr]; congr 1; omega
      rw [gMode_eq_An0 h, ghostB_An, anConst_eq_I a (by simp; omega), e1]
  | 1, hm =>
    have hz : m ≠ -1 := fun h0 => hm (Or.inr ⟨rfl, h0⟩)
    rw [show trIdx 1 m = -m - 2 by simp [trIdx]]
    rcases lt_or_ge m 0 with h | h
    · have h' : m < -1 := lt_of_le_of_ne (by omega) hz
      have e1 : An a (swapMode ((-m - 1).toNat, 1)) = gMode a 1 (-m - 2) := by
        rw [show swapMode ((-m - 1).toNat, 1) = ((-m - 1).toNat - 1, 0) by
          simp only [swapMode, Fin.isValue, one_ne_zero, if_false]; rw [if_neg (by omega)]]
        simp only [An]; congr 1; omega
      rw [gMode_eq_Cr1 h, ghostB_Cr, crConst_eq_I a (by simp; omega), e1]
    · have e1 : Cr a (swapMode (m.toNat, 0)) = gMode a 1 (-m - 2) := by
        rw [show swapMode (m.toNat, 0) = (m.toNat + 1, 1) by simp [swapMode]]
        simp only [Cr]; congr 1; push_cast; omega
      rw [gMode_eq_An1 h, ghostB_An, anConst_eq_I a (by simp), e1]

theorem trIdx_trIdx (e : Fin 2) (m : ℤ) : trIdx e (trIdx e m) = m := by
  unfold trIdx; split_ifs <;> ring

theorem not_isZeroMode_trIdx {e : Fin 2} {m : ℤ} (hm : ¬ IsZeroMode e m) :
    ¬ IsZeroMode e (trIdx e m) := by
  unfold IsZeroMode trIdx at *
  fin_cases e <;> simp_all <;> omega

/-- The transpose in the second slot. -/
theorem ghostB_gMode_right (a : Fin 3) (e : Fin 2) (m : ℤ) (hm : ¬ IsZeroMode e m)
    (z y : Sl2GhostSpace) :
    ghostB z (gMode a e m y) = -Complex.I * ghostB (gMode a e (trIdx e m) (Ppar z)) y := by
  have h := ghostB_gMode a e (trIdx e m) (not_isZeroMode_trIdx hm) (Ppar z) y
  rw [trIdx_trIdx, Ppar_Ppar] at h
  rw [h, ← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

end

end VOA.ConcreteHodge
