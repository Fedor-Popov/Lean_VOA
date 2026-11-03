/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedGeneralVertex
import VOA.Moonshine.LatticeTwistedFields

/-! # Charge-parametric fields for even lattices
Adapted from `LatticeTwistedFields` using only `TwistedCharge` relations.
The existing generic oscillator and lattice-state results are reused. -/
namespace VOA.Moonshine.LatticeTwistedGeneral
open LatticeTwisted MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN
open IntegralLattice LatGen Extraspecial
open Module (End)
open scoped BigOperators TensorProduct

section Lattice

open IntegralLattice LatGen Extraspecial

variable (L : IntegralLattice) (hEven : L.Even) (C : TwistedCharge L)

abbrev MT : Type := FockT (rank L) ⊗[ℂ] Space L hEven C

theorem FgenTFld_eq_FgT (a : Fin (rank L)) : FgenTFld L hEven C a = FgT a := rfl

noncomputable def Fw (α : L.carrier) : List (ℕ × Fin (rank L)) → ℤ → Fld (MT L hEven C)
  | [], e => YTLFld L hEven C α e
  | (c :: l), e => star (1 / 2) (FgT c.2) (-(c.1 : ℤ) - 1) (Fw α l (e - 1))

@[simp] theorem Fw_nil (α : L.carrier) (e : ℤ) : Fw L hEven C α [] e = YTLFld L hEven C α e :=
  rfl

theorem Fw_cons (α : L.carrier) (c : ℕ × Fin (rank L)) (l : List (ℕ × Fin (rank L))) (e : ℤ) :
    Fw L hEven C α (c :: l) e = star (1 / 2) (FgT c.2) (-(c.1 : ℤ) - 1) (Fw L hEven C α l (e - 1)) :=
  rfl

theorem FgT_mem (a : Fin (rank L)) :
    FgT a ∈ TGenerated (latGenSet L hEven C) :=
  subset_tgenerated (Set.mem_union_left _ ⟨a, rfl⟩)

theorem YTLFld_mem (α : L.carrier) (e : ℤ) :
    YTLFld L hEven C α e ∈ TGenerated (latGenSet L hEven C) :=
  subset_tgenerated (Set.mem_union_right _ ⟨(α, e), rfl⟩)

variable (hPos : L.PosDef)
include hPos

theorem Fw_mem (α : L.carrier) (l : List (ℕ × Fin (rank L))) (e : ℤ) :
    Fw L hEven C α l e ∈ TGenerated (latGenSet L hEven C) := by
  induction l generalizing e with
  | nil => exact YTLFld_mem L hEven C α e
  | cons c l ih =>
      exact star_mem (latGenSet_local L hEven C hPos) (FgT_mem L hEven C c.2) (ih _) _ _

theorem tloc {X Y : Fld (MT L hEven C)} (hX : X ∈ TGenerated (latGenSet L hEven C))
    (hY : Y ∈ TGenerated (latGenSet L hEven C)) : Local X.1 Y.1 :=
  latticeTwistedSystem_local L hEven C hPos hX hY

omit hPos in
theorem YTLFld_add_two (α : L.carrier) (e : ℤ) :
    YTLFld L hEven C α (e + 2) = fzmul 1 (YTLFld L hEven C α e) :=
  Subtype.ext (resc_add_N (YTL L hEven C α) 2 e)

omit hPos in
theorem Fw_add_two (α : L.carrier) (l : List (ℕ × Fin (rank L))) (e : ℤ) :
    Fw L hEven C α l (e + 2) = fzmul 1 (Fw L hEven C α l e) := by
  induction l generalizing e with
  | nil => exact YTLFld_add_two L hEven C α e
  | cons c l ih =>
      rw [Fw_cons, Fw_cons, show e + 2 - 1 = (e - 1) + 2 by ring, ih, star_fzmul_right]

omit hPos in
theorem Fw_shift (α : L.carrier) (l : List (ℕ × Fin (rank L))) (e c : ℤ) :
    Fw L hEven C α l (e + 2 * c) = fzmul c (Fw L hEven C α l e) := by
  induction c using Int.induction_on with
  | zero => simp
  | succ c ih =>
      rw [show e + 2 * (c + 1) = (e + 2 * c) + 2 by ring, Fw_add_two, ih, fzmul_fzmul, add_comm]
  | pred c ih =>
      have h := Fw_add_two L hEven C α l (e + 2 * (-(c : ℤ) - 1))
      rw [show e + 2 * (-(c : ℤ) - 1) + 2 = e + 2 * (-(c : ℤ)) by ring, ih] at h
      have h' := congrArg (fzmul (-1)) h
      rw [fzmul_fzmul, fzmul_fzmul, show (-1 : ℤ) + 1 = 0 by norm_num, fzmul_zero_shift] at h'
      rw [← h', show (-1 : ℤ) + -(c : ℤ) = -(c : ℤ) - 1 by ring]

theorem star_gT_swap (c c' : ℕ × Fin (rank L)) {F : Fld (MT L hEven C)}
    (hF : F ∈ TGenerated (latGenSet L hEven C)) :
    star (1 / 2) (FgT c.2) (-(c.1 : ℤ) - 1) (star (1 / 2) (FgT c'.2) (-(c'.1 : ℤ) - 1) F)
      = star (1 / 2) (FgT c'.2) (-(c'.1 : ℤ) - 1)
          (star (1 / 2) (FgT c.2) (-(c.1 : ℤ) - 1) F) := by
  have h := star_comm (latGenSet_local L hEven C hPos) (FgT_mem L hEven C c.2)
    (FgT_mem L hEven C c'.2) hF (1 / 2) (1 / 2)
    (-(c.1 : ℤ) - 1) (-(c'.1 : ℤ) - 1) 2 (fun s hs => prod_FgT_two_le _ _ (by omega))
  rw [Finset.sum_range_succ, Finset.sum_range_one, star_gT_gen, star_gT_gen, if_neg (by norm_num),
    if_pos (by norm_num), star_zero_left, smul_zero, zero_add,
    star_smul_left (local_fzmul_one_left 1 F),
    show (1 / 2 : ℂ) + 1 / 2 = ((1 : ℤ) : ℂ) by norm_num, star_fzmul_one,
    if_neg (show -(c.1 : ℤ) - 1 + (-(c'.1 : ℤ) - 1) - ((1 : ℕ) : ℤ) ≠ -1 by push_cast; omega),
    smul_zero, smul_zero] at h
  exact sub_eq_zero.mp h

theorem Fw_perm (α : L.carrier) {l l' : List (ℕ × Fin (rank L))} (h : l.Perm l') (e : ℤ) :
    Fw L hEven C α l e = Fw L hEven C α l' e := by
  induction h generalizing e with
  | nil => rfl
  | cons x _ ih => rw [Fw_cons, Fw_cons, ih]
  | swap x y l =>
      rw [Fw_cons, Fw_cons, Fw_cons, Fw_cons, star_gT_swap L hEven C hPos y x
        (Fw_mem L hEven C hPos α l _)]
  | trans _ _ ih₁ ih₂ => exact (ih₁ e).trans (ih₂ e)

omit hPos in
theorem YTLFld_neg (α : L.carrier) (e : ℤ) :
    YTLFld L hEven C (-α) e = ((-1 : ℂ) ^ e) • YTLFld L hEven C α e := by
  apply fld_ext_mode
  intro p x
  change mode (resc (YTL L hEven C (-α)) 2 e) p x = mode ((-1 : ℂ) ^ e • resc (YTL L hEven C α) 2 e) p x
  rw [mode_resc, mode_smul, mode_resc, YTL_neg, neg_one_zpow_congr (b := e) (by omega)]

theorem Fw_neg (α : L.carrier) (l : List (ℕ × Fin (rank L))) (e : ℤ) :
    Fw L hEven C (-α) l e = ((-1 : ℂ) ^ (e + l.length)) • Fw L hEven C α l e := by
  induction l generalizing e with
  | nil => rw [Fw_nil, Fw_nil, YTLFld_neg, List.length_nil, Nat.cast_zero, add_zero]
  | cons c l ih =>
      rw [Fw_cons, Fw_cons, ih, star_smul_right (tloc L hEven C hPos (FgT_mem L hEven C c.2)
        (Fw_mem L hEven C hPos α l _)), List.length_cons]
      congr 1
      exact neg_one_zpow_congr (by push_cast; omega)

noncomputable def FLB (e : ℤ) :
    FockN (rank L) →ₗ[ℂ] (L.carrier →₀ ℂ) →ₗ[ℂ] Fld (MT L hEven C) :=
  Finsupp.linearCombination ℂ (fun m : (ℕ × Fin (rank L)) →₀ ℕ =>
    Finsupp.linearCombination ℂ (fun α : L.carrier => Fw L hEven C α (monoWordN m) e))

noncomputable def FL (e : ℤ) : LatModuleGen L →ₗ[ℂ] Fld (MT L hEven C) :=
  TensorProduct.lift (FLB L hEven C e)

omit hPos in
theorem FL_monomial (e : ℤ) (m : (ℕ × Fin (rank L)) →₀ ℕ) (a : ℂ) (α : L.carrier) (c : ℂ) :
    FL L hEven C e (monomial m a ⊗ₜ[ℂ] Finsupp.single α c)
      = (a * c) • Fw L hEven C α (monoWordN m) e := by
  rw [FL, TensorProduct.lift.tmul]
  have h1 : FLB L hEven C e (monomial m a)
      = a • Finsupp.linearCombination ℂ (fun α : L.carrier => Fw L hEven C α (monoWordN m) e) :=
    Finsupp.linearCombination_single ℂ a m
  rw [h1, LinearMap.smul_apply, Finsupp.linearCombination_single, smul_smul]

omit hPos in
theorem FL_monomial_eGen (e : ℤ) (m : (ℕ × Fin (rank L)) →₀ ℕ) (α : L.carrier) :
    FL L hEven C e (monomial m 1 ⊗ₜ[ℂ] eGen L α) = Fw L hEven C α (monoWordN m) e := by
  rw [eGen, FL_monomial, one_mul, one_smul]

omit hEven C hPos in
theorem wordStateN_perm {l l' : List (ℕ × Fin (rank L))} (h : l.Perm l') :
    wordStateN l = wordStateN l' := by
  rw [wordStateN, wordStateN]
  exact (h.map _).prod_eq

theorem FL_wordState (e : ℤ) (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    FL L hEven C e (wordStateN l ⊗ₜ[ℂ] eGen L α) = Fw L hEven C α l e := by
  set m : (ℕ × Fin (rank L)) →₀ ℕ := Multiset.toFinsupp (l : Multiset (ℕ × Fin (rank L)))
  have hp : (monoWordN m).Perm l := by
    rw [← Multiset.coe_eq_coe, Moonshine.coe_monoWordN, Multiset.toFinsupp_toMultiset]
  rw [← wordStateN_perm L hp, wordStateN_monoWordN, FL_monomial_eGen, Fw_perm L hEven C hPos α hp]

theorem FL_mem (e : ℤ) (u : LatModuleGen L) :
    FL L hEven C e u ∈ TGenerated (latGenSet L hEven C) := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem_tgenerated _
  | add x y hx hy => rw [map_add]; exact add_mem_tgenerated hx hy
  | tmul p g =>
      induction p using MvPolynomial.induction_on' with
      | monomial m a =>
          induction g using Finsupp.induction_linear with
          | zero => rw [TensorProduct.tmul_zero, map_zero]; exact zero_mem_tgenerated _
          | add g₁ g₂ h₁ h₂ =>
              rw [TensorProduct.tmul_add, map_add]; exact add_mem_tgenerated h₁ h₂
          | single α c =>
              rw [FL_monomial]
              exact smul_mem_tgenerated _ (Fw_mem L hEven C hPos α _ e)
      | add p q hp hq => rw [TensorProduct.add_tmul, map_add]; exact add_mem_tgenerated hp hq

theorem FL_local (e e' : ℤ) (u v : LatModuleGen L) :
    Local (FL L hEven C e u).1 (FL L hEven C e' v).1 :=
  tloc L hEven C hPos (FL_mem L hEven C hPos e u) (FL_mem L hEven C hPos e' v)

theorem FL_mul_X (e : ℤ) (c : ℕ × Fin (rank L)) (p : FockN (rank L)) (g : L.carrier →₀ ℂ) :
    FL L hEven C (e + 1) ((X c * p) ⊗ₜ[ℂ] g)
      = star (1 / 2) (FgT c.2) (-(c.1 : ℤ) - 1) (FL L hEven C e (p ⊗ₜ[ℂ] g)) := by
  have hl : ∀ u : LatModuleGen L, Local (FgT (Tm := Space L hEven C)
      c.2).1 (FL L hEven C e u).1 := fun u =>
    tloc L hEven C hPos (FgT_mem L hEven C c.2) (FL_mem L hEven C hPos e u)
  induction p using MvPolynomial.induction_on' with
  | monomial m a =>
      rw [Moonshine.X_mul_monomial']
      induction g using Finsupp.induction_linear with
      | zero => rw [TensorProduct.tmul_zero, TensorProduct.tmul_zero, map_zero, map_zero,
          star_zero_right]
      | add g₁ g₂ h₁ h₂ =>
          rw [TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, map_add, h₁, h₂,
            star_add_right (hl _) (hl _)]
      | single α d =>
          rw [FL_monomial, FL_monomial, star_smul_right (tloc L hEven C hPos
              (FgT_mem L hEven C c.2) (Fw_mem L hEven C hPos α _ e)),
            Fw_perm L hEven C hPos α (Moonshine.monoWordN_add_single_perm _ m c), Fw_cons,
            add_sub_cancel_right]
  | add p q hp hq =>
      rw [mul_add, TensorProduct.add_tmul, TensorProduct.add_tmul, map_add, map_add, hp, hq,
        star_add_right (hl _) (hl _)]

theorem FL_mulLeft (e : ℤ) (c : ℕ × Fin (rank L)) (w : LatModuleGen L) :
    FL L hEven C (e + 1) ((LinearMap.mulLeft ℂ (X c : FockN (rank L))).rTensor _ w)
      = star (1 / 2) (FgT c.2) (-(c.1 : ℤ) - 1) (FL L hEven C e w) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, star_zero_right]
  | tmul p g => rw [LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, FL_mul_X L hEven C hPos]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add, star_add_right
        (tloc L hEven C hPos (FgT_mem L hEven C c.2) (FL_mem L hEven C hPos e x))
        (tloc L hEven C hPos (FgT_mem L hEven C c.2) (FL_mem L hEven C hPos e y))]

omit hPos in
theorem FL_shift (e c : ℤ) (u : LatModuleGen L) :
    FL L hEven C (e + 2 * c) u = fzmul c (FL L hEven C e u) := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, fzmul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, fzmul_add]
  | tmul p g =>
      induction p using MvPolynomial.induction_on' with
      | monomial m a =>
          induction g using Finsupp.induction_linear with
          | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, fzmul_zero]
          | add g₁ g₂ h₁ h₂ =>
              rw [TensorProduct.tmul_add, map_add, map_add, h₁, h₂, fzmul_add]
          | single α d => rw [FL_monomial, FL_monomial, Fw_shift, fzmul_smul]
      | add p q hp hq => rw [TensorProduct.add_tmul, map_add, map_add, hp, hq, fzmul_add]

theorem FL_theta (e : ℤ) (u : LatModuleGen L) :
    FL L hEven C e (thetaLat L u) = ((-1 : ℂ) ^ e) • FL L hEven C e u := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]
  | tmul p g =>
      induction p using MvPolynomial.induction_on' with
      | monomial m a =>
          induction g using Finsupp.induction_linear with
          | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, smul_zero]
          | add g₁ g₂ h₁ h₂ =>
              rw [TensorProduct.tmul_add, map_add, map_add, h₁, h₂, map_add, smul_add]
          | single α d =>
              have hs : (monomial m a : FockN (rank L)) ⊗ₜ[ℂ] Finsupp.single α d
                  = (a * d) • ((monomial m 1 : FockN (rank L)) ⊗ₜ[ℂ] eGen L α) := by
                rw [eGen, show (monomial m a : FockN (rank L)) = a • monomial m 1 by
                    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
                  show (Finsupp.single α d : L.carrier →₀ ℂ) = d • Finsupp.single α 1 by
                    rw [Finsupp.smul_single_one],
                  TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul, mul_comm d a]
              rw [hs, map_smul, map_smul, map_smul, thetaLat_tmul, Moonshine.sigmaN_monomial_length,
                ← TensorProduct.smul_tmul', map_smul, FL_monomial_eGen, FL_monomial_eGen,
                Fw_neg L hEven C hPos, smul_smul, smul_smul, smul_comm ((-1 : ℂ) ^ e), smul_smul]
              have hpow : ((-1 : ℂ) ^ (monoWordN m).length) * ((-1 : ℂ) ^ (monoWordN m).length)
                  = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
              congr 1
              rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast]
              linear_combination (a * d * (-1 : ℂ) ^ e) * hpow
      | add p q hp hq =>
          rw [TensorProduct.add_tmul, map_add, map_add, hp, hq, map_add, smul_add]

noncomputable def YML : LatModuleGen L →ₗ[ℂ] (ℤ → End ℂ (MT L hEven C)) :=
  LinearMap.pi (fun k => (modeL 0).comp (FL L hEven C k))

omit hPos in
theorem YML_apply (u : LatModuleGen L) (k : ℤ) : YML L hEven C u k = mode (FL L hEven C k u).1 0 :=
  rfl

omit hPos in
theorem resc_YML (u : LatModuleGen L) (e : ℤ) : resc (YML L hEven C u) 2 e = (FL L hEven C e u).1 := by
  funext n
  rw [resc, YML_apply, show ((2 : ℕ) : ℤ) * (-n - 1) + e = e + 2 * (-n - 1) by push_cast; ring,
    FL_shift, fzmul_val, mode_zmul, zero_add, mode_apply, show -(-n - 1) - 1 = n by ring]

omit hPos in
theorem YML_eq_mode (u : LatModuleGen L) (e p : ℤ) :
    YML L hEven C u (2 * p + e) = mode (FL L hEven C e u).1 p := by
  have h := mode_resc (YML L hEven C u) 2 e p
  push_cast at h
  rw [← h, resc_YML]

omit hPos in
theorem YML_truncation (u : LatModuleGen L) (x : MT L hEven C) :
    ∃ K : ℤ, ∀ k : ℤ, K ≤ k → YML L hEven C u k x = 0 := by
  obtain ⟨B0, h0⟩ := (FL L hEven C 0 u).2 x
  obtain ⟨B1, h1⟩ := (FL L hEven C 1 u).2 x
  refine ⟨2 * (B0.natAbs + B1.natAbs) + 2, fun k hk => ?_⟩
  obtain ⟨q, e, he, rfl⟩ : ∃ q e : ℤ, (e = 0 ∨ e = 1) ∧ k = 2 * q + e :=
    ⟨k / 2, k % 2, by omega, by omega⟩
  rw [YML_eq_mode, mode_apply]
  rcases he with rfl | rfl
  · exact h0 _ (by omega)
  · exact h1 _ (by omega)

omit hPos in
theorem YML_vacuum (k : ℤ) :
    YML L hEven C (latVacuumGen L) k = if k = -2 then 1 else 0 := by
  rw [YML_apply, latVacuumGen, latStateGen, show (vacuumN (rank L)) = monomial 0 1 by
      rw [vacuumN, monomial_zero', map_one],
    FL_monomial_eGen, monoWordN_zero, Fw_nil]
  change mode (resc (YTL L hEven C 0) 2 k) 0 = _
  rw [mode_resc, mul_zero, zero_add, YTL_zero]

theorem YML_support (j : ℕ) (u : LatModuleGen L)
    (hu : u ∈ (thetaAut L hEven hPos).twistedEigenspace 2 j) (k : ℤ)
    (hk : (k + j) % ((2 : ℕ) : ℤ) ≠ 0) : YML L hEven C u k = 0 := by
  rw [Aut.twistedEigenspace, Module.End.mem_eigenspace_iff, HeisenbergN.exp_twisted_two] at hu
  have hu' : thetaLat L u = ((-1 : ℂ) ^ j) • u := hu
  have h := FL_theta L hEven C hPos k u
  rw [hu', map_smul] at h
  have hsign : ((-1 : ℂ) ^ j) = -((-1 : ℂ) ^ k) := by
    rw [← zpow_natCast, neg_one_zpow_congr (b := k + 1) (by push_cast at hk ⊢; omega),
      zpow_add₀ (by norm_num), zpow_one, mul_neg_one]
  rw [hsign, neg_smul] at h
  have h2 : (2 * (-1 : ℂ) ^ k) • FL L hEven C k u = 0 := by
    rw [mul_smul, two_smul, ← sub_eq_zero.mpr h.symm]
    abel
  have hne : (2 * (-1 : ℂ) ^ k) ≠ 0 := mul_ne_zero two_ne_zero (zpow_ne_zero _ (by norm_num))
  rw [YML_apply, (smul_eq_zero.mp h2).resolve_left hne]
  rfl

theorem YML_local (u v : LatModuleGen L) (e e' : ℤ) :
    Local (resc (YML L hEven C u) 2 e) (resc (YML L hEven C v) 2 e') := by
  rw [resc_YML, resc_YML]
  exact FL_local L hEven C hPos e e' u v

end Lattice

end VOA.Moonshine.LatticeTwistedGeneral
