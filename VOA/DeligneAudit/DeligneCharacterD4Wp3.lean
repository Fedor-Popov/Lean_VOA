/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Wp2

/-!
# The cubic theta identity (layer 3)

With `Π(u) = ∏_{m ≥ 1}(1 - u q^m)(1 - u⁻¹q^m)(1 - q^m)`, `Ψ = (1-a)Π(a)` (Jacobi),
`Ψ₋ = (1+a)Π(-a)`, `E = ∏_{k ≥ 0}(1 - a²q^{2k+1})(1 - a⁻²q^{2k+1})`, `η = ∏(1 - q^m)`:

  **`η · C₃(Ψ) = J³ · a · Ψ₋ · E`**,  `J = (DΨ)(1) = -η³`,

where `C₃(F) = F²D³F - 3F·DF·D²F + 2(DF)³` and `D = a d/da`.  This is `℘'(z) = -σ(2z)/σ(z)⁴` in
theta form.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4Wp

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

/-- `D = a d/da` on `L⟦q⟧`. -/
abbrev Da : PowerSeries L → PowerSeries L := DQ wa

/-- The third cumulant `C₃(F) = F²D³F - 3F·DF·D²F + 2(DF)³`. -/
def C3 (F : PowerSeries L) : PowerSeries L :=
  F ^ 2 * Da (Da (Da F)) - 3 * F * Da F * Da (Da F) + 2 * Da F ^ 3

/-- `J = (DΨ)(1)`. -/
def Jc : PowerSeries L := PowerSeries.map ev1L (Da Psi)

theorem DQ_three {G : Type*} [AddCommGroup G] (w : G →+ ℤ) :
    DQ w (3 : PowerSeries (AddMonoidAlgebra ℚ G)) = 0 := by
  rw [show (3 : PowerSeries (AddMonoidAlgebra ℚ G)) = 2 + 1 by norm_num, DQ_add, DQ_two, DQ_one,
    add_zero]

/-- `-2ΨC₃(Ψ) = -κ a Ψ(a²) J`. -/
theorem two_Psi_C3 :
    2 * Psi * C3 Psi = kap * (PowerSeries.C (mono 1) * (PowerSeries.map (embL dbl) Psi * Jc)) := by
  have h := diag_identity
  rw [Gser] at h
  simp only [DQ_mul, DQ_sub, DQ_two] at h
  rw [C3, Jc]
  linear_combination -h

/-! ## Products -/

theorem pf_sub (c : L) (e : ℕ → ℕ) (he : ∀ k, k < e k) :
    ProdFactors fun k => (1 : PowerSeries L) - PowerSeries.C c * X ^ e k := by
  have h := prodFactors_one_add (-c) e he
  simpa [sub_eq_add_neg, map_neg] using h

/-- `η = ∏(1 - qᵐ)`. -/
def eta : PowerSeries L := infProd fun k => 1 - X ^ (k + 1)
/-- `Π(a)`. -/
def PiA : PowerSeries L := infProd (tripleFactor ua)
/-- `Π(-a)`. -/
def PiM : PowerSeries L := infProd (tripleFactor (-ua))
/-- `Ψ(-a) = (1 + a)Π(-a)`. -/
def Psim : PowerSeries L := (1 + PowerSeries.C (mono 1)) * PiM

def Thf (k : ℕ) : PowerSeries L :=
  (1 - PowerSeries.C (mono 2) * X ^ (2 * k + 2)) * (1 - PowerSeries.C (mono (-2)) * X ^ (2 * k + 2))
def Ef (k : ℕ) : PowerSeries L :=
  (1 - PowerSeries.C (mono 2) * X ^ (2 * k + 1)) * (1 - PowerSeries.C (mono (-2)) * X ^ (2 * k + 1))
def sqf (k : ℕ) : PowerSeries L :=
  (1 - PowerSeries.C (mono 2) * X ^ (k + 1)) * (1 - PowerSeries.C (mono (-2)) * X ^ (k + 1))

/-- `E = ∏(1 - a²q^{2k+1})(1 - a⁻²q^{2k+1})`. -/
def Ep : PowerSeries L := infProd Ef
def Vp : PowerSeries L := infProd sqf

theorem pf_eta : ProdFactors fun k => (1 : PowerSeries L) - X ^ (k + 1) := by
  have h := pf_sub 1 (fun k => k + 1) (fun k => Nat.lt_succ_self k)
  simpa using h
theorem pf_Thf : ProdFactors Thf :=
  (pf_sub _ (fun k => 2 * k + 2) (fun k => by dsimp only; omega)).mul (pf_sub _ (fun k => 2 * k + 2) (fun k => by dsimp only; omega))
theorem pf_Ef : ProdFactors Ef :=
  (pf_sub _ (fun k => 2 * k + 1) (fun k => by dsimp only; omega)).mul (pf_sub _ (fun k => 2 * k + 1) (fun k => by dsimp only; omega))
theorem pf_sqf : ProdFactors sqf :=
  (pf_sub _ (fun k => k + 1) (fun k => by dsimp only; omega)).mul (pf_sub _ (fun k => k + 1) (fun k => by dsimp only; omega))

theorem val_ua : ((ua : Lˣ) : L) = mono 1 := rfl
theorem val_ua_inv : ((ua⁻¹ : Lˣ) : L) = mono (-1) := rfl
theorem val_neg_ua : ((-ua : Lˣ) : L) = -mono 1 := rfl
theorem val_neg_ua_inv : (((-ua)⁻¹ : Lˣ) : L) = -mono (-1) := by
  rw [inv_neg, Units.val_neg]; rfl

theorem Cm_sq : PowerSeries.C (mono 1) * PowerSeries.C (mono 1) = (PowerSeries.C (mono 2) : PowerSeries L) := by
  rw [← map_mul, mono_mul]; norm_num
theorem Cmi_sq :
    PowerSeries.C (mono (-1)) * PowerSeries.C (mono (-1)) = (PowerSeries.C (mono (-2)) : PowerSeries L) := by
  rw [← map_mul, mono_mul]; norm_num

theorem triple_mul_triple (k : ℕ) :
    tripleFactor ua k * tripleFactor (-ua) k = Thf k * (1 - X ^ (k + 1)) ^ 2 := by
  rw [tripleFactor, tripleFactor, Thf, val_ua, val_ua_inv, val_neg_ua, val_neg_ua_inv, map_neg, map_neg,
    ← Cm_sq, ← Cmi_sq]
  ring

theorem PiA_mul_PiM : PiA * PiM = infProd Thf * eta ^ 2 := by
  rw [PiA, PiM, infProd_mul (prodFactors_tripleFactor ua) (prodFactors_tripleFactor (-ua)),
    infProd_congr triple_mul_triple, eta, infProd_pow pf_eta, infProd_mul pf_Thf (pf_eta.pow 2)]

theorem Vp_eq : Vp = Ep * infProd Thf := by
  rw [Vp, ← infProd_pairs pf_sqf, Ep, infProd_mul pf_Ef pf_Thf]
  refine infProd_congr fun k => ?_
  rw [sqf, sqf, Ef, Thf, show 2 * k + 1 + 1 = 2 * k + 2 by ring]

theorem hX_map (φ : L →+* L) : ∀ K, (X : PowerSeries L) ^ K ∣ PowerSeries.map φ (X ^ K) := by
  intro K; rw [map_pow, PowerSeries.map_X]

theorem map_dbl_PiA : PowerSeries.map (embL dbl) PiA = Vp * eta := by
  rw [PiA, map_infProd (PowerSeries.map (embL dbl)) (hX_map _) (prodFactors_tripleFactor ua),
    Vp, eta, infProd_mul pf_sqf pf_eta]
  refine infProd_congr fun k => ?_
  rw [tripleFactor, sqf, val_ua, val_ua_inv]
  simp only [map_mul, map_sub, map_one, PowerSeries.map_C, map_pow, PowerSeries.map_X, embL_mono]
  rfl

theorem map_dbl_Psi : PowerSeries.map (embL dbl) Psi = (1 - PowerSeries.C (mono 2)) * (Vp * eta) := by
  rw [← Psi_eq_prod, map_mul, map_sub, map_one, PowerSeries.map_C, embL_mono, ← PiA, map_dbl_PiA]
  rfl

/-- **Duplication**: `Ψ(a)Ψ(-a)E(a) = η Ψ(a²)`. -/
theorem Psi_Psim_Ep : Psi * Psim * Ep = eta * PowerSeries.map (embL dbl) Psi := by
  rw [map_dbl_Psi, ← Psi_eq_prod, Psim, ← PiA]
  have h1 : (1 - PowerSeries.C (mono 1)) * PiA * ((1 + PowerSeries.C (mono 1)) * PiM) * Ep =
      (1 - PowerSeries.C (mono 1) * PowerSeries.C (mono 1)) * (PiA * PiM) * Ep := by ring
  rw [h1, Cm_sq, PiA_mul_PiM, Vp_eq]
  ring

/-! ## Cancelling `Ψ` -/

theorem Psi_ne_zero : Psi ≠ 0 := by
  intro h
  rw [← Psi_eq_prod] at h
  have hu : IsUnit PiA := isUnit_infProd _
  rw [← PiA] at h
  have h1 : (1 - PowerSeries.C (mono 1) : PowerSeries L) = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h hu.ne_zero
  have h2 := congrArg (fun F => (PowerSeries.constantCoeff F) (0 : ℤ)) h1
  simp only [map_sub, map_one, PowerSeries.constantCoeff_C] at h2
  rw [mono] at h2
  change (1 : L) 0 - (AddMonoidAlgebra.single (1 : ℤ) (1 : ℚ)) 0 = (0 : L) 0 at h2
  rw [show (1 : L) = AddMonoidAlgebra.single 0 1 from rfl, Finsupp.single_apply, Finsupp.single_apply,
    if_pos rfl, if_neg (by norm_num)] at h2
  have h3 : (1 : ℚ) - 0 = 0 := h2
  norm_num at h3

/-- `2ηC₃(Ψ) = κ a J Ψ₋ E`. -/
theorem two_eta_C3 :
    2 * eta * C3 Psi = kap * PowerSeries.C (mono 1) * Jc * Psim * Ep := by
  have h := two_Psi_C3
  have key : Psi * (2 * eta * C3 Psi - kap * PowerSeries.C (mono 1) * Jc * Psim * Ep) = 0 := by
    have hd := Psi_Psim_Ep
    linear_combination eta * h - kap * PowerSeries.C (mono 1) * Jc * hd
  rcases mul_eq_zero.mp key with h0 | h0
  · exact absurd h0 Psi_ne_zero
  · exact sub_eq_zero.mp h0

/-! ## Evaluation at `a = 1` -/

theorem ev_ev (x : L) : ev1L (ev1L x) = ev1L x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single j c =>
      simp only [ev1L, embL, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
        AddMonoidHom.zero_apply]

theorem map_ev_ev (F : PowerSeries L) :
    PowerSeries.map ev1L (PowerSeries.map ev1L F) = PowerSeries.map ev1L F := by
  ext n : 1; simp [ev_ev]

theorem ev_cst (c : ℚ) : ev1L (cst c) = cst c := by
  simp only [cst_apply, ev1L, embL, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomain_single, AddMonoidHom.zero_apply]

theorem ev_kap : PowerSeries.map ev1L kap = kap := by
  rw [kap, phi0, psi1, phi1, psi0]
  simp only [map_sub, map_mul, lat_map, map_one, ev_cst]

theorem ev_mono (j : ℤ) : ev1L (mono j) = 1 := by
  rw [embL_mono]; rfl

theorem ev_eta : PowerSeries.map ev1L eta = eta := by
  rw [eta, map_infProd _ (hX_map _) pf_eta]
  exact infProd_congr fun k => by simp

theorem pf_plus : ProdFactors fun k => (1 : PowerSeries L) + X ^ (k + 1) := by
  have h := prodFactors_one_add (R := L) 1 (fun k => k + 1) (fun k => Nat.lt_succ_self k)
  simpa using h

/-- `∏(1 + qᵐ)² (1 - qᵐ)`. -/
def Pm : PowerSeries L := infProd fun k => (1 + X ^ (k + 1)) ^ 2 * (1 - X ^ (k + 1))
/-- `∏(1 - q^{2k+1})²`. -/
def Eodd : PowerSeries L := infProd fun k => (1 - X ^ (2 * k + 1)) ^ 2

theorem pf_odd : ProdFactors fun k => (1 : PowerSeries L) - X ^ (2 * k + 1) := by
  have h := pf_sub 1 (fun k => 2 * k + 1) (fun k => by dsimp only; omega)
  simpa using h

theorem pf_even : ProdFactors fun k => (1 : PowerSeries L) - X ^ (2 * k + 2) := by
  have h := pf_sub 1 (fun k => 2 * k + 2) (fun k => by dsimp only; omega)
  simpa using h

/-- **Euler**: `(-q;q)_∞ (q;q²)_∞ = 1`. -/
theorem euler_odd :
    infProd (fun k => (1 : PowerSeries L) + X ^ (k + 1)) * infProd (fun k => 1 - X ^ (2 * k + 1)) = 1 := by
  have h1 : infProd (fun k => (1 : PowerSeries L) + X ^ (k + 1)) * eta =
      infProd fun k => 1 - X ^ (2 * k + 2) := by
    rw [eta, infProd_mul pf_plus pf_eta]
    exact infProd_congr fun k => by ring
  have h2 : eta = infProd (fun k => (1 : PowerSeries L) - X ^ (2 * k + 1)) *
      infProd fun k => 1 - X ^ (2 * k + 2) := by
    rw [eta, ← infProd_pairs pf_eta, infProd_mul pf_odd pf_even]
  have hu : IsUnit (infProd fun k => (1 : PowerSeries L) - X ^ (2 * k + 2)) := isUnit_infProd _
  rw [h2] at h1
  apply hu.mul_left_cancel
  linear_combination h1

theorem Pm_Eodd : Pm * Eodd = eta := by
  have he := euler_odd
  have hPm : Pm = infProd (fun k => (1 : PowerSeries L) + X ^ (k + 1)) ^ 2 * eta := by
    rw [Pm, eta, infProd_pow pf_plus, infProd_mul (pf_plus.pow 2) pf_eta]
  have hE : Eodd = infProd (fun k => (1 : PowerSeries L) - X ^ (2 * k + 1)) ^ 2 := by
    rw [Eodd, infProd_pow pf_odd]
  rw [hPm, hE]
  linear_combination (infProd (fun k => (1 : PowerSeries L) + X ^ (k + 1)) *
    infProd (fun k => (1 : PowerSeries L) - X ^ (2 * k + 1)) + 1) * eta * he

theorem ev_C_mono (j : ℤ) : PowerSeries.map ev1L (PowerSeries.C (mono j)) = 1 := by
  rw [PowerSeries.map_C, ev_mono, map_one]

theorem ev_PiA : PowerSeries.map ev1L PiA = eta ^ 3 := by
  rw [PiA, map_infProd _ (hX_map _) (prodFactors_tripleFactor ua), eta, infProd_pow pf_eta]
  refine infProd_congr fun k => ?_
  rw [tripleFactor, val_ua, val_ua_inv]
  simp only [map_mul, map_sub, map_one, PowerSeries.map_C, map_pow, PowerSeries.map_X, ev_mono]
  ring

theorem ev_PiM : PowerSeries.map ev1L PiM = Pm := by
  rw [PiM, map_infProd _ (hX_map _) (prodFactors_tripleFactor (-ua)), Pm]
  refine infProd_congr fun k => ?_
  rw [tripleFactor, val_neg_ua, val_neg_ua_inv]
  simp only [map_mul, map_sub, map_one, map_neg, PowerSeries.map_C, map_pow, PowerSeries.map_X, ev_mono]
  ring

theorem ev_Psim : PowerSeries.map ev1L Psim = 2 * Pm := by
  rw [Psim, map_mul, map_add, map_one, ev_C_mono, ev_PiM]; ring

theorem ev_Ep : PowerSeries.map ev1L Ep = Eodd := by
  rw [Ep, map_infProd _ (hX_map _) pf_Ef, Eodd]
  refine infProd_congr fun k => ?_
  rw [Ef]
  simp only [map_mul, map_sub, map_one, PowerSeries.map_C, map_pow, PowerSeries.map_X, ev_mono]
  ring

theorem DQ_C {G : Type*} [AddCommGroup G] (w : G →+ ℤ) (c : AddMonoidAlgebra ℚ G) :
    DQ w (PowerSeries.C c) = PowerSeries.C (wd w c) := by
  ext n : 1
  rw [coeff_DQ, coeff_C, coeff_C]
  split_ifs
  · rfl
  · exact wd_zero w

theorem Jc_eq : Jc = -eta ^ 3 := by
  rw [Jc, ← Psi_eq_prod, Da, DQ_mul, DQ_sub, DQ_one, DQ_C, wd_mono, ← PiA, Int.cast_one, map_one, one_mul]
  have e1 : PowerSeries.map ev1L (PowerSeries.C (mono 1)) = 1 := ev_C_mono 1
  simp only [map_add, map_mul, map_sub, zero_sub, map_neg, map_one, e1, ev_PiA, sub_self, zero_mul,
    add_zero]
  ring

theorem ev_C3 : PowerSeries.map ev1L (C3 Psi) = 2 * Jc ^ 3 := by
  rw [C3]
  simp only [map_add, map_sub, map_mul, map_pow, ev_Psi, map_ofNat]
  rw [← Jc]
  ring

theorem two_ne_zero_PS : (2 : PowerSeries L) ≠ 0 := by
  intro h
  have h1 := congrArg PowerSeries.constantCoeff h
  rw [map_ofNat, map_zero, ← map_ofNat cst 2] at h1
  exact two_ne_zero ((map_eq_zero_iff cst cst.injective).mp h1)

/-- `κJ = 2J³`. -/
theorem kap_Jc : kap * Jc = 2 * Jc ^ 3 := by
  have h := congrArg (PowerSeries.map ev1L) two_eta_C3
  simp only [map_mul, map_ofNat, ev_eta, ev_C3, ev_kap, ev_C_mono, ev_Psim, ev_Ep] at h
  rw [show PowerSeries.map ev1L Jc = Jc from map_ev_ev _] at h
  have hPE := Pm_Eodd
  have hu : IsUnit eta := isUnit_infProd _
  have key : eta * (2 * (2 * Jc ^ 3 - kap * Jc)) = 0 := by
    linear_combination h + 2 * kap * Jc * hPE
  rcases mul_eq_zero.mp key with h0 | h0
  · exact absurd h0 hu.ne_zero
  · rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 two_ne_zero_PS
    · linear_combination -h1

/-- **The cubic theta identity** (`℘' = -σ(2z)/σ⁴`): `η·C₃(Ψ) = J³·a·Ψ(-a)·E(a)`. -/
theorem eta_C3 : eta * C3 Psi = Jc ^ 3 * PowerSeries.C (mono 1) * Psim * Ep := by
  have h := two_eta_C3
  have hk := kap_Jc
  have key : (2 : PowerSeries L) * (eta * C3 Psi - Jc ^ 3 * PowerSeries.C (mono 1) * Psim * Ep) = 0 := by
    linear_combination h + PowerSeries.C (mono 1) * Psim * Ep * hk
  rcases mul_eq_zero.mp key with h0 | h0
  · exact absurd h0 two_ne_zero_PS
  · exact sub_eq_zero.mp h0

end

end VOA.DeligneAudit.DeligneCharacter.D4Wp
