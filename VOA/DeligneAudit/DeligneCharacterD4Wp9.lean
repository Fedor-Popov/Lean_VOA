/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Wp8
import VOA.DeligneAudit.DeligneCharacterD4Final

/-!
# Integral form of the D₄ kernel (layer 9)

The kernel `D4K.kernelM ∈ 𝕜[x,z]⟦s⟧` has coefficients in `ℚ⟦r⟧ ⊂ 𝕜 = ℚ((r))`: `kernelM = ιS kernelM'`
(`ιS_kernelM'`), with `kernelM' ∈ ℚ⟦r⟧[x,z]⟦s⟧` built from the same Euler series.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4Wp

open PowerSeries

open scoped BigOperators

noncomputable section

/-- `ℚ⟦r⟧`. -/
abbrev P := PowerSeries ℚ

/-- `ℚ⟦r⟧ → ℚ((r))`. -/
abbrev coeK : P →+* D4K.Kq := HahnSeries.ofPowerSeries ℤ ℚ

theorem coeK_X : coeK X = D4K.rr := by rw [HahnSeries.ofPowerSeries_X]; rfl

theorem coeK_X_sq : coeK (X ^ 2) = D4K.qq := by rw [map_pow, coeK_X, D4K.qq_eq_rr_sq]

theorem coeK_injective : Function.Injective coeK := HahnSeries.ofPowerSeries_injective

/-- `ℚ⟦r⟧[x^{±1}, z^{±1}]`. -/
abbrev R' := AddMonoidAlgebra P D4K.V

/-- `ℚ⟦r⟧[x,z] → 𝕜[x,z]`. -/
def ιR : R' →+* D4K.R :=
  AddMonoidAlgebra.liftNCRingHom ((algebraMap D4K.Kq D4K.R).comp coeK) (AddMonoidAlgebra.of D4K.Kq D4K.V)
    (fun _ _ => Commute.all _ _)

theorem ιR_single (v : D4K.V) (c : P) : ιR (AddMonoidAlgebra.single v c) = D4K.mon v (coeK c) := by
  rw [ιR, AddMonoidAlgebra.liftNCRingHom_single]
  simp only [RingHom.coe_comp, Function.comp_apply, AddMonoidAlgebra.of_apply]
  rw [show (AddMonoidAlgebra.single (Multiplicative.toAdd (Multiplicative.ofAdd v)) (1 : D4K.Kq)) =
    D4K.mon v 1 from rfl, D4K.algebraMap_mul_mon, mul_one]

theorem ιR_apply (f : R') (v : D4K.V) : (ιR f) v = coeK (f v) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; show (0 : D4K.Kq) = coeK (0 : P); rw [map_zero]
  | add f g hf hg =>
      rw [map_add]
      show (ιR f) v + (ιR g) v = coeK ((f + g) v)
      rw [hf, hg, show (f + g) v = f v + g v from rfl, map_add]
  | single w c =>
      rw [ιR_single, D4K.mon]
      show (Finsupp.single w (coeK c)) v = coeK ((Finsupp.single w c) v)
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp

theorem ιR_injective : Function.Injective ιR := by
  intro f g h
  refine Finsupp.ext fun v => ?_
  have := congrArg (fun F => F v) h
  simp only [ιR_apply] at this
  exact coeK_injective this

/-- `ιS = map ιR`. -/
abbrev ιS : PowerSeries R' →+* D4K.S := PowerSeries.map ιR

theorem ιS_injective : Function.Injective ιS := by
  intro F G h
  ext n : 1
  exact ιR_injective (by rw [← coeff_map, ← coeff_map, h])

/-! ## Integral Euler series -/

/-- `(q;q)_n` in `ℚ⟦r⟧`. -/
def qpochP (n : ℕ) : P := ∏ i ∈ Finset.range n, (1 - X ^ (2 * (i + 1)))

theorem coeK_qpochP (n : ℕ) : coeK (qpochP n) = D4K.qpoch n := by
  rw [qpochP, D4K.qpoch, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_sub, map_one, pow_mul, map_pow, coeK_X_sq]

theorem constantCoeff_qpochP (n : ℕ) : constantCoeff (qpochP n) = 1 := by
  rw [qpochP, map_prod]
  exact Finset.prod_eq_one fun i _ => by simp

theorem coeK_inv_qpochP (n : ℕ) : coeK (qpochP n)⁻¹ = (D4K.qpoch n)⁻¹ := by
  have h : (qpochP n)⁻¹ * qpochP n = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [constantCoeff_qpochP]; exact one_ne_zero)
  have h2 := congrArg coeK h
  rw [map_mul, map_one, coeK_qpochP] at h2
  exact eq_inv_of_mul_eq_one_left h2

/-- `∑ yⁿ/(q;q)_n` over `ℚ⟦r⟧`. -/
def eInvP : PowerSeries P := PowerSeries.mk fun n => (qpochP n)⁻¹

/-- `∑ (-1)ⁿ q^{n(n-1)/2} yⁿ/(q;q)_n` over `ℚ⟦r⟧`. -/
def ePosP : PowerSeries P :=
  PowerSeries.mk fun n => (-1) ^ n * (X ^ 2) ^ (n * (n - 1) / 2) * (qpochP n)⁻¹

theorem map_eInvP : PowerSeries.map coeK eInvP = D4K.eInv := by
  ext n : 1; rw [coeff_map, eInvP, coeff_mk, D4K.eInv, coeff_mk, coeK_inv_qpochP]

theorem map_ePosP : PowerSeries.map coeK ePosP = D4K.ePos := by
  ext n : 1
  rw [coeff_map, ePosP, coeff_mk, D4K.ePos, coeff_mk, map_mul, map_mul, coeK_inv_qpochP, map_pow, map_pow,
    coeK_X_sq]
  simp

/-- `𝕜`-coefficients of `ℚ⟦r⟧`-series. -/
def liftS' : PowerSeries P →+* PowerSeries R' := PowerSeries.map (algebraMap P R')

theorem ιR_algebraMap (c : P) : ιR (algebraMap P R' c) = algebraMap D4K.Kq D4K.R (coeK c) := by
  rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
    ιR_single]
  rw [show (algebraMap D4K.Kq D4K.R) (coeK c) = D4K.mon 0 (coeK c) by
    rw [AddMonoidAlgebra.coe_algebraMap]; rfl]

theorem ιS_liftS' (f : PowerSeries P) : ιS (liftS' f) = D4K.liftS (PowerSeries.map coeK f) := by
  ext n : 1
  rw [liftS', D4K.liftS, coeff_map, coeff_map, coeff_map, coeff_map, ιR_algebraMap]

/-- Integral `1/(c z^v s^k; q)_∞`. -/
def EInv' (c : P) (v : D4K.V) (k : ℕ) (hk : k ≠ 0) : PowerSeries R' :=
  expand k hk (rescale (AddMonoidAlgebra.single v c) (liftS' eInvP))

/-- Integral `(c z^v s^k; q)_∞`. -/
def EPos' (c : P) (v : D4K.V) (k : ℕ) (hk : k ≠ 0) : PowerSeries R' :=
  expand k hk (rescale (AddMonoidAlgebra.single v c) (liftS' ePosP))

theorem ιS_EInv' (c : P) (v : D4K.V) (k : ℕ) (hk : k ≠ 0) :
    ιS (EInv' c v k hk) = D4K.EInv (coeK c) v k hk := by
  rw [EInv', D4K.EInv, PowerSeries.map_expand, ← rescale_map, ιS_liftS', ιR_single, map_eInvP]

theorem ιS_EPos' (c : P) (v : D4K.V) (k : ℕ) (hk : k ≠ 0) :
    ιS (EPos' c v k hk) = D4K.EPos (coeK c) v k hk := by
  rw [EPos', D4K.EPos, PowerSeries.map_expand, ← rescale_map, ιS_liftS', ιR_single, map_ePosP]

/-- Integral kernel. -/
def tFactors' : PowerSeries R' :=
  EPos' 1 0 2 two_ne_zero * EPos' 1 (2 • D4K.xv) 2 two_ne_zero * EPos' 1 (-2 • D4K.xv) 2 two_ne_zero

def hyperFactors' : PowerSeries R' := (D4K.hyperVecs.map fun v => EInv' 1 v 1 one_ne_zero).prod

def kernelM' : PowerSeries R' := tFactors' * hyperFactors'

theorem ιS_kernelM' : ιS kernelM' = D4K.kernelM := by
  rw [kernelM', D4K.kernelM, tFactors', hyperFactors', D4K.tFactors, D4K.hyperFactors, map_mul, map_mul,
    map_mul, ιS_EPos', ιS_EPos', ιS_EPos', map_one, map_list_prod, List.map_map]
  congr 2
  refine List.map_congr_left fun v _ => ?_
  simp only [Function.comp_apply, ιS_EInv', map_one]

/-! ## Transported functional equations -/

theorem EInv'_mul_one_sub (c : P) (v : D4K.V) :
    EInv' c v 1 one_ne_zero * (1 - PowerSeries.C (AddMonoidAlgebra.single v c) * X) =
      EInv' (X ^ 2 * c) v 1 one_ne_zero := by
  apply ιS_injective
  rw [map_mul, ιS_EInv', ιS_EInv', map_sub, map_one, map_mul, PowerSeries.map_C, PowerSeries.map_X,
    ιR_single, map_mul, coeK_X_sq, ← D4K.EInv_mul_one_sub, smul_eq_C_mul, pow_one]

theorem EPos'_eq (c : P) (v : D4K.V) :
    EPos' c v 2 two_ne_zero =
      (1 - PowerSeries.C (AddMonoidAlgebra.single v c) * X ^ 2) * EPos' (X ^ 2 * c) v 2 two_ne_zero := by
  apply ιS_injective
  rw [map_mul, ιS_EPos', ιS_EPos', map_sub, map_one, map_mul, PowerSeries.map_C, map_pow, PowerSeries.map_X,
    ιR_single, map_mul, coeK_X_sq, D4K.EPos_eq, smul_eq_C_mul]

end

end VOA.DeligneAudit.DeligneCharacter.D4Wp
