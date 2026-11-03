/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.QExpSpan2Trace

/-!
# Normalized weight-one Eisenstein series, binomials and their products

`eisN v` (`v ∈ (ℤ/N)²`) is the normalized weight-one series `weightOneNormalized (v 0) (v 1)`
as a modular form for `Γ(N)`; it satisfies the exact slash law `eisN v ∣ γ = eisN (v γ)`
(proved in `QExpWeightOneSlash` from the unconditional theta Fourier identity).
A *binomial* is `c₁ E_v − c₂ E_w`; rows of the Cramer frame are products of binomials.

* `eisCoeff_zero`: the constant term `Cval v`
  (`(N − 2ã)/(2N)` for `a ≠ 0`, `(1+ζ^b)/(2(1−ζ^b))` for `a = 0 ≠ b`);
* `eisCoeff_mem_frameRing`: all coefficients lie in `ℤ[1/M][ζ]` when `2N ∣ M`;
* `qExpansion_gammaSlash_binProd`: the expansion of a product of binomials at any cusp.
-/

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

noncomputable section

namespace VOA.Classification.COne.SSHecke

variable {N : ℕ}

theorem stdRoot_isPrimitiveRoot (N : ℕ) [NeZero N] :
    IsPrimitiveRoot (weightOneStandardRoot N) N :=
  Complex.isPrimitiveRoot_exp N (NeZero.ne N)

theorem stdSlashLaws (N : ℕ) [NeZero N] : WeightOneSlashLaws N (weightOneStandardRoot N) :=
  weightOneSlashLaws_standard_of_thetaFourier (NeZero.pos N)
    (weightOneThetaFourier (NeZero.pos N))

/-- The clearing scalar of the generator with index `v`. -/
def eisScale [NeZero N] (v : Fin 2 → ZMod N) : ℂ :=
  weightOneScale N (weightOneStandardRoot N) (weightOneIndex (v 0)) (weightOneIndex (v 1))

theorem eisScale_ne_zero [NeZero N] (v : Fin 2 → ZMod N) : eisScale v ≠ 0 :=
  weightOneScale_ne_zero (NeZero.pos N) (stdRoot_isPrimitiveRoot N) _ _

/-- The normalized weight-one Eisenstein series `E_v` for `Γ(N)`. -/
def eisN [NeZero N] (v : Fin 2 → ZMod N) : ModularForm (GammaGL N) 1 :=
  (eisScale v)⁻¹ • weightOneModularForm (NeZero.pos N) (stdRoot_isPrimitiveRoot N)
    (stdSlashLaws N) (weightOneIndex (v 0)) (weightOneIndex (v 1))

theorem coe_eisN [NeZero N] (v : Fin 2 → ZMod N) :
    ⇑(eisN v) = weightOneNormalized (v 0) (v 1) := by
  funext τ
  simp only [eisN, weightOneNormalized, eisScale, div_eq_inv_mul]
  rfl

/-- The exact slash law `E_v ∣ γ = E_{vγ}`. -/
theorem gammaSlash_eisN [NeZero N] (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) :
    ⇑(gammaSlash (eisN v) γ) = ⇑(eisN (weightOneResidueAction v γ)) := by
  rw [coe_gammaSlash, coe_eisN, coe_eisN]
  exact weightOneNormalized_slash (weightOneThetaFourier (NeZero.pos N)) v γ

/-- Coefficients of `E_v`. -/
def eisCoeff [NeZero N] (v : Fin 2 → ZMod N) (n : ℕ) : ℂ :=
  (eisScale v)⁻¹ * weightOneIntegralCoeff N (weightOneStandardRoot N)
    (weightOneIndex (v 0)) (weightOneIndex (v 1)) n

def eisSeries [NeZero N] (v : Fin 2 → ZMod N) : PowerSeries ℂ := PowerSeries.mk (eisCoeff v)

theorem qExpansion_eisN [NeZero N] (v : Fin 2 → ZMod N) :
    qExpansion (N : ℝ) (eisN v) = eisSeries v := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  ext n
  rw [eisN, show ⇑((eisScale v)⁻¹ • weightOneModularForm (NeZero.pos N)
      (stdRoot_isPrimitiveRoot N) (stdSlashLaws N) (weightOneIndex (v 0))
      (weightOneIndex (v 1))) = (eisScale v)⁻¹ • ⇑(weightOneModularForm (NeZero.pos N)
      (stdRoot_isPrimitiveRoot N) (stdSlashLaws N) (weightOneIndex (v 0))
      (weightOneIndex (v 1))) from rfl,
    ModularForm.qExpansion_smul hNR (nat_mem_strictPeriods_Gamma N),
    PowerSeries.coeff_smul, weightOneModularForm_coeff, eisSeries, PowerSeries.coeff_mk,
    eisCoeff, smul_eq_mul]

/-- The constant term of `E_v`. -/
def Cval [NeZero N] (v : Fin 2 → ZMod N) : ℂ :=
  if v 0 = 0 then
    (if v 1 = 0 then 0 else
      (1 + weightOneStandardRoot N ^ (v 1).val) /
        (2 * (1 - weightOneStandardRoot N ^ (v 1).val)))
  else ((N : ℂ) - 2 * (v 0).val) / (2 * N)

theorem weightOneIndex_val [NeZero N] (a : ZMod N) : (weightOneIndex a).val = a.val := rfl

theorem eisScale_eq [NeZero N] (v : Fin 2 → ZMod N) :
    eisScale v = if v 0 = 0 ∧ v 1 ≠ 0 then
      2 * N * (1 - weightOneStandardRoot N ^ (v 1).val) else 2 * N := by
  simp only [eisScale, weightOneScale, weightOneIndex_val, ne_eq, ZMod.val_eq_zero]

theorem eisCoeff_zero [NeZero N] (v : Fin 2 → ZMod N) : eisCoeff v 0 = Cval v := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hI : weightOneIntegralCoeff N (weightOneStandardRoot N) (weightOneIndex (v 0))
      (weightOneIndex (v 1)) 0 = if v 0 = 0 ∧ v 1 = 0 then 0 else
        if v 0 = 0 then (N : ℂ) * (1 + weightOneStandardRoot N ^ (v 1).val)
        else (N : ℂ) - 2 * (v 0).val := by
    simp only [weightOneIntegralCoeff, weightOneIndex_val, ZMod.val_eq_zero, if_true]
  rw [eisCoeff, hI, eisScale_eq, Cval]
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · simp [h0, h1]
    · have hz : (1 : ℂ) - weightOneStandardRoot N ^ (v 1).val ≠ 0 := by
        refine sub_ne_zero.mpr (Ne.symm ?_)
        exact (stdRoot_isPrimitiveRoot N).pow_ne_one_of_pos_of_lt
          ((ZMod.val_ne_zero _).mpr h1) (ZMod.val_lt _)
      simp only [h0, h1, true_and, ne_eq, not_false_eq_true, if_true, if_false]
      field_simp
  · simp only [h0, false_and, if_false]
    field_simp

theorem eisCoeff_of_pos [NeZero N] (v : Fin 2 → ZMod N) {n : ℕ} (hn : n ≠ 0) :
    eisCoeff v n = if v = 0 then 0 else
      weightOneDivisorCoeff N (weightOneStandardRoot N) (weightOneIndex (v 0))
        (weightOneIndex (v 1)) n := by
  have hv : (v = 0) ↔ (v 0 = 0 ∧ v 1 = 0) := by
    constructor
    · rintro rfl; simp
    · rintro ⟨h0, h1⟩; ext i; fin_cases i <;> simp [h0, h1]
  simp only [eisCoeff, weightOneIntegralCoeff, weightOneIndex_val, ZMod.val_eq_zero, hn,
    if_false, hv]
  split_ifs
  · simp
  · rw [← mul_assoc, show weightOneScale N (weightOneStandardRoot N) (weightOneIndex (v 0))
      (weightOneIndex (v 1)) = eisScale v from rfl, inv_mul_cancel₀ (eisScale_ne_zero v),
      one_mul]

/-- The `q^{1/N}` coefficient of `E_{(1,0)}` is `1`. -/
theorem eisCoeff_one_e1 [NeZero N] (hN : 3 ≤ N) : eisCoeff (N := N) ![1, 0] 1 = 1 := by
  have h1 : ((1 : ZMod N)).val = 1 := ZMod.val_one_eq_one_mod N ▸ Nat.mod_eq_of_lt (by omega)
  rw [eisCoeff_of_pos _ one_ne_zero, if_neg]
  · simp only [weightOneDivisorCoeff, Nat.divisors_one, Finset.sum_singleton, weightOneIndex_val,
      Matrix.cons_val_zero, Matrix.cons_val_one, ZMod.val_zero, h1,
      Nat.one_mod_eq_one.mpr (by omega : N ≠ 1), if_true, pow_zero, Nat.div_one, mul_zero]
    rw [if_neg (by rw [Nat.mod_eq_of_lt (by omega)]; omega)]
    ring
  · intro h
    have := congrFun h 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at this
    have h1' := congrArg ZMod.val this
    rw [h1, ZMod.val_zero] at h1'
    exact one_ne_zero h1'

/-- The `q^{1/N}` coefficient of `E_{(0,1)}` is `0`. -/
theorem eisCoeff_one_e2 [NeZero N] (hN : 3 ≤ N) : eisCoeff (N := N) ![0, 1] 1 = 0 := by
  rw [eisCoeff_of_pos _ one_ne_zero]
  split_ifs
  · rfl
  · simp only [weightOneDivisorCoeff, Nat.divisors_one, Finset.sum_singleton, weightOneIndex_val,
      Matrix.cons_val_zero, ZMod.val_zero, Nat.one_mod_eq_one.mpr (by omega : N ≠ 1),
      add_zero]
    rw [if_neg one_ne_zero, if_neg one_ne_zero, sub_zero]

/-! ## Integrality -/

theorem Cval_mem_frameRing [NeZero N] {M : ℕ} (hM : M ≠ 0) (h2N : 2 * N ∣ M)
    (v : Fin 2 → ZMod N) : Cval v ∈ frameRing M (weightOneStandardRoot N) := by
  set A := frameRing M (weightOneStandardRoot N)
  have hNM : N ∣ M := (Dvd.intro_left 2 rfl).trans h2N
  have h2M : 2 ∣ M := (Dvd.intro _ rfl).trans h2N
  have hzN : weightOneStandardRoot N ^ N = 1 := (stdRoot_isPrimitiveRoot N).pow_eq_one
  unfold Cval
  split_ifs with h0 h1
  · exact A.zero_mem
  · have hne : weightOneStandardRoot N ^ (v 1).val ≠ 1 :=
      (stdRoot_isPrimitiveRoot N).pow_ne_one_of_pos_of_lt
        ((ZMod.val_ne_zero _).mpr h1) (ZMod.val_lt _)
    rw [div_eq_mul_inv, mul_inv]
    refine A.mul_mem (A.add_mem A.one_mem (zeta_pow_mem_frameRing M _ _))
      (A.mul_mem ?_ (inv_one_sub_mem_frameRing hM hNM (NeZero.pos N) hzN _ hne))
    exact_mod_cast inv_natCast_mem_frameRing _ hM h2M
  · rw [div_eq_mul_inv]
    refine A.mul_mem (A.sub_mem (natCast_mem_frameRing M _ N)
      (A.mul_mem (natCast_mem_frameRing M _ 2) (natCast_mem_frameRing M _ _))) ?_
    exact_mod_cast inv_natCast_mem_frameRing _ hM h2N

theorem eisCoeff_mem_frameRing [NeZero N] {M : ℕ} (hM : M ≠ 0) (h2N : 2 * N ∣ M)
    (v : Fin 2 → ZMod N) (n : ℕ) :
    eisCoeff v n ∈ frameRing M (weightOneStandardRoot N) := by
  by_cases hn : n = 0
  · subst hn
    rw [eisCoeff_zero]
    exact Cval_mem_frameRing hM h2N v
  · rw [eisCoeff_of_pos v hn]
    split_ifs
    · exact Subalgebra.zero_mem _
    · exact weightOneDivisorCoeff_mem_subalgebra _ N (zeta_mem_frameRing M _) _ _ n

/-! ## Binomials and products -/

/-- A binomial `c₁ E_v − c₂ E_w`. -/
structure Bin (N : ℕ) where
  c1 : ℂ
  v : Fin 2 → ZMod N
  c2 : ℂ
  w : Fin 2 → ZMod N

/-- Transport of the indices by `γ`. -/
def Bin.act (b : Bin N) (γ : SL(2, ℤ)) : Bin N :=
  ⟨b.c1, weightOneResidueAction b.v γ, b.c2, weightOneResidueAction b.w γ⟩

theorem Bin.act_mul (b : Bin N) (γ δ : SL(2, ℤ)) : b.act (γ * δ) = (b.act γ).act δ := by
  simp [Bin.act, weightOneResidueAction_mul]

@[simp] theorem Bin.act_one (b : Bin N) : b.act 1 = b := by
  cases b; simp [Bin.act]

def binForm [NeZero N] (b : Bin N) : ModularForm (GammaGL N) 1 :=
  b.c1 • eisN b.v - b.c2 • eisN b.w

def binSeries [NeZero N] (b : Bin N) : PowerSeries ℂ :=
  b.c1 • eisSeries b.v - b.c2 • eisSeries b.w

theorem coe_binForm [NeZero N] (b : Bin N) :
    ⇑(binForm b) = b.c1 • ⇑(eisN b.v) - b.c2 • ⇑(eisN b.w) := rfl

theorem gammaSlash_binForm [NeZero N] (b : Bin N) (γ : SL(2, ℤ)) :
    ⇑(gammaSlash (binForm b) γ) = ⇑(binForm (b.act γ)) := by
  rw [coe_gammaSlash, coe_binForm, coe_binForm, sub_eq_add_neg, SlashAction.add_slash,
    SlashAction.neg_slash, ModularForm.SL_smul_slash, ModularForm.SL_smul_slash,
    ← sub_eq_add_neg, ← coe_gammaSlash, ← coe_gammaSlash, gammaSlash_eisN, gammaSlash_eisN]
  rfl

theorem qExpansion_binForm [NeZero N] (b : Bin N) :
    qExpansion (N : ℝ) (binForm b) = binSeries b := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hP := nat_mem_strictPeriods_Gamma N
  rw [show ⇑(binForm b) = ⇑(b.c1 • eisN b.v) - ⇑(b.c2 • eisN b.w) from rfl,
    ModularForm.qExpansion_sub hNR hP,
    show ⇑(b.c1 • eisN b.v) = b.c1 • ⇑(eisN b.v) from rfl,
    show ⇑(b.c2 • eisN b.w) = b.c2 • ⇑(eisN b.w) from rfl,
    ModularForm.qExpansion_smul hNR hP, ModularForm.qExpansion_smul hNR hP,
    qExpansion_eisN, qExpansion_eisN, binSeries]

theorem constantCoeff_binSeries [NeZero N] (b : Bin N) :
    PowerSeries.constantCoeff (binSeries b) = b.c1 * Cval b.v - b.c2 * Cval b.w := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [binSeries, eisSeries, eisCoeff_zero]

/-- A product of binomials as a modular form of weight equal to the length. -/
def binProd [NeZero N] : (l : List (Bin N)) → ModularForm (GammaGL N) (l.length : ℤ)
  | [] => ModularForm.mcast (by simp) (1 : ModularForm (GammaGL N) 0)
  | b :: l => ModularForm.mcast (by simp; ring) ((binForm b).mul (binProd l))

theorem coe_binProd_nil [NeZero N] : ⇑(binProd ([] : List (Bin N))) = 1 := rfl

theorem coe_binProd_cons [NeZero N] (b : Bin N) (l : List (Bin N)) :
    ⇑(binProd (b :: l)) = ⇑(binForm b) * ⇑(binProd l) := rfl

theorem gammaSlash_binProd [NeZero N] (l : List (Bin N)) (γ : SL(2, ℤ)) :
    ⇑(gammaSlash (binProd l) γ) = ⇑(binProd (l.map (·.act γ))) := by
  induction l with
  | nil =>
    rw [coe_gammaSlash, List.map_nil, coe_binProd_nil]
    have := ModularForm.is_invariant_const γ (1 : ℂ)
    simpa [Function.const] using this
  | cons b l ih =>
    rw [coe_gammaSlash, List.map_cons, coe_binProd_cons, coe_binProd_cons]
    have hw : ((b :: l).length : ℤ) = 1 + (l.length : ℤ) := by simp; ring
    rw [hw, ModularForm.mul_slash_SL2, ← coe_gammaSlash, ← coe_gammaSlash, gammaSlash_binForm,
      ih]

theorem qExpansion_binProd [NeZero N] (l : List (Bin N)) :
    qExpansion (N : ℝ) (binProd l) = (l.map binSeries).prod := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hP := nat_mem_strictPeriods_Gamma N
  induction l with
  | nil => rw [coe_binProd_nil, List.map_nil, List.prod_nil]; exact qExpansion_one _
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons, ← ih, ← qExpansion_binForm, coe_binProd_cons,
      ← ModularForm.coe_mul, ModularForm.qExpansion_mul hNR hP]

/-- The expansion of a product of binomials at the cusp of `γ`. -/
theorem qExpansion_gammaSlash_binProd [NeZero N] (l : List (Bin N)) (γ : SL(2, ℤ)) :
    qExpansion (N : ℝ) (gammaSlash (binProd l) γ) = (l.map fun b => binSeries (b.act γ)).prod := by
  rw [gammaSlash_binProd, qExpansion_binProd, List.map_map]
  rfl

end VOA.Classification.COne.SSHecke
