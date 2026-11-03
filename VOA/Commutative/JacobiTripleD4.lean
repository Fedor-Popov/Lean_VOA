/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.JacobiTriple
import VOA.DeligneAudit.DeligneCharacterD4Theta

/-!
# The two-variable Jacobi triple product for the D₄ theta measure

Discharges `VOA.DeligneAudit.DeligneCharacter.TwoVariableJTP`: for every truncation order `M`,
`x`-degree `j` and `q`-degree `d < M`,

  `[q^d x^j] ∏_{i<M} (1-q^{i+1})(1-q^i x²)(1-q^{i+1}x⁻²)`
  `  = [q^d x^j] ∑_k (-1)^k q^{k(k-1)/2} x^{2k}`.

`TwoVariableJTP` lives in `(ℤ⟦q⟧)[x, x⁻¹]` (Laurent outside), while `VOA.QSeries.JTP.jacobiTriple`
lives in `(ℤ[x, x⁻¹])⟦q⟧` (series outside).  The bridge is the ring homomorphism
`toSeries : (ℤ⟦q⟧)[x,x⁻¹] →+* (ℤ[x,x⁻¹])⟦q⟧` (`LaurentPolynomial.eval₂`), which preserves every
coefficient `[q^d x^j]` (`coeff_toSeries_apply`).
-/

namespace VOA.QSeries.JTP

open PowerSeries LaurentPolynomial

open scoped BigOperators

noncomputable section

local notation "L" => LaurentPolynomial ℤ

/-- `x^n` as a unit of `ℤ[x, x⁻¹]`. -/
def unitT (n : ℤ) : Lˣ :=
  ⟨T n, T (-n), by rw [← T_add, add_neg_cancel, T_zero], by rw [← T_add, neg_add_cancel, T_zero]⟩

@[simp] theorem val_unitT (n : ℤ) : ((unitT n : Lˣ) : L) = T n := rfl

theorem unitT_add (a b : ℤ) : unitT (a + b) = unitT a * unitT b := by
  ext; simp only [Units.val_mul, val_unitT, T_add]

theorem unitT_zero : unitT 0 = 1 := by
  ext; simp only [val_unitT, T_zero, Units.val_one]

theorem unitT_inv (n : ℤ) : (unitT n)⁻¹ = unitT (-n) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← unitT_add, add_neg_cancel, unitT_zero]

theorem unitT_zpow (n j : ℤ) : unitT n ^ j = unitT (j * n) := by
  induction j using Int.induction_on with
  | zero => rw [zpow_zero, zero_mul, unitT_zero]
  | succ i ih => rw [zpow_add_one, ih, ← unitT_add]; congr 1; ring
  | pred i ih => rw [zpow_sub_one, ih, unitT_inv, ← unitT_add]; congr 1; ring

theorem negSign_laurent (j : ℤ) : (negSign j : L) = LaurentPolynomial.C (negSign j : ℤ) := by
  simp [negSign]

theorem sum_signed_T_apply (s : Finset ℤ) (b : ℤ) :
    ((∑ j ∈ s, (negSign j : L) * T (j * 2) : L) : ℤ →₀ ℤ) b =
      ∑ j ∈ s, if j * 2 = b then (negSign j : ℤ) else 0 := by
  erw [Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [negSign_laurent, ← single_eq_C_mul_T, Finsupp.single_apply]

/-- `x` as a unit of `ℤ[x, x⁻¹]⟦q⟧`. -/
def xUnit : (PowerSeries L)ˣ :=
  Units.map (PowerSeries.C : L →+* PowerSeries L).toMonoidHom (unitT 1)

theorem val_xUnit_zpow (n : ℤ) :
    ((xUnit ^ n : (PowerSeries L)ˣ) : PowerSeries L) = PowerSeries.C (T n) := by
  rw [xUnit, ← map_zpow, unitT_zpow, mul_one]
  rfl

/-- Moving the Laurent variable inside the power series. -/
def toSeries : (PowerSeries ℤ)[T;T⁻¹] →+* PowerSeries L :=
  LaurentPolynomial.eval₂ (PowerSeries.map (LaurentPolynomial.C : ℤ →+* L)) xUnit

theorem toSeries_C_mul_T (a : PowerSeries ℤ) (n : ℤ) :
    toSeries (LaurentPolynomial.C a * T n) =
      PowerSeries.map (LaurentPolynomial.C : ℤ →+* L) a * PowerSeries.C (T n) := by
  rw [toSeries, eval₂_C_mul_T, val_xUnit_zpow]

theorem toSeries_C (a : PowerSeries ℤ) :
    toSeries (LaurentPolynomial.C a) = PowerSeries.map (LaurentPolynomial.C : ℤ →+* L) a := by
  rw [toSeries, LaurentPolynomial.eval₂_C]

theorem toSeries_T (n : ℤ) : toSeries (T n) = PowerSeries.C (T n) := by
  rw [toSeries, eval₂_T, val_xUnit_zpow]

/-- `toSeries` preserves every coefficient `[q^d x^j]`. -/
theorem coeff_toSeries_apply (F : (PowerSeries ℤ)[T;T⁻¹]) (d : ℕ) (j : ℤ) :
    ((coeff d (toSeries F) : L) : ℤ →₀ ℤ) j = coeff d ((F : ℤ →₀ PowerSeries ℤ) j) := by
  induction F using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, map_add]
      erw [Finsupp.add_apply, Finsupp.add_apply]
      rw [hp, hq, map_add]
  | C_mul_T n a =>
      rw [toSeries_C_mul_T, coeff_mul_C, coeff_map, ← single_eq_C_mul_T, ← single_eq_C_mul_T,
        Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp

theorem coeff_tripleSum_unitT_apply (d : ℕ) (j : ℤ) :
    ((coeff d (tripleSum (unitT 2)) : L) : ℤ →₀ ℤ) j =
      coeff d (VOA.DeligneAudit.DeligneCharacter.jtpCoeff j) := by
  have hsum : (coeff d (tripleSum (unitT 2)) : L) =
      ∑ k ∈ Finset.Icc (-(d : ℤ) - 1) (d + 1) with pentExp k = d, (negSign k : L) * T (k * 2) := by
    rw [tripleSum, coeff_zSeries]
    apply Finset.sum_congr rfl
    intro k _
    rw [tripleCoeff, unitT_zpow, val_unitT]
  rw [hsum, sum_signed_T_apply, VOA.DeligneAudit.DeligneCharacter.jtpCoeff]
  split_ifs with hj
  · obtain ⟨k0, hk0⟩ := hj
    have hdiv : j / 2 = k0 := by omega
    rw [hdiv, show ((-1 : PowerSeries ℤ) ^ k0.natAbs) = PowerSeries.C ((-1) ^ k0.natAbs) by simp,
      coeff_C_mul_X_pow]
    by_cases hk : pentExp k0 = d
    · have hmem : k0 ∈ (Finset.Icc (-(d : ℤ) - 1) (d + 1)).filter (fun k => pentExp k = d) := by
        rw [Finset.mem_filter, Finset.mem_Icc]
        have := natAbs_le_pentExp k0
        exact ⟨⟨by omega, by omega⟩, hk⟩
      rw [Finset.sum_eq_single_of_mem k0 hmem (fun k _ hne => if_neg (by omega)), if_pos (by omega),
        if_pos (show d = VOA.DeligneAudit.DeligneCharacter.triC k0 from hk.symm)]
      rfl
    · rw [if_neg (show ¬ d = VOA.DeligneAudit.DeligneCharacter.triC k0 from fun h => hk h.symm)]
      apply Finset.sum_eq_zero
      intro k hks
      rw [if_neg]
      intro h
      have hkk : k = k0 := by omega
      subst hkk
      exact hk (Finset.mem_filter.mp hks).2
  · rw [map_zero]
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg]
    intro h
    exact hj ⟨k, by omega⟩

theorem toSeries_jtpTrunc (M : ℕ) :
    toSeries (VOA.DeligneAudit.DeligneCharacter.jtpTrunc M) =
      ∏ i ∈ Finset.range M, ((1 - X ^ (i + 1)) * (1 - PowerSeries.C (T 2 : L) * X ^ i) *
        (1 - PowerSeries.C (T (-2) : L) * X ^ (i + 1))) := by
  rw [VOA.DeligneAudit.DeligneCharacter.jtpTrunc, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [map_mul, map_sub, map_one, toSeries_C, toSeries_T, map_pow, map_X]
  ring

/-- Telescoping the truncation against the normalized factors of `jacobiTriple`. -/
theorem jtp_trunc_telescope (M : ℕ) :
    (∏ i ∈ Finset.range M, ((1 - X ^ (i + 1)) * (1 - PowerSeries.C (T 2 : L) * X ^ i) *
        (1 - PowerSeries.C (T (-2) : L) * X ^ (i + 1)))) * (1 - PowerSeries.C (T 2 : L) * X ^ M) =
      (1 - PowerSeries.C (T 2 : L)) * ∏ i ∈ Finset.range M, tripleFactor (unitT 2) i := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, tripleFactor, unitT_inv, val_unitT,
        val_unitT]
      linear_combination ((1 - X ^ (M + 1)) * (1 - PowerSeries.C (T (-2) : L) * X ^ (M + 1)) *
        (1 - PowerSeries.C (T 2 : L) * X ^ (M + 1))) * ih

/-- **`TwoVariableJTP`, discharged.** -/
theorem twoVariableJTP : VOA.DeligneAudit.DeligneCharacter.TwoVariableJTP := by
  refine ⟨fun M j d hd => ?_⟩
  have hag : AgreeTo M (toSeries (VOA.DeligneAudit.DeligneCharacter.jtpTrunc M))
      (tripleSum (unitT 2)) := by
    rw [toSeries_jtpTrunc, ← jacobiTriple, val_unitT]
    set P := ∏ i ∈ Finset.range M, ((1 - X ^ (i + 1)) * (1 - PowerSeries.C (T 2 : L) * X ^ i) *
        (1 - PowerSeries.C (T (-2) : L) * X ^ (i + 1)))
    have h1 : AgreeTo M P (P * (1 - PowerSeries.C (T 2 : L) * X ^ M)) := by
      have : AgreeTo M (1 : PowerSeries L) (1 - PowerSeries.C (T 2 : L) * X ^ M) := by
        unfold AgreeTo
        rw [sub_sub_cancel]
        exact Dvd.intro_left _ rfl
      simpa using this.mul_left P
    rw [jtp_trunc_telescope] at h1
    exact h1.trans (((agreeTo_infProd (prodFactors_tripleFactor (unitT 2)) M).symm.mono
      (Nat.le_succ M)).mul_left _)
  rw [← coeff_toSeries_apply, hag.coeff_eq hd, coeff_tripleSum_unitT_apply]

end

end VOA.QSeries.JTP

section AxiomAudit
#print axioms VOA.QSeries.JTP.jacobiTriple
#print axioms VOA.QSeries.JTP.coeff_toSeries_apply
#print axioms VOA.QSeries.JTP.twoVariableJTP
end AxiomAudit
