/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Wp9

/-!
# The specialised kernel (layer 10)

`Sp' : ℚ⟦r⟧[x,z]⟦s⟧ → ℚ[x^{±1}]⟦r⟧` (`z = 1`, `s = r`) is a ring homomorphism, and
`Sp' kernelM' · Den⁸ = M_num` (`Sp'_kernelM'`).
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4Wp

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

/-- `z^v ↦ x^{v₀}`. -/
def gx : Multiplicative D4K.V →* PowerSeries L where
  toFun v := PowerSeries.C (mono ((Multiplicative.toAdd v) 0))
  map_one' := by simp [mono_zero]
  map_mul' v w := by rw [← map_mul, mono_mul]; rfl

/-- `ℚ⟦r⟧[x,z] → ℚ[x^{±1}]⟦r⟧`, `z = 1`. -/
def ψ : R' →+* PowerSeries L :=
  AddMonoidAlgebra.liftNCRingHom (PowerSeries.map cst) gx (fun _ _ => Commute.all _ _)

theorem ψ_single (v : D4K.V) (c : P) :
    ψ (AddMonoidAlgebra.single v c) = PowerSeries.map cst c * PowerSeries.C (mono (v 0)) := by
  rw [ψ, AddMonoidAlgebra.liftNCRingHom_single]; rfl

/-- **Specialisation** `z = 1`, `s = r`. -/
def Sp' : PowerSeries R' →+* PowerSeries L := diagHom.comp (PowerSeries.map ψ)

theorem diagS_C_mul_X_pow {A : Type*} [CommRing A] (a : PowerSeries A) (k : ℕ) :
    diagS (PowerSeries.C a * X ^ k) = a * X ^ k := by
  ext n : 1
  rw [coeff_diagS, coeff_mul_X_pow']
  simp only [coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single k]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg hb, map_zero]
    · intro hk; exact absurd (Finset.mem_range.mpr (by omega)) hk
  · refine Finset.sum_eq_zero fun b hb => ?_
    split_ifs with hb'
    · subst hb'; exfalso; rw [Finset.mem_range] at hb; omega
    · rw [map_zero]

theorem Sp'_C_mul_X_pow (v : D4K.V) (c : P) (k : ℕ) :
    Sp' (PowerSeries.C (AddMonoidAlgebra.single v c) * X ^ k) =
      PowerSeries.map cst c * PowerSeries.C (mono (v 0)) * X ^ k := by
  rw [Sp', RingHom.comp_apply, map_mul, PowerSeries.map_C, map_pow, PowerSeries.map_X, ψ_single]
  exact diagS_C_mul_X_pow _ _

theorem map_cst_X_pow (n : ℕ) : PowerSeries.map cst (X ^ n : P) = X ^ n := by
  rw [map_pow, PowerSeries.map_X]

/-- Agreement of a diagonal with `1`. -/
theorem diag_agree (G : PowerSeries (PowerSeries L)) (a : ℕ) (h0 : coeff 0 G = 1)
    (h : ∀ n, 1 ≤ n → (X : PowerSeries L) ^ (a * n) ∣ coeff n G) : AgreeTo (a + 1) (diagS G) 1 := by
  apply AgreeTo.of_coeff
  intro i hi
  rw [coeff_diagS, Finset.sum_range_succ', h0, coeff_one]
  rw [Finset.sum_eq_zero, zero_add]
  · simp
  · intro k hk
    rw [Finset.mem_range] at hk
    have ha : a ≤ a * (k + 1) := Nat.le_mul_of_pos_right a (by omega)
    exact (PowerSeries.X_pow_dvd_iff.mp (h (k + 1) (by omega))) _ (by omega)

theorem coeff_rescale_liftS' (v : D4K.V) (c : P) (f : PowerSeries P) (n : ℕ) :
    coeff n (rescale (AddMonoidAlgebra.single v c) (liftS' f)) =
      AddMonoidAlgebra.single (n • v) (c ^ n * coeff n f) := by
  rw [coeff_rescale, liftS', coeff_map, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.coe_algebraMap,
    Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply, AddMonoidAlgebra.single_mul_single,
    add_zero]

theorem coeff_EInv'_one (v : D4K.V) (c : P) (n : ℕ) :
    coeff n (EInv' c v 1 one_ne_zero) = AddMonoidAlgebra.single (n • v) (c ^ n * (qpochP n)⁻¹) := by
  rw [EInv', expand_one_apply, coeff_rescale_liftS', eInvP, coeff_mk]

theorem coeff_EPos'_two (v : D4K.V) (c : P) (j : ℕ) :
    coeff j (EPos' c v 2 two_ne_zero) = if 2 ∣ j then
      AddMonoidAlgebra.single ((j / 2) • v) (c ^ (j / 2) * coeff (j / 2) ePosP) else 0 := by
  rw [EPos', coeff_expand]
  split_ifs
  · rw [coeff_rescale_liftS']
  · rfl

theorem qpochP_zero : qpochP 0 = 1 := by simp [qpochP]

/-- `Sp'` of `1/(q^m x^{v₀} s; q)_∞`. -/
def Aser (v : D4K.V) (m : ℕ) : PowerSeries L := Sp' (EInv' (X ^ (2 * m)) v 1 one_ne_zero)

theorem Aser_succ (v : D4K.V) (m : ℕ) :
    Aser v m * (1 - PowerSeries.C (mono (v 0)) * X ^ (2 * m + 1)) = Aser v (m + 1) := by
  have h := congrArg Sp' (EInv'_mul_one_sub (X ^ (2 * m)) v)
  rw [map_mul, map_sub, map_one, ← pow_one (X : PowerSeries R'), Sp'_C_mul_X_pow, map_cst_X_pow,
    ← pow_add, show 2 + 2 * m = 2 * (m + 1) by ring] at h
  rw [Aser, Aser, ← h]
  congr 2; ring

theorem Aser_agree (v : D4K.V) (m : ℕ) : AgreeTo (m + 1) (Aser v m) 1 := by
  apply diag_agree
  · rw [coeff_map, coeff_EInv'_one, pow_zero, qpochP_zero, inv_one, mul_one, zero_smul, ψ_single,
      map_one, Pi.zero_apply, mono_zero]
    simp
  · intro n _
    rw [coeff_map, coeff_EInv'_one, ψ_single, ← pow_mul, map_mul, map_cst_X_pow]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (pow_dvd_pow _ (by nlinarith)) _) _

theorem pfAv (j : ℤ) : ProdFactors fun k => (1 : PowerSeries L) - PowerSeries.C (mono j) * X ^ (2 * k + 1) :=
  pf_sub _ _ fun k => by omega

theorem Aser_prod (v : D4K.V) (K : ℕ) :
    Aser v 0 * ∏ k ∈ Finset.range K, (1 - PowerSeries.C (mono (v 0)) * X ^ (2 * k + 1)) = Aser v K := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.prod_range_succ, ← mul_assoc, ih, Aser_succ]

/-- **`Sp'` of the hypermultiplet factor**: `Sp'(1/(x^{v₀} s; q)_∞) · (x^{v₀} r; r²)_∞ = 1`. -/
theorem Sp'_EInv' (v : D4K.V) :
    Sp' (EInv' 1 v 1 one_ne_zero) * infProd (fun k => 1 - PowerSeries.C (mono (v 0)) * X ^ (2 * k + 1)) = 1 := by
  apply eq_of_agreeTo
  intro K
  have h0 : Sp' (EInv' 1 v 1 one_ne_zero) = Aser v 0 := by rw [Aser, mul_zero, pow_zero]
  rw [h0]
  refine ((agreeTo_infProd (pfAv (v 0)) K).mul_left _).trans ?_
  rw [Aser_prod]
  exact Aser_agree v K

/-- `Sp'` of `(q^m x^{v₀} s²; q)_∞`. -/
def Bser (v : D4K.V) (m : ℕ) : PowerSeries L := Sp' (EPos' (X ^ (2 * m)) v 2 two_ne_zero)

theorem Bser_eq (v : D4K.V) (m : ℕ) :
    Bser v m = (1 - PowerSeries.C (mono (v 0)) * X ^ (2 * m + 2)) * Bser v (m + 1) := by
  have h := congrArg Sp' (EPos'_eq (X ^ (2 * m)) v)
  rw [map_mul, map_sub, map_one, Sp'_C_mul_X_pow, map_cst_X_pow, ← pow_add,
    show 2 + 2 * m = 2 * (m + 1) by ring] at h
  rw [Bser, Bser, h]
  congr 2; ring

theorem Bser_agree (v : D4K.V) (m : ℕ) : AgreeTo (m + 1) (Bser v m) 1 := by
  apply diag_agree
  · rw [coeff_map, coeff_EPos'_two, if_pos (dvd_zero 2), Nat.zero_div, pow_zero, zero_smul, ψ_single, ePosP,
      coeff_mk, qpochP_zero, Pi.zero_apply, mono_zero]
    simp
  · intro n _
    rw [coeff_map, coeff_EPos'_two]
    split_ifs with h2
    · obtain ⟨t, rfl⟩ := h2
      rw [Nat.mul_div_cancel_left _ (by norm_num), ψ_single, ← pow_mul, map_mul, map_cst_X_pow]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (pow_dvd_pow _ (by nlinarith)) _) _
    · rw [map_zero]; exact dvd_zero _

theorem pfBv (j : ℤ) : ProdFactors fun k => (1 : PowerSeries L) - PowerSeries.C (mono j) * X ^ (2 * k + 2) :=
  pf_sub _ _ fun k => by omega

theorem Bser_prod (v : D4K.V) (K : ℕ) :
    Bser v 0 = (∏ k ∈ Finset.range K, (1 - PowerSeries.C (mono (v 0)) * X ^ (2 * k + 2))) * Bser v K := by
  induction K with
  | zero => simp
  | succ K ih => rw [ih, Bser_eq v K, Finset.prod_range_succ]; ring

/-- **`Sp'` of the vector-multiplet factor**: `Sp'((x^{v₀} s²; q)_∞) = (x^{v₀} r²; r²)_∞`. -/
theorem Sp'_EPos' (v : D4K.V) :
    Sp' (EPos' 1 v 2 two_ne_zero) = infProd fun k => 1 - PowerSeries.C (mono (v 0)) * X ^ (2 * k + 2) := by
  apply eq_of_agreeTo
  intro K
  have h0 : Sp' (EPos' 1 v 2 two_ne_zero) = Bser v 0 := by rw [Bser, mul_zero, pow_zero]
  rw [h0, Bser_prod v K]
  refine (((Bser_agree v K).mul_left _).trans ?_).trans (agreeTo_infProd (pfBv (v 0)) K).symm
  rw [mul_one]
  exact AgreeTo.refl _ _

theorem hyperVecs_x : D4K.hyperVecs.map (fun v => v 0) = [1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1] := by
  decide

theorem Sp'_tFactors' : Sp' tFactors' = Mnum := by
  rw [tFactors', map_mul, map_mul, Sp'_EPos', Sp'_EPos', Sp'_EPos', Mnum, etaR, Uq]
  have e0 : ((0 : D4K.V) 0) = 0 := rfl
  have e2 : ((2 • D4K.xv : D4K.V) 0) = 2 := by decide
  have e2' : ((-2 • D4K.xv : D4K.V) 0) = -2 := by decide
  rw [e0, e2, e2', mono_zero, map_one, mul_assoc, infProd_mul (pfBv 2) (pfBv (-2))]
  congr 1
  all_goals first | exact infProd_congr fun k => by ring | exact infProd_congr fun k => by rw [uf]

theorem Sp'_hyperFactors' : Sp' hyperFactors' * Den ^ 8 = 1 := by
  rw [hyperFactors', map_list_prod, List.map_map, Den_eq]
  have hD : ∀ v ∈ D4K.hyperVecs, (Sp' ∘ fun v => EInv' 1 v 1 one_ne_zero) v *
      infProd (fun k => 1 - PowerSeries.C (mono (v 0)) * X ^ (2 * k + 1)) = 1 :=
    fun v _ => Sp'_EInv' v
  have hprod : (D4K.hyperVecs.map fun v => infProd (fun k =>
      (1 : PowerSeries L) - PowerSeries.C (mono (v 0)) * X ^ (2 * k + 1))).prod = Pa ^ 8 * Pc ^ 8 := by
    rw [show (fun v : D4K.V => infProd (fun k =>
        (1 : PowerSeries L) - PowerSeries.C (mono (v 0)) * X ^ (2 * k + 1))) =
        (fun j : ℤ => infProd (fun k => (1 : PowerSeries L) - PowerSeries.C (mono j) * X ^ (2 * k + 1))) ∘
          (fun v : D4K.V => v 0) from rfl, ← List.map_map, hyperVecs_x]
    simp [Pa, Pc, List.prod_cons]
    ring
  rw [mul_pow, ← hprod, ← List.prod_map_mul]
  exact List.prod_eq_one fun x hx => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    exact hD v hv

/-- **The specialised kernel**: `Sp'(M) · Den⁸ = M_num`. -/
theorem Sp'_kernelM' : Sp' kernelM' * Den ^ 8 = Mnum := by
  rw [kernelM', map_mul, mul_assoc, Sp'_hyperFactors', mul_one, Sp'_tFactors']

end

end VOA.DeligneAudit.DeligneCharacter.D4Wp
