/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Wp

/-!
# The half-period substitution `a = x/r`, `q = r²` (layer 4)

`tau : L⟦q⟧ → L⟦r⟧`, `a^j qⁿ ↦ x^j r^{2n-j}` (same carrier type: `L = ℚ[x^{±1}]`).  It is additive,
commutes with `D = x d/dx` (`tau_Da`), and is multiplicative on series supported in `j ≤ n`
(`SC`, `tau_mul`); it carries infinite products of such factors to infinite products
(`tau_infProd`).
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4Wp

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

/-- `a^j qⁿ ↦ x^j r^{2n-j}`. -/
def tau (F : PowerSeries L) : PowerSeries L :=
  PowerSeries.mk fun m => ∑ n ∈ Finset.range (m + 1),
    AddMonoidAlgebra.single (2 * (n : ℤ) - m) ((coeff n F) (2 * (n : ℤ) - m))

theorem coeff_tau (F : PowerSeries L) (m : ℕ) :
    coeff m (tau F) = ∑ n ∈ Finset.range (m + 1),
      AddMonoidAlgebra.single (2 * (n : ℤ) - m) ((coeff n F) (2 * (n : ℤ) - m)) := coeff_mk _ _

theorem L_add_apply (f g : L) (i : ℤ) : (f + g) i = f i + g i := rfl
theorem L_zero_apply (i : ℤ) : (0 : L) i = 0 := rfl

theorem tau_add (F G : PowerSeries L) : tau (F + G) = tau F + tau G := by
  ext m : 1
  rw [map_add, coeff_tau, coeff_tau, coeff_tau, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by rw [map_add, L_add_apply, AddMonoidAlgebra.single_add]

theorem tau_zero : tau 0 = 0 := by
  ext m : 1
  rw [coeff_tau, map_zero]
  exact Finset.sum_eq_zero fun n _ => by rw [map_zero, L_zero_apply, AddMonoidAlgebra.single_zero]

/-- `tau` as an additive map. -/
def tauHom : PowerSeries L →+ PowerSeries L := ⟨⟨tau, tau_zero⟩, tau_add⟩

theorem tau_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries L) :
    tau (∑ i ∈ s, f i) = ∑ i ∈ s, tau (f i) := map_sum tauHom f s

/-- The support condition `j ≤ n`. -/
def SC (F : PowerSeries L) : Prop := ∀ (n : ℕ) (j : ℤ), (n : ℤ) < j → (coeff n F) j = 0

theorem tau_monomial (j : ℤ) (c : ℚ) (n : ℕ) (hj : j ≤ n) :
    tau (PowerSeries.C (AddMonoidAlgebra.single j c) * X ^ n) =
      PowerSeries.C (AddMonoidAlgebra.single j c) * X ^ (2 * (n : ℤ) - j).toNat := by
  ext m : 1
  rw [coeff_tau, coeff_C_mul_X_pow]
  simp only [coeff_C_mul_X_pow]
  split_ifs with hm
  · rw [Finset.sum_eq_single n]
    · rw [if_pos rfl]
      have : 2 * (n : ℤ) - m = j := by omega
      rw [this, Finsupp.single_eq_same]
    · intro b _ hb; rw [if_neg hb, L_zero_apply, AddMonoidAlgebra.single_zero]
    · intro hn; exfalso; rw [Finset.mem_range] at hn; omega
  · refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hb
    · subst hb
      rw [Finsupp.single_apply, if_neg (by omega), AddMonoidAlgebra.single_zero]
    · rw [L_zero_apply, AddMonoidAlgebra.single_zero]

theorem tau_agree {K : ℕ} {F G : PowerSeries L} (h : AgreeTo K F G) : AgreeTo K (tau F) (tau G) :=
  AgreeTo.of_coeff fun m hm => by
    rw [coeff_tau, coeff_tau]
    exact Finset.sum_congr rfl fun n hn => by
      rw [h.coeff_eq (by rw [Finset.mem_range] at hn; omega)]

theorem L_sum_single (f : L) : ∑ j ∈ f.support, AddMonoidAlgebra.single j (f j) = f := by
  show (Finsupp.sum (f : ℤ →₀ ℚ) Finsupp.single) = f
  exact Finsupp.sum_single f

/-- Finite truncation as a sum of monomials. -/
def trS (K : ℕ) (F : PowerSeries L) : PowerSeries L :=
  ∑ p ∈ (Finset.range K).sigma (fun n => (coeff n F).support),
    PowerSeries.C (AddMonoidAlgebra.single p.2 ((coeff p.1 F) p.2)) * X ^ p.1

theorem agree_trS (K : ℕ) (F : PowerSeries L) : AgreeTo K F (trS K F) := by
  apply AgreeTo.of_coeff
  intro m hm
  rw [trS, map_sum, Finset.sum_sigma]
  rw [Finset.sum_eq_single m]
  · simp only [coeff_C_mul_X_pow, if_true]
    exact (L_sum_single _).symm
  · intro b _ hb
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [coeff_C_mul_X_pow, if_neg (Ne.symm hb)]
  · intro h; exfalso; exact h (Finset.mem_range.mpr hm)

theorem tau_mul_trS (K : ℕ) (F G : PowerSeries L) (hF : SC F) (hG : SC G) :
    tau (trS K F * trS K G) = tau (trS K F) * tau (trS K G) := by
  rw [trS, trS, Finset.sum_mul_sum]
  simp only [tau_sum]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun p' hp' => ?_
  rw [Finset.mem_sigma, Finsupp.mem_support_iff] at hp hp'
  have h1 : p.2 ≤ p.1 := by
    by_contra h; exact hp.2 (hF _ _ (by omega))
  have h2 : p'.2 ≤ p'.1 := by
    by_contra h; exact hp'.2 (hG _ _ (by omega))
  rw [show PowerSeries.C (AddMonoidAlgebra.single p.2 ((coeff p.1 F) p.2)) * X ^ p.1 *
      (PowerSeries.C (AddMonoidAlgebra.single p'.2 ((coeff p'.1 G) p'.2)) * X ^ p'.1) =
      PowerSeries.C (AddMonoidAlgebra.single (p.2 + p'.2) ((coeff p.1 F) p.2 * (coeff p'.1 G) p'.2)) *
        X ^ (p.1 + p'.1) by
    rw [← AddMonoidAlgebra.single_mul_single, map_mul, pow_add]; ring]
  rw [tau_monomial _ _ _ (by push_cast; omega), tau_monomial _ _ _ h1, tau_monomial _ _ _ h2,
    ← AddMonoidAlgebra.single_mul_single, map_mul]
  rw [show (2 * ((p.1 + p'.1 : ℕ) : ℤ) - (p.2 + p'.2)).toNat =
    (2 * (p.1 : ℤ) - p.2).toNat + (2 * (p'.1 : ℤ) - p'.2).toNat by push_cast; omega, pow_add]
  ring

/-- **`tau` is multiplicative on `SC` series.** -/
theorem tau_mul (F G : PowerSeries L) (hF : SC F) (hG : SC G) : tau (F * G) = tau F * tau G := by
  apply eq_of_agreeTo
  intro K
  have hF' := agree_trS (K + 1) F
  have hG' := agree_trS (K + 1) G
  refine (tau_agree (hF'.mul hG')).trans ?_
  rw [tau_mul_trS _ _ _ hF hG]
  exact ((tau_agree hF').mul (tau_agree hG')).symm

/-! ## Support condition: closure -/

/-- `f` is supported in degrees `≤ a`. -/
def Supp (f : L) (a : ℤ) : Prop := ∀ j, a < j → f j = 0

theorem Supp_mul {f g : L} {a b : ℤ} (hf : Supp f a) (hg : Supp g b) : Supp (f * g) (a + b) := by
  intro j hj
  by_contra h
  have hs : j ∈ (f * g).support := Finsupp.mem_support_iff.mpr h
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (AddMonoidAlgebra.support_mul f g hs)
  rw [Finsupp.mem_support_iff] at hx hy
  by_cases hxa : a < x
  · exact hx (hf x hxa)
  · exact hy (hg y (by omega))

theorem Supp_add {f g : L} {a : ℤ} (hf : Supp f a) (hg : Supp g a) : Supp (f + g) a := by
  intro j hj; rw [L_add_apply, hf j hj, hg j hj, add_zero]

theorem Supp_zero (a : ℤ) : Supp 0 a := fun _ _ => rfl

theorem Supp_sum {ι : Type*} (s : Finset ι) (f : ι → L) (a : ℤ) (h : ∀ i ∈ s, Supp (f i) a) :
    Supp (∑ i ∈ s, f i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Supp_zero a
  | insert x s hx ih =>
      rw [Finset.sum_insert hx]
      exact Supp_add (h x (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem SC_iff (F : PowerSeries L) : SC F ↔ ∀ n : ℕ, Supp (coeff n F) n := Iff.rfl

theorem SC_mul {F G : PowerSeries L} (hF : SC F) (hG : SC G) : SC (F * G) := by
  intro n j hj
  rw [coeff_mul]
  refine Supp_sum _ _ n (fun p hp => ?_) j hj
  have := Supp_mul (hF p.1) (hG p.2)
  rw [Finset.mem_antidiagonal] at hp
  rwa [show ((p.1 : ℕ) : ℤ) + p.2 = n by rw [← hp]; push_cast; ring] at this

theorem SC_add {F G : PowerSeries L} (hF : SC F) (hG : SC G) : SC (F + G) := fun n j hj => by
  rw [map_add, L_add_apply, hF n j hj, hG n j hj, add_zero]

theorem SC_neg {F : PowerSeries L} (hF : SC F) : SC (-F) := fun n j hj => by
  rw [map_neg, show ((-coeff n F : L) j) = -(coeff n F j) from rfl, hF n j hj, neg_zero]

theorem SC_sub {F G : PowerSeries L} (hF : SC F) (hG : SC G) : SC (F - G) := by
  rw [sub_eq_add_neg]; exact SC_add hF (SC_neg hG)

theorem SC_C_mul_X_pow (j : ℤ) (c : ℚ) (n : ℕ) (hj : j ≤ n) :
    SC (PowerSeries.C (AddMonoidAlgebra.single j c) * X ^ n) := by
  intro m i hi
  rw [coeff_C_mul_X_pow]
  split_ifs with h
  · subst h; rw [Finsupp.single_apply, if_neg (by omega)]
  · rfl

theorem SC_one : SC (1 : PowerSeries L) := by
  have h := SC_C_mul_X_pow 0 1 0 le_rfl
  rwa [pow_zero, mul_one, show AddMonoidAlgebra.single (0 : ℤ) (1 : ℚ) = (1 : L) from rfl, map_one] at h

theorem SC_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries L) (h : ∀ i ∈ s, SC (f i)) :
    SC (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact SC_one
  | insert x s hx ih =>
      rw [Finset.prod_insert hx]
      exact SC_mul (h x (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem SC_infProd (f : ℕ → PowerSeries L) (h : ∀ k, SC (f k)) : SC (infProd f) := by
  intro n j hj
  rw [infProd, coeff_mk]
  exact SC_prod _ _ (fun k _ => h k) n j hj

theorem tau_one : tau 1 = 1 := by
  have h := tau_monomial 0 1 0 le_rfl
  rwa [pow_zero, mul_one, show AddMonoidAlgebra.single (0 : ℤ) (1 : ℚ) = (1 : L) from rfl, map_one,
    show (2 * ((0 : ℕ) : ℤ) - 0).toNat = 0 by rfl, pow_zero, mul_one] at h

theorem tau_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries L) (h : ∀ i ∈ s, SC (f i)) :
    tau (∏ i ∈ s, f i) = ∏ i ∈ s, tau (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, tau_one]
  | insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.prod_insert hx,
        tau_mul _ _ (h x (Finset.mem_insert_self _ _))
          (SC_prod _ _ fun i hi => h i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/-- **`tau` of an infinite product.** -/
theorem tau_infProd (f : ℕ → PowerSeries L) (hf : ProdFactors f) (h : ∀ k, SC (f k)) :
    tau (infProd f) = infProd fun k => tau (f k) := by
  have hf' : ProdFactors fun k => tau (f k) := fun k => by
    have := tau_agree (hf k); rwa [tau_one] at this
  apply eq_infProd_of_agree hf'
  intro N
  have := tau_agree (agreeTo_infProd hf N)
  rwa [tau_prod _ _ fun k _ => h k] at this

/-! ## `tau` and `D` -/

theorem wd_apply {G : Type*} [AddCommGroup G] (w : G →+ ℤ) (f : AddMonoidAlgebra ℚ G) (g : G) :
    (wd w f) g = (w g : ℚ) * f g := by
  classical
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [wd_zero]; show (0 : ℚ) = (w g : ℚ) * 0; ring
  | add f f' hf hf' =>
      rw [wd_add]
      show (wd w f) g + (wd w f') g = (w g : ℚ) * (f g + f' g)
      rw [hf, hf']; ring
  | single a c =>
      rw [wd_single]
      show (Finsupp.single a ((w a : ℚ) * c)) g = (w g : ℚ) * (Finsupp.single a c) g
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs with h
      · rw [h]
      · ring

theorem tau_Da (F : PowerSeries L) : tau (DQ wa F) = DQ wa (tau F) := by
  ext m : 1
  rw [coeff_DQ, coeff_tau, coeff_tau, wd_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [coeff_DQ, wd_apply, wd_single]

end

end VOA.DeligneAudit.DeligneCharacter.D4Wp
