/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Wp10

/-!
# The constant-term functional on the integral kernel (layer 11)

`ctP f = ∑_v f(v) θ(-v₀)` with `θ` the integral theta coefficients `thP`; then
`ev1 (ctTheta (ιR f)) = coeK (ctP f)` (`ev1_ctTheta_ιR`).
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4Wp

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

/-- Integral theta coefficients: `θ_{2k} = (-1)^k (q^{T(k)} + q^{T(k+1)})`, `θ_odd = 0`, `q = r²`. -/
def thP (i : ℤ) : P :=
  if Even i then (-1) ^ (i / 2).natAbs * ((X ^ 2) ^ triC (i / 2) + (X ^ 2) ^ triC (i / 2 + 1)) else 0

theorem coeK_thP (i : ℤ) : coeK (thP i) = D4K.thK i := by
  rw [thP, D4K.thK]
  split_ifs
  · simp only [map_mul, map_add, map_pow, map_neg, map_one]
    rw [← map_pow, coeK_X_sq, D4K.sgn, D4K.qC, D4K.qC, zpow_natCast, zpow_natCast]
  · rw [map_zero]

/-- `f ↦ ∑_v f(v) θ(-v₀)`. -/
def ctP (f : R') : P := f.sum fun v c => c * thP (-(v 0))

theorem ctP_add (f g : R') : ctP (f + g) = ctP f + ctP g :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem ctP_single (v : D4K.V) (c : P) : ctP (AddMonoidAlgebra.single v c) = c * thP (-(v 0)) :=
  Finsupp.sum_single_index (zero_mul _)

theorem ctP_zero : ctP 0 = 0 := Finsupp.sum_zero_index

theorem ev1_ctTheta_ιR (f : R') : D4K.ev1 (D4K.ctTheta (ιR f)) = coeK (ctP f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, ctP_zero, map_zero]
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg, ctP_add, map_add]
  | single v c =>
      rw [ιR_single, D4K.ctFun_mon, D4K.ev1_mon, ctP_single, map_mul, coeK_thP]

/-! ## The theta factor `Θ(x)` on the `x`-annulus -/

/-- `Ψ(x²)` with `q = r²`. -/
def E2Psi : PowerSeries L := expand 2 two_ne_zero (PowerSeries.map (embL dbl) Psi)

theorem expand_Vp : expand 2 two_ne_zero Vp = Uq := by
  rw [Vp, expand_infProd 2 two_ne_zero pf_sqf, Uq]
  refine infProd_congr fun k => ?_
  rw [sqf, uf, map_mul, map_sub, map_sub, map_one, map_mul, map_mul, expand_C, expand_C, map_pow, expand_X,
    ← pow_mul]
  ring_nf

theorem expand_eta : expand 2 two_ne_zero eta = etaR := by
  rw [eta, expand_infProd 2 two_ne_zero pf_eta, etaR]
  refine infProd_congr fun k => ?_
  rw [map_sub, map_one, map_pow, expand_X, ← pow_mul]
  ring_nf

theorem ThX_eq : ThX = (1 - PowerSeries.C (mono (-2))) * E2Psi := by
  rw [ThX, E2Psi, map_dbl_Psi, map_mul, map_mul, expand_Vp, expand_eta, map_sub, map_one, expand_C]
  ring

theorem L_sum_apply {ι : Type*} (s : Finset ι) (f : ι → L) (i : ℤ) :
    (∑ x ∈ s, f x) i = ∑ x ∈ s, (f x) i := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, L_add_apply, ih]

theorem negSign_mul_apply (j : ℤ) (f : L) (i : ℤ) :
    ((negSign j : L) * f) i = (negSign j : ℚ) * f i := by
  rw [negSign_eq, negSign_eq]
  split_ifs
  · rw [one_mul, one_mul]
  · rw [neg_one_mul, neg_one_mul]; rfl

theorem coeff_map_dbl_Psi (b : ℕ) (i : ℤ) :
    (coeff b (PowerSeries.map (embL dbl) Psi)) i =
      if Even i ∧ pentExp (i / 2) = b then (negSign (i / 2) : ℚ) else 0 := by
  rw [coeff_map, Psi, coeff_lat, map_sum, L_sum_apply]
  simp only [map_mul, embL_negSign, embL_mono, negSign_mul_apply, mono_apply]
  have hdbl : ∀ j, dbl j = 2 * j := fun j => by simp [dbl]; ring
  simp only [hdbl]
  split_ifs with h
  · rw [Finset.sum_eq_single (i / 2)]
    · rw [if_pos (by obtain ⟨t, ht⟩ := h.1; omega), mul_one]
    · intro j _ hj; rw [if_neg (by intro h'; apply hj; omega), mul_zero]
    · intro hn; exfalso; exact hn ((mem_fib hbox_pent).mpr h.2)
  · refine Finset.sum_eq_zero fun j hj => ?_
    rw [if_neg, mul_zero]
    intro h'
    apply h
    refine ⟨⟨j, by omega⟩, ?_⟩
    rw [mem_fib hbox_pent] at hj
    rw [show i / 2 = j by omega]; exact hj

theorem mono_mul_apply (k : ℤ) (f : L) (i : ℤ) : (mono k * f) i = f (i - k) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [mul_zero]; rfl
  | add f g hf hg => rw [mul_add, L_add_apply, hf, hg, L_add_apply]
  | single j c =>
      rw [mono, AddMonoidAlgebra.single_mul_single, one_mul]
      show (Finsupp.single (k + j) c) i = (Finsupp.single j c) (i - k)
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> first | rfl | (exfalso; omega)

theorem coeff_E2Psi (a : ℕ) (i : ℤ) : (coeff a E2Psi) i =
    if Even i ∧ 2 * pentExp (i / 2) = a then (negSign (i / 2) : ℚ) else 0 := by
  rw [E2Psi, coeff_expand]
  split_ifs with h1 h2 h2
  · rw [coeff_map_dbl_Psi, if_pos ⟨h2.1, by omega⟩]
  · rw [coeff_map_dbl_Psi, if_neg (by intro h; exact h2 ⟨h.1, by omega⟩)]
  · exfalso; exact h1 ⟨_, h2.2.symm⟩
  · rfl

theorem coeff_X_sq_pow (t a : ℕ) : coeff a (((X : P) ^ 2) ^ t) = if a = 2 * t then 1 else 0 := by
  rw [← pow_mul, coeff_X_pow]

/-- **The `x^i`-coefficient of `Θ` is `θ_i`.** -/
theorem coeff_ThX (a : ℕ) (i : ℤ) : (coeff a ThX) i = coeff a (thP i) := by
  rw [ThX_eq, sub_mul, one_mul, map_sub, coeff_C_mul, L_sub_apply, mono_mul_apply, coeff_E2Psi, coeff_E2Psi,
    thP]
  by_cases hi : Even i
  · obtain ⟨j, rfl⟩ := hi
    have e1 : (j + j) / 2 = j := by omega
    have e2 : (j + j - -2) / 2 = j + 1 := by omega
    have ev2 : Even (j + j - -2) := ⟨j + 1, by ring⟩
    have ev1 : Even (j + j) := ⟨j, rfl⟩
    simp only [e1, e2, ev1, ev2, true_and, if_true]
    have hc : ((-1 : P)) ^ j.natAbs = PowerSeries.C ((-1 : ℚ) ^ j.natAbs) := by
      rw [map_pow, map_neg, map_one]
    rw [hc, coeff_C_mul, map_add, coeff_X_sq_pow, coeff_X_sq_pow]
    have hn : (negSign (j + 1) : ℚ) = -negSign j := by rw [negSign_add]; simp [negSign]
    rw [hn, show (negSign j : ℚ) = (-1) ^ j.natAbs from rfl]
    simp only [triC, pentExp]
    simp only [@eq_comm ℕ a]
    split_ifs <;> ring
  · have hi2 : ¬ Even (i - -2) := by
      intro h; apply hi; obtain ⟨t, ht⟩ := h; exact ⟨t - 1, by omega⟩
    rw [if_neg (fun h => hi h.1), if_neg (fun h => hi2 h.1), if_neg hi, map_zero, sub_zero]

/-! ## `CT_x(Θ · Sp' F)` -/

theorem ctx_add (F G : PowerSeries L) : ctx (F + G) = ctx F + ctx G := by
  ext n : 1; simp only [ctx, coeff_mk, map_add, L_add_apply]

theorem ctx_zero : ctx 0 = 0 := by ext n : 1; simp only [ctx, coeff_mk, map_zero]; rfl

theorem ctx_map_cst_mul (p : P) (G : PowerSeries L) : ctx (PowerSeries.map cst p * G) = p * ctx G := by
  ext n : 1
  rw [ctx, coeff_mk, coeff_mul, coeff_mul, L_sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map, cst_mul_apply, ctx, coeff_mk]

theorem ctx_X_pow_mul (k : ℕ) (G : PowerSeries L) : ctx (X ^ k * G) = X ^ k * ctx G := by
  ext n : 1
  rw [ctx, coeff_mk, coeff_X_pow_mul', coeff_X_pow_mul']
  split_ifs
  · rw [ctx, coeff_mk]
  · rfl

theorem ctx_ThX_mono (j : ℤ) : ctx (ThX * PowerSeries.C (mono j)) = thP (-j) := by
  ext a : 1
  rw [ctx, coeff_mk, mul_comm, coeff_C_mul, mono_mul_apply, zero_sub, coeff_ThX]

theorem ctx_agree {K : ℕ} {F G : PowerSeries L} (h : AgreeTo K F G) : AgreeTo K (ctx F) (ctx G) :=
  AgreeTo.of_coeff fun n hn => by rw [ctx, ctx, coeff_mk, coeff_mk, h.coeff_eq hn]

theorem diagS_agree {A : Type*} [CommRing A] {K : ℕ} {G H : PowerSeries (PowerSeries A)}
    (h : AgreeTo K G H) : AgreeTo K (diagS G) (diagS H) :=
  AgreeTo.of_coeff fun n hn => by
    rw [coeff_diagS, coeff_diagS]
    exact Finset.sum_congr rfl fun k hk => by
      rw [h.coeff_eq (by rw [Finset.mem_range] at hk; omega)]

/-- `F ↦ ∑ rᵏ ctP(Fₖ)`. -/
def rhsCT (F : PowerSeries R') : P := diagS (PowerSeries.mk fun k => ctP (coeff k F))

theorem rhsCT_add (F G : PowerSeries R') : rhsCT (F + G) = rhsCT F + rhsCT G := by
  rw [rhsCT, rhsCT, rhsCT, ← diagS_add]
  congr 1; ext k : 1; simp [ctP_add]

theorem rhsCT_zero : rhsCT 0 = 0 := by
  rw [rhsCT]; ext n : 1; simp [coeff_diagS, ctP_zero]

/-- `F ↦ CT_x(Θ · Sp' F)`. -/
def lhsCT (F : PowerSeries R') : P := ctx (ThX * Sp' F)

theorem lhsCT_add (F G : PowerSeries R') : lhsCT (F + G) = lhsCT F + lhsCT G := by
  rw [lhsCT, lhsCT, lhsCT, map_add, mul_add, ctx_add]

theorem lhsCT_zero : lhsCT 0 = 0 := by rw [lhsCT, map_zero, mul_zero, ctx_zero]

def lhsHom : PowerSeries R' →+ P := ⟨⟨lhsCT, lhsCT_zero⟩, lhsCT_add⟩
def rhsHom : PowerSeries R' →+ P := ⟨⟨rhsCT, rhsCT_zero⟩, rhsCT_add⟩

theorem lhs_monomial (v : D4K.V) (p : P) (k : ℕ) :
    lhsCT (PowerSeries.C (AddMonoidAlgebra.single v p) * X ^ k) = p * thP (-(v 0)) * X ^ k := by
  rw [lhsCT, Sp'_C_mul_X_pow, show ThX * (PowerSeries.map cst p * PowerSeries.C (mono (v 0)) * X ^ k) =
    PowerSeries.map cst p * (X ^ k * (ThX * PowerSeries.C (mono (v 0)))) by ring,
    ctx_map_cst_mul, ctx_X_pow_mul, ctx_ThX_mono]
  ring

theorem rhs_monomial (v : D4K.V) (p : P) (k : ℕ) :
    rhsCT (PowerSeries.C (AddMonoidAlgebra.single v p) * X ^ k) = p * thP (-(v 0)) * X ^ k := by
  rw [rhsCT, show (PowerSeries.mk fun n => ctP (coeff n (PowerSeries.C (AddMonoidAlgebra.single v p) * X ^ k))) =
      PowerSeries.C (p * thP (-(v 0))) * X ^ k by
    ext n : 1
    rw [coeff_mk, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    split_ifs
    · rw [ctP_single]
    · exact ctP_zero, diagS_C_mul_X_pow]

/-- Truncation of an `R'`-series as a finite sum of monomials. -/
def trR (K : ℕ) (F : PowerSeries R') : PowerSeries R' :=
  ∑ x ∈ (Finset.range K).sigma (fun n => (coeff n F).support),
    PowerSeries.C (AddMonoidAlgebra.single x.2 ((coeff x.1 F) x.2)) * X ^ x.1

theorem R'_sum_single (f : R') : ∑ v ∈ f.support, AddMonoidAlgebra.single v (f v) = f := by
  show (Finsupp.sum (f : D4K.V →₀ P) Finsupp.single) = f
  exact Finsupp.sum_single f

theorem agree_trR (K : ℕ) (F : PowerSeries R') : AgreeTo K F (trR K F) := by
  apply AgreeTo.of_coeff
  intro m hm
  rw [trR, map_sum, Finset.sum_sigma, Finset.sum_eq_single m]
  · simp only [coeff_C_mul_X_pow, if_true]
    exact (R'_sum_single _).symm
  · intro b _ hb
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [coeff_C_mul_X_pow, if_neg (Ne.symm hb)]
  · intro h; exfalso; exact h (Finset.mem_range.mpr hm)

theorem lhs_agree {K : ℕ} {F G : PowerSeries R'} (h : AgreeTo K F G) : AgreeTo K (lhsCT F) (lhsCT G) := by
  rw [lhsCT, lhsCT]
  refine ctx_agree (AgreeTo.mul_left _ ?_)
  rw [Sp', RingHom.comp_apply, RingHom.comp_apply]
  exact diagS_agree (h.map (PowerSeries.map ψ) (by rw [map_pow, PowerSeries.map_X]))

theorem rhs_agree {K : ℕ} {F G : PowerSeries R'} (h : AgreeTo K F G) : AgreeTo K (rhsCT F) (rhsCT G) := by
  rw [rhsCT, rhsCT]
  refine diagS_agree (AgreeTo.of_coeff fun n hn => ?_)
  rw [coeff_mk, coeff_mk, h.coeff_eq hn]

/-- **`CT_x(Θ · Sp' F) = ∑_k rᵏ ctP(F_k)`.** -/
theorem lhsCT_eq_rhsCT (F : PowerSeries R') : lhsCT F = rhsCT F := by
  apply eq_of_agreeTo
  intro K
  have h := agree_trR (K + 1) F
  refine (lhs_agree h).trans (AgreeTo.of_eq ?_) |>.trans (rhs_agree h).symm
  change lhsHom (trR (K + 1) F) = rhsHom (trR (K + 1) F)
  rw [trR, map_sum, map_sum]
  exact Finset.sum_congr rfl fun x _ => by
    change lhsCT _ = rhsCT _
    rw [lhs_monomial, rhs_monomial]

end

end VOA.DeligneAudit.DeligneCharacter.D4Wp
