/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Wp3
import VOA.DeligneAudit.DeligneCharacterD4Wp4

/-!
# Transport of the cubic theta identity to the `x`-annulus (layer 5)

Under `tau` (`a = x/r`, `q = r²`) the identity `eta_C3` becomes

  `C₃(Den) = η(r²)⁶ · r · x⁻¹ · Den(-x) · ϑ(x)ϑ(-x)`  (`C3_Den`),

with `Den(x) = ∏_{k ≥ 0}(1 - x r^{2k+1})(1 - x⁻¹ r^{2k+1})`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4Wp

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

/-! ## Generic product lemmas -/

theorem infProd_succ {R : Type*} [CommRing R] {u : ℕ → PowerSeries R} (hu : ProdFactors u) :
    infProd u = u 0 * infProd (fun k => u (k + 1)) := by
  have hu' : ProdFactors fun k => u (k + 1) := fun k => (hu (k + 1)).mono (by omega)
  symm
  apply eq_infProd_of_agree hu
  intro N
  refine ((agreeTo_infProd hu' N).mul_left (u 0)).trans ?_
  rw [mul_comm (u 0), ← Finset.prod_range_succ' u N]
  exact partialProd_agree hu (by omega)

/-! ## `SC` for the `y`-side factors -/

theorem mono_eq_single (j : ℤ) : mono j = AddMonoidAlgebra.single j 1 := rfl

theorem SC_one_sub (j : ℤ) (n : ℕ) (hj : j ≤ n) :
    SC (1 - PowerSeries.C (mono j) * X ^ n) :=
  SC_sub SC_one (SC_C_mul_X_pow j 1 n hj)

theorem SC_one_add (j : ℤ) (n : ℕ) (hj : j ≤ n) :
    SC (1 + PowerSeries.C (mono j) * X ^ n) :=
  SC_add SC_one (SC_C_mul_X_pow j 1 n hj)

theorem SC_X_pow (n : ℕ) : SC (X ^ n : PowerSeries L) := by
  have h := SC_C_mul_X_pow 0 1 n (by omega)
  rwa [show AddMonoidAlgebra.single (0 : ℤ) (1 : ℚ) = (1 : L) from rfl, map_one, one_mul] at h

theorem SC_one_sub_X (n : ℕ) : SC (1 - X ^ n : PowerSeries L) := SC_sub SC_one (SC_X_pow n)

theorem SC_tripleFactor_ua (k : ℕ) : SC (tripleFactor ua k) := by
  rw [tripleFactor, val_ua, val_ua_inv]
  exact SC_mul (SC_mul (SC_one_sub 1 _ (by omega)) (SC_one_sub (-1) _ (by omega))) (SC_one_sub_X _)

theorem SC_tripleFactor_neg_ua (k : ℕ) : SC (tripleFactor (-ua) k) := by
  rw [tripleFactor, val_neg_ua, val_neg_ua_inv, map_neg, map_neg, neg_mul, neg_mul, sub_neg_eq_add,
    sub_neg_eq_add]
  exact SC_mul (SC_mul (SC_one_add 1 _ (by omega)) (SC_one_add (-1) _ (by omega))) (SC_one_sub_X _)

theorem SC_PiA : SC PiA := SC_infProd _ SC_tripleFactor_ua
theorem SC_PiM : SC PiM := SC_infProd _ SC_tripleFactor_neg_ua

theorem SC_C_mono_neg : SC (PowerSeries.C (mono (-1))) := by
  have h := SC_C_mul_X_pow (-1) 1 0 (by omega)
  rwa [pow_zero, mul_one] at h

/-! ## `tau` on monomial factors -/

theorem tau_neg (F : PowerSeries L) : tau (-F) = -tau F := map_neg tauHom F

theorem tau_sub (F G : PowerSeries L) : tau (F - G) = tau F - tau G := map_sub tauHom F G

theorem tau_C_mono_X_pow (j : ℤ) (n : ℕ) (hj : j ≤ n) :
    tau (PowerSeries.C (mono j) * X ^ n) = PowerSeries.C (mono j) * X ^ (2 * (n : ℤ) - j).toNat :=
  tau_monomial j 1 n hj

theorem tau_X_pow (n : ℕ) : tau (X ^ n : PowerSeries L) = X ^ (2 * n) := by
  have h := tau_monomial 0 1 n (by omega)
  rw [show AddMonoidAlgebra.single (0 : ℤ) (1 : ℚ) = (1 : L) from rfl, map_one, one_mul, one_mul] at h
  rw [h, show (2 * (n : ℤ) - 0).toNat = 2 * n by omega]

theorem tau_one_sub (j : ℤ) (n : ℕ) (hj : j ≤ n) :
    tau (1 - PowerSeries.C (mono j) * X ^ n) = 1 - PowerSeries.C (mono j) * X ^ (2 * (n : ℤ) - j).toNat := by
  rw [tau_sub, tau_one, tau_C_mono_X_pow j n hj]

theorem tau_one_add (j : ℤ) (n : ℕ) (hj : j ≤ n) :
    tau (1 + PowerSeries.C (mono j) * X ^ n) = 1 + PowerSeries.C (mono j) * X ^ (2 * (n : ℤ) - j).toNat := by
  rw [tau_add, tau_one, tau_C_mono_X_pow j n hj]

theorem tau_one_sub_X (n : ℕ) : tau (1 - X ^ n : PowerSeries L) = 1 - X ^ (2 * n) := by
  rw [tau_sub, tau_one, tau_X_pow]

/-! ## Logarithmic derivatives of products (generic) -/

theorem prod_logDeriv' {R : Type*} [CommRing R] (D : PowerSeries R → PowerSeries R)
    (hD : ∀ f g, D (f * g) = D f * g + f * D g) (hD1 : D 1 = 0)
    (f lam : ℕ → PowerSeries R) (h : ∀ m, D (f m) = lam m * f m) (K : ℕ) :
    D (∏ m ∈ Finset.range K, f m) = (∑ m ∈ Finset.range K, lam m) * ∏ m ∈ Finset.range K, f m := by
  induction K with
  | zero => simp [hD1]
  | succ K ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ, hD, ih, h]
      ring

/-- Locally finite sums. -/
def lsum' {R : Type*} [CommRing R] (g : ℕ → PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun k => coeff k (∑ m ∈ Finset.range (k + 1), g m)

theorem coeff_sum_range_of_dvd' {R : Type*} [CommRing R] (g : ℕ → PowerSeries R)
    (hg : ∀ m, (X : PowerSeries R) ^ (m + 1) ∣ g m) {k M : ℕ} (hM : k ≤ M) :
    coeff k (∑ m ∈ Finset.range M, g m) = ∑ m ∈ Finset.range k, coeff k (g m) := by
  rw [map_sum]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hM)
  intro m _ hm
  rw [Finset.mem_range, not_lt] at hm
  exact (PowerSeries.X_pow_dvd_iff.mp (hg m)) k (by omega)

theorem coeff_lsum' {R : Type*} [CommRing R] (g : ℕ → PowerSeries R)
    (hg : ∀ m, (X : PowerSeries R) ^ (m + 1) ∣ g m) (k : ℕ) :
    coeff k (lsum' g) = ∑ m ∈ Finset.range k, coeff k (g m) := by
  rw [lsum', coeff_mk, coeff_sum_range_of_dvd' g hg (by omega)]

theorem agreeTo_lsum' {R : Type*} [CommRing R] (g : ℕ → PowerSeries R)
    (hg : ∀ m, (X : PowerSeries R) ^ (m + 1) ∣ g m) (K : ℕ) :
    AgreeTo (K + 1) (lsum' g) (∑ m ∈ Finset.range K, g m) :=
  AgreeTo.of_coeff fun k hk => by
    rw [coeff_lsum' g hg, coeff_sum_range_of_dvd' g hg (by omega)]

theorem lsum'_neg {R : Type*} [CommRing R] (g : ℕ → PowerSeries R) :
    lsum' (fun m => -g m) = -lsum' g := by
  ext k : 1; simp [lsum', Finset.sum_neg_distrib]

theorem infProd_logDeriv' {R : Type*} [CommRing R] (D : PowerSeries R → PowerSeries R)
    (hD : ∀ f g, D (f * g) = D f * g + f * D g) (hD1 : D 1 = 0)
    (hDa : ∀ K f g, AgreeTo K f g → AgreeTo K (D f) (D g))
    (f lam : ℕ → PowerSeries R) (hf : ProdFactors f)
    (hlam : ∀ m, (X : PowerSeries R) ^ (m + 1) ∣ lam m) (h : ∀ m, D (f m) = lam m * f m) :
    D (infProd f) = lsum' lam * infProd f := by
  apply eq_of_agreeTo
  intro N
  have h1 := hDa _ _ _ (agreeTo_infProd hf N)
  rw [prod_logDeriv' D hD hD1 f lam h N] at h1
  exact h1.trans ((agreeTo_lsum' lam hlam N).mul (agreeTo_infProd hf N)).symm

theorem AgreeTo.DQ' {G : Type*} [AddCommGroup G] (w : G →+ ℤ) {K : ℕ}
    {f g : PowerSeries (AddMonoidAlgebra ℚ G)} (h : AgreeTo K f g) : AgreeTo K (DQ w f) (DQ w g) :=
  AgreeTo.of_coeff fun n hn => by simp [h.coeff_eq hn]

theorem DQ_infProd (f lam : ℕ → PowerSeries L) (hf : ProdFactors f)
    (hlam : ∀ m, (X : PowerSeries L) ^ (m + 1) ∣ lam m) (h : ∀ m, Da (f m) = lam m * f m) :
    Da (infProd f) = lsum' lam * infProd f :=
  infProd_logDeriv' Da (DQ_mul wa) (DQ_one wa) (fun K f g h => AgreeTo.DQ' wa h) f lam hf hlam h

theorem Da_X_pow (n : ℕ) : Da (X ^ n : PowerSeries L) = 0 := by
  ext m : 1
  rw [coeff_DQ, coeff_X_pow]
  split_ifs
  · exact wd_one wa
  · exact wd_zero wa

theorem Da_one_sub_X (n : ℕ) : Da (1 - X ^ n : PowerSeries L) = 0 := by
  show DQ wa (1 - X ^ n) = 0
  rw [DQ_sub, DQ_one, show DQ wa (X ^ n : PowerSeries L) = 0 from Da_X_pow n, sub_zero]

/-- A product of `x`-free factors is `D`-constant. -/
theorem Da_infProd_const (e : ℕ → ℕ) (he : ∀ k, k < e k) :
    Da (infProd fun k => (1 : PowerSeries L) - X ^ e k) = 0 := by
  have hf : ProdFactors fun k => (1 : PowerSeries L) - X ^ e k := by
    have h := pf_sub 1 e he; simpa using h
  rw [DQ_infProd _ (fun _ => 0) hf (fun _ => dvd_zero _) (fun k => by rw [Da_one_sub_X, zero_mul])]
  rw [show lsum' (fun _ : ℕ => (0 : PowerSeries L)) = 0 by ext n : 1; simp [lsum'], zero_mul]

/-! ## The cumulant `C₃` -/

theorem C3_const_mul (c F : PowerSeries L) (hc : DQ wa c = 0) : C3 (c * F) = c ^ 3 * C3 F := by
  rw [C3, C3]
  simp only [Da, DQ_mul, DQ_add, hc, zero_mul, zero_add]
  ring

theorem C3_C_mono_mul (j : ℤ) (F : PowerSeries L) :
    C3 (PowerSeries.C (mono j) * F) = PowerSeries.C (mono j) ^ 3 * C3 F := by
  have hD : DQ wa (PowerSeries.C (mono j)) = PowerSeries.C (cst j) * PowerSeries.C (mono j) := by
    rw [DQ_C, wd_mono, map_mul]
  have hD' : DQ wa (PowerSeries.C (cst j)) = 0 := by
    rw [DQ_C, cst_apply, wd_single, map_zero, Int.cast_zero, zero_mul, AddMonoidAlgebra.single_zero, map_zero]
  have hD0 : DQ wa (0 : PowerSeries L) = 0 := by ext n : 1; simp [wd_zero]
  rw [C3, C3]
  simp only [Da, DQ_mul, DQ_add, hD, hD', hD0]
  ring

/-! ## `tau` of the `y`-side products -/

theorem SC_Da (F : PowerSeries L) (hF : SC F) : SC (Da F) := by
  intro n j hj
  rw [Da, coeff_DQ, wd_apply, hF n j hj, mul_zero]

theorem tau_Da' (F : PowerSeries L) : tau (Da F) = Da (tau F) := tau_Da F

theorem tau_C3 (F : PowerSeries L) (hF : SC F) : tau (C3 F) = C3 (tau F) := by
  have h1 := SC_Da F hF
  have h2 := SC_Da _ h1
  have h3 := SC_Da _ h2
  have e1 : C3 F = F * F * Da (Da (Da F)) - 3 • (F * Da F * Da (Da F)) + 2 • (Da F * (Da F * Da F)) := by
    rw [C3, nsmul_eq_mul, nsmul_eq_mul]; push_cast; ring
  have e2 : C3 (tau F) = tau F * tau F * Da (Da (Da (tau F))) -
      3 • (tau F * Da (tau F) * Da (Da (tau F))) + 2 • (Da (tau F) * (Da (tau F) * Da (tau F))) := by
    rw [C3, nsmul_eq_mul, nsmul_eq_mul]; push_cast; ring
  rw [e1, e2, tau_add, tau_sub]
  change tau _ - tauHom (3 • _) + tauHom (2 • _) = _
  rw [map_nsmul, map_nsmul]
  change tau _ - 3 • tau _ + 2 • tau _ = _
  rw [tau_mul _ _ (SC_mul hF hF) h3, tau_mul _ _ hF hF, tau_mul _ _ (SC_mul hF h1) h2, tau_mul _ _ hF h1,
    tau_mul _ _ h1 (SC_mul h1 h1), tau_mul _ _ h1 h1]
  simp only [tau_Da']

/-- `η(r²) = ∏(1 - r^{2k+2})`. -/
def etaR : PowerSeries L := infProd fun k => 1 - X ^ (2 * k + 2)

theorem tau_eta : tau eta = etaR := by
  rw [eta, tau_infProd _ pf_eta (fun k => SC_one_sub_X _), etaR]
  exact infProd_congr fun k => by rw [tau_one_sub_X]; ring_nf

theorem tau_Jc : tau Jc = -etaR ^ 3 := by
  have hs : SC eta := SC_infProd _ fun k => SC_one_sub_X _
  rw [Jc_eq, tau_neg, pow_three, tau_mul _ _ hs (SC_mul hs hs), tau_mul _ _ hs hs, tau_eta]; ring

theorem SC_C3 (F : PowerSeries L) (hF : SC F) : SC (C3 F) := by
  have h1 := SC_Da F hF
  have h2 := SC_Da _ h1
  have h3 := SC_Da _ h2
  rw [C3, show (3 : PowerSeries L) * F * Da F * Da (Da F) = F * Da F * Da (Da F) + F * Da F * Da (Da F) +
      F * Da F * Da (Da F) by ring,
    show (2 : PowerSeries L) * Da F ^ 3 = Da F ^ 3 + Da F ^ 3 by ring, pow_two, pow_three]
  have hA := SC_mul (SC_mul hF hF) h3
  have hB := SC_mul (SC_mul hF h1) h2
  have hC := SC_mul h1 (SC_mul h1 h1)
  exact SC_add (SC_sub hA (SC_add (SC_add hB hB) hB)) (SC_add hC hC)

theorem Cm_inv : PowerSeries.C (mono (-1)) * PowerSeries.C (mono 1) = (1 : PowerSeries L) := by
  rw [← map_mul, mono_mul]; simp [mono_zero]

/-! ### `Ψ(a)` -/

theorem tau_triple_ua (k : ℕ) : tau (tripleFactor ua k) =
    (1 - PowerSeries.C (mono 1) * X ^ (2 * k + 1)) * (1 - PowerSeries.C (mono (-1)) * X ^ (2 * k + 3)) *
      (1 - X ^ (2 * k + 2)) := by
  rw [tripleFactor, val_ua, val_ua_inv,
    tau_mul _ _ (SC_mul (SC_one_sub 1 _ (by omega)) (SC_one_sub (-1) _ (by omega))) (SC_one_sub_X _),
    tau_mul _ _ (SC_one_sub 1 _ (by omega)) (SC_one_sub (-1) _ (by omega)),
    tau_one_sub 1 (k + 1) (by omega), tau_one_sub (-1) (k + 1) (by omega), tau_one_sub_X,
    show (2 * ((k + 1 : ℕ) : ℤ) - 1).toNat = 2 * k + 1 by omega,
    show (2 * ((k + 1 : ℕ) : ℤ) - -1).toNat = 2 * k + 3 by omega,
    show 2 * (k + 1) = 2 * k + 2 by ring]

def Pa : PowerSeries L := infProd fun k => 1 - PowerSeries.C (mono 1) * X ^ (2 * k + 1)
def Pb : PowerSeries L := infProd fun k => 1 - PowerSeries.C (mono (-1)) * X ^ (2 * k + 3)
def Pc : PowerSeries L := infProd fun k => 1 - PowerSeries.C (mono (-1)) * X ^ (2 * k + 1)

/-- `Den(x) = ∏(1 - x r^{2k+1})(1 - x⁻¹ r^{2k+1})`. -/
def Den : PowerSeries L := infProd fun k =>
  (1 - PowerSeries.C (mono 1) * X ^ (2 * k + 1)) * (1 - PowerSeries.C (mono (-1)) * X ^ (2 * k + 1))

theorem pfA (c : L) : ProdFactors fun k => (1 : PowerSeries L) - PowerSeries.C c * X ^ (2 * k + 1) :=
  pf_sub c _ fun k => by omega
theorem pfB (c : L) : ProdFactors fun k => (1 : PowerSeries L) - PowerSeries.C c * X ^ (2 * k + 3) :=
  pf_sub c _ fun k => by omega
theorem pfE (c : L) : ProdFactors fun k => (1 : PowerSeries L) - X ^ (2 * k + 2) := by
  have h := pf_sub (1 : L) (fun k => 2 * k + 2) (fun k => by show k < 2 * k + 2; omega); simpa using h

theorem tau_PiA : tau PiA = Pa * Pb * etaR := by
  rw [PiA, tau_infProd _ (prodFactors_tripleFactor ua) SC_tripleFactor_ua, Pa, Pb, etaR,
    infProd_mul (pfA _) (pfB _), infProd_mul ((pfA _).mul (pfB _)) (pfE 1)]
  exact infProd_congr tau_triple_ua

theorem Pc_eq : Pc = (1 - PowerSeries.C (mono (-1)) * X) * Pb := by
  rw [Pc, infProd_succ (pfA _), Pb]
  congr 1
  all_goals first | ring | exact infProd_congr fun k => by ring_nf

theorem Den_eq : Den = Pa * Pc := by
  rw [Den, Pa, Pc, infProd_mul (pfA _) (pfA _)]

theorem tau_C_mono_neg : tau (PowerSeries.C (mono (-1))) = PowerSeries.C (mono (-1)) * X := by
  have h := tau_C_mono_X_pow (-1) 0 (by omega)
  rwa [pow_zero, mul_one, show (2 * ((0 : ℕ) : ℤ) - -1).toNat = 1 by rfl, pow_one] at h

/-- `a⁻¹Ψ(a)`. -/
def A1 : PowerSeries L := PowerSeries.C (mono (-1)) * Psi

theorem A1_eq : A1 = (PowerSeries.C (mono (-1)) - 1) * PiA := by
  rw [A1, ← Psi_eq_prod, ← PiA]
  linear_combination (-PiA) * Cm_inv

theorem SC_A1 : SC A1 := by
  rw [A1_eq]; exact SC_mul (SC_sub SC_C_mono_neg SC_one) SC_PiA

theorem tau_A1 : tau A1 = -(etaR * Den) := by
  rw [A1_eq, tau_mul _ _ (SC_sub SC_C_mono_neg SC_one) SC_PiA, tau_sub, tau_one, tau_C_mono_neg, tau_PiA,
    Den_eq, Pc_eq]
  ring

/-! ### `Ψ(-a)` -/

theorem pfA' (c : L) : ProdFactors fun k => (1 : PowerSeries L) + PowerSeries.C c * X ^ (2 * k + 1) :=
  prodFactors_one_add c _ fun k => by omega
theorem pfB' (c : L) : ProdFactors fun k => (1 : PowerSeries L) + PowerSeries.C c * X ^ (2 * k + 3) :=
  prodFactors_one_add c _ fun k => by omega

theorem tau_triple_neg_ua (k : ℕ) : tau (tripleFactor (-ua) k) =
    (1 + PowerSeries.C (mono 1) * X ^ (2 * k + 1)) * (1 + PowerSeries.C (mono (-1)) * X ^ (2 * k + 3)) *
      (1 - X ^ (2 * k + 2)) := by
  rw [tripleFactor, val_neg_ua, val_neg_ua_inv, map_neg, map_neg, neg_mul, neg_mul, sub_neg_eq_add,
    sub_neg_eq_add,
    tau_mul _ _ (SC_mul (SC_one_add 1 _ (by omega)) (SC_one_add (-1) _ (by omega))) (SC_one_sub_X _),
    tau_mul _ _ (SC_one_add 1 _ (by omega)) (SC_one_add (-1) _ (by omega)),
    tau_one_add 1 (k + 1) (by omega), tau_one_add (-1) (k + 1) (by omega), tau_one_sub_X,
    show (2 * ((k + 1 : ℕ) : ℤ) - 1).toNat = 2 * k + 1 by omega,
    show (2 * ((k + 1 : ℕ) : ℤ) - -1).toNat = 2 * k + 3 by omega,
    show 2 * (k + 1) = 2 * k + 2 by ring]

def Qa : PowerSeries L := infProd fun k => 1 + PowerSeries.C (mono 1) * X ^ (2 * k + 1)
def Qb : PowerSeries L := infProd fun k => 1 + PowerSeries.C (mono (-1)) * X ^ (2 * k + 3)
def Qc : PowerSeries L := infProd fun k => 1 + PowerSeries.C (mono (-1)) * X ^ (2 * k + 1)

/-- `Den(-x) = ∏(1 + x r^{2k+1})(1 + x⁻¹ r^{2k+1})`. -/
def Denm : PowerSeries L := infProd fun k =>
  (1 + PowerSeries.C (mono 1) * X ^ (2 * k + 1)) * (1 + PowerSeries.C (mono (-1)) * X ^ (2 * k + 1))

theorem tau_PiM : tau PiM = Qa * Qb * etaR := by
  rw [PiM, tau_infProd _ (prodFactors_tripleFactor (-ua)) SC_tripleFactor_neg_ua, Qa, Qb, etaR,
    infProd_mul (pfA' _) (pfB' _), infProd_mul ((pfA' _).mul (pfB' _)) (pfE 1)]
  exact infProd_congr tau_triple_neg_ua

theorem Qc_eq : Qc = (1 + PowerSeries.C (mono (-1)) * X) * Qb := by
  rw [Qc, infProd_succ (pfA' _), Qb]
  congr 1
  all_goals first | ring | exact infProd_congr fun k => by ring_nf

theorem Denm_eq : Denm = Qa * Qc := by
  rw [Denm, Qa, Qc, infProd_mul (pfA' _) (pfA' _)]

/-- `a⁻¹Ψ(-a)`. -/
def B1 : PowerSeries L := PowerSeries.C (mono (-1)) * Psim

theorem B1_eq : B1 = (PowerSeries.C (mono (-1)) + 1) * PiM := by
  rw [B1, Psim]
  linear_combination PiM * Cm_inv

theorem SC_B1 : SC B1 := by
  rw [B1_eq]; exact SC_mul (SC_add SC_C_mono_neg SC_one) SC_PiM

theorem tau_B1 : tau B1 = etaR * Denm := by
  rw [B1_eq, tau_mul _ _ (SC_add SC_C_mono_neg SC_one) SC_PiM, tau_add, tau_one, tau_C_mono_neg, tau_PiM,
    Denm_eq, Qc_eq]
  ring

/-! ### `E(a)` -/

/-- `a⁻¹E(a)`. -/
def E2 : PowerSeries L := PowerSeries.C (mono (-1)) * Ep

def Ep1 : PowerSeries L := infProd fun k => Ef (k + 1)

theorem Ep_eq : Ep = Ef 0 * Ep1 := infProd_succ pf_Ef

theorem SC_Ef_succ (k : ℕ) : SC (Ef (k + 1)) := by
  rw [Ef]; exact SC_mul (SC_one_sub 2 _ (by omega)) (SC_one_sub (-2) _ (by omega))

theorem E2_eq : E2 = ((PowerSeries.C (mono (-1)) - PowerSeries.C (mono 1) * X) *
    (1 - PowerSeries.C (mono (-2)) * X)) * Ep1 := by
  rw [E2, Ep_eq, Ef]
  have h2 : PowerSeries.C (mono (-1)) * PowerSeries.C (mono 2) = (PowerSeries.C (mono 1) : PowerSeries L) := by
    rw [← map_mul, mono_mul]; norm_num
  linear_combination (-(X * (1 - PowerSeries.C (mono (-2)) * X) * Ep1)) * h2

theorem SC_E2a : SC ((PowerSeries.C (mono (-1)) - PowerSeries.C (mono 1) * X) *
    (1 - PowerSeries.C (mono (-2)) * X)) := by
  refine SC_mul (SC_sub SC_C_mono_neg ?_) ?_
  · have h := SC_C_mul_X_pow 1 1 1 (by omega); rwa [pow_one] at h
  · have h := SC_one_sub (-2) 1 (by omega); rwa [pow_one] at h

theorem SC_E2 : SC E2 := by
  rw [E2_eq]; exact SC_mul SC_E2a (SC_infProd _ SC_Ef_succ)

def Ra : PowerSeries L := infProd fun k => 1 - PowerSeries.C (mono 2) * X ^ (4 * k + 4)
def Rb : PowerSeries L := infProd fun k => 1 - PowerSeries.C (mono (-2)) * X ^ (4 * k + 8)
def Rc : PowerSeries L := infProd fun k => 1 - PowerSeries.C (mono (-2)) * X ^ (4 * k + 4)

/-- `ϑ(x)ϑ(-x) = (1 - x²)∏(1 - x²r^{4k+4})(1 - x⁻²r^{4k+4})`. -/
def thxR : PowerSeries L := (1 - PowerSeries.C (mono 2)) * (Ra * Rc)

theorem pf4 (c : L) (b : ℕ) (hb : 1 ≤ b) :
    ProdFactors fun k => (1 : PowerSeries L) - PowerSeries.C c * X ^ (4 * k + 4 * b) :=
  pf_sub c _ fun k => by omega

theorem tau_Ep1 : tau Ep1 = Ra * Rb := by
  have hpf : ProdFactors fun k => Ef (k + 1) := fun k => (pf_Ef (k + 1)).mono (by omega)
  rw [Ep1, tau_infProd _ hpf SC_Ef_succ, Ra, Rb]
  rw [show (fun k => (1 : PowerSeries L) - PowerSeries.C (mono 2) * X ^ (4 * k + 4)) =
      fun k => 1 - PowerSeries.C (mono 2) * X ^ (4 * k + 4 * 1) from rfl,
    show (fun k => (1 : PowerSeries L) - PowerSeries.C (mono (-2)) * X ^ (4 * k + 8)) =
      fun k => 1 - PowerSeries.C (mono (-2)) * X ^ (4 * k + 4 * 2) from rfl,
    infProd_mul (pf4 _ 1 le_rfl) (pf4 _ 2 (by norm_num))]
  refine infProd_congr fun k => ?_
  rw [Ef, tau_mul _ _ (SC_one_sub 2 _ (by omega)) (SC_one_sub (-2) _ (by omega)),
    tau_one_sub 2 _ (by omega), tau_one_sub (-2) _ (by omega),
    show (2 * ((2 * (k + 1) + 1 : ℕ) : ℤ) - 2).toNat = 4 * k + 4 * 1 by omega,
    show (2 * ((2 * (k + 1) + 1 : ℕ) : ℤ) - -2).toNat = 4 * k + 4 * 2 by omega]

theorem Rc_eq : Rc = (1 - PowerSeries.C (mono (-2)) * X ^ 4) * Rb := by
  have hpf := pf4 (mono (-2)) 1 le_rfl
  rw [show Rc = infProd fun k => (1 : PowerSeries L) - PowerSeries.C (mono (-2)) * X ^ (4 * k + 4 * 1) from rfl,
    infProd_succ hpf, Rb]
  congr 1
  all_goals first | ring | exact infProd_congr fun k => by ring_nf

theorem tau_E2 : tau E2 = X * PowerSeries.C (mono (-1)) * thxR := by
  have SC_Ep1 : SC Ep1 := SC_infProd _ SC_Ef_succ
  rw [E2_eq, tau_mul _ _ SC_E2a SC_Ep1, tau_Ep1,
    tau_mul _ _ (SC_sub SC_C_mono_neg (by have h := SC_C_mul_X_pow 1 1 1 (by omega); rwa [pow_one] at h))
      (by have h := SC_one_sub (-2) 1 (by omega); rwa [pow_one] at h),
    tau_sub, tau_sub, tau_one, tau_C_mono_neg, ← pow_one (X : PowerSeries L),
    tau_C_mono_X_pow 1 1 (by omega), tau_C_mono_X_pow (-2) 1 (by omega), thxR, Rc_eq]
  have h2 : PowerSeries.C (mono (-1)) * PowerSeries.C (mono 2) = (PowerSeries.C (mono 1) : PowerSeries L) := by
    rw [← map_mul, mono_mul]; norm_num
  rw [show (2 * ((1 : ℕ) : ℤ) - 1).toNat = 1 by rfl, show (2 * ((1 : ℕ) : ℤ) - -2).toNat = 4 by rfl]
  linear_combination (X * (1 - PowerSeries.C (mono (-2)) * X ^ 4) * (Ra * Rb)) * h2

/-! ## The transported identity -/

theorem y_identity : eta * C3 A1 = Jc ^ 3 * B1 * E2 := by
  rw [A1, C3_C_mono_mul, B1, E2]
  have h := eta_C3
  have hi := Cm_inv
  linear_combination PowerSeries.C (mono (-1)) ^ 3 * h +
    Jc ^ 3 * Psim * Ep * PowerSeries.C (mono (-1)) ^ 2 * hi

theorem Da_etaR : Da etaR = 0 := Da_infProd_const (fun k => 2 * k + 2) fun k => by show k < 2 * k + 2; omega

/-- **The cubic identity on the `x`-annulus**: `C₃(Den) = η⁶ · r x⁻¹ · Den(-x) · ϑ(x)ϑ(-x)`. -/
theorem C3_Den : C3 Den = etaR ^ 6 * X * PowerSeries.C (mono (-1)) * Denm * thxR := by
  have hs : SC eta := SC_infProd _ fun k => SC_one_sub_X _
  have hJ : SC Jc := by
    rw [Jc_eq, pow_three]; exact SC_neg (SC_mul hs (SC_mul hs hs))
  have hJ3 : SC (Jc ^ 3) := by rw [pow_three]; exact SC_mul hJ (SC_mul hJ hJ)
  have hneg : DQ wa (-etaR) = 0 := by
    have : DQ wa (-etaR) = -DQ wa etaR := by ext n : 1; simp [wd_neg]
    rw [this, show DQ wa etaR = 0 from Da_etaR, neg_zero]
  have h := congrArg tau y_identity
  rw [tau_mul _ _ hs (SC_C3 _ SC_A1), tau_C3 _ SC_A1, tau_eta, tau_A1,
    tau_mul _ _ (SC_mul hJ3 SC_B1) SC_E2, tau_mul _ _ hJ3 SC_B1, pow_three, tau_mul _ _ hJ (SC_mul hJ hJ),
    tau_mul _ _ hJ hJ, tau_Jc, tau_B1, tau_E2,
    show -(etaR * Den) = (-etaR) * Den by ring, C3_const_mul _ _ hneg] at h
  have hu : IsUnit (etaR ^ 4) := (isUnit_infProd _).pow 4
  have key : etaR ^ 4 * (C3 Den - etaR ^ 6 * X * PowerSeries.C (mono (-1)) * Denm * thxR) = 0 := by
    linear_combination -h
  rcases mul_eq_zero.mp key with h0 | h0
  · exact absurd h0 hu.ne_zero
  · exact sub_eq_zero.mp h0

end

end VOA.DeligneAudit.DeligneCharacter.D4Wp
