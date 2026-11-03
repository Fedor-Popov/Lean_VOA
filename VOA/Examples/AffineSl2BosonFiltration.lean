/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ChargedPolynomialWords
import VOA.Core.QuotientVOA

/-!
# Signed boson-count filtrations on the actual Wakimoto carrier

Both upper and lower boson-count bounds are expressed by an integer signed
weight. Beta and gamma preserve the bound exactly; the boson modes shift it
by one signed unit. These estimates include all normal-ordering contractions.
-/
namespace VOA.Wak.Charged
open MvPolynomial
noncomputable section

/-- Assign a signed unit to boson variables and zero to both ghost families.
Choosing sign minus one turns a lower filtration bound into an upper degree bound. -/
def bosonWeight (s : ℤ) (v : Fin 3×ℕ) : ℤ := if v.1=2 then s else 0

/-- The span of actual monomials above a signed boson-count threshold. -/
def bosonAtLeast (s d : ℤ) : Submodule ℂ WakFock :=
  Submodule.span ℂ {P | ∃ e : Occupation,
    d≤Finsupp.weight (bosonWeight s) e ∧ P=monomial e 1}

/-- A monomial belongs exactly at each threshold below its signed weight. -/
theorem boson_monomial_mem (s d : ℤ) (e : Occupation)
    (he : d≤Finsupp.weight (bosonWeight s) e) :
    monomial e (1 : ℂ)∈bosonAtLeast s d := Submodule.subset_span ⟨e,he,rfl⟩

/-- Increasing the required signed weight only shrinks the subspace. -/
theorem bosonAtLeast_mono (s : ℤ) {d e : ℤ} (h : d≤e) :
    bosonAtLeast s e≤bosonAtLeast s d := by
  apply Submodule.span_mono
  rintro P ⟨a,ha,rfl⟩
  exact ⟨a,h.trans ha,rfl⟩

/-- Multiplication by one oscillator shifts the exact signed threshold. -/
theorem boson_X_mul (s : ℤ) (v : Fin 3×ℕ) {d : ℤ} {P : WakFock}
    (hP : P∈bosonAtLeast s d) : X v*P∈bosonAtLeast s (d+bosonWeight s v) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨e,he,rfl⟩ := hP
    rw [X,monomial_mul,one_mul]
    apply boson_monomial_mem
    simp only [map_add,Finsupp.weight_single,one_nsmul]
    omega
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add P Q _ _ hP hQ => rw [mul_add]; exact Submodule.add_mem _ hP hQ
  | smul z P _ hP => rw [mul_smul_comm]; exact Submodule.smul_mem _ z hP

/-- A partial derivative subtracts its variable's signed weight. Integer
bounds avoid any artificial truncation when differentiating below degree zero. -/
theorem boson_pderiv (s : ℤ) (v : Fin 3×ℕ) {d : ℤ} {P : WakFock}
    (hP : P∈bosonAtLeast s d) : pderiv v P∈bosonAtLeast s (d-bosonWeight s v) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨e,he,rfl⟩ := hP
    rw [pderiv_monomial,one_mul]
    by_cases hz : e v=0
    · rw [hz,Nat.cast_zero,monomial_zero]; exact Submodule.zero_mem _
    · have hw := Finsupp.weight_sub_single_add (w:=bosonWeight s) hz
      have hm := boson_monomial_mem s (d-bosonWeight s v) (e-Finsupp.single v 1) (by omega)
      simpa only [smul_monomial,smul_eq_mul,mul_one] using
        Submodule.smul_mem (bosonAtLeast s (d-bosonWeight s v)) (e v : ℂ) hm
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add P Q _ _ hP hQ => rw [map_add]; exact Submodule.add_mem _ hP hQ
  | smul z P _ hP =>
    rw [(pderiv v).map_smul]
    exact Submodule.smul_mem _ z hP

/-- Every beta oscillator preserves signed boson count, whether it creates
beta or differentiates gamma. -/
theorem boson_Bet (s : ℤ) (n : ℤ) {d : ℤ} {P : WakFock}
    (hP : P∈bosonAtLeast s d) : Bet n P∈bosonAtLeast s d := by
  by_cases hn : n≤-1
  · rw [Bet_of_neg hn,mulL_apply,bV_of_pos (by omega)]
    simpa [bosonWeight] using boson_X_mul s ((0 : Fin 3),(-n-1).toNat) hP
  · rw [Bet_of_nonneg (by omega),cD_of_nonneg (by omega),dV_apply]
    simpa [bosonWeight] using boson_pderiv s ((1 : Fin 3),n.toNat) hP

/-- Every gamma oscillator preserves signed boson count, including its
minus sign on beta annihilators. -/
theorem boson_Gam (s : ℤ) (n : ℤ) {d : ℤ} {P : WakFock}
    (hP : P∈bosonAtLeast s d) : Gam n P∈bosonAtLeast s d := by
  by_cases hn : n≤0
  · rw [Gam_of_nonpos hn,mulL_apply,cV_of_nonneg (by omega)]
    simpa [bosonWeight] using boson_X_mul s ((1 : Fin 3),(-n).toNat) hP
  · rw [Gam_of_pos (by omega),LinearMap.neg_apply,bD_of_pos (by omega),dV_apply]
    apply Submodule.neg_mem
    simpa [bosonWeight] using boson_pderiv s ((0 : Fin 3),(n-1).toNat) hP

/-- Every summand of the actual normal-ordered beta-gamma current preserves
signed boson count, in both normal-ordering branches. -/
theorem boson_bgFam (s n p : ℤ) {d : ℤ} {P : WakFock}
    (hP : P∈bosonAtLeast s d) : bgFam n p P∈bosonAtLeast s d := by
  unfold bgFam
  split_ifs
  · exact boson_Bet s p (boson_Gam s (n-p) hP)
  · exact boson_Gam s (n-p) (boson_Bet s p hP)

/-- The full locally finite beta-gamma current preserves signed boson count;
the estimate includes every contraction term, not just the classical symbol. -/
theorem boson_BG (s n : ℤ) {d : ℤ} {P : WakFock}
    (hP : P∈bosonAtLeast s d) : BG n P∈bosonAtLeast s d := by
  rw [BG,opSum_apply (bgFam_locFin n)]
  exact QuotVOA.finsum_mem_submodule _ _ (fun p => boson_bgFam s n p hP)

/-- A negative boson mode creates one boson, shifting signed count by s. -/
theorem boson_Aos_negative (s : ℤ) (k : ℂ) (n : ℤ) (hn : n≤-1)
    {d : ℤ} {P : WakFock} (hP : P∈bosonAtLeast s d) :
    Aos k n P∈bosonAtLeast s (d+s) := by
  rw [Aos_of_neg k hn,mulL_apply,aV_of_pos (by omega)]
  simpa [bosonWeight] using boson_X_mul s ((2 : Fin 3),(-n-1).toNat) hP

/-- A positive boson mode removes one boson, shifting signed count by -s;
the actual level-dependent scalar may vanish and causes no difficulty. -/
theorem boson_Aos_positive (s : ℤ) (k : ℂ) (n : ℤ) (hn : 0<n)
    {d : ℤ} {P : WakFock} (hP : P∈bosonAtLeast s d) :
    Aos k n P∈bosonAtLeast s (d-s) := by
  rw [Aos_of_nonneg k (by omega),LinearMap.smul_apply,aD_of_pos (by omega),dV_apply]
  apply Submodule.smul_mem
  simpa [bosonWeight] using boson_pderiv s ((2 : Fin 3),(n-1).toNat) hP

/-- Below-threshold monomial coefficients of a filtered vector vanish. -/
theorem boson_coeff_zero (s d : ℤ) {P : WakFock} (hP : P∈bosonAtLeast s d)
    (e : Occupation) (he : Finsupp.weight (bosonWeight s) e<d) : coeff e P=0 := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨a,ha,rfl⟩ := hP
    rw [coeff_monomial,if_neg (by intro h; subst a; omega)]
  | zero => exact coeff_zero _
  | add P Q _ _ hP hQ => rw [coeff_add,hP,hQ,add_zero]
  | smul z P _ hP => rw [coeff_smul,hP,smul_zero]

end
end VOA.Wak.Charged
