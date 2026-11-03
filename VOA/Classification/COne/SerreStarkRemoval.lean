/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkBeta
import VOA.Classification.COne.SerreStarkFE
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Serre–Stark S5-5a: the L-series of a class form (removal identity)

For a class form `g` (class-form space `V`, `p ∣ N` primes) and `Re s > 3/2`:

`L(s, ∏_{p ∣ N} (1 − p^{−2s} U(p²)) g) = a_g(t) · t^{−s} · L(2s, ψ^{(N)})`

(`LS_removal`), where `ψ^{(N)} = changeLevel ψ` is `ψ` restricted to integers prime to `N`.
Each factor `1 − p^{−2s} U(p²)` removes the terms with `p² ∣ n`; what is left is supported on
`t v²` with `v` prime to `N`. No analytic continuation is used: this is coefficient bookkeeping.
-/

open Complex
open scoped UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

namespace ClassSetup

variable (S : ClassSetup)

/-- The L-series of a class form. -/
def LS (s : ℂ) (g : S.V) : ℂ := LSeries (fun n => S.coeffL n g) s

theorem coeffL_bound (g : S.V) : ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 4 ≤ n →
    ‖S.coeffL n g‖ ≤ B * (n : ℝ) ^ (1 / 2 : ℝ) := by
  obtain ⟨f, hf, hfg⟩ := g.2
  obtain ⟨B, hB0, hB⟩ := exists_norm_coeff_le S.h4 S.hN hf.1
  exact ⟨B, hB0, fun n hn => by rw [S.coeffL_eq hfg]; exact hB n hn⟩

/-- Any function dominated by the coefficients of a class form has a summable L-series for
`Re s > 3/2`. -/
theorem lseriesSummable_of_le (g : S.V) {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ ‖S.coeffL n g‖)
    {s : ℂ} (hs : 3 / 2 < s.re) : LSeriesSummable c s := by
  obtain ⟨B, hB0, hB⟩ := S.coeffL_bound g
  refine LSeriesSummable_of_isBigO_rpow (x := 3 / 2) hs ?_
  refine Asymptotics.IsBigO.of_bound B ?_
  filter_upwards [Filter.eventually_ge_atTop 4] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have e : (3 / 2 : ℝ) - 1 = 1 / 2 := by norm_num
  rw [e]
  exact (hc n).trans (hB n hn)

theorem lseriesSummable (g : S.V) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable (fun n => S.coeffL n g) s :=
  S.lseriesSummable_of_le g (fun _ => le_rfl) hs

/-! ## Removing `p²`-divisible terms -/

/-- The coefficients of `g` at `n` with `p² ∤ n` for all `p ∈ Q`. -/
def cQ (Q : Finset S.ι) (g : S.V) (n : ℕ) : ℂ :=
  if ∀ p ∈ Q, ¬ p.1 ^ 2 ∣ n then S.coeffL n g else 0

theorem norm_cQ_le (Q : Finset S.ι) (g : S.V) (n : ℕ) : ‖S.cQ Q g n‖ ≤ ‖S.coeffL n g‖ := by
  unfold cQ; split_ifs <;> simp

theorem lseriesSummable_cQ (Q : Finset S.ι) (g : S.V) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable (S.cQ Q g) s :=
  S.lseriesSummable_of_le g (S.norm_cQ_le Q g) hs

/-- One removal step. -/
theorem LSeries_cQ_insert {Q : Finset S.ι} {p : S.ι} (hp : p ∉ Q) (g : S.V) {s : ℂ}
    (hs : 3 / 2 < s.re) :
    LSeries (S.cQ Q g) s - (p.1 : ℂ) ^ (-(2 * s)) * LSeries (S.cQ Q (S.U p g)) s =
      LSeries (S.cQ (insert p Q) g) s := by
  classical
  have hp0 : (p.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (S.prime p).ne_zero
  -- the dilated series
  have hdil : (p.1 : ℂ) ^ (-(2 * s)) * LSeries (S.cQ Q (S.U p g)) s =
      LSeries (fun n => if p.1 ^ 2 ∣ n then S.cQ Q g n else 0) s := by
    set F : ℕ → ℂ := fun n => if p.1 ^ 2 ∣ n then S.cQ Q g n else 0 with hF
    rw [LSeries, LSeries, ← tsum_mul_left]
    have hinj : Function.Injective fun n : ℕ => p.1 ^ 2 * n :=
      fun a b h => Nat.eq_of_mul_eq_mul_left (pow_pos (S.prime p).pos 2) h
    have hsupp : Function.support (LSeries.term F s) ⊆ Set.range fun n : ℕ => p.1 ^ 2 * n := by
      intro n hn
      by_contra hc
      apply hn
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; exact LSeries.term_zero _ _
      · rw [LSeries.term_of_ne_zero h0.ne', hF]
        simp only
        rw [if_neg, zero_div]
        rintro ⟨k, rfl⟩; exact hc ⟨k, rfl⟩
    rw [← hinj.tsum_eq hsupp]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [LSeries.term_zero]
    · have hpn : p.1 ^ 2 * n ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ (S.prime p).ne_zero) hn.ne'
      rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hpn, hF]
      simp only
      rw [if_pos (Dvd.intro n rfl)]
      -- coefficients
      have hc : S.cQ Q (S.U p g) n = S.cQ Q g (p.1 ^ 2 * n) := by
        unfold cQ
        rw [coeffL_U]
        congr 1
        apply propext
        refine forall₂_congr fun q hq => ?_
        have hqp : q ≠ p := fun h => hp (h ▸ hq)
        constructor
        · intro h1 h2
          apply h1
          have hcop : Nat.Coprime (q.1 ^ 2) (p.1 ^ 2) := by
            refine Nat.Coprime.pow 2 2 ?_
            exact (Nat.coprime_primes (S.prime q) (S.prime p)).2 (fun h => hqp (Subtype.ext h))
          exact hcop.dvd_of_dvd_mul_left h2
        · intro h1 h2; exact h1 (h2.mul_left _)
      rw [hc]
      have key : ((p.1 ^ 2 * n : ℕ) : ℂ) ^ s = (p.1 : ℂ) ^ (2 * s) * (n : ℂ) ^ s := by
        rw [Nat.cast_mul, natCast_mul_natCast_cpow, Nat.cast_pow,
          ← natCast_cpow_natCast_mul]
        norm_num
      have hns : (n : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.2 (Or.inl (Nat.cast_ne_zero.2 hn.ne'))
      have hps : (p.1 : ℂ) ^ (2 * s) ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hp0)
      rw [key, cpow_neg]
      field_simp
  rw [hdil, ← LSeries_sub (S.lseriesSummable_cQ Q g hs)]
  · refine LSeries_congr (fun {n} _ => ?_) s
    simp only [Pi.sub_apply]
    unfold cQ
    by_cases h1 : ∀ q ∈ Q, ¬ q.1 ^ 2 ∣ n
    · by_cases h2 : p.1 ^ 2 ∣ n
      · have h3 : ¬ ∀ q ∈ insert p Q, ¬ q.1 ^ 2 ∣ n := fun h =>
          h p (Finset.mem_insert_self p Q) h2
        rw [if_pos h1, if_pos h2, if_neg h3, sub_self]
      · have h3 : ∀ q ∈ insert p Q, ¬ q.1 ^ 2 ∣ n := by
          intro q hq
          rcases Finset.mem_insert.1 hq with rfl | hq
          · exact h2
          · exact h1 q hq
        rw [if_pos h1, if_neg h2, if_pos h3, sub_zero]
    · have h3 : ¬ ∀ q ∈ insert p Q, ¬ q.1 ^ 2 ∣ n := fun h =>
        h1 fun q hq => h q (Finset.mem_insert_of_mem hq)
      rw [if_neg h1, if_neg h3]
      split_ifs <;> ring
  · exact S.lseriesSummable_of_le g (fun n => by
      split_ifs
      · exact S.norm_cQ_le Q g n
      · simp) hs

theorem LS_sub_smul (s : ℂ) (hs : 3 / 2 < s.re) (x y : S.V) (c : ℂ) :
    S.LS s (x - c • y) = S.LS s x - c * S.LS s y := by
  unfold LS
  have e : (fun n => S.coeffL n (x - c • y)) = (fun n => S.coeffL n x) -
      c • (fun n => S.coeffL n y) := by
    funext n; simp [map_sub, map_smul]
  rw [e, LSeries_sub (S.lseriesSummable x hs) ((S.lseriesSummable y hs).smul c), LSeries_smul]

theorem cQ_empty (g : S.V) : S.cQ ∅ g = fun n => S.coeffL n g := by
  funext n; simp [cQ]

/-- Iterated removal: `L(c_Q(g), s) = L(s, ∏_{p ∈ Q} (1 − p^{−2s} U_p) g)`. -/
theorem LSeries_cQ_prod (Q : Finset S.ι) (g : S.V) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries (S.cQ Q g) s = S.LS s
      (((∏ p ∈ Q, (1 - (p.1 : ℂ) ^ (-(2 * s)) • S.Ua p) : S.opAlg) : Module.End ℂ S.V) g) := by
  classical
  induction Q using Finset.induction_on generalizing g with
  | empty => rw [cQ_empty]; simp [LS]
  | insert p Q hp ih =>
    rw [← S.LSeries_cQ_insert hp g hs, ih, ih, Finset.prod_insert hp]
    set X : S.opAlg := ∏ q ∈ Q, (1 - (q.1 : ℂ) ^ (-(2 * s)) • S.Ua q)
    have e1 : (((1 - (p.1 : ℂ) ^ (-(2 * s)) • S.Ua p) * X : S.opAlg) : Module.End ℂ S.V) g =
        (X : Module.End ℂ S.V) g - (p.1 : ℂ) ^ (-(2 * s)) • S.U p ((X : Module.End ℂ S.V) g) := by
      rw [Subalgebra.coe_mul, Module.End.mul_apply, Subalgebra.coe_sub, Subalgebra.coe_one,
        Subalgebra.coe_smul]
      rfl
    have e2 : (X : Module.End ℂ S.V) (S.U p g) = S.U p ((X : Module.End ℂ S.V) g) := by
      have hc : Commute (X : Module.End ℂ S.V) (S.U p) := S.opAlg_comm X.2 (S.U_mem p)
      rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply]
    rw [e1, e2, S.LS_sub_smul s hs]

/-- `ψ` restricted to integers prime to `N`. -/
def chiN (v : ℕ) : ℂ := if v.Coprime S.N then S.ψ (v : ZMod S.r) else 0

/-- Nonzero `p²`-free coefficients of a class form sit at `t v²`, `v` prime to `N`. -/
theorem eq_t_mul_sq_of_cQ {g : S.V} {n : ℕ} (hn : 0 < n) (h : S.cQ Finset.univ g n ≠ 0) :
    ∃ v, v.Coprime S.N ∧ n = S.t * v ^ 2 := by
  classical
  unfold cQ at h
  by_cases hsq : ∀ p ∈ (Finset.univ : Finset S.ι), ¬ p.1 ^ 2 ∣ n
  swap
  · rw [if_neg hsq] at h; exact absurd rfl h
  rw [if_pos hsq] at h
  obtain ⟨f, hf, hfg⟩ := g.2
  rw [S.coeffL_eq hfg] at h
  obtain ⟨x, hx⟩ := hf.2.1 n hn h
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx; omega
  obtain ⟨v, hxv, hv⟩ := exists_smooth_decomp (P := S.N.primeFactors)
    (fun p hp => Nat.prime_of_mem_primeFactors hp) hx0
  have hvN : v.Coprime S.N := Nat.coprime_of_dvd fun k hk hkv hkN =>
    hv k (Nat.mem_primeFactors.2 ⟨hk, hkN, S.hN.ne'⟩) hkv
  refine ⟨v, hvN, ?_⟩
  -- the smooth part is `1`
  have hs1 : ∏ p ∈ S.N.primeFactors, p ^ x.factorization p = 1 := by
    refine Finset.prod_eq_one fun p hp => ?_
    by_contra hne
    have hpos : 0 < x.factorization p := by
      rcases Nat.eq_zero_or_pos (x.factorization p) with h0 | h0
      · rw [h0, pow_zero] at hne; exact absurd rfl hne
      · exact h0
    have hpx : p ∣ x := Nat.dvd_of_factorization_pos hpos.ne'
    apply hsq ⟨p, hp⟩ (Finset.mem_univ _)
    rw [hx]
    exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hpx 2) _
  rw [hx, hxv, hs1, one_mul]

theorem cQ_univ_t_mul_sq (g : S.V) (v : ℕ) :
    S.cQ Finset.univ g (S.t * v ^ 2) = S.chiN v * S.coeffL S.t g := by
  classical
  obtain ⟨f, hf, hfg⟩ := g.2
  unfold cQ chiN
  by_cases hvN : v.Coprime S.N
  · rw [if_pos hvN, if_pos, S.coeffL_eq hfg, S.coeffL_eq hfg,
      hf.2.2 S.t v (Nat.pos_of_ne_zero S.ht.ne_zero) hvN]
    intro p _ hp2
    -- `p² ∣ t v²` with `p ∤ v` contradicts `t` squarefree
    have hpv : ¬ p.1 ∣ v := fun h => (Nat.Prime.coprime_iff_not_dvd (S.prime p)).1
      (Nat.Coprime.coprime_dvd_left (S.dvd p) hvN.symm) h
    have hcop : Nat.Coprime (p.1 ^ 2) (v ^ 2) :=
      Nat.Coprime.pow 2 2 ((Nat.Prime.coprime_iff_not_dvd (S.prime p)).2 hpv)
    have := hcop.dvd_of_dvd_mul_right hp2
    have := S.ht p.1 (by rw [← pow_two]; exact this)
    exact (S.prime p).one_lt.ne' (Nat.isUnit_iff.1 this)
  · rw [if_neg hvN, zero_mul, if_neg]
    intro h
    obtain ⟨k, hk, hkv, hkN⟩ := Nat.Prime.not_coprime_iff_dvd.1 hvN
    exact h ⟨k, Nat.mem_primeFactors.2 ⟨hk, hkN, S.hN.ne'⟩⟩ (Finset.mem_univ _)
      (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hkv 2) _)

/-- **Removal identity.** For `Re s > 3/2`,
`L(s, ∏_p (1 − p^{−2s} U_p) g) = a_g(t) t^{−s} L(2s, ψ^{(N)})`. -/
theorem LS_removal (g : S.V) {s : ℂ} (hs : 3 / 2 < s.re) :
    S.LS s (((∏ p, (1 - (p.1 : ℂ) ^ (-(2 * s)) • S.Ua p) : S.opAlg) : Module.End ℂ S.V) g) =
      S.coeffL S.t g * (S.t : ℂ) ^ (-s) * LSeries S.chiN (2 * s) := by
  classical
  rw [← S.LSeries_cQ_prod Finset.univ g hs]
  have ht0 : 0 < S.t := Nat.pos_of_ne_zero S.ht.ne_zero
  have hinj : Function.Injective fun v : ℕ => S.t * v ^ 2 := fun a b h =>
    Nat.pow_left_injective two_ne_zero (Nat.eq_of_mul_eq_mul_left ht0 h)
  have hsupp : Function.support (LSeries.term (S.cQ Finset.univ g) s) ⊆
      Set.range fun v : ℕ => S.t * v ^ 2 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; exact absurd (LSeries.term_zero _ _) hn
    · rw [Function.mem_support, LSeries.term_of_ne_zero h0.ne'] at hn
      have hc : S.cQ Finset.univ g n ≠ 0 := fun h => hn (by rw [h, zero_div])
      obtain ⟨v, -, rfl⟩ := S.eq_t_mul_sq_of_cQ h0 hc
      exact ⟨v, rfl⟩
  rw [LSeries, ← hinj.tsum_eq hsupp, LSeries, ← tsum_mul_left]
  refine tsum_congr fun v => ?_
  rcases Nat.eq_zero_or_pos v with hv | hv
  · subst hv; simp [LSeries.term_zero]
  · have htv : S.t * v ^ 2 ≠ 0 := Nat.mul_ne_zero S.ht.ne_zero (pow_ne_zero _ hv.ne')
    rw [LSeries.term_of_ne_zero htv, LSeries.term_of_ne_zero hv.ne', S.cQ_univ_t_mul_sq g v]
    have key : ((S.t * v ^ 2 : ℕ) : ℂ) ^ s = (S.t : ℂ) ^ s * (v : ℂ) ^ (2 * s) := by
      rw [Nat.cast_mul, natCast_mul_natCast_cpow, Nat.cast_pow, ← natCast_cpow_natCast_mul]
      norm_num
    have ht' : (S.t : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.2 (Or.inl (Nat.cast_ne_zero.2 ht0.ne'))
    have hv' : (v : ℂ) ^ (2 * s) ≠ 0 := cpow_ne_zero_iff.2 (Or.inl (Nat.cast_ne_zero.2 hv.ne'))
    rw [key, cpow_neg]
    field_simp

/-! ## Inverting the removal operators -/

instance : FiniteDimensional ℂ S.opAlg :=
  FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule S.opAlg)

/-- An element of the (finite-dimensional, commutative) operator algebra that is invertible as an
operator is invertible in the algebra. -/
theorem isUnit_of_isUnit_coe {a : S.opAlg} (h : IsUnit (a : Module.End ℂ S.V)) : IsUnit a := by
  let L : S.opAlg →ₗ[ℂ] S.opAlg := LinearMap.mulLeft ℂ a
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    have h1 : (a : Module.End ℂ S.V) * (b : Module.End ℂ S.V) = 0 := by
      have := congrArg Subtype.val hb
      simpa [L] using this
    apply Subtype.ext
    obtain ⟨u, hu⟩ := h
    have : (b : Module.End ℂ S.V) = ↑u⁻¹ * ((a : Module.End ℂ S.V) * b) := by
      rw [← mul_assoc, ← hu, Units.inv_mul, one_mul]
    rw [this, h1, mul_zero]; rfl
  obtain ⟨b, hb⟩ := (LinearMap.injective_iff_surjective.1 hinj) 1
  exact IsUnit.of_mul_eq_one b hb

/-- `1 − x U_p` is invertible unless `x⁻¹` is an eigenvalue, in particular when `p ≤ ‖x‖⁻²`. -/
theorem isUnit_one_sub (p : S.ι) {x : ℂ} (hx : (p.1 : ℝ) ≤ ‖x‖⁻¹ ^ 2) :
    IsUnit (1 - x • S.Ua p) := by
  apply S.isUnit_of_isUnit_coe
  have e : ((1 - x • S.Ua p : S.opAlg) : Module.End ℂ S.V) = 1 - x • S.U p := rfl
  rw [e, LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  by_contra hv0
  have h1 : v = x • S.U p v := by
    have := hv
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply] at this
    exact sub_eq_zero.1 this
  have hx0 : x ≠ 0 := by rintro rfl; rw [zero_smul] at h1; exact hv0 h1
  have heig : (S.U p).HasEigenvalue x⁻¹ := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv0⟩
    rw [Module.End.mem_eigenspace_iff]
    calc S.U p v = x⁻¹ • (x • S.U p v) := by rw [smul_smul, inv_mul_cancel₀ hx0, one_smul]
      _ = x⁻¹ • v := by rw [← h1]
  have := upEnd_eigenvalue_norm_sq_lt (p := p.1) (hpf := ⟨S.prime p⟩) S.ψ S.hN S.h24 (S.dvd p)
    S.hrN S.ht heig
  rw [norm_inv] at this
  linarith

/-- The resolvent product `R(s) = ∏_p (1 − p^{−2s} U_p)^{−1}` (junk where not invertible). -/
def Rinv (s : ℂ) : S.opAlg := ∏ p, Ring.inverse (1 - (p.1 : ℂ) ^ (-(2 * s)) • S.Ua p)

/-- `F_g(s) = a_{R(s) g}(t)`. -/
def Fs (s : ℂ) (g : S.V) : ℂ := S.coeffL S.t (((S.Rinv s : S.opAlg) : Module.End ℂ S.V) g)

/-- `s` is good if every `1 − p^{−2s} U_p` is invertible. -/
def Good (s : ℂ) : Prop := ∀ p : S.ι, IsUnit (1 - (p.1 : ℂ) ^ (-(2 * s)) • S.Ua p)

theorem prod_mul_Rinv {s : ℂ} (hs : S.Good s) :
    (∏ p, (1 - (p.1 : ℂ) ^ (-(2 * s)) • S.Ua p)) * S.Rinv s = 1 := by
  rw [Rinv, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun p _ => Ring.mul_inverse_cancel _ (hs p)

theorem good_of_re {s : ℂ} (hs : 1 / 4 < s.re) : S.Good s := by
  intro p
  apply S.isUnit_one_sub p
  have hp1 : (1 : ℝ) < p.1 := by exact_mod_cast (S.prime p).one_lt
  have hp0 : (0 : ℝ) < p.1 := by linarith
  rw [Complex.norm_natCast_cpow_of_pos (S.prime p).pos, neg_re, mul_re]
  simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  rw [← Real.rpow_neg hp0.le, neg_neg, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
  calc (p.1 : ℝ) = (p.1 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (p.1 : ℝ) ^ (2 * s.re * ((2 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hp1.le (by push_cast; linarith)

/-- **The L-series of a class form through the resolvent.** For `Re s > 3/2`,
`L(s, g) = F_g(s) · t^{−s} · L(2s, ψ^{(N)})`. -/
theorem LS_eq_Fs (g : S.V) {s : ℂ} (hs : 3 / 2 < s.re) :
    S.LS s g = S.Fs s g * (S.t : ℂ) ^ (-s) * LSeries S.chiN (2 * s) := by
  have hgood := S.good_of_re (s := s) (by linarith)
  have := S.LS_removal (((S.Rinv s : S.opAlg) : Module.End ℂ S.V) g) hs
  rw [← Module.End.mul_apply, ← Subalgebra.coe_mul, S.prod_mul_Rinv hgood] at this
  exact this

end ClassSetup

end SSHecke

end VOA.Classification.COne
