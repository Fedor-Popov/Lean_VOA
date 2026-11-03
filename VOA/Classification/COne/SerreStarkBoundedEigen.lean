/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkBoundedMeanSq

/-!
# Serre–Stark S5-2d: consequences of the mean-square bound

* `norm_coeff_sq_le`: `|a(n)|² ≤ C √n` for every θ-type form (`a(n) = O(n^{1/4})`).
* `norm_sq_lt_of_upOp_eigen`: if a class form `f` (for `(ψ, t)`, conductor `r ∣ N`) satisfies
  `U(p²) f = c f` (`p ∣ N`, `24 ∣ N`) and `f` has a nonzero positive coefficient, then
  `|c|² < p`. Proof: along `n₀ p^{2k} (1 + jN)²` the coefficients are `c^k a(n₀)`; at
  `y = 1/(4 N² n₀ p^{2K})` the mean-square sum is `≥ e^{−π} |a(n₀)|² p^K Σ_{k ≤ K} (|c|²/p)^k`
  while `sum_sq_coeff_le` bounds it by `C · 2N √n₀ p^K`; if `|c|² ≥ p` the left side grows like
  `K p^K`.
* `upEnd_eigenvalue_norm_sq_lt`: every eigenvalue `c` of `U(p²)` on `classSpace N r ψ t`
  satisfies `|c|² < p`.

This is the analytic input that excludes the "fake pairs" `(c, p/c)` of the Fricke functional
equation.
-/

open Complex
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-! ## The coefficient bound -/

/-- `|a(n)|² ≤ C √n` (`n ≥ 4`). -/
theorem norm_coeff_sq_le {N : ℕ} (h4 : 4 ∣ N) (hN : 0 < N) {f : ℂ → ℂ}
    (hf : IsThetaTypeForm N f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n →
      ‖thetaTypeCoeff f n‖ ^ 2 ≤ C * Real.sqrt n := by
  obtain ⟨C, hC0, hC⟩ := sum_sq_coeff_le h4 hN hf
  refine ⟨C * Real.exp (4 * Real.pi), by positivity, fun n hn => ?_⟩
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hy0 : (0 : ℝ) < 1 / n := by positivity
  have hy : (1 : ℝ) / n ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hnR
  have h := hC (1 / n) hy0 hy (n + 1)
  have hle : ‖thetaTypeCoeff f n‖ ^ 2 * Real.exp (-(4 * Real.pi * n * (1 / n))) ≤
      ∑ m ∈ Finset.range (n + 1), ‖thetaTypeCoeff f m‖ ^ 2 *
        Real.exp (-(4 * Real.pi * m * (1 / n))) :=
    Finset.single_le_sum (f := fun m : ℕ => ‖thetaTypeCoeff f m‖ ^ 2 *
      Real.exp (-(4 * Real.pi * m * (1 / n)))) (fun m _ => by positivity)
      (Finset.self_mem_range_succ n)
  have e1 : 4 * Real.pi * n * (1 / n) = 4 * Real.pi := by field_simp
  rw [e1] at hle
  have e2 : (Real.sqrt (1 / n))⁻¹ = Real.sqrt n := by
    rw [Real.sqrt_div' _ hn0.le, Real.sqrt_one, one_div, inv_inv]
  rw [e2] at h
  have h3 := hle.trans h
  have hexp : Real.exp (-(4 * Real.pi)) * Real.exp (4 * Real.pi) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖thetaTypeCoeff f n‖ ^ 2 = ‖thetaTypeCoeff f n‖ ^ 2 * Real.exp (-(4 * Real.pi)) *
        Real.exp (4 * Real.pi) := by rw [mul_assoc, hexp, mul_one]
    _ ≤ C * Real.sqrt n * Real.exp (4 * Real.pi) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = C * Real.exp (4 * Real.pi) * Real.sqrt n := by ring

/-! ## `U(p²)`-eigenvalues on class forms -/

section Eigen

variable {p : ℕ} [hpf : Fact p.Prime]

/-- Along `n₀ p^{2k}` an eigenform of `U(p²)` has coefficients `c^k a(n₀)`. -/
theorem coeff_pow_of_upOp_eigen {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N) (hpN : p ∣ N)
    {f : ℂ → ℂ} (hf : IsThetaTypeForm N f) {c : ℂ}
    (hc : ∀ τ : ℂ, 0 < τ.im → upOp p f τ = c * f τ) (n : ℕ) (k : ℕ) :
    thetaTypeCoeff f (p ^ (2 * k) * n) = c ^ k * thetaTypeCoeff f n := by
  have h1 : ∀ m, thetaTypeCoeff f (p ^ 2 * m) = c * thetaTypeCoeff f m := by
    intro m
    rw [← coeff_upOp hN h24 hpN hf m, thetaTypeCoeff_congr hc m,
      show (fun τ => c * f τ) = c • f from rfl, hf.coeff_smul c m]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show p ^ (2 * (k + 1)) * n = p ^ 2 * (p ^ (2 * k) * n) by ring, h1, ih, pow_succ]
    ring

/-- For `v ≡ 1 (mod N)` the class-form coefficients are unchanged: `a(n v²) = a(n)`. -/
theorem classForm_coeff_one_mod {N r t : ℕ} {ψ : DirichletCharacter ℂ r} (hrN : r ∣ N)
    {f : ℂ → ℂ} (hf : IsClassForm N r ψ t f) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    thetaTypeCoeff f (n * (1 + j * N) ^ 2) = thetaTypeCoeff f n := by
  have hcop : (1 + j * N).Coprime N :=
    (Nat.coprime_add_mul_right_left 1 N j).2 (Nat.coprime_one_left N)
  rw [hf.2.2 n _ hn hcop]
  have : ((1 + j * N : ℕ) : ZMod r) = 1 := by
    obtain ⟨m, hm⟩ := hrN
    rw [hm]; push_cast
    rw [ZMod.natCast_self, zero_mul, mul_zero, add_zero]
  rw [this, map_one, one_mul]

/-- **`|c|² < p` for `U(p²)`-eigenforms among class forms.** -/
theorem norm_sq_lt_of_upOp_eigen {N r t : ℕ} {ψ : DirichletCharacter ℂ r} (hN : 0 < N)
    (h24 : 24 ∣ N) (hpN : p ∣ N) (hrN : r ∣ N) {f : ℂ → ℂ} (hf : IsClassForm N r ψ t f)
    {c : ℂ} (hc : ∀ τ : ℂ, 0 < τ.im → upOp p f τ = c * f τ) {n₀ : ℕ} (hn₀ : 0 < n₀)
    (ha : thetaTypeCoeff f n₀ ≠ 0) : ‖c‖ ^ 2 < p := by
  have hp := hpf.out
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  obtain ⟨C, hC0, hC⟩ := sum_sq_coeff_le h4 hN hf.1
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn₀R : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  set A := ‖thetaTypeCoeff f n₀‖ ^ 2 with hA
  have hA0 : 0 < A := pow_pos (norm_pos_iff.2 ha) 2
  by_contra hcon
  push Not at hcon
  -- choose `K` with `K + 1 > 2 C N √n₀ e^π / A`
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * C * N * Real.sqrt n₀ * Real.exp Real.pi / A)
  set y : ℝ := 1 / (4 * (N : ℝ) ^ 2 * n₀ * (p : ℝ) ^ (2 * K)) with hy
  have hy0 : 0 < y := by positivity
  have hy4 : y ≤ 1 / 4 := by
    rw [hy]
    apply one_div_le_one_div_of_le (by norm_num)
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hNR
    have h2 : (1 : ℝ) ≤ (p : ℝ) ^ (2 * K) := one_le_pow₀ hpR.le
    have h3 : (1 : ℝ) ≤ (N : ℝ) ^ 2 * n₀ * (p : ℝ) ^ (2 * K) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 hn₀R) h2
    nlinarith
  -- the index set and the injection
  set S : Finset (Σ _ : ℕ, ℕ) := (Finset.range (K + 1)).sigma fun k => Finset.range (p ^ (K - k))
  let m : (Σ _ : ℕ, ℕ) → ℕ := fun kj => p ^ (2 * kj.1) * n₀ * (1 + kj.2 * N) ^ 2
  have hmcoeff : ∀ kj ∈ S, thetaTypeCoeff f (m kj) = c ^ kj.1 * thetaTypeCoeff f n₀ := by
    intro kj _
    simp only [m]
    rw [classForm_coeff_one_mod hrN hf (Nat.mul_pos (pow_pos hp.pos _) hn₀),
      coeff_pow_of_upOp_eigen hN h24 hpN hf.1 hc]
  have hminj : Set.InjOn m S := by
    rintro ⟨k, j⟩ _ ⟨k', j'⟩ _ hkk
    simp only [m] at hkk
    have hpv : ∀ (k j : ℕ), padicValNat p (p ^ (2 * k) * n₀ * (1 + j * N) ^ 2) =
        2 * k + padicValNat p n₀ := by
      intro k j
      haveI := hpf
      have hu : ¬ p ∣ 1 + j * N := by
        intro h
        have : p ∣ j * N := dvd_mul_of_dvd_right hpN j
        have := (Nat.dvd_add_right this).1 (by rwa [add_comm] at h)
        exact hp.one_lt.ne' (Nat.dvd_one.1 this)
      have hu0 : 1 + j * N ≠ 0 := by omega
      rw [padicValNat.mul (Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) hn₀.ne')
        (pow_ne_zero _ hu0), padicValNat.mul (pow_ne_zero _ hp.ne_zero) hn₀.ne',
        padicValNat.prime_pow, padicValNat.pow _ hu0, padicValNat.eq_zero_of_not_dvd hu]
      ring
    have hk : k = k' := by
      have := congrArg (padicValNat p) hkk
      rw [hpv, hpv] at this
      omega
    subst hk
    have h1 : (1 + j * N) ^ 2 = (1 + j' * N) ^ 2 :=
      Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (pow_pos hp.pos _) hn₀) hkk
    have h2 : 1 + j * N = 1 + j' * N := Nat.pow_left_injective two_ne_zero h1
    have h3 : j = j' := by
      have : j * N = j' * N := by omega
      exact Nat.eq_of_mul_eq_mul_right hN this
    rw [h3]
  -- bound `M` so that the image lies in `range M`
  set M : ℕ := (S.image m).sup id + 1
  have hmM : ∀ kj ∈ S, m kj ∈ Finset.range M := by
    intro kj hkj
    rw [Finset.mem_range]
    have := Finset.le_sup (f := id) (Finset.mem_image_of_mem m hkj)
    simp only [id] at this
    omega
  have hupper := hC y hy0 hy4 M
  -- lower bound
  set g : ℕ → ℝ := fun n => ‖thetaTypeCoeff f n‖ ^ 2 * Real.exp (-(4 * Real.pi * n * y))
  have hg0 : ∀ n, 0 ≤ g n := fun n => by positivity
  have hsub : ∑ kj ∈ S, g (m kj) ≤ ∑ n ∈ Finset.range M, g n := by
    rw [← Finset.sum_image hminj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => by
      obtain ⟨kj, hkj, rfl⟩ := Finset.mem_image.1 hn; exact hmM kj hkj) (fun n _ _ => hg0 n)
  have hterm : ∀ kj ∈ S, Real.exp (-Real.pi) * (‖c‖ ^ 2) ^ kj.1 * A ≤ g (m kj) := by
    rintro ⟨k, j⟩ hkj
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.1 hkj
    simp only [Finset.mem_range] at hk hj
    simp only [g]
    have e : ‖c ^ k * thetaTypeCoeff f n₀‖ ^ 2 = (‖c‖ ^ 2) ^ k * A := by
      rw [norm_mul, norm_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k 2]
    rw [hmcoeff ⟨k, j⟩ hkj, e]
    have hexp : Real.exp (-Real.pi) ≤ Real.exp (-(4 * Real.pi * (m ⟨k, j⟩ : ℝ) * y)) := by
      apply Real.exp_le_exp.2
      have hjN : ((1 + j * N : ℕ) : ℝ) ≤ N * (p : ℝ) ^ (K - k) := by
        have : 1 + j * N ≤ N * p ^ (K - k) := by
          have hj1 : j + 1 ≤ p ^ (K - k) := hj
          nlinarith
        exact_mod_cast this
      have hmval : (m ⟨k, j⟩ : ℝ) ≤ (p : ℝ) ^ (2 * k) * n₀ * (N * (p : ℝ) ^ (K - k)) ^ 2 := by
        simp only [m]; push_cast
        gcongr
        exact_mod_cast hjN
      have hpow : (p : ℝ) ^ (2 * k) * ((p : ℝ) ^ (K - k)) ^ 2 = (p : ℝ) ^ (2 * K) := by
        rw [← pow_mul, ← pow_add]; congr 1; omega
      have : (m ⟨k, j⟩ : ℝ) * y ≤ 1 / 4 := by
        rw [hy, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        calc (m ⟨k, j⟩ : ℝ) * 4 ≤ (p : ℝ) ^ (2 * k) * n₀ * (N * (p : ℝ) ^ (K - k)) ^ 2 * 4 :=
              by gcongr
          _ = 1 * (4 * (N : ℝ) ^ 2 * n₀ * (p : ℝ) ^ (2 * K)) := by rw [← hpow]; ring
      nlinarith [Real.pi_pos]
    calc Real.exp (-Real.pi) * (‖c‖ ^ 2) ^ k * A
        = (‖c‖ ^ 2) ^ k * A * Real.exp (-Real.pi) := by ring
      _ ≤ (‖c‖ ^ 2) ^ k * A * Real.exp (-(4 * Real.pi * (m ⟨k, j⟩ : ℝ) * y)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
  -- assemble: `Σ_{k ≤ K} p^{K-k} |c|^{2k} ≥ (K+1) p^K`
  have hlow : Real.exp (-Real.pi) * A * ((K + 1) * (p : ℝ) ^ K) ≤ ∑ kj ∈ S, g (m kj) := by
    have h1 : ∑ kj ∈ S, Real.exp (-Real.pi) * (‖c‖ ^ 2) ^ kj.1 * A ≤ ∑ kj ∈ S, g (m kj) :=
      Finset.sum_le_sum hterm
    refine le_trans ?_ h1
    rw [Finset.sum_sigma]
    have h2 : ∀ k ∈ Finset.range (K + 1), Real.exp (-Real.pi) * A * (p : ℝ) ^ K ≤
        ∑ j ∈ Finset.range (p ^ (K - k)), Real.exp (-Real.pi) * (‖c‖ ^ 2) ^ k * A := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hck : (p : ℝ) ^ k ≤ (‖c‖ ^ 2) ^ k := pow_le_pow_left₀ hp0.le hcon k
      have hsplit : (p : ℝ) ^ K = (p : ℝ) ^ (K - k) * (p : ℝ) ^ k := by
        rw [← pow_add]; congr 1; omega
      push_cast
      rw [hsplit]
      have : 0 ≤ Real.exp (-Real.pi) * A * (p : ℝ) ^ (K - k) := by positivity
      calc Real.exp (-Real.pi) * A * ((p : ℝ) ^ (K - k) * (p : ℝ) ^ k)
          = Real.exp (-Real.pi) * A * (p : ℝ) ^ (K - k) * (p : ℝ) ^ k := by ring
        _ ≤ Real.exp (-Real.pi) * A * (p : ℝ) ^ (K - k) * (‖c‖ ^ 2) ^ k :=
            mul_le_mul_of_nonneg_left hck this
        _ = (p : ℝ) ^ (K - k) * (Real.exp (-Real.pi) * (‖c‖ ^ 2) ^ k * A) := by ring
    calc Real.exp (-Real.pi) * A * ((K + 1) * (p : ℝ) ^ K)
        = ∑ k ∈ Finset.range (K + 1), Real.exp (-Real.pi) * A * (p : ℝ) ^ K := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := Finset.sum_le_sum h2
  have htot := (hlow.trans hsub).trans hupper
  -- `(√y)⁻¹ = 2 N √n₀ p^K`
  have hsy : (Real.sqrt y)⁻¹ = 2 * N * Real.sqrt n₀ * (p : ℝ) ^ K := by
    rw [hy, Real.sqrt_div' _ (by positivity), Real.sqrt_one, one_div, inv_inv]
    rw [show (4 : ℝ) * (N : ℝ) ^ 2 * n₀ * (p : ℝ) ^ (2 * K) =
      (2 * N * (p : ℝ) ^ K) ^ 2 * n₀ by rw [mul_pow, mul_pow, ← pow_mul]; ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    ring
  rw [hsy] at htot
  have hpK : (0 : ℝ) < (p : ℝ) ^ K := by positivity
  have h5 : Real.exp (-Real.pi) * A * (K + 1) ≤ C * (2 * N * Real.sqrt n₀) := by
    have := htot
    have e : C * (2 * N * Real.sqrt n₀ * (p : ℝ) ^ K) = C * (2 * N * Real.sqrt n₀) * (p : ℝ) ^ K :=
      by ring
    rw [e, show Real.exp (-Real.pi) * A * ((K + 1) * (p : ℝ) ^ K) =
      Real.exp (-Real.pi) * A * (K + 1) * (p : ℝ) ^ K by ring] at this
    exact le_of_mul_le_mul_right this hpK
  have hK' : 2 * C * N * Real.sqrt n₀ * Real.exp Real.pi / A < K + 1 := by linarith
  rw [div_lt_iff₀ hA0] at hK'
  have hexp : Real.exp (-Real.pi) * Real.exp Real.pi = 1 := by
    rw [← Real.exp_add]; simp
  have h6 : A * (K + 1) ≤ C * (2 * N * Real.sqrt n₀) * Real.exp Real.pi := by
    have := mul_le_mul_of_nonneg_right h5 (Real.exp_pos Real.pi).le
    calc A * (K + 1) = Real.exp (-Real.pi) * A * (K + 1) * Real.exp Real.pi := by
          rw [show Real.exp (-Real.pi) * A * (K + 1) * Real.exp Real.pi =
            (Real.exp (-Real.pi) * Real.exp Real.pi) * (A * (K + 1)) by ring, hexp, one_mul]
      _ ≤ _ := this
  nlinarith

/-- **Every eigenvalue `c` of `U(p²)` on class forms satisfies `|c|² < p`.** -/
theorem upEnd_eigenvalue_norm_sq_lt {N r t : ℕ} (ψ : DirichletCharacter ℂ r) (hN : 0 < N)
    (h24 : 24 ∣ N) (hpN : p ∣ N) (hrN : r ∣ N) (ht : Squarefree t) {c : ℂ}
    (hc : Module.End.HasEigenvalue (upEnd ψ hN h24 hpN ht) c) : ‖c‖ ^ 2 < p := by
  obtain ⟨g, hg⟩ := hc.exists_hasEigenvector
  obtain ⟨hgE, hg0⟩ := hg
  have hgE' : upEnd ψ hN h24 hpN ht g = c • g := Module.End.mem_eigenspace_iff.1 hgE
  obtain ⟨f, hf, hfg⟩ := g.2
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  -- the eigen-equation on `ℍ`
  have hc' : ∀ τ : ℂ, 0 < τ.im → upOp p f τ = c * f τ := by
    intro τ hτ
    have := congrFun (congrArg (fun x : classSpace N r ψ t => (x : ℍ → ℂ)) hgE') ⟨τ, hτ⟩
    simp only [upEnd, LinearMap.restrict_apply, Submodule.coe_smul] at this
    rw [← hfg, upH_restrictUpper] at this
    simpa [restrictUpper_apply] using this
  -- a nonzero positive coefficient
  have hpos : ∃ n, 0 < n ∧ thetaTypeCoeff f n ≠ 0 := by
    by_contra hall
    push Not at hall
    have hz := thetaType_eq_zero_of_coeff_pos hN h4 hf.1 hall
    apply hg0
    ext τ
    rw [← hfg]
    simp [restrictUpper_apply, hz τ τ.2]
  obtain ⟨n₀, hn₀, ha⟩ := hpos
  exact norm_sq_lt_of_upOp_eigen hN h24 hpN hrN hf hc' hn₀ ha

end Eigen

end SSHecke

end VOA.Classification.COne
