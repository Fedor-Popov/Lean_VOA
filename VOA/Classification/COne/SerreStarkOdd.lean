/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkFEClass
import VOA.Classification.COne.SerreStarkBeta

/-!
# Serre–Stark S5-6: class forms for odd characters vanish

`serreStarkOddVanish24 : SerreStarkOddVanish24`.

For `ψ` odd and primitive, the continuation `G1_eq_G2` at `s = 1/2 − k` (`k` a large integer)
contains the factor `L(1 − 2k, ψ)`, a trivial zero (`Odd.LFunction_neg_two_mul_nat_sub_one`); by
Hecke's functional equation `L(k, W f) = 0` for all large integers `k`, so all coefficients of
`W f` vanish (`LSeries.tendsto_cpow_mul_atTop`), `W f = 0`, and `f = 0` (`fricke_fricke`).
-/

open Complex Filter Topology LSeries
open scoped UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-- L-series of θ-type forms converge absolutely for `Re s > 3/2`. -/
theorem lseriesSummable_thetaType {N : ℕ} (h4 : 4 ∣ N) (hN : 0 < N) {f : ℂ → ℂ}
    (hf : IsThetaTypeForm N f) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable (thetaTypeCoeff f) s := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_coeff_le h4 hN hf
  refine LSeriesSummable_of_isBigO_rpow (x := 3 / 2) hs ?_
  refine Asymptotics.IsBigO.of_bound B ?_
  filter_upwards [eventually_ge_atTop 4] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have e : (3 / 2 : ℝ) - 1 = 1 / 2 := by norm_num
  rw [e]
  exact hB n hn

/-- A Dirichlet series vanishing at all large integers has vanishing coefficients. -/
theorem coeff_eq_zero_of_LSeries_nat {b : ℕ → ℂ} (hb : abscissaOfAbsConv b < ⊤) {K : ℕ}
    (h : ∀ k : ℕ, K ≤ k → LSeries b k = 0) (n : ℕ) (hn : n ≠ 0) : b n = 0 := by
  set b' : ℕ → ℂ := fun n => if n = 0 then 0 else b n with hb'
  have hL : ∀ x : ℂ, LSeries b' x = LSeries b x :=
    fun x => LSeries_congr (fun {n} hn => by simp [hb', hn]) x
  have hb'a : abscissaOfAbsConv b' < ⊤ := by
    rw [abscissaOfAbsConv_congr (g := b) (fun {n} hn => by simp [hb', hn])]
    exact hb
  have key : ∀ m : ℕ, ∀ j ≤ m, b' j = 0 := by
    intro m
    induction m with
    | zero => intro j hj; simp [hb', Nat.le_zero.1 hj]
    | succ m ih =>
      intro j hj
      rcases Nat.lt_or_ge j (m + 1) with hlt | hge
      · exact ih j (by omega)
      · have hj : j = m + 1 := by omega
        subst hj
        have ht := LSeries.tendsto_cpow_mul_atTop ih hb'a
        have ht' := ht.comp tendsto_natCast_atTop_atTop
        have hzero : (fun x : ℝ => ((m : ℂ) + 1) ^ (x : ℂ) * LSeries b' x) ∘
            (fun k : ℕ => (k : ℝ)) =ᶠ[atTop] fun _ => 0 := by
          filter_upwards [eventually_ge_atTop K] with k hk
          simp only [Function.comp_apply]
          rw [hL, show ((k : ℝ) : ℂ) = (k : ℂ) by push_cast; rfl, h k hk, mul_zero]
        exact tendsto_nhds_unique (ht'.congr' hzero) tendsto_const_nhds
  have := key n n le_rfl
  simpa [hb', hn] using this

namespace ClassSetup

variable (S : ClassSetup)

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- For all large integers `k`, `1/2 − k` is good. -/
theorem eventually_good_half_sub : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → S.Good (1 / 2 - k) := by
  classical
  have hp : ∀ p : S.ι, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      IsUnit (1 - ((p.1 : ℂ) ^ (-(2 * (1 / 2 - (k : ℂ))))) • S.Mp p) := by
    intro p
    set R := (Matrix.charpolyRev (S.Mp p)).roots.toFinset
    set B : ℝ := ∑ x ∈ R, ‖x‖ + 1
    have hp1 : (1 : ℝ) < p.1 := by exact_mod_cast (S.prime p).one_lt
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt B hp1
    refine ⟨K + 1, fun k hk => ?_⟩
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← eval_charpolyRev_eq_det]
    intro hroot
    set x := (p.1 : ℂ) ^ (-(2 * (1 / 2 - (k : ℂ))))
    have hmem : x ∈ R := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots]
      · exact hroot
      · intro h0
        have := congrArg (Polynomial.eval 0) h0
        rw [Matrix.eval_charpolyRev, Polynomial.eval_zero] at this
        exact one_ne_zero this
    have hle : ‖x‖ ≤ ∑ x ∈ R, ‖x‖ :=
      Finset.single_le_sum (f := fun x => ‖x‖) (fun _ _ => norm_nonneg _) hmem
    have hnorm : ‖x‖ = (p.1 : ℝ) ^ (2 * (k : ℝ) - 1) := by
      rw [Complex.norm_natCast_cpow_of_pos (S.prime p).pos]
      congr 1
      simp; ring
    have hbig : (p.1 : ℝ) ^ K ≤ (p.1 : ℝ) ^ (2 * (k : ℝ) - 1) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hp1.le (by
        have : (K : ℝ) + 1 ≤ k := by exact_mod_cast hk
        linarith)
    linarith
  choose K hK using hp
  refine ⟨∑ p, K p, fun k hk => S.good_of_isUnit_Mp fun p => hK p k ?_⟩
  exact le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)) hk

end ClassSetup

/-- **Class forms for odd primitive characters vanish.** -/
theorem serreStarkOddVanish24 : SerreStarkOddVanish24 := by
  intro N hN h24 r ψ t f hprim hrN ht htN hodd hf n hn
  let S : ClassSetup := ⟨N, r, t, ψ, hN, h24, hrN, ht, htN⟩
  have h4 : 4 ∣ N := S.h4
  haveI : NeZero S.N := ⟨hN.ne'⟩
  haveI : NeZero S.r := ⟨fun h => by
    change r = 0 at h; rw [h] at hrN; exact hN.ne' (Nat.eq_zero_of_zero_dvd hrN)⟩
  have hW := isThetaTypeForm_fricke hN h24 hf.1
  obtain ⟨K, hK⟩ := S.eventually_good_half_sub
  -- `L(k, W f) = 0` for all large integers `k`
  have hLk : ∀ k : ℕ, K + 2 ≤ k → LSeries (thetaTypeCoeff (fricke N f)) k = 0 := by
    intro k hk
    have hk2 : (3 / 2 : ℝ) < ((k : ℂ)).re := by
      simp only [Complex.natCast_re]
      have : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      linarith
    have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    -- `1/2 − k ∈ Ω`
    have hs0 : (1 / 2 - (k : ℂ)) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      have : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      linarith
    have hs12 : (1 / 2 - (k : ℂ)) ≠ 1 / 2 := fun h => hk0 (by linear_combination -h)
    have hΩ : (1 / 2 - (k : ℂ)) ∈ S.Ω := ⟨hK k (by omega), hs0, hs12⟩
    have hG := S.G1_eq_G2 hf hΩ
    -- the trivial zero
    have hzero : DirichletCharacter.LFunction S.χN (2 * (1 / 2 - (k : ℂ))) = 0 := by
      have hCL := DirichletCharacter.LFunction_changeLevel S.hrN ψ (s := 2 * (1 / 2 - (k : ℂ)))
        (Or.inr (fun h => hk0 (by linear_combination -h / 2)))
      rw [show DirichletCharacter.changeLevel S.hrN ψ = S.χN from rfl] at hCL
      rw [hCL]
      have : 2 * (1 / 2 - (k : ℂ)) = -(2 * ((k - 1 : ℕ) : ℂ)) - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this, hodd.LFunction_neg_two_mul_nat_sub_one, zero_mul]
    rw [ClassSetup.G2, hzero, mul_zero, ClassSetup.G1] at hG
    -- `Γ(1/2 − k) ≠ 0`
    have hΓ : Gamma (1 / 2 - (k : ℂ)) ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro m hm
      have := congrArg Complex.re hm
      simp at this
      -- `1/2 − k = −m` is impossible for integers
      have h2 : (2 : ℝ) * (k - m) = 1 := by linarith
      have h3 : (2 * ((k : ℤ) - m) : ℤ) = 1 := by exact_mod_cast h2
      omega
    have hΛ : (fePair N f hN h24 hf.1).Λ (1 / 2 - (k : ℂ)) = 0 := by
      have := mul_eq_zero.1 hG
      rcases this with h | h
      · exact h
      · exact absurd (inv_eq_zero.1 h) hΓ
    have hFE := fePair_functional_equation hN h24 hf.1 (k : ℂ)
    rw [hΛ, fePair_symm_Λ_eq hN h24 hf.1 hk2] at hFE
    have hε := feRoot_ne_zero hN
    have hΓk : Gamma (k : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hc : ((feScale N : ℝ) : ℂ) ^ (-(k : ℂ)) ≠ 0 :=
      cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 (feScale_pos hN).ne'))
    have := hFE.symm
    simp only [mul_eq_zero, hε, hΓk, hc, false_or] at this
    exact this
  -- all coefficients of `W f` vanish
  have hab : abscissaOfAbsConv (thetaTypeCoeff (fricke N f)) < ⊤ := by
    have hs := lseriesSummable_thetaType h4 hN hW (s := 2) (by norm_num)
    exact lt_of_le_of_lt (hs.abscissaOfAbsConv_le) (by simp)
  have hWc : ∀ m, 0 < m → thetaTypeCoeff (fricke N f) m = 0 := fun m hm =>
    coeff_eq_zero_of_LSeries_nat hab (K := K + 2) (fun k hk => by
      have := hLk k hk; simpa using this) m hm.ne'
  have hW0 := thetaType_eq_zero_of_coeff_pos hN h4 hW hWc
  -- `f = 0` on `ℍ`
  have hf0 : ∀ τ : ℂ, 0 < τ.im → f τ = 0 := by
    intro τ hτ
    have h1 := fricke_fricke hN f hτ
    have h2 : fricke N (fricke N f) τ = 0 := by
      rw [fricke, hW0 _ (im_neg_inv_pos hN hτ), zero_mul, zero_div]
    rw [h2] at h1
    have hne : ((4 / N : ℝ) : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
      refine cpow_ne_zero_iff.2 (Or.inl ?_)
      exact Complex.ofReal_ne_zero.2 (by positivity)
    exact (mul_eq_zero.1 h1.symm).resolve_left hne
  rw [thetaTypeCoeff_congr (g := fun _ => 0) hf0]
  exact coeff_eq_zero_of_eq_zero (fun _ _ => rfl) n

end SSHecke

end VOA.Classification.COne
