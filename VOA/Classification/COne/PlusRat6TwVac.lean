import VOA.Classification.COne.PlusRat6TwFock

/-! # The vacuum values `o(H⁴) = -1/128`, `o(H⁶) = 1/256` on the twisted Fock vacuum

With `x₀ = 1 ⊗ 1 ∈ FockT ⊗ ℂ` and `y(n,p) = (h₍₋ₙ₎ L(-1)^p h)₍ₙ₊ₚ₎ x₀` (the zero mode), the twisted
Jacobi identity at `ℓ = -n`, `k = 1` gives (`iter_eq`)

  `Σ_{i<n} C(1/2,i) y(n-i,p) + C(1/2,n+p+1) (p+1)! x₀ = 0`,

because `h₍ⱼ₎ L(-1)^p h` is `0` for `0 ≤ j ≤ p`, `(p+1)! 𝟙` for `j = p+1`, and `0` for `j ≥ p+2`
(grading).  Solving the twelve equations needed:  `o4_vac`, `o6_vac`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat6
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusRat3 PlusRat5
open VOA.Moonshine.LatticeTwistedGeneral VOA.TwistedHeisenberg VOA.Moonshine.LatticeTwisted
open scoped TensorProduct

variable (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2)

/-- The twisted vacuum `1 ⊗ 1`. -/
abbrev x0 : FockT (rank (latP m)) ⊗[ℂ] ℂ := (1 : FockT (rank (latP m))) ⊗ₜ[ℂ] (1 : ℂ)

/-- `L(-1)^p h`. -/
abbrev Lh (p : ℕ) : LatModuleGen (latP m) := ((V2m m hm).L (-1))^[p] (ls m hR)

theorem L_neg_one_mem_grading {k : ℤ} {v : LatModuleGen (latP m)} (hv : v ∈ (V2m m hm).grading k) :
    (V2m m hm).L (-1) v ∈ (V2m m hm).grading (k + 1) := by
  have h := (V2m m hm).smul_mem_grading (V2m m hm).conformal_mem hv 0
  rw [show (2 : ℤ) + k - 0 - 1 = k + 1 by ring] at h
  exact h

theorem Lh_mem (p : ℕ) : Lh m hm p ∈ (V2m m hm).grading ((p : ℤ) + 1) := by
  induction p with
  | zero => simpa using h_mem_grading m hm
  | succ p ih =>
    rw [Lh, Function.iterate_succ_apply']
    have := L_neg_one_mem_grading m hm ih
    rwa [show ((p + 1 : ℕ) : ℤ) + 1 = (p : ℤ) + 1 + 1 by push_cast; ring]

theorem smul_h_Lh_high (p j : ℕ) (hj : p + 2 ≤ j) :
    (V2m m hm).smul (ls m hR) (j : ℤ) (Lh m hm p) = 0 := by
  have h := (V2m m hm).smul_mem_grading (h_mem_grading m hm) (Lh_mem m hm p) (j : ℤ)
  rw [(V2m m hm).positivity _ (by push_cast; omega), Submodule.mem_bot] at h
  exact h

theorem Lh_eq (p : ℕ) : Lh m hm p = ls m (LmPow p hR) := (ls_LmPow m hm hR p).symm

theorem ls_vac (c : ℚ) : ls m [(c, [])] = (c : ℂ) • (V2m m hm).vacuum := by
  rw [ls, evR_cons, evR_nil, evalWord_nil, add_zero, latStateGen_csmul]
  rfl

theorem ls_nil : ls m ([] : RawPoly ℕ) = 0 := by
  rw [ls, evR_nil, latStateGen, TensorProduct.zero_tmul]

theorem smul_h_Lh_cert (p j : ℕ) (c : ℚ)
    (hc : normR (polyActW hR (-(j : ℤ) - 1) (LmPow p hR)) = normR [(c, [])]) :
    (V2m m hm).smul (ls m hR) (j : ℤ) (Lh m hm p) = (c : ℂ) • (V2m m hm).vacuum := by
  rw [Lh_eq, V2m_smul_ls, ← ls_normR, hc, ls_normR, ls_vac]

theorem smul_h_Lh_zero (p j : ℕ)
    (hc : normR (polyActW hR (-(j : ℤ) - 1) (LmPow p hR)) = normR []) :
    (V2m m hm).smul (ls m hR) (j : ℤ) (Lh m hm p) = 0 := by
  rw [Lh_eq, V2m_smul_ls, ← ls_normR, hc, ls_normR, ls_nil]

/-- The zero mode `y(n,p)` on the vacuum. -/
abbrev yv (n p : ℕ) : FockT (rank (latP m)) ⊗[ℂ] ℂ :=
  (Tw m hm t).YM ((V2m m hm).smul (ls m hR) (-(n : ℤ)) (Lh m hm p)) (2 * ((n : ℤ) + p)) (x0 m)

theorem YM_Lh_vac (p : ℕ) (q : ℤ) (hq : 2 * (p : ℤ) < q) (hodd : Odd q) :
    (Tw m hm t).YM (Lh m hm p) q (x0 m) = 0 := by
  rw [Lh, tw_deriv_iter (Tw m hm t) _ (theta_h m hm) p q hodd,
    YM_h_pos m hm t _ (by omega), smul_zero]

/-- The iterate equations on the vacuum. -/
theorem iter_eq (n p : ℕ) (hn : 1 ≤ n)
    (hz : ∀ j : ℕ, j ≤ p → (V2m m hm).smul (ls m hR) (j : ℤ) (Lh m hm p) = 0)
    (hv : (V2m m hm).smul (ls m hR) ((p + 1 : ℕ) : ℤ) (Lh m hm p) =
      (((p + 1).factorial : ℕ) : ℂ) • (V2m m hm).vacuum) :
    ∑ i ∈ Finset.range n, cbinom ((1 : ℂ) / 2) i • yv m hm t (n - i) p +
      (cbinom ((1 : ℂ) / 2) (n + p + 1) * (((p + 1).factorial : ℕ) : ℂ)) • x0 m = 0 := by
  have J := tw_iter_vac (Tw m hm t) (ls m hR) (mem_eig_one (theta_h m hm)) (Lh m hm p) (x0 m)
    (n : ℤ) (2 * ((n : ℤ) + p) - 1)
    (fun i => YM_h_pos m hm t _ (by omega))
    (fun i => YM_Lh_vac m hm t p _ (by omega) ⟨(n : ℤ) + p + i - 1, by ring⟩)
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (n + (p + 2))) _ (by
      intro i hi
      rw [Function.mem_support] at hi
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      apply hi
      have := smul_h_Lh_high m hm p (i - n) (by omega)
      rw [show (-(n : ℤ) + (i : ℤ)) = ((i - n : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : n ≤ i)]; ring,
        this, map_zero, Pi.zero_apply, LinearMap.zero_apply, smul_zero])] at J
  rw [Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_eq_zero (s := Finset.range (p + 1))
    (fun k hk => by
      rw [show (-(n : ℤ) + ((n + k : ℕ) : ℤ)) = ((k : ℕ) : ℤ) by push_cast; ring,
        hz k (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hk), map_zero, Pi.zero_apply,
        LinearMap.zero_apply, smul_zero]), zero_add] at J
  rw [show (-(n : ℤ) + ((n + (p + 1) : ℕ) : ℤ)) = ((p + 1 : ℕ) : ℤ) by push_cast; ring, hv,
    map_smul, Pi.smul_apply, LinearMap.smul_apply,
    show (1 : ℤ) + (2 * ((n : ℤ) + p) - 1) - 2 * ((n + (p + 1) : ℕ) : ℤ) = -2 by push_cast; ring,
    tw_vac, if_pos rfl, smul_smul, show n + (p + 1) = n + p + 1 by ring] at J
  have hsum : ∑ i ∈ Finset.range n, cbinom ((1 : ℂ) / 2) i • yv m hm t (n - i) p =
      ∑ i ∈ Finset.range n, cbinom ((1 : ℂ) / 2) i • (Tw m hm t).YM
        ((V2m m hm).smul (ls m hR) (-(n : ℤ) + (i : ℤ)) (Lh m hm p))
        (1 + (2 * ((n : ℤ) + p) - 1) - 2 * (i : ℤ)) (x0 m) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' := Finset.mem_range.mp hi
    rw [yv, show (-(n : ℤ) + (i : ℤ)) = -((n - i : ℕ) : ℤ) by push_cast [Nat.cast_sub hi'.le]; ring,
      show (1 : ℤ) + (2 * ((n : ℤ) + p) - 1) - 2 * (i : ℤ) = 2 * (((n - i : ℕ) : ℤ) + p) by
        push_cast [Nat.cast_sub hi'.le]; ring]
  rw [hsum]
  exact J

theorem cb1 : cbinom ((1 : ℂ) / 2) 1 = 1 / 2 := by norm_num [cbinom, Finset.prod_range_succ]
theorem cb2 : cbinom ((1 : ℂ) / 2) 2 = -1 / 8 := by norm_num [cbinom, Finset.prod_range_succ, Nat.factorial]
theorem cb3 : cbinom ((1 : ℂ) / 2) 3 = 1 / 16 := by norm_num [cbinom, Finset.prod_range_succ, Nat.factorial]
theorem cb4 : cbinom ((1 : ℂ) / 2) 4 = -5 / 128 := by norm_num [cbinom, Finset.prod_range_succ, Nat.factorial]
theorem cb5 : cbinom ((1 : ℂ) / 2) 5 = 7 / 256 := by norm_num [cbinom, Finset.prod_range_succ, Nat.factorial]
theorem cb6 : cbinom ((1 : ℂ) / 2) 6 = -21 / 1024 := by norm_num [cbinom, Finset.prod_range_succ, Nat.factorial]

theorem hz0 : ∀ j : ℕ, j ≤ 0 → (V2m m hm).smul (ls m hR) (j : ℤ) (Lh m hm 0) = 0 := by
  intro j hj
  obtain rfl : j = 0 := by omega
  exact smul_h_Lh_zero m hm 0 0 (by decide +kernel)

theorem hz1 : ∀ j : ℕ, j ≤ 1 → (V2m m hm).smul (ls m hR) (j : ℤ) (Lh m hm 1) = 0 := by
  intro j hj
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · exact smul_h_Lh_zero m hm 1 0 (by decide +kernel)
  · exact smul_h_Lh_zero m hm 1 1 (by decide +kernel)

theorem hz2 : ∀ j : ℕ, j ≤ 2 → (V2m m hm).smul (ls m hR) (j : ℤ) (Lh m hm 2) = 0 := by
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  · exact smul_h_Lh_zero m hm 2 0 (by decide +kernel)
  · exact smul_h_Lh_zero m hm 2 1 (by decide +kernel)
  · exact smul_h_Lh_zero m hm 2 2 (by decide +kernel)

theorem hv0 : (V2m m hm).smul (ls m hR) ((0 + 1 : ℕ) : ℤ) (Lh m hm 0) =
    (((0 + 1).factorial : ℕ) : ℂ) • (V2m m hm).vacuum := by
  rw [smul_h_Lh_cert m hm 0 1 1 (by decide +kernel)]; norm_num

theorem hv1 : (V2m m hm).smul (ls m hR) ((1 + 1 : ℕ) : ℤ) (Lh m hm 1) =
    (((1 + 1).factorial : ℕ) : ℂ) • (V2m m hm).vacuum := by
  rw [smul_h_Lh_cert m hm 1 2 2 (by decide +kernel)]; norm_num [Nat.factorial]

theorem hv2 : (V2m m hm).smul (ls m hR) ((2 + 1 : ℕ) : ℤ) (Lh m hm 2) =
    (((2 + 1).factorial : ℕ) : ℂ) • (V2m m hm).vacuum := by
  rw [smul_h_Lh_cert m hm 2 3 6 (by decide +kernel)]; norm_num [Nat.factorial]


theorem yv_10 : yv m hm t 1 0 = (1 / 8 : ℂ) • x0 m := by
  have e := iter_eq m hm t 1 0 (by norm_num) (hz0 m hm) (hv0 m hm)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cbinom_zero, Nat.factorial,
    one_smul] at e
  norm_num [cb1, cb2, cb3, cb4, cb5, cb6] at e
  linear_combination (norm := module) e

theorem yv_20 : yv m hm t 2 0 = (-1 / 8 : ℂ) • x0 m := by
  have e := iter_eq m hm t 2 0 (by norm_num) (hz0 m hm) (hv0 m hm)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cbinom_zero, Nat.factorial,
    one_smul] at e
  norm_num [cb1, cb2, cb3, cb4, cb5, cb6] at e
  linear_combination (norm := module) e - (1 / 2 : ℂ) • yv_10 m hm t

theorem yv_30 : yv m hm t 3 0 = (15 / 128 : ℂ) • x0 m := by
  have e := iter_eq m hm t 3 0 (by norm_num) (hz0 m hm) (hv0 m hm)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cbinom_zero, Nat.factorial,
    one_smul] at e
  norm_num [cb1, cb2, cb3, cb4, cb5, cb6] at e
  linear_combination (norm := module) e - (1 / 2 : ℂ) • yv_20 m hm t - (-1 / 8 : ℂ) • yv_10 m hm t

theorem yv_40 : yv m hm t 4 0 = (-7 / 64 : ℂ) • x0 m := by
  have e := iter_eq m hm t 4 0 (by norm_num) (hz0 m hm) (hv0 m hm)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cbinom_zero, Nat.factorial,
    one_smul] at e
  norm_num [cb1, cb2, cb3, cb4, cb5, cb6] at e
  linear_combination (norm := module) e - (1 / 2 : ℂ) • yv_30 m hm t - (-1 / 8 : ℂ) • yv_20 m hm t - (1 / 16 : ℂ) • yv_10 m hm t

theorem yv_50 : yv m hm t 5 0 = (105 / 1024 : ℂ) • x0 m := by
  have e := iter_eq m hm t 5 0 (by norm_num) (hz0 m hm) (hv0 m hm)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cbinom_zero, Nat.factorial,
    one_smul] at e
  norm_num [cb1, cb2, cb3, cb4, cb5, cb6] at e
  linear_combination (norm := module) e - (1 / 2 : ℂ) • yv_40 m hm t - (-1 / 8 : ℂ) • yv_30 m hm t - (1 / 16 : ℂ) • yv_20 m hm t - (-5 / 128 : ℂ) • yv_10 m hm t

theorem yv_11 : yv m hm t 1 1 = (-1 / 8 : ℂ) • x0 m := by
  have e := iter_eq m hm t 1 1 (by norm_num) (hz1 m hm) (hv1 m hm)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cbinom_zero, Nat.factorial,
    one_smul] at e
  norm_num [cb1, cb2, cb3, cb4, cb5, cb6] at e
  linear_combination (norm := module) e

theorem yv_21 : yv m hm t 2 1 = (9 / 64 : ℂ) • x0 m := by
  have e := iter_eq m hm t 2 1 (by norm_num) (hz1 m hm) (hv1 m hm)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cbinom_zero, Nat.factorial,
    one_smul] at e
  norm_num [cb1, cb2, cb3, cb4, cb5, cb6] at e
  linear_combination (norm := module) e - (1 / 2 : ℂ) • yv_11 m hm t

theorem yv_31 : yv m hm t 3 1 = (-9 / 64 : ℂ) • x0 m := by
  have e := iter_eq m hm t 3 1 (by norm_num) (hz1 m hm) (hv1 m hm)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cbinom_zero, Nat.factorial,
    one_smul] at e
  norm_num [cb1, cb2, cb3, cb4, cb5, cb6] at e
  linear_combination (norm := module) e - (1 / 2 : ℂ) • yv_21 m hm t - (-1 / 8 : ℂ) • yv_11 m hm t

theorem yv_41 : yv m hm t 4 1 = (35 / 256 : ℂ) • x0 m := by
  have e := iter_eq m hm t 4 1 (by norm_num) (hz1 m hm) (hv1 m hm)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cbinom_zero, Nat.factorial,
    one_smul] at e
  norm_num [cb1, cb2, cb3, cb4, cb5, cb6] at e
  linear_combination (norm := module) e - (1 / 2 : ℂ) • yv_31 m hm t - (-1 / 8 : ℂ) • yv_21 m hm t - (1 / 16 : ℂ) • yv_11 m hm t

theorem yv_12 : yv m hm t 1 2 = (15 / 64 : ℂ) • x0 m := by
  have e := iter_eq m hm t 1 2 (by norm_num) (hz2 m hm) (hv2 m hm)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cbinom_zero, Nat.factorial,
    one_smul] at e
  norm_num [cb1, cb2, cb3, cb4, cb5, cb6] at e
  linear_combination (norm := module) e

theorem yv_22 : yv m hm t 2 2 = (-9 / 32 : ℂ) • x0 m := by
  have e := iter_eq m hm t 2 2 (by norm_num) (hz2 m hm) (hv2 m hm)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cbinom_zero, Nat.factorial,
    one_smul] at e
  norm_num [cb1, cb2, cb3, cb4, cb5, cb6] at e
  linear_combination (norm := module) e - (1 / 2 : ℂ) • yv_12 m hm t

theorem yv_32 : yv m hm t 3 2 = (75 / 256 : ℂ) • x0 m := by
  have e := iter_eq m hm t 3 2 (by norm_num) (hz2 m hm) (hv2 m hm)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cbinom_zero, Nat.factorial,
    one_smul] at e
  norm_num [cb1, cb2, cb3, cb4, cb5, cb6] at e
  linear_combination (norm := module) e - (1 / 2 : ℂ) • yv_22 m hm t - (-1 / 8 : ℂ) • yv_12 m hm t

/-- `o(H⁴)` on the twisted vacuum. -/
theorem o4_vac : (Tw m hm t).YM (ls m H4R) 6 (x0 m) = (-1 / 128 : ℂ) • x0 m := by
  have h30 := yv_30 m hm t
  have h21 := yv_21 m hm t
  simp only [yv] at h30 h21
  rw [Lh_eq] at h21
  simp only [Lh, Function.iterate_zero, id] at h30
  norm_num at h30 h21
  rw [← ls_normR, certH4quad, ls_normR, PlusRat5.ls_append, PlusRat5.ls_scaleR, PlusRat5.ls_scaleR, ← V2m_smul_ls m hm,
    ← V2m_smul_ls m hm]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, LinearMap.add_apply,
    LinearMap.smul_apply]
  norm_num
  rw [h30, h21]
  module

/-- `o(H⁶)` on the twisted vacuum. -/
theorem o6_vac : (Tw m hm t).YM (ls m H6R) 10 (x0 m) = (1 / 256 : ℂ) • x0 m := by
  have h50 := yv_50 m hm t
  have h41 := yv_41 m hm t
  have h32 := yv_32 m hm t
  simp only [yv] at h50 h41 h32
  rw [Lh_eq] at h41 h32
  simp only [Lh, Function.iterate_zero, id] at h50
  norm_num at h50 h41 h32
  rw [← ls_normR, certH6quad, ls_normR, PlusRat5.ls_append, PlusRat5.ls_append, PlusRat5.ls_scaleR, PlusRat5.ls_scaleR, PlusRat5.ls_scaleR,
    ← V2m_smul_ls m hm, ← V2m_smul_ls m hm, ← V2m_smul_ls m hm]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, LinearMap.add_apply,
    LinearMap.smul_apply]
  norm_num
  rw [h50, h41, h32]
  module

end VOA.Classification.COne.PlusRat6
