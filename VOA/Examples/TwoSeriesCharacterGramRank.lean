/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesCharacterKacCount
import VOA.Examples.LYGramRank

/-!
# The Feigin–Fuchs rank bound for the vacuum Verma module of `M(2, 2n+3)`, proved

The generalisation of `LYGramRank` (the case `n = 1`) to every `n`: along the vacuum curve
`c(t) = 13 - 6t - 6/t`, `h = 0`, at `t₀ = 2/(2n+3)`, the corank of the complement block of the
Shapovalov form is at most the order of vanishing of its determinant, and the orders are the
Kac orders `aQ n m`, `bQ n m` of `TwoSeriesCharacterKacOrders`.  With `rcq_eq_orders`:

* `rank_boundQ` — `p(1+m) - p(m) - aQ n m + bQ n m ≤ rank G_{1+m}(c(t₀), 0)`;
* `rcq_le_gramRank` — `rcq n N ≤ rank (vermaGramMatrix c_{2,2n+3} 0 N)` for every `N`;
* `rcq_le_finrank` — **the Rocha-Caridi lower bound**
  `Σ_k (-1)^k p(N - k((2n+3)k + 2n+1)/2) ≤ dim L(c_{2,2n+3}, 0)_N`, for every `n` and `N`.

All proved, no hypotheses.  The proof is the corank-≤-order argument of `LYGramRank` verbatim,
with `t₀ = 2/5` replaced by `2/(2n+3)`.
-/

open Finset

noncomputable section

namespace VOA.TwoSeriesCharacter.KacGram

open VOA.InverseDS.VirasoroVerma VOA.VirasoroScreening VOA.Classification.COne
open VOA.Classification.COne.FFLower VOA.RRLower.LYGram
open Polynomial Filter Topology
open scoped Classical

variable (n : ℕ)

theorem charge_cont0 : ContinuousAt vermaBSACharge (t0 n) := by
  unfold vermaBSACharge
  exact (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).sub
    (continuousAt_const.div continuousAt_id (t0_ne n))

theorem weight_cont0 (N : ℕ) : ContinuousAt (vermaBSAWeight N) (t0 n) := by
  unfold vermaBSAWeight
  exact (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
    (mul_ne_zero (by norm_num) (t0_ne n))).sub continuousAt_const

theorem famB_cont0 (N m : ℕ) {ρ : Type*} (f : ρ → VermaPartitions (N + m) → ℂ)
    (x : VermaPartitions m ⊕ ρ) (i : VermaPartitions (N + m)) :
    ContinuousAt (fun t => famB t N m f x i) (t0 n) := by
  cases x with
  | inl lam =>
    simp only [famB, Sum.elim_inl, dc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact cAt_sum _ _ _ fun ν _ => (bsaS_cont0 N (t0 n) ν).mul continuousAt_const
  | inr j => exact continuousAt_const

theorem dT_cont0 (N m : ℕ) {ρ : Type*} [Fintype ρ]
    (e : VermaPartitions m ⊕ ρ ≃ VermaPartitions (N + m)) (f : ρ → VermaPartitions (N + m) → ℂ) :
    ContinuousAt (fun t => (Matrix.of fun i k => famB t N m f (e.symm k) i).det) (t0 n) :=
  continuousAt_det _ (t0 n) fun i k => famB_cont0 n N m f (e.symm k) i

theorem detD_cont0 (N L : ℕ) {ρ : Type*} [Fintype ρ] (f : ρ → VermaPartitions L → ℂ) :
    ContinuousAt (fun t => (Matrix.of fun j j' : ρ => f j ⬝ᵥ
      (vermaGramMatrix (vermaBSACharge t) (vermaBSAWeight N t) L).mulVec (f j')).det) (t0 n) := by
  refine continuousAt_det _ (t0 n) fun j j' => ?_
  simp only [Matrix.of_apply, dotProduct, Matrix.mulVec]
  exact cAt_sum _ _ _ fun i _ => continuousAt_const.mul (cAt_sum _ _ _ fun k _ =>
    (gram_cont _ _ (t0 n) (charge_cont0 n) (weight_cont0 n N) L i k).mul continuousAt_const)

theorem charge_subQ (t : ℂ) (ht : t ≠ 0) :
    vermaBSACharge t - vermaBSACharge (t0 n) = (t - t0 n) * (-6 + 6 / (t * t0 n)) := by
  have h0 := t0_ne n
  simp only [vermaBSACharge]
  field_simp
  ring

/-- **The level-`(1+m)` rank bound at `t₀ = 2/(2n+3)`.** -/
theorem rank_boundQ (m : ℕ) :
    (VOA.Classification.COne.FFLower.pp (1 + m) : ℤ) -
        (VOA.Classification.COne.FFLower.pp m : ℤ) - (aQ n m : ℤ) + (bQ n m : ℤ) ≤
      ((vermaGramMatrix (vermaBSACharge (t0 n)) 0 (1 + m)).rank : ℤ) := by
  have hN : 0 < 1 := by omega
  obtain ⟨ρ, _, e, f, hM⟩ := exists_complement _ (dc_linIndep (t0 n) (t0_ne n) 1 m hN)
  obtain ⟨ρ0, _, e0, f0, hM0⟩ := exists_complement _ (dc_linIndep (t0 n) (t0_ne n) 1 0 hN)
  have hρ0 : IsEmpty ρ0 := by
    have hc := Fintype.card_congr e0
    rw [Fintype.card_sum, card_vp_one, show Fintype.card (VermaPartitions 0) = 1 from pp_zero]
      at hc
    exact Fintype.card_eq_zero_iff.mp (by omega)
  set c0 := vermaBSACharge (t0 n) with hc0
  set k := Module.finrank ℂ (LinearMap.ker ((PD (1 + m) f).map (Polynomial.eval c0)).mulVecLin)
    with hk
  obtain ⟨Q, hQ⟩ := pow_dvd_det_of_ker (PD (1 + m) f) c0 (PD_symm (1 + m) f c0)
  rw [← hk] at hQ
  set dT : ℂ → ℂ := fun t => (Matrix.of fun i k => famB t 1 m f (e.symm k) i).det with hdT
  set dT0 : ℂ → ℂ := fun t => (Matrix.of fun i k => famB t 1 0 f0 (e0.symm k) i).det with hdT0
  set DD : ℂ → ℂ := fun t => (Matrix.of fun j j' : ρ => f j ⬝ᵥ (vermaGramMatrix (vermaBSACharge t)
      (vermaBSAWeight 1 t) (1 + m)).mulVec (f j')).det with hDD
  set DD0 : ℂ → ℂ := fun t => (Matrix.of fun j j' : ρ0 => f0 j ⬝ᵥ
      (vermaGramMatrix (vermaBSACharge t) (vermaBSAWeight 1 t) (1 + 0)).mulVec (f0 j')).det
    with hDD0
  set K := ∏ w : VermaPartitions (1 + m), vermaDiagonalContraction w.val with hK
  set K0 := ∏ w : VermaPartitions (1 + 0), vermaDiagonalContraction w.val with hK0
  set Km := ∏ w : VermaPartitions m, vermaDiagonalContraction w.val with hKm
  set Kz := ∏ w : VermaPartitions 0, vermaDiagonalContraction w.val with hKz
  set Den : ℂ → ℂ := fun t => Kz * GBq n 0 t * DD0 t with hDen
  set γ : ℂ → ℂ := fun t => dT0 t ^ 2 * K0 * GRq n 0 t / Den t with hγ
  set uu : ℂ → ℂ := fun t => -6 + 6 / (t * t0 n) with huu
  have hDD0_one : ∀ t, DD0 t = 1 := fun t => Matrix.det_isEmpty
  have hDen_cont : ContinuousAt Den (t0 n) :=
    (continuousAt_const.mul (GBq_cont n 0)).mul (detD_cont0 n _ _ f0)
  have hDen1 : Den (t0 n) ≠ 0 := by
    simp only [hDen, hDD0_one, mul_one]
    exact mul_ne_zero (diag_ne 0) (GBq_ne n 0)
  have hγ_cont : ContinuousAt γ (t0 n) :=
    ((((dT_cont0 n _ _ e0 f0).pow 2).mul continuousAt_const).mul (GRq_cont n 0)).div
      hDen_cont hDen1
  have huu_cont : ContinuousAt uu (t0 n) :=
    continuousAt_const.add (continuousAt_const.div (continuousAt_id.mul continuousAt_const)
      (mul_ne_zero (t0_ne n) (t0_ne n)))
  have hQc : ContinuousAt (fun t => Q.eval (vermaBSACharge t)) (t0 n) :=
    (Polynomial.continuous Q).continuousAt.comp (charge_cont0 n)
  have hDDQ : ∀ t, t ≠ 0 → DD t = ((t - t0 n) * uu t) ^ k * Q.eval (vermaBSACharge t) := by
    intro t ht
    simp only [hDD, weight_one]
    rw [← PD_map_eval, ← eval_det_poly, hQ, eval_mul, eval_pow, eval_sub, eval_X, eval_C,
      hc0, charge_subQ n t ht]
  have hev : ∀ᶠ t in 𝓝[≠] (t0 n), t ≠ 0 ∧ t ≠ t0 n ∧ Den t ≠ 0 := by
    have h0 : ∀ᶠ t in 𝓝 (t0 n), t ≠ 0 := eventually_ne_nhds (t0_ne n)
    have h2 : ∀ᶠ t in 𝓝 (t0 n), Den t ≠ 0 := hDen_cont.eventually_ne hDen1
    have h1 : ∀ᶠ t in 𝓝[≠] (t0 n), t ≠ t0 n := eventually_mem_nhdsWithin
    filter_upwards [nhdsWithin_le_nhds h0, h1, nhdsWithin_le_nhds h2] with t ha hb hc
    exact ⟨ha, hb, hc⟩
  have hpp : Fintype.card (VermaPartitions m) = VOA.Classification.COne.FFLower.pp m := rfl
  have hF : ∀ᶠ t in 𝓝[≠] (t0 n), dT t ^ 2 * K * ((t - t0 n) ^ aQ n m * GRq n m t) =
      γ t ^ VOA.Classification.COne.FFLower.pp m * (Km * ((t - t0 n) ^ bQ n m * GBq n m t)) *
        (((t - t0 n) * uu t) ^ k * Q.eval (vermaBSACharge t)) := by
    filter_upwards [hev] with t ⟨ht0, ht1, hDt⟩
    have I0 := curve_identity t ht0 1 0 hN e0 f0
    rw [kwpRest_eval_q n 0 t ht0, gram_shift_det_q n 0 t ht0, aQ_zero, bQ_zero,
      show Fintype.card (VermaPartitions 0) = 1 from pp_zero, pow_one, pow_zero, one_mul,
      one_mul] at I0
    have Im := curve_identity t ht0 1 m hN e f
    rw [kwpRest_eval_q n m t ht0, gram_shift_det_q n m t ht0, hpp] at Im
    have hβ : betaT t 1 = γ t := by
      simp only [hγ, hDen] at hDt ⊢
      rw [eq_div_iff hDt]
      linear_combination -I0
    rw [hβ] at Im
    rw [← hDDQ t ht0]
    exact Im
  have hord : bQ n m + k ≤ aQ n m := by
    by_contra hlt
    rw [not_le] at hlt
    set r := bQ n m + k - aQ n m with hr
    have hr0 : 0 < r := by omega
    have hF' : ∀ᶠ t in 𝓝[≠] (t0 n), dT t ^ 2 * K * GRq n m t =
        (t - t0 n) ^ r * (γ t ^ VOA.Classification.COne.FFLower.pp m * (Km * GBq n m t) *
          (uu t ^ k * Q.eval (vermaBSACharge t))) := by
      filter_upwards [hF, hev] with t h ⟨_, ht1, _⟩
      have hne : (t - t0 n) ^ aQ n m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr ht1)
      apply mul_left_cancel₀ hne
      have hsplit : (t - t0 n) ^ aQ n m * (t - t0 n) ^ r =
          (t - t0 n) ^ bQ n m * (t - t0 n) ^ k := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      calc (t - t0 n) ^ aQ n m * (dT t ^ 2 * K * GRq n m t)
          = dT t ^ 2 * K * ((t - t0 n) ^ aQ n m * GRq n m t) := by ring
        _ = _ := h
        _ = ((t - t0 n) ^ bQ n m * (t - t0 n) ^ k) *
              (γ t ^ VOA.Classification.COne.FFLower.pp m *
              (Km * GBq n m t) * (uu t ^ k * Q.eval (vermaBSACharge t))) := by rw [mul_pow]; ring
        _ = _ := by rw [← hsplit]; ring
    have hlim := eq_at (a := t0 n) (F1 := fun t => dT t ^ 2 * K * GRq n m t)
      (F2 := fun t => (t - t0 n) ^ r * (γ t ^ VOA.Classification.COne.FFLower.pp m *
        (Km * GBq n m t) * (uu t ^ k * Q.eval (vermaBSACharge t))))
      ((((dT_cont0 n _ _ e f).pow 2).mul continuousAt_const).mul (GRq_cont n m))
      (((continuousAt_id.sub continuousAt_const).pow r).mul
        (((hγ_cont.pow _).mul (continuousAt_const.mul (GBq_cont n m))).mul
          ((huu_cont.pow k).mul hQc))) hF'
    have hL1 : dT (t0 n) ^ 2 * K * GRq n m (t0 n) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ hM) (diag_ne _)) (GRq_ne n m)
    apply hL1
    simp only at hlim
    rw [hlim]
    simp only [sub_self, zero_pow hr0.ne', zero_mul]
  have hrn := ((PD (1 + m) f).map (Polynomial.eval c0)).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have hcard := Fintype.card_congr e
  rw [Fintype.card_sum] at hcard
  have hrk : ((PD (1 + m) f).map (Polynomial.eval c0)).rank ≤
      (vermaGramMatrix c0 0 (1 + m)).rank := by
    rw [PD_map_eval]; exact rank_compress_le _ f
  have hrk' : Module.finrank ℂ
      (LinearMap.range ((PD (1 + m) f).map (Polynomial.eval c0)).mulVecLin) =
      ((PD (1 + m) f).map (Polynomial.eval c0)).rank := rfl
  have h1 : (VOA.Classification.COne.FFLower.pp (1 + m) : ℤ) =
      (Fintype.card (VermaPartitions (1 + m)) : ℤ) := rfl
  have h2 : (VOA.Classification.COne.FFLower.pp m : ℤ) =
      (Fintype.card (VermaPartitions m) : ℤ) := rfl
  rw [h1, h2]
  omega

/-- The charge at `t₀` is `c_{2,2n+3} = bsaCharge (2n+2)`. -/
theorem charge_t0 : vermaBSACharge (t0 n) = VOA.VirModule.bsaCharge (2 * n + 2) := by
  have hQ := QC_ne n
  simp only [vermaBSACharge, VOA.VirModule.bsaCharge, t0]
  have e1 : (6 : ℂ) / (2 / QC n) = 3 * QC n := by field_simp; ring
  have e2 : (((2 * n + 2 : ℕ) : ℂ) + 1) = QC n := by simp only [QC]; push_cast; ring
  rw [e1, e2]
  ring

theorem rcq_zero : rcq n 0 = 1 := by
  unfold rcq
  have hI : Finset.Ico (-((0 : ℕ) : ℤ) - 1) ((0 : ℕ) + 1) = {-1, 0} := by decide
  rw [hI, Finset.sum_pair (by norm_num)]
  have h1 : eeq n (-1) = 1 := eeq_param n (by ring)
  have h0 : eeq n 0 = 0 := eeq_param n (by ring)
  rw [h1, h0]
  norm_num [VOA.RRLower.sgn, VOA.RRLower.pp_of_neg]
  decide

/-- **The Feigin–Fuchs rank bound for `M(c_{2,2n+3}, 0)`.** -/
theorem rcq_le_gramRank (N : ℕ) :
    rcq n N ≤ ((vermaGramMatrix (VOA.VirModule.bsaCharge (2 * n + 2)) 0 N).rank : ℤ) := by
  rw [← charge_t0]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    have hr : (vermaGramMatrix (vermaBSACharge (t0 n)) 0 0).rank = 1 := by
      rw [← vermaSimpleLevel_finrank_eq_gramRank, vermaSimpleLevel_zero_finrank]
    rw [hr, rcq_zero]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, N = 1 + m := ⟨N - 1, by omega⟩
    rw [rcq_eq_orders n m]
    have := rank_boundQ n m
    linarith

/-- **The Rocha-Caridi lower bound for the vacuum module of `M(2, 2n+3)`.** -/
theorem rcq_le_finrank (N : ℕ) :
    rcq n N ≤ (Module.finrank ℂ ((VOA.VirSimple.virasoroSimple
      (VOA.VirModule.bsaCharge (2 * n + 2))).grading (N : ℤ)) : ℤ) := by
  refine (rcq_le_gramRank n N).trans (Nat.cast_le.mpr ?_)
  rw [← vermaSimpleLevel_finrank_eq_gramRank]
  exact VOA.RRLower.vermaSimpleLevel_finrank_le _ N

end VOA.TwoSeriesCharacter.KacGram
