/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.LYGramCount
import VOA.Examples.RRLowerGram

/-!
# The Feigin–Fuchs rank bound for the Lee–Yang vacuum Verma module, proved

`RRLower.LeeYangGramRankBound : ∀ N, rc N ≤ rank (vermaGramMatrix (-22/5) 0 N)`.

## Method (a Jantzen-type corank bound along the vacuum curve)

Deform along the `(1,1)` curve `c(t) = 13 - 6t - 6/t`, `h = h_{1,1}(t) = 0`; the Lee–Yang point
is `t₀ = 2/5`.  On the whole curve `L_{-1}|0⟩` is singular, and `FFLower.curve_identity` (with
`N = 1`, level `1 + m`) gives, for every `t ≠ 0`,

`det(T)² · K · R(t) = β(t)^{p(m)} · det G_m(c(t), 1) · det D(c(t))`,

where `D(c)` is the Gram matrix at `h = 0` of a fixed complement `f` (chosen at `t₀`) of the
descendants `L_{-λ} L_{-1}|0⟩`.  `D` is a polynomial matrix in `c`, so (`pow_dvd_det_of_ker`, a
block-determinant argument) `(c - c₀)^k ∣ det D(c)` with `k = dim ker D(c₀)`.  Comparing the
orders of `t - 2/5` (`LYGramOrders`: `ord R = aLY m`, `ord det G_m(c(t),1) = bLY m`; `β` is
continuous at `t₀` by the same identity at `m = 0`) forces `k + bLY m ≤ aLY m`.  Hence

`rank G_{1+m}(c₀, 0) ≥ rank D(c₀) = |f| - k ≥ p(1+m) - p(m) - aLY m + bLY m = rc (1+m)`

by the exact count `rc_eq_orders` (`LYGramCount`).  This is the corank-≤-order bound only; no
statement about the Jantzen filtration beyond `J¹` is needed (the vacuum Jantzen filtration along
this curve has length one, which is why the bound is sharp).

* `leeYangGramRankBound_holds : LeeYangGramRankBound` — proved outright.

The consequences `leeYangRochaCaridiLowerBound_holds`, `leeYangRRLowerBound_holds`,
`leeYangRochaCaridiCharacter_holds` are in `LYGramRankCharacter.lean`, so that
this file does not import `RRLowerReduction`.
-/

open Finset

noncomputable section

namespace VOA.RRLower.LYGram

open VOA.InverseDS.VirasoroVerma VOA.VirasoroScreening VOA.Classification.COne
open VOA.Classification.COne.FFLower
open Polynomial Filter Topology
open scoped Classical

/-! ## Continuity at `t₀` -/

theorem bsaSource_cont0 (N r : ℕ) (cf hf : ℂ → ℂ) (a : ℂ)
    (ih : ∀ j < r, ∀ i : VermaPartitions j,
      ContinuousAt (fun t => lc (cf t) (hf t) j (vermaBSAState (cf t) (hf t) t N j) i) a)
    (i : VermaPartitions r) :
    ContinuousAt (fun t => lc (cf t) (hf t) r (vermaBSASource (cf t) (hf t) t N r) i) a := by
  have he : ∀ t, lc (cf t) (hf t) r (vermaBSASource (cf t) (hf t) t N r) i =
      ∑ j : Fin r, ∑ ν : VermaPartitions j,
        lc (cf t) (hf t) j (vermaBSAState (cf t) (hf t) t N j) ν * wc r ((r - 1 - j) :: ν.val) i := by
    intro t
    rw [vermaBSASource, lc_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : ((j : ℕ) : ℤ) - (r : ℤ) = -((r - 1 - j : ℕ) : ℤ) - 1 := by omega
    rw [hj, lc_mode_neg _ _ j (r - 1 - j) r (by omega) _ (vermaBSAState_mem_level _ _ t N j),
      Finset.sum_apply]
    rfl
  simp only [he]
  refine cAt_sum _ _ _ fun j _ => cAt_sum _ _ _ fun ν _ => ?_
  exact (ih j j.isLt ν).mul continuousAt_const

theorem bsaState_cont0 (N : ℕ) (cf hf : ℂ → ℂ) (a : ℂ) :
    ∀ r, ∀ i : VermaPartitions r,
      ContinuousAt (fun t => lc (cf t) (hf t) r (vermaBSAState (cf t) (hf t) t N r) i) a := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro i
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0
      have he : ∀ t, lc (cf t) (hf t) 0 (vermaBSAState (cf t) (hf t) t N 0) i = wc 0 [] i := by
        intro t
        rw [vermaBSAState_zero, ← negWord_nil,
          lc_eq_of_levelState _ _ _ _ _ (levelState_wc _ _ 0 [] rfl)]
      simp only [he]
      exact continuousAt_const
    · have he : ∀ t, lc (cf t) (hf t) r (vermaBSAState (cf t) (hf t) t N r) i =
          (-t / ((r : ℂ) * ((N : ℂ) - (r : ℂ)))) *
            lc (cf t) (hf t) r (vermaBSASource (cf t) (hf t) t N r) i := by
        intro t
        rw [vermaBSAState_eq_source _ _ _ N r hpos, lc_smul]
        rfl
      simp only [he]
      refine ContinuousAt.mul ?_ (bsaSource_cont0 N r cf hf a (fun j hj => ih j hj) i)
      exact (continuousAt_id.neg).div_const _

theorem bsaS_cont0 (N : ℕ) (a : ℂ) (i : VermaPartitions N) :
    ContinuousAt (fun t => bsaS t N i) a :=
  bsaSource_cont0 N N _ _ a (fun j _ => bsaState_cont0 N _ _ a j) i

theorem charge_cont0 : ContinuousAt vermaBSACharge t0 := by
  unfold vermaBSACharge
  exact (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).sub
    (continuousAt_const.div continuousAt_id t0_ne)

theorem weight_cont0 (N : ℕ) : ContinuousAt (vermaBSAWeight N) t0 := by
  unfold vermaBSAWeight
  exact (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
    (mul_ne_zero (by norm_num) t0_ne)).sub continuousAt_const

theorem famB_cont0 (N m : ℕ) {ρ : Type*} (f : ρ → VermaPartitions (N + m) → ℂ)
    (x : VermaPartitions m ⊕ ρ) (i : VermaPartitions (N + m)) :
    ContinuousAt (fun t => famB t N m f x i) t0 := by
  cases x with
  | inl lam =>
    simp only [famB, Sum.elim_inl, dc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact cAt_sum _ _ _ fun ν _ => (bsaS_cont0 N t0 ν).mul continuousAt_const
  | inr j => exact continuousAt_const

theorem dT_cont0 (N m : ℕ) {ρ : Type*} [Fintype ρ]
    (e : VermaPartitions m ⊕ ρ ≃ VermaPartitions (N + m)) (f : ρ → VermaPartitions (N + m) → ℂ) :
    ContinuousAt (fun t => (Matrix.of fun i k => famB t N m f (e.symm k) i).det) t0 :=
  continuousAt_det _ t0 fun i k => famB_cont0 N m f (e.symm k) i

theorem detD_cont0 (N n : ℕ) {ρ : Type*} [Fintype ρ] (f : ρ → VermaPartitions n → ℂ) :
    ContinuousAt (fun t => (Matrix.of fun j j' : ρ => f j ⬝ᵥ
      (vermaGramMatrix (vermaBSACharge t) (vermaBSAWeight N t) n).mulVec (f j')).det) t0 := by
  refine continuousAt_det _ t0 fun j j' => ?_
  simp only [Matrix.of_apply, dotProduct, Matrix.mulVec]
  exact cAt_sum _ _ _ fun i _ => continuousAt_const.mul (cAt_sum _ _ _ fun k _ =>
    (gram_cont _ _ t0 charge_cont0 (weight_cont0 N) n i k).mul continuousAt_const)

theorem eq_at {F1 F2 : ℂ → ℂ} {a : ℂ} (h1 : ContinuousAt F1 a) (h2 : ContinuousAt F2 a)
    (h : ∀ᶠ t in 𝓝[≠] a, F1 t = F2 t) : F1 a = F2 a :=
  tendsto_nhds_unique (h1.tendsto.mono_left nhdsWithin_le_nhds)
    ((h2.tendsto.mono_left nhdsWithin_le_nhds).congr' (h.mono fun _ ht => ht.symm))

/-! ## Corank of a polynomial matrix bounds the order of its determinant -/

/-- **Corank ≤ order.** If `P(c₀)` is symmetric with kernel of dimension `k`, then
`(X - c₀)^k` divides `det P`. -/
theorem pow_dvd_det_of_ker {ρ : Type} [Fintype ρ] (P : Matrix ρ ρ ℂ[X]) (c0 : ℂ)
    (hsym : (P.map (Polynomial.eval c0)).transpose = P.map (Polynomial.eval c0)) :
    ∃ Q : ℂ[X], P.det =
      (X - Polynomial.C c0) ^ Module.finrank ℂ (LinearMap.ker (P.map (Polynomial.eval c0)).mulVecLin) * Q := by
  set W := LinearMap.ker (P.map (Polynomial.eval c0)).mulVecLin with hW
  let bW := Module.finBasis ℂ W
  let v : Fin (Module.finrank ℂ W) → ρ → ℂ := fun j => (bW j : ρ → ℂ)
  have hv : LinearIndependent ℂ v := bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  obtain ⟨ρ', _, e, f, hM⟩ := exists_complement v hv
  have hb : ∀ k, (P.map (Polynomial.eval c0)).mulVec (Sum.elim v f (Sum.inl k)) = 0 := by
    intro k
    exact LinearMap.mem_ker.mp (bW k).2
  obtain ⟨Q, hQ, -⟩ := block_det e P c0 hsym (Sum.elim v f) hb
  set d := (Matrix.of fun i k => Sum.elim v f (e.symm k) i).det with hd
  refine ⟨Polynomial.C ((d ^ 2)⁻¹) * Q, ?_⟩
  rw [Fintype.card_fin] at hQ
  have hd2 : d ^ 2 ≠ 0 := pow_ne_zero _ hM
  calc P.det = Polynomial.C ((d ^ 2)⁻¹) * (Polynomial.C (d ^ 2) * P.det) := by
        rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hd2, Polynomial.C_1, one_mul]
    _ = _ := by rw [hQ]; ring

/-- A compression `Fᵀ G F` has rank at most `rank G`. -/
theorem rank_compress_le {ι ρ : Type} [Fintype ι] [Fintype ρ] (G : Matrix ι ι ℂ)
    (f : ρ → ι → ℂ) :
    (Matrix.of fun j j' : ρ => f j ⬝ᵥ G.mulVec (f j')).rank ≤ G.rank := by
  set F : Matrix ι ρ ℂ := Matrix.of fun i j => f j i with hF
  have heq : (Matrix.of fun j j' : ρ => f j ⬝ᵥ G.mulVec (f j')) = F.transpose * G * F := by
    ext j j'
    simp only [Matrix.of_apply, hF, Matrix.mul_apply, Matrix.transpose_apply, dotProduct,
      Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [heq]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- The vacuum Gram matrix with the central charge as the polynomial variable. -/
def GC (n : ℕ) : Matrix (VermaPartitions n) (VermaPartitions n) ℂ[X] :=
  vermaAlgebraGramMatrix (Polynomial.X : ℂ[X]) (Polynomial.C 0) n

theorem GC_map_eval (c : ℂ) (n : ℕ) : (GC n).map (Polynomial.eval c) = vermaGramMatrix c 0 n := by
  have he := vermaAlgebraGramMatrix_eval (Polynomial.X : ℂ[X]) (Polynomial.C 0)
    (Polynomial.aeval c) n
  have e1 : (Polynomial.aeval c) (Polynomial.C (0 : ℂ)) = 0 := by simp
  rw [aeval_X, e1] at he
  rw [← he]
  ext i j
  simp [GC]

/-- The complement block as a polynomial matrix in `c`. -/
def PD (n : ℕ) {ρ : Type} [Fintype ρ] (f : ρ → VermaPartitions n → ℂ) : Matrix ρ ρ ℂ[X] :=
  Matrix.of fun j j' => pairX (GC n) (f j) (f j')

theorem PD_map_eval (n : ℕ) {ρ : Type} [Fintype ρ] (f : ρ → VermaPartitions n → ℂ) (c : ℂ) :
    (PD n f).map (Polynomial.eval c) =
      Matrix.of fun j j' : ρ => f j ⬝ᵥ (vermaGramMatrix c 0 n).mulVec (f j') := by
  ext j j'
  simp only [PD, Matrix.map_apply, Matrix.of_apply, eval_pairX, GC_map_eval]

theorem PD_symm (n : ℕ) {ρ : Type} [Fintype ρ] (f : ρ → VermaPartitions n → ℂ) (c : ℂ) :
    ((PD n f).map (Polynomial.eval c)).transpose = (PD n f).map (Polynomial.eval c) := by
  rw [PD_map_eval]
  ext j j'
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, vermaGramMatrix_symm, dotProduct_comm]

/-! ## The corank bound at the Lee–Yang point -/

theorem charge_sub (t : ℂ) (ht : t ≠ 0) :
    vermaBSACharge t - vermaBSACharge t0 = (t - t0) * (-6 + 6 / (t * t0)) := by
  simp only [vermaBSACharge, t0]
  field_simp
  ring

theorem card_vp_one : Fintype.card (VermaPartitions 1) = 1 := by
  have h := ffpp_eq 1
  have h1 : pp ((1 : ℕ) : ℤ) = 1 := by decide
  rw [h1] at h
  exact_mod_cast h

/-- **The level-`(1+m)` rank bound**: `rank G_{1+m}(c(t₀), 0) + aLY m ≥ p(1+m) - p(m) + bLY m`. -/
theorem rank_bound (m : ℕ) :
    (VOA.Classification.COne.FFLower.pp (1 + m) : ℤ) -
        (VOA.Classification.COne.FFLower.pp m : ℤ) - (aLY m : ℤ) + (bLY m : ℤ) ≤
      ((vermaGramMatrix (vermaBSACharge t0) 0 (1 + m)).rank : ℤ) := by
  have hN : 0 < 1 := by omega
  obtain ⟨ρ, _, e, f, hM⟩ := exists_complement _ (dc_linIndep t0 t0_ne 1 m hN)
  obtain ⟨ρ0, _, e0, f0, hM0⟩ := exists_complement _ (dc_linIndep t0 t0_ne 1 0 hN)
  -- `ρ0` is empty: the level-1 space is spanned by `L_{-1}|0⟩`
  have hρ0 : IsEmpty ρ0 := by
    have hc := Fintype.card_congr e0
    rw [Fintype.card_sum, card_vp_one, show Fintype.card (VermaPartitions 0) = 1 from pp_zero]
      at hc
    exact Fintype.card_eq_zero_iff.mp (by omega)
  set c0 := vermaBSACharge t0 with hc0
  -- the polynomial complement block and its order at `c₀`
  set k := Module.finrank ℂ (LinearMap.ker ((PD (1 + m) f).map (Polynomial.eval c0)).mulVecLin) with hk
  obtain ⟨Q, hQ⟩ := pow_dvd_det_of_ker (PD (1 + m) f) c0 (PD_symm (1 + m) f c0)
  rw [← hk] at hQ
  -- the functions of `t`
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
  set Den : ℂ → ℂ := fun t => Kz * GBly 0 t * DD0 t with hDen
  set γ : ℂ → ℂ := fun t => dT0 t ^ 2 * K0 * GRly 0 t / Den t with hγ
  set uu : ℂ → ℂ := fun t => -6 + 6 / (t * t0) with huu
  have hDD0_one : ∀ t, DD0 t = 1 := fun t => Matrix.det_isEmpty
  have hDen_cont : ContinuousAt Den t0 :=
    (continuousAt_const.mul (GBly_cont 0)).mul (detD_cont0 _ _ f0)
  have hDen1 : Den t0 ≠ 0 := by
    simp only [hDen, hDD0_one, mul_one]
    exact mul_ne_zero (diag_ne 0) (GBly_ne 0)
  have hγ_cont : ContinuousAt γ t0 :=
    ((((dT_cont0 _ _ e0 f0).pow 2).mul continuousAt_const).mul (GRly_cont 0)).div hDen_cont hDen1
  have huu_cont : ContinuousAt uu t0 :=
    continuousAt_const.add (continuousAt_const.div (continuousAt_id.mul continuousAt_const)
      (mul_ne_zero t0_ne t0_ne))
  have hQc : ContinuousAt (fun t => Q.eval (vermaBSACharge t)) t0 :=
    (Polynomial.continuous Q).continuousAt.comp charge_cont0
  -- `DD t = (c(t) - c₀)^k · Q(c(t))`
  have hDDQ : ∀ t, t ≠ 0 → DD t = ((t - t0) * uu t) ^ k * Q.eval (vermaBSACharge t) := by
    intro t ht
    simp only [hDD, weight_one]
    rw [← PD_map_eval, ← eval_det_poly, hQ, eval_mul, eval_pow, eval_sub, eval_X, eval_C,
      hc0, charge_sub t ht]
  -- eventually: `t ≠ 0`, `t ≠ t₀`, `Den t ≠ 0`
  have hev : ∀ᶠ t in 𝓝[≠] t0, t ≠ 0 ∧ t ≠ t0 ∧ Den t ≠ 0 := by
    have h0 : ∀ᶠ t in 𝓝 t0, t ≠ 0 := eventually_ne_nhds t0_ne
    have h2 : ∀ᶠ t in 𝓝 t0, Den t ≠ 0 := hDen_cont.eventually_ne hDen1
    have h1 : ∀ᶠ t in 𝓝[≠] t0, t ≠ t0 := eventually_mem_nhdsWithin
    filter_upwards [nhdsWithin_le_nhds h0, h1, nhdsWithin_le_nhds h2] with t ha hb hc
    exact ⟨ha, hb, hc⟩
  have hpp : Fintype.card (VermaPartitions m) = VOA.Classification.COne.FFLower.pp m := rfl
  -- the curve identity with all orders displayed
  have hF : ∀ᶠ t in 𝓝[≠] t0, dT t ^ 2 * K * ((t - t0) ^ aLY m * GRly m t) =
      γ t ^ VOA.Classification.COne.FFLower.pp m * (Km * ((t - t0) ^ bLY m * GBly m t)) *
        (((t - t0) * uu t) ^ k * Q.eval (vermaBSACharge t)) := by
    filter_upwards [hev] with t ⟨ht0, ht1, hDt⟩
    have I0 := curve_identity t ht0 1 0 hN e0 f0
    rw [kwpRest_eval_LY 0 t ht0, gram_shift_det_LY 0 t ht0, aLY_zero, bLY_zero,
      show Fintype.card (VermaPartitions 0) = 1 from pp_zero, pow_one, pow_zero, one_mul,
      one_mul] at I0
    have Im := curve_identity t ht0 1 m hN e f
    rw [kwpRest_eval_LY m t ht0, gram_shift_det_LY m t ht0, hpp] at Im
    have hβ : betaT t 1 = γ t := by
      simp only [hγ, hDen] at hDt ⊢
      rw [eq_div_iff hDt]
      linear_combination -I0
    rw [hβ] at Im
    rw [← hDDQ t ht0]
    exact Im
  -- the order comparison
  have hord : bLY m + k ≤ aLY m := by
    by_contra hlt
    rw [not_le] at hlt
    set r := bLY m + k - aLY m with hr
    have hr0 : 0 < r := by omega
    have hF' : ∀ᶠ t in 𝓝[≠] t0, dT t ^ 2 * K * GRly m t =
        (t - t0) ^ r * (γ t ^ VOA.Classification.COne.FFLower.pp m * (Km * GBly m t) *
          (uu t ^ k * Q.eval (vermaBSACharge t))) := by
      filter_upwards [hF, hev] with t h ⟨_, ht1, _⟩
      have hne : (t - t0) ^ aLY m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr ht1)
      apply mul_left_cancel₀ hne
      have hsplit : (t - t0) ^ aLY m * (t - t0) ^ r = (t - t0) ^ bLY m * (t - t0) ^ k := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      calc (t - t0) ^ aLY m * (dT t ^ 2 * K * GRly m t)
          = dT t ^ 2 * K * ((t - t0) ^ aLY m * GRly m t) := by ring
        _ = _ := h
        _ = ((t - t0) ^ bLY m * (t - t0) ^ k) * (γ t ^ VOA.Classification.COne.FFLower.pp m *
              (Km * GBly m t) * (uu t ^ k * Q.eval (vermaBSACharge t))) := by rw [mul_pow]; ring
        _ = _ := by rw [← hsplit]; ring
    have hlim := eq_at (a := t0) (F1 := fun t => dT t ^ 2 * K * GRly m t)
      (F2 := fun t => (t - t0) ^ r * (γ t ^ VOA.Classification.COne.FFLower.pp m *
        (Km * GBly m t) * (uu t ^ k * Q.eval (vermaBSACharge t))))
      ((((dT_cont0 _ _ e f).pow 2).mul continuousAt_const).mul (GRly_cont m))
      (((continuousAt_id.sub continuousAt_const).pow r).mul
        (((hγ_cont.pow _).mul (continuousAt_const.mul (GBly_cont m))).mul
          ((huu_cont.pow k).mul hQc))) hF'
    have hL1 : dT t0 ^ 2 * K * GRly m t0 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ hM) (diag_ne _)) (GRly_ne m)
    apply hL1
    simp only at hlim
    rw [hlim]
    simp only [sub_self, zero_pow hr0.ne', zero_mul]
  -- rank–nullity for the complement block
  have hrn := ((PD (1 + m) f).map (Polynomial.eval c0)).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have hcard := Fintype.card_congr e
  rw [Fintype.card_sum] at hcard
  have hrk : ((PD (1 + m) f).map (Polynomial.eval c0)).rank ≤ (vermaGramMatrix c0 0 (1 + m)).rank := by
    rw [PD_map_eval]; exact rank_compress_le _ f
  have hrk' : Module.finrank ℂ (LinearMap.range ((PD (1 + m) f).map (Polynomial.eval c0)).mulVecLin) =
      ((PD (1 + m) f).map (Polynomial.eval c0)).rank := rfl
  have h1 : (VOA.Classification.COne.FFLower.pp (1 + m) : ℤ) =
      (Fintype.card (VermaPartitions (1 + m)) : ℤ) := rfl
  have h2 : (VOA.Classification.COne.FFLower.pp m : ℤ) = (Fintype.card (VermaPartitions m) : ℤ) :=
    rfl
  rw [h1, h2]
  omega

end VOA.RRLower.LYGram

namespace VOA.RRLower

open VOA.InverseDS.VirasoroVerma VOA.LeeYang

/-- **The Feigin–Fuchs rank bound for `M(-22/5, 0)`**, proved outright:
`Σ_k (-1)^k p(N - k(5k+3)/2) ≤ rank (vermaGramMatrix (-22/5) 0 N)` for every `N`. -/
theorem leeYangGramRankBound_holds : LeeYangGramRankBound := by
  intro N
  have hc : leeYangC = vermaBSACharge LYGram.t0 := by
    rw [LYGram.charge_t0]; rfl
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    have hr : (vermaGramMatrix leeYangC 0 0).rank = 1 := by
      rw [← vermaSimpleLevel_finrank_eq_gramRank,
        vermaSimpleLevel_zero_finrank]
    rw [hr]
    decide
  · obtain ⟨m, rfl⟩ : ∃ m, N = 1 + m := ⟨N - 1, by omega⟩
    rw [hc, LYGram.rc_eq_orders m]
    have := LYGram.rank_bound m
    linarith

end VOA.RRLower
