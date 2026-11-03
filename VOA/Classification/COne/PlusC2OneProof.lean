/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusC2One
import VOA.Classification.COne.PlusC2Degree
import VOA.Core.WeakAssoc

/-!
# `Q₁ = Q₀·Ē`: the residual `SectorOneViaE` is a theorem for `m ≥ 2`

Notation of `PlusC2Sector.lean`; `y_n = h(−n)` (`X(n−1,a₀)`), `c = ⟨α⟩_{a₀}` (`c² = 2m`),
`E = x_α = e^α + e^{−α}`, `Tgt = C₂(V⁺) + E₍₋₁₎M(1)⁺`.

The proof follows Yamskulna (Comm. Algebra 32 (2004), Lemmas 4.4, 4.6, 4.7, 4.10) at charge 1:

* **base** (`base_mem`): `T(y_n e^α) = c·y_n y_1 e^α + n·y_{n+1} e^α` and
  `(y_n y_1 𝟙)₍₋₁₎e^α = y_n y_1 e^α + c(n + (−1)^{n−1})·y_{n+1} e^α` (exact, from the Borcherds
  iterate), so `(2m(n + (−1)^{n−1}) − n)·P(y_{n+1} e^α) ∈ Tgt`; the factor is nonzero for `m ≥ 2`
  (`factor_ne_zero`; it vanishes at `m = 1, n = 2`).  `P(y_1 e^α) = c⁻¹·P(T e^α) ∈ C₂`.
* **length induction** (`FilF_le_good`): for an even monomial `w`, `w₍₋₁₎e^α = w e^α + (lower)`;
  for an odd one `w = w'·y_n`, `w'₍₋₁₎(y_n e^α) = w e^α + (lower)`
  (`word_smul_neg_one_sub_mem_Fil`), and `w'₍₋₁₎` preserves `Tgt` (`smul_mem_tgt`: `C₂` is an
  ideal and `A₂(V⁺)` is commutative and associative, `M(1)⁺` is closed under products).

## Main results
* `sectorOneViaE_holds : 2 ≤ m → SectorOneViaE m hm`.
* `v2mPlusC2CofiniteFactGe2_of_m1PlusC2Line` — **`V2mPlusC2CofiniteFactGe2` from the single
  lattice-free residual `M1PlusC2Line`** (about the Heisenberg orbifold `M(1)⁺` only).
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN VOA.Moonshine LatMod
  MvPolynomial

namespace PlusC2

variable (m : ℕ) (hm : 1 ≤ m)


/-! ## §1  Preliminaries -/

/-- For `θ`-fixed `u`: `⟨u⟩₍ₙ₎P(v) = P(u₍ₙ₎v)`. -/
theorem smul_fixed_PP (u : LatModuleGen (latP m)) (hu : u ∈ VP m hm) (n : ℤ)
    (v : LatModuleGen (latP m)) :
    (V2mPlus m hm).smul ⟨u, hu⟩ n (PP m hm v) = PP m hm ((V2m m hm).smul u n v) := by
  apply Subtype.ext
  rw [V2mPlus_smul_coe, PP_coe, PP_coe, theta_smul, (mem_VP_iff m hm u).mp hu,
    PreVertexAlgebra.smul_smul_right, PreVertexAlgebra.smul_add_right]

theorem PP_smul_left (u : LatModuleGen (latP m)) (n : ℤ) (v : LatModuleGen (latP m))
    (hv : thetaLat (latP m) v = v) :
    PP m hm ((V2m m hm).smul u n v) = (V2mPlus m hm).smul (PP m hm u) n ⟨v, (mem_VP_iff m hm v).mpr hv⟩ := by
  apply Subtype.ext
  rw [V2mPlus_smul_coe, PP_coe, PP_coe, theta_smul]
  change _ = (V2m m hm).smul ((1 / 2 : ℂ) • (u + thetaLat (latP m) u)) n v
  rw [hv, PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_add_left]

theorem vacuum_mem_VP : latVacuumGen (latP m) ∈ VP m hm :=
  (mem_VP_iff m hm _).mpr (thetaLat_vacuum _)

/-- `P(T v) ∈ C₂(V⁺)`. -/
theorem PP_T_mem_O₂ (v : LatModuleGen (latP m)) :
    PP m hm ((V2m m hm).smul v (-2) (latVacuumGen (latP m))) ∈ O₂ (V2mPlus m hm) := by
  rw [PP_smul_left m hm v (-2) _ (thetaLat_vacuum _)]
  exact smul_le_neg_two_mem_O₂ _ _ _ le_rfl

/-- The target `Tgt = C₂(V⁺) + E₍₋₁₎M(1)⁺`. -/
noncomputable abbrev Tgt : Submodule ℂ (VP m hm) := O₂ (V2mPlus m hm) ⊔ eTimesM1Plus m hm

theorem E_smul_mem_tgt (q : FockN (rank (latP m))) :
    (V2mPlus m hm).smul (xP m hm ((1 : ℤ) : (latP m).carrier)) (-1) (PP m hm (latStateGen (latP m) q 0)) ∈ Tgt m hm :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨q, rfl⟩)

/-- Charge-0 states multiply into charge 0. -/
theorem smul_sector_zero (a b : FockN (rank (latP m))) (n : ℤ) :
    ∃ r : FockN (rank (latP m)),
      (V2m m hm).smul (latStateGen (latP m) a 0) n (latStateGen (latP m) b 0) = latStateGen (latP m) r 0 := by
  set S : Submodule ℂ (FockN (rank (latP m))) :=
    { carrier := {a | ∃ r, (V2m m hm).smul (latStateGen (latP m) a 0) n (latStateGen (latP m) b 0) =
        latStateGen (latP m) r 0}
      add_mem' := by
        rintro x y ⟨r, hr⟩ ⟨r', hr'⟩
        refine ⟨r + r', ?_⟩
        rw [latStateGen_add_boson, PreVertexAlgebra.smul_add_left, hr, hr', latStateGen_add_boson]
      zero_mem' := ⟨0, by simp [latStateGen]⟩
      smul_mem' := by
        rintro c x ⟨r, hr⟩
        refine ⟨c • r, ?_⟩
        rw [latStateGen_csmul, PreVertexAlgebra.smul_smul_left, hr, latStateGen_csmul] }
  suffices h : (⊤ : Submodule ℂ (FockN (rank (latP m)))) ≤ S from h Submodule.mem_top
  refine (gradingWN_iSup_eq_top _).ge.trans (iSup_le fun w => ?_)
  refine (gradingWN_le_span_words _ w).trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨l, -, rfl⟩
  have hx : latStateGen (latP m) b 0 ∈ Fil (latP m) (b.totalDegree : ℤ) 0 :=
    latStateGen_mem_Fil (latP m) b 0 le_rfl
  have h := (word_smul_mem_Fil (latP m) (latP_even m) (latP_posDef m hm) l n _ 0 _ hx).1
  rw [wordStateLatGen_eq] at h
  obtain ⟨r, -, hr⟩ := h
  exact ⟨r, hr.symm⟩

/-- `Tgt` is stable under `⟨u⟩₍₋₁₎` for `u ∈ M(1)⁺`. -/
theorem smul_mem_tgt (q : FockN (rank (latP m))) {t : VP m hm} (ht : t ∈ Tgt m hm) :
    (V2mPlus m hm).smul (PP m hm (latStateGen (latP m) q 0)) (-1) t ∈ Tgt m hm := by
  set W := V2mPlus m hm
  set u := PP m hm (latStateGen (latP m) q 0)
  set μ : VP m hm →ₗ[ℂ] VP m hm := mode (W.Y u) (-1) with hμ
  have hμapp : ∀ y, μ y = W.smul u (-1) y := fun y => by rw [hμ, PreVertexAlgebra.smul_def]
  rw [← hμapp]
  suffices hle : Tgt m hm ≤ (Tgt m hm).comap μ from hle ht
  refine sup_le ?_ ?_
  · intro z hz
    rw [Submodule.mem_comap, hμapp]
    exact Submodule.mem_sup_left (poissonMul_mem_O₂_right W u hz)
  · rw [eTimesM1Plus, Submodule.span_le]
    rintro _ ⟨q', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, hμapp]
    set E := xP m hm ((1 : ℤ) : (latP m).carrier)
    set u' := PP m hm (latStateGen (latP m) q' 0)
    -- `u·u'` is again in `M(1)⁺`
    obtain ⟨r, hr⟩ : ∃ r : FockN (rank (latP m)), W.smul u (-1) u' = PP m hm (latStateGen (latP m) r 0) := by
      have hu : (u : LatModuleGen (latP m)) = latStateGen (latP m)
          ((1 / 2 : ℂ) • (q + sigmaN _ q)) 0 := by
        rw [PP_coe, thetaLat_latStateGen, neg_zero, ← latStateGen_add_boson, ← latStateGen_csmul]
      have hu' : (u' : LatModuleGen (latP m)) = latStateGen (latP m)
          ((1 / 2 : ℂ) • (q' + sigmaN _ q')) 0 := by
        rw [PP_coe, thetaLat_latStateGen, neg_zero, ← latStateGen_add_boson, ← latStateGen_csmul]
      obtain ⟨r, hr⟩ := smul_sector_zero m hm ((1 / 2 : ℂ) • (q + sigmaN _ q))
        ((1 / 2 : ℂ) • (q' + sigmaN _ q')) (-1)
      refine ⟨r, ?_⟩
      rw [← PP_of_mem m hm (W.smul u (-1) u'), V2mPlus_smul_coe, hu, hu', hr]
    have hA : mk₂ W (W.smul u (-1) (W.smul E (-1) u')) = mk₂ W (W.smul E (-1) (W.smul u (-1) u')) := by
      have h1 := A₂_mul_mk W E u'
      have h2 := A₂_mul_mk W u (poissonMul W E u')
      have h3 := A₂_mul_mk W u u'
      have h4 := A₂_mul_mk W E (poissonMul W u u')
      simp only [poissonMul_def] at h1 h2 h3 h4
      rw [← h2, ← h1, ← h4, ← h3]
      ring
    have hdiff : W.smul u (-1) (W.smul E (-1) u') - W.smul E (-1) (W.smul u (-1) u') ∈ O₂ W := by
      rw [← mk₂_eq_zero_iff, map_sub, hA, sub_self]
    have hgen : W.smul E (-1) (W.smul u (-1) u') ∈ Tgt m hm := by
      rw [hr]; exact E_smul_mem_tgt m hm r
    have : W.smul u (-1) (W.smul E (-1) u') =
        (W.smul u (-1) (W.smul E (-1) u') - W.smul E (-1) (W.smul u (-1) u')) +
          W.smul E (-1) (W.smul u (-1) u') := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hdiff) hgen

/-! ## §2  The base: `P(y_n e^α) ∈ Tgt` -/

/-- The charge coordinate `c` of `α`, with `c² = 2m`. -/
noncomputable abbrev cα : ℂ := chargeCoord (latP m) ((1 : ℤ) : (latP m).carrier) (a0 m)

include hm in
theorem cα_sq : cα m * cα m = 2 * (m : ℂ) := by
  have h := sum_chargeCoord (latP m) (latP_posDef m hm) ((1 : ℤ) : (latP m).carrier)
    ((1 : ℤ) : (latP m).carrier)
  rw [sum_rankOne, latP_form] at h
  rw [h]; push_cast; ring

include hm in
theorem cα_ne_zero : cα m ≠ 0 := chargeCoord_one_ne_zero m hm

/-- `H = h_{a₀}(−1)𝟙`. -/
noncomputable abbrev Hb : LatModuleGen (latP m) := bosonState (latP m) (a0 m)

theorem a_eq_a0 (a : Fin (rank (latP m))) : a = a0 m := by
  have h1 : a.val < 1 := lt_of_lt_of_eq a.isLt (rank_latP m)
  exact Fin.ext (by simp only [a0]; omega)

/-- `H₍ⱼ₎(p ⊗ e^γ)` for the pure exponential `p = 1`. -/
theorem Hb_smul_one (j : ℤ) (γ : (latP m).carrier) :
    (V2m m hm).smul (Hb m) j (latStateGen (latP m) 1 γ) =
      if j < 0 then latStateGen (latP m) (X ((-j - 1).toNat, a0 m)) γ
      else if j = 0 then chargeCoord (latP m) γ (a0 m) • latStateGen (latP m) 1 γ else 0 := by
  unfold V2m
  rw [smul_bosonState_latStateGen]
  rcases lt_trichotomy j 0 with hj | hj | hj
  · rw [oscN_neg _ _ _ hj, mulXN_apply, mul_one, if_neg (by omega), add_zero, if_pos hj]
  · subst hj; simp [latStateGen]
  · rw [oscN_pos _ _ _ hj]
    simp [latStateGen, hj.ne', not_lt.mpr hj.le]

/-- `T e^α = c·y₁ e^α`. -/
theorem T_eAlpha :
    (V2m m hm).smul (latStateGen (latP m) 1 ((1 : ℤ) : (latP m).carrier)) (-2) (latVacuumGen (latP m)) =
      cα m • latStateGen (latP m) (X (0, a0 m)) ((1 : ℤ) : (latP m).carrier) := by
  have hvac : latVacuumGen (latP m) = latStateGen (latP m) (vacuumN _) 0 := rfl
  rw [hvac, V2m, show latStateGen (latP m) 1 ((1 : ℤ) : (latP m).carrier) =
      latChargeGen (latP m) ((1 : ℤ) : (latP m).carrier) from rfl,
    latVOA_smul_latChargeGen_state, latticeCocycle_zero_right, one_smul,
    show (latP m).form ((1 : ℤ) : (latP m).carrier) 0 = 0 by simp, sub_zero, add_zero,
    show -(-2 : ℤ) - 1 = ((1 : ℕ) : ℤ) by norm_num, EEVec_vacuum, if_pos (by norm_num),
    Int.toNat_natCast, show (1 : ℕ) = 0 + 1 from rfl, vSchur_succ, Finset.sum_range_one,
    vSchur_zero, mul_one, vVar_rankOne, ← latStateGen_csmul]
  norm_num

/-- `T(y_n e^α) = c·y_n y_1 e^α + n·y_{n+1} e^α` (`y_n = X(n−1)`, here `n = k+1`). -/
theorem T_yeAlpha (k : ℕ) :
    (V2m m hm).smul (latStateGen (latP m) (X (k, a0 m)) ((1 : ℤ) : (latP m).carrier)) (-2)
        (latVacuumGen (latP m)) =
      latStateGen (latP m) (cα m • (X (k, a0 m) * X (0, a0 m)) + ((k : ℂ) + 1) • X (k + 1, a0 m))
        ((1 : ℤ) : (latP m).carrier) := by
  set W := V2m m hm with hW
  have hy : latStateGen (latP m) (X (k, a0 m)) ((1 : ℤ) : (latP m).carrier) =
      W.smul (Hb m) (-(k : ℤ) - 1) (latStateGen (latP m) 1 ((1 : ℤ) : (latP m).carrier)) := by
    rw [hW]; unfold V2m; rw [smul_bosonState_neg_latStateGen, mul_one]
  have hcomm := VertexOperatorAlgebra.smul_comm_T W (Hb m) (latStateGen (latP m) 1 ((1 : ℤ) : (latP m).carrier)) (-(k : ℤ) - 1)
  simp only [PreVertexAlgebra.T_apply] at hcomm
  have hvac : W.vacuum = latVacuumGen (latP m) := rfl
  rw [hvac] at hcomm
  rw [hy, ← sub_eq_iff_eq_add.mpr hcomm]
  have hT := T_eAlpha m hm
  rw [hT, PreVertexAlgebra.smul_smul_right]
  have h1 : W.smul (Hb m) (-(k : ℤ) - 1) (latStateGen (latP m) (X (0, a0 m)) ((1 : ℤ) : (latP m).carrier)) =
      latStateGen (latP m) (X (k, a0 m) * X (0, a0 m)) ((1 : ℤ) : (latP m).carrier) := by
    rw [hW]; unfold V2m; rw [smul_bosonState_neg_latStateGen]
  have h2 : W.smul (Hb m) (-(k : ℤ) - 1 - 1) (latStateGen (latP m) 1 ((1 : ℤ) : (latP m).carrier)) =
      latStateGen (latP m) (X (k + 1, a0 m)) ((1 : ℤ) : (latP m).carrier) := by
    rw [Hb_smul_one, if_pos (by omega), show (-(-(k : ℤ) - 1 - 1) - 1).toNat = k + 1 by omega]
  rw [h1, h2, latStateGen_add_boson, latStateGen_csmul, latStateGen_csmul]
  rw [show ((-(k : ℤ) - 1 : ℤ) • latStateGen (latP m) (X (k + 1, a0 m)) ((1 : ℤ) : (latP m).carrier)) =
      (-((k : ℂ) + 1)) • latStateGen (latP m) (X (k + 1, a0 m)) ((1 : ℤ) : (latP m).carrier) by
    rw [← Int.cast_smul_eq_zsmul ℂ]; push_cast; ring_nf]
  rw [neg_smul, sub_neg_eq_add]

/-- `(y_n y_1 𝟙)₍₋₁₎e^α = y_n y_1 e^α + c(n − (−1)^n)·y_{n+1} e^α` (`n = k+1`; Yamskulna Lemma 4.4). -/
theorem word2_smul_eAlpha (k : ℕ) :
    (V2m m hm).smul (latStateGen (latP m) (X (k, a0 m) * X (0, a0 m)) 0) (-1)
        (latStateGen (latP m) 1 ((1 : ℤ) : (latP m).carrier)) =
      latStateGen (latP m) (X (k, a0 m) * X (0, a0 m)) ((1 : ℤ) : (latP m).carrier) +
        (cα m * ((k : ℂ) + 1 - (-1 : ℂ) ^ (k + 1))) •
          latStateGen (latP m) (X (k + 1, a0 m)) ((1 : ℤ) : (latP m).carrier) := by
  set W := V2m m hm with hW
  set x := latStateGen (latP m) 1 ((1 : ℤ) : (latP m).carrier) with hx
  have hu : latStateGen (latP m) (X (k, a0 m) * X (0, a0 m)) 0 = W.smul (Hb m) (-(k : ℤ) - 1) (Hb m) := by
    rw [hW]; unfold V2m
    exact (smul_bosonState_neg_latStateGen (latP m) (latP_even m) (latP_posDef m hm) (a0 m) k
      (X (0, a0 m)) 0).symm
  rw [hu, VertexOperatorAlgebra.mode_iterate W (Hb m) (Hb m) (-(k : ℤ) - 1) (-1) x]
  have hHx : ∀ j : ℤ, W.smul (Hb m) j x = if j < 0 then latStateGen (latP m) (X ((-j - 1).toNat, a0 m))
      ((1 : ℤ) : (latP m).carrier) else if j = 0 then cα m • x else 0 := by
    intro j; rw [hW, hx, Hb_smul_one]
  have hHy : ∀ j : ℤ, j < 0 → ∀ (p : FockN (rank (latP m))),
      W.smul (Hb m) j (latStateGen (latP m) p ((1 : ℤ) : (latP m).carrier)) =
        latStateGen (latP m) (X ((-j - 1).toNat, a0 m) * p) ((1 : ℤ) : (latP m).carrier) := by
    intro j hj p
    rw [hW]; unfold V2m
    have := smul_bosonState_neg_latStateGen (latP m) (latP_even m) (latP_posDef m hm) (a0 m) (-j - 1).toNat p
      ((1 : ℤ) : (latP m).carrier)
    rwa [show -(((-j - 1).toNat : ℕ) : ℤ) - 1 = j by omega] at this
  set f : ℕ → LatModuleGen (latP m) := fun i => ((-1:ℂ)^i * gBinom (-(k : ℤ) - 1) i) •
      (W.smul (Hb m) (-(k : ℤ) - 1 - i) (W.smul (Hb m) (-1 + i) x)
        - ((-1:ℂ)^(-(k : ℤ) - 1)) • W.smul (Hb m) (-(k : ℤ) - 1 + -1 - i) (W.smul (Hb m) i x)) with hf
  have hsupp : Function.support f ⊆ (({0, 1} : Finset ℕ) : Set ℕ) := by
    intro i hi
    by_contra hc
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or] at hc
    apply hi
    have h1 : W.smul (Hb m) (-1 + i) x = 0 := by
      rw [hHx, if_neg (by omega), if_neg (by omega)]
    have h2 : W.smul (Hb m) i x = 0 := by
      rw [hHx, if_neg (by omega), if_neg (by omega)]
    simp only [hf, h1, h2, PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero]
  rw [finsum_eq_sum_of_support_subset f hsupp, Finset.sum_pair (by norm_num)]
  have hX0 : W.smul (Hb m) (-1 + ((0 : ℕ) : ℤ)) x = latStateGen (latP m) (X (0, a0 m)) ((1 : ℤ) : (latP m).carrier) := by
    rw [hHx, if_pos (by norm_num)]; rfl
  have hX1 : W.smul (Hb m) (-1 + ((1 : ℕ) : ℤ)) x = cα m • x := by
    rw [hHx, if_neg (by norm_num), if_pos (by norm_num)]
  have h00 : W.smul (Hb m) ((0 : ℕ) : ℤ) x = cα m • x := by
    rw [hHx, if_neg (by norm_num), if_pos (by norm_num)]
  have h01 : W.smul (Hb m) ((1 : ℕ) : ℤ) x = 0 := by
    rw [hHx, if_neg (by norm_num), if_neg (by norm_num)]
  have hxX : x = latStateGen (latP m) 1 ((1 : ℤ) : (latP m).carrier) := rfl
  have hK : W.smul (Hb m) (-(k : ℤ) - 1 - ((1 : ℕ) : ℤ)) x =
      latStateGen (latP m) (X (k + 1, a0 m)) ((1 : ℤ) : (latP m).carrier) := by
    rw [hHx, if_pos (by omega), show (-(-(k : ℤ) - 1 - ((1 : ℕ) : ℤ)) - 1).toNat = k + 1 by omega]
  have hK' : W.smul (Hb m) (-(k : ℤ) - 1 + -1 - ((0 : ℕ) : ℤ)) x =
      latStateGen (latP m) (X (k + 1, a0 m)) ((1 : ℤ) : (latP m).carrier) := by
    rw [hHx, if_pos (by omega), show (-(-(k : ℤ) - 1 + -1 - ((0 : ℕ) : ℤ)) - 1).toNat = k + 1 by omega]
  have hL : W.smul (Hb m) (-(k : ℤ) - 1 - ((0 : ℕ) : ℤ))
      (latStateGen (latP m) (X (0, a0 m)) ((1 : ℤ) : (latP m).carrier)) =
      latStateGen (latP m) (X (k, a0 m) * X (0, a0 m)) ((1 : ℤ) : (latP m).carrier) := by
    rw [hHy _ (by omega), show (-(-(k : ℤ) - 1 - ((0 : ℕ) : ℤ)) - 1).toNat = k by omega]
  simp only [hf]
  rw [hX0, hX1, h00, h01, PreVertexAlgebra.smul_smul_right, PreVertexAlgebra.smul_smul_right,
    PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero, hK, hK', hL]
  have hz : ((-1 : ℂ) ^ (-(k : ℤ) - 1)) = (-1 : ℂ) ^ (k + 1) := by
    rw [show (-(k : ℤ) - 1) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    rcases neg_one_pow_eq_or ℂ (k + 1) with h | h <;> rw [h] <;> norm_num
  rw [hz]
  simp only [pow_zero, gBinom_zero, mul_one, one_smul, pow_one]
  have hb1 : gBinom (-(k : ℤ) - 1) 1 = -((k : ℂ) + 1) := by simp [gBinom]; ring
  rw [hb1]
  module

/-- The arithmetic factor `2m(n − (−1)^n) − n` is nonzero for `m ≥ 2`, `n ≥ 1`. -/
theorem factor_ne_zero (hm2 : 2 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    2 * (m : ℂ) * ((n : ℂ) - (-1 : ℂ) ^ n) - n ≠ 0 := by
  rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [Even.neg_one_pow ⟨j, rfl⟩]
    intro h
    have h' : (2 * (m : ℤ) * (((j + j : ℕ) : ℤ) - 1) - ((j + j : ℕ) : ℤ)) = 0 := by exact_mod_cast h
    push_cast at h'
    have : (2 : ℤ) ≤ m := by exact_mod_cast hm2
    have hj : (1 : ℤ) ≤ j := by omega
    nlinarith [mul_le_mul_of_nonneg_right this (show (0 : ℤ) ≤ 2 * j - 1 by omega)]
  · rw [Odd.neg_one_pow ⟨j, rfl⟩]
    intro h
    have h' : (2 * (m : ℤ) * (((2 * j + 1 : ℕ) : ℤ) - -1) - ((2 * j + 1 : ℕ) : ℤ)) = 0 := by exact_mod_cast h
    push_cast at h'
    have : (2 : ℤ) ≤ m := by exact_mod_cast hm2
    nlinarith

/-- `P(e^α) = ½E`. -/
theorem PP_eAlpha : PP m hm (latStateGen (latP m) 1 ((1 : ℤ) : (latP m).carrier)) =
    (1 / 2 : ℂ) • xP m hm ((1 : ℤ) : (latP m).carrier) := by
  apply Subtype.ext
  rw [PP_coe, thetaLat_latStateGen, sigmaN_one]
  rfl

/-- For a `σ`-even `q`: `P(q₍₋₁₎e^α) ∈ Tgt`. -/
theorem PP_smul_eAlpha_mem (q : FockN (rank (latP m))) (hq : sigmaN (rank (latP m)) q = q) :
    PP m hm ((V2m m hm).smul (latStateGen (latP m) q 0) (-1)
      (latStateGen (latP m) 1 ((1 : ℤ) : (latP m).carrier))) ∈ Tgt m hm := by
  have hu : latStateGen (latP m) q 0 ∈ VP m hm := by
    rw [mem_VP_iff, thetaLat_latStateGen, hq, neg_zero]
  rw [← smul_fixed_PP m hm _ hu, PP_eAlpha, PreVertexAlgebra.smul_smul_right]
  refine Submodule.smul_mem _ _ ?_
  set W := V2mPlus m hm
  set E := xP m hm ((1 : ℤ) : (latP m).carrier)
  have hswap := poissonMul_sub_swap_mem_O₂ W ⟨_, hu⟩ E
  simp only [poissonMul_def] at hswap
  have hgen : W.smul E (-1) ⟨_, hu⟩ ∈ Tgt m hm := by
    have := E_smul_mem_tgt m hm q
    rwa [PP_of_mem m hm ⟨_, hu⟩] at this
  have : W.smul ⟨_, hu⟩ (-1) E = (W.smul ⟨_, hu⟩ (-1) E - W.smul E (-1) ⟨_, hu⟩) +
      W.smul E (-1) ⟨_, hu⟩ := by abel
  rw [this]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hswap) hgen

include hm in
/-- **The base**: `P(y_n e^α) ∈ Tgt` for every `n ≥ 1`, when `m ≥ 2`. -/
theorem base_mem (hm2 : 2 ≤ m) (k : ℕ) :
    PP m hm (latStateGen (latP m) (X (k, a0 m)) ((1 : ℤ) : (latP m).carrier)) ∈ Tgt m hm := by
  rcases k with _ | j
  · have hT := PP_T_mem_O₂ m hm (latStateGen (latP m) 1 ((1 : ℤ) : (latP m).carrier))
    rw [T_eAlpha m hm, map_smul] at hT
    have := Submodule.smul_mem _ (cα m)⁻¹ hT
    rw [smul_smul, inv_mul_cancel₀ (cα_ne_zero m hm), one_smul] at this
    exact Submodule.mem_sup_left this
  · set x := latStateGen (latP m) 1 ((1 : ℤ) : (latP m).carrier)
    set Y := latStateGen (latP m) (X (j + 1, a0 m)) ((1 : ℤ) : (latP m).carrier)
    set F : ℂ := 2 * (m : ℂ) * (((j + 1 : ℕ) : ℂ) - (-1 : ℂ) ^ (j + 1)) - ((j + 1 : ℕ) : ℂ) with hF
    have hFne := factor_ne_zero m hm2 (j + 1) (by omega)
    have hR : cα m • (V2m m hm).smul (latStateGen (latP m) (X (j, a0 m) * X (0, a0 m)) 0) (-1) x -
        (V2m m hm).smul (latStateGen (latP m) (X (j, a0 m)) ((1 : ℤ) : (latP m).carrier)) (-2)
          (latVacuumGen (latP m)) = F • Y := by
      rw [word2_smul_eAlpha m hm j, T_yeAlpha m hm j, latStateGen_add_boson, latStateGen_csmul,
        latStateGen_csmul, smul_add, smul_smul, hF]
      have h2 := cα_sq m hm
      have : cα m * (cα m * ((j : ℂ) + 1 - (-1) ^ (j + 1))) = 2 * (m : ℂ) * ((j : ℂ) + 1 - (-1) ^ (j + 1)) := by
        rw [← mul_assoc, h2]
      rw [this]
      push_cast
      module
    have hmem : PP m hm (F • Y) ∈ Tgt m hm := by
      rw [← hR, map_sub, map_smul]
      refine Submodule.sub_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.mem_sup_left (PP_T_mem_O₂ m hm _))
      refine PP_smul_eAlpha_mem m hm _ ?_
      rw [sigmaN_mul, sigmaN_X, sigmaN_X, neg_mul_neg]
    rw [map_smul] at hmem
    have := Submodule.smul_mem _ F⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hFne, one_smul] at this

/-! ## §3  The length induction -/

theorem length_monoWordN' (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) :
    (monoWordN s).length = s.sum fun _ k => k := by
  classical
  rw [monoWordN, List.length_flatMap]
  simp only [List.length_replicate]
  rw [Finset.sum_map_toList]
  rfl

/-- The Fock states `f` with `P(f ⊗ e^α) ∈ Tgt`. -/
noncomputable def good : Submodule ℂ (FockN (rank (latP m))) :=
  (Tgt m hm).comap ((PP m hm).comp (stateMap (latP m) ((1 : ℤ) : (latP m).carrier)))

theorem mem_good (f : FockN (rank (latP m))) :
    f ∈ good m hm ↔ PP m hm (latStateGen (latP m) f ((1 : ℤ) : (latP m).carrier)) ∈ Tgt m hm :=
  Iff.rfl

theorem Fil_le_good {e : ℤ} (h : FilF (latP m) e ≤ good m hm) (x : LatModuleGen (latP m))
    (hx : x ∈ Fil (latP m) e ((1 : ℤ) : (latP m).carrier)) : PP m hm x ∈ Tgt m hm := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact h hp

include hm in
theorem FilF_le_good (hm2 : 2 ≤ m) : ∀ e : ℕ, FilF (latP m) (e : ℤ) ≤ good m hm := by
  intro e
  induction e with
  | zero =>
    rw [FilF, Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    have hs0 : s = 0 := by
      ext v
      have hle : s v ≤ s.sum fun _ k => k := by
        by_cases hv : v ∈ s.support
        · exact Finset.single_le_sum (f := fun v => s v) (fun _ _ => Nat.zero_le _) hv
        · rw [Finsupp.notMem_support_iff.mp hv]; exact Nat.zero_le _
      simp only [Nat.cast_zero] at hs
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    subst hs0
    rw [SetLike.mem_coe, mem_good, show (monomial 0 (1 : ℂ) : FockN (rank (latP m))) = 1 by simp, PP_eAlpha]
    have h := E_smul_mem_tgt m hm 1
    have hvac : PP m hm (latStateGen (latP m) 1 0) = (V2mPlus m hm).vacuum := by
      apply Subtype.ext
      rw [PP_coe, thetaLat_latStateGen, sigmaN_one, neg_zero, ← two_smul ℂ, smul_smul]
      norm_num; rfl
    rw [hvac, (PreVertexAlgebra.smul_vacuum_right _ _).1] at h
    exact Submodule.smul_mem _ _ h
  | succ e ih =>
    rw [FilF, Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe]
    rcases lt_or_eq_of_le hs with hlt | heq
    · exact ih (monomial_mem_FilF (latP m) s 1 (by push_cast at hlt ⊢; omega))
    · have hIH := Fil_le_good m hm ih
      have hdeg : (s.sum fun _ k => k) = e + 1 := by exact_mod_cast heq
      set l := monoWordN s with hl
      have hlen : (l.length : ℤ) = e + 1 := by rw [hl, length_monoWordN', hdeg]; push_cast; ring
      have hword : wordStateN l = monomial s 1 := wordStateN_monoWordN s
      rcases Nat.even_or_odd (e + 1) with hev | hodd
      · -- even length: `w₍₋₁₎e^α = w e^α + lower`
        have hD := word_smul_neg_one_sub_mem_Fil (latP m) (latP_even m) (latP_posDef m hm) l 0
          ((1 : ℤ) : (latP m).carrier) 1 (monomial_mem_FilF (latP m) 0 1 (by simp))
        rw [wordStateLatGen_eq, hword, mul_one, hlen] at hD
        have hD' := hIH _ (Fil_mono (latP m) (show (0 : ℤ) + (e + 1) - 1 ≤ e by omega) _ hD)
        have hlenN : l.length = e + 1 := by exact_mod_cast hlen
        have hσ : sigmaN (rank (latP m)) (monomial s 1) = monomial s 1 := by
          rw [← hword, sigmaN_wordStateN, hlenN, Even.neg_one_pow hev, one_smul]
        have hA := PP_smul_eAlpha_mem m hm (monomial s 1) hσ
        rw [mem_good]
        have : latStateGen (latP m) (monomial s 1) ((1 : ℤ) : (latP m).carrier) =
            (V2m m hm).smul (latStateGen (latP m) (monomial s 1) 0) (-1)
              (latStateGen (latP m) 1 ((1 : ℤ) : (latP m).carrier)) -
            ((V2m m hm).smul (latStateGen (latP m) (monomial s 1) 0) (-1)
              (latStateGen (latP m) 1 ((1 : ℤ) : (latP m).carrier)) -
              latStateGen (latP m) (monomial s 1) ((1 : ℤ) : (latP m).carrier)) := by abel
        rw [this, map_sub]
        exact Submodule.sub_mem _ hA hD'
      · -- odd length: `w'₍₋₁₎(y e^α) = w e^α + lower`
        obtain ⟨v, hv⟩ : ∃ v, s v ≠ 0 := by
          by_contra h
          push Not at h
          have : (s.sum fun _ k => k) = 0 := by
            rw [Finsupp.sum]; exact Finset.sum_eq_zero fun v _ => h v
          omega
        set s' := s - Finsupp.single v 1 with hs'
        have hle : Finsupp.single v 1 ≤ s := by
          intro w
          rw [Finsupp.single_apply]
          split_ifs with h
          · subst h; omega
          · exact Nat.zero_le _
        have hss : s' + Finsupp.single v 1 = s := tsub_add_cancel_of_le hle
        have hdeg' : (s'.sum fun _ k => k) = e := by
          have := Finsupp.sum_add_index' (f := s') (g := Finsupp.single v 1)
            (h := fun _ k => k) (fun _ => rfl) (fun _ _ _ => rfl)
          rw [hss, Finsupp.sum_single_index rfl, hdeg] at this
          omega
        set l' := monoWordN s' with hl'
        have hlen' : (l'.length : ℤ) = e := by rw [hl', length_monoWordN', hdeg']
        have hword' : wordStateN l' = monomial s' 1 := wordStateN_monoWordN s'
        obtain ⟨k, a⟩ := v
        have ha := a_eq_a0 m a
        subst ha
        have hD := word_smul_neg_one_sub_mem_Fil (latP m) (latP_even m) (latP_posDef m hm) l' 1
          ((1 : ℤ) : (latP m).carrier) (X (k, a0 m)) (by
            refine monomial_mem_FilF (latP m) _ _ ?_
            rw [Finsupp.sum_single_index rfl]; norm_num)
        rw [wordStateLatGen_eq, hword', hlen'] at hD
        have hmul : monomial s' (1 : ℂ) * X (k, a0 m) = monomial s 1 := by
          rw [X, monomial_mul, one_mul, hss]
        rw [hmul] at hD
        have hD' := hIH _ (Fil_mono (latP m) (show (1 : ℤ) + e - 1 ≤ e by omega) _ hD)
        have hσ' : sigmaN (rank (latP m)) (monomial s' 1) = monomial s' 1 := by
          have hl'N : l'.length = e := by exact_mod_cast hlen'
          have hev : Even e := by
            obtain ⟨t, ht⟩ := hodd
            exact ⟨t, by omega⟩
          rw [← hword', sigmaN_wordStateN, hl'N, Even.neg_one_pow hev, one_smul]
        have hu : latStateGen (latP m) (monomial s' 1) 0 ∈ VP m hm := by
          rw [mem_VP_iff, thetaLat_latStateGen, hσ', neg_zero]
        have hA : PP m hm ((V2m m hm).smul (latStateGen (latP m) (monomial s' 1) 0) (-1)
            (latStateGen (latP m) (X (k, a0 m)) ((1 : ℤ) : (latP m).carrier))) ∈ Tgt m hm := by
          rw [← smul_fixed_PP m hm _ hu]
          have := smul_mem_tgt m hm (monomial s' 1) (base_mem m hm hm2 k)
          rwa [PP_of_mem m hm ⟨_, hu⟩] at this
        rw [mem_good]
        have : latStateGen (latP m) (monomial s 1) ((1 : ℤ) : (latP m).carrier) =
            (V2m m hm).smul (latStateGen (latP m) (monomial s' 1) 0) (-1)
              (latStateGen (latP m) (X (k, a0 m)) ((1 : ℤ) : (latP m).carrier)) -
            ((V2m m hm).smul (latStateGen (latP m) (monomial s' 1) 0) (-1)
              (latStateGen (latP m) (X (k, a0 m)) ((1 : ℤ) : (latP m).carrier)) -
              latStateGen (latP m) (monomial s 1) ((1 : ℤ) : (latP m).carrier)) := by abel
        rw [this, map_sub]
        exact Submodule.sub_mem _ hA hD'

include hm in
/-- **`SectorOneViaE` holds for every `m ≥ 2`** (Yamskulna §4 at charge 1). -/
theorem sectorOneViaE_holds (hm2 : 2 ≤ m) : SectorOneViaE m hm := by
  intro f
  have := FilF_le_good m hm hm2 f.totalDegree (mem_FilF_of_totalDegree_le (latP m) f le_rfl)
  exact this

end PlusC2

open PlusC2

/-- **The single residual of the `C₂` fact**: the lattice-free statement `M1PlusC2Line`
(`dim R(M(1)⁺)_w ≤ 1` for large `w`, detected by `α(−1)^w`), for every `m ≥ 2`. -/
def V2mPlusM1Residual : Prop := ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → M1PlusC2Line m hm

/-- **`V2mPlusC2CofiniteFactGe2` from the single lattice-free residual `M1PlusC2Line`.** -/
theorem v2mPlusC2CofiniteFactGe2_of_m1PlusC2Line (h : V2mPlusM1Residual) :
    V2mPlusC2CofiniteFactGe2 :=
  v2mPlusC2CofiniteFactGe2_of_residuals fun m hm h2 => ⟨h m hm h2, sectorOneViaE_holds m hm h2⟩

end VOA.Classification.COne

section AxiomAudit
#print axioms VOA.Classification.COne.PlusC2.word2_smul_eAlpha
#print axioms VOA.Classification.COne.PlusC2.base_mem
#print axioms VOA.Classification.COne.PlusC2.sectorOneViaE_holds
#print axioms VOA.Classification.COne.v2mPlusC2CofiniteFactGe2_of_m1PlusC2Line
end AxiomAudit
