/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaTopTarget

/-!
# The Golay frame at weight two: frame letters, blocks of `(V₃⁺)₂`, zero modes on `(T⁺)₂`

Coordinates: a Leech vector is `x ∈ ℤ²⁴` with `⟨x,y⟩ = x·y/8` (`lv`); the frame vectors are
`w_j = 8e_j = ι(4e_j) ∈ Λ₀` (`fw`, `⟨w_j, x⟩ = x_j`, `⟨w_j,w_k⟩ = 8δ_jk`).

## Blocks of `(V₃⁺)₂`
An odd norm-4 Leech vector has all coordinates odd and `Σ xᵢ² = 32`, hence exactly one entry `±3`
(`exists_unique_three`, `lv_sq`); its position is the **block** `blk n`.  `(V₃⁺)₂` splits into 24
blocks of 2048 vectors `x_n`, matching `(T_s⁺)₂ = ⊕_j h_{w_j}(−½) ⊗ T_s`.

## Zero modes on `(T⁺)₂ = {h_v(−½) ⊗ t}` (`hP v t`, `v` in orthonormal coordinates)
* `actT_qV_hP` — `o(h_a h_b)(h_v ⊗ t) = h_{quadL v} ⊗ t`;
* `actT_lV_hP` — `o(e^γ + e^{−γ})(h_v ⊗ t) = 2⁻³ h_{v − 2⟨v,γ⟩γ} ⊗ e_γ t` (`|γ|² = 4`);
* `actT_dV_hP` — for the frame quadratic letters `dV α β = α(−1)β(−1)𝟙`:
  `o(dV α β)(h_v ⊗ t) = h_{(⟨α,β⟩/8) v + ½⟨v,β⟩α + ½⟨v,α⟩β} ⊗ t`;
* `actT_dV_fw_hP`, `actV_dV_fw` — the diagonal frame letter `w_j(−1)²𝟙` acts by `9` on block
  `j` and by `1` on the other blocks, on **both** `(V₃⁺)₂` (`n_j² ∈ {9,1}`) and `(T⁺)₂`.
* Also: `hP_mem_weight`, `hP_mem_frame`, `x0T_eq_hP`, `actV_dV` (source, `⟨α,n⟩⟨β,n⟩`).

## Status
`sorry`-free; `#print axioms`: `[propext, Classical.choice, Quot.sound]`.  Unconditional.  
Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaTop

open VOA VOA.Moonshine VOA.Moonshine.TrialityTw VOA.Moonshine.SigmaExist VOA.IntegralLattice
open VOA.LatGen HeisenbergN MvPolynomial VOA.TwistedHeisenberg VOA.Moonshine.InvForm
open VOA.Moonshine.LatticeTwisted VOA.Moonshine.Extraspecial
open Module (End)
open Submodule

/-! ## §1  Coordinates -/

/-- The integer coordinates `x ∈ ℤ²⁴` of a Leech vector (`⟨x,y⟩ = x·y/8`). -/
def lv (x : leech.carrier) : Fin 24 → ℤ := (show ↥Leech.carrier from x).1

theorem lv_add (x y : leech.carrier) : lv (x + y) = lv x + lv y := rfl

theorem lv_neg (x : leech.carrier) : lv (-x) = -lv x := rfl

theorem lv_sub (x y : leech.carrier) : lv (x - y) = lv x - lv y := rfl

theorem leech_form_lv (x y : leech.carrier) : leech.form x y = (lv x ⬝ᵥ lv y) / 8 := rfl

theorem eight_dvd_lv (x y : leech.carrier) : (8 : ℤ) ∣ lv x ⬝ᵥ lv y :=
  Leech.eight_dvd_dot (show ↥Leech.carrier from x).2 (show ↥Leech.carrier from y).2

theorem lv_dot (x y : leech.carrier) : lv x ⬝ᵥ lv y = 8 * leech.form x y := by
  rw [leech_form_lv, Int.mul_ediv_cancel' (eight_dvd_lv x y)]

/-- `4e_j ∈ A`. -/
theorem four_single_mem_subA (j : Fin 24) : (4 : ℤ) • (Pi.single j 1 : Fin 24 → ℤ) ∈ Leech.subA := by
  refine ⟨?_, ?_⟩
  · rw [show (4 : ℤ) • (Pi.single j 1 : Fin 24 → ℤ) = (2 : ℤ) • ((2 : ℤ) • Pi.single j 1) by
      rw [smul_smul]; norm_num]
    exact two_smul_mem_preimageOfCode Code.golay _
  · refine ⟨1, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, Finset.sum_pi_single', Finset.mem_univ,
      if_true]

/-- `a_j = 4e_j ∈ A = Λ₀` (in the `A`-coordinates). -/
def a4 (j : Fin 24) : lam0.carrier := (⟨_, four_single_mem_subA j⟩ : ↥Leech.subA)

/-- The frame vector `w_j = 8e_j = ι(a_j) ∈ Λ₀`. -/
noncomputable def fw (j : Fin 24) : leech.carrier := inclΛ (a4 j)

theorem lv_fw (j : Fin 24) : lv (fw j) = (8 : ℤ) • (Pi.single j 1 : Fin 24 → ℤ) := by
  change (2 : ℤ) • ((4 : ℤ) • (Pi.single j 1 : Fin 24 → ℤ)) = _
  rw [smul_smul]; norm_num

theorem form_fw_left (j : Fin 24) (x : leech.carrier) : leech.form (fw j) x = lv x j := by
  rw [leech_form_lv, lv_fw, smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul,
    Int.mul_ediv_cancel_left _ (by norm_num : (8 : ℤ) ≠ 0)]

theorem form_fw_fw (j k : Fin 24) : leech.form (fw j) (fw k) = if j = k then 8 else 0 := by
  rw [form_fw_left, lv_fw]
  by_cases h : j = k
  · subst h; simp
  · rw [if_neg h]; simp [Ne.symm h]

theorem fw_mem_lambda0 (j : Fin 24) : fw j ∈ lambda0 := (mem_range_inclΛ _).mp ⟨a4 j, rfl⟩

/-! ## §2  The odd norm-4 vectors `(∓3, ±1²³)` and their blocks -/

theorem lv_odd_of_not_mem {n : leech.carrier} (hn : n ∉ lambda0) (i : Fin 24) : Odd (lv n i) := by
  rcases (show ↥Leech.carrier from n).2 with h | h
  · exfalso
    apply hn
    rw [mem_lambda0]
    obtain ⟨a, _, ha⟩ := Leech.mem_subA2.1 h
    change (((show ↥Leech.carrier from n).1 0 : ℤ) : ZMod 2) = 0
    rw [← ha, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
    rw [show ((2 : ℤ) : ZMod 2) = 0 from rfl, zero_mul]
  · obtain ⟨a, _, ha⟩ := Leech.mem_subA2.1 h
    have hi := congrFun ha i
    rw [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hi
    change Odd ((show ↥Leech.carrier from n).1 i)
    have hu : Odd (Leech.uVec i) := by
      unfold Leech.uVec; split_ifs
      · exact ⟨2, by norm_num⟩
      · exact ⟨0, by norm_num⟩
    obtain ⟨k, hk⟩ := hu
    exact ⟨a i + k, by linarith⟩

theorem sum_sq_lv (n : leech.carrier) (h4 : leech.form n n = 4) : ∑ i, (lv n i) ^ 2 = 32 := by
  have h := lv_dot n n
  rw [h4] at h
  have h' : ∑ i, lv n i ^ 2 = lv n ⬝ᵥ lv n := by
    rw [dotProduct]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [h', h]; norm_num

/-- An odd vector of `ℤ²⁴` with `Σ fᵢ² = 32` has exactly one entry `±3`, the others `±1`. -/
theorem exists_unique_three (f : Fin 24 → ℤ) (hodd : ∀ i, Odd (f i)) (hs : ∑ i, f i ^ 2 = 32) :
    ∃ j, f j ^ 2 = 9 ∧ ∀ i, i ≠ j → f i ^ 2 = 1 := by
  have hg : ∀ i, ∃ g : ℤ, 0 ≤ g ∧ f i ^ 2 = 8 * g + 1 := by
    intro i
    obtain ⟨k, hk⟩ := hodd i
    refine ⟨k * (k + 1) / 2, ?_, ?_⟩
    · rcases le_or_gt 0 k with h | h
      · exact Int.ediv_nonneg (by positivity) (by norm_num)
      · exact Int.ediv_nonneg (by nlinarith) (by norm_num)
    · have h2 : (2 : ℤ) ∣ k * (k + 1) := by
        rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
        · exact ⟨m * (k + 1), by rw [hm]; ring⟩
        · exact ⟨k * (m + 1), by rw [hm]; ring⟩
      rw [hk]
      have := Int.ediv_mul_cancel h2
      nlinarith [this]
  choose g hg0 hgf using hg
  have hsum : ∑ i, g i = 1 := by
    have h1 : ∑ i, f i ^ 2 = ∑ i, (8 * g i + 1) := Finset.sum_congr rfl fun i _ => hgf i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs] at h1
    simp at h1
    omega
  obtain ⟨j, hj⟩ : ∃ j, 0 < g j := by
    by_contra hc
    push Not at hc
    have : ∑ i, g i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (hc i) (hg0 i)
    omega
  have hsplit := Finset.add_sum_erase Finset.univ g (Finset.mem_univ j)
  rw [hsum] at hsplit
  have hrest : 0 ≤ ∑ i ∈ Finset.univ.erase j, g i := Finset.sum_nonneg fun i _ => hg0 i
  have hgj : g j = 1 := by omega
  have hrest0 : ∑ i ∈ Finset.univ.erase j, g i = 0 := by omega
  refine ⟨j, by rw [hgf, hgj]; norm_num, fun i hi => ?_⟩
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hg0 i)).mp hrest0 i
    (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
  rw [hgf, this]; norm_num

open Classical in
/-- The block of `n`: the position of the entry `±3`. -/
noncomputable def blk (n : leech.carrier) : Fin 24 :=
  if h : ∃ j, lv n j ^ 2 = 9 then h.choose else 0

/-- For `n ∉ Λ₀` of norm 4: `n_j² = 9` at `j = blk n` and `1` elsewhere. -/
theorem lv_sq {n : leech.carrier} (hn : n ∉ lambda0) (h4 : leech.form n n = 4) (j : Fin 24) :
    lv n j ^ 2 = if j = blk n then 9 else 1 := by
  obtain ⟨j₀, hj₀, hother⟩ := exists_unique_three (lv n) (lv_odd_of_not_mem hn) (sum_sq_lv n h4)
  have hex : ∃ j, lv n j ^ 2 = 9 := ⟨j₀, hj₀⟩
  have hb : blk n = j₀ := by
    rw [blk, dif_pos hex]
    by_contra hne
    have := hother _ hne
    rw [hex.choose_spec] at this
    norm_num at this
  rw [hb]
  split_ifs with h
  · rw [h, hj₀]
  · exact hother j h

theorem blk_neg (n : leech.carrier) : blk (-n) = blk n := by
  unfold blk
  simp only [lv_neg, Pi.neg_apply, neg_sq]

/-! ## §3  The top level `(T⁺)₂ = h(−½) ⊗ T` -/

/-- `h_v(−½) = Σ_a v_a X_{(0,a)}` for `v` in the orthonormal coordinates of `Λ ⊗ ℂ`. -/
noncomputable def hvec (v : Fin (rank leech) → ℂ) : FockT 24 := ∑ a, v a • (X (0, cc a) : FockT 24)

theorem hvec_add (v w : Fin (rank leech) → ℂ) : hvec (v + w) = hvec v + hvec w := by
  simp only [hvec, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem hvec_smul (c : ℂ) (v : Fin (rank leech) → ℂ) : hvec (c • v) = c • hvec v := by
  simp only [hvec, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

theorem hvec_sub (v w : Fin (rank leech) → ℂ) : hvec (v - w) = hvec v - hvec w := by
  simp only [hvec, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem hvec_single (a : Fin (rank leech)) : hvec (Pi.single a 1) = X (0, cc a) := by
  rw [hvec, Finset.sum_eq_single a (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul])
    (by simp), Pi.single_eq_same, one_smul]

theorem hvec_mem_gradingT (v : Fin (rank leech) → ℂ) : hvec v ∈ gradingT 24 1 := by
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
  have := MvPolynomial.isWeightedHomogeneous_X ℂ (wT (r := 24)) (0, cc a)
  simpa using this

/-- `h_v(−½) ⊗ t`. -/
noncomputable def hT (v : Fin (rank leech) → ℂ) (t : TLeechT) : Tw := hvec v ⊗ₜ t

theorem thetaT_hvec (v : Fin (rank leech) → ℂ) : thetaT 24 (hvec v) = -hvec v := by
  simp only [hvec, map_sum, map_smul, thetaT_X, smul_neg, Finset.sum_neg_distrib]

theorem hT_mem_TP (v : Fin (rank leech) → ℂ) (t : TLeechT) : hT v t ∈ TP := by
  rw [TwistedPlus.mem_plusSub]
  change TwistedSector.twTheta 24 leechT (hvec v ⊗ₜ t) = hvec v ⊗ₜ t
  rw [TwistedSector.twTheta_tmul, thetaT_hvec, TensorProduct.neg_tmul, TensorProduct.tmul_neg,
    neg_neg]

/-- `h_v(−½) ⊗ t ∈ (T⁺)₂`. -/
noncomputable def hP (v : Fin (rank leech) → ℂ) (t : TLeechT) : TP := ⟨hT v t, hT_mem_TP v t⟩

theorem hP_coe (v : Fin (rank leech) → ℂ) (t : TLeechT) : (hP v t : Tw) = hvec v ⊗ₜ t := rfl

theorem hP_mem_weight (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    hP v t ∈ plusModule.weight (2 : ℂ) := by
  have hg : hT v t ∈ TwistedSector.twGrading 24 leechT 1 :=
    TwistedSector.tmul_mem_twGrading 24 leechT (hvec_mem_gradingT v) t
  have hw : hT v t ∈ TwistedSector.twWeight 24 leechT ((2 : ℚ)) := by
    have h := TwistedSector.twWeight_levelT 24 leechT 1
    have h1 : levelT 24 1 = (2 : ℚ) := by
      have := TwistedSector.levelT_24_odd 0
      simpa using this
    rw [h1] at h
    rw [h]; exact hg
  have hmem : hT v t ∈ (plusModule.weight ((2 : ℚ) : ℂ)).map TP.subtype := by
    rw [map_plusModule_weight]
    exact ⟨TwistedSector.twGrading_le_twFixed (by decide) hg, hw⟩
  obtain ⟨y, hy, hyx⟩ := hmem
  have : y = hP v t := Subtype.ext hyx
  rw [← this]
  simpa using hy

theorem hP_mem_frame {s : ZMod 2} (v : Fin (rank leech) → ℂ) {t : TLeechT}
    (ht : t ∈ leechFrameT s) : hP v t ∈ TPframe s := by
  rw [mem_TPframe, hP_coe, mem_twFrameL, LinearMap.lTensor_tmul, (FrameT.mem_frameT _ _ _).mp ht,
    TensorProduct.tmul_smul]

theorem hP_add_left (v w : Fin (rank leech) → ℂ) (t : TLeechT) : hP (v + w) t = hP v t + hP w t := by
  apply Subtype.ext; simp only [hP_coe, Submodule.coe_add, hvec_add, TensorProduct.add_tmul]

theorem hP_smul_left (c : ℂ) (v : Fin (rank leech) → ℂ) (t : TLeechT) : hP (c • v) t = c • hP v t := by
  apply Subtype.ext; simp only [hP_coe, Submodule.coe_smul, hvec_smul, TensorProduct.smul_tmul']

theorem x0T_eq_hP (t : TLeechT) : x0T t = hP (Pi.single (Fin.cast leech_rank.symm 0) 1) t := by
  apply Subtype.ext
  rw [hP_coe, hvec_single]
  rfl

/-! ## §4  The zero modes of the letters on `(T⁺)₂` -/

theorem cc_inj {a b : Fin (rank leech)} : cc a = cc b ↔ a = b := (Fin.cast_injective leech_rank).eq_iff

theorem pi_eq_sum_single (v : Fin (rank leech) → ℂ) : v = ∑ c, v c • Pi.single c (1 : ℂ) := by
  ext i; simp [Finset.sum_apply, Pi.single_apply]

/-- `v ↦ (δ_ab/8) v + ½ v_b e_a + ½ v_a e_b`, the action of `o(h_a h_b)` on `h_v(−½)`. -/
noncomputable def quadL (a b : Fin (rank leech)) :
    (Fin (rank leech) → ℂ) →ₗ[ℂ] (Fin (rank leech) → ℂ) :=
  (if a = b then (1 / 8 : ℂ) else 0) • LinearMap.id
    + (1 / 2 : ℂ) • (LinearMap.proj b).smulRight (Pi.single a 1)
    + (1 / 2 : ℂ) • (LinearMap.proj a).smulRight (Pi.single b 1)

theorem actT_coe (u : V0Sub.carrier) (n : ℤ) (y : TP) :
    ((actT u n y : TP) : Tw) = leechTwistedModule.YM ((u : VPlus) : LatModuleGen leech) (2 * n) y :=
  mode_plusModule (u : VPlus) n y

theorem actT_hP_sum (u : V0Sub.carrier) (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    actT u 1 (hP v t) = ∑ c, v c • actT u 1 (hP (Pi.single c 1) t) := by
  conv_lhs => rw [pi_eq_sum_single v]
  have h : ∀ (s : Finset (Fin (rank leech))), hP (∑ c ∈ s, v c • Pi.single c (1 : ℂ)) t
      = ∑ c ∈ s, v c • hP (Pi.single c 1) t := by
    intro s
    induction s using Finset.induction_on with
    | empty => apply Subtype.ext; simp [hP_coe, hvec]
    | insert c s hc ih => rw [Finset.sum_insert hc, Finset.sum_insert hc, hP_add_left, hP_smul_left, ih]
  rw [h, map_sum]
  simp only [map_smul]

/-- **Target, Heisenberg letters**: `o(h_a h_b)(h_v ⊗ t) = h_{quadL v} ⊗ t`. -/
theorem actT_qV_hP (a b : Fin (rank leech)) (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    actT (qV a b) 1 (hP v t) = hP (quadL a b v) t := by
  rw [actT_hP_sum]
  conv_rhs => rw [pi_eq_sum_single v, map_sum]
  have h : ∀ (s : Finset (Fin (rank leech))), hP (∑ c ∈ s, quadL a b (v c • Pi.single c (1 : ℂ))) t
      = ∑ c ∈ s, v c • hP (quadL a b (Pi.single c 1)) t := by
    intro s
    induction s using Finset.induction_on with
    | empty => apply Subtype.ext; simp [hP_coe, hvec]
    | insert c s hc ih =>
      rw [Finset.sum_insert hc, Finset.sum_insert hc, hP_add_left, map_smul, hP_smul_left, ih]
  rw [h]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  apply Subtype.ext
  rw [actT_coe, hP_coe, hP_coe, hvec_single]
  change leechTwistedModule.YM (qL a b) (2 * 1) _ = _
  rw [show (2 : ℤ) * 1 = 2 by norm_num, leechYM_quad]
  simp only [quadL, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply, hvec_add, hvec_smul, hvec_single, cc_inj]
  congr 1
  by_cases hbc : b = c <;> by_cases hac : a = c <;>
    simp [hbc, hac, Pi.single_apply, @eq_comm _ c]

/-- `v ↦ v − 2⟨v, γ⟩ γ`, the Fock part of `o(e^γ)` on `h_v(−½)` (`|γ|² = 4`). -/
noncomputable def latL (γ : leech.carrier) :
    (Fin (rank leech) → ℂ) →ₗ[ℂ] (Fin (rank leech) → ℂ) :=
  LinearMap.id - (2 : ℂ) • (∑ a, chargeCoord leech γ a • LinearMap.proj a).smulRight (chargeCoord leech γ)

theorem hvec_chargeCoord (γ : leech.carrier) : hvec (chargeCoord leech γ) = vVarT (chT γ) 0 := by
  rw [hvec, vVarT]
  exact (Fintype.sum_equiv (finCongr leech_rank) _ _ fun a => by simp [chT, cc]).trans rfl

/-- **Target, lattice letters**: `o(e^γ + e^{−γ})(h_v ⊗ t) = 2⁻³ h_{latL v} ⊗ e_γ t`. -/
theorem actT_lV_hP {γ : leech.carrier} (hγ : γ ∈ lambda0) (hγ4 : leech.form γ γ = 4)
    (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    actT (lV γ hγ) 1 (hP v t)
      = ((2 : ℂ) ^ (-(3 : ℤ))) • hP (latL γ v) (eT leech leech_even leech_isUnit_det_gramMat γ t) := by
  rw [actT_hP_sum]
  conv_rhs => rw [pi_eq_sum_single v, map_sum]
  have h : ∀ (s : Finset (Fin (rank leech))), hP (∑ c ∈ s, latL γ (v c • Pi.single c (1 : ℂ)))
      (eT leech leech_even leech_isUnit_det_gramMat γ t)
      = ∑ c ∈ s, v c • hP (latL γ (Pi.single c 1)) (eT leech leech_even leech_isUnit_det_gramMat γ t) := by
    intro s
    induction s using Finset.induction_on with
    | empty => apply Subtype.ext; simp [hP_coe, hvec]
    | insert c s hc ih =>
      rw [Finset.sum_insert hc, Finset.sum_insert hc, hP_add_left, map_smul, hP_smul_left, ih]
  rw [h, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_comm]
  congr 1
  apply Subtype.ext
  rw [actT_coe, hP_coe, Submodule.coe_smul, hP_coe, hvec_single]
  change leechTwistedModule.YM (echg leech γ + echg leech (-γ)) (2 * 1) _ = _
  rw [show (2 : ℤ) * 1 = 2 by norm_num, map_add, Pi.add_apply, LinearMap.add_apply,
    leechYM_echg_neg_two, leechYM_echg_X γ hγ4]
  simp only [latL, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, LinearMap.sum_apply, LinearMap.proj_apply,
    hvec_sub, hvec_smul, hvec_single, hvec_chargeCoord]
  have hc : chT γ (cc c) = chargeCoord leech γ c := by simp [chT, cc]
  have hs : (∑ a, chargeCoord leech γ a • Pi.single c (1 : ℂ) a) = chargeCoord leech γ c := by
    simp [Pi.single_apply]
  rw [hc, hs, ← add_smul, ← smul_smul (2 : ℂ) (chargeCoord leech γ c)]
  congr 1
  norm_num

/-! ## §5  Frame quadratic letters `α(−1)β(−1)𝟙` -/

theorem smul_sum_right' {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : PreVertexAlgebra 𝒱) {ι : Type*}
    (s : Finset ι) (u : 𝒱) (n : ℤ) (f : ι → 𝒱) :
    V.smul u n (∑ i ∈ s, f i) = ∑ i ∈ s, V.smul u n (f i) := by
  simp only [PreVertexAlgebra.smul_def, map_sum]

/-- `α(−1)β(−1)𝟙 = Σ_{a,b} α_a β_b h_a(−1)h_b(−1)𝟙`. -/
theorem quadH_eq_sum (α β : leech.carrier) :
    quadH leech leech_even leech_posDef α β
      = ∑ a, ∑ b, (chargeCoord leech α a * chargeCoord leech β b) • qL a b := by
  rw [quadH, hSt_eq_sum, smul_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [PreVertexAlgebra.smul_smul_left, hSt_eq_sum, smul_sum_right', Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [PreVertexAlgebra.smul_smul_right, smul_smul, hgen_eq_word, hgen_eq_word]
  rfl

theorem quadH_theta (α β : leech.carrier) :
    thetaLat leech (quadH leech leech_even leech_posDef α β) = quadH leech leech_even leech_posDef α β := by
  rw [quadH_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, qL_theta]

theorem quadH_frame (α β : leech.carrier) :
    chiLat leech frameChar (quadH leech leech_even leech_posDef α β) = quadH leech leech_even leech_posDef α β := by
  rw [quadH_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, qL_frame]

/-- The frame quadratic letter `α(−1)β(−1)𝟙 ∈ V₀⁺`. -/
noncomputable def dV (α β : leech.carrier) : V0Sub.carrier :=
  ⟨⟨quadH leech leech_even leech_posDef α β, (mem_leechVOAPlus_iff _).mpr (quadH_theta α β)⟩, by
    rw [V0Sub_carrier, mem_frameSector, Extraspecial.sgn_zero, one_smul]
    exact quadH_frame α β⟩

theorem dV_eq_sum (α β : leech.carrier) :
    dV α β = ∑ a, ∑ b, (chargeCoord leech α a * chargeCoord leech β b) • qV a b := by
  apply Subtype.ext; apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  exact quadH_eq_sum α β

theorem dV_mem_grading (α β : leech.carrier) : ((dV α β : V0Sub.carrier) : VPlus) ∈ leechVOAPlus.grading 2 := by
  rw [dV_eq_sum]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (qP_mem_grading a b)

/-- **Source, frame quadratic letters**: `o(α(−1)β(−1)𝟙) x_n = ⟨α,n⟩⟨β,n⟩ x_n`. -/
theorem actV_dV (α β n : leech.carrier) :
    actV (dV α β) 1 (frameX0P n)
      = (((leech.form α n : ℤ) : ℂ) * ((leech.form β n : ℤ) : ℂ)) • frameX0P n := by
  apply Subtype.ext
  change leechVOA.smul (quadH leech leech_even leech_posDef α β) 1 (frameX0 n) = _
  rw [frameX0, PreVertexAlgebra.smul_add_right]
  change (latticeVOAGen leech leech_even leech_posDef).smul _ 1 (echg leech n)
    + (latticeVOAGen leech leech_even leech_posDef).smul _ 1 (echg leech (-n)) = _
  rw [quadH_one_echg, quadH_one_echg, leech_form_neg_right, leech_form_neg_right]
  push_cast
  rw [neg_mul_neg]
  change _ = _ • (echg leech n + echg leech (-n))
  rw [smul_add]

/-- `v ↦ (⟨α,β⟩/8) v + ½⟨v,β⟩ α + ½⟨v,α⟩ β`, the action of `o(α(−1)β(−1)𝟙)` on `h_v(−½)`. -/
noncomputable def dL (α β : leech.carrier) :
    (Fin (rank leech) → ℂ) →ₗ[ℂ] (Fin (rank leech) → ℂ) :=
  (((leech.form α β : ℤ) : ℂ) / 8) • LinearMap.id
    + (1 / 2 : ℂ) • (∑ b, chargeCoord leech β b • LinearMap.proj b).smulRight (chargeCoord leech α)
    + (1 / 2 : ℂ) • (∑ a, chargeCoord leech α a • LinearMap.proj a).smulRight (chargeCoord leech β)

theorem dL_eq_sum (α β : leech.carrier) :
    dL α β = ∑ a, ∑ b, (chargeCoord leech α a * chargeCoord leech β b) • quadL a b := by
  apply LinearMap.ext; intro v; funext i
  simp only [dL, quadL, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, LinearMap.sum_apply, LinearMap.proj_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [← sum_chargeCoord leech leech_posDef α β]
  simp only [mul_add, Finset.sum_add_distrib]
  set A := chargeCoord leech α
  set B := chargeCoord leech β
  have e1 : ∑ x, ∑ y, A x * B y * ((if x = y then (1 / 8 : ℂ) else 0) * v i)
      = (∑ b, A b * B b) / 8 * v i := by
    rw [Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single x (fun y _ hy => by rw [if_neg (Ne.symm hy)]; ring) (by simp)]
    rw [if_pos rfl]; ring
  have e2 : ∑ x, ∑ y, A x * B y * (1 / 2 * (v y * (Pi.single x (1 : ℂ) : Fin (rank leech) → ℂ) i))
      = 1 / 2 * ((∑ y, B y * v y) * A i) := by
    rw [Finset.sum_eq_single i (fun x _ hx => Finset.sum_eq_zero fun y _ => by
      rw [Pi.single_apply, if_neg (Ne.symm hx)]; ring) (by simp)]
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Pi.single_eq_same]; ring
  have e3 : ∑ x, ∑ y, A x * B y * (1 / 2 * (v x * (Pi.single y (1 : ℂ) : Fin (rank leech) → ℂ) i))
      = 1 / 2 * ((∑ x, A x * v x) * B i) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single i (fun y _ hy => by rw [Pi.single_apply, if_neg (Ne.symm hy)]; ring)
      (by simp)]
    rw [Pi.single_eq_same]; ring
  rw [e1, e2, e3]

theorem actT_sum_left {ι : Type*} (s : Finset ι) (f : ι → V0Sub.carrier) (n : ℤ) (y : TP) :
    actT (∑ i ∈ s, f i) n y = ∑ i ∈ s, actT (f i) n y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [actT]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, actT_add_left, ih]

theorem hP_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin (rank leech) → ℂ) (t : TLeechT) :
    hP (∑ i ∈ s, f i) t = ∑ i ∈ s, hP (f i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => apply Subtype.ext; simp [hP_coe, hvec]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hP_add_left, ih]

/-- **Target, frame quadratic letters**: `o(α(−1)β(−1)𝟙)(h_v ⊗ t) = h_{dL v} ⊗ t`. -/
theorem actT_dV_hP (α β : leech.carrier) (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    actT (dV α β) 1 (hP v t) = hP (dL α β v) t := by
  rw [dV_eq_sum, actT_sum_left, dL_eq_sum, LinearMap.sum_apply, hP_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [actT_sum_left, LinearMap.sum_apply, hP_sum_left]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [actT_smul_left, actT_qV_hP, LinearMap.smul_apply, hP_smul_left]

/-- The orthonormal coordinates of the frame vector `w_j`. -/
noncomputable def cw (j : Fin 24) : Fin (rank leech) → ℂ := chargeCoord leech (fw j)

theorem pair_cw (α : leech.carrier) (m : Fin 24) :
    ∑ b, chargeCoord leech α b * cw m b = ((leech.form α (fw m) : ℤ) : ℂ) :=
  sum_chargeCoord leech leech_posDef α (fw m)

/-- `o(w_j(−1)²𝟙)` on `h_{w_m}(−½)`: eigenvalue `9` if `j = m`, `1` otherwise. -/
theorem dL_fw_fw (j m : Fin 24) : dL (fw j) (fw j) (cw m) = (if j = m then (9 : ℂ) else 1) • cw m := by
  simp only [dL, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, LinearMap.sum_apply, LinearMap.proj_apply, smul_eq_mul]
  have hp : ∑ b, chargeCoord leech (fw j) b * cw m b = ((leech.form (fw j) (fw m) : ℤ) : ℂ) :=
    pair_cw (fw j) m
  have hp' : ∑ x, chargeCoord leech (fw j) x * cw m x = ((leech.form (fw j) (fw m) : ℤ) : ℂ) := hp
  rw [hp', form_fw_fw, form_fw_fw, if_pos rfl]
  by_cases h : j = m
  · subst h; rw [if_pos rfl, if_pos rfl]; unfold cw; module
  · rw [if_neg h, if_neg h]; simp

/-- **The diagonal frame letter on `(T⁺)₂`**. -/
theorem actT_dV_fw_hP (j m : Fin 24) (t : TLeechT) :
    actT (dV (fw j) (fw j)) 1 (hP (cw m) t) = (if j = m then (9 : ℂ) else 1) • hP (cw m) t := by
  rw [actT_dV_hP, dL_fw_fw, hP_smul_left]

/-- **The diagonal frame letter on `(V₃⁺)₂`**: `o(w_j(−1)²𝟙) x_n = n_j² x_n`. -/
theorem actV_dV_fw {n : leech.carrier} (hn : n ∉ lambda0) (h4 : leech.form n n = 4) (j : Fin 24) :
    actV (dV (fw j) (fw j)) 1 (frameX0P n) = (if j = blk n then (9 : ℂ) else 1) • frameX0P n := by
  rw [actV_dV, form_fw_left]
  congr 1
  have h := lv_sq hn h4 j
  have h' : ((lv n j : ℤ) : ℂ) * ((lv n j : ℤ) : ℂ) = (((lv n j ^ 2 : ℤ)) : ℂ) := by push_cast; ring
  rw [h', h]
  split_ifs <;> norm_num

end VOA.Moonshine.SigmaTop
