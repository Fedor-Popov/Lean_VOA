/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaTop2Main

/-!
# The octad letters: `σ` on `e^{γ} + e^{−γ}`, `γ = (±2⁸, 0¹⁶)`, and the identity on `V₃⁺`

Every lattice letter is transported, `golayToV0 (yA a) = e^{ιa} + e^{−ιa}` (`golayToV0_yA`).  For
an octad `D` and an even `S ⊆ D` the `N`-charge of `γ_S` is the spinor `1_D − δ_S`; on the cube `σ`
is the Hadamard transform (`golaySigma_bp`), the odd-`|S'|` terms vanish because `σ(y)` stays in
`V_N^{⟨χ,Θ⟩}` (`coef_odd_zero`, which also gives `XS_eq_YS`), so
`σ(u_{γ_S}) = Σ_{S' ⊆ D even} K(S,S') e^{γ_{S'}}` (`sig_lV_aSA`).  On `φ⋆(x_n) = h_{w_b} ⊗ τ⋆(n)`
each term is `C₀ ∏_{i ∈ S'} ζ_i · e_n W(b) t` (`term_eval`), the `h`-parts are
`latL γ_{S'} (w_b) = w_b − [b ∈ D] Σ_{l ∈ D} s'_b s'_l w_l` (`latL_cw`), and the even Hadamard sums
of the `±1`-patterns `ζ`, `ζη` collapse to `2^{|D|−1}([≡1] + [≡−1])` (`sum_even_pm`).

## Main results
* `golayToV0_yA`, `golaySigma_bp`, `golaySigma_yAN`, `coef_odd_zero`, `XS_eq_YS`, `coef_even`.
* `sig_lV_aSA`, `actT_sig_lV_aSA`, `term_eval`, `rhs_formula`, `lhs_term`, `cE_aSA_add`.
* `octad_out` (block `∉ D`), `octad_in` (block `∈ D`, the block moves to the unique `l₀`).
* `phiV3_ZM_aSA` — every octad letter intertwines for `φ⋆`.

## Status
`sorry`-free; `#print axioms`: `[propext, Classical.choice, Quot.sound]`.  Reached from the
umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaTop

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen VOA.Moonshine.Triality HeisenbergN
open VOA.Moonshine.TrialityTw VOA.Moonshine.SigmaExist
open Module (End)

/-! ## §1  The lattice letters of `V₀⁺` as transported `N`-states -/

theorem golayChi_inclN (a : lam0.carrier) :
    golayChi (latChargeGen golayN (inclN a)) = latChargeGen golayN (inclN a) := by
  show chiLat golayN golayParity (latStateGen golayN _ _) = _
  rw [chiLat_latStateGen, chiSign_of_eq_zero _ _ ((mem_range_inclN _).mp ⟨a, rfl⟩), one_smul]; rfl

theorem golayTheta_inclN (a : lam0.carrier) :
    golayTheta (latChargeGen golayN (inclN a)) = (eV a * eV a)⁻¹ • latChargeGen golayN (inclN (-a)) := by
  have h1 := golayTheta_bridgeN_latChargeGen a
  have hneg : charVal lam0 golayE (-a) = (eV a)⁻¹ := eV_neg a
  rw [bridgeN_latChargeGen, bridgeN_latChargeGen, aut_smul, smul_smul, latCob_neg, charVal_negE,
    hneg] at h1
  have hc := latCob_ne_zero lam0 golayN inclN a
  have h2 := congrArg (fun v => (latCob lam0 golayN inclN a)⁻¹ • v) h1
  simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
  rw [h2, mul_inv]; congr 1; field_simp

/-- The `N`-state `tc(a)⁻¹ e^{a} + tc(−a)⁻¹ e^{−a}` of `V_N^{⟨χ,Θ⟩}`. -/
noncomputable def yAN (a : lam0.carrier) : LatModuleGen golayN :=
  (tc a)⁻¹ • latChargeGen golayN (inclN a) + (tc (-a))⁻¹ • latChargeGen golayN (inclN (-a))

theorem yAN_mem (a : lam0.carrier) : yAN a ∈ (orbifold golayK).carrier := by
  rw [mem_golayV0_iff]
  constructor
  · rw [yAN, aut_add, aut_smul, aut_smul, golayChi_inclN, golayChi_inclN]
  · rw [yAN, aut_add, aut_smul, aut_smul, golayTheta_inclN, golayTheta_inclN, neg_neg, smul_smul,
      smul_smul, tc_neg, eV_neg, add_comm]
    have he := charVal_ne_zero lam0 golayE a
    have ht := tc_ne_zero a
    congr 1
    · congr 1; field_simp
    · congr 1; field_simp

/-- `yAN` as a state of the orbifold. -/
noncomputable def yA (a : lam0.carrier) : (orbifold golayK).carrier := ⟨yAN a, yAN_mem a⟩

theorem inclΛ_mem (a : lam0.carrier) : inclΛ a ∈ lambda0 := (mem_range_inclΛ _).mp ⟨a, rfl⟩

/-- **Every lattice letter is transported**: `golayToV0 (yA a) = e^{ιa} + e^{−ιa}`. -/
theorem golayToV0_yA (a : lam0.carrier) : golayToV0 (yA a) = lV (inclΛ a) (inclΛ_mem a) := by
  apply Subtype.ext; apply Subtype.ext
  have h := golayToV0_charged (Finset.univ : Finset (Fin 2)) ![(tc a)⁻¹, (tc (-a))⁻¹] ![a, -a] (yA a)
    (by rw [Fin.sum_univ_two]; rfl)
  rw [h, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [inv_mul_cancel₀ (tc_ne_zero a), inv_mul_cancel₀ (tc_ne_zero (-a)), one_smul, one_smul, map_neg]
  rfl

/-! ## §2  `σ` on the spinor cube is a Hadamard transform -/

/-- The local `2 × 2` matrix of `σ` on a doublet. -/
noncomputable def hadV (v : Fin 2 → ℂ) : Fin 2 → ℂ := gvec (chivec (ginv v))

/-- `r = 1/√2`. -/
noncomputable abbrev rH : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) / 2

theorem hadV_up : hadV ![1, 0] = ![rH, rH] := by
  have hs := sqrt2_mul_self'
  set r : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) with hr
  funext l
  fin_cases l
  · simp [hadV, gvec, ginv, chivec, aG, bG]; rw [← hr]; linear_combination (-(1 / 2 : ℂ)) * hs
  · simp [hadV, gvec, ginv, chivec, aG, bG]; rw [← hr]; ring

theorem hadV_down : hadV ![0, 1] = ![rH, -rH] := by
  have hs := sqrt2_mul_self'
  set r : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) with hr
  funext l
  fin_cases l
  · simp [hadV, gvec, ginv, chivec, aG, bG]; rw [← hr]; linear_combination (-(r - 2) / 2) * hs
  · simp [hadV, gvec, ginv, chivec, aG, bG]; rw [← hr]; linear_combination ((1 / 2 : ℂ)) * hs

theorem rH_pow_eight : rH ^ 8 = 1 / 16 := by
  have hs := sqrt2_mul_self'
  rw [rH, div_pow]
  rw [show ((Real.sqrt 2 : ℝ) : ℂ) ^ 8 = (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)) ^ 4 by ring, hs]
  norm_num

/-! ## §3  Basis vectors of the cube and `σ` on them -/

/-- The product data of the basis vector `b_T`. -/
def basisD (T : Finset (Fin 24)) (i : Fin 24) : Fin 2 → ℂ := if i ∈ T then ![0, 1] else ![1, 0]

theorem prodC_basisD {D T S : Finset (Fin 24)} (hT : T ⊆ D) (hS : S ⊆ D) :
    prodC D (basisD T) S = if S = T then 1 else 0 := by
  unfold prodC basisD
  split_ifs with hST
  · subst hST
    exact Finset.prod_eq_one fun i _ => by by_cases h : i ∈ S <;> simp [h]
  · have : ∃ i ∈ D, (i ∈ S ↔ ¬ i ∈ T) := by
      by_contra hcon
      push Not at hcon
      apply hST
      ext i
      by_cases hi : i ∈ D
      · have := hcon i hi; tauto
      · exact ⟨fun h => absurd (hS h) hi, fun h => absurd (hT h) hi⟩
    obtain ⟨i, hiD, hi⟩ := this
    refine Finset.prod_eq_zero hiD ?_
    by_cases h : i ∈ T
    · have h' : i ∉ S := fun hs => (hi.mp hs) h
      simp [h, h']
    · have h' : i ∈ S := hi.mpr h
      simp [h, h']

theorem vecP_basisD (β : golayN.carrier) {D T : Finset (Fin 24)} (hT : T ⊆ D) :
    vecP β D (basisD T) = bp β T := by
  unfold vecP
  rw [Finset.sum_eq_single T]
  · rw [prodC_basisD hT hT, if_pos rfl, one_smul]
  · intro S hS hne
    rw [prodC_basisD hT (Finset.mem_powerset.mp hS), if_neg hne, zero_smul]
  · intro h; exact absurd (Finset.mem_powerset.mpr hT) h

theorem prodC_had {D T S : Finset (Fin 24)} (hT : T ⊆ D) :
    prodC D (fun m => hadV (basisD T m)) S = rH ^ D.card * (-1 : ℂ) ^ (T ∩ S).card := by
  unfold prodC
  have h : ∀ i ∈ D, hadV (basisD T i) (if i ∈ S then 1 else 0)
      = rH * (if i ∈ T ∩ S then (-1 : ℂ) else 1) := by
    intro i _
    unfold basisD
    by_cases h1 : i ∈ T <;> by_cases h2 : i ∈ S <;> simp [h1, h2, hadV_up, hadV_down]
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_ite,
    Finset.prod_const, Finset.prod_const_one, mul_one, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr ((Finset.inter_subset_left).trans hT)]

/-- **`σ` on a cube basis vector is the Hadamard transform**:
`σ b_T = (χz₀ sign) · Σ_{S ⊆ D} r^{|D|} (−1)^{|T ∩ S|} b_S`, `r = 1/√2`. -/
theorem golaySigma_bp {β : golayN.carrier} {D T : Finset (Fin 24)} (hβ : gv β = ind D)
    (h4 : 4 ∣ D.card) (hT : T ⊆ D) :
    golaySigma (bp β T) = cD D • ∑ S ∈ D.powerset, (rH ^ D.card * (-1 : ℂ) ^ (T ∩ S).card) • bp β S := by
  rw [← vecP_basisD β hT, golaySigma_vecP β hβ h4]
  congr 1
  unfold vecP
  exact Finset.sum_congr rfl fun S _ => by rw [← prodC_had hT]; rfl

/-! ## §4  The spinor charges `a_S = 1_D − 2·1_S ∈ Λ₀` -/

theorem two_ind_mem (S : Finset (Fin 24)) (h : Even S.card) : (2 : ℤ) • ind S ∈ Leech.subA := by
  refine ⟨two_smul_mem_preimageOfCode Code.golay _, ?_⟩
  obtain ⟨m, hm⟩ := h
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ind, Finset.sum_boole,
    Finset.filter_mem_eq_inter, Finset.univ_inter]
  exact ⟨m, by rw [hm]; push_cast; ring⟩

open Classical in
/-- `δ_S ∈ Λ₀` (for `|S|` even; junk `0` otherwise). -/
noncomputable def dSA (S : Finset (Fin 24)) : lam0.carrier :=
  if h : Even S.card then (⟨(2 : ℤ) • ind S, two_ind_mem S h⟩ : ↥Leech.subA) else 0

theorem inclN_dSA {S : Finset (Fin 24)} (h : Even S.card) : inclN (dSA S) = dl S := by
  unfold dSA; rw [dif_pos h]; rfl

variable {D : Finset (Fin 24)} (hDA : ind D ∈ Leech.subA)

/-- The codeword charge `1_D ∈ Λ₀`. -/
def bAD : lam0.carrier := (⟨ind D, hDA⟩ : ↥Leech.subA)

theorem gv_inclN_bAD : gv (inclN (bAD hDA)) = ind D := rfl

/-- The spinor charge `a_S = 1_D − δ_S`. -/
noncomputable def aSA (S : Finset (Fin 24)) : lam0.carrier := bAD hDA - dSA S

theorem inclN_aSA {S : Finset (Fin 24)} (h : Even S.card) :
    inclN (aSA hDA S) = inclN (bAD hDA) - dl S := by
  rw [aSA, map_sub, inclN_dSA h]

theorem ind_sdiff {S : Finset (Fin 24)} (hS : S ⊆ D) : ind (D \ S) = ind D - ind S := by
  funext i
  simp only [ind, Finset.mem_sdiff, Pi.sub_apply]
  by_cases h1 : i ∈ D <;> by_cases h2 : i ∈ S <;> simp [h1, h2]
  exact absurd (hS h2) h1

theorem dl_sdiff {S : Finset (Fin 24)} (hS : S ⊆ D) : dl (D \ S) = dl D - dl S := by
  rw [dl, dl, dl, ind_sdiff hS, map_sub]

theorem inclN_neg_aSA {S : Finset (Fin 24)} (h : Even S.card) (hS : S ⊆ D) :
    inclN (-aSA hDA S) = inclN (bAD hDA) - dl (D \ S) := by
  rw [map_neg, inclN_aSA hDA h, dl_sdiff hS, dl_full (inclN (bAD hDA)) (gv_inclN_bAD hDA)]
  abel

theorem nuC_ne_zero (β : golayN.carrier) (S : Finset (Fin 24)) : nuC β S ≠ 0 :=
  mul_ne_zero (mul_ne_zero (εN_ne_zero _ _) (xi_ne_zero _))
    (inv_ne_zero (pow_ne_zero _ Complex.I_ne_zero))

theorem latChargeGen_eq_bp (β : golayN.carrier) (T : Finset (Fin 24)) :
    latChargeGen golayN (β - dl T) = (nuC β T)⁻¹ • bp β T := by
  rw [bp, smul_smul, inv_mul_cancel₀ (nuC_ne_zero β T), one_smul]

/-- The two cube coefficients of the letter `y_{a_S}`. -/
noncomputable def XS (S : Finset (Fin 24)) : ℂ := (tc (aSA hDA S))⁻¹ * (nuC (inclN (bAD hDA)) S)⁻¹
noncomputable def YS (S : Finset (Fin 24)) : ℂ :=
  (tc (-aSA hDA S))⁻¹ * (nuC (inclN (bAD hDA)) (D \ S))⁻¹

theorem yAN_cube {S : Finset (Fin 24)} (h : Even S.card) (hS : S ⊆ D) :
    yAN (aSA hDA S) = XS hDA S • bp (inclN (bAD hDA)) S + YS hDA S • bp (inclN (bAD hDA)) (D \ S) := by
  rw [yAN, inclN_aSA hDA h, inclN_neg_aSA hDA h hS, latChargeGen_eq_bp, latChargeGen_eq_bp,
    smul_smul, smul_smul, XS, YS]

/-! ## §5  `σ(y_{a_S})`: the odd terms vanish, the even terms are a Hadamard sum -/

open Classical in
theorem coordEα_golayN (α γ : golayN.carrier) :
    coordEα golayN α (latChargeGen golayN γ) = if α = γ then vacuumN (rank golayN) else 0 :=
  coordEα_apply golayN α γ _

theorem ind_injective : Function.Injective ind := by
  intro S T h
  ext i
  have := congrFun h i
  simp only [ind] at this
  by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ T <;> simp_all

theorem dl_injective : Function.Injective dl := fun S T h => ind_injective (phiR_injective h)

open Classical in
theorem coordEα_bp (β : golayN.carrier) (S T : Finset (Fin 24)) :
    coordEα golayN (β - dl S) (bp β T) = if T = S then nuC β S • vacuumN (rank golayN) else 0 := by
  rw [bp, map_smul, coordEα_golayN]
  by_cases h : T = S
  · subst h; simp
  · rw [if_neg (fun h' => h (dl_injective (sub_right_injective h').symm)), if_neg h, smul_zero]

variable (hD8 : D.card = 8)
include hD8

theorem four_dvd_D : 4 ∣ D.card := by rw [hD8]; norm_num

theorem golayParity_odd {S : Finset (Fin 24)} (hS : S ⊆ D) (ho : ¬ Even S.card) :
    golayParity (inclN (bAD hDA) - dl S) ≠ 0 := by
  rw [Ne, golayParity_eq_zero_iff]
  change ¬ (4 : ℤ) ∣ ∑ l, gv (inclN (bAD hDA) - dl S) l
  rw [sum_gv_sub _ (gv_inclN_bAD hDA) hS, hD8]
  rw [Nat.not_even_iff_odd] at ho
  obtain ⟨m, hm⟩ := ho
  rw [hm]; push_cast; omega

/-- The coefficient of `b_{S'}` in `σ(y_{a_S})`. -/
noncomputable def coefS (S S' : Finset (Fin 24)) : ℂ :=
  cD D * (rH ^ D.card * (XS hDA S * (-1 : ℂ) ^ (S ∩ S').card + YS hDA S * (-1 : ℂ) ^ ((D \ S) ∩ S').card))

theorem golaySigma_yAN {S : Finset (Fin 24)} (h : Even S.card) (hS : S ⊆ D) :
    golaySigma (yAN (aSA hDA S)) = ∑ S' ∈ D.powerset, coefS hDA S S' • bp (inclN (bAD hDA)) S' := by
  have hβ := gv_inclN_bAD hDA
  rw [yAN_cube hDA h hS, aut_add, aut_smul, aut_smul, golaySigma_bp hβ (four_dvd_D hD8) hS,
    golaySigma_bp hβ (four_dvd_D hD8) Finset.sdiff_subset, Finset.smul_sum, Finset.smul_sum,
    Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S' _ => ?_
  rw [smul_smul, smul_smul, smul_smul, smul_smul, ← add_smul, coefS]
  congr 1; ring

open Classical in
theorem coef_odd_zero {S S' : Finset (Fin 24)} (h : Even S.card) (hS : S ⊆ D) (hS' : S' ⊆ D)
    (ho : ¬ Even S'.card) : coefS hDA S S' = 0 := by
  have hmem : golaySigma (yAN (aSA hDA S)) ∈ (orbifold golayK).carrier := by
    have := (golaySigma0 (yA (aSA hDA S))).2
    rwa [golaySigma0_coe] at this
  have h0 := mem_golayV0_momentum hmem _ (golayParity_odd hDA hD8 hS' ho)
  rw [golaySigma_yAN hDA hD8 h hS, map_sum] at h0
  simp only [map_smul, coordEα_bp] at h0
  rw [Finset.sum_eq_single S'] at h0
  · rw [if_pos rfl, smul_smul] at h0
    have hv : vacuumN (rank golayN) ≠ 0 := one_ne_zero
    have := (smul_eq_zero.mp h0).resolve_right hv
    exact (mul_eq_zero.mp this).resolve_right (nuC_ne_zero _ _)
  · intro T _ hT; rw [if_neg hT, smul_zero]
  · intro hn; exact absurd (Finset.mem_powerset.mpr hS') hn

theorem XS_eq_YS {S : Finset (Fin 24)} (h : Even S.card) (hS : S ⊆ D) : XS hDA S = YS hDA S := by
  have hne : D.Nonempty := Finset.card_pos.mp (by rw [hD8]; norm_num)
  obtain ⟨i, hi⟩ := hne
  have h0 := coef_odd_zero hDA hD8 h hS (Finset.singleton_subset_iff.mpr hi) (by simp)
  rw [coefS] at h0
  have hc : cD D ≠ 0 := by unfold cD; split_ifs <;> norm_num
  have hr : rH ^ D.card ≠ 0 := pow_ne_zero _ (div_ne_zero (by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne') two_ne_zero)
  have h1 := (mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hc)).resolve_left hr
  by_cases his : i ∈ S
  · have e1 : S ∩ {i} = {i} := Finset.inter_singleton_of_mem his
    have e2 : (D \ S) ∩ {i} = ∅ := by
      ext l; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨_, h⟩, rfl⟩; exact absurd his h
      · simp
    rw [e1, e2] at h1; simp at h1; linear_combination -h1
  · have e1 : S ∩ {i} = ∅ := Finset.inter_singleton_of_notMem his
    have e2 : (D \ S) ∩ {i} = {i} := Finset.inter_singleton_of_mem (Finset.mem_sdiff.mpr ⟨hi, his⟩)
    rw [e1, e2] at h1; simp at h1; linear_combination h1

theorem coef_even {S S' : Finset (Fin 24)} (h : Even S.card) (hS : S ⊆ D) (hS' : S' ⊆ D)
    (he : Even S'.card) :
    coefS hDA S S' = 2 * cD D * rH ^ D.card * XS hDA S * (-1 : ℂ) ^ (S ∩ S').card := by
  rw [coefS, ← XS_eq_YS hDA hD8 h hS]
  have hc : ((D \ S) ∩ S').card + (S ∩ S').card = S'.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext l; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
      · intro hl; by_cases hlS : l ∈ S
        · exact Or.inr ⟨hlS, hl⟩
        · exact Or.inl ⟨⟨hS' hl, hlS⟩, hl⟩
    · rw [Finset.disjoint_left]
      intro l hl1 hl2
      simp only [Finset.mem_inter, Finset.mem_sdiff] at hl1 hl2
      exact hl1.1.2 hl2.1
  have hsgn : (-1 : ℂ) ^ ((D \ S) ∩ S').card = (-1 : ℂ) ^ (S ∩ S').card := by
    have := congrArg (fun m : ℕ => (-1 : ℂ) ^ m) hc
    simp only [pow_add, he.neg_one_pow] at this
    have hs : (-1 : ℂ) ^ (S ∩ S').card * (-1 : ℂ) ^ (S ∩ S').card = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    linear_combination (-1 : ℂ) ^ (S ∩ S').card * this - (-1 : ℂ) ^ ((D \ S) ∩ S').card * hs
  rw [hsgn]; ring

/-! ## §6  `σ(u_{γ_S})` in `V_Λ` and its zero mode on the twisted top -/

omit hD8 in
theorem inclN_aSA_bp {S' : Finset (Fin 24)} (he : Even S'.card) :
    bp (inclN (bAD hDA)) S' = nuC (inclN (bAD hDA)) S' • latChargeGen golayN (inclN (aSA hDA S')) := by
  rw [inclN_aSA hDA he]; rfl

/-- The coefficient of `e^{γ_{S'}}` in `σ(u_{γ_S})`. -/
noncomputable def KS (S S' : Finset (Fin 24)) : ℂ :=
  coefS hDA S S' * nuC (inclN (bAD hDA)) S' * tc (aSA hDA S')

theorem golaySigma_yAN_even {S : Finset (Fin 24)} (h : Even S.card) (hS : S ⊆ D) :
    golaySigma (yAN (aSA hDA S)) = ∑ S' ∈ D.powerset.filter (fun S' : Finset (Fin 24) => _root_.Even S'.card),
      (coefS hDA S S' * nuC (inclN (bAD hDA)) S') • latChargeGen golayN (inclN (aSA hDA S')) := by
  rw [golaySigma_yAN hDA hD8 h hS, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S' hS' => ?_
  split_ifs with he
  · rw [inclN_aSA_bp hDA he, smul_smul]
  · rw [coef_odd_zero hDA hD8 h hS (Finset.mem_powerset.mp hS') he, zero_smul]

/-- **`σ` on an octad letter**: `σ(e^{γ_S} + e^{−γ_S}) = Σ_{S' ⊆ D even} K(S,S') e^{γ_{S'}}`. -/
theorem sig_lV_aSA {S : Finset (Fin 24)} (h : Even S.card) (hS : S ⊆ D) :
    (((sig (lV (inclΛ (aSA hDA S)) (inclΛ_mem _)) : V0Sub.carrier) : VPlus) : LatModuleGen leech)
      = ∑ S' ∈ D.powerset.filter (fun S' : Finset (Fin 24) => _root_.Even S'.card),
          KS hDA S S' • latChargeGen leech (inclΛ (aSA hDA S')) := by
  rw [← golayToV0_yA, sig, ← golayToV0_sigma]
  rw [golayToV0_charged _ _ _ _ (by rw [golaySigma0_coe]; exact golaySigma_yAN_even hDA hD8 h hS)]
  rfl

omit hD8 in
theorem form_aSA (S' : Finset (Fin 24)) (he : Even S'.card) (hS' : S' ⊆ D) (hD8 : D.card = 8) :
    leech.form (inclΛ (aSA hDA S')) (inclΛ (aSA hDA S')) = 4 := by
  rw [inclΛ_form, ← inclN_form, inclN_aSA hDA he, golayN_form]
  have hg : gv (inclN (bAD hDA) - dl S') = fun l => ind D l - 2 * ind S' l :=
    funext (gv_sub_dl _ (gv_inclN_bAD hDA) S')
  rw [hg]
  have : ∀ l, (ind D l - 2 * ind S' l) * (ind D l - 2 * ind S' l) = ind D l := by
    intro l; simp only [ind]
    by_cases h1 : l ∈ D <;> by_cases h2 : l ∈ S' <;> simp [h1, h2]
    exact absurd (hS' h2) h1
  rw [dotProduct, Finset.sum_congr rfl (fun l _ => this l)]
  simp only [ind, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, hD8]
  norm_num

/-- **The zero mode of `σ(u_{γ_S})` on `h_v(−½) ⊗ x`.** -/
theorem actT_sig_lV_aSA {S : Finset (Fin 24)} (h : Even S.card) (hS : S ⊆ D)
    (v : Fin (rank leech) → ℂ) (x : TLeechT) :
    actT (sig (lV (inclΛ (aSA hDA S)) (inclΛ_mem _))) 1 (hP v x)
      = ∑ S' ∈ D.powerset.filter (fun S' : Finset (Fin 24) => _root_.Even S'.card),
          (KS hDA S S' * (2 : ℂ) ^ (-(4 : ℤ))) • hP (latL (inclΛ (aSA hDA S')) v) (eL (inclΛ (aSA hDA S')) x) := by
  apply Subtype.ext
  rw [actT_coe, sig_lV_aSA hDA hD8 h hS, hP_coe, show (2 : ℤ) * 1 = 2 by norm_num, map_sum,
    Finset.sum_apply, LinearMap.sum_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun S' hS' => ?_
  obtain ⟨hS'p, he⟩ := Finset.mem_filter.mp hS'
  rw [map_smul, Pi.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, hP_coe, ← hT,
    leechYM_echg_hT (inclΛ_mem _) (form_aSA hDA S' he (Finset.mem_powerset.mp hS'p) hD8), smul_smul]
  rfl

/-! ## §7  Hadamard sums over the even subsets -/

omit hD8 in
theorem sum_even_prod (D : Finset (Fin 24)) (f : Fin 24 → ℂ) :
    ∑ S' ∈ D.powerset.filter (fun S' : Finset (Fin 24) => _root_.Even S'.card), ∏ i ∈ S', f i
      = ((∏ i ∈ D, (1 + f i)) + ∏ i ∈ D, (1 + -f i)) / 2 := by
  rw [Finset.prod_one_add, Finset.prod_one_add, ← Finset.sum_add_distrib, Finset.sum_div,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun S' _ => ?_
  rw [Finset.prod_neg]
  split_ifs with he
  · rw [he.neg_one_pow]; ring
  · rw [(Nat.not_even_iff_odd.mp he).neg_one_pow]; ring

omit hD8 in
theorem prod_one_add_pm (D : Finset (Fin 24)) (f : Fin 24 → ℂ) (hf : ∀ i ∈ D, f i = 1 ∨ f i = -1) :
    ∏ i ∈ D, (1 + f i) = if ∀ i ∈ D, f i = 1 then 2 ^ D.card else 0 := by
  split_ifs with h
  · rw [Finset.prod_congr rfl fun i hi => by rw [h i hi], Finset.prod_const]; norm_num
  · push Not at h
    obtain ⟨i, hi, hne⟩ := h
    refine Finset.prod_eq_zero hi ?_
    rcases hf i hi with h' | h'
    · exact absurd h' hne
    · rw [h']; ring

omit hD8 in
/-- **The even Hadamard sum of a `±1`-pattern**: `2^{|D|-1}([ζ ≡ 1] + [ζ ≡ −1])`. -/
theorem sum_even_pm (D : Finset (Fin 24)) (f : Fin 24 → ℂ) (hf : ∀ i ∈ D, f i = 1 ∨ f i = -1) :
    ∑ S' ∈ D.powerset.filter (fun S' : Finset (Fin 24) => _root_.Even S'.card), ∏ i ∈ S', f i
      = ((if ∀ i ∈ D, f i = 1 then 2 ^ D.card else 0) + (if ∀ i ∈ D, f i = -1 then 2 ^ D.card else 0)) / 2 := by
  rw [sum_even_prod, prod_one_add_pm D f hf,
    prod_one_add_pm D (fun i => -f i) (fun i hi => by rcases hf i hi with h | h <;> simp [h])]
  congr 2
  simp only [neg_eq_iff_eq_neg]

/-! ## §8  The terms `e_{γ_{S'}} τ⋆(n)` -/

omit hD8 in
theorem mem_chargesS_aP_ne {t : TLeechT} (ht : IsSeed t) {j k : Fin 24} (hjk : j ≠ k) :
    aP j k ∈ chargesS t := by
  refine ⟨Pi.single j 1 + Pi.single k 1, (phiR_pair j k).symm, ?_⟩
  have h := (ht j k hjk).1
  rw [AP_eq_Wop hjk, LinearMap.smul_apply] at h
  rw [xi_pair]
  have hs := εN_sq (golayRoot j) (golayRoot k)
  have h2 := congrArg (fun x => (2 * εN (golayRoot j) (golayRoot k)) • x) h
  simp only [smul_smul] at h2
  rw [show 2 * εN (golayRoot j) (golayRoot k) * (1 / 2 * εN (golayRoot j) (golayRoot k))
    = εN (golayRoot j) (golayRoot k) * εN (golayRoot j) (golayRoot k) by ring, hs, one_smul] at h2
  rw [h2]; congr 1; ring

omit hD8 in
theorem mem_chargesS_aM_ne {t : TLeechT} (ht : IsSeed t) {j k : Fin 24} (hjk : j ≠ k) :
    aM j k ∈ chargesS t := by
  refine ⟨Pi.single j 1 - Pi.single k 1, (phiR_pairM j k).symm, ?_⟩
  have h := (ht j k hjk).2
  rw [AM_eq_Wop hjk, LinearMap.smul_apply] at h
  rw [xi_pairM]
  have hs := εN_sq (golayRoot j) (golayRoot k)
  have he := golayEps_mul_self k
  set c := golayEps k * εN (golayRoot j) (golayRoot k) with hc
  have hcc : c * c = 1 := by rw [hc]; linear_combination (golayEps k * golayEps k) * hs + he
  have h2 := congrArg (fun x => (2 * c) • x) h
  simp only [smul_smul] at h2
  rw [show 2 * c * (1 / 2 * c) = c * c by ring, hcc, one_smul] at h2
  rw [h2]; congr 1; ring

omit hD8 in
theorem mem_chargesS_aP {t : TLeechT} (ht : IsSeed t) (j k : Fin 24) : aP j k ∈ chargesS t := by
  by_cases h : j = k
  · subst h
    obtain ⟨l, hl⟩ : ∃ l : Fin 24, l ≠ j := ⟨if j = 0 then 1 else 0, by split_ifs with h <;> simp [h]; exact Ne.symm h⟩
    have e : aP j j = aP j l + aM j l := by
      apply inclN_injective; rw [map_add, inclN_aP, inclN_aP, inclN_aM]; abel
    rw [e]
    exact add_mem (mem_chargesS_aP_ne ht (Ne.symm hl)) (mem_chargesS_aM_ne ht (Ne.symm hl))
  · exact mem_chargesS_aP_ne ht h

omit hD8 in
theorem dSA_eq_sum {S' : Finset (Fin 24)} (he : _root_.Even S'.card) :
    dSA S' = ∑ i ∈ S', aP 0 i - ((S'.card / 2 : ℕ) : ℤ) • aP 0 0 := by
  apply valA_injective
  rw [map_sub, map_sum, map_zsmul]
  change (show ↥Leech.subA from dSA S').1 = ∑ i ∈ S', apv 0 i - _ • apv 0 0
  unfold dSA; rw [dif_pos he]
  change (2 : ℤ) • ind S' = _
  obtain ⟨m, hm⟩ := he
  rw [hm, show (m + m) / 2 = m by omega]
  funext l
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Finset.sum_apply, apv, Pi.add_apply,
    Pi.single_apply, ind, Finset.sum_add_distrib, mul_add]
  by_cases hl0 : l = 0 <;> by_cases hlS : l ∈ S' <;> simp [hl0, hlS, Finset.sum_const, hm] <;> ring

omit hD8 in
theorem mem_chargesS_dSA {t : TLeechT} (ht : IsSeed t) {S' : Finset (Fin 24)}
    (he : _root_.Even S'.card) : dSA S' ∈ chargesS t := by
  rw [dSA_eq_sum he]
  exact sub_mem (sum_mem fun i _ => mem_chargesS_aP ht 0 i) (zsmul_mem (mem_chargesS_aP ht 0 0) _)

omit hD8 in
theorem Wop_aSA_seed {t : TLeechT} (ht : IsSeed t) {S' : Finset (Fin 24)} (he : _root_.Even S'.card) :
    Wop (aSA hDA S') t = (εN (inclN (bAD hDA)) (dl S') * xi (-ind S')) • Wop (bAD hDA) t := by
  have hm := congrArg (fun f : End ℂ TLeechT => f t) (Wop_mul (bAD hDA) (-dSA S'))
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at hm
  have hd : Wop (-dSA S') t = xi (-ind S') • t := by
    refine mem_chargesS (neg_mem (mem_chargesS_dSA ht he)) ?_
    rw [map_neg, inclN_dSA he, map_neg]; rfl
  rw [hd, map_smul, map_neg, inclN_dSA he] at hm
  simp only [εN, latticeCocycle_neg_right, ← sub_eq_add_neg] at hm
  change xi (-ind S') • Wop (bAD hDA) t = εN (inclN (bAD hDA)) (dl S') • Wop (aSA hDA S') t at hm
  have hs := εN_sq (inclN (bAD hDA)) (dl S')
  calc Wop (aSA hDA S') t
      = (εN (inclN (bAD hDA)) (dl S') * εN (inclN (bAD hDA)) (dl S')) • Wop (aSA hDA S') t := by
        rw [hs, one_smul]
    _ = εN (inclN (bAD hDA)) (dl S') • (εN (inclN (bAD hDA)) (dl S') • Wop (aSA hDA S') t) := by
        rw [smul_smul]
    _ = _ := by rw [← hm, smul_smul]

omit hD8 in
theorem form_dl_β {S' : Finset (Fin 24)} (hS' : S' ⊆ D) :
    golayN.form (dl S') (inclN (bAD hDA)) = S'.card := by
  rw [golayN_form, dl, gv_phiR, gv_inclN_bAD, smul_dotProduct, smul_eq_mul]
  have : ind S' ⬝ᵥ ind D = S'.card := by
    simp only [dotProduct, ind]
    rw [Finset.sum_congr rfl fun i _ => show (if i ∈ S' then (1 : ℤ) else 0) * (if i ∈ D then 1 else 0)
      = if i ∈ S' then 1 else 0 by
        by_cases h : i ∈ S'
        · simp [h, hS' h]
        · simp [h]]
    simp [Finset.sum_boole]
  rw [this]; omega

omit hD8 in
theorem nuC_eps_xi {S' : Finset (Fin 24)} (hS' : S' ⊆ D) :
    nuC (inclN (bAD hDA)) S' * εN (inclN (bAD hDA)) (dl S') * xi (-ind S')
      = (-1 : ℂ) ^ S'.card * (Complex.I ^ S'.card)⁻¹ := by
  have hx := xi_mul (ind S') (-ind S')
  rw [add_neg_cancel, xi_zero, mul_one, map_neg] at hx
  change xi (ind S') * xi (-ind S') = latticeCocycle golayN (dl S') (-dl S') at hx
  rw [latticeCocycle_neg_right] at hx
  have hc := latticeCocycle_comm golayN golayN_even (dl S') (inclN (bAD hDA))
  rw [form_dl_β hDA hS', zpow_natCast] at hc
  have hs := εN_sq (dl S') (dl S')
  rw [nuC]
  simp only [εN, latticeCocycle_add_right] at hs ⊢
  linear_combination (Complex.I ^ S'.card)⁻¹ *
    (latticeCocycle golayN (dl S') (dl S') * latticeCocycle golayN (dl S') (inclN (bAD hDA)) *
      latticeCocycle golayN (inclN (bAD hDA)) (dl S')) * hx
    + (Complex.I ^ S'.card)⁻¹ * (latticeCocycle golayN (dl S') (inclN (bAD hDA)) *
      latticeCocycle golayN (inclN (bAD hDA)) (dl S')) * hs + (Complex.I ^ S'.card)⁻¹ * hc

/-! ## §9  Signs -/

omit hD8 in
theorem valA_aSA {S' : Finset (Fin 24)} (he : _root_.Even S'.card) :
    valA (aSA hDA S') = ind D - (2 : ℤ) • ind S' := by
  rw [aSA, map_sub]
  change ind D - (show ↥Leech.subA from dSA S').1 = _
  unfold dSA; rw [dif_pos he]

omit hD8 in
theorem lv_inclΛ (a : lam0.carrier) : lv (inclΛ a) = (2 : ℤ) • valA a := rfl

omit hD8 in
theorem I_zpow_sum (s : Finset (Fin 24)) (f : Fin 24 → ℤ) :
    Complex.I ^ (-(∑ i ∈ s, f i)) = ∏ i ∈ s, Complex.I ^ (-(f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, neg_add, zpow_add₀ Complex.I_ne_zero, ih]

omit hD8 in
/-- `(−1)^{⟨γ_{S'}, n⟩} = (−1)^{⟨γ_∅, n⟩} i^{−Σ_{S'} n_i}`. -/
theorem form_sign {S' : Finset (Fin 24)} (he : _root_.Even S'.card) (n : leech.carrier) :
    (-1 : ℂ) ^ (leech.form (inclΛ (aSA hDA S')) n)
      = (-1 : ℂ) ^ (leech.form (inclΛ (bAD hDA)) n) * Complex.I ^ (-(∑ i ∈ S', lv n i)) := by
  have h1 := eight_dvd_lv (inclΛ (aSA hDA S')) n
  have h2 := eight_dvd_lv (inclΛ (bAD hDA)) n
  rw [leech_form_lv, leech_form_lv]
  rw [lv_inclΛ, valA_aSA hDA he] at h1 ⊢
  rw [lv_inclΛ] at h2 ⊢
  change (8 : ℤ) ∣ (2 : ℤ) • ind D ⬝ᵥ lv n at h2
  change _ = (-1 : ℂ) ^ (((2 : ℤ) • ind D ⬝ᵥ lv n) / 8) * _
  have hB : ind S' ⬝ᵥ lv n = ∑ i ∈ S', lv n i := by
    simp only [dotProduct, ind, ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  rw [smul_dotProduct, sub_dotProduct, smul_dotProduct, hB] at h1 ⊢
  rw [smul_dotProduct] at h2 ⊢
  simp only [smul_eq_mul] at h1 h2 ⊢
  obtain ⟨p, hp⟩ := h2
  have hA : ind D ⬝ᵥ lv n = 4 * p := by omega
  rw [hA] at h1 ⊢
  obtain ⟨q, hq⟩ := h1
  have hBq : ∑ i ∈ S', lv n i = 2 * (p - q) := by omega
  rw [hBq, show 2 * (4 * p - 2 * (2 * (p - q))) / 8 = q by omega,
    show 2 * (4 * p) / 8 = p by omega, show -(2 * (p - q)) = 2 * (q - p) by ring, zpow_mul,
    show Complex.I ^ (2 : ℤ) = -1 by rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, Complex.I_sq],
    ← zpow_add₀ (by norm_num)]
  congr 1; ring

/-- The local sign `ζ_i = s_i · (−1) · i⁻¹ · i^{−n_i}` of the Hadamard sum. -/
noncomputable def zetaS (S : Finset (Fin 24)) (n : leech.carrier) (i : Fin 24) : ℂ :=
  (if i ∈ S then -1 else 1) * (-1) * (Complex.I)⁻¹ * Complex.I ^ (-(lv n i))

omit hD8 in
theorem prod_zetaS (S S' : Finset (Fin 24)) (n : leech.carrier) :
    ∏ i ∈ S', zetaS S n i = (-1 : ℂ) ^ (S ∩ S').card * ((-1 : ℂ) ^ S'.card * (Complex.I ^ S'.card)⁻¹)
      * Complex.I ^ (-(∑ i ∈ S', lv n i)) := by
  unfold zetaS
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite,
    Finset.prod_const, Finset.prod_const_one, mul_one, Finset.prod_const, Finset.prod_const,
    I_zpow_sum, inv_pow]
  rw [show (Finset.filter (fun i => i ∈ S) S') = S ∩ S' by
    ext i; simp [Finset.mem_inter, and_comm]]
  ring

/-! ## §10  The Hadamard-sum form of the target -/

/-- The `S'`-independent prefactor. -/
noncomputable def C0 (S : Finset (Fin 24)) (n : leech.carrier) : ℂ :=
  2 * cD D * rH ^ D.card * XS hDA S * (2 : ℂ) ^ (-(4 : ℤ)) * cE n *
    (-1 : ℂ) ^ (leech.form (inclΛ (bAD hDA)) n)

omit hD8 in
theorem eL_comm_apply (γ n : leech.carrier) (t : TLeechT) :
    eL γ (eL n t) = (-1 : ℂ) ^ (leech.form γ n) • eL n (eL γ t) :=
  congrArg (fun f : End ℂ TLeechT => f t) (eT_comm_sign' leech leech_even leech_isUnit_det_gramMat γ n)

omit hD8 in
theorem eL_eq_Wop (a : lam0.carrier) (t : TLeechT) : eL (inclΛ a) t = (tc a)⁻¹ • Wop a t := by
  rw [Wop, LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ (tc_ne_zero a), one_smul]

/-- **Each term of the target sum**: `K(S,S') 2⁻⁴ e_{γ_{S'}} τ⋆(n) = C₀ ∏_{i ∈ S'} ζ_i · e_n W(b) t`. -/
theorem term_eval {t : TLeechT} (ht : IsSeed t) {S S' : Finset (Fin 24)} (h : _root_.Even S.card)
    (hS : S ⊆ D) (he' : _root_.Even S'.card) (hS' : S' ⊆ D) (n : leech.carrier) :
    (KS hDA S S' * (2 : ℂ) ^ (-(4 : ℤ))) • eL (inclΛ (aSA hDA S')) (tauStar t n)
      = (C0 hDA S n * ∏ i ∈ S', zetaS S n i) • eL n (Wop (bAD hDA) t) := by
  rw [tauStar, map_smul, eL_comm_apply, eL_eq_Wop, Wop_aSA_seed hDA ht he', map_smul, map_smul,
    smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [KS, coef_even hDA hD8 h hS hS' he', form_sign hDA he', prod_zetaS, C0]
  have hn := nuC_eps_xi hDA hS'
  have htc : tc (aSA hDA S') * (tc (aSA hDA S'))⁻¹ = 1 := mul_inv_cancel₀ (tc_ne_zero _)
  set K := 2 * cD D * rH ^ D.card * XS hDA S * (-1 : ℂ) ^ (S ∩ S').card * (2 : ℂ) ^ (-(4 : ℤ)) * cE n *
    (-1 : ℂ) ^ (leech.form (inclΛ (bAD hDA)) n) * Complex.I ^ (-(∑ i ∈ S', lv n i))
  linear_combination K * (nuC (inclN (bAD hDA)) S' * εN (inclN (bAD hDA)) (dl S') * xi (-ind S')) * htc
    + K * hn

/-! ## §11  The `h`-parts `latL γ_{S'} (w_b)` -/

omit hD8 in
theorem chargeCoord_eq_sum_cw (γ : leech.carrier) :
    chargeCoord leech γ = ∑ l, (((lv γ l : ℤ) : ℂ) / 8) • cw l := by
  conv_lhs => rw [pi_eq_sum_single (chargeCoord leech γ)]
  simp_rw [single_eq_sum_cw, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_smul, ← pair_cw_left γ l, Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by ring

omit hD8 in
theorem latL_cw (γ : leech.carrier) (b : Fin 24) :
    latL γ (cw b) = cw b - ∑ l, (((2 * lv γ b * lv γ l : ℤ) : ℂ) / 8) • cw l := by
  rw [latL_apply, pair_cw_left, chargeCoord_eq_sum_cw, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul]; congr 1; push_cast; ring

omit hD8 in
/-- `s'_i = ±1` according to `i ∉ S'` / `i ∈ S'`, as a product over `S'`. -/
theorem prod_single_sign (S' : Finset (Fin 24)) (b : Fin 24) :
    ∏ i ∈ S', (if i = b then (-1 : ℂ) else 1) = if b ∈ S' then -1 else 1 := by
  rw [Finset.prod_ite_eq']

/-- The pair sign pattern `η^{bl}`. -/
def etaS (b l : Fin 24) (i : Fin 24) : ℂ := (if i = b then -1 else 1) * (if i = l then -1 else 1)

omit hD8 in
theorem lv_aSA_mul {S' : Finset (Fin 24)} (he : _root_.Even S'.card) (hS' : S' ⊆ D) (b l : Fin 24) :
    (((2 * lv (inclΛ (aSA hDA S')) b * lv (inclΛ (aSA hDA S')) l : ℤ) : ℂ) / 8)
      = if b ∈ D ∧ l ∈ D then ∏ i ∈ S', etaS b l i else 0 := by
  rw [lv_inclΛ, valA_aSA hDA he]
  simp only [etaS, Finset.prod_mul_distrib, prod_single_sign, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, ind]
  have hbS' : b ∉ D → b ∉ S' := fun h h' => h (hS' h')
  have hlS' : l ∉ D → l ∉ S' := fun h h' => h (hS' h')
  by_cases hb : b ∈ D <;> by_cases hl : l ∈ D
  · by_cases hbS : b ∈ S' <;> by_cases hlS : l ∈ S' <;> simp [hb, hl, hbS, hlS] <;> norm_num
  · simp [hb, hl, hlS' hl]
  · simp [hb, hl, hbS' hb]
  · simp [hb, hl, hbS' hb, hlS' hl]

/-- **The target, summed**: `o(σ u_{γ_S})(h_{w_b} ⊗ τ⋆(n))` as a Hadamard sum. -/
theorem rhs_formula {t : TLeechT} (ht : IsSeed t) {S : Finset (Fin 24)} (h : _root_.Even S.card)
    (hS : S ⊆ D) (n : leech.carrier) (b : Fin 24) :
    actT (sig (lV (inclΛ (aSA hDA S)) (inclΛ_mem _))) 1 (hP (cw b) (tauStar t n))
      = (C0 hDA S n * ∑ S' ∈ D.powerset.filter (fun S' : Finset (Fin 24) => _root_.Even S'.card),
            ∏ i ∈ S', zetaS S n i) • hP (cw b) (eL n (Wop (bAD hDA) t))
        - ∑ l, (if b ∈ D ∧ l ∈ D then C0 hDA S n * ∑ S' ∈ D.powerset.filter
            (fun S' : Finset (Fin 24) => _root_.Even S'.card), ∏ i ∈ S', (zetaS S n i * etaS b l i)
            else 0) • hP (cw l) (eL n (Wop (bAD hDA) t)) := by
  rw [actT_sig_lV_aSA hDA hD8 h hS]
  have hterm : ∀ S' ∈ D.powerset.filter (fun S' : Finset (Fin 24) => _root_.Even S'.card),
      (KS hDA S S' * (2 : ℂ) ^ (-(4 : ℤ))) • hP (latL (inclΛ (aSA hDA S')) (cw b))
          (eL (inclΛ (aSA hDA S')) (tauStar t n))
        = (C0 hDA S n * ∏ i ∈ S', zetaS S n i) • hP (cw b) (eL n (Wop (bAD hDA) t))
          - ∑ l, ((if b ∈ D ∧ l ∈ D then C0 hDA S n * ∏ i ∈ S', (zetaS S n i * etaS b l i) else 0))
              • hP (cw l) (eL n (Wop (bAD hDA) t)) := by
    intro S' hS'
    obtain ⟨hS'p, he'⟩ := Finset.mem_filter.mp hS'
    rw [← hP_smul_right, term_eval hDA hD8 ht h hS he' (Finset.mem_powerset.mp hS'p), latL_cw,
      hP_sub_left, hP_smul_right, hP_sum_left]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [lv_aSA_mul hDA he' (Finset.mem_powerset.mp hS'p), hP_smul_left, hP_smul_right, smul_smul]
    congr 1
    split_ifs
    · rw [Finset.prod_mul_distrib]; ring
    · ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_smul, Finset.mul_sum,
    Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  split_ifs
  · rw [Finset.mul_sum]
  · simp

/-! ## §12  Sign patterns -/

omit hD8 in
theorem sum_pm_bounds (X : Finset (Fin 24)) (p : Fin 24 → ℤ) (hp : ∀ i ∈ X, p i = 1 ∨ p i = -1) :
    -(X.card : ℤ) ≤ ∑ i ∈ X, p i ∧ ∑ i ∈ X, p i ≤ X.card := by
  constructor
  · have : ∑ i ∈ X, (-1 : ℤ) ≤ ∑ i ∈ X, p i :=
      Finset.sum_le_sum fun i hi => by rcases hp i hi with h | h <;> rw [h] <;> norm_num
    simpa using this
  · have : ∑ i ∈ X, p i ≤ ∑ i ∈ X, (1 : ℤ) :=
      Finset.sum_le_sum fun i hi => by rcases hp i hi with h | h <;> rw [h] <;> norm_num
    simpa using this

omit hD8 in
theorem sum_pm_eq_neg (X : Finset (Fin 24)) (p : Fin 24 → ℤ) (hp : ∀ i ∈ X, p i = 1 ∨ p i = -1)
    (h : ∑ i ∈ X, p i = -(X.card : ℤ)) : ∀ i ∈ X, p i = -1 := by
  have h0 : ∑ i ∈ X, (p i + 1) = 0 := by rw [Finset.sum_add_distrib, h]; simp
  intro i hi
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => by
    rcases hp j hj with h' | h' <;> rw [h'] <;> norm_num)).mp h0 i hi
  linarith

omit hD8 in
theorem sum_pm_eq_pos (X : Finset (Fin 24)) (p : Fin 24 → ℤ) (hp : ∀ i ∈ X, p i = 1 ∨ p i = -1)
    (h : ∑ i ∈ X, p i = (X.card : ℤ)) : ∀ i ∈ X, p i = 1 := by
  have h0 : ∑ i ∈ X, (1 - p i) = 0 := by rw [Finset.sum_sub_distrib, h]; simp
  intro i hi
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => by
    rcases hp j hj with h' | h' <;> rw [h'] <;> norm_num)).mp h0 i hi
  linarith

/-- The integer pattern `p_i = s_i n_i` (`s_i = −1` on `S`). -/
def pS (S : Finset (Fin 24)) (n : leech.carrier) (i : Fin 24) : ℤ := (if i ∈ S then -1 else 1) * lv n i

omit hD8 in
theorem zetaS_val (S : Finset (Fin 24)) (n : leech.carrier) (i : Fin 24)
    (hv : lv n i = 1 ∨ lv n i = -1 ∨ lv n i = 3 ∨ lv n i = -3) :
    zetaS S n i = if pS S n i = 1 ∨ pS S n i = -3 then 1 else -1 := by
  unfold zetaS pS
  have hI : Complex.I⁻¹ = -Complex.I := Complex.inv_I
  by_cases hS : i ∈ S <;> rcases hv with h | h | h | h <;> simp only [hS, h, if_true, if_false] <;>
    norm_num [hI, zpow_neg, zpow_ofNat, Complex.I_sq, pow_succ, Complex.I_mul_I]

/-! ## §13  The source side -/

theorem form_aSA_self {S : Finset (Fin 24)} (h : _root_.Even S.card) (hS : S ⊆ D) :
    leech.form (inclΛ (aSA hDA S)) (inclΛ (aSA hDA S)) = 4 := form_aSA hDA S h hS hD8

omit hD8 in
theorem ind_dot (X : Finset (Fin 24)) (f : Fin 24 → ℤ) : ind X ⬝ᵥ f = ∑ i ∈ X, f i := by
  simp only [dotProduct, ind, ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]

omit hD8 in
theorem sum_pS {S : Finset (Fin 24)} (hS : S ⊆ D) (n : leech.carrier) :
    ∑ i ∈ D, pS S n i = ∑ i ∈ D, lv n i - 2 * ∑ i ∈ S, lv n i := by
  have h1 : ∑ i ∈ D, pS S n i = ∑ i ∈ D, (lv n i - 2 * (if i ∈ S then lv n i else 0)) :=
    Finset.sum_congr rfl fun i _ => by unfold pS; split_ifs <;> ring
  rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr hS]

omit hD8 in
theorem four_form_aSA {S : Finset (Fin 24)} (h : _root_.Even S.card) (hS : S ⊆ D) (n : leech.carrier) :
    4 * leech.form (inclΛ (aSA hDA S)) n = ∑ i ∈ D, pS S n i := by
  have h8 := eight_dvd_lv (inclΛ (aSA hDA S)) n
  rw [leech_form_lv]
  rw [lv_inclΛ, valA_aSA hDA h, smul_dotProduct, sub_dotProduct, smul_dotProduct, ind_dot, ind_dot,
    smul_eq_mul, smul_eq_mul] at h8 ⊢
  rw [sum_pS hS]
  omega

omit hD8 in
theorem four_form_bAD (n : leech.carrier) :
    4 * leech.form (inclΛ (bAD hDA)) n = ∑ i ∈ D, lv n i := by
  have h8 := eight_dvd_lv (inclΛ (bAD hDA)) n
  rw [leech_form_lv]
  rw [lv_inclΛ] at h8 ⊢
  change (8 : ℤ) ∣ (2 : ℤ) • ind D ⬝ᵥ lv n at h8
  change 4 * ((2 : ℤ) • ind D ⬝ᵥ lv n / 8) = _
  rw [smul_dotProduct, ind_dot, smul_eq_mul] at h8 ⊢
  omega

omit hD8 in
/-- The `Θ`-type scalar `tc(a_S)⁻¹ ε ξ`, in terms of `XS`. -/
theorem tc_eps_xi_eq {S : Finset (Fin 24)} (hS : S ⊆ D) :
    (tc (aSA hDA S))⁻¹ * (εN (inclN (bAD hDA)) (dl S) * xi (-ind S))
      = XS hDA S * ((-1 : ℂ) ^ S.card * (Complex.I ^ S.card)⁻¹) := by
  rw [← nuC_eps_xi hDA hS, XS]
  have := nuC_ne_zero (inclN (bAD hDA)) S
  field_simp

/-- **The source term**: `ε(γ_S,n) φ⋆(x_{γ_S+n})` for a move `⟨γ_S,n⟩ = −2`. -/
theorem lhs_term {t : TLeechT} (ht : IsSeed t) {S : Finset (Fin 24)} (h : _root_.Even S.card) (hS : S ⊆ D)
    {n : leech.carrier} (hn0 : n ∉ lambda0) (h4 : leech.form n n = 4)
    (hf : leech.form (inclΛ (aSA hDA S)) n = -2) :
    εΛ (inclΛ (aSA hDA S)) n • phiV3 (tauStar t) (frameX0P (inclΛ (aSA hDA S) + n))
      = hP (cw (blk (inclΛ (aSA hDA S) + n)))
          ((cE (inclΛ (aSA hDA S) + n) * (XS hDA S * ((-1 : ℂ) ^ S.card * (Complex.I ^ S.card)⁻¹)))
            • eL n (Wop (bAD hDA) t)) := by
  have h0' := not_mem_add (inclΛ_mem (aSA hDA S)) hn0
  have h4' := form_self_add (form_aSA_self hDA hD8 h hS) h4 hf
  rw [phiV3_frameX0P_any (tauStar_neg t) h0' h4', ← hP_smul_right, tauStar, smul_comm,
    eps_eL_add _ _ ⟨-1, by rw [hf]; norm_num⟩, eL_eq_Wop, Wop_aSA_seed hDA ht h, map_smul, map_smul,
    smul_smul, smul_smul]
  congr 2
  rw [← tc_eps_xi_eq hDA hS]; ring

/-! ## §14  The normalisation `c⋆` along octad moves -/

omit hD8 in
theorem lv_aSA_apply {S : Finset (Fin 24)} (h : _root_.Even S.card) (i : Fin 24) :
    lv (inclΛ (aSA hDA S)) i = 2 * (ind D i - 2 * ind S i) := by
  rw [lv_inclΛ, valA_aSA hDA h]; simp [Pi.smul_apply, smul_eq_mul]

omit hD8 in
theorem I_zpow_cD {S : Finset (Fin 24)} (hS : S ⊆ D) :
    Complex.I ^ (2 * (ind D 0 - 2 * ind S 0)) = cD D := by
  unfold cD ind
  by_cases h0 : (0 : Fin 24) ∈ D
  · by_cases h0S : (0 : Fin 24) ∈ S
    · simp only [h0, h0S, if_true]; norm_num; rw [zpow_two, Complex.I_mul_I]; norm_num
    · simp only [h0, h0S, if_true, if_false]; norm_num
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, Complex.I_sq]
  · have h0S : (0 : Fin 24) ∉ S := fun h' => h0 (hS h')
    simp [h0, h0S]

omit hD8 in
/-- **`c⋆` along an octad move**: `c⋆(γ_S + m) · sign(m_blk) = (χz₀-sign) · sign((γ_S+m)_blk) · c⋆(m)`. -/
theorem cE_aSA_add {S : Finset (Fin 24)} (h : _root_.Even S.card) (hS : S ⊆ D) {m : leech.carrier}
    (hm0 : m ∉ lambda0) :
    cE (inclΛ (aSA hDA S) + m) * sgnBlk m = cD D * sgnBlk (inclΛ (aSA hDA S) + m) * cE m := by
  have h0' := not_mem_add (inclΛ_mem (aSA hDA S)) hm0
  rw [cE_eq hm0, cE_eq h0', cStar, cStar, lv_add, Pi.add_apply, lv_aSA_apply hDA h,
    zpow_add₀ Complex.I_ne_zero, I_zpow_cD hS]
  ring

/-! ## §15  The octad identity on `V₃⁺` -/

omit hD8 in
theorem sum_sI {S : Finset (Fin 24)} (hS : S ⊆ D) :
    ∑ i ∈ D, (if i ∈ S then (-1 : ℤ) else 1) = D.card - 2 * S.card := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr hS]
  have hc := Finset.card_filter_add_card_filter_not (s := D) (fun i => i ∈ S)
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hS] at hc
  rw [nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  omega

omit hD8 in
theorem lv_eq_of_pS {S : Finset (Fin 24)} {n : leech.carrier} {i : Fin 24} {v : ℤ} (hp : pS S n i = v) :
    lv n i = (if i ∈ S then -1 else 1) * v := by
  rw [← hp, pS]; split_ifs <;> ring

omit hD8 in
theorem pS_neg (S : Finset (Fin 24)) (n : leech.carrier) (i : Fin 24) : pS S (-n) i = -pS S n i := by
  simp [pS, lv_neg]

theorem C0_mul (S : Finset (Fin 24)) (n : leech.carrier) :
    C0 hDA S n * (2 ^ D.card / 2) = cD D * XS hDA S * cE n * (-1 : ℂ) ^ (leech.form (inclΛ (bAD hDA)) n) := by
  rw [C0, hD8, rH_pow_eight]; norm_num; ring

omit hD8 in
theorem signS {S : Finset (Fin 24)} (h : _root_.Even S.card) :
    (-1 : ℂ) ^ S.card * (Complex.I ^ S.card)⁻¹ = (-1 : ℂ) ^ (S.card / 2) := by
  obtain ⟨m, hm⟩ := h
  rw [hm, show m + m = 2 * m by ring, pow_mul, pow_mul, Complex.I_sq]
  norm_num
  rcases neg_one_pow_eq_or ℂ m with h' | h' <;> rw [h'] <;> norm_num

omit hD8 in
theorem sgnBlk_ne_zero {n : leech.carrier} (hn0 : n ∉ lambda0) (h4 : leech.form n n = 4) : sgnBlk n ≠ 0 := by
  have h := lv_sq hn0 h4 (blk n)
  rw [if_pos rfl] at h
  rw [sgnBlk]
  refine div_ne_zero ?_ (by norm_num)
  intro h0
  have : lv n (blk n) = 0 := by exact_mod_cast h0
  rw [this] at h; norm_num at h

omit hD8 in
theorem form_bAD_val {S : Finset (Fin 24)} (h : _root_.Even S.card) (hS : S ⊆ D) {n : leech.carrier}
    {c : ℤ} (hc : ∑ i ∈ D, lv n i = c) :
    (-1 : ℂ) ^ (leech.form (inclΛ (bAD hDA)) n) = (-1 : ℂ) ^ (c / 4) := by
  have := four_form_bAD hDA n
  rw [hc] at this
  rw [show leech.form (inclΛ (bAD hDA)) n = c / 4 by omega]

/-- **Octad letters, block outside the octad.** -/
theorem octad_out {t : TLeechT} (ht : IsSeed t) {S : Finset (Fin 24)} (h : _root_.Even S.card)
    (hS : S ⊆ D) {n : leech.carrier} (hn : n ∈ halfFourChi 1) (hb : blk n ∉ D) :
    phiV3 (tauStar t) (actV (lV (inclΛ (aSA hDA S)) (inclΛ_mem _)) 1 (frameX0P n))
      = actT (sig (lV (inclΛ (aSA hDA S)) (inclΛ_mem _))) 1 (phiV3 (tauStar t) (frameX0P n)) := by
  obtain ⟨h4, h1⟩ := mem_halfFourChi hn
  have hn0 : n ∉ lambda0 := by rw [mem_lambda0, h1]; exact one_ne_zero
  have hsq := lv_sq hn0 h4
  have hv1 : ∀ i ∈ D, lv n i = 1 ∨ lv n i = -1 := fun i hi => by
    have := hsq i; rw [if_neg (fun h' : i = blk n => hb (h' ▸ hi))] at this; exact int_sq_one this
  have hp1 : ∀ i ∈ D, pS S n i = 1 ∨ pS S n i = -1 := fun i hi => by
    unfold pS; rcases hv1 i hi with h' | h' <;> rw [h'] <;> split_ifs <;> simp
  have hζ : ∀ i ∈ D, zetaS S n i = 1 ∨ zetaS S n i = -1 := fun i hi => by
    rw [zetaS_val S n i (by rcases hv1 i hi with h' | h' <;> simp [h'])]
    split_ifs <;> simp
  have hζp : ∀ i ∈ D, (zetaS S n i = 1 ↔ pS S n i = 1) := fun i hi => by
    rw [zetaS_val S n i (by rcases hv1 i hi with h' | h' <;> simp [h'])]
    rcases hp1 i hi with h' | h' <;> simp [h'] <;> norm_num
  have hζm : ∀ i ∈ D, (zetaS S n i = -1 ↔ pS S n i = -1) := fun i hi => by
    rw [zetaS_val S n i (by rcases hv1 i hi with h' | h' <;> simp [h'])]
    rcases hp1 i hi with h' | h' <;> simp [h'] <;> norm_num
  have hDne : D.Nonempty := Finset.card_pos.mp (by rw [hD8]; norm_num)
  have hlb : lv (inclΛ (aSA hDA S)) (blk n) = 0 := by
    have hbS : blk n ∉ S := fun h' => hb (hS h')
    rw [lv_aSA_apply hDA h]; simp [ind, hb, hbS]
  rw [actV_lV (inclΛ_mem _) hn0 (form_aSA_self hDA hD8 h hS) h4, map_add, phiV3_frameX0P _ hn,
    rhs_formula hDA hD8 ht h hS n (blk n)]
  have hsum0 : ∑ l, (if blk n ∈ D ∧ l ∈ D then C0 hDA S n * ∑ S' ∈ D.powerset.filter
      (fun S' : Finset (Fin 24) => _root_.Even S'.card), ∏ i ∈ S', (zetaS S n i * etaS (blk n) l i)
      else 0) • hP (cw l) (eL n (Wop (bAD hDA) t)) = 0 :=
    Finset.sum_eq_zero fun l _ => by rw [if_neg (fun h' => hb h'.1), zero_smul]
  rw [hsum0, sub_zero, sum_even_pm D _ hζ]
  have h4f := four_form_aSA hDA h hS n
  have hsI := sum_sI hS
  have hcard : (D.card : ℤ) = 8 := by exact_mod_cast hD8
  obtain ⟨m, hm⟩ := h
  by_cases hA : ∀ i ∈ D, pS S n i = -1
  · -- the move `⟨γ_S, n⟩ = −2`
    have hP8 : ∑ i ∈ D, pS S n i = -8 := by
      rw [Finset.sum_congr rfl hA]; simp [hD8]
    have hf : leech.form (inclΛ (aSA hDA S)) n = -2 := by omega
    have hnotB : ¬ ∀ i ∈ D, zetaS S n i = 1 := fun h' => by
      obtain ⟨i, hi⟩ := hDne; have := (hζp i hi).mp (h' i hi); rw [hA i hi] at this; norm_num at this
    rw [if_pos hf, if_neg (by rw [hf]; norm_num), map_zero, add_zero, map_smul,
      lhs_term hDA hD8 ht ⟨m, hm⟩ hS hn0 h4 hf,
      if_neg hnotB, if_pos (fun i hi => (hζm i hi).mpr (hA i hi)), zero_add]
    have hblk : blk (inclΛ (aSA hDA S) + n) = blk n := by
      have hn3 := hsq (blk n); rw [if_pos rfl] at hn3
      refine blk_eq_of_three (not_mem_add (inclΛ_mem _) hn0)
        (form_self_add (form_aSA_self hDA hD8 ⟨m, hm⟩ hS) h4 hf) ?_
      rw [lv_add, Pi.add_apply, hlb, zero_add]; exact int_sq_nine hn3
    rw [hblk, hP_smul_right]
    congr 1
    have hc := cE_aSA_add hDA ⟨m, hm⟩ hS hn0
    have hsg : sgnBlk (inclΛ (aSA hDA S) + n) = sgnBlk n := by
      rw [sgnBlk, sgnBlk, hblk, lv_add, Pi.add_apply, hlb, zero_add]
    rw [hsg] at hc
    have hce : cE (inclΛ (aSA hDA S) + n) = cD D * cE n :=
      mul_right_cancel₀ (sgnBlk_ne_zero hn0 h4) (by rw [hc]; ring)
    have hsumn : ∑ i ∈ D, lv n i = -(8 - 2 * (2 * m)) := by
      rw [Finset.sum_congr rfl fun i hi => lv_eq_of_pS (hA i hi)]
      have := hsI; simp only [mul_neg, mul_one] at this ⊢
      rw [Finset.sum_neg_distrib, this, hcard, hm]; push_cast; ring
    rw [hce, signS ⟨m, hm⟩, C0_mul hDA hD8 S n, form_bAD_val hDA ⟨m, hm⟩ hS hsumn, hm]
    rw [show (m + m) / 2 = m by omega, show -(8 - 2 * (2 * (m : ℤ))) / 4 = (m : ℤ) - 2 by omega,
      zpow_sub₀ (by norm_num), zpow_natCast]
    norm_num; ring
  · by_cases hB : ∀ i ∈ D, pS S n i = 1
    · -- the move `⟨γ_S, −n⟩ = −2`
      have hP8 : ∑ i ∈ D, pS S n i = 8 := by
        rw [Finset.sum_congr rfl hB]; simp [hD8]
      have hf2 : leech.form (inclΛ (aSA hDA S)) n = 2 := by omega
      have hfm : leech.form (inclΛ (aSA hDA S)) (-n) = -2 := by rw [map_neg, hf2]
      have hn0' : -n ∉ lambda0 := fun h' => hn0 (by simpa using neg_mem h')
      have h4' : leech.form (-n) (-n) = 4 := by simp only [map_neg, LinearMap.neg_apply, neg_neg]; exact h4
      have hnotA : ¬ ∀ i ∈ D, zetaS S n i = -1 := fun h' => by
        obtain ⟨i, hi⟩ := hDne; have := (hζm i hi).mp (h' i hi); rw [hB i hi] at this; norm_num at this
      rw [if_neg (by rw [hf2]; norm_num), if_pos hf2, map_zero, zero_add, map_smul, sub_eq_add_neg,
        lhs_term hDA hD8 ht ⟨m, hm⟩ hS hn0' h4' hfm,
        if_pos (fun i hi => (hζp i hi).mpr (hB i hi)), if_neg hnotA, add_zero]
      have hlbn : lv (inclΛ (aSA hDA S) + -n) (blk n) = -lv n (blk n) := by
        rw [lv_add, lv_neg, Pi.add_apply, Pi.neg_apply, hlb, zero_add]
      have hblk : blk (inclΛ (aSA hDA S) + -n) = blk n := by
        have hn3 := hsq (blk n); rw [if_pos rfl] at hn3
        refine blk_eq_of_three (not_mem_add (inclΛ_mem _) hn0')
          (form_self_add (form_aSA_self hDA hD8 ⟨m, hm⟩ hS) h4' hfm) ?_
        rw [hlbn]; rcases int_sq_nine hn3 with h' | h' <;> rw [h'] <;> norm_num
      have heL : eL (-n) (Wop (bAD hDA) t) = eL n (Wop (bAD hDA) t) :=
        congrArg (fun f : End ℂ TLeechT => f (Wop (bAD hDA) t)) (eT_neg leech leech_even leech_isUnit_det_gramMat n)
      rw [hblk, heL, hP_smul_right]
      congr 1
      have hc := cE_aSA_add hDA ⟨m, hm⟩ hS hn0'
      have hsg : sgnBlk (inclΛ (aSA hDA S) + -n) = sgnBlk (-n) := by
        rw [sgnBlk, sgnBlk, hblk, blk_neg, hlbn, lv_neg, Pi.neg_apply]
      rw [hsg] at hc
      have hce : cE (inclΛ (aSA hDA S) + -n) = cD D * cE n := by
        rw [cE_neg] at hc
        exact mul_right_cancel₀ (sgnBlk_ne_zero hn0' h4') (by rw [hc]; ring)
      have hsumn : ∑ i ∈ D, lv n i = 8 - 2 * (2 * m) := by
        rw [Finset.sum_congr rfl fun i hi => lv_eq_of_pS (hB i hi)]
        have := hsI; simp only [mul_one] at this ⊢
        rw [this, hcard, hm]; push_cast; ring
      rw [hce, signS ⟨m, hm⟩, C0_mul hDA hD8 S n, form_bAD_val hDA ⟨m, hm⟩ hS hsumn, hm]
      rw [show (m + m) / 2 = m by omega, show (8 - 2 * (2 * (m : ℤ))) / 4 = 2 - (m : ℤ) by omega,
        zpow_sub₀ (by norm_num), zpow_natCast]
      rcases neg_one_pow_eq_or ℂ m with h' | h' <;> rw [h'] <;> norm_num <;> ring
    · -- no move: both sides vanish
      have hnA : ¬ ∀ i ∈ D, zetaS S n i = -1 := fun h' => hA fun i hi => (hζm i hi).mp (h' i hi)
      have hnB : ¬ ∀ i ∈ D, zetaS S n i = 1 := fun h' => hB fun i hi => (hζp i hi).mp (h' i hi)
      have hf1 : leech.form (inclΛ (aSA hDA S)) n ≠ -2 := fun hf => hA
        (sum_pm_eq_neg D (pS S n) hp1 (by rw [hD8]; push_cast; omega))
      have hf2 : leech.form (inclΛ (aSA hDA S)) n ≠ 2 := fun hf => hB
        (sum_pm_eq_pos D (pS S n) hp1 (by rw [hD8]; push_cast; omega))
      rw [if_neg hf1, if_neg hf2, if_neg hnA, if_neg hnB, map_zero]
      simp

omit hD8 in
theorem sum_ite_univ_mem (D : Finset (Fin 24)) {M : Type*} [AddCommMonoid M] (f : Fin 24 → M) :
    ∑ l, (if l ∈ D then f l else 0) = ∑ l ∈ D, f l := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

omit hD8 in
theorem etaS_self (b i : Fin 24) : etaS b b i = 1 := by
  unfold etaS; split_ifs <;> norm_num

omit hD8 in
/-- A configuration lemma: three-level sums of a `±1` pattern. -/
theorem sum_split_two {X : Finset (Fin 24)} {b l : Fin 24} (hb : b ∈ X) (hl : l ∈ X.erase b) (p : Fin 24 → ℤ) :
    ∑ i ∈ X, p i = p b + p l + ∑ i ∈ (X.erase b).erase l, p i := by
  rw [← Finset.add_sum_erase X p hb, ← Finset.add_sum_erase (X.erase b) p hl]; ring

/-- **Octad letters, block inside the octad.** -/
theorem octad_in {t : TLeechT} (ht : IsSeed t) {S : Finset (Fin 24)} (h : _root_.Even S.card)
    (hS : S ⊆ D) {n : leech.carrier} (hn : n ∈ halfFourChi 1) (hb : blk n ∈ D) :
    phiV3 (tauStar t) (actV (lV (inclΛ (aSA hDA S)) (inclΛ_mem _)) 1 (frameX0P n))
      = actT (sig (lV (inclΛ (aSA hDA S)) (inclΛ_mem _))) 1 (phiV3 (tauStar t) (frameX0P n)) := by
  obtain ⟨h4, h1⟩ := mem_halfFourChi hn
  have hn0 : n ∉ lambda0 := by rw [mem_lambda0, h1]; exact one_ne_zero
  have hsq := lv_sq hn0 h4
  set b := blk n with hbdef
  have hvb : lv n b = 3 ∨ lv n b = -3 := by have := hsq b; rw [if_pos rfl] at this; exact int_sq_nine this
  have hv1 : ∀ i, i ≠ b → lv n i = 1 ∨ lv n i = -1 := fun i hi => by
    have := hsq i; rw [if_neg hi] at this; exact int_sq_one this
  have hvall : ∀ i, lv n i = 1 ∨ lv n i = -1 ∨ lv n i = 3 ∨ lv n i = -3 := fun i => by
    by_cases hi : i = b
    · subst hi; rcases hvb with h' | h' <;> simp [h']
    · rcases hv1 i hi with h' | h' <;> simp [h']
  have hpb : pS S n b = 3 ∨ pS S n b = -3 := by
    unfold pS; rcases hvb with h' | h' <;> rw [h'] <;> split_ifs <;> simp
  have hp1 : ∀ i, i ≠ b → pS S n i = 1 ∨ pS S n i = -1 := fun i hi => by
    unfold pS; rcases hv1 i hi with h' | h' <;> rw [h'] <;> split_ifs <;> simp
  have hζb : zetaS S n b = if pS S n b = -3 then 1 else -1 := by
    rw [zetaS_val S n b (hvall b)]; rcases hpb with h' | h' <;> simp [h']
  have hζi : ∀ i, i ≠ b → zetaS S n i = (pS S n i : ℂ) := fun i hi => by
    rw [zetaS_val S n i (hvall i)]; rcases hp1 i hi with h' | h' <;> simp [h']
  have hζη : ∀ l i, i ∈ D → zetaS S n i * etaS b l i = 1 ∨ zetaS S n i * etaS b l i = -1 := by
    intro l i _
    have hz : zetaS S n i = 1 ∨ zetaS S n i = -1 := by
      by_cases hi : i = b
      · subst hi; rw [hζb]; split_ifs <;> simp
      · rw [hζi i hi]; rcases hp1 i hi with h' | h' <;> simp [h']
    unfold etaS
    rcases hz with h' | h' <;> rw [h'] <;> split_ifs <;> simp
  have hζpm : ∀ i ∈ D, zetaS S n i = 1 ∨ zetaS S n i = -1 := fun i hi => by
    have := hζη b i hi; rwa [etaS_self, mul_one] at this
  -- the configurations
  have hA_iff : ∀ l ∈ D.erase b, (∀ i ∈ D, zetaS S n i * etaS b l i = -1) →
      pS S n b = -3 ∧ pS S n l = 1 ∧ ∀ i ∈ (D.erase b).erase l, pS S n i = -1 := by
    intro l hl hA
    have hlb : l ≠ b := Finset.ne_of_mem_erase hl
    refine ⟨?_, ?_, ?_⟩
    · have := hA b hb; unfold etaS at this
      rw [if_pos rfl, if_neg (Ne.symm hlb), hζb] at this
      split_ifs at this with h'
      · exact h'
      · norm_num at this
    · have := hA l (Finset.mem_of_mem_erase hl); rw [hζi l hlb] at this; unfold etaS at this
      rw [if_neg hlb, if_pos rfl] at this
      rcases hp1 l hlb with h' | h'
      · exact h'
      · rw [h'] at this; norm_num at this
    · intro i hi
      have hil : i ≠ l := Finset.ne_of_mem_erase hi
      have hib : i ≠ b := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      have := hA i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
      rw [hζi i hib] at this; unfold etaS at this
      rw [if_neg hib, if_neg hil] at this
      rcases hp1 i hib with h' | h'
      · rw [h'] at this; norm_num at this
      · exact h'
  have hB_iff : ∀ l ∈ D.erase b, (∀ i ∈ D, zetaS S n i * etaS b l i = 1) →
      pS S n b = 3 ∧ pS S n l = -1 ∧ ∀ i ∈ (D.erase b).erase l, pS S n i = 1 := by
    intro l hl hB
    have hlb : l ≠ b := Finset.ne_of_mem_erase hl
    refine ⟨?_, ?_, ?_⟩
    · have := hB b hb; unfold etaS at this
      rw [if_pos rfl, if_neg (Ne.symm hlb), hζb] at this
      split_ifs at this with h'
      · norm_num at this
      · rcases hpb with h'' | h''
        · exact h''
        · exact absurd h'' h'
    · have := hB l (Finset.mem_of_mem_erase hl); rw [hζi l hlb] at this; unfold etaS at this
      rw [if_neg hlb, if_pos rfl] at this
      rcases hp1 l hlb with h' | h'
      · rw [h'] at this; norm_num at this
      · exact h'
    · intro i hi
      have hil : i ≠ l := Finset.ne_of_mem_erase hi
      have hib : i ≠ b := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      have := hB i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
      rw [hζi i hib] at this; unfold etaS at this
      rw [if_neg hib, if_neg hil] at this
      rcases hp1 i hib with h' | h'
      · exact h'
      · rw [h'] at this; norm_num at this
  have hcardE : ((D.erase b).card : ℤ) = 7 := by rw [Finset.card_erase_of_mem hb, hD8]; norm_num
  have hcardEE : ∀ l ∈ D.erase b, (((D.erase b).erase l).card : ℤ) = 6 := fun l hl => by
    rw [Finset.card_erase_of_mem hl, Finset.card_erase_of_mem hb, hD8]; norm_num
  have hp1E : ∀ i ∈ D.erase b, pS S n i = 1 ∨ pS S n i = -1 := fun i hi =>
    hp1 i (Finset.ne_of_mem_erase hi)
  have hp1EE : ∀ l, ∀ i ∈ (D.erase b).erase l, pS S n i = 1 ∨ pS S n i = -1 := fun l i hi =>
    hp1E i (Finset.mem_of_mem_erase hi)
  have hsplit : ∀ l ∈ D.erase b, ∑ i ∈ D, pS S n i
      = pS S n b + pS S n l + ∑ i ∈ (D.erase b).erase l, pS S n i := fun l hl => sum_split_two hb hl _
  -- the target side
  rw [actV_lV (inclΛ_mem _) hn0 (form_aSA_self hDA hD8 h hS) h4, map_add, phiV3_frameX0P _ hn,
    rhs_formula hDA hD8 ht h hS n b]
  have hR : ∀ (g : Fin 24 → ℂ) (v : Fin 24 → TP),
      ∑ l, (if b ∈ D ∧ l ∈ D then g l else 0) • v l = g b • v b + ∑ l ∈ D.erase b, g l • v l := by
    intro g v
    rw [Finset.add_sum_erase D (fun l => g l • v l) hb, ← sum_ite_univ_mem D (fun l => g l • v l)]
    exact Finset.sum_congr rfl fun l _ => by
      by_cases hl : l ∈ D <;> simp [hl, hb]
  rw [hR]
  simp only [etaS_self, mul_one]
  rw [sub_add_eq_sub_sub, sub_self, zero_sub]
  simp only [fun l => sum_even_pm D _ (hζη l)]
  have h4f := four_form_aSA hDA h hS n
  have hsI := sum_sI hS
  have hcard : (D.card : ℤ) = 8 := by exact_mod_cast hD8
  obtain ⟨m, hm⟩ := h
  have hbS : b ∈ S ∨ b ∉ S := em _
  by_cases hP1 : ∑ i ∈ D, pS S n i = -8
  · -- the move `⟨γ_S,n⟩ = −2`
    have hf : leech.form (inclΛ (aSA hDA S)) n = -2 := by omega
    have hEbd := sum_pm_bounds (D.erase b) (pS S n) hp1E
    have hpb3 : pS S n b = -3 := by
      have := Finset.add_sum_erase D (pS S n) hb
      rcases hpb with h' | h'
      · exfalso
        have h1' := hEbd.1
        rw [hcardE] at h1'
        linarith
      · exact h'
    obtain ⟨l₀, hl₀, hpl₀⟩ : ∃ l ∈ D.erase b, pS S n l = 1 := by
      by_contra hcon
      push Not at hcon
      have hall : ∀ i ∈ D.erase b, pS S n i = -1 := fun i hi =>
        (hp1E i hi).resolve_left (hcon i hi)
      have := Finset.add_sum_erase D (pS S n) hb
      rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_neg, nsmul_eq_mul, mul_one, hcardE,
        hpb3] at this
      linarith
    have hrest : ∀ i ∈ (D.erase b).erase l₀, pS S n i = -1 :=
      sum_pm_eq_neg _ _ (hp1EE l₀) (by have := hsplit l₀ hl₀; rw [hcardEE l₀ hl₀]; omega)
    have hl₀b : l₀ ≠ b := Finset.ne_of_mem_erase hl₀
    -- the pattern holds exactly at `l₀`
    have hA0 : ∀ i ∈ D, zetaS S n i * etaS b l₀ i = -1 := by
      intro i hi
      unfold etaS
      by_cases hib : i = b
      · subst hib; rw [hζb, if_pos hpb3, if_pos rfl, if_neg (Ne.symm hl₀b)]; norm_num
      · by_cases hil : i = l₀
        · subst hil; rw [hζi i hib, hpl₀, if_neg hib, if_pos rfl]; norm_num
        · have hi' : i ∈ (D.erase b).erase l₀ := Finset.mem_erase.mpr ⟨hil, Finset.mem_erase.mpr ⟨hib, hi⟩⟩
          rw [hζi i hib, hrest i hi', if_neg hib, if_neg hil]; norm_num
    have hnB : ∀ l ∈ D.erase b, ¬ ∀ i ∈ D, zetaS S n i * etaS b l i = 1 := fun l hl hB' => by
      have := (hB_iff l hl hB').1; rw [hpb3] at this; norm_num at this
    have hnA : ∀ l ∈ D.erase b, l ≠ l₀ → ¬ ∀ i ∈ D, zetaS S n i * etaS b l i = -1 := fun l hl hll hA' => by
      have := (hA_iff l hl hA').2.1
      have hl' : l ∈ (D.erase b).erase l₀ := Finset.mem_erase.mpr ⟨hll, hl⟩
      rw [hrest l hl'] at this; norm_num at this
    rw [Finset.sum_eq_single l₀ (fun l hl hll => by rw [if_neg (hnB l hl), if_neg (hnA l hl hll)]; simp)
      (fun h' => absurd hl₀ h'), if_neg (hnB l₀ hl₀), if_pos hA0]
    rw [if_pos hf, if_neg (by rw [hf]; norm_num), map_zero, add_zero, map_smul,
      lhs_term hDA hD8 ht ⟨m, hm⟩ hS hn0 h4 hf]
    -- the new block is `l₀`
    have hnl₀ : lv n l₀ = (if l₀ ∈ S then -1 else 1) * 1 := lv_eq_of_pS hpl₀
    have hlvl₀ : lv (inclΛ (aSA hDA S) + n) l₀ = 3 * (if l₀ ∈ S then -1 else 1) := by
      rw [lv_add, Pi.add_apply, lv_aSA_apply hDA ⟨m, hm⟩, hnl₀]
      simp only [ind, Finset.mem_of_mem_erase hl₀, if_true]
      split_ifs <;> norm_num
    have hblk : blk (inclΛ (aSA hDA S) + n) = l₀ :=
      blk_eq_of_three (not_mem_add (inclΛ_mem _) hn0)
        (form_self_add (form_aSA_self hDA hD8 ⟨m, hm⟩ hS) h4 hf)
        (by rw [hlvl₀]; split_ifs <;> norm_num)
    rw [hblk, hP_smul_right, ← neg_smul]
    congr 1
    have hc := cE_aSA_add hDA ⟨m, hm⟩ hS hn0
    have hnb : lv n b = (if b ∈ S then -1 else 1) * (-3) := lv_eq_of_pS hpb3
    have hsgn : sgnBlk n = -(if b ∈ S then (-1 : ℂ) else 1) := by
      rw [sgnBlk, ← hbdef, hnb]; split_ifs <;> norm_num
    have hsgn' : sgnBlk (inclΛ (aSA hDA S) + n) = (if l₀ ∈ S then (-1 : ℂ) else 1) := by
      rw [sgnBlk, hblk, hlvl₀]; split_ifs <;> norm_num
    rw [hsgn, hsgn'] at hc
    have hsumn : ∑ i ∈ D, lv n i = -2 * (if b ∈ S then -1 else 1) + 2 * (if l₀ ∈ S then -1 else 1)
        - (8 - 2 * (2 * m)) := by
      have e1 : ∑ i ∈ D, lv n i = ∑ i ∈ D, (if i ∈ S then -1 else 1) * pS S n i :=
        Finset.sum_congr rfl fun i _ => by unfold pS; split_ifs <;> ring
      have e2 := sum_split_two hb hl₀ (fun i => (if i ∈ S then (-1 : ℤ) else 1) * pS S n i)
      have e3 := sum_split_two hb hl₀ (fun i => (if i ∈ S then (-1 : ℤ) else 1))
      have e4 : ∑ i ∈ (D.erase b).erase l₀, (if i ∈ S then (-1 : ℤ) else 1) * pS S n i
          = -∑ i ∈ (D.erase b).erase l₀, (if i ∈ S then (-1 : ℤ) else 1) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i hi => by rw [hrest i hi]; ring
      simp only at e2 e3
      rw [e1, e2, e4, hpb3, hpl₀]
      rw [hsI, hcard, hm] at e3
      push_cast at e3 ⊢
      linarith
    have hce : cE (inclΛ (aSA hDA S) + n) = -(cD D * (if l₀ ∈ S then (-1 : ℂ) else 1) *
        (if b ∈ S then (-1 : ℂ) else 1)) * cE n := by
      have hs2 : (if b ∈ S then (-1 : ℂ) else 1) * (if b ∈ S then (-1 : ℂ) else 1) = 1 := by
        split_ifs <;> norm_num
      linear_combination (-(if b ∈ S then (-1 : ℂ) else 1)) * hc
        - (cE (inclΛ (aSA hDA S) + n)) * hs2
    rw [hce, signS ⟨m, hm⟩, zero_add, C0_mul hDA hD8 S n, form_bAD_val hDA ⟨m, hm⟩ hS hsumn, hm,
      show (m + m) / 2 = m by omega]
    by_cases hbS' : b ∈ S <;> by_cases hlS : l₀ ∈ S <;> simp only [hbS', hlS, if_true, if_false] <;>
      [rw [show (-2 * (-1) + 2 * (-1) - (8 - 2 * (2 * (m : ℤ)))) / 4 = (m : ℤ) - 2 by omega];
       rw [show (-2 * (-1) + 2 * 1 - (8 - 2 * (2 * (m : ℤ)))) / 4 = (m : ℤ) - 1 by omega];
       rw [show (-2 * 1 + 2 * (-1) - (8 - 2 * (2 * (m : ℤ)))) / 4 = (m : ℤ) - 3 by omega];
       rw [show (-2 * 1 + 2 * 1 - (8 - 2 * (2 * (m : ℤ)))) / 4 = (m : ℤ) - 2 by omega]] <;>
      rw [zpow_sub₀ (by norm_num), zpow_natCast] <;>
      rcases neg_one_pow_eq_or ℂ m with h' | h' <;> rw [h'] <;> norm_num <;> ring
  · by_cases hP2 : ∑ i ∈ D, pS S n i = 8
    · -- the move `⟨γ_S,−n⟩ = −2`
      have hf2 : leech.form (inclΛ (aSA hDA S)) n = 2 := by omega
      have hfm : leech.form (inclΛ (aSA hDA S)) (-n) = -2 := by rw [map_neg, hf2]
      have hn0' : -n ∉ lambda0 := fun h' => hn0 (by simpa using neg_mem h')
      have h4' : leech.form (-n) (-n) = 4 := by simp only [map_neg, LinearMap.neg_apply, neg_neg]; exact h4
      have hEbd := sum_pm_bounds (D.erase b) (pS S n) hp1E
      have hpb3 : pS S n b = 3 := by
        have := Finset.add_sum_erase D (pS S n) hb
        rcases hpb with h' | h'
        · exact h'
        · exfalso
          have h1' := hEbd.2
          rw [hcardE] at h1'
          linarith
      obtain ⟨l₀, hl₀, hpl₀⟩ : ∃ l ∈ D.erase b, pS S n l = -1 := by
        by_contra hcon
        push Not at hcon
        have hall : ∀ i ∈ D.erase b, pS S n i = 1 := fun i hi =>
          (hp1E i hi).resolve_right (hcon i hi)
        have := Finset.add_sum_erase D (pS S n) hb
        rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, mul_one, hcardE, hpb3] at this
        linarith
      have hrest : ∀ i ∈ (D.erase b).erase l₀, pS S n i = 1 :=
        sum_pm_eq_pos _ _ (hp1EE l₀) (by have := hsplit l₀ hl₀; rw [hcardEE l₀ hl₀]; omega)
      have hl₀b : l₀ ≠ b := Finset.ne_of_mem_erase hl₀
      have hB0 : ∀ i ∈ D, zetaS S n i * etaS b l₀ i = 1 := by
        intro i hi
        unfold etaS
        by_cases hib : i = b
        · subst hib; rw [hζb, if_neg (by rw [hpb3]; norm_num), if_pos rfl, if_neg (Ne.symm hl₀b)]; norm_num
        · by_cases hil : i = l₀
          · subst hil; rw [hζi i hib, hpl₀, if_neg hib, if_pos rfl]; norm_num
          · have hi' : i ∈ (D.erase b).erase l₀ := Finset.mem_erase.mpr ⟨hil, Finset.mem_erase.mpr ⟨hib, hi⟩⟩
            rw [hζi i hib, hrest i hi', if_neg hib, if_neg hil]; norm_num
      have hnA : ∀ l ∈ D.erase b, ¬ ∀ i ∈ D, zetaS S n i * etaS b l i = -1 := fun l hl hA' => by
        have := (hA_iff l hl hA').1; rw [hpb3] at this; norm_num at this
      have hnB : ∀ l ∈ D.erase b, l ≠ l₀ → ¬ ∀ i ∈ D, zetaS S n i * etaS b l i = 1 := fun l hl hll hB' => by
        have := (hB_iff l hl hB').2.1
        have hl' : l ∈ (D.erase b).erase l₀ := Finset.mem_erase.mpr ⟨hll, hl⟩
        rw [hrest l hl'] at this; norm_num at this
      rw [Finset.sum_eq_single l₀ (fun l hl hll => by rw [if_neg (hnB l hl hll), if_neg (hnA l hl)]; simp)
        (fun h' => absurd hl₀ h'), if_pos hB0, if_neg (hnA l₀ hl₀)]
      rw [if_neg (by rw [hf2]; norm_num), if_pos hf2, map_zero, zero_add, map_smul, sub_eq_add_neg,
        lhs_term hDA hD8 ht ⟨m, hm⟩ hS hn0' h4' hfm]
      have hnl₀ : lv n l₀ = (if l₀ ∈ S then -1 else 1) * (-1) := lv_eq_of_pS hpl₀
      have hlvl₀ : lv (inclΛ (aSA hDA S) + -n) l₀ = 3 * (if l₀ ∈ S then -1 else 1) := by
        rw [lv_add, lv_neg, Pi.add_apply, Pi.neg_apply, lv_aSA_apply hDA ⟨m, hm⟩, hnl₀]
        simp only [ind, Finset.mem_of_mem_erase hl₀, if_true]
        split_ifs <;> norm_num
      have hblk : blk (inclΛ (aSA hDA S) + -n) = l₀ :=
        blk_eq_of_three (not_mem_add (inclΛ_mem _) hn0')
          (form_self_add (form_aSA_self hDA hD8 ⟨m, hm⟩ hS) h4' hfm)
          (by rw [hlvl₀]; split_ifs <;> norm_num)
      have heL : eL (-n) (Wop (bAD hDA) t) = eL n (Wop (bAD hDA) t) :=
        congrArg (fun f : End ℂ TLeechT => f (Wop (bAD hDA) t)) (eT_neg leech leech_even leech_isUnit_det_gramMat n)
      rw [hblk, heL, hP_smul_right, ← neg_smul]
      congr 1
      have hc := cE_aSA_add hDA ⟨m, hm⟩ hS hn0'
      have hnb : lv n b = (if b ∈ S then -1 else 1) * 3 := lv_eq_of_pS hpb3
      have hsgn : sgnBlk (-n) = -(if b ∈ S then (-1 : ℂ) else 1) := by
        rw [sgnBlk, blk_neg, ← hbdef, lv_neg, Pi.neg_apply, hnb]; split_ifs <;> norm_num
      have hsgn' : sgnBlk (inclΛ (aSA hDA S) + -n) = (if l₀ ∈ S then (-1 : ℂ) else 1) := by
        rw [sgnBlk, hblk, hlvl₀]; split_ifs <;> norm_num
      rw [hsgn, hsgn', cE_neg] at hc
      have hsumn : ∑ i ∈ D, lv n i = 2 * (if b ∈ S then -1 else 1) - 2 * (if l₀ ∈ S then -1 else 1)
          + (8 - 2 * (2 * m)) := by
        have e1 : ∑ i ∈ D, lv n i = ∑ i ∈ D, (if i ∈ S then -1 else 1) * pS S n i :=
          Finset.sum_congr rfl fun i _ => by unfold pS; split_ifs <;> ring
        have e2 := sum_split_two hb hl₀ (fun i => (if i ∈ S then (-1 : ℤ) else 1) * pS S n i)
        have e3 := sum_split_two hb hl₀ (fun i => (if i ∈ S then (-1 : ℤ) else 1))
        have e4 : ∑ i ∈ (D.erase b).erase l₀, (if i ∈ S then (-1 : ℤ) else 1) * pS S n i
            = ∑ i ∈ (D.erase b).erase l₀, (if i ∈ S then (-1 : ℤ) else 1) :=
          Finset.sum_congr rfl fun i hi => by rw [hrest i hi]; ring
        simp only at e2 e3
        rw [e1, e2, e4, hpb3, hpl₀]
        rw [hsI, hcard, hm] at e3
        push_cast at e3 ⊢
        linarith
      have hce : cE (inclΛ (aSA hDA S) + -n) = -(cD D * (if l₀ ∈ S then (-1 : ℂ) else 1) *
          (if b ∈ S then (-1 : ℂ) else 1)) * cE n := by
        have hs2 : (if b ∈ S then (-1 : ℂ) else 1) * (if b ∈ S then (-1 : ℂ) else 1) = 1 := by
          split_ifs <;> norm_num
        linear_combination (-(if b ∈ S then (-1 : ℂ) else 1)) * hc
          - (cE (inclΛ (aSA hDA S) + -n)) * hs2
      rw [hce, signS ⟨m, hm⟩, add_zero, C0_mul hDA hD8 S n, form_bAD_val hDA ⟨m, hm⟩ hS hsumn, hm,
        show (m + m) / 2 = m by omega]
      by_cases hbS' : b ∈ S <;> by_cases hlS : l₀ ∈ S <;> simp only [hbS', hlS, if_true, if_false] <;>
        [rw [show (2 * (-1) - 2 * (-1) + (8 - 2 * (2 * (m : ℤ)))) / 4 = 2 - (m : ℤ) by omega];
         rw [show (2 * (-1) - 2 * 1 + (8 - 2 * (2 * (m : ℤ)))) / 4 = 1 - (m : ℤ) by omega];
         rw [show (2 * 1 - 2 * (-1) + (8 - 2 * (2 * (m : ℤ)))) / 4 = 3 - (m : ℤ) by omega];
         rw [show (2 * 1 - 2 * 1 + (8 - 2 * (2 * (m : ℤ)))) / 4 = 2 - (m : ℤ) by omega]] <;>
        rw [zpow_sub₀ (by norm_num), zpow_natCast] <;>
        rcases neg_one_pow_eq_or ℂ m with h' | h' <;> rw [h'] <;> norm_num <;> ring
    · -- no move: both sides vanish
      have hnA : ∀ l ∈ D.erase b, ¬ ∀ i ∈ D, zetaS S n i * etaS b l i = -1 := fun l hl hA' => by
        obtain ⟨h1', h2', h3'⟩ := hA_iff l hl hA'
        have hr := Finset.sum_congr rfl h3'
        rw [Finset.sum_const, smul_neg, nsmul_eq_mul, mul_one, hcardEE l hl] at hr
        exact hP1 (by rw [hsplit l hl, h1', h2', hr]; norm_num)
      have hnB : ∀ l ∈ D.erase b, ¬ ∀ i ∈ D, zetaS S n i * etaS b l i = 1 := fun l hl hB' => by
        obtain ⟨h1', h2', h3'⟩ := hB_iff l hl hB'
        have hr := Finset.sum_congr rfl h3'
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcardEE l hl] at hr
        exact hP2 (by rw [hsplit l hl, h1', h2', hr]; norm_num)
      have hf1 : leech.form (inclΛ (aSA hDA S)) n ≠ -2 := fun hf => hP1 (by omega)
      have hf2 : leech.form (inclΛ (aSA hDA S)) n ≠ 2 := fun hf => hP2 (by omega)
      rw [if_neg hf1, if_neg hf2, map_zero, add_zero]
      rw [Finset.sum_eq_zero fun l hl => by rw [if_neg (hnB l hl), if_neg (hnA l hl)]; simp]
      simp

/-- **The octad letters intertwine** for `φ⋆`: for every octad `D`, every even `S ⊆ D`. -/
theorem phiV3_ZM_aSA {t : TLeechT} (ht : IsSeed t) {S : Finset (Fin 24)} (h : _root_.Even S.card)
    (hS : S ⊆ D) : ZM (phiV3 (tauStar t)) OmegaV3 (lV (inclΛ (aSA hDA S)) (inclΛ_mem _)) := by
  refine ZM_of_basis _ _ fun n hn => ?_
  by_cases hb : blk n ∈ D
  · exact octad_in hDA hD8 ht h hS hn hb
  · exact octad_out hDA hD8 ht h hS hn hb

end VOA.Moonshine.SigmaTop
