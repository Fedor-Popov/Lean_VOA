/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.CharacterDelta
import VOA.Modularity.JInvariantAnalytic
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# The level-two identity `t(τ) + t(-1/τ) + t(-1/(τ+1)) = j - 768`  (Moonshine step M7d, part 3)

The third identity of `CharacterSeries.lean`, proved:

  `levelTwoIdentity : LevelTwoIdentity`, i.e.
  `∏(1+qⁿ)^{-24} + 2¹³ q² T_odd = q·j - 768 q` in `ℂ⟦q⟧`,

with `T_odd = Σ P_T(24, 2n+1) qⁿ` the (compressed) odd part of `∏(1-x^{2i+1})^{-24}`,
`x = q^{1/2}`.  With `t = η(τ)^{24}/η(2τ)^{24} = Δ(τ)/Δ(2τ)` this is the trace of the `Γ₀(2)`
hauptmodul over the three cosets of `Γ₀(2)` in `SL₂(ℤ)`.

## Route
* §1 (analytic).  `phiFun z = Δ(z)² (Δ(2z)⁻¹ + 2¹² Δ(z/2)⁻¹ + 2¹² Δ((z+1)/2)⁻¹)`, with the
  maps `dblH`, `hlfH`, `hlf1H` (`affH a b`: `z ↦ a z + b`).  `T` swaps the last two terms
  (`phiFun_of_add_one`); `S` permutes all three, the third via `gammaST = [[1,-1],[2,-1]]`
  (`phiFun_of_neg_inv`).  Holomorphy `phiFun_mdiff`; boundedness at `i∞`
  `phiFun_isBoundedAtImInfty` from `|Δ| ≍ e^{-2π Im}` (`sq_div_comp_affH_isBigO`).  Hence
  `phiForm : ModularForm 𝒮ℒ 12`.
* §2 (formal).  `fockSigned_mul_expand_deltaProd : ∏(1+qⁿ)^{-24} ∏(1-q^{2n})^{24} = ∏(1-qⁿ)^{24}`,
  `fock_eq_tw_mul_expand : ∏(1-qⁿ)^{-24} = ∏(1-q^{2i+1})^{-24} ∏(1-q^{2n})^{-24}` (odd/even
  splitting, `HasProd.even_mul_odd`), the even series `Gser`, its compression `Hser`, and
  `phiSeries = D² · P(q²) + 2¹² Hser`; `phiSeries_mul_fock : phiSeries · P = B + 2¹³ q² T_odd`
  and `levelTwoIdentity_of_phiSeries`.
* §4 (bridge).  `phiFun_eq_ev : Φ(τ) = Σ [qⁿ]phiSeries · qⁿ` (via `CharacterBridge` and
  `Δ(w) = q_w · ev D q_w`), so `qExpansion_phiForm : qExpansion Φ = phiSeries`;
  `phiSeries_coeff_zero_one` (`1`, `-48`) and the `M₁₂` structure give
  `phiSeries_eq : phiSeries = E₄³ - 768Δ`.

## Status
All declarations proved, no `sorry`, no new axioms.
-/

set_option linter.style.longLine false

open scoped MatrixGroups ModularForm Manifold
open UpperHalfPlane ModularForm Complex PowerSeries Filter Topology
open scoped PowerSeries.WithPiTopology

namespace VOA

namespace Moonshine

open QBridge

/-! ## §1  The modular form `Φ` -/

local notation "Δ" => ModularForm.discriminant

/-- `z ↦ a z + b` on `ℍ` for real `a > 0`, `b`. -/
noncomputable def affH (a b : ℝ) (ha : 0 < a) (z : ℍ) : ℍ :=
  ⟨(a : ℂ) * z + b, by simpa using mul_pos ha z.im_pos⟩

@[simp] theorem coe_affH (a b : ℝ) (ha : 0 < a) (z : ℍ) : (affH a b ha z : ℂ) = a * z + b := rfl

theorem affH_ext {w z : ℍ} (h : (w : ℂ) = z) : w = z := UpperHalfPlane.ext h

theorem discriminant_T (z : ℍ) (w : ℍ) (h : (w : ℂ) = z + 1) : Δ w = Δ z := by
  have := discriminant_smul ModularGroup.T z
  have hw : w = ModularGroup.T • z := by
    apply UpperHalfPlane.ext; rw [h, modular_T_smul]; simp [add_comm]
  rw [hw, this]; simp [ModularGroup.T]

theorem discriminant_S (z w : ℍ) (h : (w : ℂ) = -(z : ℂ)⁻¹) : Δ w = (z : ℂ) ^ 12 * Δ z := by
  have := discriminant_smul ModularGroup.S z
  have hw : w = ModularGroup.S • z := by
    apply UpperHalfPlane.ext; rw [h, modular_S_smul]; simp
  rw [hw, this]; simp [ModularGroup.S]; left; norm_cast

/-- `γ = [[1,-1],[2,-1]]`. -/
def gammaST : SL(2, ℤ) := ⟨!![1, -1; 2, -1], by simp [Matrix.det_fin_two]⟩

theorem discriminant_gam (z w : ℍ) (h : (w : ℂ) = ((z : ℂ) - 1) / (2 * z - 1)) :
    Δ w = (2 * (z : ℂ) - 1) ^ 12 * Δ z := by
  have := discriminant_smul gammaST z
  have hw : w = gammaST • z := by
    apply UpperHalfPlane.ext; rw [h, specialLinearGroup_apply]; simp [gammaST]; ring_nf
  rw [hw, this]; simp [gammaST]; left
  rw [sub_eq_add_neg]; norm_cast

noncomputable abbrev dblH : ℍ → ℍ := affH 2 0 two_pos
noncomputable abbrev hlfH : ℍ → ℍ := affH (1 / 2) 0 (by norm_num)
noncomputable abbrev hlf1H : ℍ → ℍ := affH (1 / 2) (1 / 2) (by norm_num)

/-- `Φ(z) = Δ(z)² (Δ(2z)⁻¹ + 2¹² Δ(z/2)⁻¹ + 2¹² Δ((z+1)/2)⁻¹)`. -/
noncomputable def phiFun (z : ℍ) : ℂ :=
  Δ z ^ 2 * ((Δ (dblH z))⁻¹ + 4096 * (Δ (hlfH z))⁻¹ + 4096 * (Δ (hlf1H z))⁻¹)

theorem phiFun_of_add_one (z w : ℍ) (hTz : (w : ℂ) = z + 1) : phiFun w = phiFun z := by
  have h1 : Δ w = Δ z := discriminant_T z _ hTz
  have h2 : Δ (dblH w) = Δ (dblH z) := by
    rw [discriminant_T (affH 2 1 two_pos z) _ (by rw [coe_affH, coe_affH, hTz]; push_cast; ring),
      discriminant_T (dblH z) _ (by rw [coe_affH, coe_affH]; push_cast; ring)]
  have h3 : hlfH w = hlf1H z := by
    apply UpperHalfPlane.ext; rw [coe_affH, coe_affH, hTz]; push_cast; ring
  have h4 : Δ (hlf1H w) = Δ (hlfH z) :=
    discriminant_T (hlfH z) _ (by rw [coe_affH, coe_affH, hTz]; push_cast; ring)
  rw [phiFun, phiFun, h1, h2, h3, h4]; ring

theorem phiFun_of_neg_inv (z w : ℍ) (hSz : (w : ℂ) = -(z : ℂ)⁻¹) :
    phiFun w = (z : ℂ) ^ 12 * phiFun z := by
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have h1 : Δ w = (z : ℂ) ^ 12 * Δ z := discriminant_S z _ hSz
  have h2 : Δ (dblH w) = ((z : ℂ) / 2) ^ 12 * Δ (hlfH z) := by
    rw [discriminant_S (hlfH z) _ (by rw [coe_affH, coe_affH, hSz]; push_cast; simp only [add_zero]; field_simp)]
    rw [coe_affH]; push_cast; ring
  have h3 : Δ (hlfH w) = (2 * (z : ℂ)) ^ 12 * Δ (dblH z) := by
    rw [discriminant_S (dblH z) _ (by rw [coe_affH, coe_affH, hSz]; push_cast; simp only [add_zero]; field_simp)]
    rw [coe_affH]; push_cast; ring
  have h4 : Δ (hlf1H w) = (z : ℂ) ^ 12 * Δ (hlf1H z) := by
    have h2z : (2 * ((z : ℂ) + 1) / 2 - 1) = z := by ring
    rw [discriminant_gam (hlf1H z) _ (by
      rw [coe_affH, coe_affH, hSz]; push_cast; field_simp; ring_nf; field_simp)]
    rw [coe_affH]; push_cast; ring
  have d0 := discriminant_ne_zero z
  have d1 := discriminant_ne_zero (dblH z)
  have d2 := discriminant_ne_zero (hlfH z)
  have d3 := discriminant_ne_zero (hlf1H z)
  rw [phiFun, phiFun, h1, h2, h3, h4]
  field_simp
  ring

theorem phiFun_slash_S : phiFun ∣[(12 : ℤ)] ModularGroup.S = phiFun := by
  ext z
  rw [ModularForm.slash_action_eq'_iff, phiFun_of_neg_inv z _ (by rw [modular_S_smul]; simp)]
  simp [ModularGroup.S]; left; norm_cast

theorem phiFun_slash_T : phiFun ∣[(12 : ℤ)] ModularGroup.T = phiFun := by
  ext z
  rw [ModularForm.slash_action_eq'_iff,
    phiFun_of_add_one z _ (by rw [modular_T_smul]; simp [add_comm])]
  simp [ModularGroup.T]

theorem mdiff_comp_affH {f : ℍ → ℂ} (hf : MDiff f) (a b : ℝ) (ha : 0 < a) :
    MDiff (fun z => f (affH a b ha z)) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have hmaps : Set.MapsTo (fun w : ℂ => (a : ℂ) * w + b) {z : ℂ | 0 < z.im} {z : ℂ | 0 < z.im} :=
    fun w hw => by simpa using mul_pos ha hw
  refine (hf.comp ((differentiable_id.const_mul _).add_const _).differentiableOn hmaps).congr
    fun w hw => ?_
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw,
    ofComplex_apply_of_im_pos (hmaps hw)]
  rfl

theorem mdiff_discriminant : MDiff (Δ : ℍ → ℂ) := by
  have := ModularFormClass.holo CuspForm.discriminant
  rwa [CuspForm.coe_discriminant] at this

theorem phiFun_mdiff : MDiff phiFun := by
  have hD := mdiff_discriminant
  have hinv : ∀ (a b : ℝ) (ha : 0 < a), MDiff (fun z => (Δ (affH a b ha z))⁻¹) := fun a b ha =>
    (mdiff_comp_affH hD a b ha).inv fun z => discriminant_ne_zero _
  have := (hD.pow 2).mul (((hinv 2 0 two_pos).add
    ((mdifferentiable_const (c := (4096 : ℂ))).mul (hinv (1/2) 0 (by norm_num)))).add
    ((mdifferentiable_const (c := (4096 : ℂ))).mul (hinv (1/2) (1/2) (by norm_num))))
  exact this

open Asymptotics Filter in
theorem tendsto_affH (a b : ℝ) (ha : 0 < a) : Tendsto (affH a b ha) atImInfty atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  have : (UpperHalfPlane.im ∘ affH a b ha) = fun z => a * z.im := by
    funext z; show ((a : ℂ) * z + b).im = a * (z : ℂ).im; simp
  rw [this]
  exact Tendsto.const_mul_atTop ha tendsto_comap

open Asymptotics Filter in
theorem discriminant_isBigO_exp :
    (Δ : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  have := CuspFormClass.exp_decay_atImInfty (h := 1) CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL
  simpa using this

open Asymptotics Filter in
/-- `Δ(z)² / Δ(a z + b) = O(1)` at the cusp for `0 < a ≤ 2`. -/
theorem sq_div_comp_affH_isBigO (a b : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) :
    (fun z : ℍ => Δ z ^ 2 * (Δ (affH a b ha z))⁻¹) =O[atImInfty] (fun _ => (1 : ℝ)) := by
  have hlow := exp_isBigO_discriminant.comp_tendsto (tendsto_affH a b ha)
  have hinv := hlow.inv_rev (Eventually.of_forall fun z h => absurd h (Real.exp_pos _).ne')
  have hup := discriminant_isBigO_exp.pow 2
  refine (hup.mul hinv).trans ?_
  refine IsBigO.of_bound 1 ?_
  refine Eventually.of_forall fun z => ?_
  have hy := z.im_pos
  have him : (affH a b ha z).im = a * z.im := by
    show ((a : ℂ) * z + b).im = _; simp
  simp only [Function.comp_apply, him, norm_one, mul_one]
  rw [norm_mul, norm_pow, norm_inv, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.exp_pos _).le, sq, ← Real.exp_add, ← Real.exp_neg, ← Real.exp_add,
    Real.exp_le_one_iff]
  nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hy.le) (sub_nonneg.mpr ha2)]

open Asymptotics Filter in
theorem phiFun_isBoundedAtImInfty : IsBoundedAtImInfty phiFun := by
  have h1 := sq_div_comp_affH_isBigO 2 0 two_pos le_rfl
  have h2 := sq_div_comp_affH_isBigO (1/2) 0 (by norm_num) (by norm_num)
  have h3 := sq_div_comp_affH_isBigO (1/2) (1/2) (by norm_num) (by norm_num)
  have := (h1.add (h2.const_mul_left 4096)).add (h3.const_mul_left 4096)
  refine this.congr_left fun z => ?_
  simp only [phiFun]; ring

/-- **`Φ` is a level-one modular form of weight 12.** -/
noncomputable def phiForm : ModularForm 𝒮ℒ 12 where
  toFun := phiFun
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact SlashInvariantForm.slash_action_generators_SL2Z phiFun_slash_S phiFun_slash_T A
  holo' := phiFun_mdiff
  bdd_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [SlashInvariantForm.slash_action_generators_SL2Z phiFun_slash_S phiFun_slash_T γ]
    exact phiFun_isBoundedAtImInfty


/-! ## §2  Formal product identities -/

noncomputable abbrev expandTwo : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ := PowerSeries.expand 2 two_ne_zero

theorem hasProd_expand {u : ℕ → PowerSeries ℂ} {F : PowerSeries ℂ} (h : HasProd u F) :
    HasProd (fun i => expandTwo (u i)) (expandTwo F) := by
  unfold HasProd at h ⊢
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at h ⊢
  intro n
  simp only [← map_prod, PowerSeries.coeff_expand]
  split_ifs
  · exact h _
  · exact tendsto_const_nhds

theorem expand_inv {g : PowerSeries ℂ} (hg : constantCoeff g ≠ 0) : expandTwo g⁻¹ = (expandTwo g)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by rwa [constantCoeff_expand])]
  rw [← map_mul, PowerSeries.inv_mul_cancel _ hg, map_one]

theorem expand_one_sub_X_pow (k : ℕ) : expandTwo ((1 : PowerSeries ℂ) - X ^ k) = 1 - X ^ (2 * k) := by
  rw [map_sub, map_one, map_pow, expand_X, ← pow_mul]

/-- `∏(1+qⁿ)^{-24} · ∏(1-q^{2n})^{24} = ∏(1-qⁿ)^{24}`. -/
theorem fockSigned_mul_expand_deltaProd :
    LatGen.fockSignedGenFun 24 * expandTwo deltaProd = deltaProd := by
  have h := (LatGen.hasProd_fockSignedGenFun 24).mul (hasProd_expand hasProd_deltaProd)
  have hf : (fun i : ℕ => ((1 + (X : PowerSeries ℂ) ^ (i + 1))⁻¹) ^ 24 *
      expandTwo (((1 : PowerSeries ℂ) - X ^ (i + 1)) ^ 24)) = fun i => ((1 : PowerSeries ℂ) - X ^ (i + 1)) ^ 24 := by
    funext i
    rw [map_pow, expand_one_sub_X_pow, ← mul_pow]
    congr 1
    have h1 : (1 : PowerSeries ℂ) - X ^ (2 * (i + 1)) = (1 - X ^ (i + 1)) * (1 + X ^ (i + 1)) := by ring
    rw [h1, mul_comm (1 - X ^ (i + 1)), ← mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), one_mul]
  rw [hf] at h
  exact h.unique hasProd_deltaProd

/-- `∏(1-qⁿ)^{-24} = ∏(1-q^{2i+1})^{-24} · ∏(1-q^{2n})^{-24}` (odd and even factors). -/
theorem fock_eq_tw_mul_expand :
    LatGen.fockGenFun 24 = TwistedSector.twGenFun 24 * expandTwo (LatGen.fockGenFun 24) := by
  have he := TwistedSector.hasProd_twGenFun 24
  have ho := hasProd_expand (LatGen.hasProd_fockGenFun 24)
  have he' : HasProd (fun k : ℕ => ((1 - (X : PowerSeries ℂ) ^ (2 * k + 1))⁻¹) ^ 24)
      (TwistedSector.twGenFun 24) := he
  have ho' : HasProd (fun k : ℕ => ((1 - (X : PowerSeries ℂ) ^ (2 * k + 1 + 1))⁻¹) ^ 24)
      (expandTwo (LatGen.fockGenFun 24)) := by
    convert ho using 2 with k
    rw [map_pow, expand_inv (by simp), expand_one_sub_X_pow]
    ring_nf
  have h := HasProd.even_mul_odd (f := fun i : ℕ => ((1 - (X : PowerSeries ℂ) ^ (i + 1))⁻¹) ^ 24)
    he' ho'
  exact (LatGen.hasProd_fockGenFun 24).unique h

local notation "P24" => LatGen.fockGenFun 24

noncomputable abbrev rescaleNeg : PowerSeries ℂ →+* PowerSeries ℂ := PowerSeries.rescale (-1 : ℂ)

/-- `G(x) = x³ ∏(1-x^{2n})^{48} (∏(1-xⁿ)^{-24} - ∏(1-(-x)ⁿ)^{-24})` (an even series). -/
noncomputable def Gser : PowerSeries ℂ := X ^ 3 * (expandTwo deltaProd) ^ 2 * (P24 - rescaleNeg P24)

/-- The compression `H(q) = G(q^{1/2})`. -/
noncomputable def Hser : PowerSeries ℂ := PowerSeries.mk fun n => coeff (2 * n) Gser

/-- The formal `q`-expansion of `Φ = Δ²(Δ(2τ)⁻¹ + 2¹² Δ(τ/2)⁻¹ + 2¹² Δ((τ+1)/2)⁻¹)`. -/
noncomputable def phiSeries : PowerSeries ℂ := deltaProd ^ 2 * expandTwo P24 + (4096 : ℂ) • Hser

theorem rescaleNeg_expand (f : PowerSeries ℂ) : rescaleNeg (expandTwo f) = expandTwo f := by
  ext n
  rw [coeff_rescale, coeff_expand]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h; rw [pow_mul]; norm_num
  · rw [mul_zero]

theorem rescaleNeg_rescaleNeg (f : PowerSeries ℂ) : rescaleNeg (rescaleNeg f) = f := by
  rw [rescale_rescale]; norm_num

theorem rescaleNeg_X : rescaleNeg X = -X := by
  rw [rescale_X]; simp

theorem rescaleNeg_Gser : rescaleNeg Gser = Gser := by
  simp only [Gser, map_mul, map_pow, map_sub, rescaleNeg_expand, rescaleNeg_rescaleNeg, rescaleNeg_X]
  ring

theorem coeff_Gser_odd {n : ℕ} (hn : Odd n) : coeff n Gser = 0 := by
  have h := congrArg (coeff n) rescaleNeg_Gser
  rw [coeff_rescale, hn.neg_one_pow] at h
  linear_combination -h / 2

theorem expand_Hser : expandTwo Hser = Gser := by
  ext n
  rw [coeff_expand]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    simp [Hser]
  · exact (coeff_Gser_odd (Nat.odd_iff.mpr (by omega))).symm

theorem expand_injective {f g : PowerSeries ℂ} (h : expandTwo f = expandTwo g) : f = g := by
  ext m
  have := congrArg (coeff (2 * m)) h
  rwa [coeff_expand_mul, coeff_expand_mul] at this

theorem deltaProd_mul_fock : deltaProd * P24 = 1 := by
  rw [← deltaOverQ_eq_deltaProd]; exact deltaProductIdentity

theorem expand_deltaProd_mul_expand_fock : expandTwo deltaProd * expandTwo P24 = 1 := by
  rw [← map_mul, deltaProd_mul_fock, map_one]

theorem deltaProd_mul_expand_fock : deltaProd * expandTwo P24 = LatGen.fockSignedGenFun 24 := by
  calc deltaProd * expandTwo P24 = LatGen.fockSignedGenFun 24 * (expandTwo deltaProd * expandTwo P24) := by
        rw [← mul_assoc, fockSigned_mul_expand_deltaProd]
    _ = _ := by rw [expand_deltaProd_mul_expand_fock, mul_one]

theorem expand_deltaProd_mul_fock : expandTwo deltaProd * P24 = TwistedSector.twGenFun 24 := by
  conv_lhs => rw [fock_eq_tw_mul_expand]
  rw [mul_left_comm, expand_deltaProd_mul_expand_fock, mul_one]

theorem coeff_tw_sub (d : ℕ) :
    coeff d (TwistedSector.twGenFun 24 - rescaleNeg (TwistedSector.twGenFun 24))
      = (1 - (-1) ^ d) * (TwistedSector.twCount 24 d : ℂ) := by
  rw [map_sub, coeff_rescale, TwistedSector.twGenFun, coeff_mk]; ring

theorem Hser_mul_fock : Hser * P24 = (2 : ℂ) • (X ^ 2 * twOddSeries) := by
  apply expand_injective
  have hE : expandTwo (Hser * P24) = X ^ 3 * (TwistedSector.twGenFun 24 - rescaleNeg (TwistedSector.twGenFun 24)) := by
    rw [map_mul, expand_Hser, Gser]
    have h1 : X ^ 3 * expandTwo deltaProd ^ 2 * (P24 - rescaleNeg P24) * expandTwo P24
        = X ^ 3 * (expandTwo deltaProd * P24 - rescaleNeg (expandTwo deltaProd * P24)) * (expandTwo deltaProd * expandTwo P24) := by
      rw [map_mul, rescaleNeg_expand]; ring
    rw [h1, expand_deltaProd_mul_expand_fock, mul_one, expand_deltaProd_mul_fock]
  rw [hE]
  ext n
  rw [coeff_expand, coeff_X_pow_mul']
  split_ifs with h1 h2 h2
  · obtain ⟨m, rfl⟩ := h2
    rw [coeff_tw_sub, Nat.mul_div_cancel_left _ two_pos, coeff_smul, coeff_X_pow_mul']
    rw [if_pos (by omega), twOddSeries, coeff_mk, smul_eq_mul]
    have hodd : Odd (2 * m - 3) := ⟨m - 2, by omega⟩
    rw [hodd.neg_one_pow, show 2 * (m - 2) + 1 = 2 * m - 3 by omega]
    ring
  · rw [coeff_tw_sub, (Nat.even_iff.mpr (by omega) : Even (n - 3)).neg_one_pow]; ring
  · obtain ⟨m, rfl⟩ := h2
    rw [Nat.mul_div_cancel_left _ two_pos, coeff_smul, coeff_X_pow_mul', if_neg (by omega),
      smul_zero]
  · rfl

/-- `Φ · ∏(1-qⁿ)^{-24} = ∏(1+qⁿ)^{-24} + 2¹³ q² T_odd`. -/
theorem phiSeries_mul_fock :
    phiSeries * P24 = LatGen.fockSignedGenFun 24 + (8192 : ℂ) • (X ^ 2 * twOddSeries) := by
  have h : deltaProd ^ 2 * expandTwo P24 * P24 = deltaProd * expandTwo P24 * (deltaProd * P24) := by ring
  rw [phiSeries, add_mul, h, deltaProd_mul_fock, mul_one, deltaProd_mul_expand_fock, smul_mul_assoc,
    Hser_mul_fock, smul_smul]
  norm_num

/-- The level-two identity follows from `Φ = E₄³ - 768Δ`. -/
theorem levelTwoIdentity_of_phiSeries (h : phiSeries = E4Series ^ 3 - (768 : ℂ) • deltaSeries) :
    LevelTwoIdentity := by
  unfold LevelTwoIdentity
  rw [← phiSeries_mul_fock, h, sub_mul, jShift_eq, deltaSeries_eq_X_mul_deltaProd, smul_mul_assoc,
    mul_assoc, deltaProd_mul_fock, mul_one]

/-! ## Evaluation -/

/-- Absolute convergence of `Σ [Xⁿ]f · xⁿ`. -/
def AbsSumAt (f : PowerSeries ℂ) (x : ℂ) : Prop := Summable fun n => ‖coeff n f * x ^ n‖

theorem AbsSumAt.add {f g : PowerSeries ℂ} {x : ℂ} (hf : AbsSumAt f x) (hg : AbsSumAt g x) :
    AbsSumAt (f + g) x ∧ ev (f + g) x = ev f x + ev g x := by
  have hfg : Summable fun n => ‖coeff n f * x ^ n‖ + ‖coeff n g * x ^ n‖ :=
    Summable.add (f := fun n => ‖coeff n f * x ^ n‖) hf hg
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hfg, ?_⟩
  · rw [map_add, add_mul]; exact norm_add_le _ _
  · unfold ev; rw [← Summable.tsum_add (Summable.of_norm hf) (Summable.of_norm hg)]
    exact tsum_congr fun n => by rw [map_add, add_mul]

theorem AbsSumAt.smul {f : PowerSeries ℂ} {x : ℂ} (hf : AbsSumAt f x) (c : ℂ) :
    AbsSumAt (c • f) x ∧ ev (c • f) x = c * ev f x := by
  refine ⟨(hf.mul_left ‖c‖).congr fun n => ?_, ?_⟩
  · rw [coeff_smul, smul_eq_mul, mul_assoc, norm_mul]
    simp only [norm_mul]
  · unfold ev; rw [← tsum_mul_left]
    exact tsum_congr fun n => by rw [coeff_smul, smul_eq_mul, mul_assoc]

theorem AbsSumAt.mul {f g : PowerSeries ℂ} {x : ℂ} (hf : AbsSumAt f x) (hg : AbsSumAt g x) :
    AbsSumAt (f * g) x ∧ ev (f * g) x = ev f x * ev g x :=
  ⟨summable_norm_mul hf hg, ev_mul hf hg⟩

theorem AbsSumAt.pow {f : PowerSeries ℂ} {x : ℂ} (hf : AbsSumAt f x) (m : ℕ) :
    AbsSumAt (f ^ m) x ∧ ev (f ^ m) x = ev f x ^ m := ev_pow hf m

theorem SN_X_pow (k : ℕ) (x : ℂ) : AbsSumAt (X ^ k) x ∧ ev (X ^ k) x = x ^ k := by
  have hz : ∀ n ∉ ({k} : Finset ℕ), coeff n (X ^ k : PowerSeries ℂ) * x ^ n = 0 := fun n hn => by
    rw [coeff_X_pow, if_neg (by simpa using hn), zero_mul]
  refine ⟨summable_of_ne_finset_zero (s := {k}) fun n hn => by rw [hz n hn, norm_zero], ?_⟩
  rw [ev, tsum_eq_sum hz, Finset.sum_singleton, coeff_X_pow, if_pos rfl, one_mul]

theorem SN_expand {f : PowerSeries ℂ} {x : ℂ} (hf : AbsSumAt f (x ^ 2)) :
    AbsSumAt (expandTwo f) x ∧ ev (expandTwo f) x = ev f (x ^ 2) := by
  have hinj : Function.Injective fun m : ℕ => 2 * m := fun a b h => by simpa using h
  have hcomp : ∀ m, coeff (2 * m) (expandTwo f) * x ^ (2 * m) = coeff m f * (x ^ 2) ^ m := fun m => by
    rw [coeff_expand_mul, pow_mul]
  have hzero : ∀ n ∉ Set.range (fun m : ℕ => 2 * m), coeff n (expandTwo f) * x ^ n = 0 := fun n hn => by
    rw [coeff_expand_of_not_dvd, zero_mul]
    rintro ⟨m, rfl⟩; exact hn ⟨m, rfl⟩
  constructor
  · rw [AbsSumAt, ← hinj.summable_iff (fun n hn => by rw [hzero n hn, norm_zero])]
    exact hf.congr fun m => by simp only [Function.comp_apply, hcomp]
  · rw [ev, ← hinj.tsum_eq (fun n hn => by
      by_contra h; exact hn (hzero n h))]
    exact tsum_congr hcomp

theorem SN_rescale {f : PowerSeries ℂ} {a x : ℂ} (hf : AbsSumAt f (a * x)) :
    AbsSumAt (PowerSeries.rescale a f) x ∧ ev (PowerSeries.rescale a f) x = ev f (a * x) := by
  have h : ∀ n, coeff n (PowerSeries.rescale a f) * x ^ n = coeff n f * (a * x) ^ n := fun n => by
    rw [coeff_rescale, mul_pow]; ring
  exact ⟨hf.congr fun n => by rw [h], tsum_congr h⟩

theorem SN_Hser {x : ℂ} (hG : AbsSumAt Gser x) : AbsSumAt Hser (x ^ 2) ∧ ev Hser (x ^ 2) = ev Gser x := by
  have hinj : Function.Injective fun m : ℕ => 2 * m := fun a b h => by simpa using h
  have hs : AbsSumAt Hser (x ^ 2) := by
    have := hG.comp_injective hinj
    refine this.congr fun m => ?_
    simp only [Function.comp_apply, Hser, coeff_mk, pow_mul]
  refine ⟨hs, ?_⟩
  rw [← (SN_expand hs).2, expand_Hser]


/-! ## §4  `Φ` evaluated -/

local notation "𝕢" => Function.Periodic.qParam

theorem SN_deltaProd {x : ℂ} (hx : ‖x‖ < 1) : AbsSumAt deltaProd x :=
  (tendsto_ev_one_sub_pow (e := fun i => i + 1) (fun _ => le_rfl) 24 coeff_deltaProd hx).1

theorem ev_deltaProd {x : ℂ} (hx : ‖x‖ < 1) : ev deltaProd x = ∏' n : ℕ, (1 - x ^ (n + 1)) ^ 24 :=
  (hasSum_deltaProd hx).tsum_eq

theorem coeff_fock_geom (n : ℕ) :
    coeff n P24 = coeff n (∏ i ∈ Finset.range n, (geom ℂ (i + 1)) ^ 24) := by
  have h := LatGen.hasProd_fockGenFun 24
  have hg : ∀ i : ℕ, ((1 : PowerSeries ℂ) - X ^ (i + 1))⁻¹ = geom ℂ (i + 1) := fun i =>
    ((PowerSeries.eq_inv_iff_mul_eq_one (by simp)).mpr (geom_mul_one_sub ℂ (Nat.succ_pos i))).symm
  simp_rw [hg] at h
  exact coeff_of_hasProd h (fun _ => dvd_sub_one_pow (dvd_geom_sub_one ℂ le_rfl) 24) n

theorem SN_fock {x : ℂ} (hx : ‖x‖ < 1) : AbsSumAt P24 x :=
  (tendsto_ev_geom_pow (e := fun i => i + 1) (fun _ => le_rfl) 24 coeff_fock_geom hx).1

theorem ev_fock_mul_ev_deltaProd {x : ℂ} (hx : ‖x‖ < 1) : ev P24 x * ev deltaProd x = 1 := by
  rw [← ev_mul (SN_fock hx) (SN_deltaProd hx), mul_comm, deltaProd_mul_fock, ev_one]

theorem discriminant_eq_ev (w : ℍ) : Δ w = 𝕢 1 (w : ℂ) * ev deltaProd (𝕢 1 (w : ℂ)) := by
  have hq : ‖𝕢 1 (w : ℂ)‖ < 1 := by simpa using UpperHalfPlane.norm_qParam_lt_one 1 w
  rw [discriminant_eq_q_prod, ev_deltaProd hq]

theorem qParam_affH (a b : ℝ) (ha : 0 < a) (z : ℍ) :
    𝕢 1 ((affH a b ha z : ℍ) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * (a * z + b)) := by
  simp [Function.Periodic.qParam, coe_affH]

theorem norm_qParam_lt (w : ℍ) : ‖𝕢 1 (w : ℂ)‖ < 1 := by
  simpa using UpperHalfPlane.norm_qParam_lt_one 1 w

/-- **`Φ(τ)` is the evaluation of the formal series `phiSeries` at `q = e^{2πiτ}`.** -/
theorem phiFun_eq_ev (z : ℍ) : AbsSumAt phiSeries (𝕢 1 (z : ℂ)) ∧ phiFun z = ev phiSeries (𝕢 1 (z : ℂ)) := by
  set q := 𝕢 1 (z : ℂ) with hqdef
  set x := 𝕢 1 ((hlfH z : ℍ) : ℂ) with hxdef
  have hq : ‖q‖ < 1 := norm_qParam_lt z
  have hx : ‖x‖ < 1 := norm_qParam_lt (hlfH z)
  have hmx : ‖-x‖ < 1 := by rwa [norm_neg]
  have hxq : x ^ 2 = q := by
    rw [hxdef, hqdef, qParam_affH, Function.Periodic.qParam, sq, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hq2 : 𝕢 1 ((dblH z : ℍ) : ℂ) = q ^ 2 := by
    rw [hqdef, qParam_affH, Function.Periodic.qParam, sq, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hx1 : 𝕢 1 ((hlf1H z : ℍ) : ℂ) = -x := by
    rw [hxdef, qParam_affH, qParam_affH]
    have : 2 * (Real.pi : ℂ) * Complex.I * (((1 / 2 : ℝ) : ℂ) * z + ((1 / 2 : ℝ) : ℂ))
        = 2 * Real.pi * Complex.I * (((1 / 2 : ℝ) : ℂ) * z + ((0 : ℝ) : ℂ)) + Real.pi * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_pi_mul_I]; ring
  have hq2n : ‖q ^ 2‖ < 1 := by rw [← hq2]; exact norm_qParam_lt (dblH z)
  -- the formal pieces
  have sD := SN_deltaProd hq
  have sP2 := SN_fock hq2n
  have sE2P := SN_expand (x := q) sP2
  have sD2 := sD.pow 2
  have sT1 := sD2.1.mul sE2P.1
  have sDx2 : AbsSumAt deltaProd (x ^ 2) := by rw [hxq]; exact sD
  have sE2D := SN_expand (x := x) sDx2
  have sE2D2 := sE2D.1.pow 2
  have sPx := SN_fock hx
  have sR1 : AbsSumAt (rescaleNeg P24) x ∧ ev (rescaleNeg P24) x = ev P24 (-1 * x) :=
    SN_rescale (by rw [neg_one_mul]; exact SN_fock hmx)
  have sdiff := sPx.add (sR1.1.smul (-1)).1
  have sX3 := SN_X_pow 3 x
  have sG1 := sX3.1.mul sE2D2.1
  have sG := sG1.1.mul sdiff.1
  have hGeq : Gser = X ^ 3 * (expandTwo deltaProd) ^ 2 * (P24 + (-1 : ℂ) • rescaleNeg P24) := by
    rw [Gser, neg_one_smul, ← sub_eq_add_neg]
  have sGser : AbsSumAt Gser x := by rw [hGeq]; exact sG.1
  have sH := SN_Hser sGser
  have sHq : AbsSumAt Hser q := by rw [← hxq]; exact sH.1
  have sH4 := sHq.smul 4096
  have sPhi := sT1.1.add sH4.1
  refine ⟨sPhi.1, ?_⟩
  -- values
  have evPhi : ev phiSeries q = (ev deltaProd q) ^ 2 * ev P24 (q ^ 2)
      + 4096 * (x ^ 3 * (ev deltaProd q) ^ 2 * (ev P24 x - ev P24 (-x))) := by
    rw [phiSeries, sPhi.2, sH4.2, sT1.2, sD2.2, sE2P.2]
    congr 2
    rw [← hxq, sH.2, hGeq, sG.2, sG1.2, sX3.2, sE2D2.2, sE2D.2, sdiff.2, (sR1.1.smul (-1)).2,
      sR1.2, neg_one_mul]
    ring_nf
  rw [evPhi, phiFun, discriminant_eq_ev z, discriminant_eq_ev (dblH z), discriminant_eq_ev (hlfH z),
    discriminant_eq_ev (hlf1H z), ← hqdef, ← hxdef, hq2, hx1]
  have e1 := ev_fock_mul_ev_deltaProd hq2n
  have e2 := ev_fock_mul_ev_deltaProd hx
  have e3 := ev_fock_mul_ev_deltaProd hmx
  have hx0 : x ≠ 0 := Complex.exp_ne_zero _
  have hb : ev deltaProd (q ^ 2) ≠ 0 := right_ne_zero_of_mul_eq_one e1
  have hc : ev deltaProd x ≠ 0 := right_ne_zero_of_mul_eq_one e2
  have hd : ev deltaProd (-x) ≠ 0 := right_ne_zero_of_mul_eq_one e3
  rw [eq_inv_of_mul_eq_one_left e1, eq_inv_of_mul_eq_one_left e2, eq_inv_of_mul_eq_one_left e3,
    ← hxq]
  field_simp
  ring

/-- **`qExpansion Φ = phiSeries`.** -/
theorem qExpansion_phiForm : qExpansion 1 (phiForm : ℍ → ℂ) = phiSeries := by
  ext m
  refine (ModularFormClass.qExpansion_coeff_unique (h := 1) (Γ := 𝒮ℒ) one_pos
    one_mem_strictPeriods_SL (f := phiForm) (c := fun m => coeff m phiSeries) (fun τ => ?_) m).symm
  obtain ⟨hs, he⟩ := phiFun_eq_ev τ
  have : phiForm τ = phiFun τ := rfl
  rw [this, he]
  simpa only [smul_eq_mul] using hs.of_norm.hasSum

theorem coeff_one_one_sub_X_pow (n : ℕ) :
    coeff 1 (((1 : PowerSeries ℂ) - X) ^ n) = -(n : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, coeff_one_mul', ih, map_pow]
    simp [coeff_one, coeff_X]

theorem coeff_deltaProd_zero_one :
    coeff 0 deltaProd = 1 ∧ coeff 1 deltaProd = -24 := by
  refine ⟨?_, ?_⟩
  · rw [coeff_deltaProd 0]; simp
  · rw [coeff_deltaProd 1]
    simp only [Finset.range_one, Finset.prod_singleton, zero_add, pow_one]
    rw [coeff_one_one_sub_X_pow]; norm_num

theorem phiSeries_coeff_zero_one : coeff 0 phiSeries = 1 ∧ coeff 1 phiSeries = -48 := by
  obtain ⟨d0, d1⟩ := coeff_deltaProd_zero_one
  have hH0 : coeff 0 Hser = 0 := by
    rw [Hser, coeff_mk, Gser, mul_assoc, coeff_X_pow_mul', if_neg (by omega)]
  have hH1 : coeff 1 Hser = 0 := by
    rw [Hser, coeff_mk, Gser, mul_assoc, coeff_X_pow_mul', if_neg (by omega)]
  have hE0 : coeff 0 (expandTwo P24) = 1 := by
    rw [show (0 : ℕ) = 2 * 0 from rfl, coeff_expand_mul]
    simp [LatGen.fockGenFun, LatGen.fockCount_zero]
  have hE1 : coeff 1 (expandTwo P24) = 0 := coeff_expand_of_not_dvd _ _ _ (by decide)
  constructor
  · rw [phiSeries, map_add, coeff_smul, hH0, smul_zero, add_zero, sq,
      ModularForm.coeff_zero_mul, ModularForm.coeff_zero_mul, d0, hE0]; norm_num
  · rw [phiSeries, map_add, coeff_smul, hH1, smul_zero, add_zero, sq,
      ModularForm.coeff_one_mul, ModularForm.coeff_zero_mul, ModularForm.coeff_one_mul, d0, d1,
      hE0, hE1]; norm_num

/-- **`Φ = E₄³ - 768Δ`** as formal `q`-series: `Φ` is a level-one weight-12 form with
`q`-expansion `1 - 48q + ⋯`. -/
theorem phiSeries_eq : phiSeries = E4Series ^ 3 - (768 : ℂ) • deltaSeries := by
  set g : ModularForm 𝒮ℒ ((12 : ℕ) : ℤ) := ModularForm.mcast (by norm_num) phiForm with hg
  have hqg : qExpansion 1 (g : ℍ → ℂ) = phiSeries := by
    rw [hg, ModularForm.qExpansion_mcast, qExpansion_phiForm]
  have h := qExpansion_weight_twelve g
  rw [hqg, phiSeries_coeff_zero_one.1, phiSeries_coeff_zero_one.2] at h
  rw [h, deltaSeries]
  ext n
  simp only [map_add, coeff_smul, smul_eq_mul, map_sub]
  ring

/-- **`LevelTwoIdentity`**: `∏(1+qⁿ)^{-24} + 2¹³ q² T_odd = q·j - 768 q`. -/
theorem levelTwoIdentity : LevelTwoIdentity :=
  levelTwoIdentity_of_phiSeries phiSeries_eq

end Moonshine

end VOA
