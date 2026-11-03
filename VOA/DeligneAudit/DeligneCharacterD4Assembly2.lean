/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Assembly

/-!
# Assembly of the D₄ recursion (layer 7, part 2): laws in `S` and the `x`-symmetries of `M`
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4K

open PowerSeries

noncomputable section

/-- `x²`. -/
def xx2 : R := mon ((2 : ℤ) • xv) 1

/-- `ι : x ↦ x⁻¹` on `S`. -/
def iotaS : S →+* S := PowerSeries.map (domHom negX : R →+* R)

/-- `τ_q : x ↦ qx` on `S`. -/
def tauQ : S →+* S := PowerSeries.map (twist chiX qq qq_ne_zero : R →+* R)

/-- `τ_r : x ↦ √q x` on `S`. -/
def tauR : S →+* S := PowerSeries.map (twist chiX rr rr_ne_zero : R →+* R)

theorem coeff_C_mul_map (a : R) (φ : R →+* R) (F : S) (n : ℕ) :
    coeff n (C a * PowerSeries.map φ F) = a * φ (coeff n F) := by
  rw [coeff_C_mul, coeff_map]

/-- `Θ = (1-x²)Θ'` in `S`. -/
theorem smap_ctTheta_eq (F : S) : smap ctTheta F = smap ctThetaP (C (1 - xx2) * F) := by
  ext n : 1
  rw [coeff_smap, coeff_smap, coeff_C_mul, ctTheta_eq]
  rfl

/-- Inversion in `S`. -/
theorem smap_ctThetaP_inv (F : S) :
    smap ctThetaP F = smap ctThetaP (C (mon ((2 : ℤ) • xv) (-1)) * iotaS F) := by
  ext n : 1
  rw [coeff_smap, coeff_smap, iotaS, coeff_C_mul_map, ctThetaP_inv]
  rfl

/-- The `q`-shift in `S`. -/
theorem smap_ctThetaP_qshift (F : S) :
    smap ctThetaP F = smap ctThetaP (C (mon ((-4 : ℤ) • xv) (qq ^ (-3 : ℤ))) * tauQ F) := by
  ext n : 1
  rw [coeff_smap, coeff_smap, tauQ, coeff_C_mul_map, ctThetaP_qshift]
  rfl

/-- The half shift in `S`. -/
theorem smap_ctTheta_half (F : S) :
    smap ctTheta F = smap ctThetaP (C (1 - mon ((-2 : ℤ) • xv) qq⁻¹) * tauR F) := by
  ext n : 1
  rw [coeff_smap, coeff_smap, tauR, coeff_C_mul_map, ctTheta_half]
  rfl

/-! ## Symmetries of the factors -/

theorem map_twist_one_sub_smul (χ : V →+ ℤ) (b : Kq) (hb : b ≠ 0) (v : V) (c : Kq) (k : ℕ) :
    PowerSeries.map (twist χ b hb : R →+* R) (1 - mon v c • X ^ k) =
      1 - mon v (b ^ χ v * c) • X ^ k := by
  rw [smul_eq_C_mul, smul_eq_C_mul, map_sub, map_one, map_mul, map_C, map_pow, map_X]
  rw [show ((twist χ b hb : R →+* R) (mon v c)) = mon v (b ^ χ v * c) from twist_mon χ b hb v c]

theorem negX_two : negX (2 • xv) = (-2 : ℤ) • xv := by decide
theorem negX_neg_two : negX ((-2 : ℤ) • xv) = 2 • xv := by decide

theorem hyperVecs_perm_negX : (hyperVecs.map negX).Perm hyperVecs := by decide

theorem iotaS_kernelM : iotaS kernelM = kernelM := by
  rw [iotaS, kernelM, tFactors, hyperFactors_eq, map_mul, map_mul, map_mul, map_domHom_EPos,
    map_domHom_EPos, map_domHom_EPos, map_zero, negX_two, negX_neg_two]
  have hh : PowerSeries.map (domHom negX : R →+* R) (prodE hyperVecs fun _ => 1) =
      prodE hyperVecs fun _ => 1 := by
    unfold prodE
    rw [map_list_prod, List.map_map]
    have : (fun v => PowerSeries.map (domHom negX : R →+* R) (EInv 1 v 1 one_ne_zero)) =
        fun v => EInv 1 (negX v) 1 one_ne_zero := by
      funext v; exact map_domHom_EInv _ _ _ _ _
    simp only [Function.comp_def]
    rw [this, show (hyperVecs.map fun x => EInv 1 (negX x) 1 one_ne_zero) =
      (hyperVecs.map negX).map (fun v => EInv 1 v 1 one_ne_zero) by rw [List.map_map]; rfl]
    exact (hyperVecs_perm_negX.map _).prod_eq
  rw [hh]
  ring

theorem hyperHalf_negX : (hyperHalf 1).map negX = hyperHalf (-1) := by decide

theorem iotaS_Pplus : iotaS PplusS = PminusS := by
  rw [iotaS, PplusS, PminusS, prodLin, prodLin, map_list_prod, List.map_map, ← hyperHalf_negX,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro v _
  simp only [Function.comp_apply]
  exact map_domHom_one_sub_smul negX v 1 1

theorem iotaS_Dp : iotaS Dp = Dm := by
  rw [iotaS, Dp, Dm, map_mul, map_domHom_one_sub_smul, map_domHom_one_sub_smul, negX_two]

theorem iotaS_T1 : iotaS (1 - mon 0 1 • X ^ 2) = 1 - mon 0 1 • X ^ 2 := by
  rw [iotaS, map_domHom_one_sub_smul, map_zero]

theorem tauQ_T1 : tauQ (1 - mon 0 1 • X ^ 2) = 1 - mon 0 1 • X ^ 2 := by
  rw [tauQ, map_twist_one_sub_smul, map_zero, zpow_zero, one_mul]

theorem tauQ_Dm : tauQ Dm = (1 - mon ((-2 : ℤ) • xv) (qq ^ (-2 : ℤ)) • X ^ 2) *
    (1 - mon ((-2 : ℤ) • xv) (qq ^ (-1 : ℤ)) • X ^ 2) := by
  have h : chiX ((-2 : ℤ) • xv) = -2 := by decide
  rw [tauQ, Dm, map_mul, map_twist_one_sub_smul, map_twist_one_sub_smul, h, mul_one]
  congr 3
  rw [← zpow_add_one₀ qq_ne_zero]; norm_num

theorem tauQ_Pminus : tauQ PminusS = (hyperVecs.map xShiftDen).prod := by
  rw [tauQ, PminusS, prodLin, map_list_prod, List.map_map, hyperVecs_eq, List.map_append,
    List.prod_append]
  have h1 : ((hyperHalf 1).map xShiftDen).prod = 1 := by
    rw [List.prod_eq_one]
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    rw [xShiftDen, if_neg (by rw [chiX_hyperHalf 1 v hv]; decide)]
  rw [h1, one_mul]
  congr 1
  apply List.map_congr_left
  intro v hv
  simp only [Function.comp_apply]
  rw [map_twist_one_sub_smul, xShiftDen, if_pos (chiX_hyperHalf (-1) v hv),
    chiX_hyperHalf (-1) v hv, zpow_neg_one, mul_one]

theorem Pplus_xShiftNum : PplusS = (hyperVecs.map xShiftNum).prod := by
  rw [PplusS, prodLin, hyperVecs_eq, List.map_append, List.prod_append]
  have h1 : ((hyperHalf (-1)).map xShiftNum).prod = 1 := by
    rw [List.prod_eq_one]
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    rw [xShiftNum, if_neg (by rw [chiX_hyperHalf (-1) v hv]; decide)]
  rw [h1, mul_one]
  congr 1

/-! ## The half-shifted kernel `A = H(M)` -/

/-- `A = M(√q s, √q x)`. -/
def Ahalf : S := rescale (algebraMap Kq R rr) (tauR kernelM)

/-- `(1-t)`. -/
def T1 : S := 1 - mon 0 1 • X ^ 2

theorem Ahalf_eq : Ahalf * (T1 * Dp) = kernelM * PplusS := halfShift_kernelM

theorem iota_rescale (a : Kq) (F : S) :
    iotaS (rescale (algebraMap Kq R a) F) = rescale (algebraMap Kq R a) (iotaS F) :=
  map_domHom_rescale negX a F

theorem tauQ_rescale (a : Kq) (F : S) :
    tauQ (rescale (algebraMap Kq R a) F) = rescale (algebraMap Kq R a) (tauQ F) := by
  rw [tauQ, ← rescale_map]
  congr 2
  exact (twist chiX qq qq_ne_zero).commutes a

theorem iota_Ahalf_eq : iotaS Ahalf * (T1 * Dm) = kernelM * PminusS := by
  have h := congrArg iotaS Ahalf_eq
  rw [map_mul, map_mul, map_mul, T1, iotaS_T1, iotaS_Dp, iotaS_kernelM, iotaS_Pplus] at h
  exact h

theorem isUnit_of_constantCoeff_one {F : S} (h : constantCoeff F = 1) : IsUnit F := by
  rw [isUnit_iff_constantCoeff, h]; exact isUnit_one

theorem constantCoeff_Dp : constantCoeff Dp = 1 := by
  rw [Dp, map_mul, constantCoeff_one_sub_smul _ _ 2 two_ne_zero,
    constantCoeff_one_sub_smul _ _ 2 two_ne_zero, mul_one]

theorem constantCoeff_T1 : constantCoeff T1 = 1 := constantCoeff_one_sub_smul _ _ 2 two_ne_zero

theorem constantCoeff_tauQDm : constantCoeff (tauQ Dm) = 1 := by
  rw [tauQ_Dm, map_mul, constantCoeff_one_sub_smul _ _ 2 two_ne_zero,
    constantCoeff_one_sub_smul _ _ 2 two_ne_zero, mul_one]

/-- **`τ_q ι A = A`**: the `q`-shift of the inverted half-shifted kernel is the half-shifted kernel. -/
theorem tauQ_iota_Ahalf : tauQ (iotaS Ahalf) = Ahalf := by
  have h1 := congrArg tauQ iota_Ahalf_eq
  rw [map_mul, map_mul, map_mul, T1, tauQ_T1, tauQ_Pminus] at h1
  -- `τ_q(M) D₊ ∏den = M τ_q(D₋) P₊`
  have h2 := xShift_kernelM
  rw [← tauQ, ← tauQ_Dm, ← Pplus_xShiftNum] at h2
  have hDm : IsUnit (tauQ Dm) := isUnit_of_constantCoeff_one constantCoeff_tauQDm
  have hT : IsUnit (T1 * Dp) := (isUnit_of_constantCoeff_one constantCoeff_T1).mul
    (isUnit_of_constantCoeff_one constantCoeff_Dp)
  -- multiply `h1` by `D₊`
  have h3 : tauQ (iotaS Ahalf) * (T1 * Dp) * tauQ Dm = Ahalf * (T1 * Dp) * tauQ Dm := by
    calc tauQ (iotaS Ahalf) * (T1 * Dp) * tauQ Dm
        = (tauQ (iotaS Ahalf) * ((1 - mon 0 1 • X ^ 2) * tauQ Dm)) * Dp := by rw [T1]; ring
      _ = tauQ kernelM * Dp * (hyperVecs.map xShiftDen).prod := by rw [h1]; ring
      _ = kernelM * tauQ Dm * PplusS := h2
      _ = Ahalf * (T1 * Dp) * tauQ Dm := by rw [Ahalf_eq]; ring
  have h4 := hDm.mul_right_cancel h3
  exact hT.mul_right_cancel h4

/-! ## The finite identity in readable form -/

/-- `1 - qt`. -/
def Tq : S := 1 - mon 0 qq • X ^ 2

theorem mon_zero_smul_eq (c : Kq) (F : S) : mon 0 c • F = C (algebraMap Kq R c) * F := by
  rw [smul_eq_C_mul]; rfl

theorem finiteIdentityS' (hF : D4F.D4FiniteIdentity) (Y : S)
    (hY : C (1 - mon thetaV qq⁻¹) * Y = NS) :
    C (1 - xx2) * (C (algebraMap Kq R qq) * X ^ 2) * piThetaS Y =
      C (1 - xx2) * T1 * Tq * Dp * Dm - Tq * (PplusS * Dm - C xx2 * PminusS * Dp) := by
  have h := finiteIdentityS hF Y hY
  have v0 : vecOf (D4F.ev [0, 0, 2, 0, 0, 0, 0]) = (2 : ℤ) • xv := by decide
  have v1 : vecOf (D4F.ev [1, 2, 0, 0, 0, 0, 0]) = 0 := by decide
  have v2 : vecOf (D4F.ev [0, 2, 0, 0, 0, 0, 0]) = 0 := by decide
  have v3 : vecOf (D4F.ev [1, 2, 2, 0, 0, 0, 0]) = 2 • xv := by decide
  have v4 : vecOf (D4F.ev [0, 2, 2, 0, 0, 0, 0]) = 2 • xv := by decide
  have v5 : vecOf (D4F.ev [0, 2, -2, 0, 0, 0, 0]) = (-2 : ℤ) • xv := by decide
  have v6 : vecOf (D4F.ev [1, 2, -2, 0, 0, 0, 0]) = (-2 : ℤ) • xv := by decide
  simp only [linOf, v0, v1, v2, v3, v4, v5, v6] at h
  simp only [show ([0, 0, 2, 0, 0, 0, 0] : List ℤ).getD 0 0 = 0 from rfl,
    show ([0, 0, 2, 0, 0, 0, 0] : List ℤ).getD 1 0 = 0 from rfl,
    show ([1, 2, 0, 0, 0, 0, 0] : List ℤ).getD 0 0 = 1 from rfl,
    show ([1, 2, 0, 0, 0, 0, 0] : List ℤ).getD 1 0 = 2 from rfl,
    show ([0, 2, 0, 0, 0, 0, 0] : List ℤ).getD 0 0 = 0 from rfl,
    show ([0, 2, 0, 0, 0, 0, 0] : List ℤ).getD 1 0 = 2 from rfl,
    show ([0, 2, 2, 0, 0, 0, 0] : List ℤ).getD 0 0 = 0 from rfl,
    show ([0, 2, 2, 0, 0, 0, 0] : List ℤ).getD 1 0 = 2 from rfl,
    show ([1, 2, 2, 0, 0, 0, 0] : List ℤ).getD 0 0 = 1 from rfl,
    show ([1, 2, 2, 0, 0, 0, 0] : List ℤ).getD 1 0 = 2 from rfl,
    show ([0, 2, -2, 0, 0, 0, 0] : List ℤ).getD 0 0 = 0 from rfl,
    show ([0, 2, -2, 0, 0, 0, 0] : List ℤ).getD 1 0 = 2 from rfl,
    show ([1, 2, -2, 0, 0, 0, 0] : List ℤ).getD 0 0 = 1 from rfl,
    show ([1, 2, -2, 0, 0, 0, 0] : List ℤ).getD 1 0 = 2 from rfl,
    zpow_zero, zpow_one, show (2 : ℤ).toNat = 2 from rfl, show (0 : ℤ).toNat = 0 from rfl,
    pow_zero] at h
  rw [T1, Tq, Dp, Dm, xx2]
  rw [mon_zero_smul_eq] at h
  simp only [smul_eq_C_mul, mul_one] at h ⊢
  rw [show (C (mon 0 qq) : S) = C (algebraMap Kq R qq) from rfl, map_sub, map_one]
  linear_combination h

/-! ## The recursion `I(t) - I(qt) = tq B I(q²t)` -/

/-- `2 I(t, z) = CT_x Θ(x) M(s, x, z)`. -/
def Ikernel : S := smap ctTheta kernelM

theorem smap_neg (ℓ : R →ₗ[Kq] R) (F : S) : smap ℓ (-F) = -smap ℓ F := by
  ext n : 1; simp [coeff_smap]

theorem smap_C_mul_C (a b : R) (F : S) :
    C a * (C b * F) = C (a * b) * F := by rw [map_mul, mul_assoc]

theorem tauR_rescale (a : Kq) (F : S) :
    tauR (rescale (algebraMap Kq R a) F) = rescale (algebraMap Kq R a) (tauR F) := by
  rw [tauR, ← rescale_map]
  congr 2
  exact (twist chiX rr rr_ne_zero).commutes a

theorem tauQ_C (a : R) : tauQ (C a) = C (twist chiX qq qq_ne_zero a) := map_C _ _

/-- **The D₄ recursion**, conditional only on `D4F.D4FiniteIdentity`. -/
theorem Ikernel_recursion (hF : D4F.D4FiniteIdentity) :
    Ikernel - rescale (algebraMap Kq R rr) Ikernel =
      C (algebraMap Kq R qq) * X ^ 2 * Bop (rescale (algebraMap Kq R qq) Ikernel) := by
  obtain ⟨Y, hY, hB⟩ := Bop_kernel
  have hF' := finiteIdentityS' hF Y hY
  set Mq := rescale (algebraMap Kq R qq) kernelM with hMq
  set W := kernelM - C (algebraMap Kq R qq) * X ^ 2 * Bop Mq with hW
  -- `(1 - x²) W = A - x² ι A`
  have hden : IsUnit denS := isUnit_denS
  have hclaim : C (1 - xx2) * W = Ahalf - C xx2 * iotaS Ahalf := by
    apply hden.mul_right_cancel
    have hA := Ahalf_eq
    have hι := iota_Ahalf_eq
    rw [hW]
    simp only [denS, Tden, T1, Tq] at hA hι hF' hB ⊢
    linear_combination (-(C (1 - xx2) * (C (algebraMap Kq R qq) * X ^ 2))) * hB +
      (-kernelM) * hF' + (-((1 - mon 0 qq • X ^ 2) * Dm)) * hA +
      (C xx2 * (1 - mon 0 qq • X ^ 2) * Dp) * hι
  -- `CT Θ W = CT Θ' A + CT Θ' A`
  have hinv : smap ctThetaP Ahalf = -smap ctThetaP (C xx2 * iotaS Ahalf) := by
    rw [smap_ctThetaP_inv Ahalf, ← smap_neg, ← neg_mul, ← map_neg]
    congr 3
    exact Finsupp.single_neg _ _
  have hW' : smap ctTheta W = smap ctThetaP Ahalf + smap ctThetaP Ahalf := by
    rw [smap_ctTheta_eq, hclaim, smap_sub]
    nth_rewrite 2 [hinv]
    ring
  -- the half-shifted side
  have hq : smap ctThetaP (C xx2 * iotaS Ahalf) =
      smap ctThetaP (C (mon ((-2 : ℤ) • xv) qq⁻¹) * Ahalf) := by
    have h2 : chiX ((2 : ℤ) • xv) = 2 := by decide
    have hm : mon ((-4 : ℤ) • xv) (qq ^ (-3 : ℤ)) * mon ((2 : ℤ) • xv) (qq ^ chiX ((2 : ℤ) • xv) * 1) =
        mon ((-2 : ℤ) • xv) qq⁻¹ := by
      rw [mon_mul_mon, h2, mul_one, ← zpow_add₀ qq_ne_zero]
      congr 1
      · module
      · norm_num
    rw [smap_ctThetaP_qshift, map_mul, tauQ_iota_Ahalf, tauQ_C, xx2, twist_mon, ← mul_assoc,
      ← map_mul, hm]
  have hhalf : rescale (algebraMap Kq R rr) Ikernel = smap ctThetaP Ahalf + smap ctThetaP Ahalf := by
    rw [Ikernel, ← smap_rescale, smap_ctTheta_half, tauR_rescale, ← Ahalf, map_sub, map_one,
      sub_mul, one_mul, smap_sub, ← hq]
    rw [hinv]
    ring
  -- conclude
  have hBI : Bop (rescale (algebraMap Kq R qq) Ikernel) = smap ctTheta (Bop Mq) := by
    rw [Ikernel, ← smap_rescale, ← hMq, smap_ct_Bop]
  rw [hBI, hhalf, ← hW', hW, smap_sub, mul_assoc, smap_C_mul, smap_X_pow_mul, Ikernel, mul_assoc]
  ring

end

end VOA.DeligneAudit.DeligneCharacter.D4K

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.tauQ_iota_Ahalf
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.Ikernel_recursion
end AxiomAudit
