/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Bstep
import VOA.DeligneAudit.DeligneCharacterD4FiniteStatement

/-!
# From `D4F.D4FiniteIdentity` to the kernel ring (layer 6b)

`D4F.D4FiniteIdentity` is stated in `LP7 = ℤ[q^±, s^±, x^±, z^±]`.  The ring map
`ψ : LP7 → H = HahnSeries ℤ R` sends `q^a s^b x^c z^μ ↦ s^b · q^a x^c z^μ`, and `S = R⟦s⟧` embeds in
`H` by `ofPS` (injective).  Coefficientwise maps `smap ℓ` on `S` correspond to `hmap ℓ` on `H`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4K

open PowerSeries

noncomputable section

/-- Laurent series in `s` over `R`. -/
abbrev H := HahnSeries ℤ R

/-- `S ↪ H`. -/
def ofPS : S →+* H := HahnSeries.ofPowerSeries ℤ R

theorem ofPS_injective : Function.Injective ofPS := HahnSeries.ofPowerSeries_injective

theorem ofPS_coeff_nat (F : S) (n : ℕ) : (ofPS F).coeff (n : ℤ) = coeff n F :=
  HahnSeries.ofPowerSeries_apply_coeff F n

theorem ofPS_coeff_neg (F : S) (g : ℤ) (hg : g < 0) : (ofPS F).coeff g = 0 := by
  rw [ofPS, HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
  rintro ⟨n, hn⟩
  simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk] at hn
  omega

/-- A linear map of `R`, coefficientwise on `H`. -/
def hmap (ℓ : R →ₗ[Kq] R) (h : H) : H := h.map ℓ

theorem hmap_ofPS (ℓ : R →ₗ[Kq] R) (F : S) : hmap ℓ (ofPS F) = ofPS (smap ℓ F) := by
  ext g
  rcases lt_or_ge g 0 with hg | hg
  · rw [hmap, HahnSeries.map_coeff, ofPS_coeff_neg _ _ hg, ofPS_coeff_neg _ _ hg, map_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hg
    rw [hmap, HahnSeries.map_coeff, ofPS_coeff_nat, ofPS_coeff_nat, coeff_smap]

theorem hmap_add (ℓ : R →ₗ[Kq] R) (a b : H) : hmap ℓ (a + b) = hmap ℓ a + hmap ℓ b := by
  ext g; simp [hmap]

theorem hmap_single (ℓ : R →ₗ[Kq] R) (g : ℤ) (r : R) :
    hmap ℓ (HahnSeries.single g r) = HahnSeries.single g (ℓ r) := by
  ext g'
  rw [hmap, HahnSeries.map_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs <;> simp

/-! ## The ring map `ψ : LP7 → H` -/

open VOA.DeligneAudit.DeligneCharacter.D4F in
/-- The `(x, z)`-part of an exponent vector of `LP7`. -/
def vecOf (w : Fin 7 → ℤ) : V := fun j => w ⟨j.val + 2, by omega⟩

theorem vecOf_add (w w' : Fin 7 → ℤ) : vecOf (w + w') = vecOf w + vecOf w' := rfl
theorem vecOf_zero : vecOf 0 = 0 := rfl

/-- `q^a s^b x^c z^μ ↦ s^b · q^a x^c z^μ`. -/
def hmon (w : Fin 7 → ℤ) : H := HahnSeries.single (w 1) (mon (vecOf w) (qq ^ (w 0)))

def psiAux : Multiplicative (Fin 7 → ℤ) →* H where
  toFun w := hmon (Multiplicative.toAdd w)
  map_one' := by
    simp only [toAdd_one, hmon, Pi.zero_apply, zpow_zero, vecOf_zero]
    rfl
  map_mul' w w' := by
    simp only [toAdd_mul, hmon, Pi.add_apply, HahnSeries.single_mul_single, mon_mul_mon,
      vecOf_add, zpow_add₀ qq_ne_zero]

/-- **`ψ : LP7 → H`**. -/
def psi : D4F.LP7 →+* H := (AddMonoidAlgebra.lift ℤ H (Fin 7 → ℤ) psiAux).toRingHom

theorem psi_single (w : Fin 7 → ℤ) (c : ℤ) :
    psi (AddMonoidAlgebra.single w c) = (c : H) * hmon w := by
  rw [psi, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AddMonoidAlgebra.lift_single,
    Algebra.smul_def, eq_intCast]
  rfl

theorem psi_mono (w : Fin 7 → ℤ) : psi (D4F.mono w) = hmon w := by
  rw [D4F.mono, psi_single, Int.cast_one, one_mul]

/-- `hmap ℓ` as an additive map. -/
def hmapAdd (ℓ : R →ₗ[Kq] R) : H →+ H where
  toFun := hmap ℓ
  map_zero' := by ext g; simp [hmap]
  map_add' := hmap_add ℓ

theorem hmap_intCast_mul (ℓ : R →ₗ[Kq] R) (c : ℤ) (h : H) :
    hmap ℓ ((c : H) * h) = (c : H) * hmap ℓ h := by
  rw [← zsmul_eq_mul, ← zsmul_eq_mul]
  exact map_zsmul (hmapAdd ℓ) c h

theorem hmap_neg (ℓ : R →ₗ[Kq] R) (h : H) : hmap ℓ (-h) = -hmap ℓ h :=
  map_neg (hmapAdd ℓ) h

theorem hmap_sum (ℓ : R →ₗ[Kq] R) {ι : Type*} (s : Finset ι) (f : ι → H) :
    hmap ℓ (∑ i ∈ s, f i) = ∑ i ∈ s, hmap ℓ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext g; simp [hmap]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hmap_add, ih]

/-! ## `ψ` intertwines the Demazure operators -/

theorem vecOf_zEmbed (i : Fin 4) : vecOf (D4F.zEmbed (D4F.d4Root i)) = rootV i := by
  fin_cases i <;> decide

theorem zEmbed_zero (r : Fin 4 → ℤ) : D4F.zEmbed r 0 = 0 := rfl
theorem zEmbed_one (r : Fin 4 → ℤ) : D4F.zEmbed r 1 = 0 := rfl

theorem zPair_eq_dotZ (w : Fin 7 → ℤ) (i : Fin 4) :
    D4F.zPair w (D4F.d4Root i) = dotZ (vecOf w) (rootV i) := by
  fin_cases i <;> simp [D4F.zPair, dotZ, vecOf, D4F.d4Root, rootV, zv, Fin.sum_univ_four,
    Pi.single_apply]

theorem hmon_shift (w : Fin 7 → ℤ) (i : Fin 4) (k : ℤ) :
    hmon (w + k • D4F.zEmbed (D4F.d4Root i)) =
      HahnSeries.single (w 1) (mon (vecOf w + k • rootV i) (qq ^ (w 0))) := by
  rw [hmon]
  simp only [Pi.add_apply, Pi.smul_apply, zEmbed_zero, zEmbed_one, smul_zero, add_zero]
  congr 2
  rw [vecOf_add, ← vecOf_zEmbed i]
  rfl

theorem single_sum {ι : Type*} (g : ℤ) (s : Finset ι) (f : ι → R) :
    HahnSeries.single g (∑ i ∈ s, f i) = ∑ i ∈ s, HahnSeries.single g (f i) :=
  map_sum (HahnSeries.single.addMonoidHom g) f s

theorem psi_demazureString (i : Fin 4) (w : Fin 7 → ℤ) :
    psi (D4F.demazureString i w) =
      HahnSeries.single (w 1) (piR (rootV i) (mon (vecOf w) (qq ^ (w 0)))) := by
  rw [piR_mon, D4F.demazureString, piStr]
  simp only [zPair_eq_dotZ]
  split_ifs with hn
  · rw [map_sum, Finset.smul_sum, single_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [psi_mono, sub_eq_add_neg, ← neg_smul, hmon_shift, smul_mon, mul_one, sub_eq_add_neg,
      neg_smul]
  · rw [map_neg, map_sum, smul_neg, Finset.smul_sum, HahnSeries.single_neg, single_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [psi_mono, hmon_shift, smul_mon, mul_one]

theorem psi_zsmul (c : ℤ) (f : D4F.LP7) : psi (c • f) = (c : H) * psi f := by
  rw [map_zsmul, zsmul_eq_mul]

theorem demazurePi_single (i : Fin 4) (w : Fin 7 → ℤ) (c : ℤ) :
    D4F.demazurePi i (AddMonoidAlgebra.single w c) = c • D4F.demazureString i w :=
  Finsupp.linearCombination_single ℤ c w

/-- **`ψ ∘ π_i = π_i ∘ ψ`.** -/
theorem psi_demazurePi (i : Fin 4) (f : D4F.LP7) :
    psi (D4F.demazurePi i f) = hmap (piR (rootV i)) (psi f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero =>
      rw [LinearMap.map_zero, RingHom.map_zero]
      exact ((hmapAdd (piR (rootV i))).map_zero).symm
  | add f g hf hg => rw [LinearMap.map_add, RingHom.map_add, hf, hg, RingHom.map_add, hmap_add]
  | single w c =>
      rw [demazurePi_single, psi_zsmul, psi_demazureString, psi_single, hmap_intCast_mul, hmon,
        hmap_single]

theorem wordTheta_eq : D4F.wordTheta = wordS := rfl

/-- `ψ ∘ π_{s_θ} = π_{s_θ} ∘ ψ`, and on the image of `S` it is `piThetaS`. -/
theorem psi_demazureTheta (G : D4F.LP7) (F : S) (hG : psi G = ofPS F) :
    psi (D4F.demazureTheta G) = ofPS (piThetaS F) := by
  rw [D4F.demazureTheta, piThetaS, wordTheta_eq]
  generalize wordS = w
  induction w generalizing G F with
  | nil => exact hG
  | cons i w ih =>
      simp only [List.foldl_cons]
      apply ih
      rw [psi_demazurePi, hG, hmap_ofPS]

/-! ## Images of the polynomials of `(P)` -/

theorem ofPS_mon_smul (v : V) (c : Kq) (b : ℕ) :
    ofPS (mon v c • X ^ b) = HahnSeries.single (b : ℤ) (mon v c) := by
  rw [smul_eq_C_mul, map_mul, map_pow, ofPS, HahnSeries.ofPowerSeries_C,
    HahnSeries.ofPowerSeries_X, HahnSeries.single_pow, HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add, one_pow, mul_one]
  simp

theorem hmon_ev (l : List ℤ) (hb : 0 ≤ l.getD 1 0) :
    hmon (D4F.ev l) = ofPS (mon (vecOf (D4F.ev l)) (qq ^ l.getD 0 0) • X ^ (l.getD 1 0).toNat) := by
  rw [ofPS_mon_smul, hmon, Int.toNat_of_nonneg hb]
  rfl

theorem psi_oneSub (l : List ℤ) (hb : 0 ≤ l.getD 1 0) :
    psi (D4F.oneSub l) =
      ofPS (1 - mon (vecOf (D4F.ev l)) (qq ^ l.getD 0 0) • X ^ (l.getD 1 0).toNat) := by
  rw [D4F.oneSub, map_sub, map_one, psi_mono, hmon_ev l hb, map_sub, map_one]

/-- A list of exponent vectors with nonnegative `s`-degree, read as factors `1 - c z^v s^b`. -/
def linOf (l : List ℤ) : S := 1 - mon (vecOf (D4F.ev l)) (qq ^ l.getD 0 0) • X ^ (l.getD 1 0).toNat

theorem psi_prodOneSub (fs : List (List ℤ)) (hfs : ∀ l ∈ fs, 0 ≤ l.getD 1 0) :
    psi (D4F.prodOneSub fs) = ofPS ((fs.map linOf).prod) := by
  rw [D4F.prodOneSub, map_list_prod, map_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  exact psi_oneSub l (hfs l hl)

/-- The data `(v, q-exponent, s-degree)` of a factor. -/
def tri (l : List ℤ) : V × ℤ × ℕ := (vecOf (D4F.ev l), l.getD 0 0, (l.getD 1 0).toNat)

def linTriple (t : V × ℤ × ℕ) : S := 1 - mon t.1 (qq ^ t.2.1) • X ^ t.2.2

theorem linOf_eq (l : List ℤ) : linOf l = linTriple (tri l) := rfl

theorem prod_linOf (fs : List (List ℤ)) :
    (fs.map linOf).prod = ((fs.map tri).map linTriple).prod := by
  rw [List.map_map]; rfl

theorem factorsP0_tri : D4F.factorsP0.map tri = hyperVecs.map fun v => (v, 0, 1) := by decide

theorem P0S_eq_list : P0S = (D4F.factorsP0.map linOf).prod := by
  rw [prod_linOf, factorsP0_tri, List.map_map, P0S, prodLin]
  congr 1

theorem factorsPplus_tri :
    (D4F.factorsP0.filter fun l => l.getD 2 0 = 1).map tri = (hyperHalf 1).map fun v => (v, 0, 1) := by
  decide

theorem factorsPminus_tri :
    (D4F.factorsP0.filter fun l => l.getD 2 0 = -1).map tri =
      (hyperHalf (-1)).map fun v => (v, 0, 1) := by
  decide

theorem PplusS_eq_list : PplusS = ((D4F.factorsP0.filter fun l => l.getD 2 0 = 1).map linOf).prod := by
  rw [prod_linOf, factorsPplus_tri, List.map_map, PplusS, prodLin]
  congr 1

theorem PminusS_eq_list :
    PminusS = ((D4F.factorsP0.filter fun l => l.getD 2 0 = -1).map linOf).prod := by
  rw [prod_linOf, factorsPminus_tri, List.map_map, PminusS, prodLin]
  congr 1

/-- The factors of `P_θ` attached to `v`. -/
def thetaTriples (v : V) : List (V × ℤ × ℕ) :=
  if chiTheta v = -1 then [(v, 0, 1), (v, 1, 1)] else if chiTheta v = 1 then [] else [(v, 0, 1)]

theorem pThetaFactor_eq (v : V) : pThetaFactor v = ((thetaTriples v).map linTriple).prod := by
  unfold pThetaFactor thetaTriples
  split_ifs <;> simp [linTriple]

theorem factorsPtheta_tri : D4F.factorsPtheta.map tri = hyperVecs.flatMap thetaTriples := by
  decide

theorem prod_flatMap' (l : List V) (f : V → List S) :
    (l.flatMap f).prod = (l.map fun a => (f a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.prod_append, ih]

theorem PthetaS_eq_list : PthetaS = (D4F.factorsPtheta.map linOf).prod := by
  rw [prod_linOf, factorsPtheta_tri, PthetaS, List.map_flatMap, prod_flatMap']
  congr 1
  apply List.map_congr_left
  intro v _
  exact pThetaFactor_eq v

/-! ## The transfer -/

theorem psi_mono_ev (l : List ℤ) (hb : 0 ≤ l.getD 1 0) :
    psi (D4F.mono (D4F.ev l)) = ofPS (mon (vecOf (D4F.ev l)) (qq ^ l.getD 0 0) • X ^ (l.getD 1 0).toNat) := by
  rw [psi_mono, hmon_ev l hb]

/-- `1 - q⁻¹z^θ` as a factor. -/
theorem linOf_theta : linOf [-1, 0, 0, 1, 1, 0, 0] = C (1 - mon thetaV qq⁻¹) := by
  have hv : vecOf (D4F.ev [-1, 0, 0, 1, 1, 0, 0]) = thetaV := by decide
  rw [linOf, hv]
  simp [smul_eq_C_mul]

theorem vecOf_two_theta : vecOf (D4F.ev [-2, 0, 0, 2, 2, 0, 0]) = (2 : ℤ) • thetaV := by decide

/-- The `S`-side numerator. -/
theorem psi_Nnum : psi D4F.Nnum = ofPS NS := by
  rw [D4F.Nnum, map_sub, map_mul, D4F.P0, D4F.Ptheta, psi_prodOneSub _ (by decide),
    psi_prodOneSub _ (by decide), psi_mono_ev _ (by decide), ← P0S_eq_list, ← PthetaS_eq_list,
    NS, vecOf_two_theta, map_sub, map_mul]
  simp [smul_eq_C_mul]

/-- **Transfer of the finite identity to `S`.** -/
theorem finiteIdentityS (hF : D4F.D4FiniteIdentity) (Y : S)
    (hY : C (1 - mon thetaV qq⁻¹) * Y = NS) :
    linOf [0, 0, 2, 0, 0, 0, 0] * (mon (vecOf (D4F.ev [1, 2, 0, 0, 0, 0, 0])) (qq ^ (1 : ℤ)) • X ^ 2) *
        piThetaS Y =
      linOf [0, 0, 2, 0, 0, 0, 0] * linOf [0, 2, 0, 0, 0, 0, 0] * linOf [1, 2, 0, 0, 0, 0, 0] *
          (linOf [0, 2, 2, 0, 0, 0, 0] * linOf [1, 2, 2, 0, 0, 0, 0]) *
          (linOf [0, 2, -2, 0, 0, 0, 0] * linOf [1, 2, -2, 0, 0, 0, 0]) -
        linOf [1, 2, 0, 0, 0, 0, 0] *
          (PplusS * (linOf [0, 2, -2, 0, 0, 0, 0] * linOf [1, 2, -2, 0, 0, 0, 0]) -
            (mon (vecOf (D4F.ev [0, 0, 2, 0, 0, 0, 0])) (qq ^ (0 : ℤ)) • X ^ 0) * PminusS *
              (linOf [0, 2, 2, 0, 0, 0, 0] * linOf [1, 2, 2, 0, 0, 0, 0])) := by
  obtain ⟨G₀, h1, h2⟩ := hF.holds
  -- `ψ G₀ = Y`
  have hG : psi G₀ = ofPS Y := by
    have e := congrArg psi h1
    rw [map_mul, psi_oneSub _ (by decide), psi_Nnum, ← linOf, linOf_theta, ← hY, map_mul] at e
    have hne : ofPS (C (1 - mon thetaV qq⁻¹)) ≠ 0 := by
      rw [Ne, ← map_zero ofPS, ofPS_injective.eq_iff]
      exact C_one_sub_mon_ne_zero thetaV qq⁻¹ (by decide)
    exact mul_left_cancel₀ hne e
  have e := congrArg psi h2
  apply ofPS_injective
  have po : ∀ l : List ℤ, 0 ≤ l.getD 1 0 → psi (D4F.oneSub l) = ofPS (linOf l) :=
    fun l hl => psi_oneSub l hl
  have pp : psi D4F.Pplus = ofPS PplusS := by
    rw [D4F.Pplus, psi_prodOneSub _ (by decide), ← PplusS_eq_list]
  have pm : psi D4F.Pminus = ofPS PminusS := by
    rw [D4F.Pminus, psi_prodOneSub _ (by decide), ← PminusS_eq_list]
  rw [D4F.Dplus, D4F.Dminus] at e
  simp only [map_mul, map_sub] at e ⊢
  rw [psi_demazureTheta G₀ Y hG, pp, pm, po _ (by decide), po _ (by decide), po _ (by decide),
    po _ (by decide), po _ (by decide), po _ (by decide), po _ (by decide),
    psi_mono_ev _ (by decide), psi_mono_ev _ (by decide)] at e
  exact e

end

end VOA.DeligneAudit.DeligneCharacter.D4K

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.psi_demazureTheta
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.finiteIdentityS
end AxiomAudit
