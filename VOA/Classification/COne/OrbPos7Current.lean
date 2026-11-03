import VOA.Classification.COne.OrbPos7Creation

/-! # Current products on arbitrary inner-shifted lattice states -/

set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbPos7
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 OrbPos5 OrbPos6 LatMod TwistedReduction
open Moonshine.LatticeTwisted
open scoped TensorProduct

noncomputable def rescaledField {n : ℕ} (hn : 0 < n) (a j e : ℤ) :
    Space →ₗ[ℂ] Fld Space where
  toFun u := rescFld hn (shiftedY_truncation hn a j u) e
  map_add' u v := by
    apply Subtype.ext
    exact map_add ((rescaleLinear n e).comp (shiftedY n a j)) u v
  map_smul' c u := by
    apply Subtype.ext
    exact map_smul ((rescaleLinear n e).comp (shiftedY n a j)) c u

theorem rescaledField_local {n : ℕ} (hn : 0 < n) (a j e f : ℤ) (u v : Space) :
    Local (rescaledField hn a j e u).1 (rescaledField hn a j f v).1 :=
  shiftedY_local hn a j e f u v

theorem rescaledField_sector_off {n : ℕ} (hn : 0 < n) (a j β e : ℤ)
    (he : (e - a * β) % (n : ℤ) ≠ 0) (p : Osc) :
    rescaledField hn a j e (latStateGen (latP 1) p β) = 0 := by
  apply Subtype.ext
  funext t
  change shiftedY n a j (latStateGen (latP 1) p β) ((n : ℤ)*(-t-1)+e) = 0
  rw [shiftedY_latState]
  apply sectorField_support
  simpa only [show (n : ℤ)*(-t-1)+e-a*β = (n : ℤ)*(-t-1)+(e - a * β) by ring,
    Int.add_emod, Int.mul_emod_right, zero_add, Int.emod_emod] using he

/-- Creation recursion for every state and every residue offset. -/
theorem current_creation {n : ℕ} (hn : 0 < n) (a j e : ℤ) (k : ℕ) (v : Space) :
    Fld.prod (-(k : ℤ)-1) (shiftedCurrent j ((a : ℂ)/(2*n)))
      (rescaledField hn a j e v) =
    rescaledField hn a j e ((V2m 1 le_rfl).smul h (-(k : ℤ)-1) v) := by
  have hh : (prodR (-(k : ℤ)-1) (shiftedCurrent j ((a : ℂ)/(2*n)))).comp
      (rescaledField hn a j e) =
      (rescaledField hn a j e).comp (mode ((V2m 1 le_rfl).Y h) (-(k : ℤ)-1)) := by
    apply LinearMap.ext_on_range (latStateGen_span (latP 1))
    rintro ⟨p, β⟩
    change ℤ at β
    change Fld.prod _ _ (rescaledField hn a j e (latStateGen (latP 1) p β)) =
      rescaledField hn a j e ((V2m 1 le_rfl).smul h (-(k : ℤ)-1)
        (latStateGen (latP 1) p β))
    have hs : (V2m 1 le_rfl).smul h (-(k : ℤ)-1) (latStateGen (latP 1) p β) =
        latStateGen (latP 1) (MvPolynomial.X (k, a0 1) * p) β := by
      change (latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)).smul
        (hgen (latP 1) (a0 1)) _ (p ⊗ₜ[ℂ] eGen (latP 1) β) = _
      rw [smul_hgen_neg, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply]
      rfl
    rw [hs]
    by_cases he : (e - a * β) % (n : ℤ) = 0
    · unfold rescaledField
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [resc_sector_polynomial hn a j β e he p,
        resc_sector_polynomial hn a j β e he (MvPolynomial.X (k, a0 1) * p),
        prod_fzmul_right, delta_creation]
    · rw [rescaledField_sector_off hn a j β e he, rescaledField_sector_off hn a j β e he,
        prod_zero_right]
  exact congrArg (fun f : Space →ₗ[ℂ] Fld Space => f v) hh

theorem ordinaryField_vacuum (j : ℤ) :
    ordinaryField j (V2m 1 le_rfl).vacuum = Fld.one := by
  apply Subtype.ext
  exact (latticeModule 1 le_rfl j).vacuum_YM

theorem current_one_nonneg (j : ℤ) (t : ℂ) (ℓ : ℤ) (hℓ : 0 ≤ ℓ) :
    Fld.prod ℓ (shiftedCurrent j t) Fld.one = 0 :=
  prod_one_right_nonneg' ℓ hℓ _

theorem current_current_nonneg (j : ℤ) (t : ℂ) (ℓ : ℤ) (hℓ : 0 ≤ ℓ) :
    Fld.prod ℓ (shiftedCurrent j t) (shiftedCurrent j t) =
      if ℓ = 1 then Fld.one else 0 := by
  rw [shiftedCurrent, Fld.prod_add_left, Fld.prod_smul_left,
    prod_inverse_z_nonneg ℓ hℓ, smul_zero, add_zero,
    Fld.prod_add_right, Fld.prod_smul_right, prod_fzmul_right,
    prod_one_right_nonneg' ℓ hℓ, fzmul_zero, smul_zero, add_zero,
    ordinaryField_prod]
  have hh := Moonshine.LatticeTwistedGeneral.smul_hgen_hgen_nonneg
    (latP 1) (latP_even 1) (latP_posDef 1 le_rfl) (a0 1) (a0 1) hℓ
  change (V2m 1 le_rfl).smul h ℓ h = _ at hh
  rw [hh]
  simp only [and_true]
  split_ifs
  · exact ordinaryField_vacuum j
  · apply Subtype.ext
    exact map_zero (latticeModule 1 le_rfl j).YM

theorem current_charge_nonneg {n : ℕ} (hn : 0 < n) (a j e β ℓ : ℤ)
    (hℓ : 0 ≤ ℓ) :
    Fld.prod ℓ (shiftedCurrent j ((a : ℂ)/(2*n)))
      (rescaledField hn a j e (latChargeGen (latP 1) β)) =
    rescaledField hn a j e ((V2m 1 le_rfl).smul h ℓ (latChargeGen (latP 1) β)) := by
  have hs := smul_hgen_echg_nonneg (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)
    (a0 1) hℓ β
  change (V2m 1 le_rfl).smul h ℓ (latChargeGen (latP 1) β) = _ at hs
  rw [hs]
  by_cases he : (e - a * β) % (n : ℤ) = 0
  · have hc : rescaledField hn a j e (latChargeGen (latP 1) β) =
        fzmul ((e - a * β)/(n : ℤ)) (ordinaryField j (latChargeGen (latP 1) β)) :=
      resc_chargeField hn a j β e he
    rw [hc, prod_fzmul_right, shiftedCurrent, Fld.prod_add_left, Fld.prod_smul_left,
      prod_inverse_z_nonneg ℓ hℓ, smul_zero, add_zero, ordinaryField_prod, hs]
    split_ifs
    · rw [map_smul, hc]
      change fzmul _ (ordinaryLinear j β (chargeCoord (latP 1) β (a0 1) • 1)) = _
      rw [map_smul, fzmul_smul]
      rfl
    · rw [map_zero]
      have hz : ordinaryField j 0 = 0 := Subtype.ext (map_zero (latticeModule 1 le_rfl j).YM)
      rw [hz, fzmul_zero]
  · have hc : rescaledField hn a j e (latChargeGen (latP 1) β) = 0 :=
      rescaledField_sector_off hn a j β e he 1
    rw [hc, prod_zero_right]
    split_ifs <;> simp only [map_smul, hc, smul_zero, map_zero]

theorem rescaledField_vacuum_zero {n : ℕ} (hn : 0 < n) (a j : ℤ) :
    rescaledField hn a j 0 (V2m 1 le_rfl).vacuum = Fld.one := by
  have hh := resc_chargeField hn a j 0 0 (by simp)
  exact hh.trans (by
    simp only [mul_zero, sub_self, Int.zero_ediv]
    change fzmul 0 (ordinaryField j (V2m 1 le_rfl).vacuum) = Fld.one
    rw [fzmul_zero_shift, ordinaryField_vacuum])

theorem h_product_nonneg (ℓ : ℤ) (hℓ : 0 ≤ ℓ) :
    (V2m 1 le_rfl).smul h ℓ h =
      if ℓ = 1 then (V2m 1 le_rfl).vacuum else 0 := by
  simpa only [and_true] using Moonshine.LatticeTwistedGeneral.smul_hgen_hgen_nonneg
    (latP 1) (latP_even 1) (latP_posDef 1 le_rfl) (a0 1) (a0 1) hℓ

theorem word_cons (c : ℕ × Fin (rank (latP 1)))
    (l : List (ℕ × Fin (rank (latP 1)))) (β : ℤ) :
    wordStateN (c :: l) ⊗ₜ[ℂ] eGen (latP 1) β =
      (V2m 1 le_rfl).smul h (-(c.1 : ℤ)-1) (wordStateN l ⊗ₜ[ℂ] eGen (latP 1) β) := by
  have hb : c.2 = a0 1 := by
    haveI : Subsingleton (Fin (rank (latP 1))) := by rw [rank_latP]; infer_instance
    exact Subsingleton.elim _ _
  change _ = (latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)).smul _ _ _
  rw [smul_hgen_neg, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, wordStateN_cons]
  rw [show c = (c.1, a0 1) from Prod.ext rfl hb]

theorem current_product_word {n : ℕ} (hn : 0 < n) (a j e : ℤ)
    (l : List (ℕ × Fin (rank (latP 1)))) (β : ℤ) (ℓ : ℤ) :
    Fld.prod ℓ (shiftedCurrent j ((a : ℂ)/(2*n)))
      (rescaledField hn a j e (wordStateN l ⊗ₜ[ℂ] eGen (latP 1) β)) =
    rescaledField hn a j e ((V2m 1 le_rfl).smul h ℓ
      (wordStateN l ⊗ₜ[ℂ] eGen (latP 1) β)) := by
  induction l generalizing ℓ with
  | nil =>
    rcases lt_or_ge ℓ 0 with hℓ | hℓ
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ℓ = -(k : ℤ)-1 := ⟨(-ℓ-1).toNat, by omega⟩
      exact current_creation hn a j e k _
    · exact current_charge_nonneg hn a j e β ℓ hℓ
  | cons c l ih =>
    rcases lt_or_ge ℓ 0 with hℓ | hℓ
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ℓ = -(k : ℤ)-1 := ⟨(-ℓ-1).toNat, by omega⟩
      exact current_creation hn a j e k _
    set v := wordStateN l ⊗ₜ[ℂ] eGen (latP 1) β
    set H := shiftedCurrent j ((a : ℂ)/(2*n))
    set F := rescaledField hn a j e
    have hloc : Local H.1 H.1 := by
      rw [show H = rescaledField hn a j 0 h from (resc_current hn a j).symm]
      exact rescaledField_local hn a j 0 0 h h
    have hT := prod_comm_formula (C := F v) hloc 2
      (fun r hr => by rw [current_current_nonneg j _ r (by omega), if_neg (by omega)])
      ℓ (-(c.1 : ℤ)-1)
    have hV := Moonshine.voa_comm (V2m 1 le_rfl) h h v ℓ (-(c.1 : ℤ)-1) 2
      (fun r hr => by rw [h_product_nonneg r (by omega), if_neg (by omega)])
    have hFV := congrArg F hV
    rw [map_sub, map_sum] at hFV
    simp only [map_smul] at hFV
    have hsum : ∀ r ∈ Finset.range 2,
        Fld.prod (ℓ + (-(c.1 : ℤ)-1) - r) (Fld.prod r H H) (F v) =
        F ((V2m 1 le_rfl).smul ((V2m 1 le_rfl).smul h r h)
          (ℓ + (-(c.1 : ℤ)-1) - r) v) := by
      intro r _
      rw [current_current_nonneg j _ r (by omega), h_product_nonneg r (by omega)]
      split_ifs
      · rw [Fld.prod_one_left_all, PreVertexAlgebra.smul_vacuum_left]
        split_ifs <;> simp only [map_zero]
      · rw [prod_zero_left, PreVertexAlgebra.smul_zero_left, map_zero]
    rw [Finset.sum_congr rfl (fun r hr => congrArg (fun x : Fld Space => gBinom ℓ r • x)
      (hsum r hr))] at hT
    rw [current_creation hn a j e c.1, show Fld.prod ℓ H (F v) =
      F ((V2m 1 le_rfl).smul h ℓ v) from ih ℓ, current_creation hn a j e c.1] at hT
    rw [word_cons]
    exact sub_left_injective (hT.trans hFV.symm)

/-- Full current product formula: all states, all integer products, all offsets. -/
theorem current_product {n : ℕ} (hn : 0 < n) (a j e ℓ : ℤ) (v : Space) :
    Fld.prod ℓ (shiftedCurrent j ((a : ℂ)/(2*n))) (rescaledField hn a j e v) =
      rescaledField hn a j e ((V2m 1 le_rfl).smul h ℓ v) := by
  induction v using Moonshine.LatticeTwistedGeneral.latState_induction (latP 1) with
  | h0 => rw [map_zero, prod_zero_right, PreVertexAlgebra.smul_zero_right, map_zero]
  | hadd x y hx hy =>
    rw [map_add, Fld.prod_add_right, hx, hy, PreVertexAlgebra.smul_add_right, map_add]
  | hsmul c x hx =>
    rw [map_smul, Fld.prod_smul_right, hx, PreVertexAlgebra.smul_smul_right, map_smul]
  | hw l β => exact current_product_word hn a j e l β ℓ

end VOA.Classification.COne.OrbPos7
