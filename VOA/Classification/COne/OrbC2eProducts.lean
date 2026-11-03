import VOA.Classification.COne.OrbC2eCertificates

/-! # Charged self-product certificates at norm eight

The four E-E identities complete the three low-mode columns of
Dong--Jiang Lemma 3.4. These are state identities, not just C₂ congruences.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

namespace VOA.Classification.COne.OrbC2e
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 LatMod PlusRat3 OrbC2c

theorem chargeCoord_neg (L : IntegralLattice) (β : L.carrier) (a : Fin (rank L)) :
    chargeCoord L (-β) a = -chargeCoord L β a := by
  have h := chargeCoord_add L β (-β) a
  rw [add_neg_cancel, chargeCoord_zero] at h
  linear_combination -h

/-- The complete E-E product in the neutral range, before charge reduction.
The four charge pairs are simplified separately to keep coercions small. -/
theorem E_smul_E_neutral (m : ℕ) (hm : 1 ≤ m) (n : ℤ)
    (hn : -(2 * (m : ℤ)) ≤ n) :
    ((V2mPlus m hm).smul (EP m hm) n (EP m hm) : LatModuleGen (latP m)) =
      latStateGen (latP m)
        (evRc (a0 m) (cα m)
          (let P := if 0 ≤ -n-1+2*(m : ℤ) then schurR (-n-1+2*(m : ℤ)).toNat else []
           P ++ negChargeR P)) 0 := by
  have hneg : ¬0 ≤ -n-1-2*(m : ℤ) := by omega
  have hz (δ : (latP m).carrier) : latStateGen (latP m) 0 δ = 0 := by
    simp [latStateGen]
  have hc : chargeCoord (latP m) ((-1 : ℤ) : (latP m).carrier) (a0 m) = -cα m :=
    chargeCoord_neg (latP m) ((1 : ℤ) : (latP m).carrier) (a0 m)
  have hpp := V2m_charge_smul_charge m hm (1 : ℤ) (1 : ℤ) n
  have hpm := V2m_charge_smul_charge m hm (1 : ℤ) (-1 : ℤ) n
  have hmp := V2m_charge_smul_charge m hm (-1 : ℤ) (1 : ℤ) n
  have hmm := V2m_charge_smul_charge m hm (-1 : ℤ) (-1 : ℤ) n
  simp only [PlusCharacterTable.rankOne_cocycle, one_smul, latP_form, mul_one,
    mul_neg_one, neg_neg, sub_neg_eq_add, hneg, if_false, evRc_nil, hz, hc] at hpp hpm hmp hmm
  rw [V2mPlus_smul_coe, EP_coe, PreVertexAlgebra.smul_add_left,
    PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_add_right, hpp, hpm, hmp, hmm,
    zero_add, add_zero]
  rw [evRc_append, evRc_negChargeR, latStateGen_add_boson]
  rfl

namespace NeutralExpr
open OrbC2c.NeutralExpr

def ee : Fin 4 → OrbC2c.NeutralExpr
  | ⟨0, _⟩ => .add u3 (.scale (20/9) v3)
  | ⟨1, _⟩ => .add u2 (.scale (20/9) v2)
  | ⟨2, _⟩ => .add u1 (.scale (10/9) (.vir (-1) .j))
  | ⟨3, _⟩ => .add u0 (.scale (20/9) .j)

set_option maxHeartbeats 2400000 in
-- Kernel reduction of the degree-seven normal-ordering and Schur certificates.
theorem ee_cert (n : Fin 4) :
    normR (reduceR 8 (schurR (7-n.val) ++ negChargeR (schurR (7-n.val)))) =
      normR (liftR (ee n).poly) := by
  fin_cases n <;> decide +kernel

end NeutralExpr

/-- All four charged self-product identities in Dong--Jiang Lemma 3.4. -/
theorem E_modes_E_four (n : Fin 4) :
    (V2mPlus 4 (by norm_num)).smul (EP 4 (by norm_num)) (n : ℤ) (EP 4 (by norm_num)) =
      (NeutralExpr.ee n).state 4 (by norm_num) := by
  apply Subtype.ext
  rw [E_smul_E_neutral 4 (by norm_num) (n : ℤ) (by omega)]
  dsimp only
  norm_num only [Nat.cast_ofNat]
  have hi : -((n : ℕ) : ℤ)-1+8 = (7-n.val : ℕ) := by omega
  rw [hi, if_pos (by positivity), Int.toNat_natCast,
    norm_eight_eq_of_cert _ _ (NeutralExpr.ee_cert n)]
  exact (OrbC2c.NeutralExpr.hasN_state 4 (by norm_num) (NeutralExpr.ee n)).symm

/-- The leading E-E vacuum coefficient fixes the normalization. -/
theorem E_seven_E_four :
    (V2mPlus 4 (by norm_num)).smul (EP 4 (by norm_num)) 7 (EP 4 (by norm_num)) =
      (2 : ℂ) • (V2mPlus 4 (by norm_num)).vacuum := by
  apply Subtype.ext
  rw [E_smul_E_neutral 4 (by norm_num) 7 (by norm_num)]
  norm_num [schurR, negChargeR, evRc_cons, evRc_nil, evalWordC_nil]
  rw [show (2 : FockN (rank (latP 4))) = (2 : ℂ) • 1 by
    simp only [MvPolynomial.smul_eq_C_mul, mul_one, map_ofNat],
    latStateGen_csmul]
  rfl

end VOA.Classification.COne.OrbC2e
