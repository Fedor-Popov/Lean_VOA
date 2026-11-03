import VOA.DeligneAudit.D4CharGTHilbert

/-! Unit-variable specialization of the full Demazure character identity. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open DeligneCharacter

noncomputable section

/-- The rational-polynomial version of jmap: q goes to the actual nome r squared. -/
def rsPolyMap : Polynomial ℚ →+* D4K.Kq :=
  (HahnSeries.ofPowerSeries ℤ ℚ).comp
    ((PowerSeries.expand 2 two_ne_zero).toRingHom.comp Polynomial.coeToPowerSeries.ringHom)

theorem rsPolyMap_X : rsPolyMap Polynomial.X = D4K.qq := by
  simp [rsPolyMap, D4K.qq, HahnSeries.single_pow]

theorem rsPolyMap_coeff (P : Polynomial ℚ) (N : ℕ) :
    (rsPolyMap P).coeff (2 * (N : ℤ)) = P.coeff N := by
  rw [show 2 * (N : ℤ) = ((2 * N : ℕ) : ℤ) by omega]
  simp only [rsPolyMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_expand_mul, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeff_coe]

theorem rsPolyMap_qmulti (t : Fin 4 → ℕ) :
    rsPolyMap (qmultiPoly t) = rsMultinomial t := by
  simp only [qmultiPoly, rsMultinomial, map_mul, A2.map_qbinom, rsPolyMap_X]

theorem rsPolyMap_gl4 (a b c d : ℕ) :
    rsPolyMap (gl4Poly a b c d) =
      gtEval D4K.qq (fun _ => 1) 4 ![(a : ℤ), (b : ℤ), (c : ℤ), (d : ℤ)] := by
  rw [← rsGT_gl4Poly, gtEval_map]
  simp only [rsPolyMap_X, map_one]

/-- Evaluation at all Laurent variables equal to one, as an algebra homomorphism. -/
def rsEvOne : D4K.R →ₐ[D4K.Kq] D4K.Kq :=
  AddMonoidAlgebra.lift D4K.Kq D4K.Kq D4K.V 1

theorem rsEvOne_mon (v : D4K.V) (c : D4K.Kq) : rsEvOne (D4K.mon v c) = c := by
  simp [rsEvOne, D4K.mon, AddMonoidAlgebra.lift_single]

theorem rsEvOne_eq_ev1 : rsEvOne.toLinearMap = D4K.ev1 := by
  apply Finsupp.lhom_ext
  intro v c
  change rsEvOne (D4K.mon v c) = D4K.ev1 (D4K.mon v c)
  rw [rsEvOne_mon, D4K.ev1_mon]

theorem rsEvOne_gt (lam : Fin 4 → ℤ) :
    D4K.ev1 (gtEval rsNome rsZAlphabet 4 lam) = gtEval D4K.qq (fun _ => 1) 4 lam := by
  rw [← rsEvOne_eq_ev1]
  change rsEvOne.toRingHom (gtEval rsNome rsZAlphabet 4 lam) = _
  rw [gtEval_map]
  have hq : rsEvOne.toRingHom rsNome = D4K.qq := rsEvOne.commutes D4K.qq
  have hu : (fun i => Units.map rsEvOne.toRingHom (rsZAlphabet i)) =
      (fun _ : ℕ => (1 : D4K.Kqˣ)) := by
    funext i
    apply Units.ext
    change rsEvOne (D4K.mon (rsZVector i) 1) = 1
    exact rsEvOne_mon _ _
  rw [hq, hu]

/-- The central shift has determinant one after unit-variable specialization. -/
theorem rsEvOne_mixed (a b c : ℕ) :
    D4K.ev1 (gtEval rsNome rsZAlphabet 4
      (gtMixedFourRow ((a + b : ℕ) : ℤ) b ((a + c : ℕ) : ℤ) c)) =
        rsPolyMap (gl4Poly (2 * a + (b + c)) (a + (b + c)) a 0) := by
  rw [rsEvOne_gt, rsPolyMap_gl4]
  have hs := gtEval_central_shift D4K.qq (fun _ => (1 : D4K.Kqˣ)) 4
    (gtMixedFourRow ((a + b : ℕ) : ℤ) b ((a + c : ℕ) : ℤ) c) (a + c : ℕ)
  simp only [one_zpow, Units.val_one, Finset.prod_const_one, one_mul] at hs
  have he : (fun i =>
      gtMixedFourRow ((a + b : ℕ) : ℤ) b ((a + c : ℕ) : ℤ) c i + (a + c : ℕ)) =
        (![((2 * a + (b + c) : ℕ) : ℤ), ((a + (b + c) : ℕ) : ℤ), (a : ℤ), 0] :
          Fin 4 → ℤ) := by
    ext i
    fin_cases i <;> simp [gtMixedFourRow] <;> ring
  rw [he] at hs
  exact hs.symm

/-- The full polynomial equality underlying L4, before extracting any degree. -/
theorem rsEvOne_Cdem (n : ℕ) :
    D4K.ev1 (D4K.Cdem n) = rsPolyMap (d4LeviPoly n) := by
  rw [rsCdem_eq_gt_sum, map_sum, d4LeviPoly, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [map_smul, smul_eq_mul, map_mul, rsPolyMap_qmulti, rsEvOne_mixed]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.rsPolyMap_X
#print axioms VOA.DeligneAudit.D4Char.rsPolyMap_coeff
#print axioms VOA.DeligneAudit.D4Char.rsPolyMap_qmulti
#print axioms VOA.DeligneAudit.D4Char.rsPolyMap_gl4
#print axioms VOA.DeligneAudit.D4Char.rsEvOne_mon
#print axioms VOA.DeligneAudit.D4Char.rsEvOne_eq_ev1
#print axioms VOA.DeligneAudit.D4Char.rsEvOne_gt
#print axioms VOA.DeligneAudit.D4Char.rsEvOne_mixed
#print axioms VOA.DeligneAudit.D4Char.rsEvOne_Cdem
