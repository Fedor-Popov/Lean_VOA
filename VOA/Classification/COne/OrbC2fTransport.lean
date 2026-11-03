import VOA.Classification.COne.OrbC2fCubic

/-! # Explicit norm-eight embedding and transport of generators -/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbC2f
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 LatMod OrbC2c OrbC2e OrbC2b

theorem rankOne_index_eq (m : ℕ) (a : Fin (rank (latP m))) : a = a0 m := by
  apply Fin.ext
  have h : a.val < 1 := lt_of_lt_of_eq a.isLt (rank_latP m)
  change a.val = 0
  omega

theorem rankOne_sum {M : Type*} [AddCommMonoid M] (m : ℕ)
    (f : Fin (rank (latP m)) → M) : ∑ a, f a = f (a0 m) := by
  apply Finset.sum_eq_single (a0 m)
  · intro b _ hb
    exact (hb (rankOne_index_eq m b)).elim
  · simp

theorem rankOne_cocForm (m : ℕ) : cocForm (latP m) = 0 := by
  apply LinearMap.ext₂
  intro a b
  change cocExp (latP m) (latticeBasis (latP m)) a b = 0
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ (latP m).carrier) = 1 := by
    rw [← Module.finrank_eq_card_basis (Module.Free.chooseBasis ℤ (latP m).carrier)]
    exact rank_latP m
  have he : ∀ i j : Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ (latP m).carrier)),
      ¬j < i := by intro i j; have := i.isLt; have := j.isLt; simp only [hc] at *; omega
  simp [cocExp, he]

theorem rankOne_latCob (p q : ℕ) (ι : (latP p).carrier →ₗ[ℤ] (latP q).carrier)
    (a : (latP p).carrier) : latCob (latP p) (latP q) ι a = 1 := by
  simp [latCob, cobSign, cocDiff, rankOne_cocForm, symForm, symMatrix]

/-- The actual chosen frame may have either sign; its square is one. -/
theorem scale_osc_square :
    (oscMatrix (latP 4) (latP 1) (scaleIota 1 2) (a0 1) (a0 4)) ^ 2 = 1 := by
  have h := congrArg (fun Q => Q (a0 4) (a0 4))
    (oscMatrix_transpose_mul (latP 4) (latP 1) (latP_posDef 4 four_ge_one)
      (latP_posDef 1 le_rfl) (scaleIota 1 2) (scaleIota_isometry 1 2))
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, rankOne_sum,
    Matrix.one_apply_eq, sq] using h

theorem scale_fock_J :
    fockMap (oscMatrix (latP 4) (latP 1) (scaleIota 1 2)) (evR (a0 4) JR) =
      evR (a0 1) JR := by
  have hQ := scale_osc_square
  simp only [JR, evR_cons, evR_nil, evalWord_cons, evalWord_nil,
    map_add, map_smul, map_mul, map_one, map_zero, fockMap_X, rankOne_sum]
  simp only [MvPolynomial.smul_eq_C_mul]
  have hC : (MvPolynomial.C
      (oscMatrix (latP 4) (latP 1) (scaleIota 1 2) (a0 1) (a0 4))) ^ 2 =
      (1 : FockN (rank (latP 1))) := by rw [← map_pow, hQ, map_one]
  norm_num only [map_one, map_neg, map_ofNat]
  linear_combination
    (MvPolynomial.X (0, a0 1)^4 *
      ((MvPolynomial.C (oscMatrix (latP 4) (latP 1) (scaleIota 1 2) (a0 1) (a0 4)))^2+1) -
      2*MvPolynomial.X (2,a0 1)*MvPolynomial.X (0,a0 1) +
      MvPolynomial.C (3/2 : ℂ) * MvPolynomial.X (1,a0 1)^2) * hC

theorem scaleMorph_J : scaleMorph 1 2 (J 4 four_ge_one : LatModuleGen (latP 4)) =
    ls 1 JR := by
  rw [hasN_J]
  change latMorph (latP 4) (latP 1) (scaleIota 1 2)
    (latStateGen (latP 4) (evR (a0 4) JR) 0) = _
  rw [latMorph_latStateGen, rankOne_latCob, one_smul, scale_fock_J, map_zero]

theorem scaleMorph_E : scaleMorph 1 2 (EP 4 four_ge_one : LatModuleGen (latP 4)) =
    latChargeGen (latP 1) (2 : ℤ) + latChargeGen (latP 1) (-2 : ℤ) := by
  rw [EP_coe, map_add]
  change latMorph (latP 4) (latP 1) (scaleIota 1 2) (latStateGen _ 1 _) +
    latMorph (latP 4) (latP 1) (scaleIota 1 2) (latStateGen _ 1 _) = _
  rw [latMorph_latStateGen, latMorph_latStateGen, rankOne_latCob, rankOne_latCob,
    one_smul, one_smul, map_one]
  rfl

end VOA.Classification.COne.OrbC2f
