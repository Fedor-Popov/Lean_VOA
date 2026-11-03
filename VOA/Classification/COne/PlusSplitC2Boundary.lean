import VOA.Classification.COne.PlusSplitC2Count

/-! Uniform neutral boundary, including m=2,3,4. The leading oscillator
coefficient detects the omega term before passing to the lattice quotient. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusC2Sharp
open PlusC2 PlusUnitary VOA.TripletNilp VOA.LatGen VOA.LatGen.Triplet
  VOA.IntegralLattice HeisenbergN VOA.Moonshine MvPolynomial
variable (m : ℕ) (hm : 1 ≤ m)

def iterW (a : ℕ) : (m1Sub m hm).carrier :=
  (fun x => (M1P m hm).smul (ωM m hm) (-1) x)^[a] (WM m hm)

theorem iterW_poly (a : ℕ) :
    ∃ P ∈ FilF (latP m) (2 + 2 * a),
      ((iterW m hm a : (m1Sub m hm).carrier) : LatModuleGen (latP m)) =
        latStateGen (latP m) P 0 := by
  induction a with
  | zero =>
    refine ⟨W4poly m, ?_, rfl⟩
    have h1 : (1 : FockN (rank (latP m))) ∈ FilF (latP m) 0 :=
      monomial_mem_FilF (latP m) 0 1 (by simp)
    have hpair (i j : ℕ) : X (i, LatMod.a0 m) * X (j, LatMod.a0 m) ∈
        FilF (latP m) 2 := by
      simpa using X_mul_mem_FilF (latP m) (i, LatMod.a0 m)
        (X_mul_mem_FilF (latP m) (j, LatMod.a0 m) h1)
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (hpair 0 2))
      (Submodule.smul_mem _ _ (hpair 1 1))
  | succ a ih =>
    obtain ⟨P, hP, hPe⟩ := ih
    obtain ⟨R, hR, hRe⟩ := omega_smul_neg_one m hm P hP
    refine ⟨(1 / 2 : ℂ) • (X (0, LatMod.a0 m) * (X (0, LatMod.a0 m) * P)) + R, ?_, ?_⟩
    · apply Submodule.add_mem
      · apply Submodule.smul_mem
        exact FilF_mono (latP m) (by push_cast; omega)
          (X_mul_mem_FilF (latP m) _ (X_mul_mem_FilF (latP m) _ hP))
      · exact FilF_mono (latP m) (by push_cast; omega) hR
    · rw [iterW, Function.iterate_succ_apply', M1P_smul_coe]
      change (V2m m hm).smul _ (-1) (iterW m hm a) = _
      rw [hPe, hRe]

theorem phi_iterW (a : ℕ) :
    phi m (2 * a + 4) (iterW m hm a : LatModuleGen (latP m)) = 0 := by
  obtain ⟨P, hP, hp⟩ := iterW_poly m hm a
  rw [hp, phi_latStateGen]
  exact topCoeff_FilF m _ (by push_cast; omega) hP

/-- The coefficient in the old existential cubic W relation is zero. -/
theorem M1_omega_cubed_W :
    mk₂ (M1P m hm) (ωM m hm) ^ 3 * mk₂ (M1P m hm) (WM m hm) = 0 := by
  obtain ⟨τ, hτ⟩ := rel10M_holds m hm
  have hO : iterW m hm 3 - τ • pMulPow (M1P m hm) (ωM m hm) 5 ∈ O₂ (M1P m hm) := by
    rw [← mk₂_eq_zero_iff, map_sub, map_smul, mk₂_pMulPow]
    change mk₂ _ ((fun x => (M1P m hm).smul (ωM m hm) (-1) x)^[3] _) - _ = 0
    rw [mk₂_omIter, hτ, sub_self]
  have hf := phi_O₂ m hm 10 hO
  simp only [Submodule.coe_sub, Submodule.coe_smul, phi_sub, phi_smul] at hf
  rw [show 10 = 2 * 3 + 4 from rfl, phi_iterW] at hf
  rw [show 2 * 3 + 4 = 2 * 5 from rfl, phi_omegaPow] at hf
  have hz : τ = 0 := by
    have hp : (1 / 2 : ℂ) ^ 5 ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (mul_eq_zero.mp (by linear_combination -hf : τ * (1 / 2 : ℂ) ^ 5 = 0)).resolve_right hp
  simpa only [hz, zero_smul] using hτ

section Algebra
variable {R : Type*} [CommRing R] [Algebra ℂ R]

theorem monomial_mem_pair (o w : R) (ρ σ : ℂ)
    (h8 : w ^ 2 = ρ • (o ^ 2 * w) + σ • o ^ 4)
    (k a b : ℕ) (hk : 2 ≤ k) (hab : a + 2 * b = k) :
    o ^ a * w ^ b ∈ Submodule.span ℂ ({o ^ k, o ^ (k - 2) * w} : Set R) := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rcases b with _ | _ | b
    · have ha : a = k := by omega
      simp only [pow_zero, mul_one, ha]
      exact Submodule.subset_span (by simp)
    · have ha : a = k - 2 := by omega
      simp only [ha]
      exact Submodule.subset_span (by simp)
    · have heq : o ^ a * w ^ (b + 2) =
          ρ • (o ^ (a + 2) * w ^ (b + 1)) + σ • (o ^ (a + 4) * w ^ b) := by
        rw [pow_add w b 2, h8]
        simp only [mul_add, mul_smul_comm]
        ring_nf
      rw [heq]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (ih (b + 1) (by omega) (a + 2) (by omega)))
        (Submodule.smul_mem _ _ (ih b (by omega) (a + 4) (by omega)))
end Algebra

theorem neutral_class_mem_pair (k : ℕ) (hk : 2 ≤ k)
    (v : (m1Sub m hm).carrier) (hv : v ∈ (M1P m hm).grading (2 * k)) :
    mk₂ (M1P m hm) v ∈ Submodule.span ℂ
      ({mk₂ (M1P m hm) (ωM m hm) ^ k,
        mk₂ (M1P m hm) (ωM m hm) ^ (k - 2) * mk₂ (M1P m hm) (WM m hm)} : Set _) := by
  obtain ⟨ρ, σ, h8⟩ := rel8M_holds m hm
  refine (show monSpan m hm (2 * k) ≤ _ from ?_) (neutral_class_mem_monSpan m hm v hv)
  rw [monSpan, Submodule.span_le]
  rintro _ ⟨a, b, hab, rfl⟩
  exact monomial_mem_pair _ _ ρ σ h8 k a b hk (by omega)

/-- The first charged relation gives a uniform neutral boundary. -/
theorem omega_boundary_relation (hm2 : 2 ≤ m) :
    ∃ c : ℂ, o m hm ^ (m + 1) = c • (o m hm ^ (m - 1) * w m hm) := by
  let k := m + 1
  let S := vSchur (latP m) ((1 : ℤ) : (latP m).carrier) (2 * k)
  let q := (1 / 2 : ℂ) • (S + sigmaN _ S)
  have hσ : sigmaN (rank (latP m)) q = q := by
    dsimp [q]; rw [map_smul, map_add, sigmaN_sigmaN, add_comm]
  let v : (m1Sub m hm).carrier :=
    ⟨latStateGen (latP m) q 0, (mem_m1Carrier_iff m hm _).mpr ⟨q, hσ, rfl⟩⟩
  have hS : S ∈ gradingWN (rank (latP m)) (2 * k) := vSchur_mem_gradingWN _ _ _
  have hv : v ∈ (M1P m hm).grading (2 * k) :=
    latStateGen_mem_grading m hm (Submodule.smul_mem _ _
      (Submodule.add_mem _ hS (sigmaN_mem_gradingWN _ hS)))
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp
    (neutral_class_mem_pair m hm k (by dsimp [k]; omega) v hv)
  have hphi : phi m (2 * k) (v : LatModuleGen (latP m)) ≠ 0 := by
    change phi m (2 * k) (latStateGen (latP m) q 0) ≠ 0
    rw [phi_latStateGen]
    have he : topCoeff m (2 * k) q = topCoeff m (2 * k) S := by
      dsimp [q]
      simp only [topCoeff, coeff_smul, coeff_add, smul_eq_mul]
      rw [← topCoeff, ← topCoeff, topCoeff_sigmaN, Even.neg_one_pow (even_two_mul k)]
      ring
    rw [he]
    exact topCoeff_vSchur_ne_zero m hm 1 (by omega) (2 * k)
  have ha : a ≠ 0 := by
    intro ha
    have hO : v - b • iterW m hm (k - 2) ∈ O₂ (M1P m hm) := by
      rw [← mk₂_eq_zero_iff, map_sub, map_smul]
      change mk₂ _ v - b • mk₂ _ ((fun x => (M1P m hm).smul (ωM m hm) (-1) x)^[k-2] _) = 0
      rw [mk₂_omIter, ← hab, ha, zero_smul, zero_add, sub_self]
    have hf := phi_O₂ m hm (2 * k) hO
    simp only [Submodule.coe_sub, Submodule.coe_smul, phi_sub, phi_smul] at hf
    rw [show 2 * k = 2 * (k - 2) + 4 by dsimp [k]; omega, phi_iterW, mul_zero,
      sub_zero] at hf
    have he : 2 * (k - 2) + 4 = 2 * k := by dsimp [k]; omega
    rw [he] at hf
    exact hphi hf
  have hi : incl m hm v = PP m hm (latStateGen (latP m) S 0) := by
    apply Subtype.ext
    change latStateGen (latP m) q 0 = _
    rw [PP_coe, thetaLat_latStateGen, neg_zero, ← latStateGen_add_boson,
      ← latStateGen_csmul]
  have hz : poissonIncl m hm (mk₂ (M1P m hm) v) = 0 := by
    rw [poissonIncl_mk₂, hi, mk₂_eq_zero_iff]
    exact vSchur_mem_G m hm 1 (2 * k) (by dsimp [k]; simp)
      (by dsimp [k]; simp; omega)
  rw [← hab, map_add, map_smul, map_smul, map_pow, map_mul, map_pow,
    poissonIncl_mk₂, poissonIncl_mk₂] at hz
  have he : k - 2 = m - 1 := by dsimp [k]; omega
  change a • o m hm ^ k + b • (o m hm ^ (k - 2) * w m hm) = 0 at hz
  have hz' := congrArg (fun x : A₂ (V2mPlus m hm) => a⁻¹ • x) hz
  dsimp only at hz'
  rw [smul_add, smul_smul, inv_mul_cancel₀ ha, one_smul, smul_zero] at hz'
  refine ⟨-(a⁻¹ * b), ?_⟩
  simpa only [he, smul_smul, neg_smul] using eq_neg_of_add_eq_zero_left hz'

theorem omega_cubed_W : o m hm ^ 3 * w m hm = 0 := by
  have h := congrArg (poissonIncl m hm) (M1_omega_cubed_W m hm)
  simpa only [map_mul, map_pow, map_zero, poissonIncl_mk₂] using h

theorem omega_pow_eq_zero_ge4 (hm4 : 4 ≤ m) : o m hm ^ (m + 1) = 0 := by
  obtain ⟨c, hc⟩ := omega_boundary_relation m hm (by omega)
  rw [hc, show m - 1 = (m - 4) + 3 by omega, pow_add, mul_assoc,
    omega_cubed_W, mul_zero, smul_zero]

end VOA.Classification.COne.PlusC2Sharp
