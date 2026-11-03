import VOA.Classification.COne.OrbOddUV
import VOA.Classification.COne.OrbRat5Char

/-!
# OrbOdd (7): `TetraOddAnnihilator` from five scalars

With `[u] * [v] = c · q([ω]) [u]` (`tetra_uv_zhu`, `u₍₁₅₎v = c u`) and `[v] = V([ω])·1`
(the `τ`-even part of `A(W)` is `ℂ[[ω]]`), centrality of `[ω]` gives

  `R([ω]) [u] = 0`,  `R = V - c q`,

and `R(λ) = ψ(v) - c q(λ)` for every character `ψ` of `A(W)` with `ψ([ω]) = λ`.

* `vacuumChar`: the character of the vacuum top (`ψ₀([ω]) = 0`, `ψ₀([v]) = 0`), so
  `R(0) = -c q(0) ≠ 0` as soon as `c ≠ 0` (`q(0) = 101/12547518984`).
* `tetraOddAnnihilator_of_singleValues`: the remaining input is the named residual
  `TetraOddSingleValues`: `c ≠ 0`, and at each of `λ = 1, 1/4, 1/16, 9/16` some character
  `ψ` with `ψ([ω]) = λ` has `ψ([v]) ≠ c q(λ)`.
* `cubicZhuDimensionBound_of_singleValues`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbOdd

open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbC2b OrbC2c OrbRat2 OrbZhu
  VOA.LatGen VOA.LatGen.Triplet Polynomial

/-- `tetra ≅ A₄` is finite (the same instance as in `OrbZhuGraded`). -/
noncomputable local instance tetraFintypeR : Fintype tetra :=
  @Fintype.ofFinite _ (Finite.of_equiv (alternatingGroup (Fin 4)) tetra_group.some.symm.toEquiv)

/-! ## The vacuum character -/

theorem wt_vacuum_ne_zero : Wt.vacuum ≠ 0 := (exceptionalOrbifold_isSimple tetra).vacuum_ne_zero

theorem vacuum_mem_Omega : Wt.vacuum ∈ Omega (adjointWeakModule Wt) := by
  intro β a ha n hn
  rcases lt_or_ge β 0 with hβ | hβ
  · rw [Wt.positivity β hβ] at ha
    rw [(Submodule.mem_bot ℂ).mp ha]
    change mode (Wt.Y 0) n Wt.vacuum = 0
    rw [map_zero]; rfl
  · rw [show mode ((adjointWeakModule Wt).YM a) n Wt.vacuum = Wt.smul a n Wt.vacuum by
      rw [PreVertexAlgebra.smul_def]; rfl]
    exact PreVertexAlgebra.smul_vacuum_nonneg _ a (by omega)

theorem vacuum_line (k : ℤ) (a : (orbifold tetra).carrier) (ha : a ∈ Wt.grading k) :
    ∃ c : ℂ, mode ((adjointWeakModule Wt).YM a) (k - 1) Wt.vacuum = c • Wt.vacuum := by
  have hm : mode ((adjointWeakModule Wt).YM a) (k - 1) Wt.vacuum = Wt.smul a (k - 1) Wt.vacuum := by
    rw [PreVertexAlgebra.smul_def]; rfl
  rw [hm]
  rcases lt_or_ge k 1 with hk | hk
  · rcases lt_or_ge k 0 with hk0 | hk0
    · rw [Wt.positivity k hk0] at ha
      rw [(Submodule.mem_bot ℂ).mp ha]
      exact ⟨0, by simp⟩
    · obtain rfl : k = 0 := by omega
      rw [Wt.vacuum_grade] at ha
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp ha
      refine ⟨t, ?_⟩
      rw [PreVertexAlgebra.smul_smul_left, show (0 : ℤ) - 1 = -1 by norm_num,
        PreVertexAlgebra.smul_vacuum_neg_one]
  · exact ⟨0, by rw [PreVertexAlgebra.smul_vacuum_nonneg _ a (by omega), zero_smul]⟩

theorem exists_vacuumChar :
    ∃ ψ : A Wt →ₗ[ℂ] ℂ, (∀ p q, ψ (Amul (zhuRingData_holds Wt) p q) = ψ p * ψ q) ∧
      ψ (mk Wt Wt.vacuum) = 1 ∧ ψ (mk Wt Wt.conformalVector) = 0 ∧ ψ (mk Wt tetraV) = 0 := by
  letI := instRingA Wt
  letI := instAlgebraA Wt
  obtain ⟨χ, hχ⟩ := OrbRat5.exists_character_of_top_line (adjointWeakModule Wt) vacuum_mem_Omega
    wt_vacuum_ne_zero vacuum_line
  have hval : ∀ (k : ℤ) (a : (orbifold tetra).carrier), a ∈ Wt.grading k →
      χ (mk Wt a) • Wt.vacuum = Wt.smul a (k - 1) Wt.vacuum := by
    intro k a ha
    rw [← hχ, PlusSplitting.topEvaluation_mk, oLevW_homogeneous _ 0 ha, add_zero,
      PreVertexAlgebra.smul_def]; rfl
  refine ⟨χ.toLinearMap, fun p q => map_mul χ p q, map_one χ, ?_, ?_⟩
  · have h := hval 2 _ Wt.conformal_mem
    rw [PreVertexAlgebra.smul_vacuum_nonneg _ _ (by norm_num)] at h
    exact (smul_eq_zero.mp h).resolve_right wt_vacuum_ne_zero
  · have h := hval 16 _ tetraV_mem
    rw [PreVertexAlgebra.smul_vacuum_nonneg _ _ (by norm_num)] at h
    exact (smul_eq_zero.mp h).resolve_right wt_vacuum_ne_zero

/-! ## `[v]` is a polynomial in `[ω]` -/

theorem exists_poly_V : ∃ V : ℂ[X], mk Wt tetraV = aeval (omegaL Wt) V (mk Wt Wt.vacuum) := by
  obtain ⟨ψ, hmul, h1, hw⟩ := exists_psi
  let w : Fin 13 → A Wt := fun a => (omegaL Wt ^ (a : ℕ)) (mk Wt Wt.vacuum)
  have hψw : ∀ (j : Fin 13) (P : ℂ[X]),
      ψ (lamIdx j) ((aeval (omegaL Wt) P) (mk Wt Wt.vacuum)) = P.eval (lam j) := by
    intro j P
    rw [psi_aeval (hmul _) (h1 _) (hw _) P, tetraWeight_lamIdx]
  have hV : (Matrix.vandermonde lam).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr lam_injective
  have hcomb : ∀ (d : Fin 13 → ℂ) (j : Fin 13),
      ψ (lamIdx j) (∑ a, d a • w a) = Matrix.mulVec (Matrix.vandermonde lam) d j := by
    intro d j
    change _ = ∑ a, Matrix.vandermonde lam j a * d a
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, smul_eq_mul, Matrix.vandermonde_apply, mul_comm]
    congr 1
    have := hψw j (X ^ (a : ℕ))
    simpa [w] using this
  have hind : LinearIndependent ℂ w := by
    rw [Fintype.linearIndependent_iff]
    intro d hd
    have hz : Matrix.mulVec (Matrix.vandermonde lam) d = 0 := by
      funext j
      rw [← hcomb, hd, map_zero]; rfl
    have := Matrix.eq_zero_of_mulVec_eq_zero hV hz
    intro a; rw [this]; rfl
  have hfixed : ∀ P : ℂ[X], (aeval (omegaL Wt) P) (mk Wt Wt.vacuum) ∈ evenSpan := fun P =>
    mem_evenSpan_of_fixed (by rw [tauA_aeval, tauA_vac])
  have hwE : Submodule.span ℂ (Set.range w) ≤ evenSpan := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have := hfixed (X ^ (a : ℕ))
    simpa [w] using this
  haveI : FiniteDimensional ℂ evenSpan := by
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun a : Fin 11 =>
        (omegaL Wt ^ (a : ℕ)) (mk Wt Wt.vacuum))) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun a : Fin 2 =>
        (omegaL Wt ^ (a : ℕ)) (mk Wt tetraV))) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    unfold evenSpan
    infer_instance
  have hspan_eq : Submodule.span ℂ (Set.range w) = evenSpan := by
    apply Submodule.eq_of_le_of_finrank_le hwE
    rw [finrank_span_eq_card hind, Fintype.card_fin]
    exact finrank_evenSpan_le
  have hv : mk Wt tetraV ∈ Submodule.span ℂ (Set.range w) := by
    rw [hspan_eq]; exact mem_evenSpan_of_fixed tauA_V
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
  refine ⟨∑ a : Fin 13, Polynomial.C (d a) * X ^ (a : ℕ), ?_⟩
  rw [← hd, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, aeval_C, aeval_X_pow, Module.End.mul_apply, Module.algebraMap_end_apply]

/-! ## Centrality -/

theorem omegaL_pow_central (n : ℕ) (x : A Wt) :
    Amul (zhuRingData_holds Wt) x ((omegaL Wt ^ n) (mk Wt Wt.vacuum)) =
      Amul (zhuRingData_holds Wt) ((omegaL Wt ^ n) (mk Wt Wt.vacuum)) x := by
  letI := instRingA Wt
  induction n with
  | zero =>
    simp only [pow_zero, Module.End.one_apply]
    rw [Amul_one_left, Amul_one_right]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    change Amul _ x (Amul _ (mk Wt Wt.conformalVector) _) =
      Amul _ (Amul _ (mk Wt Wt.conformalVector) _) x
    have hc : ∀ y : A Wt, Amul (zhuRingData_holds Wt) (mk Wt Wt.conformalVector) y =
        Amul (zhuRingData_holds Wt) y (mk Wt Wt.conformalVector) := omega_central Wt
    rw [← Amul_assoc, ← hc x, Amul_assoc, ih, ← Amul_assoc, Amul_assoc]

theorem aeval_one_central (P : ℂ[X]) (x : A Wt) :
    Amul (zhuRingData_holds Wt) x ((aeval (omegaL Wt) P) (mk Wt Wt.vacuum)) =
      (aeval (omegaL Wt) P) x := by
  rw [aeval_omegaL_eq_Amul Wt P x]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, LinearMap.add_apply, map_add, hP, hQ, map_add, LinearMap.add_apply]
  | monomial n c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul,
      omegaL_pow_central, map_smul, LinearMap.smul_apply]

/-! ## The reduction -/

/-- The four non-vacuum single weights. -/
def sgl4 : Fin 4 → ℚ := ![1, 1/4, 1/16, 9/16]

/-- OPEN residual (five scalars, lattice computations): with `u₍₁₅₎ v = c u`, `c ≠ 0`, and for
each `λ ∈ {1, 1/4, 1/16, 9/16}` some character `ψ` of `A(W)` with `ψ([ω]) = λ` has
`ψ([v]) ≠ c · q(λ)` (`q = qList`). -/
def TetraOddSingleValues : Prop :=
  ∀ c : ℂ, Wt.smul tetraU 15 tetraV = c • tetraU →
    c ≠ 0 ∧ ∀ i : Fin 4, ∃ ψ : A Wt →ₗ[ℂ] ℂ,
      (∀ p q, ψ (Amul (zhuRingData_holds Wt) p q) = ψ p * ψ q) ∧
      ψ (mk Wt Wt.vacuum) = 1 ∧ ψ (mk Wt Wt.conformalVector) = ((sgl4 i : ℚ) : ℂ) ∧
      ψ (mk Wt tetraV) ≠ c * (zp qList).eval ((sgl4 i : ℚ) : ℂ)

theorem qList_eval_zero : (zp qList).eval 0 ≠ 0 := by
  simp only [qList, zp, eval_add, eval_C, eval_mul, eval_X, zero_mul, add_zero]
  norm_num

/-- The odd annihilator from the five scalars. -/
theorem tetraOddAnnihilator_of_singleValues (h : TetraOddSingleValues) : TetraOddAnnihilator := by
  obtain ⟨c, h15, hprod⟩ := tetra_uv_zhu
  obtain ⟨hc0, hvals⟩ := h c h15
  obtain ⟨V, hV⟩ := exists_poly_V
  refine ⟨V - Polynomial.C c * zp qList, ?_, ?_⟩
  · intro i
    rw [eval_sub, eval_mul, eval_C]
    -- evaluate `V` through a character
    have key : ∀ (ψ : A Wt →ₗ[ℂ] ℂ), (∀ p q, ψ (Amul (zhuRingData_holds Wt) p q) = ψ p * ψ q) →
        ψ (mk Wt Wt.vacuum) = 1 → ∀ {lam : ℂ}, ψ (mk Wt Wt.conformalVector) = lam →
        V.eval lam = ψ (mk Wt tetraV) := by
      intro ψ hmul h1 lam hw
      rw [hV, psi_aeval hmul h1 hw]
    have hsgl : ∀ j : Fin 4, ∃ ψ : A Wt →ₗ[ℂ] ℂ,
        (∀ p q, ψ (Amul (zhuRingData_holds Wt) p q) = ψ p * ψ q) ∧
        ψ (mk Wt Wt.vacuum) = 1 ∧ ψ (mk Wt Wt.conformalVector) = ((sglQ j.succ : ℚ) : ℂ) ∧
        ψ (mk Wt tetraV) ≠ c * (zp qList).eval ((sglQ j.succ : ℚ) : ℂ) := by
      intro j
      obtain ⟨ψ, hmul, h1, hw, hne⟩ := hvals j
      refine ⟨ψ, hmul, h1, ?_, ?_⟩
      · rw [hw]; fin_cases j <;> rfl
      · convert hne using 3
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · obtain ⟨ψ, hmul, h1, hw, hv⟩ := exists_vacuumChar
      have e := key ψ hmul h1 (lam := ((sglQ 0 : ℚ) : ℂ)) (by rw [hw]; simp [sglQ])
      rw [e, hv, zero_sub, neg_ne_zero]
      have h0 : ((sglQ 0 : ℚ) : ℂ) = 0 := by simp [sglQ]
      rw [h0]
      exact mul_ne_zero hc0 qList_eval_zero
    · obtain ⟨ψ, hmul, h1, hw, hne⟩ := hsgl j
      rw [key ψ hmul h1 hw]
      exact sub_ne_zero.mpr hne
  · -- `R([ω]) [u] = [u]*[v] - c q([ω]) [u] = 0`
    have hc := aeval_one_central V (mk Wt tetraU)
    rw [← hV, hprod] at hc
    rw [map_sub, LinearMap.sub_apply, ← hc, map_mul, aeval_C, Module.End.mul_apply,
      Module.algebraMap_end_apply, sub_self]

/-- `CubicZhuDimensionBound` from the five scalars. -/
theorem cubicZhuDimensionBound_of_singleValues (h : TetraOddSingleValues) :
    CubicZhuDimensionBound :=
  cubicZhuDimensionBound_of_annihilator (tetraOddAnnihilator_of_singleValues h)

end VOA.Classification.COne.OrbOdd
