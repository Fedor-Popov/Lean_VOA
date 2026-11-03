import VOA.Classification.COne.OrbZhuSixteen
import VOA.Classification.COne.OrbRat6Heis

/-!
# OrbZhu (5): the even half of `A(V₂^{A₄})` is `ℂ¹³`; the odd residual becomes a single
# annihilator

With `τ` the octahedral involution (`τ u = -u`, `τ v = v`) and the 21 proved characters
(`OrbRat6.cubicZhuCharacterTable_holds`):

* the `τ`-fixed part of `A(W)` lies in `span{[ω]^a (a ≤ 10), [ω]^a[v] (a ≤ 1)}` (13 vectors),
  while `[ω]^a·1` (`a ≤ 12`) are independent there (Vandermonde on 13 distinct lowest weights);
  hence `q₁₃([ω]) = 0` with `q₁₃ = ∏_{13 lowest weights} (X - λ)` (`q13_omega_eq_zero`);
* so `q₁₃([ω])[u] = 0`, and ANY relation `R([ω])[u] = 0` with `R` nonzero at the five
  singly-occurring weights `0, 1, 1/4, 1/16, 9/16` gives, by Bézout,
  `P₈([ω])[u] = 0` for the monic degree-8 `P₈ = ∏_{doubled weights} (X - λ)`
  (`tetraOddZhuRelation_of_annihilator`).

The remaining residual `TetraOddAnnihilator` is what the associativity identity
`([u]*[v])*[v] = [u]*([v]*[v])` supplies (checked numerically, outside Lean).
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbZhu

open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbC2b OrbC2c OrbRat2 Polynomial
  VOA.LatGen VOA.LatGen.Triplet Equiv Equiv.Perm

/-- `tetra ≅ A₄` is finite (the same instance as in `OrbZhuGraded`). -/
noncomputable local instance tetraFintypeZ'' : Fintype tetra :=
  @Fintype.ofFinite _ (Finite.of_equiv (alternatingGroup (Fin 4)) tetra_group.some.symm.toEquiv)

/-! ## Zhu algebra maps from VOA homomorphisms -/

section ZhuMap
universe u v
variable {𝒱 : Type u} {𝒲 : Type v} [AddCommGroup 𝒱] [Module ℂ 𝒱] [AddCommGroup 𝒲]
  [Module ℂ 𝒲] {V : VertexOperatorAlgebra 𝒱} {T : VertexOperatorAlgebra 𝒲}

/-- The linear map `A(V) → A(T)` induced by a conformal VOA homomorphism. -/
def zhuMap {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ)
    (hω : φ V.conformalVector = T.conformalVector) : A V →ₗ[ℂ] A T :=
  Submodule.mapQ (O V) (O T) φ (Submodule.map_le_iff_le_comap.mp (voaHom_map_O hφ hω))

theorem zhuMap_mk {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ)
    (hω : φ V.conformalVector = T.conformalVector) (x : 𝒱) :
    zhuMap hφ hω (mk V x) = mk T (φ x) := rfl

theorem zhuMap_Amul {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ)
    (hω : φ V.conformalVector = T.conformalVector) (p q : A V) :
    zhuMap hφ hω (Amul (zhuRingData_holds V) p q) =
      Amul (zhuRingData_holds T) (zhuMap hφ hω p) (zhuMap hφ hω q) := by
  obtain ⟨a, rfl⟩ := mk_surjective V p
  obtain ⟨b, rfl⟩ := mk_surjective V q
  rw [Amul_mk, zhuMap_mk, zhuMap_mk, zhuMap_mk, Amul_mk, voaHom_map_zhuMul hφ hω]

theorem zhuMap_omegaL {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ)
    (hω : φ V.conformalVector = T.conformalVector) (p : A V) :
    zhuMap hφ hω (omegaL V p) = omegaL T (zhuMap hφ hω p) := by
  rw [omegaL, zhuMap_Amul, zhuMap_mk, hω]; rfl

theorem zhuMap_omegaL_pow {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ)
    (hω : φ V.conformalVector = T.conformalVector) (a : ℕ) (p : A V) :
    zhuMap hφ hω ((omegaL V ^ a) p) = (omegaL T ^ a) (zhuMap hφ hω p) := by
  induction a with
  | zero => rfl
  | succ a ih => rw [pow_succ', Module.End.mul_apply, zhuMap_omegaL, ih, pow_succ',
      Module.End.mul_apply]

theorem zhuMap_aeval {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ)
    (hω : φ V.conformalVector = T.conformalVector) (P : ℂ[X]) (p : A V) :
    zhuMap hφ hω ((aeval (omegaL V) P) p) = (aeval (omegaL T) P) (zhuMap hφ hω p) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add,
      hP, hQ]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul,
      zhuMap_omegaL_pow]

end ZhuMap

/-! ## `[ω]`-polynomials act by multiplication -/

section Mul
universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)

theorem omegaL_pow_eq_Amul (a : ℕ) (x : A W) :
    (omegaL W ^ a) x = Amul (zhuRingData_holds W) ((omegaL W ^ a) (mk W W.vacuum)) x := by
  induction a with
  | zero => exact (Amul_one_left (zhuRingData_holds W) x).symm
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply, ih, Module.End.mul_apply]
    exact (Amul_assoc (zhuRingData_holds W) _ _ _).symm

theorem aeval_omegaL_eq_Amul (P : ℂ[X]) (x : A W) :
    (aeval (omegaL W) P) x =
      Amul (zhuRingData_holds W) ((aeval (omegaL W) P) (mk W W.vacuum)) x := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, LinearMap.add_apply, LinearMap.add_apply, hP, hQ, map_add,
      LinearMap.add_apply]
  | monomial n c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, omegaL_pow_eq_Amul, map_smul,
      LinearMap.smul_apply]

end Mul

/-! ## The octahedral involution on the seeds -/

theorem sgnC_transposition : sgnC transposition = -1 := by
  have h : Perm.sign transposition = -1 := by decide
  simp [sgnC, h]

theorem autL_tv_gen (σ : Perm (Fin 4)) (i : Fin 4) :
    autL (octHom σ) (tv i) = sgnC σ • tv (σ i) := by
  apply xyzL_injective
  rw [xyzL_autL, ← tvec_eq, map_smul, ← tvec_eq]
  exact octFun_spec σ i

theorem phiE_ell_gen (σ : Perm (Fin 4)) (i : Fin 4) :
    phiE (octHom σ) (ell i) = sgnC σ • ell (σ i) := by
  rw [phiE_apply, ell, substL_lin, autL_tv_gen, map_smul, ell]

theorem phiE_psum_gen (σ : Perm (Fin 4)) (k : ℕ) :
    phiE (octHom σ) (psum k) = sgnC σ ^ k • psum k := by
  rw [psum, map_sum]
  simp only [map_pow, phiE_ell_gen, _root_.smul_pow]
  rw [← Finset.smul_sum]
  congr 1
  exact Equiv.sum_comp σ (fun i => ell i ^ k)

theorem phiE_rot2_I3 : phiE (octHom transposition) I3 = -I3 := by
  have hI3 : I3 = (24 : ℂ)⁻¹ • psum 3 := by
    rw [psum_three, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  rw [hI3, map_smul, phiE_psum_gen, sgnC_transposition,
    show ((-1 : ℂ)) ^ 3 = -1 by norm_num, neg_one_smul, smul_neg]

theorem phiE_rot2_r2 : phiE (octHom transposition) r2 = r2 := by
  have hr2 : r2 = (4 : ℂ)⁻¹ • psum 2 := by
    rw [psum_two, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  rw [hr2, map_smul, phiE_psum_gen, sgnC_transposition,
    show ((-1 : ℂ)) ^ 2 = 1 by norm_num, one_smul]

theorem phiE_rot2_I4 : phiE (octHom transposition) I4 = I4 := by
  have hI4 : I4 = (8 : ℂ)⁻¹ • ((12 : ℂ) • r2 ^ 2 - psum 4) := by
    rw [psum_four, sub_sub_cancel, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  rw [hI4, map_smul, map_sub, map_smul, map_pow, phiE_rot2_r2, phiE_psum_gen,
    sgnC_transposition, show ((-1 : ℂ)) ^ 4 = 1 by norm_num, one_smul]

/-- `τ` on the averaged model: `τ (T F) = T (φ(rot₂) F)` for `A₄`-invariant `F`. -/
theorem tetraInvolution_tT {F : P3} (hF : IsA4Inv F) (hF' : IsA4Inv (phiE (octHom transposition) F)) :
    tetraInvolution (tT F) = tT (phiE (octHom transposition) F) := by
  apply Subtype.ext
  change rot2 ((avgT tetra T2 F : (orbifold tetra).carrier) : LatModuleGen (latP 1)) =
    ((avgT tetra T2 (phiE (octHom transposition) F) : (orbifold tetra).carrier) :
      LatModuleGen (latP 1))
  rw [avgT_coe tetraV2Model hF, avgT_coe tetraV2Model hF', ← octHom_transposition,
    T2_equivariant]

theorem isA4Inv_neg {F : P3} (hF : IsA4Inv F) : IsA4Inv (-F) := by
  obtain ⟨f1, f2, f3⟩ := hF
  exact ⟨by rw [map_neg, f1], by rw [map_neg, f2], by rw [map_neg, f3]⟩

theorem tetraInvolution_U : tetraInvolution tetraU = -tetraU := by
  have h := tetraInvolution_tT isA4Inv_I3 (by rw [phiE_rot2_I3]; exact isA4Inv_neg isA4Inv_I3)
  rw [phiE_rot2_I3, map_neg] at h
  exact h

theorem tetraInvolution_V : tetraInvolution tetraV = tetraV := by
  have h := tetraInvolution_tT isA4Inv_I4 (by rw [phiE_rot2_I4]; exact isA4Inv_I4)
  rw [phiE_rot2_I4] at h
  exact h

/-! ## The involution on `A(W)` -/

theorem tau_hom : IsVOAHom Wt Wt tetraInvolution.toLinearEquiv.toLinearMap :=
  ⟨tetraInvolution.map_vacuum, tetraInvolution.map_smul'⟩

/-- `τ` on Zhu's algebra. -/
def tauA : A Wt →ₗ[ℂ] A Wt := zhuMap tau_hom tetraInvolution.map_omega

theorem tauA_omegaL_pow (a : ℕ) (p : A Wt) :
    tauA ((omegaL Wt ^ a) p) = (omegaL Wt ^ a) (tauA p) :=
  zhuMap_omegaL_pow tau_hom tetraInvolution.map_omega a p

theorem tauA_aeval (P : ℂ[X]) (p : A Wt) :
    tauA ((aeval (omegaL Wt) P) p) = (aeval (omegaL Wt) P) (tauA p) :=
  zhuMap_aeval tau_hom tetraInvolution.map_omega P p

theorem tauA_vac : tauA (mk Wt Wt.vacuum) = mk Wt Wt.vacuum := by
  change mk Wt (tetraInvolution Wt.vacuum) = _
  rw [tetraInvolution.map_vacuum]

theorem tauA_U : tauA (mk Wt tetraU) = -mk Wt tetraU := by
  change mk Wt (tetraInvolution tetraU) = _
  rw [tetraInvolution_U, map_neg]

theorem tauA_V : tauA (mk Wt tetraV) = mk Wt tetraV := by
  change mk Wt (tetraInvolution tetraV) = _
  rw [tetraInvolution_V]

/-! ## The even/odd split -/

/-- The even span: `[ω]^a` (`a ≤ 10`) and `[ω]^a [v]` (`a ≤ 1`). -/
def evenSpan : Submodule ℂ (A Wt) :=
  Submodule.span ℂ (Set.range fun a : Fin 11 => (omegaL Wt ^ (a : ℕ)) (mk Wt Wt.vacuum)) ⊔
    Submodule.span ℂ (Set.range fun a : Fin 2 => (omegaL Wt ^ (a : ℕ)) (mk Wt tetraV))

/-- The odd span: `[ω]^a [u]` (`a ≤ 10`). -/
def oddSpan : Submodule ℂ (A Wt) :=
  Submodule.span ℂ (Set.range fun a : Fin 11 => (omegaL Wt ^ (a : ℕ)) (mk Wt tetraU))

theorem even_odd_top : evenSpan ⊔ oddSpan = ⊤ := by
  have h := span_towers_A_eq_top Wt gSeed (fun i => (gWt i : ℤ)) gSeed_mem nR ![11, 11, 2]
    (towers_span_truncated tetraSixteenTruncation_holds) (by
      intro i a ha
      exact pow_mem_towerSub Wt _ (by fin_cases i <;> simpa [nR] using ha))
  apply top_unique
  rw [← h, Submodule.span_le]
  rintro _ ⟨⟨i, a⟩, rfl⟩
  fin_cases i
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩))
  · exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩)
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩))

theorem tauA_even {x : A Wt} (hx : x ∈ evenSpan) : tauA x = x := by
  have h1 : ∀ y ∈ Submodule.span ℂ (Set.range fun a : Fin 11 =>
      (omegaL Wt ^ (a : ℕ)) (mk Wt Wt.vacuum)), tauA y = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨a, rfl⟩ := hy; rw [tauA_omegaL_pow, tauA_vac]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  have h2 : ∀ y ∈ Submodule.span ℂ (Set.range fun a : Fin 2 =>
      (omegaL Wt ^ (a : ℕ)) (mk Wt tetraV)), tauA y = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨a, rfl⟩ := hy; rw [tauA_omegaL_pow, tauA_V]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, h1 a ha, h2 b hb]

theorem tauA_odd {x : A Wt} (hx : x ∈ oddSpan) : tauA x = -x := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; rw [tauA_omegaL_pow, tauA_U, map_neg]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, neg_add]
  | smul c x _ hx => rw [map_smul, hx, smul_neg]

/-- `τ`-fixed classes lie in the even span. -/
theorem mem_evenSpan_of_fixed {x : A Wt} (hx : tauA x = x) : x ∈ evenSpan := by
  have hx' : x ∈ evenSpan ⊔ oddSpan := by rw [even_odd_top]; trivial
  obtain ⟨e, he, o, ho, rfl⟩ := Submodule.mem_sup.mp hx'
  rw [map_add, tauA_even he, tauA_odd ho] at hx
  have ho0 : o = 0 := by
    have hno : -o = o := add_left_cancel hx
    have h2 : (2 : ℂ) • o = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hno]
      exact neg_add_cancel o
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  rw [ho0, add_zero]; exact he

theorem finrank_evenSpan_le : Module.finrank ℂ evenSpan ≤ 13 := by
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun a : Fin 11 =>
      (omegaL Wt ^ (a : ℕ)) (mk Wt Wt.vacuum))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun a : Fin 2 =>
      (omegaL Wt ^ (a : ℕ)) (mk Wt tetraV))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
  have h1 := finrank_range_le_card (R := ℂ)
    (fun a : Fin 11 => (omegaL Wt ^ (a : ℕ)) (mk Wt Wt.vacuum))
  have h2 := finrank_range_le_card (R := ℂ)
    (fun a : Fin 2 => (omegaL Wt ^ (a : ℕ)) (mk Wt tetraV))
  simp only [Fintype.card_fin, Set.finrank] at h1 h2
  omega

/-! ## Thirteen characters -/

/-- The 13 distinct lowest weights. -/
def lamQ : Fin 13 → ℚ := ![4, 9/4, 1/36, 25/36, 49/36, 1/9, 4/9, 16/9, 0, 1, 1/4, 1/16, 9/16]

/-- Their positions in `tetraWeight`. -/
def lamIdx : Fin 13 → Fin 21 := ![2, 5, 9, 10, 11, 12, 13, 14, 0, 1, 4, 7, 8]

theorem lamIdx_spec : ∀ j, tetraWeightQ (lamIdx j) = lamQ j := by decide +kernel

theorem lamQ_injective : Function.Injective lamQ := by decide +kernel

def lam (j : Fin 13) : ℂ := (lamQ j : ℂ)

theorem lam_injective : Function.Injective lam := fun i j h =>
  lamQ_injective (Rat.cast_injective (α := ℂ) h)

theorem tetraWeight_lamIdx (j : Fin 13) : tetraWeight (lamIdx j) = lam j := by
  rw [tetraWeight, lamIdx_spec]; rfl

/-- The 21 characters of `A(cubicModel)`, pulled back to `A(W)`. -/
theorem exists_psi : ∃ ψ : Fin 21 → (A Wt →ₗ[ℂ] ℂ),
    (∀ i p q, ψ i (Amul (zhuRingData_holds Wt) p q) = ψ i p * ψ i q) ∧
    (∀ i, ψ i (mk Wt Wt.vacuum) = 1) ∧
    (∀ i, ψ i (mk Wt Wt.conformalVector) = tetraWeight i) := by
  obtain ⟨χ, -, hχ⟩ := OrbRat6.cubicZhuCharacterTable_holds
  obtain ⟨e, he, hω⟩ := tetra_cubic_iso
  have hs := ConverseUniverse.isVOAHom_symm' e he
  have hω' : e.symm Wt.conformalVector = cubicModel.conformalVector := by
    rw [← hω, LinearEquiv.symm_apply_apply]
  let f := zhuMap hs hω'
  letI := instRingA cubicModel
  letI := instAlgebraA cubicModel
  refine ⟨fun i => (χ i).toLinearMap ∘ₗ f, ?_, ?_, ?_⟩
  · intro i p q
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
    rw [zhuMap_Amul]
    exact map_mul (χ i) (f p) (f q)
  · intro i
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
    rw [zhuMap_mk, hs.map_vacuum]
    exact map_one (χ i)
  · intro i
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
    rw [zhuMap_mk, LinearEquiv.coe_coe, hω']
    exact hχ i

/-- `q₁₃ = P₈ · P₅`. -/
def dblQ : Fin 8 → ℚ := ![4, 9/4, 1/36, 25/36, 49/36, 1/9, 4/9, 16/9]
def sglQ : Fin 5 → ℚ := ![0, 1, 1/4, 1/16, 9/16]

/-- The doubled weights. -/
def P8 : ℂ[X] := ∏ i : Fin 8, (X - Polynomial.C ((dblQ i : ℚ) : ℂ))
/-- The single weights. -/
def P5 : ℂ[X] := ∏ i : Fin 5, (X - Polynomial.C ((sglQ i : ℚ) : ℂ))

theorem P8_monic : P8.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _

theorem P8_natDegree : P8.natDegree = 8 := by
  rw [P8, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
  simp

theorem eval_P8P5 (j : Fin 13) : (P8 * P5).eval (lam j) = 0 := by
  rw [eval_mul, P8, P5, eval_prod, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  fin_cases j
  · exact mul_eq_zero_of_left (Finset.prod_eq_zero (i := 0) (Finset.mem_univ _)
      (by simp [lam, lamQ, dblQ])) _
  · exact mul_eq_zero_of_left (Finset.prod_eq_zero (i := 1) (Finset.mem_univ _)
      (by simp [lam, lamQ, dblQ])) _
  · exact mul_eq_zero_of_left (Finset.prod_eq_zero (i := 2) (Finset.mem_univ _)
      (by simp [lam, lamQ, dblQ])) _
  · exact mul_eq_zero_of_left (Finset.prod_eq_zero (i := 3) (Finset.mem_univ _)
      (by simp [lam, lamQ, dblQ])) _
  · exact mul_eq_zero_of_left (Finset.prod_eq_zero (i := 4) (Finset.mem_univ _)
      (by simp [lam, lamQ, dblQ])) _
  · exact mul_eq_zero_of_left (Finset.prod_eq_zero (i := 5) (Finset.mem_univ _)
      (by simp [lam, lamQ, dblQ])) _
  · exact mul_eq_zero_of_left (Finset.prod_eq_zero (i := 6) (Finset.mem_univ _)
      (by simp [lam, lamQ, dblQ])) _
  · exact mul_eq_zero_of_left (Finset.prod_eq_zero (i := 7) (Finset.mem_univ _)
      (by simp [lam, lamQ, dblQ])) _
  · exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := 0) (Finset.mem_univ _)
      (by simp [lam, lamQ, sglQ]))
  · exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := 1) (Finset.mem_univ _)
      (by simp [lam, lamQ, sglQ]))
  · exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := 2) (Finset.mem_univ _)
      (by simp [lam, lamQ, sglQ]))
  · exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := 3) (Finset.mem_univ _)
      (by simp [lam, lamQ, sglQ]))
  · exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := 4) (Finset.mem_univ _)
      (by simp [lam, lamQ, sglQ]))

/-- A character evaluates `[ω]`-polynomials on `1` at its lowest weight. -/
theorem psi_aeval {ψ : A Wt →ₗ[ℂ] ℂ}
    (hmul : ∀ p q, ψ (Amul (zhuRingData_holds Wt) p q) = ψ p * ψ q)
    (h1 : ψ (mk Wt Wt.vacuum) = 1) {w : ℂ} (hw : ψ (mk Wt Wt.conformalVector) = w)
    (P : ℂ[X]) : ψ ((aeval (omegaL Wt) P) (mk Wt Wt.vacuum)) = P.eval w := by
  have hpow : ∀ a : ℕ, ψ ((omegaL Wt ^ a) (mk Wt Wt.vacuum)) = w ^ a := by
    intro a
    induction a with
    | zero => simpa using h1
    | succ a ih =>
      rw [pow_succ', Module.End.mul_apply]
      change ψ (Amul (zhuRingData_holds Wt) (mk Wt Wt.conformalVector)
        ((omegaL Wt ^ a) (mk Wt Wt.vacuum))) = _
      rw [hmul, hw, ih, pow_succ, mul_comm]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, LinearMap.add_apply, map_add, hP, hQ, eval_add]
  | monomial n c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, hpow,
      eval_monomial, smul_eq_mul]

/-- **`q₁₃([ω]) = 0` in `A(V₂^{A₄})`.** -/
theorem q13_omega_eq_zero : (aeval (omegaL Wt) (P8 * P5)) (mk Wt Wt.vacuum) = 0 := by
  obtain ⟨ψ, hmul, h1, hw⟩ := exists_psi
  let w : Fin 13 → A Wt := fun a => (omegaL Wt ^ (a : ℕ)) (mk Wt Wt.vacuum)
  have hψw : ∀ (j : Fin 13) (P : ℂ[X]),
      ψ (lamIdx j) ((aeval (omegaL Wt) P) (mk Wt Wt.vacuum)) = P.eval (lam j) := by
    intro j P
    rw [psi_aeval (hmul _) (h1 _) (hw _) P, tetraWeight_lamIdx]
  have hV : (Matrix.vandermonde lam).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr lam_injective
  -- the values of the 13 characters on a combination of the `w a`
  have hcomb : ∀ (d : Fin 13 → ℂ) (j : Fin 13),
      ψ (lamIdx j) (∑ a, d a • w a) = Matrix.mulVec (Matrix.vandermonde lam) d j := by
    intro d j
    show _ = ∑ a, Matrix.vandermonde lam j a * d a
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, smul_eq_mul, Matrix.vandermonde_apply, mul_comm]
    congr 1
    have := hψw j (X ^ (a : ℕ))
    simpa [w] using this
  -- independence
  have hind : LinearIndependent ℂ w := by
    rw [Fintype.linearIndependent_iff]
    intro d hd
    have hz : Matrix.mulVec (Matrix.vandermonde lam) d = 0 := by
      funext j
      rw [← hcomb, hd, map_zero]; rfl
    have := Matrix.eq_zero_of_mulVec_eq_zero hV hz
    intro a; rw [this]; rfl
  -- all `w a` and `q₁₃([ω])·1` are `τ`-fixed, hence in the even span
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
  have hq := hfixed (P8 * P5)
  rw [← hspan_eq] at hq
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hq
  have hz : Matrix.mulVec (Matrix.vandermonde lam) d = 0 := by
    funext j
    rw [← hcomb, hd, hψw, eval_P8P5]; rfl
  have hd0 := Matrix.eq_zero_of_mulVec_eq_zero hV hz
  rw [← hd, hd0]
  simp

/-! ## The odd residual -/

/-- OPEN (true; the associativity identity `([u]*[v])*[v] = [u]*([v]*[v])` supplies an
explicit degree-16 `R`, numerically nonzero exactly off the 8 doubled weights, by a
computation outside Lean): some `[ω]`-polynomial nonvanishing at the five single
lowest weights `0, 1, 1/4, 1/16, 9/16` annihilates `[u]` in `A(W)`. -/
def TetraOddAnnihilator : Prop :=
  ∃ R : ℂ[X], (∀ i : Fin 5, R.eval ((sglQ i : ℚ) : ℂ) ≠ 0) ∧
    (aeval (omegaL Wt) R) (mk Wt tetraU) = 0

theorem q13_kills_U : (aeval (omegaL Wt) (P8 * P5)) (mk Wt tetraU) = 0 := by
  rw [aeval_omegaL_eq_Amul, q13_omega_eq_zero, map_zero, LinearMap.zero_apply]

theorem isCoprime_P5 {R : ℂ[X]} (hR : ∀ i : Fin 5, R.eval ((sglQ i : ℚ) : ℂ) ≠ 0) :
    IsCoprime P5 R := by
  rw [P5]
  apply IsCoprime.prod_left
  intro i _
  rw [(Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd, Polynomial.dvd_iff_isRoot]
  exact hR i

/-- The odd residual of `OrbZhuBound` from a single annihilator. -/
theorem tetraOddZhuRelation_of_annihilator (h : TetraOddAnnihilator) : TetraOddZhuRelation := by
  obtain ⟨R, hR, hRu⟩ := h
  obtain ⟨a, b, hab⟩ := isCoprime_P5 hR
  refine ⟨P8, P8_monic, P8_natDegree.le, ?_⟩
  have hP : P8 = a * (P8 * P5) + (P8 * b) * R := by
    calc P8 = P8 * (a * P5 + b * R) := by rw [hab, mul_one]
      _ = a * (P8 * P5) + (P8 * b) * R := by ring
  have e1 : (aeval (omegaL Wt) (a * (P8 * P5))) (mk Wt tetraU) =
      (aeval (omegaL Wt) a) ((aeval (omegaL Wt) (P8 * P5)) (mk Wt tetraU)) := by
    rw [map_mul, Module.End.mul_apply]
  have e2 : (aeval (omegaL Wt) (P8 * b * R)) (mk Wt tetraU) =
      (aeval (omegaL Wt) (P8 * b)) ((aeval (omegaL Wt) R) (mk Wt tetraU)) := by
    rw [map_mul, Module.End.mul_apply]
  rw [hP, map_add, LinearMap.add_apply, e1, e2, q13_kills_U, hRu, map_zero, map_zero, add_zero]

/-- `CubicZhuDimensionBound` from the single odd annihilator. -/
theorem cubicZhuDimensionBound_of_annihilator (h : TetraOddAnnihilator) :
    CubicZhuDimensionBound :=
  cubicZhuDimensionBound_of_oddRelation (tetraOddZhuRelation_of_annihilator h)

end VOA.Classification.COne.OrbZhu
