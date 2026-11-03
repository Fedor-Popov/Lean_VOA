import VOA.Classification.COne.PlusSplitTopCharacters
import VOA.Classification.COne.PlusSplitZhuGeneration

/-! # Unconditional charged lattice top characters

A common eigenline for algebra generators is an eigenline for the algebra.
Applied to the existing restricted lattice modules, this constructs the
charged characters without assuming their plus-irreducibility or the dimension
of the entire bottom. The vector is the actual pure exponential e^(lambda_r).
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusCharacterTable
open PlusUnitary LatMod VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice

section Eigenline
variable {K R X I : Type*} [Field K] [Ring R] [Algebra K R]
  [AddCommGroup X] [Module K X]

/-- The character of a common eigenline for a generating family. -/
theorem exists_character_of_generator_eigenvector (g : I → R)
    (hgen : Algebra.adjoin K (Set.range g) = ⊤)
    (ρ : R →ₐ[K] Module.End K X) (x : X) (hx : x ≠ 0)
    (v : I → K) (hv : ∀ i, ρ (g i) x = v i • x) :
    ∃ χ : R →ₐ[K] K, ∀ i, χ (g i) = v i := by
  have hall : ∀ a : R, ∃ c : K, ρ a x = c • x := by
    intro a
    have ha : a ∈ Algebra.adjoin K (Set.range g) := by rw [hgen]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem a ha => obtain ⟨i, rfl⟩ := ha; exact ⟨v i, hv i⟩
    | algebraMap c => exact ⟨c, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha; obtain ⟨d, hd⟩ := hb
      exact ⟨c+d, by simp [hc, hd, add_smul]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha; obtain ⟨d, hd⟩ := hb
      exact ⟨c*d, by simp [Module.End.mul_apply, hd, hc, smul_smul, mul_comm]⟩
  obtain ⟨ell, hell⟩ := Module.Projective.exists_dual_eq_one K hx
  let f : R →ₗ[K] K := ell.comp ((LinearMap.applyₗ x).comp ρ.toLinearMap)
  have hρ (a : R) : ρ a x = f a • x := by
    obtain ⟨c, hc⟩ := hall a
    have hf : f a = c := by change ell (ρ a x) = c; rw [hc]; simp [hell]
    rw [hf]; exact hc
  have h1 : f 1 = 1 := by change ell (ρ 1 x) = 1; simp [hell]
  have hmul (a b : R) : f (a*b) = f a * f b := by
    change ell (ρ (a*b) x) = _
    rw [map_mul, Module.End.mul_apply, hρ b, map_smul, map_smul]
    change f b * f a = f a * f b
    exact mul_comm _ _
  refine ⟨AlgHom.ofLinearMap f h1 hmul, fun i => ?_⟩
  change ell (ρ (g i) x) = v i
  rw [hv i]; simp [hell]
end Eigenline

/-- Any common top eigenvector gives a plus Zhu character with those values. -/
theorem character_of_plus_top_vector (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (V2mPlus m hm) M) {h : ℂ} (hlow : IsLowestWeight N h)
    (x : M) (hx : x ∈ N.weight h) (hx0 : x ≠ 0) (v : Fin 3 → ℂ)
    (hv : ∀ i, oMod N (gP m hm i) x = v i • x) :
    letI := instRingA (V2mPlus m hm); letI := instAlgebraA (V2mPlus m hm)
    ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ,
      ∀ i, χ (VOA.mk (V2mPlus m hm) (gP m hm i)) = v i := by
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  let ρ : VOA.A (V2mPlus m hm) →ₐ[ℂ] Module.End ℂ (N.weight h) :=
    AlgHom.ofLinearMap (actA N hlow) (actA_one N hlow)
      (actA_mul (zhuRingData_holds _) hlow)
  apply exists_character_of_generator_eigenvector
    (fun i => VOA.mk (V2mPlus m hm) (gP m hm i))
    (V2mPlus_zhu_adjoin_generators m hm hm2) ρ ⟨x, hx⟩
    (fun he => hx0 (congrArg Subtype.val he)) v
  intro i
  apply Subtype.ext
  change (actA N hlow (VOA.mk (V2mPlus m hm) (gP m hm i)) ⟨x, hx⟩ : M) = _
  rw [actA_mk_apply_coe]
  exact hv i

/-- The m-1 charged characters are constructed from the existing lattice modules. -/
theorem charged_character_exists (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (r : Fin (m - 1)) :
    letI := instRingA (V2mPlus m hm); letI := instAlgebraA (V2mPlus m hm)
    ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ, HasValues m hm (.inl r) χ := by
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  let j : ℤ := r.val + 1
  have hj : |j| < (m : ℤ) := by
    rw [abs_of_nonneg (by dsimp [j]; omega)]
    have := r.isLt
    dsimp [j]; omega
  let h : ℂ := ((((j : ℝ)^2/(4*m) : ℝ)) : ℂ)
  let N := resN m hm (latticeModule m hm j)
  have hlow : IsLowestWeight N h := latticeModule_isLowestWeight m hm j hj.le
  have hx : latVacuumGen (latP m) ∈ N.weight h := latticeModule_vacuum_mem m hm j
  have hW : oMod N (WP m hm) (latVacuumGen (latP m)) = (2*h) • latVacuumGen (latP m) := by
    rw [oMod_resN m hm _ (WP_mem_grading m hm), WP_coe]
    exact oMod_W_V2m m hm _ hlow hx
  have hE : oMod N (EP m hm) (latVacuumGen (latP m)) = 0 := by
    rw [oMod_resN m hm _ (EP_mem_grading m hm)]
    exact oMod_E_lat_vac m hm j hj
  obtain ⟨χ, hχ⟩ := character_of_plus_top_vector m hm hm2 N hlow
    (latVacuumGen (latP m)) hx (latVacuumGen_ne_zero' m hm) ![h, 2*h, 0] (by
      intro i; fin_cases i
      · change oMod N (V2mPlus m hm).conformalVector _ = h • _
        rw [oMod_conformalVector]; exact N.L0_weight _ _ hx
      · exact hW
      · simpa using hE)
  refine ⟨χ, ?_, ?_, ?_⟩
  · convert hχ 0 using 1; simp [values, h, j]
  · convert hχ 1 using 1; simp [values, h, j, Complex.ofReal_mul]
  · exact hχ 2

/-- The vacuum character is constructed from the adjoint plus module. -/
theorem vacuum_character_exists (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    letI := instRingA (V2mPlus m hm); letI := instAlgebraA (V2mPlus m hm)
    ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ, HasValues m hm (.inr 0) χ := by
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  obtain ⟨χ, hχ⟩ := character_of_plus_top_vector m hm hm2
    (adjointModule (V2mPlus m hm)) (isLowestWeight_adjoint _)
    (V2mPlus m hm).vacuum (vacuum_mem_adjoint_weight _)
    (fun hz => latVacuumGen_ne_zero' m hm (congrArg Subtype.val hz))
    (fun _ => 0) (by
      intro i
      simpa using oMod_adjoint_vacuum (V2mPlus m hm)
        (show 1 ≤ (wtP m i : ℤ) by fin_cases i <;> simp [wtP]; omega)
        (gP_mem_grading m hm i))
  exact ⟨χ, hχ 0, hχ 1, hχ 2⟩

end VOA.Classification.COne.PlusCharacterTable

namespace VOA.Classification.COne
open PlusCharacterTable

/-- OPEN: only the sign and two half-lattice top models. The vacuum and
m-1 charged characters require no existence input. -/
def V2mPlusSignHalfTopModels : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → ∀ i : Fin 8,
    1 ≤ i.val → i.val < 4 → TopModel m hm (.inr i)

theorem zhuDistinctCharacters_of_signHalf_twisted
    (hs : V2mPlusSignHalfTopModels) (ht : V2mPlusTwistedTopModels) :
    V2mPlusZhuDistinctCharacters := by
  classical
  intro m hm hm2
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  have hex : ∀ i : Label m, ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ,
      HasValues m hm i χ := by
    rintro (r | i)
    · exact charged_character_exists m hm hm2 r
    · by_cases hi : i = 0
      · subst i; exact vacuum_character_exists m hm hm2
      · apply character_exists_of_topModel
        by_cases hi4 : i.val < 4
        · have hi0 : 0 < i.val := Nat.pos_of_ne_zero (by
            intro h; apply hi; exact Fin.ext h)
          exact hs m hm hm2 i hi0 hi4
        · exact ht m hm hm2 (.inr i) hi4
  choose χ hχ using hex
  let e : Label m ≃ Fin (m+7) := Fintype.equivFinOfCardEq (card_label m hm)
  exact ⟨χ ∘ e.symm, (characters_injective m hm hm2 χ hχ).comp e.symm.injective⟩

end VOA.Classification.COne
