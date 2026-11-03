import VOA.Classification.COne.PlusRat5E

/-! # Tops of the kernel and of the quotient in an extension of `V_{2m}⁺`-modules

* `low_mem_P'`: generalized weight vectors below the quotient bottom lie in the kernel.
* `quot_top_zero`: if every table row of the quotient-bottom weight `h'` kills `H^{2t}` in Zhu's
  algebra, then `o(H^{2t})` maps every `h'`-eigenvector of the extension into the kernel.
* `exists_pure_top`: a nonzero top vector produces a nonzero top vector, obtained by a zero mode,
  whose Zhu character is a single table row.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat5
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3 PlusRat4 PlusRational

section Ext
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus m hm) M) (P : Submodule (modeAlg A) M)

theorem low_mem_P' {h' : ℂ} (hbQ : FactorBottom A P ⊤ h') {v : M} {μ : ℂ}
    (hv : v ∈ (L0 A).maxGenEigenspace μ) (hμ : μ.re < h'.re) : v ∈ P := by
  by_contra h
  have hw : FactorWeight A P ⊤ μ := fun ht => h (ht ⟨Submodule.mem_top, hv⟩)
  have := hbQ.2 μ hw
  linarith

theorem oLevW_mem (a : VP m hm) {y : M} (hy : y ∈ P) : oLevW A 0 a y ∈ P := by
  have ha : a ∈ ⨆ k, (V2mPlus m hm).grading k := by
    rw [(V2mPlus m hm).isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction _ (motive := fun a => oLevW A 0 a y ∈ P) ha ?_ ?_ ?_
  · intro k b hb
    rw [oLevW_homogeneous A 0 hb]
    exact P.smul_mem (⟨mode (A.YM b) (k - 1 + 0), Algebra.subset_adjoin ⟨b, _, rfl⟩⟩ : modeAlg A) hy
  · simp
  · intro a b ha hb
    rw [map_add, LinearMap.add_apply]
    exact P.add_mem ha hb

include hm2 in
/-- The quotient top is killed by `o(H^{2t})` modulo the kernel when its rows are. -/
theorem quot_top_zero {h' : ℂ} (hbQ : FactorBottom A P ⊤ h') {x : M} (hx : L0 A x = h' • x)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ 4)
    (hrows : ∀ l : Label m, ((weight m l : ℚ) : ℂ) = h' →
      chiT m hm hm2 l (VOA.mk (V2mPlus m hm) (HP m hm t)) = 0) :
    mode (A.YM (HP m hm t)) (2 * t - 1) x ∈ P := by
  let Q : WeakModule (V2mPlus m hm) (M ⧸ (ofR A P).carrier) := WeakModule.quotient A (ofR A P)
  have hmk : ∀ (a : VP m hm) (n : ℤ) (y : M), mode (Q.YM a) n (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (mode (A.YM a) n y) := by
    intro a n y
    have := WeakModule.quotient_act_mk A (ofR A P) a n y
    simpa only [WeakModule.act_def] using this
  have hxg : x ∈ (L0 A).maxGenEigenspace h' :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hx)
  have hΩ : (Submodule.Quotient.mk x : M ⧸ (ofR A P).carrier) ∈ Omega Q := by
    intro β v hv n hn
    rw [hmk]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply low_mem_P' m hm A P hbQ (mode_mem_maxGenEigenspace A hv n hxg)
    simp only [Complex.add_re, Complex.intCast_re]
    have : ((β - n - 1 : ℤ) : ℝ) < 0 := by exact_mod_cast (show β - n - 1 < 0 by omega)
    linarith
  have hL : L0 Q (Submodule.Quotient.mk x) = h' • (Submodule.Quotient.mk x) := by
    change mode (Q.YM (V2mPlus m hm).conformalVector) 1 _ = _
    rw [hmk]
    change Submodule.Quotient.mk (L0 A x) = _
    rw [hx, Submodule.Quotient.mk_smul]
  have h0 := top_eval_zero_of_rows m hm hm2 Q hΩ hL (VOA.mk (V2mPlus m hm) (HP m hm t)) hrows
  rw [topEvaluation_mk, oLevW_homogeneous Q 0 (HP_mem_grading m hm t ht.1 ht.2), hmk] at h0
  have h1 := (Submodule.Quotient.mk_eq_zero _).mp h0
  rw [show ((2 * t : ℕ) : ℤ) - 1 + 0 = 2 * (t : ℤ) - 1 by push_cast; ring] at h1
  exact h1

include hm2 in
/-- **Pure tops.**  A nonzero top vector `y` of `P` (in the `c`-eigenspace) yields a nonzero
top vector `z = o(a) y ∈ P` whose Zhu character is a single table row. -/
theorem exists_pure_top {y : M} (hyP : y ∈ P) (hy : y ∈ Omega A) (hy0 : y ≠ 0) {c : ℂ}
    (hL : L0 A y = c • y)
    (hΩ : ∀ z ∈ P, L0 A z = c • z → z ∈ Omega A) :
    ∃ (l : Label m) (z : M) (hz : z ∈ Omega A), z ∈ P ∧ z ≠ 0 ∧ L0 A z = c • z ∧
      ∀ r, topEvaluation A z hz r = chiT m hm hm2 l r • z := by
  classical
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  set χ := chiT m hm hm2
  letI := finiteDimensional_A_of_C2Cofinite _ (V2mPlus_c2Cofinite m hm)
  have hdim : Module.finrank ℂ (VOA.A (V2mPlus m hm)) ≤ Fintype.card (Label m) := by
    rw [V2mPlus_zhu_finrank m hm hm2, card_label m hm]
  let e := characterAlgEquiv χ (chiT_injective m hm hm2) hdim
  have he_apply : ∀ r j, e r j = χ j r := fun _ _ => rfl
  let ε : Label m → VOA.A (V2mPlus m hm) := fun l => e.symm (fun j => if j = l then 1 else 0)
  set f := topEvaluation A y hy
  have hsum : ∑ l, ε l = 1 := by
    apply e.injective
    rw [map_sum, map_one]
    funext j
    simp only [ε, AlgEquiv.apply_symm_apply, Finset.sum_apply, Pi.one_apply]
    simp
  have hyf : f 1 = y := by
    obtain ⟨one, hone⟩ := VOA.mk_surjective (V2mPlus m hm) (1 : VOA.A (V2mPlus m hm))
    have : f 1 = y := by
      rw [← topEvaluation_one A y hy]
    exact this
  have hex : ∃ l, f (ε l) ≠ 0 := by
    by_contra hne
    push Not at hne
    apply hy0
    rw [← hyf, ← hsum, map_sum]
    exact Finset.sum_eq_zero (fun l _ => hne l)
  obtain ⟨l, hl⟩ := hex
  obtain ⟨a, ha⟩ := VOA.mk_surjective (V2mPlus m hm) (ε l)
  set z := f (ε l) with hz
  have hzo : z = oLevW A 0 a y := by rw [hz, ← ha, topEvaluation_mk]
  have hrε : ∀ r, r * ε l = χ l r • ε l := by
    intro r
    apply e.injective
    funext j
    rw [map_mul, map_smul]
    simp only [ε, AlgEquiv.apply_symm_apply, Pi.mul_apply, Pi.smul_apply, he_apply, smul_eq_mul]
    by_cases hj : j = l
    · subst hj; simp
    · simp [hj]
  have hcomm : ∀ r, r * ε l = ε l * r := by
    intro r
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  have hzL : L0 A z = c • z := by
    have h1 := topEvaluation_mk_mul A y hy (V2mPlus m hm).conformalVector (ε l)
    have h2 := topEvaluation_mk_mul A y hy a (VOA.mk (V2mPlus m hm) (V2mPlus m hm).conformalVector)
    rw [topEvaluation_mk, oLevW_homogeneous A 0 (V2mPlus m hm).conformal_mem,
      show (2 : ℤ) - 1 + 0 = 1 by norm_num] at h2
    have hy1 : mode (A.YM (V2mPlus m hm).conformalVector) 1 y = c • y := hL
    rw [hy1, map_smul, ← hzo] at h2
    rw [hcomm, ← ha, h2] at h1
    rw [ha, ← hz, oLevW_homogeneous A 0 (V2mPlus m hm).conformal_mem,
      show (2 : ℤ) - 1 + 0 = 1 by norm_num] at h1
    exact h1.symm
  have hzΩ := hΩ z (by rw [hzo]; exact oLevW_mem m hm A P a hyP) hzL
  refine ⟨l, z, hzΩ, by rw [hzo]; exact oLevW_mem m hm A P a hyP, hl, hzL, ?_⟩
  intro r
  obtain ⟨b, rfl⟩ := VOA.mk_surjective (V2mPlus m hm) r
  rw [topEvaluation_mk]
  have h2 := topEvaluation_mk_mul A y hy b (ε l)
  rw [hrε, map_smul] at h2
  rw [← h2]

end Ext

end VOA.Classification.COne.PlusRat5
