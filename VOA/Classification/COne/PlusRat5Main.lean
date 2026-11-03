import VOA.Classification.COne.PlusRat5Model

/-! # The uniform splitting theorem for `V_{2m}⁺` (Abe's route, Math. Z. 249 (2005), §§4-7)

`split_uniform`: let `0 → P → M → M/P → 0` be an extension of weak `V_{2m}⁺`-modules with simple
kernel `P` of bottom `h` and simple quotient of bottom `h' = h + d`, `d ≥ 1`.  Assume

* every table row of weight `h'` kills `H⁴` and `H⁶` in Zhu's algebra (charged and half rows);
* `(m+n)² > 4mh'` for `n ≥ 1` (true for charged and half quotients);
* every table row of weight `h` has a Fock model (`ModelSpec`, adapted to `h'`).

Then the extension splits.  No per-gap computation: the lift `u` of the quotient top with
`o(H⁴)u = o(H⁶)u = 0` is a top vector by Abe's Lemma 4.8 (`m1plus_chain`) and the `E`-lowering
induction (`oH4_Y`), whose only inputs are the joint spectra of the models.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat5
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3 PlusRat4 PlusRational

section Helpers
variable (m : ℕ) (hm : 1 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus m hm) M)

/-- An honest eigenvector inside a mode submodule from a generalized one. -/
theorem exists_eigen_in (P : Submodule (modeAlg A) M) {y : M} (hyP : y ∈ P) {h : ℂ}
    (hy : y ∈ (L0 A).maxGenEigenspace h) (hy0 : y ≠ 0) :
    ∃ y' : M, y' ∈ P ∧ y' ≠ 0 ∧ L0 A y' = h • y' := by
  classical
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hy
  set f := L0 A - h • (1 : Module.End ℂ M) with hf
  have hex : ∃ j : ℕ, (f ^ (j + 1)) y = 0 := ⟨k, by
    rw [show k + 1 = 1 + k by ring, pow_add, Module.End.mul_apply, hk, map_zero]⟩
  let j := Nat.find hex
  have hj : (f ^ (j + 1)) y = 0 := Nat.find_spec hex
  have hj0 : (f ^ j) y ≠ 0 := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, pow_zero]; exact hy0
    · have := Nat.find_min hex (show j - 1 < j by omega)
      rwa [Nat.sub_add_cancel h0] at this
  have hfP : ∀ i : ℕ, (f ^ i) y ∈ P := by
    intro i
    induction i with
    | zero => simpa using hyP
    | succ i ih =>
      rw [pow_succ', Module.End.mul_apply]
      have hL : L0 A ((f ^ i) y) ∈ P :=
        P.smul_mem (⟨L0 A, Algebra.subset_adjoin ⟨(V2mPlus m hm).conformalVector, 1, rfl⟩⟩ : modeAlg A) ih
      change L0 A ((f ^ i) y) - h • (1 : Module.End ℂ M) ((f ^ i) y) ∈ P
      exact P.sub_mem hL (P.smul_mem (algebraMap ℂ (modeAlg A) h) (by simpa using ih))
  refine ⟨(f ^ j) y, hfP j, hj0, ?_⟩
  have h1 : f ((f ^ j) y) = 0 := by rw [← Module.End.mul_apply, ← pow_succ']; exact hj
  change L0 A ((f ^ j) y) - h • (1 : Module.End ℂ M) ((f ^ j) y) = 0 at h1
  rw [Module.End.one_apply] at h1
  exact sub_eq_zero.mp h1

theorem evalW_lin (y : M) :
    evalW A (polyW (aL m hm) (bL m hm) [(1, 1, 0)]) y = mode (A.YM (HP m hm 2)) 3 y := by
  simp [polyW, evalW, homogeneousWord, aL]

theorem evalW_P1 (y : M) :
    evalW A (polyW (aL m hm) (bL m hm) [(5, 2, 0), (-5, 1, 0), (9, 0, 1), (-1, 0, 0)]) y =
      (5 : ℂ) • mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 2)) 3 y) -
        (5 : ℂ) • mode (A.YM (HP m hm 2)) 3 y + (9 : ℂ) • mode (A.YM (HP m hm 3)) 5 y - y := by
  simp only [polyW, evalW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.replicate, List.nil_append, List.cons_append, homogeneousWord, LinearMap.comp_apply,
    LinearMap.id_apply, aL, bL]
  module

theorem evalW_P2 (y : M) :
    evalW A (polyW (aL m hm) (bL m hm) [(1, 1, 0), (2, 0, 0)]) y =
      mode (A.YM (HP m hm 2)) 3 y + (2 : ℂ) • y := by
  simp only [polyW, evalW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.replicate, List.nil_append, List.cons_append, homogeneousWord, LinearMap.comp_apply,
    LinearMap.id_apply, aL, bL]
  module

theorem evalW_PE (c1 c0 : ℂ) (y : M) :
    evalW A (polyW (aL m hm) (bL m hm) [(c1, 1, 0), (c0, 0, 0)]) y =
      c1 • mode (A.YM (HP m hm 2)) 3 y + c0 • y := by
  simp only [polyW, evalW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.replicate, List.nil_append, List.cons_append, homogeneousWord, LinearMap.comp_apply,
    LinearMap.id_apply, aL, bL]
  module

end Helpers

section Main
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)

theorem polyV_P1_ne (s t : ℕ) :
    polyV [((5 : ℂ), 2, 0), (-5, 1, 0), (9, 0, 1), (-1, 0, 0)] (s : ℂ) (t : ℂ) ≠ 0 := by
  simp only [polyV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  intro h
  have hz : (5 * (s : ℤ) ^ 2 - 5 * s + 9 * t - 1 : ℤ) = 0 := by
    have : ((5 * (s : ℤ) ^ 2 - 5 * s + 9 * t - 1 : ℤ) : ℂ) = 0 := by
      push_cast; linear_combination h
    exact_mod_cast this
  rcases Nat.lt_or_ge s 2 with hs | hs
  · interval_cases s <;> omega
  · have : (2 : ℤ) ≤ s := by exact_mod_cast hs
    nlinarith

theorem polyV_P2_ne (s t : ℕ) : polyV [((1 : ℂ), 1, 0), (2, 0, 0)] (s : ℂ) (t : ℂ) ≠ 0 := by
  simp only [polyV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  intro h
  have : ((s + 2 : ℕ) : ℂ) = 0 := by push_cast; linear_combination h
  have := Nat.cast_eq_zero.mp this
  omega

theorem polyV_lin_ne (s t : ℕ) (hs : 1 ≤ s) : polyV [((1 : ℂ), 1, 0)] (s : ℂ) (t : ℂ) ≠ 0 := by
  simp only [polyV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  intro h
  have : ((s : ℕ) : ℂ) = 0 := by linear_combination h
  have := Nat.cast_eq_zero.mp this
  omega

theorem polyV_PE_ne (c1 c0 : ℝ) (h1 : 0 < c1) (h0 : 0 < c0) (s t : ℕ) :
    polyV [((c1 : ℂ), 1, 0), ((c0 : ℂ), 0, 0)] (s : ℂ) (t : ℂ) ≠ 0 := by
  simp only [polyV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  have : (0 : ℝ) ≤ c1 * s := by positivity
  linarith

include hm2 in
/-- **The uniform splitting theorem.** -/
theorem split_uniform {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule (V2mPlus m hm) M) (P : Submodule (modeAlg A) M) (hP : IsAtom P) (hQ : P ⋖ ⊤)
    {h h' : ℂ} (d : ℕ) (hd : 1 ≤ d) (hh' : h' = h + d)
    (hb : FactorBottom A ⊥ P h) (ht : FactorBottom A P ⊤ h')
    (hrows : ∀ l : Label m, ((weight m l : ℚ) : ℂ) = h' →
      chiT m hm hm2 l (VOA.mk (V2mPlus m hm) (HP m hm 2)) = 0 ∧
      chiT m hm hm2 l (VOA.mk (V2mPlus m hm) (HP m hm 3)) = 0)
    (him : h'.im = 0) (hpos : ∀ n : ℕ, 1 ≤ n → 4 * (m : ℝ) * h'.re < ((m : ℝ) + n) ^ 2)
    (hmodel : ∀ l : Label m, ((weight m l : ℚ) : ℂ) = h → ModelSpec m hm hm2 l h') :
    ∃ Q : Submodule (modeAlg A) M, IsCompl P Q := by
  have hC2 := V2mPlus_c2Cofinite m hm
  have hre' : h'.re = h.re + d := by rw [hh']; simp
  -- the kernel bottom
  obtain ⟨y, hy, hy0⟩ := SetLike.not_le_iff_exists.mp hb.1
  have hy0' : y ≠ 0 := fun h0 => hy0 (by rw [h0]; exact Submodule.zero_mem _)
  obtain ⟨y', hy'P, hy'0, hy'L⟩ := exists_eigen_in m hm A P hy.1 hy.2 hy0'
  have hy'g : y' ∈ (L0 A).maxGenEigenspace h :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hy'L)
  have hbotΩ : ∀ z ∈ P, L0 A z = h • z → z ∈ Omega A := fun z hz hzL =>
    kernel_bottom_mem_Omega A P h hb hz
      (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hzL))
  obtain ⟨l, k₀, hk₀, hk₀P, hk₀0, hk₀L, hχk⟩ :=
    exists_pure_top m hm hm2 A P hy'P (hbotΩ y' hy'P hy'L) hy'0 hy'L hbotΩ
  have hwl : ((weight m l : ℚ) : ℂ) = h := by
    have h1 := hχk (VOA.mk (V2mPlus m hm) (V2mPlus m hm).conformalVector)
    rw [topEvaluation_mk, oLevW_homogeneous A 0 (V2mPlus m hm).conformal_mem,
      show (2 : ℤ) - 1 + 0 = 1 by norm_num] at h1
    have h2 : L0 A k₀ = chiT m hm hm2 l (VOA.mk (V2mPlus m hm) (V2mPlus m hm).conformalVector) • k₀ := h1
    rw [hk₀L] at h2
    have h3 : chiT m hm hm2 l (generator m hm 0) = ((weight m l : ℚ) : ℂ) :=
      hasValues_omega m hm (chiT_hasValues m hm hm2 l)
    have h4 : (h - chiT m hm hm2 l (VOA.mk (V2mPlus m hm) (V2mPlus m hm).conformalVector)) • k₀ = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h4 with h5 | h5
    · rw [← h3]; exact (sub_eq_zero.mp h5).symm
    · exact absurd h5 hk₀0
  obtain ⟨N, _, _, B, e, he, he0, heL, hχe, hspanAll, hspanPos⟩ := hmodel l hwl
  rw [hwl] at heL
  -- below the kernel bottom, and between the bottoms
  have hlow : ∀ μ : ℂ, μ.re < h.re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0 := by
    intro μ hμ v hv
    have hvP : v ∈ P := low_mem_P' m hm A P ht hv (by rw [hre']; linarith)
    exact kernel_generalized_below_bottom_eq_zero A P h hb hvP hv hμ
  have hmid : ∀ k : ℕ, 0 < k → k < d → ∀ v : M, v ∈ Omega A → L0 A v = (h + (k : ℂ)) • v → v = 0 := by
    intro k hk hkd v hvΩ hvL
    have hvg : v ∈ (L0 A).maxGenEigenspace (h + k) :=
      Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hvL)
    have hvP : v ∈ P := low_mem_P' m hm A P ht hvg (by
      rw [hre']; simp; exact_mod_cast hkd)
    exact omega_mem_atom_eq_zero A hC2 P hP hy'P hy'0 hy'g hvP hvΩ k hk hvL
  -- the transfer of injectivity
  have INJ : ∀ d' : ℕ, d' ≤ d → ∀ L : List (ℂ × ℕ × ℕ), (∀ s t : ℕ, polyV L s t ≠ 0) →
      ∀ v ∈ P, L0 A v = (h + (d' : ℂ)) • v → evalW A (polyW (aL m hm) (bL m hm) L) v = 0 → v = 0 := by
    intro d' hd' L hne
    obtain ⟨C, hC⟩ := hspanAll (h + d')
    exact kernel_inj hC2 A B P hP (chiT m hm hm2 l) hk₀P hk₀0 hk₀ he hχk hχe hk₀L heL he0 hlow d hmid
      d' hd' (aL m hm) (bL m hm) (aL_deg m hm) (bL_deg m hm) C (fun _ _ => True) hC L
      (fun s t _ _ _ => hne s t)
  have hHP2 := HP_mem_grading m hm 2 (by norm_num) (by norm_num)
  have hHP3 := HP_mem_grading m hm 3 (by norm_num) (by norm_num)
  -- weights below the quotient bottom are in the kernel
  have hlowP : ∀ v : M, ∀ μ : ℂ, L0 A v = μ • v → μ.re < h'.re → v ∈ P := fun v μ hv hμ =>
    low_mem_P' m hm A P ht
      (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hv)) hμ
  have hlow0 : ∀ v : M, ∀ μ : ℂ, L0 A v = μ • v → μ.re < h.re → v = 0 := fun v μ hv hμ =>
    hlow μ hμ v (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hv))
  -- the quotient-bottom lift
  have hne : h ≠ h' := by
    intro e; have := congrArg Complex.re e; rw [hre'] at this
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨x, hxL, hxP⟩ := PlusRat2Dual.exists_eigen_lift hC2 A P hP hne hb ht
  have hAx : mode (A.YM (HP m hm 2)) 3 x ∈ P := by
    have := quot_top_zero m hm hm2 A P ht hxL 2 ⟨by norm_num, by norm_num⟩ (fun l hl => (hrows l hl).1)
    rwa [show (2 * ((2 : ℕ) : ℤ) - 1) = 3 by norm_num] at this
  have hBx : mode (A.YM (HP m hm 3)) 5 x ∈ P := by
    have := quot_top_zero m hm hm2 A P ht hxL 3 ⟨by norm_num, by norm_num⟩ (fun l hl => (hrows l hl).2)
    rwa [show (2 * ((3 : ℕ) : ℤ) - 1) = 5 by norm_num] at this
  -- the annihilator of `o(H⁴)` on the kernel at weight `h'`
  obtain ⟨C', hC'⟩ := hspanPos
  have hC'' : ∀ y : N, L0 B y = (h + (d : ℂ)) • y → y ∈ Submodule.span ℂ
      {u | ∃ s t : ℕ, 1 ≤ s ∧ s ≤ C' ∧ t ≤ C' ∧
        mode (B.YM (aL m hm).state) (aL m hm).modeIndex u = (s : ℂ) • u ∧
        mode (B.YM (bL m hm).state) (bL m hm).modeIndex u = (t : ℂ) • u} := by
    rw [← hh']; exact hC'
  obtain ⟨Vs, hV0, hann⟩ := kernel_ann_exists hC2 A B P hP (chiT m hm hm2 l) hk₀P hk₀0 hk₀ he hχk
    hχe hk₀L heL he0 hlow d hmid d le_rfl (aL m hm) (bL m hm) (aL_deg m hm) (bL_deg m hm) C'
    (fun s _ => 1 ≤ s) hC'' [(1, 1, 0)] (fun s t hs _ _ => polyV_lin_ne s t hs)
  set c := (Vs.map fun v => -v).prod with hc
  set F := annW (aL m hm) (bL m hm) [((1 : ℂ), 1, 0)] Vs with hF
  set u := c⁻¹ • evalW A F x with hu
  have hFdeg : WDeg F 0 := WDeg_annW (aL m hm) (bL m hm) (aL_deg m hm) (bL_deg m hm) _ Vs
  have hFx : evalW A F x - c • x ∈ P :=
    evalW_annW_modP A P (aL m hm) (bL m hm) [((1 : ℂ), 1, 0)] (by rw [evalW_lin]; exact hAx) Vs
  have hux : u - x ∈ P := by
    have : u - x = c⁻¹ • (evalW A F x - c • x) := by
      rw [hu, smul_sub, smul_smul, inv_mul_cancel₀ hV0, one_smul]
    rw [this]; exact P.smul_mem (algebraMap ℂ (modeAlg A) c⁻¹) (by simpa using hFx)
  have huP : u ∉ P := fun h0 => hxP (by
    have := P.sub_mem h0 hux
    rwa [sub_sub_cancel] at this)
  have huL : L0 A u = h' • u := by
    have := evalW_eigen A hxL F hFdeg
    rw [hu, map_smul, this]
    push_cast; rw [add_zero, smul_comm]
  have hAu : mode (A.YM (HP m hm 2)) 3 u = 0 := by
    have hAxL : L0 A (mode (A.YM (HP m hm 2)) 3 x) = (h + (d : ℂ)) • mode (A.YM (HP m hm 2)) 3 x := by
      rw [L0_mode_eigen A hxL hHP2 3, ← hh']; push_cast; ring_nf
    rw [hu, map_smul, ← evalW_lin m hm A, evalW_polyW_annW_comm, evalW_lin,
      hann _ hAx hAxL, smul_zero]
  have hBuP : mode (A.YM (HP m hm 3)) 5 u ∈ P := by
    have : mode (A.YM (HP m hm 3)) 5 u = mode (A.YM (HP m hm 3)) 5 x +
        mode (A.YM (HP m hm 3)) 5 (u - x) := by rw [← map_add, add_sub_cancel]
    rw [this]
    exact P.add_mem hBx (P.smul_mem (⟨mode (A.YM (HP m hm 3)) 5,
      Algebra.subset_adjoin ⟨HP m hm 3, 5, rfl⟩⟩ : modeAlg A) hux)
  have hBu : mode (A.YM (HP m hm 3)) 5 u = 0 := by
    apply kernel_inj hC2 A B P hP (chiT m hm hm2 l) hk₀P hk₀0 hk₀ he hχk hχe hk₀L heL he0 hlow d
      hmid d le_rfl (aL m hm) (bL m hm) (aL_deg m hm) (bL_deg m hm) C' (fun s _ => 1 ≤ s) hC''
      [((1 : ℂ), 1, 0)] (fun s t hs _ _ => polyV_lin_ne s t hs) _ hBuP
    · rw [L0_mode_eigen A huL hHP3 5, hh']; push_cast; ring_nf
    · rw [evalW_lin, comm_A_B, hAu, map_zero]
  -- Abe's chain (Lemma 4.8)
  have hω := HP_mem_grading m hm 1 (by norm_num) (by norm_num)
  have hchain := m1plus_chain m hm hm2 A hAu hBu (fun y hy hT => by
      have hyL : L0 A y = (h + ((d - 1 : ℕ) : ℂ)) • y := by
        rw [hy, L0_mode_eigen A huL hω 2, hh', Nat.cast_sub hd]; push_cast; ring_nf
      have hyP : y ∈ P := hlowP y _ hyL (by
        rw [hre']; simp; linarith)
      exact INJ (d - 1) (by omega) _ (fun s t => polyV_P1_ne s t) y hyP hyL
        (by rw [evalW_P1]; exact hT))
    (fun y hy hT => by
      have hyL : L0 A y = (h' - 2) • y := by
        rw [hy, L0_mode_eigen A huL hω 3]; push_cast; ring_nf
      rcases Nat.lt_or_ge d 2 with hd2 | hd2
      · apply hlow0 y _ hyL
        rw [hh']; simp
        have : (d : ℝ) < 2 := by exact_mod_cast hd2
        linarith
      · have hyL' : L0 A y = (h + ((d - 2 : ℕ) : ℂ)) • y := by
          rw [hyL, hh', Nat.cast_sub hd2]; push_cast; ring_nf
        have hyP : y ∈ P := hlowP y _ hyL (by simp)
        exact INJ (d - 2) (by omega) _ (fun s t => polyV_P2_ne s t) y hyP hyL'
          (by rw [evalW_P2]; exact hT))
  obtain ⟨hLk, hH4k⟩ := hchain
  have hLk' : ∀ k : ℤ, 1 ≤ k → mode (A.YM (V2mPlus m hm).conformalVector) (k + 1) u = 0 := by
    intro k hk
    have := hLk k.toNat (by omega)
    rwa [Int.toNat_of_nonneg (by omega)] at this
  -- the `E`-lowerings
  have hEm := EP_mem_grading m hm
  have hYL : ∀ ℓ : ℤ, L0 A (Ylow m hm A u ℓ) = (h' - ℓ) • Ylow m hm A u ℓ := by
    intro ℓ
    rw [Ylow, L0_mode_eigen A huL hEm]; push_cast; ring_nf
  have hKpos : (0 : ℝ) < 2 * (2 * (m : ℝ)) ^ 2 - 5 * (2 * (m : ℝ)) + 2 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    nlinarith
  have hh'r : h' = ((h'.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hstep : ∀ n : ℕ, 1 ≤ n → n ≤ d → (∀ ℓ : ℤ, (n : ℤ) < ℓ → Ylow m hm A u ℓ = 0) →
      Ylow m hm A u n = 0 := by
    intro n hn1 hnd hgt
    have h4 := oH4_Y m hm A huL hLk' 0 (by rw [hAu, zero_smul]) n hgt
    set Yn := Ylow m hm A u n
    have hcE : (0 : ℝ) < 2 * n * (((m : ℝ) + n) ^ 2 - 4 * m * h'.re) := by
      have := hpos n hn1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      nlinarith
    have hYnL : L0 A Yn = (h + ((d - n : ℕ) : ℂ)) • Yn := by
      rw [hYL, hh', Nat.cast_sub hnd]; push_cast; ring_nf; rfl
    have hYnP : Yn ∈ P := hlowP Yn _ (hYL n) (by
      simp; have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith)
    apply INJ (d - n) (by omega)
      [(((2 * (2 * (m : ℝ)) ^ 2 - 5 * (2 * (m : ℝ)) + 2 : ℝ) : ℂ), 1, 0),
        (((2 * n * (((m : ℝ) + n) ^ 2 - 4 * m * h'.re) : ℝ) : ℂ), 0, 0)]
      (fun s t => polyV_PE_ne _ _ hKpos hcE s t) Yn hYnP hYnL
    rw [evalW_PE]
    push_cast
    rw [h4]
    rw [hh'r]
    push_cast
    module
  have hY : ∀ t : ℕ, t ≤ d → ∀ ℓ : ℤ, (d : ℤ) - t < ℓ → Ylow m hm A u ℓ = 0 := by
    intro t
    induction t with
    | zero =>
      intro _ ℓ hℓ
      apply hlow0 _ _ (hYL ℓ)
      rw [hh']; simp
      have : (d : ℝ) < ℓ := by exact_mod_cast (by omega : (d : ℤ) < ℓ)
      linarith
    | succ t ih =>
      intro ht ℓ hℓ
      by_cases hlt : (d : ℤ) - t < ℓ
      · exact ih (by omega) ℓ hlt
      · have hℓ' : ℓ = ((d - t : ℕ) : ℤ) := by push_cast [Nat.cast_sub (by omega : t ≤ d)]; omega
        rw [hℓ']
        apply hstep (d - t) (by omega) (by omega)
        intro ℓ' hℓ'
        apply ih (by omega)
        push_cast [Nat.cast_sub (by omega : t ≤ d)] at hℓ'
        omega
  have hYall : ∀ ℓ : ℤ, 1 ≤ ℓ → Ylow m hm A u ℓ = 0 := fun ℓ hℓ =>
    hY d le_rfl ℓ (by omega)
  -- `u` is a top vector (Abe, Prop. 2.2)
  have huΩ : u ∈ Omega A := by
    apply mem_Omega_of_generators A (G := Set.range (gP m hm))
    · rintro g ⟨i, rfl⟩
      exact ⟨wtP m i, by fin_cases i <;> simp [wtP] <;> omega, gP_mem_grading m hm i⟩
    · exact top_eq_span_iterProd m hm hm2
    · rintro g ⟨i, rfl⟩ j hj n hn
      by_cases hji : j = (wtP m i : ℤ)
      · subst hji
        fin_cases i
        · -- `ω`
          have := hLk' (n - 1) (by simp [wtP] at hn; omega)
          rw [show n - 1 + 1 = n by ring] at this
          exact this
        · -- `W = 10H⁴ + L(-1)²ω/3`
          change mode (A.YM (WP m hm)) n u = 0
          rw [WP_eq_comb m hm]
          simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
          simp [wtP] at hn
          have e1 := hH4k (n - 3).toNat (by omega)
          rw [show (((n - 3).toNat : ℕ) : ℤ) + 3 = n by omega] at e1
          have e2 := hLk' (n - 3) (by omega)
          rw [show n - 3 + 1 = n - 2 by ring] at e2
          rw [show n - ((0 : ℕ) : ℤ) = n by simp, show n - ((2 : ℕ) : ℤ) = n - 2 by simp]
          rw [e1, show HP m hm 1 = (V2mPlus m hm).conformalVector from rfl, e2]; simp
        · -- `E`
          change mode (A.YM (EP m hm)) n u = 0
          simp [wtP] at hn
          have := hYall (n - m + 1) (by omega)
          rw [Ylow, show (m : ℤ) - 1 + (n - m + 1) = n by ring] at this
          exact this
      · have h0 := eq_zero_of_mem_two_gradings (W := V2mPlus m hm) hji hj (gP_mem_grading m hm i)
        rw [h0, map_zero, mode_zero, LinearMap.zero_apply]
  -- the complement
  have hug : u ∈ (L0 A).maxGenEigenspace h' :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr huL)
  apply (exists_cyclic_lift_iff_complement A P hQ h' ht).mp
  refine ⟨u, hug, huP, ?_⟩
  rw [disjoint_cyclic_iff_no_mode_word A P hP hy'P hy'0 u]
  have hy'g' : y' ∈ (L0 A).maxGenEigenspace (h' + ((-(d : ℤ) : ℤ) : ℂ)) := by
    have : h' + ((-(d : ℤ) : ℤ) : ℂ) = h := by rw [hh']; push_cast; ring
    rw [this]; exact hy'g
  rw [no_mode_word_iff_not_mem_degreeSpan hC2 A hug (-(d : ℤ)) hy'g',
    degreeSpan_neg_eq_bot A huΩ h' huL d hd]
  intro hm0
  exact hy'0 ((Submodule.mem_bot ℂ).mp hm0)

end Main

end VOA.Classification.COne.PlusRat5
