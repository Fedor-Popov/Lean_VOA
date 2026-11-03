import VOA.Classification.COne.PlusRat5Top
import VOA.Classification.COne.PlusRat5Fock

/-! # Fock models of the untwisted rows and their joint `(o(H⁴), o(H⁶))` spectra

A *model* of a row `l` at a target weight `h'` (`ModelSpec`) is a weak `V_{2m}⁺`-module `B`
with a top vector `e ≠ 0` of weight `h_l` and Zhu character `chiT l`, whose `L(0)`-eigenspaces
are spanned by joint eigenvectors of `o(H⁴), o(H⁶)` with eigenvalues in `ℕ²` (bounded), and
whose `h'`-eigenspace is spanned by joint eigenvectors with `o(H⁴)`-eigenvalue `≥ 1`.  Irreducibility of `B` is never used.

Models: charged rows `V_{L+λ_s}`, half rows `V_{L+α/2}` (with `e = e^{α/2} ± e^{-α/2}`), and the
sign row (the adjoint module `V_L`, `e = h(-1)𝟙`).  Twisted rows are not modelled.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat5
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3 PlusRat4 PlusRational

variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)

/-- The letter `o(H⁴) = H⁴₍₃₎`. -/
def aL : HomogeneousLetter (V2mPlus m hm) :=
  ⟨HP m hm 2, 4, 3, by simpa using HP_mem_grading m hm 2 (by norm_num) (by norm_num)⟩

/-- The letter `o(H⁶) = H⁶₍₅₎`. -/
def bL : HomogeneousLetter (V2mPlus m hm) :=
  ⟨HP m hm 3, 6, 5, by simpa using HP_mem_grading m hm 3 (by norm_num) (by norm_num)⟩

theorem aL_deg : (aL m hm).weight - (aL m hm).modeIndex - 1 = 0 := rfl
theorem bL_deg : (bL m hm).weight - (bL m hm).modeIndex - 1 = 0 := rfl

/-- The `w`-eigenspace of `B` is spanned by joint eigenvectors with eigenvalues in `Q`, `≤ C`. -/
def SpecSpan {N : Type} [AddCommGroup N] [Module ℂ N] (B : WeakModule (V2mPlus m hm) N) (w : ℂ)
    (C : ℕ) (Q : ℕ → ℕ → Prop) : Prop :=
  ∀ y : N, L0 B y = w • y → y ∈ Submodule.span ℂ
    {u | ∃ s t : ℕ, Q s t ∧ s ≤ C ∧ t ≤ C ∧
      mode (B.YM (aL m hm).state) (aL m hm).modeIndex u = (s : ℂ) • u ∧
      mode (B.YM (bL m hm).state) (bL m hm).modeIndex u = (t : ℂ) • u}

/-- A Fock model of the row `l`, adapted to the target weight `h'`. -/
def ModelSpec (l : Label m) (h' : ℂ) : Prop :=
  ∃ (N : Type) (_ : AddCommGroup N) (_ : Module ℂ N) (B : WeakModule (V2mPlus m hm) N) (e : N)
    (he : e ∈ Omega B), e ≠ 0 ∧ L0 B e = ((weight m l : ℚ) : ℂ) • e ∧
    (∀ r, topEvaluation B e he r = chiT m hm hm2 l r • e) ∧
    (∀ w : ℂ, ∃ C : ℕ, SpecSpan m hm B w C (fun _ _ => True)) ∧
    (∃ C : ℕ, SpecSpan m hm B h' C (fun s _ => 1 ≤ s))

/-! ## §1  Monomial bounds -/

theorem wtE_le (e : ℕ) (he : 1 ≤ e) (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) :
    wtE m e s ≤ (Finsupp.weight HeisenbergN.weightFnN s) ^ e := by
  induction s using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, map_add]
    calc wtE m e f + wtE m e g ≤ (Finsupp.weight HeisenbergN.weightFnN f) ^ e +
          (Finsupp.weight HeisenbergN.weightFnN g) ^ e := Nat.add_le_add hf hg
      _ ≤ _ := pow_add_pow_le (Nat.zero_le _) (Nat.zero_le _) (by omega)
  | single a b =>
    rw [Finsupp.weight_single, Finsupp.weight_single, smul_eq_mul, smul_eq_mul,
      HeisenbergN.weightFnN_apply, mul_pow]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) b)

/-- Monomial states of Fock degree `N ≤ R` are joint eigenvectors with eigenvalues `≤ R⁵`. -/
theorem mono_bound (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) (R : ℕ)
    (hR : Finsupp.weight HeisenbergN.weightFnN s ≤ R) :
    wtE m 3 s ≤ R ^ 5 ∧ wtE m 5 s ≤ R ^ 5 := by
  set N := Finsupp.weight HeisenbergN.weightFnN s
  have h3 : wtE m 3 s ≤ N ^ 3 := wtE_le m 3 (by norm_num) s
  have h5 : wtE m 5 s ≤ N ^ 5 := wtE_le m 5 (by norm_num) s
  have hN35 : N ^ 3 ≤ N ^ 5 := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0]; simp
    · exact Nat.pow_le_pow_right hpos (by norm_num)
  have hNR : N ^ 5 ≤ R ^ 5 := Nat.pow_le_pow_left hR 5
  omega

/-! ## §2  Spectral spans of the lattice modules `V_{L+λ_j}` -/

section Lat
variable (j : ℤ)

/-- `V_{L+λ_j}` as a weak `V⁺`-module. -/
abbrev LP : WeakModule (V2mPlus m hm) (LatModuleGen (latP m)) :=
  (resN m hm (latticeModule m hm j)).toWeakModule

theorem LP_A (u : LatModuleGen (latP m)) :
    mode ((LP m hm j).YM (aL m hm).state) (aL m hm).modeIndex u =
      mode ((LA m hm j).YM (ls m H4R)) 3 u := by
  have h := hasN_HP m hm 2 (by norm_num) (by norm_num)
  change mode ((latticeModule m hm j).YM ((HP m hm 2 : VP m hm) : LatModuleGen (latP m))) 3 u = _
  rw [h]; rfl

theorem LP_B (u : LatModuleGen (latP m)) :
    mode ((LP m hm j).YM (bL m hm).state) (bL m hm).modeIndex u =
      mode ((LA m hm j).YM (ls m H6R)) 5 u := by
  have h := hasN_HP m hm 3 (by norm_num) (by norm_num)
  change mode ((latticeModule m hm j).YM ((HP m hm 3 : VP m hm) : LatModuleGen (latP m))) 5 u = _
  rw [h]; rfl

include hm in
theorem fiber_N_le (w : ℂ) {N n : ℤ}
    (hp : (N, n) ∈ shiftFiber (latP m) (glueLat m j) (glueIota m j) (glueDelta m j) w) :
    (N : ℝ) ≤ w.re := by
  obtain ⟨hN, hw⟩ := hp
  simp only at hN hw
  rw [shiftWeight_rankOne m hm j] at hw
  have hre := congrArg Complex.re hw
  rw [Complex.ofReal_re] at hre
  have hNn : ((N.toNat : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hN
  rw [hNn] at hre
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have : 0 ≤ (((2 * m * n + j : ℤ) : ℝ)) ^ 2 / (4 * m) := by positivity
  linarith

/-- **Spectral span of `V_{L+λ_j}`.** -/
theorem lat_specSpan (w : ℂ) (Q : ℕ → ℕ → Prop)
    (hQ : ∀ (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) (n : ℤ),
      (((Finsupp.weight HeisenbergN.weightFnN s : ℕ) : ℤ), n) ∈
        shiftFiber (latP m) (glueLat m j) (glueIota m j) (glueDelta m j) w →
      Q (wtE m 3 s) (wtE m 5 s)) :
    SpecSpan m hm (LP m hm j) w (⌈w.re⌉₊ ^ 5) Q := by
  intro y hy
  have hy' : y ∈ (latticeModule m hm j).weight w := VOA.eigenvector_mem_weight _ hy
  refine Submodule.span_mono ?_ (lat_weight_mem_span m hm j w hy')
  rintro _ ⟨s, γ, _, hfib, rfl⟩
  have hb := mono_bound m s ⌈w.re⌉₊ (by
    have := fiber_N_le m hm j w hfib
    have h2 : ((Finsupp.weight HeisenbergN.weightFnN s : ℕ) : ℝ) ≤ w.re := by exact_mod_cast this
    have h3 := h2.trans (Nat.le_ceil w.re)
    exact_mod_cast h3)
  refine ⟨wtE m 3 s, wtE m 5 s, hQ s γ hfib, hb.1, hb.2, ?_, ?_⟩
  · rw [LP_A, oH4_mono m hm (LA m hm j) (mu m j) (lat_h_mode m hm j)]
  · rw [LP_B, oH6_mono m hm (LA m hm j) (mu m j) (lat_h_mode m hm j)]

end Lat

/-! ## §3  Fiber arithmetic -/

/-- No Fock vacuum of `V_{L+λ_j}` sits at the weight `s'²/(4m)`, `s' ≠ j`. -/
theorem sq_ne_of_range (j n : ℤ) (hj1 : 1 ≤ j) (hjm : j ≤ m) (s' : ℤ) (hs1 : 1 ≤ s')
    (hsm : s' ≤ m) (hne : s' ≠ j) : (2 * (m : ℤ) * n + j) ^ 2 ≠ s' ^ 2 := by
  intro h
  have hm1 : (1 : ℤ) ≤ m := by omega
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · -- `n ≤ -1`
    set X := 2 * (m : ℤ) * n + j with hX
    have hXle : X ≤ -(m : ℤ) := by nlinarith
    have hf : (X + s') * (X - s') = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp hf with h1 | h1
    · have hs' : s' = m := by omega
      have hXm : X = -(m : ℤ) := by omega
      have hn1 : n = -1 := by
        rcases lt_or_eq_of_le (show n ≤ -1 by omega) with h2 | h2
        · nlinarith
        · exact h2
      subst hn1
      omega
    · omega
  · have : (j - s') * (j + s') = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp this with h1 | h1 <;> omega
  · have h2 : s' + 1 ≤ 2 * (m : ℤ) * n + j := by nlinarith
    nlinarith

include hm in
theorem fiber_pos (j : ℤ) (hj1 : 1 ≤ j) (hjm : j ≤ m) (s' : ℕ) (hs1 : 1 ≤ s') (hsm : s' ≤ m)
    (hne : (s' : ℤ) ≠ j) {N n : ℤ}
    (hp : (N, n) ∈ shiftFiber (latP m) (glueLat m j) (glueIota m j) (glueDelta m j)
      ((((s' : ℝ) ^ 2 / (4 * m) : ℝ)) : ℂ)) : 1 ≤ N := by
  obtain ⟨hN, hw⟩ := hp
  simp only at hN hw
  rw [shiftWeight_rankOne m hm j] at hw
  have hre := congrArg Complex.re hw
  simp only [Complex.ofReal_re] at hre
  have hNn : ((N.toNat : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hN
  rw [hNn] at hre
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hZ : (4 * (m : ℤ) * N + (2 * m * n + j) ^ 2 : ℤ) = (s' : ℤ) ^ 2 := by
    have : ((4 * (m : ℤ) * N + (2 * m * n + j) ^ 2 : ℤ) : ℝ) = (((s' : ℤ) ^ 2 : ℤ) : ℝ) := by
      push_cast
      field_simp at hre
      push_cast at hre
      linarith
    exact_mod_cast this
  by_contra hlt
  have hN0 : N = 0 := by omega
  subst hN0
  exact sq_ne_of_range m j n hj1 hjm s' (by exact_mod_cast hs1) (by exact_mod_cast hsm) hne
    (by linarith)

/-! ## §4  The charged and half models -/

theorem lat_specSpan_all (j : ℤ) (w : ℂ) : ∃ C : ℕ, SpecSpan m hm (LP m hm j) w C (fun _ _ => True) :=
  ⟨_, lat_specSpan m hm j w _ (fun _ _ _ => trivial)⟩

theorem lat_specSpan_pos (j : ℤ) (h' : ℂ)
    (hS1 : ∀ N n : ℤ, (N, n) ∈ shiftFiber (latP m) (glueLat m j) (glueIota m j) (glueDelta m j) h' →
      1 ≤ N) : ∃ C : ℕ, SpecSpan m hm (LP m hm j) h' C (fun s _ => 1 ≤ s) := by
  refine ⟨_, lat_specSpan m hm j h' _ (fun s n hfib => ?_)⟩
  have h1 := hS1 _ _ hfib
  have h2 := wtE_ge m 3 (by norm_num) s
  omega

include hm2 in
/-- **The charged model.** -/
theorem modelSpec_charged (r : Fin (m - 1)) (h' : ℂ)
    (hS1 : ∀ N n : ℤ, (N, n) ∈ shiftFiber (latP m) (glueLat m ((r.val + 1 : ℕ) : ℤ))
      (glueIota m ((r.val + 1 : ℕ) : ℤ)) (glueDelta m ((r.val + 1 : ℕ) : ℤ)) h' → 1 ≤ N) :
    ModelSpec m hm hm2 (.inl r) h' :=
  ⟨LatModuleGen (latP m), inferInstance, inferInstance, LP m hm ((r.val + 1 : ℕ) : ℤ),
    latVacuumGen (latP m), es_Omega m hm r, latVacuumGen_ne_zero' m hm, es_L0 m hm r,
    lat_top_char m hm hm2 r, fun w => lat_specSpan_all m hm _ w, lat_specSpan_pos m hm _ h' hS1⟩

include hm2 in
/-- **The half models.** -/
theorem modelSpec_half (i : Fin 8) (hi : i = 2 ∨ i = 3) (h' : ℂ)
    (hS1 : ∀ N n : ℤ, (N, n) ∈ shiftFiber (latP m) (glueLat m (m : ℤ))
      (glueIota m (m : ℤ)) (glueDelta m (m : ℤ)) h' → 1 ≤ N) :
    ModelSpec m hm hm2 (.inr i) h' := by
  set σ : ℂ := if i = 2 then 1 else -1 with hσdef
  have hσ : σ * σ = 1 := by rcases hi with rfl | rfl <;> simp [hσdef]
  let N := resN m hm (latticeModule m hm m)
  have he : ((((m : ℤ) : ℝ) ^ 2 / (4 * m) : ℝ) : ℂ) = (m : ℂ) / 4 := by
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    push_cast; field_simp
  have hl : IsLowestWeight N ((m : ℂ) / 4) := by
    rw [← he]; exact latticeModule_isLowestWeight m hm m (by simp)
  have hx := halfVector_mem m hm σ
  have hΩ := lowest_mem_Omega m hm N hl hx
  set χ := chiT m hm hm2 (.inr i)
  have hχ := chiT_hasValues m hm hm2 (.inr i)
  have hw : ((weight m (.inr i) : ℚ) : ℂ) = (m : ℂ) / 4 := by
    rcases hi with rfl | rfl <;> simp [weight]
  have g0 : oMod N (gP m hm 0) (halfVector m σ) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 0)) • halfVector m σ := by
    rw [hχ.1]
    change oMod N (V2mPlus m hm).conformalVector _ = _
    rw [oMod_conformalVector, N.L0_weight _ _ hx]
    congr 1
    rcases hi with rfl | rfl <;> simp [values, exceptional]
  have g1 : oMod N (gP m hm 1) (halfVector m σ) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 1)) • halfVector m σ := by
    rw [hχ.2.1]
    change oMod N (WP m hm) _ = _
    have hlat : IsLowestWeight (latticeModule m hm m) ((m : ℂ) / 4) := by
      rw [← he]; exact latticeModule_isLowestWeight m hm m (by simp)
    rw [oMod_resN m hm _ (WP_mem_grading m hm), WP_coe, oMod_W_V2m m hm _ hlat hx]
    congr 1
    rcases hi with rfl | rfl <;> simp [values, exceptional] <;> ring
  have g2 : oMod N (gP m hm 2) (halfVector m σ) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 2)) • halfVector m σ := by
    rw [hχ.2.2]
    change oMod N (EP m hm) _ = _
    rw [halfVector_E m hm σ hσ]
    congr 1
    rcases hi with rfl | rfl <;> simp [hσdef, values, exceptional]
  have hc := topEvaluation_eq_char m hm hm2 N.toWeakModule hΩ χ (by
    intro j; rw [topEvaluation_mk_eq_oMod m hm N hΩ (gP_mem_grading m hm j)]
    fin_cases j
    exacts [g0, g1, g2])
  refine ⟨LatModuleGen (latP m), inferInstance, inferInstance, LP m hm (m : ℤ),
    halfVector m σ, hΩ, halfVector_ne_zero m σ, ?_, hc, fun w => lat_specSpan_all m hm _ w,
    lat_specSpan_pos m hm _ h' hS1⟩
  rw [hw]
  exact N.L0_weight _ _ hx

/-! ## §5  The sign model: the adjoint module `V_L` -/

section Adj

/-- `V_L` as a weak `V⁺`-module. -/
abbrev AP : WeakModule (V2mPlus m hm) (LatModuleGen (latP m)) :=
  (resN m hm (adjointModule (V2m m hm))).toWeakModule

theorem AP_A (u : LatModuleGen (latP m)) :
    mode ((AP m hm).YM (aL m hm).state) (aL m hm).modeIndex u =
      mode ((adjointWeakModule (V2m m hm)).YM (ls m H4R)) 3 u := by
  have h := hasN_HP m hm 2 (by norm_num) (by norm_num)
  change mode ((adjointWeakModule (V2m m hm)).YM ((HP m hm 2 : VP m hm) : LatModuleGen (latP m))) 3 u = _
  rw [h]; rfl

theorem AP_B (u : LatModuleGen (latP m)) :
    mode ((AP m hm).YM (bL m hm).state) (bL m hm).modeIndex u =
      mode ((adjointWeakModule (V2m m hm)).YM (ls m H6R)) 5 u := by
  have h := hasN_HP m hm 3 (by norm_num) (by norm_num)
  change mode ((adjointWeakModule (V2m m hm)).YM ((HP m hm 3 : VP m hm) : LatModuleGen (latP m))) 5 u = _
  rw [h]; rfl

/-- Weight spaces of `V_L` are spanned by monomial states. -/
theorem adj_weight_mem_span (w : ℂ) {v : LatModuleGen (latP m)} (hv : v ∈ adjWeight (V2m m hm) w) :
    v ∈ Submodule.span ℂ {u | ∃ (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) (α : ℤ) (k : ℤ),
      (k : ℂ) = w ∧ ((Finsupp.weight HeisenbergN.weightFnN s : ℕ) : ℤ) + m * α ^ 2 = k ∧
      u = latStateGen (latP m) (MvPolynomial.monomial s 1) α} := by
  refine (iSup₂_le (fun k hk => ?_) : adjWeight (V2m m hm) w ≤ _) hv
  rw [V2m_grading_eq]
  refine iSup_le (fun α => ?_)
  change Submodule.map (mkEα (latP m) α) (HeisenbergN.gradingZN (rank (latP m)) (k - LatGen.halfNorm (latP m) α)) ≤ _
  by_cases hneg : k - LatGen.halfNorm (latP m) α < 0
  · rw [HeisenbergN.gradingZN_of_neg hneg, Submodule.map_bot]; exact bot_le
  push Not at hneg
  rw [gradingZN_of_nonneg hneg]
  rintro _ ⟨q, hq, rfl⟩
  have hq' : q.IsWeightedHomogeneous HeisenbergN.weightFnN (k - LatGen.halfNorm (latP m) α).toNat := hq
  rw [MvPolynomial.as_sum q, map_sum]
  refine Submodule.sum_mem _ (fun d hd => ?_)
  have hdw : Finsupp.weight HeisenbergN.weightFnN d = (k - LatGen.halfNorm (latP m) α).toNat :=
    hq' (MvPolynomial.mem_support_iff.mp hd)
  rw [show MvPolynomial.monomial d (MvPolynomial.coeff d q) =
      MvPolynomial.coeff d q • MvPolynomial.monomial d (1 : ℂ) by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨d, α, k, hk, ?_, rfl⟩
  rw [hdw, Int.toNat_of_nonneg hneg]
  have hh := halfNorm_latP m α
  change ℤ at α
  rw [hh]; ring

/-- **Spectral span of `V_L`.** -/
theorem adj_specSpan (w : ℂ) (Q : ℕ → ℕ → Prop)
    (hQ : ∀ (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) (α k : ℤ), (k : ℂ) = w →
      ((Finsupp.weight HeisenbergN.weightFnN s : ℕ) : ℤ) + m * α ^ 2 = k →
      Q (wtE m 3 s) (wtE m 5 s)) :
    SpecSpan m hm (AP m hm) w (⌈w.re⌉₊ ^ 5) Q := by
  intro y hy
  have hy' : y ∈ (adjointModule (V2m m hm)).weight w := VOA.eigenvector_mem_weight _ hy
  refine Submodule.span_mono ?_ (adj_weight_mem_span m hm w hy')
  rintro _ ⟨s, α, k, hk, hks, rfl⟩
  have hb := mono_bound m s ⌈w.re⌉₊ (by
    have h1 : ((Finsupp.weight HeisenbergN.weightFnN s : ℕ) : ℤ) ≤ k := by nlinarith
    have h2 : ((Finsupp.weight HeisenbergN.weightFnN s : ℕ) : ℝ) ≤ w.re := by
      rw [← hk]; simp only [Complex.intCast_re]; exact_mod_cast h1
    have h3 := h2.trans (Nat.le_ceil w.re)
    exact_mod_cast h3)
  refine ⟨wtE m 3 s, wtE m 5 s, hQ s α k hk hks, hb.1, hb.2, ?_, ?_⟩
  · rw [AP_A, oH4_mono m hm (adjointWeakModule (V2m m hm)) (fun γ => chargeCoord (latP m) γ (a0 m))
      (adj_h_mode m hm)]
  · rw [AP_B, oH6_mono m hm (adjointWeakModule (V2m m hm)) (fun γ => chargeCoord (latP m) γ (a0 m))
      (adj_h_mode m hm)]

include hm2 in
/-- **The sign model** (`V_L`, top `h(-1)𝟙`). -/
theorem modelSpec_sign (h' : ℂ) (hpos : 0 < h'.re) (hlt : h'.re < m) :
    ModelSpec m hm hm2 (.inr 1) h' := by
  set N := signModule m hm
  have hl := signModule_isLowestWeight m hm
  have hx := signVector_mem m hm
  have hΩs := lowest_mem_Omega m hm N hl hx
  set χ := chiT m hm hm2 (.inr 1)
  have hχ := chiT_hasValues m hm hm2 (.inr 1)
  have g0 : oMod N (gP m hm 0) (signVector m hm) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 0)) • signVector m hm := by
    rw [hχ.1]
    change oMod N (V2mPlus m hm).conformalVector _ = _
    rw [oMod_conformalVector, N.L0_weight _ _ hx]
    congr 1
  have g1 : oMod N (gP m hm 1) (signVector m hm) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 1)) • signVector m hm := by
    rw [hχ.2.1]
    change oMod N (WP m hm) _ = _
    rw [signVector_W]
    congr 1
  have g2 : oMod N (gP m hm 2) (signVector m hm) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 2)) • signVector m hm := by
    rw [hχ.2.2]
    change oMod N (EP m hm) _ = _
    rw [signVector_E m hm hm2]
    simp [values, exceptional]
  have hgN : ∀ i : Fin 3, topEvaluation N.toWeakModule (signVector m hm) hΩs
      (VOA.mk (V2mPlus m hm) (gP m hm i)) = χ (VOA.mk (V2mPlus m hm) (gP m hm i)) • signVector m hm := by
    intro j; rw [topEvaluation_mk_eq_oMod m hm N hΩs (gP_mem_grading m hm j)]
    fin_cases j
    exacts [g0, g1, g2]
  set e : LatModuleGen (latP m) := (signVector m hm : LatModuleGen (latP m)) with he_def
  have hΩ : e ∈ Omega (AP m hm) := by
    intro β v hv n hn
    have := congrArg Subtype.val (hΩs β v hv n hn)
    exact this
  have hg : ∀ i : Fin 3, topEvaluation (AP m hm) e hΩ (VOA.mk (V2mPlus m hm) (gP m hm i)) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm i)) • e := by
    intro i
    have h1 := congrArg Subtype.val (hgN i)
    rw [topEvaluation_mk, oLevW_homogeneous _ 0 (gP_mem_grading m hm i)] at h1 ⊢
    exact h1
  have hc := topEvaluation_eq_char m hm hm2 (AP m hm) hΩ χ hg
  have he0 : e ≠ 0 := by
    intro h
    apply signVector_ne_zero m hm
    exact Subtype.ext h
  have hL : L0 (AP m hm) e = ((weight m (.inr 1) : ℚ) : ℂ) • e := by
    have h1 := congrArg Subtype.val (N.L0_weight _ _ hx)
    rw [show ((weight m (.inr 1) : ℚ) : ℂ) = 1 by simp [weight]]
    exact h1
  refine ⟨LatModuleGen (latP m), inferInstance, inferInstance, AP m hm, e, hΩ, he0, hL, hc,
    fun w => ⟨_, adj_specSpan m hm w _ (fun _ _ _ _ _ => trivial)⟩, ⟨_, adj_specSpan m hm h' _ ?_⟩⟩
  intro s α k hk hks
  have h2 := wtE_ge m 3 (by norm_num) s
  have hkre : (k : ℝ) = h'.re := by rw [← hk]; simp
  have hk0 : 0 < k := by
    have : (0 : ℝ) < k := by rw [hkre]; exact hpos
    exact_mod_cast this
  have hkm : k < m := by
    have : (k : ℝ) < m := by rw [hkre]; exact hlt
    exact_mod_cast this
  by_contra hcon
  have hw0 : Finsupp.weight HeisenbergN.weightFnN s = 0 := by omega
  rw [hw0] at hks
  push_cast at hks
  rcases lt_trichotomy α 0 with ha | ha | ha
  · have h1 : (1 : ℤ) ≤ α ^ 2 := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h1 (show (0 : ℤ) ≤ (m : ℤ) by positivity)
    linarith
  · subst ha; omega
  · have h1 : (1 : ℤ) ≤ α ^ 2 := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h1 (show (0 : ℤ) ≤ (m : ℤ) by positivity)
    linarith

end Adj

end VOA.Classification.COne.PlusRat5
