import VOA.Classification.COne.PlusRat3Transfer

/-! # The transfer lemma for a general charged row

For a charged row `s = r + 1 ≤ m - 2` (so the lattice model `V_{L+λ_s}` has a one-dimensional
weight space `h_s + 1`, spanned by `L(-1)e`), and an extension whose quotient-bottom lift `x` is a
top vector of weight `h_s` with a unique table row, every corrected degree-one vector
`t₍ₖ₋₂₎x - c L(-1)x` is a top vector (`transfer_Omega_gen`).  This is the `m`-general version of
`transfer_Omega` (`m = 6`, `s = 1`).
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat3
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible

variable (m : ℕ) (hm : 1 ≤ m)

/-- The conformal weight of a charged row, in `ℂ`. -/
abbrev hC (r : Fin (m - 1)) : ℂ := ((weight m (.inl r) : ℚ) : ℂ)

theorem hC_eq (r : Fin (m - 1)) :
    hC m r = ((((((r.val + 1 : ℕ) : ℤ) : ℝ) ^ 2 / (4 * m) : ℝ)) : ℂ) := by
  simp [hC, weight]

theorem hC_ne_zero (hm2 : 2 ≤ m) (r : Fin (m - 1)) : hC m r ≠ 0 := by
  rw [hC_eq]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have : (0 : ℝ) < (((r.val + 1 : ℕ) : ℤ) : ℝ) ^ 2 / (4 * m) := by
    apply div_pos _ (by positivity)
    have : (0 : ℝ) < (((r.val + 1 : ℕ) : ℤ) : ℝ) := by exact_mod_cast (show (0 : ℤ) < r.val + 1 by omega)
    positivity
  exact_mod_cast this.ne'

/-- The lattice model of row `s`. -/
abbrev Ns (r : Fin (m - 1)) : OrdVModule (V2mPlus m hm) (LatModuleGen (latP m)) :=
  resN m hm (latticeModule m hm ((r.val + 1 : ℕ) : ℤ))

theorem es_weight (r : Fin (m - 1)) : latVacuumGen (latP m) ∈ (Ns m hm r).weight (hC m r) := by
  rw [hC_eq]; exact latticeModule_vacuum_mem m hm _

theorem es_Omega (r : Fin (m - 1)) : latVacuumGen (latP m) ∈ Omega (Ns m hm r).toWeakModule :=
  lat_top_Omega m hm _ (by rw [abs_of_nonneg (by positivity)]; have := r.isLt; omega)

theorem es_L0 (r : Fin (m - 1)) : L0 (Ns m hm r).toWeakModule (latVacuumGen (latP m)) =
    hC m r • latVacuumGen (latP m) :=
  (Ns m hm r).L0_weight _ _ (es_weight m hm r)

/-- The weight-`(h_s + 1)` space of `V_{L+λ_s}` (`s ≤ m - 2`) is spanned by `x₀ ⊗ e⁰`. -/
theorem lat_weight_next_mem_span (r : Fin (m - 1)) (hs : r.val + 3 ≤ m) {v : LatModuleGen (latP m)}
    (hv : v ∈ (latticeModule m hm ((r.val + 1 : ℕ) : ℤ)).weight (hC m r + 1)) :
    v ∈ Submodule.span ℂ {latStateGen (latP m) (X ((0 : ℕ), a0 m)) 0} := by
  set s : ℤ := ((r.val + 1 : ℕ) : ℤ) with hsdef
  change v ∈ shiftWeightSpace (latP m) (glueLat m s) (glueIota m s) (glueDelta m s) (hC m r + 1) at hv
  refine (iSup₂_le (fun p hp => ?_) : shiftWeightSpace (latP m) (glueLat m s) (glueIota m s)
    (glueDelta m s) (hC m r + 1) ≤ _) hv
  obtain ⟨w, n⟩ := p
  change ℤ at n
  obtain ⟨hw, hwt⟩ := hp
  simp only at hw hwt
  rw [shiftWeight_rankOne m hm s, hC_eq] at hwt
  have hre := congrArg Complex.re hwt
  simp only [Complex.ofReal_re, Complex.add_re, Complex.one_re] at hre
  have hwn : ((w.toNat : ℕ) : ℝ) = (w : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hw
  rw [hwn] at hre
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hZ : (4 * m * w + (2 * m * n + s) ^ 2 : ℤ) = s ^ 2 + 4 * m := by
    have hsR : ((s : ℤ) : ℝ) = (r.val : ℝ) + 1 := by rw [hsdef]; push_cast; ring
    have : ((4 * m * w + (2 * m * n + s) ^ 2 : ℤ) : ℝ) = ((s ^ 2 + 4 * m : ℤ) : ℝ) := by
      push_cast
      field_simp at hre
      push_cast at hre
      rw [hsR]
      rw [hsR] at hre
      linarith
    exact_mod_cast this
  have hmZ : (2 : ℤ) ≤ m - s := by omega
  have hs1 : (1 : ℤ) ≤ s := by omega
  have hmz : (0 : ℤ) < m := by omega
  have hkey : w + m * n ^ 2 + n * s = 1 := by
    have h4 : (4 * m : ℤ) * (w + m * n ^ 2 + n * s) = 4 * m * 1 := by nlinarith [hZ]
    exact mul_left_cancel₀ (by positivity) h4
  have hn : n = 0 := by
    rcases lt_trichotomy n 0 with h | h | h
    · -- `n ≤ -1`: `m n² + n s ≥ m - s ≥ 2`
      have h1 : (1 : ℤ) ≤ -n := by omega
      have h2 : (2 : ℤ) ≤ m * (-n) - s := by nlinarith
      have h3 : (m : ℤ) * n ^ 2 + n * s = (-n) * (m * (-n) - s) := by ring
      have h4 : (1 : ℤ) * 2 ≤ (-n) * (m * (-n) - s) := mul_le_mul h1 h2 (by norm_num) (by omega)
      omega
    · exact h
    · have : m * n ^ 2 + n * s ≥ 3 := by nlinarith
      omega
  subst hn
  have hw1 : w = 1 := by simpa using hkey
  subst hw1
  intro y hy
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hy
  have hq1 : q ∈ gradingWN (rank (latP m)) 1 := by
    rw [gradingZN_of_nonneg (by norm_num)] at hq; exact hq
  have hspan := fock_weight_one_mem_span hq1
  have hmap := Submodule.mem_map_of_mem (f := mkEα (latP m) ((0 : ℤ) : (latP m).carrier)) hspan
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  have ha : a = a0 m := by
    apply Fin.ext
    have h1 := a.isLt
    have h2 : rank (latP m) = 1 := rank_latP m
    simp only [a0]
    omega
  subst ha
  rfl

/-- `L(1)ω = 0` in `V⁺` (`m ≥ 2`). -/
theorem L1_omega_zero_gen (hm2 : 2 ≤ m) : (V2mPlus m hm).L 1 (V2mPlus m hm).conformalVector = 0 := by
  have hg : (V2mPlus m hm).L 1 (V2mPlus m hm).conformalVector ∈ (V2mPlus m hm).grading 1 := by
    have := (V2mPlus m hm).toPreVertexAlgebra.smul_mem_grading (V2mPlus m hm).conformal_mem
      (V2mPlus m hm).conformal_mem 2
    rw [VertexOperatorAlgebra.L_def]
    simpa using this
  rw [grading_one_eq_bot m hm hm2, Submodule.mem_bot] at hg
  exact hg

/-- Every weight-`(h_s+1)` vector of the lattice model is a multiple of `L(-1)e`. -/
theorem lat_weight_next_eq (hm2 : 2 ≤ m) (r : Fin (m - 1)) (hs : r.val + 3 ≤ m)
    {v : LatModuleGen (latP m)} (hv : v ∈ (Ns m hm r).weight (hC m r + 1)) :
    ∃ c : ℂ, v = c • mode ((Ns m hm r).YM (V2mPlus m hm).conformalVector) 0 (latVacuumGen (latP m)) := by
  set e := latVacuumGen (latP m)
  set T := mode ((Ns m hm r).YM (V2mPlus m hm).conformalVector) 0 e
  have hT : T ∈ (Ns m hm r).weight (hC m r + 1) := by
    have h := mode_mem_weight (Ns m hm r) (V2mPlus m hm).conformal_mem (es_weight m hm r) 0
    have hc : hC m r + ((2 : ℤ) : ℂ) - ((0 : ℤ) : ℂ) - 1 = hC m r + 1 := by push_cast; ring
    rwa [hc] at h
  have hT0 : T ≠ 0 := by
    intro hT0
    have hc := L1_comm (Ns m hm r).toWeakModule (V2mPlus m hm).conformal_mem 0 e
    rw [L1_omega_zero_gen m hm hm2, map_zero, mode_zero, LinearMap.zero_apply, add_zero,
      Omega_mode_vanish (es_Omega m hm r) (V2mPlus m hm).conformal_mem (show (2 : ℤ) ≤ 2 by norm_num),
      map_zero, sub_zero] at hc
    rw [show mode ((Ns m hm r).toWeakModule.YM (V2mPlus m hm).conformalVector) 0 e = 0 from hT0,
      map_zero] at hc
    have hL := es_L0 m hm r
    change mode ((Ns m hm r).YM (V2mPlus m hm).conformalVector) (0 + 1) e = _ at hL
    rw [hL, smul_smul] at hc
    have he0 : e ≠ 0 := latVacuumGen_ne_zero' m hm
    have : ((((2 * 2 - 0 - 2 : ℤ) : ℂ)) * hC m r) • e = 0 := hc.symm
    rcases smul_eq_zero.mp this with h | h
    · exact hC_ne_zero m hm2 r (by simpa using h)
    · exact he0 h
  obtain ⟨cv, hcv⟩ := Submodule.mem_span_singleton.mp (lat_weight_next_mem_span m hm r hs hv)
  obtain ⟨cT, hcT⟩ := Submodule.mem_span_singleton.mp (lat_weight_next_mem_span m hm r hs hT)
  have hcT0 : cT ≠ 0 := by
    rintro rfl; rw [zero_smul] at hcT; exact hT0 hcT.symm
  refine ⟨cv / cT, ?_⟩
  rw [← hcv, ← hcT, smul_smul, div_mul_cancel₀ _ hcT0]

/-- **General transfer.**  Row `s = r + 1 ≤ m - 2`, unique at weight `h_s`. -/
theorem transfer_Omega_gen (hm2 : 2 ≤ m) (r : Fin (m - 1)) (hs : r.val + 3 ≤ m)
    (huq : ∀ j : Label m, ((weight m j : ℚ) : ℂ) = hC m r → j = .inl r)
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule (V2mPlus m hm) M) {x : M} (hxΩ : x ∈ Omega A)
    (hxL : L0 A x = hC m r • x)
    (hlow : ∀ μ : ℂ, μ.re < (hC m r).re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0)
    {k : ℤ} {t : VP m hm} (ht : t ∈ (V2mPlus m hm).grading k) :
    ∃ c : ℂ, mode (A.YM t) (k - 2) x -
      c • mode (A.YM (V2mPlus m hm).conformalVector) 0 x ∈ Omega A := by
  set e := latVacuumGen (latP m)
  set B := (Ns m hm r).toWeakModule
  set ω := (V2mPlus m hm).conformalVector
  have hte : mode ((Ns m hm r).YM t) (k - 2) e ∈ (Ns m hm r).weight (hC m r + 1) := by
    have h := mode_mem_weight (Ns m hm r) ht (es_weight m hm r) (k - 2)
    have hc : hC m r + (k : ℂ) - ((k - 2 : ℤ) : ℂ) - 1 = hC m r + 1 := by push_cast; ring
    rwa [hc] at h
  obtain ⟨c, hc⟩ := lat_weight_next_eq m hm hm2 r hs hte
  refine ⟨c, ?_⟩
  intro β b hb n hn
  have hχx := top_char_unique m hm hm2 A hxΩ hxL (.inl r) huq
  have hχe := lat_top_char m hm hm2 r
  rcases eq_or_lt_of_le hn with hnβ | hnβ
  · subst hnβ
    by_cases hβ0 : β < 0
    · rw [(V2mPlus m hm).positivity β hβ0, Submodule.mem_bot] at hb
      subst hb
      rw [map_zero, mode_zero, LinearMap.zero_apply]
    obtain ⟨P, rfl⟩ : ∃ P : ℕ, β = P := ⟨β.toNat, by omega⟩
    have h1 := lowering_composite_eq A ht hb hxΩ P (k - 2) le_rfl (by ring)
    have h2 := lowering_composite_eq A (V2mPlus m hm).conformal_mem hb hxΩ P 0 le_rfl (by ring)
    have h1e := lowering_composite_eq B ht hb (es_Omega m hm r) P (k - 2) le_rfl (by ring)
    have h2e := lowering_composite_eq B (V2mPlus m hm).conformal_mem hb (es_Omega m hm r) P 0
      le_rfl (by ring)
    rw [← topEvaluation_mk A x hxΩ, hχx] at h1 h2
    rw [← topEvaluation_mk B e (es_Omega m hm r), hχe] at h1e h2e
    have hrel : mode (B.YM b) P (mode (B.YM t) (k - 2) e) =
        c • mode (B.YM b) P (mode (B.YM ω) 0 e) := by
      change mode (B.YM b) P (mode ((Ns m hm r).YM t) (k - 2) e) = _
      rw [hc, map_smul]
    rw [h1e, h2e, smul_smul] at hrel
    set χ := chiT m hm hm2 (.inl r)
    have hs0 : (χ (VOA.mk (V2mPlus m hm) (zstate (V2mPlus m hm) t b P)) -
        c * χ (VOA.mk (V2mPlus m hm) (zstate (V2mPlus m hm) ω b P))) • e = 0 := by
      rw [sub_smul, hrel, sub_self]
    rw [map_sub, map_smul, h1, h2, smul_smul, ← sub_smul]
    rcases smul_eq_zero.mp hs0 with h | h
    · rw [h, zero_smul]
    · exact absurd h (latVacuumGen_ne_zero' m hm)
  · have hxg : x ∈ (L0 A).maxGenEigenspace (hC m r) :=
      Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hxL)
    have hv : mode (A.YM t) (k - 2) x - c • mode (A.YM ω) 0 x ∈
        (L0 A).maxGenEigenspace (hC m r + 1) := by
      have h1 := mode_mem_maxGenEigenspace A ht (k - 2) hxg
      have h2 := mode_mem_maxGenEigenspace A (V2mPlus m hm).conformal_mem 0 hxg
      have hc1 : hC m r + ((k - (k - 2) - 1 : ℤ) : ℂ) = hC m r + 1 := by push_cast; ring
      have hc2 : hC m r + ((2 - 0 - 1 : ℤ) : ℂ) = hC m r + 1 := by push_cast; ring
      rw [hc1] at h1
      rw [hc2] at h2
      exact Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h2)
    have h3 := mode_mem_maxGenEigenspace A hb n hv
    apply hlow _ _ _ h3
    have : ((β - n - 1 : ℤ) : ℝ) ≤ -2 := by exact_mod_cast (show β - n - 1 ≤ -2 by omega)
    rw [Complex.add_re, Complex.add_re, Complex.intCast_re, Complex.one_re]
    linarith

end VOA.Classification.COne.PlusRat3
