import VOA.Classification.COne.PlusRat3Quad
import VOA.Classification.COne.PlusRat3Iterate
import VOA.Classification.COne.PlusRat2Charged

/-! # Top characters, the lattice models, and the transfer lemma

* `top_char_unique`: on a top vector `y` with `L(0)y = c y`, if exactly one row `i` of the
  character table has weight `c`, then every Zhu element acts on `y` by its value at `i`.
  (`A(V_{2m}⁺) ≅ ℂ^{m+7}`; the idempotent of row `i` acts as the identity on `y`.)
* `chiT_H4`, `chiT_H6`: Abe's `H⁴, H⁶` vanish at every charged row (`H⁴, H⁶ ∈ O(V_{2m})`).
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

@[reducible] local instance zhuRing3 : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance zhuAlgebra3 : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

/-! ## §1  The character table and unique rows -/

/-- The proved character table (one character per label). -/
def chiT (hm2 : 2 ≤ m) : Label m → (VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ) :=
  Classical.choose (exists_characterTable m hm hm2)

theorem chiT_hasValues (hm2 : 2 ≤ m) (i : Label m) : HasValues m hm i (chiT m hm hm2 i) :=
  (Classical.choose_spec (exists_characterTable m hm hm2)).1 i

theorem chiT_injective (hm2 : 2 ≤ m) : Function.Injective (chiT m hm hm2) :=
  (Classical.choose_spec (exists_characterTable m hm hm2)).2

/-- **Unique-row top character.** -/
theorem top_char_unique (hm2 : 2 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule (V2mPlus m hm) M) {y : M} (hy : y ∈ Omega A) {c : ℂ}
    (hL : L0 A y = c • y) (i : Label m)
    (huniq : ∀ j : Label m, ((weight m j : ℚ) : ℂ) = c → j = i)
    (r : VOA.A (V2mPlus m hm)) :
    topEvaluation A y hy r = chiT m hm hm2 i r • y := by
  classical
  set χ := chiT m hm hm2
  letI := finiteDimensional_A_of_C2Cofinite _ (V2mPlus_c2Cofinite m hm)
  have hdim : Module.finrank ℂ (VOA.A (V2mPlus m hm)) ≤ Fintype.card (Label m) := by
    rw [V2mPlus_zhu_finrank m hm hm2, card_label m hm]
  let e := characterAlgEquiv χ (chiT_injective m hm hm2) hdim
  have he_apply : ∀ r j, e r j = χ j r := fun _ _ => rfl
  set f := topEvaluation A y hy
  -- the idempotent of row `i`
  let ε : VOA.A (V2mPlus m hm) := e.symm (fun j => if j = i then 1 else 0)
  let ξ : VOA.A (V2mPlus m hm) :=
    e.symm (fun j => if j = i then 0 else (χ j (generator m hm 0) - c)⁻¹)
  have hω : f (generator m hm 0 - algebraMap ℂ _ c) = 0 := by
    rw [map_sub, topEvaluation_omega m hm A hy, Algebra.algebraMap_eq_smul_one, map_smul,
      topEvaluation_one, hL, sub_self]
  have hfac : (1 : VOA.A (V2mPlus m hm)) - ε = ξ * (generator m hm 0 - algebraMap ℂ _ c) := by
    apply e.injective
    funext j
    rw [map_sub, map_one, map_mul, map_sub, AlgEquiv.commutes, AlgEquiv.apply_symm_apply,
      AlgEquiv.apply_symm_apply]
    simp only [Pi.sub_apply, Pi.one_apply, Pi.mul_apply, Pi.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, he_apply]
    by_cases hj : j = i
    · subst hj; simp
    · rw [if_neg hj, if_neg hj, sub_zero]
      have hne : χ j (generator m hm 0) - c ≠ 0 := by
        rw [hasValues_omega m hm (chiT_hasValues m hm hm2 j), sub_ne_zero]
        exact fun h => hj (huniq j h)
      exact (inv_mul_cancel₀ hne).symm
  have hε : f ε = y := by
    have h1 : f (1 - ε) = 0 := by
      rw [hfac]
      obtain ⟨s, hs⟩ := VOA.mk_surjective (V2mPlus m hm) ξ
      rw [← hs, topEvaluation_mk_mul, hω, map_zero]
    rw [map_sub, topEvaluation_one, sub_eq_zero] at h1
    exact h1.symm
  have hrε : r * ε = χ i r • ε := by
    apply e.injective
    funext j
    rw [map_mul, map_smul, AlgEquiv.apply_symm_apply]
    simp only [Pi.mul_apply, Pi.smul_apply, he_apply, smul_eq_mul]
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  obtain ⟨a, rfl⟩ := VOA.mk_surjective (V2mPlus m hm) r
  have h2 : f (VOA.mk (V2mPlus m hm) a * ε) = f (VOA.mk (V2mPlus m hm) a) := by
    rw [topEvaluation_mk_mul, hε, topEvaluation_mk]
  rw [← h2, hrε, map_smul, hε]

/-! ## §2  `H⁴, H⁶ ∈ O(V_{2m})` -/

/-- `Σ c·Pres(h, x_i, n)` from triples `(c, i, n)`. -/
def presList : List (ℚ × ℕ × ℕ) → List (ℚ × RawPoly ℕ)
  | [] => []
  | (c, i, n) :: rest => (c, presR 1 [(1, [0])] [(1, [i])] n) :: presList rest

theorem ls_lc_presList_mem_O : ∀ L : List (ℚ × ℕ × ℕ), ls m (lc (presList L)) ∈ O (V2m m hm)
  | [] => by rw [presList, lc, ls_nil]; exact Submodule.zero_mem _
  | (c, i, n) :: rest => by
    rw [presList, lc, ls_append, ls_scaleR]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (ls_lc_presList_mem_O rest)
    rw [← ls_Pres m hm]
    exact Pres_mem_O _ (h_mem_grading m hm) _ _

def h4PresL : List (ℚ × ℕ × ℕ) := [(-1 / 3, 0, 0), (1 / 3, 0, 1), (-1 / 3, 1, 0)]
def h6PresL : List (ℚ × ℕ × ℕ) :=
  [(1 / 2, 0, 0), (1 / 10, 0, 1), (-4 / 5, 0, 2), (1 / 5, 0, 3), (1 / 2, 1, 0), (17 / 10, 1, 1),
   (-13 / 10, 1, 2), (11 / 10, 2, 1)]

theorem h4Pres_cert : normR H4R = normR (lc (presList h4PresL)) := by decide +kernel
theorem h6Pres_cert : normR H6R = normR (lc (presList h6PresL)) := by decide +kernel

theorem H4_mem_O : ls m H4R ∈ O (V2m m hm) := by
  rw [← ls_normR, h4Pres_cert, ls_normR]; exact ls_lc_presList_mem_O m hm _

theorem H6_mem_O : ls m H6R ∈ O (V2m m hm) := by
  rw [← ls_normR, h6Pres_cert, ls_normR]; exact ls_lc_presList_mem_O m hm _

/-! ## §3  Gradings -/

theorem HP_mem_grading (t : ℕ) (ht : 1 ≤ t) (ht4 : t ≤ 4) :
    HP m hm t ∈ (V2mPlus m hm).grading ((2 * t : ℕ) : ℤ) := by
  rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 by omega) with rfl | rfl | rfl | rfl
  · exact (V2mPlus m hm).conformal_mem
  all_goals
    change ((HP m hm _ : VP m hm) : LatModuleGen (latP m)) ∈ (V2m m hm).grading _
    rw [hasN_HP m hm _ (by norm_num) (by norm_num)]
    exact latStateGen_mem_grading m hm (evR_mem_grading (a0 m) _ (by decide))

theorem LmV_mem_grading {y : VP m hm} {k : ℤ} (hy : y ∈ (V2mPlus m hm).grading k) :
    ∀ j : ℕ, LmV m hm j y ∈ (V2mPlus m hm).grading (k + j)
  | 0 => by simpa [LmV] using hy
  | j + 1 => by
    rw [LmV, Function.iterate_succ_apply', ← LmV, L_neg_one_eq_smul]
    have h := (V2mPlus m hm).toPreVertexAlgebra.smul_mem_grading (V2mPlus m hm).conformal_mem
      (LmV_mem_grading hy j) 0
    rwa [show (2 : ℤ) + (k + j) - 0 - 1 = k + ((j + 1 : ℕ) : ℤ) by push_cast; ring] at h

/-! ## §4  The lattice tops -/

section Lattice
variable (hm2 : 2 ≤ m)

/-- The charged lattice top `e^{λ_{r+1}}` of `V_{L+λ_{r+1}}`, as a `V⁺`-top vector. -/
theorem lat_top_Omega (j : ℤ) (hj : |j| ≤ m) :
    latVacuumGen (latP m) ∈ Omega (resN m hm (latticeModule m hm j)).toWeakModule :=
  lowest_mem_Omega m hm _ (latticeModule_isLowestWeight m hm j hj) (latticeModule_vacuum_mem m hm j)

/-- The charged lattice top has the table character of its row. -/
theorem lat_top_char (r : Fin (m - 1)) (ρ : VOA.A (V2mPlus m hm)) :
    topEvaluation (resN m hm (latticeModule m hm ((r.val + 1 : ℕ) : ℤ))).toWeakModule
      (latVacuumGen (latP m)) (lat_top_Omega m hm _ (by
        rw [abs_of_nonneg (by positivity)]; have := r.isLt; omega)) ρ =
      chiT m hm hm2 (.inl r) ρ • latVacuumGen (latP m) := by
  have hr := r.isLt
  set s : ℕ := r.val + 1 with hs
  have hj : |(s : ℤ)| < (m : ℤ) := by
    rw [abs_of_nonneg (by positivity)]; omega
  set χ := chiT m hm hm2 (.inl r)
  have hχ := chiT_hasValues m hm hm2 (.inl r)
  let h : ℂ := (((((s : ℤ) : ℝ) ^ 2 / (4 * m) : ℝ)) : ℂ)
  let N := resN m hm (latticeModule m hm s)
  have hlow : IsLowestWeight N h := latticeModule_isLowestWeight m hm s hj.le
  have hx : latVacuumGen (latP m) ∈ N.weight h := latticeModule_vacuum_mem m hm s
  have hval : (((values m (twistedScale m) (.inl r)).1 : ℝ) : ℂ) = h := by
    simp [values, h, hs]
  have hΩ := lowest_mem_Omega m hm N hlow hx
  have g0 : oMod N (gP m hm 0) (latVacuumGen (latP m)) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 0)) • latVacuumGen (latP m) := by
    rw [hχ.1, hval]
    change oMod N (V2mPlus m hm).conformalVector _ = h • _
    rw [oMod_conformalVector]; exact N.L0_weight _ _ hx
  have g1 : oMod N (gP m hm 1) (latVacuumGen (latP m)) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 1)) • latVacuumGen (latP m) := by
    rw [hχ.2.1]
    change oMod N (WP m hm) _ = _
    rw [oMod_resN m hm _ (WP_mem_grading m hm), WP_coe, oMod_W_V2m m hm _ hlow hx]
    congr 1
    simp [values, h, hs, Complex.ofReal_mul]
  have g2 : oMod N (gP m hm 2) (latVacuumGen (latP m)) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 2)) • latVacuumGen (latP m) := by
    rw [hχ.2.2]
    change oMod N (EP m hm) _ = _
    rw [oMod_resN m hm _ (EP_mem_grading m hm), oMod_E_lat_vac m hm s hj]
    simp [values]
  apply topEvaluation_eq_char m hm hm2 N.toWeakModule hΩ χ
  intro i
  rw [topEvaluation_mk_eq_oMod m hm N hΩ (gP_mem_grading m hm i)]
  fin_cases i
  exacts [g0, g1, g2]

/-- Abe's `H⁴` and `H⁶` vanish at every charged row. -/
theorem chiT_HP_zero (r : Fin (m - 1)) (t : ℕ) (ht : t = 2 ∨ t = 3) :
    chiT m hm hm2 (.inl r) (VOA.mk (V2mPlus m hm) (HP m hm t)) = 0 := by
  have hr := r.isLt
  have hj : |((r.val + 1 : ℕ) : ℤ)| ≤ (m : ℤ) := by
    rw [abs_of_nonneg (by positivity)]; omega
  set N := latticeModule m hm ((r.val + 1 : ℕ) : ℤ)
  have hlow := latticeModule_isLowestWeight m hm _ hj
  have hx := latticeModule_vacuum_mem m hm ((r.val + 1 : ℕ) : ℤ)
  have hgr := HP_mem_grading m hm t (by omega) (by omega)
  have h1 := lat_top_char m hm hm2 r (VOA.mk (V2mPlus m hm) (HP m hm t))
  rw [topEvaluation_mk_eq_oMod m hm _ _ hgr, oMod_resN m hm _ hgr,
    hasN_HP m hm t (by omega) (by omega)] at h1
  have h0 : oMod N (ls m (HR t)) (latVacuumGen (latP m)) = 0 := by
    rcases ht with rfl | rfl
    · exact oMod_eq_zero_of_mem_O N hlow (H4_mem_O m hm) hx
    · exact oMod_eq_zero_of_mem_O N hlow (H6_mem_O m hm) hx
  rw [h0] at h1
  rcases smul_eq_zero.mp h1.symm with h | h
  · exact h
  · exact absurd h (latVacuumGen_ne_zero' m hm)

end Lattice

/-! ## §5  The rows of weight `1/24` and `25/24` at `m = 6` -/

theorem weight_six_eq_iff_one (j : Label 6) : weight 6 j = 1 / 24 → j = .inl 0 := by
  revert j; decide +kernel

theorem weight_six_eq_iff_five (j : Label 6) : weight 6 j = 25 / 24 → j = .inl 4 := by
  revert j; decide +kernel

theorem uniq_six_one : ∀ j : Label 6, ((weight 6 j : ℚ) : ℂ) = (1 / 24 : ℂ) → j = .inl 0 := by
  intro j h
  apply weight_six_eq_iff_one
  have h' : ((weight 6 j : ℚ) : ℂ) = ((1 / 24 : ℚ) : ℂ) := by rw [h]; norm_num
  exact Rat.cast_injective h'

theorem uniq_six_five : ∀ j : Label 6, ((weight 6 j : ℚ) : ℂ) = (25 / 24 : ℂ) → j = .inl 4 := by
  intro j h
  apply weight_six_eq_iff_five
  have h' : ((weight 6 j : ℚ) : ℂ) = ((25 / 24 : ℚ) : ℂ) := by rw [h]; norm_num
  exact Rat.cast_injective h'

/-! ## §6  The lattice model at weight `25/24` (`m = 6`, `j = 1`) is one-dimensional -/

section SixLattice
variable (hm6 : 1 ≤ 6)

/-- The weight-`25/24` space of `V_{L+λ₁}` is spanned by `x₀ ⊗ e⁰`. -/
theorem lat_weight_25_mem_span {v : LatModuleGen (latP 6)}
    (hv : v ∈ (latticeModule 6 hm6 1).weight (25 / 24)) :
    v ∈ Submodule.span ℂ {latStateGen (latP 6) (X ((0 : ℕ), a0 6)) 0} := by
  change v ∈ shiftWeightSpace (latP 6) (glueLat 6 1) (glueIota 6 1) (glueDelta 6 1) (25 / 24) at hv
  refine (iSup₂_le (fun p hp => ?_) : shiftWeightSpace (latP 6) (glueLat 6 1) (glueIota 6 1)
    (glueDelta 6 1) (25 / 24) ≤ _) hv
  obtain ⟨w, n⟩ := p
  change ℤ at n
  obtain ⟨hw, hwt⟩ := hp
  simp only at hw hwt
  rw [shiftWeight_rankOne 6 hm6 1] at hwt
  have hre := congrArg Complex.re hwt
  simp only [Complex.ofReal_re] at hre
  have hwn : ((w.toNat : ℕ) : ℝ) = (w : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hw
  rw [hwn] at hre
  have hZ : (24 * w + (12 * n + 1) ^ 2 : ℤ) = 25 := by
    have : ((24 * w + (12 * n + 1) ^ 2 : ℤ) : ℝ) = 25 := by
      push_cast
      have h2 : ((2 * 6 * n + 1 : ℤ) : ℝ) = 12 * (n : ℝ) + 1 := by push_cast; ring
      norm_num at hre h2 ⊢
      nlinarith [hre]
    exact_mod_cast this
  have hn : n = 0 := by
    have hsq : 0 ≤ (12 * n + 1) ^ 2 := sq_nonneg _
    rcases lt_trichotomy n 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  subst hn
  have hw1 : w = 1 := by omega
  subst hw1
  intro y hy
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hy
  have hq1 : q ∈ gradingWN (rank (latP 6)) 1 := by
    rw [gradingZN_of_nonneg (by norm_num)] at hq; exact hq
  have hspan := fock_weight_one_mem_span hq1
  have hmap := Submodule.mem_map_of_mem (f := mkEα (latP 6) ((0 : ℤ) : (latP 6).carrier)) hspan
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  have ha : a = a0 6 := by
    apply Fin.ext
    have h1 := a.isLt
    have h2 : rank (latP 6) = 1 := rank_latP 6
    simp only [a0]
    omega
  subst ha
  rfl

end SixLattice

/-! ## §7  The transfer lemma (`m = 6`, row `c₁`) -/

section Transfer
variable (hm6 : 1 ≤ 6)

/-- The lattice model `V_{L+λ₁}` of the row `c₁`. -/
abbrev N1 : OrdVModule (V2mPlus 6 hm6) (LatModuleGen (latP 6)) := resN 6 hm6 (latticeModule 6 hm6 1)

theorem e1_weight : latVacuumGen (latP 6) ∈ (N1 hm6).weight (1 / 24) := by
  have h := latticeModule_vacuum_mem 6 hm6 1
  have hc : (((((1 : ℤ) : ℝ) ^ 2 / (4 * (6 : ℕ)) : ℝ)) : ℂ) = 1 / 24 := by push_cast; norm_num
  rw [hc] at h
  exact h

theorem e1_Omega : latVacuumGen (latP 6) ∈ Omega (N1 hm6).toWeakModule :=
  lat_top_Omega 6 hm6 1 (by norm_num)

theorem e1_L0 : L0 (N1 hm6).toWeakModule (latVacuumGen (latP 6)) =
    (1 / 24 : ℂ) • latVacuumGen (latP 6) :=
  (N1 hm6).L0_weight _ _ (e1_weight hm6)

/-- Every weight-`25/24` vector of the lattice model is a multiple of `L(-1)e`. -/
theorem lat_weight_25_eq (hm2 : 2 ≤ 6) {v : LatModuleGen (latP 6)}
    (hv : v ∈ (N1 hm6).weight (25 / 24)) :
    ∃ c : ℂ, v = c • mode ((N1 hm6).YM (V2mPlus 6 hm6).conformalVector) 0 (latVacuumGen (latP 6)) := by
  set e := latVacuumGen (latP 6)
  set T := mode ((N1 hm6).YM (V2mPlus 6 hm6).conformalVector) 0 e
  have hT : T ∈ (N1 hm6).weight (25 / 24) := by
    have h := mode_mem_weight (N1 hm6) (V2mPlus 6 hm6).conformal_mem (e1_weight hm6) 0
    have hc : (1 / 24 : ℂ) + ((2 : ℤ) : ℂ) - ((0 : ℤ) : ℂ) - 1 = 25 / 24 := by push_cast; norm_num
    rwa [hc] at h
  -- `L(1) T = 2 h e ≠ 0`
  have hT0 : T ≠ 0 := by
    intro hT0
    have hc := L1_comm (N1 hm6).toWeakModule (V2mPlus 6 hm6).conformal_mem 0 e
    have hL1ω : (V2mPlus 6 hm6).L 1 (V2mPlus 6 hm6).conformalVector = 0 := by
      have hg : (V2mPlus 6 hm6).L 1 (V2mPlus 6 hm6).conformalVector ∈ (V2mPlus 6 hm6).grading 1 := by
        have := (V2mPlus 6 hm6).toPreVertexAlgebra.smul_mem_grading (V2mPlus 6 hm6).conformal_mem
          (V2mPlus 6 hm6).conformal_mem 2
        rw [VertexOperatorAlgebra.L_def]
        simpa using this
      rw [grading_one_eq_bot 6 hm6 hm2, Submodule.mem_bot] at hg
      exact hg
    rw [hL1ω, map_zero, mode_zero, LinearMap.zero_apply, add_zero,
      Omega_mode_vanish (e1_Omega hm6) (V2mPlus 6 hm6).conformal_mem (show (2 : ℤ) ≤ 2 by norm_num),
      map_zero, sub_zero] at hc
    rw [show mode ((N1 hm6).toWeakModule.YM (V2mPlus 6 hm6).conformalVector) 0 e = 0 from hT0,
      map_zero] at hc
    have hL := e1_L0 hm6
    change mode ((N1 hm6).YM (V2mPlus 6 hm6).conformalVector) (0 + 1) e = _ at hL
    rw [hL, smul_smul] at hc
    have he0 : e ≠ 0 := latVacuumGen_ne_zero' 6 hm6
    have : ((((2 * 2 - 0 - 2 : ℤ) : ℂ)) * (1 / 24)) • e = 0 := hc.symm
    rcases smul_eq_zero.mp this with h | h
    · norm_num at h
    · exact he0 h
  obtain ⟨cv, hcv⟩ := Submodule.mem_span_singleton.mp (lat_weight_25_mem_span hm6 hv)
  obtain ⟨cT, hcT⟩ := Submodule.mem_span_singleton.mp (lat_weight_25_mem_span hm6 hT)
  have hcT0 : cT ≠ 0 := by
    rintro rfl; rw [zero_smul] at hcT; exact hT0 hcT.symm
  refine ⟨cv / cT, ?_⟩
  rw [← hcv, ← hcT, smul_smul, div_mul_cancel₀ _ hcT0]

/-- Membership in `maxGen` for an eigenvector. -/
theorem mem_maxGen_of_eigen {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule (V2mPlus 6 hm6) M) {x : M} {c : ℂ} (hL : L0 A x = c • x) :
    x ∈ (L0 A).maxGenEigenspace c :=
  Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hL)

/-- **Transfer.**  For every homogeneous `t ∈ V⁺_k`, a correction `t₍ₖ₋₂₎x - c L(-1)x` of the
degree-one vector is a top vector of the extension. -/
theorem transfer_Omega (hm2 : 2 ≤ 6) {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule (V2mPlus 6 hm6) M) {x : M} (hxΩ : x ∈ Omega A)
    (hxL : L0 A x = (1 / 24 : ℂ) • x)
    (hlow : ∀ μ : ℂ, μ.re < 1 / 24 → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0)
    {k : ℤ} {t : VP 6 hm6} (ht : t ∈ (V2mPlus 6 hm6).grading k) :
    ∃ c : ℂ, mode (A.YM t) (k - 2) x -
      c • mode (A.YM (V2mPlus 6 hm6).conformalVector) 0 x ∈ Omega A := by
  set e := latVacuumGen (latP 6)
  set B := (N1 hm6).toWeakModule
  set ω := (V2mPlus 6 hm6).conformalVector
  have hte : mode ((N1 hm6).YM t) (k - 2) e ∈ (N1 hm6).weight (25 / 24) := by
    have h := mode_mem_weight (N1 hm6) ht (e1_weight hm6) (k - 2)
    have hc : (1 / 24 : ℂ) + (k : ℂ) - ((k - 2 : ℤ) : ℂ) - 1 = 25 / 24 := by push_cast; ring
    rwa [hc] at h
  obtain ⟨c, hc⟩ := lat_weight_25_eq hm6 hm2 hte
  refine ⟨c, ?_⟩
  intro β b hb n hn
  have hχx := top_char_unique 6 hm6 hm2 A hxΩ hxL (.inl 0) uniq_six_one
  have hχe := top_char_unique 6 hm6 hm2 B (e1_Omega hm6) (e1_L0 hm6) (.inl 0) uniq_six_one
  rcases eq_or_lt_of_le hn with hnβ | hnβ
  · subst hnβ
    by_cases hβ0 : β < 0
    · rw [(V2mPlus 6 hm6).positivity β hβ0, Submodule.mem_bot] at hb
      subst hb
      rw [map_zero, mode_zero, LinearMap.zero_apply]
    obtain ⟨P, rfl⟩ : ∃ P : ℕ, β = P := ⟨β.toNat, by omega⟩
    have h1 := lowering_composite_eq A ht hb hxΩ P (k - 2) le_rfl (by ring)
    have h2 := lowering_composite_eq A (V2mPlus 6 hm6).conformal_mem hb hxΩ P 0 le_rfl (by ring)
    have h1e := lowering_composite_eq B ht hb (e1_Omega hm6) P (k - 2) le_rfl (by ring)
    have h2e := lowering_composite_eq B (V2mPlus 6 hm6).conformal_mem hb (e1_Omega hm6) P 0
      le_rfl (by ring)
    rw [← topEvaluation_mk A x hxΩ, hχx] at h1 h2
    rw [← topEvaluation_mk B e (e1_Omega hm6), hχe] at h1e h2e
    have hrel : mode (B.YM b) P (mode (B.YM t) (k - 2) e) =
        c • mode (B.YM b) P (mode (B.YM ω) 0 e) := by
      change mode (B.YM b) P (mode ((N1 hm6).YM t) (k - 2) e) = _
      rw [hc, map_smul]
    rw [h1e, h2e, smul_smul] at hrel
    set χ := chiT 6 hm6 hm2 (.inl 0)
    have hs : (χ (VOA.mk (V2mPlus 6 hm6) (zstate (V2mPlus 6 hm6) t b P)) -
        c * χ (VOA.mk (V2mPlus 6 hm6) (zstate (V2mPlus 6 hm6) ω b P))) • e = 0 := by
      rw [sub_smul, hrel, sub_self]
    rw [map_sub, map_smul, h1, h2, smul_smul, ← sub_smul]
    rcases smul_eq_zero.mp hs with h | h
    · rw [h, zero_smul]
    · exact absurd h (latVacuumGen_ne_zero' 6 hm6)
  · have hxg := mem_maxGen_of_eigen hm6 A hxL
    have hv : mode (A.YM t) (k - 2) x - c • mode (A.YM ω) 0 x ∈
        (L0 A).maxGenEigenspace (25 / 24) := by
      have h1 := mode_mem_maxGenEigenspace A ht (k - 2) hxg
      have h2 := mode_mem_maxGenEigenspace A (V2mPlus 6 hm6).conformal_mem 0 hxg
      have hc1 : (1 / 24 : ℂ) + ((k - (k - 2) - 1 : ℤ) : ℂ) = 25 / 24 := by push_cast; ring
      have hc2 : (1 / 24 : ℂ) + ((2 - 0 - 1 : ℤ) : ℂ) = 25 / 24 := by push_cast; ring
      rw [hc1] at h1
      rw [hc2] at h2
      exact Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h2)
    have h3 := mode_mem_maxGenEigenspace A hb n hv
    apply hlow _ _ _ h3
    have : ((β - n - 1 : ℤ) : ℝ) ≤ -2 := by exact_mod_cast (show β - n - 1 ≤ -2 by omega)
    rw [Complex.add_re, Complex.intCast_re]
    have h25 : (25 / 24 : ℂ).re = 25 / 24 := by norm_num
    rw [h25]
    linarith

end Transfer

end VOA.Classification.COne.PlusRat3
