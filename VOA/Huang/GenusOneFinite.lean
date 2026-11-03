import VOA.Huang.GenusOneReduction
import VOA.Modules.RationalityLattice

/-!
# Finite generation from C₂-cofiniteness of the insertion module

The induction uses an admissible refinement of the ordinary insertion module.
No dimension estimate on the traced weight spaces is substituted for trace recursion.
-/
namespace VOA.Huang.GenusOne
open VOA Module VOA.Huang.FusionC2 VOA.Huang.LWBottomRecovery VOA.Huang.BottomRecovery
open scoped BigOperators
universe u
variable {V M₁ M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V} {A : OrdVModule W M₁} {N : OrdVModule W M}

noncomputable def sqActDefect (A : OrdVModule W M₁) (a : V) (p : ℕ) (b : M₁) : M₁ :=
  ∑ᶠ i : ℤ, (if i = -2 then (0 : ℂ) else sqBracketCoeffZ p (-2) i) • mode (A.YM a) i b

theorem sqActDefect_support_finite (A : OrdVModule W M₁) (a : V) (p : ℕ) (b : M₁) :
    (Function.support fun i : ℤ =>
      (if i = -2 then (0 : ℂ) else sqBracketCoeffZ p (-2) i) • mode (A.YM a) i b).Finite := by
  refine Set.Finite.subset (sqAct_support_finite A a p (-2) b) (fun i hi => ?_)
  simp only [Function.mem_support, ne_eq] at hi ⊢
  intro hc
  apply hi
  by_cases h2 : i = -2
  · rw [if_pos h2, zero_smul]
  · rw [if_neg h2, hc]

/-- **Triangularity of the square bracket at `m = −2`**:
`a[−2]b = a₍₋₂₎b + sqActDefect`, the defect being supported on modes `i ≥ −1`. -/
theorem sqAct_neg_two_eq (A : OrdVModule W M₁) (a : V) (p : ℕ) (b : M₁) :
    sqAct A a p (-2) b = mode (A.YM a) (-2) b + sqActDefect A a p b := by
  rw [sqAct_apply, sqActDefect]
  have hsplit : ∀ i : ℤ, sqBracketCoeffZ p (-2) i • mode (A.YM a) i b
      = (if i = -2 then sqBracketCoeffZ p (-2) i • mode (A.YM a) i b else 0)
        + (if i = -2 then (0 : ℂ) else sqBracketCoeffZ p (-2) i) • mode (A.YM a) i b := by
    intro i
    by_cases h2 : i = -2
    · rw [if_pos h2, if_pos h2, zero_smul, add_zero]
    · rw [if_neg h2, if_neg h2, zero_add]
  rw [finsum_congr hsplit]
  have hfin1 : (Function.support fun i : ℤ =>
      (if i = -2 then sqBracketCoeffZ p (-2) i • mode (A.YM a) i b else 0)).Finite := by
    refine Set.Finite.subset (Set.finite_singleton (-2 : ℤ)) (fun i hi => ?_)
    simp only [Function.mem_support, ne_eq] at hi
    by_contra hne
    exact hi (if_neg hne)
  rw [finsum_add_distrib hfin1 (sqActDefect_support_finite A a p b)]
  congr 1
  rw [finsum_eq_single _ (-2 : ℤ) (fun i hi => if_neg hi), if_pos rfl,
    sqBracketCoeffZ_diag' p (-2), one_smul]


/-- The correction to the ordinary minus-two mode uses only lower module levels. -/
theorem sqActDefect_mem_lower (B : AdmissibleModule W M₁)
    (hBA : B.toWeakModule = A.toWeakModule) {p j : ℤ} {a : V} {w : M₁}
    (ha : a ∈ W.grading p) (hw : w ∈ B.lev j)
    (T : Submodule ℂ M₁) (hT : ∀ d : ℤ, d < j + p + 1 → B.lev d ≤ T) :
    sqActDefect A a p.toNat w ∈ T := by
  unfold sqActDefect
  refine finsum_mem_submodule_pd _ _ fun i => ?_
  by_cases hi : i = -2
  · rw [if_pos hi, zero_smul]; exact T.zero_mem
  rw [if_neg hi]
  by_cases hlow : i < -2
  · rw [sqBracketCoeffZ_of_lt _ hlow, zero_smul]; exact T.zero_mem
  refine T.smul_mem _ (hT (j + (p - i - 1)) (by omega) ?_)
  have h := B.act_lev ha hw (p := i)
  change mode (B.toWeakModule.YM a) i w ∈ _ at h
  rwa [hBA] at h

/-- Square modes of nonnegative index lie strictly below a minus-two product. -/
theorem sqAct_mem_lower (B : AdmissibleModule W M₁)
    (hBA : B.toWeakModule = A.toWeakModule) {p j m : ℤ} {a : V} {w : M₁}
    (ha : a ∈ W.grading p) (hw : w ∈ B.lev j) (hm : 0 ≤ m)
    (T : Submodule ℂ M₁) (hT : ∀ d : ℤ, d < j + p + 1 → B.lev d ≤ T) :
    sqAct A a p.toNat m w ∈ T := by
  rw [sqAct_apply]
  refine finsum_mem_submodule_pd _ _ fun i => ?_
  by_cases hi : i < m
  · rw [sqBracketCoeffZ_of_lt _ hi, zero_smul]; exact T.zero_mem
  refine T.smul_mem _ (hT (j + (p - i - 1)) (by omega) ?_)
  have h := B.act_lev ha hw (p := i)
  change mode (B.toWeakModule.YM a) i w ∈ _ at h
  rwa [hBA] at h

/-- Lift the collected minus-two relation to a submodule of restricted q-series. -/
theorem trace_sqAct_negTwo_mem (Y : IntertwiningOperator A N N) {h : ℂ}
    (hcw : HasConformalWeight N h)
    (T : Submodule (↥SubexpPS) ↥(QSeriesAt (h - W.centralCharge / 24)))
    {p : ℕ} {a : V} (ha : a ∈ W.grading (p : ℤ)) (hp : 1 ≤ p) (w : M₁)
    (htail : ∀ m : ℕ, blockRestrict (trace_mem_QSeriesAt Y hcw)
      (sqAct A a p (2 * (m + 1) - 2 : ℤ) w) ∈ T) :
    blockRestrict (trace_mem_QSeriesAt Y hcw) (sqAct A a p (-2) w) ∈ T := by
  classical
  let S := blockRestrict (trace_mem_QSeriesAt Y hcw)
  let c (m : ℕ) : ↥SubexpPS :=
    ((2 * (m + 1) - 1 : ℕ) : ℂ) •
      (⟨PowerSeries.mk (zhuG (m + 1)), mk_zhuG_mem_subexpPS (m + 1)⟩ : ↥SubexpPS)
  obtain ⟨K, hK⟩ := sqAct_eventually_zero A a p w
  have hz : ∀ m : ℕ, K.toNat + 1 ≤ m → sqAct A a p (2 * (m + 1) - 2 : ℤ) w = 0 :=
    fun m hm => hK _ (by omega)
  have heq : S (sqAct A a p (-2) w) =
      -(∑ m ∈ Finset.range (K.toNat + 1), c m • S (sqAct A a p (2 * (m + 1) - 2 : ℤ) w)) := by
    apply Subtype.ext
    rw [Submodule.coe_neg, Submodule.coe_sum]
    change trace Y (sqAct A a p (-2) w) = _
    have hr := trace_sqAct_negTwo Y hp ha w
    rw [add_eq_zero_iff_eq_neg] at hr
    rw [hr]
    congr 1
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (K.toNat + 1)) (fun m hm => ?_)]
    · refine Finset.sum_congr rfl fun m _ => ?_
      change _ = psSMul (((2 * (m + 1) - 1 : ℕ) : ℂ) • PowerSeries.mk (zhuG (m + 1))) _
      rw [psSMul_smul_left _ _ (S (sqAct A a p (2 * (m + 1) - 2 : ℤ) w)).property, psSMul_mk]
      rfl
    · simp only [Function.mem_support] at hm
      simp only [Finset.mem_coe, Finset.mem_range]
      by_contra hn
      exact hm (by rw [hz m (by omega), map_zero, qConv_zero_right, smul_zero])
  rw [heq]
  exact T.neg_mem (T.sum_mem fun m _ => T.smul_mem _ (htail m))

/-- C₂ reduction step, with the Eisenstein tail absorbed into the coefficient ring. -/
theorem trace_negTwo_mem_lower (Y : IntertwiningOperator A N N) {h : ℂ}
    (hcw : HasConformalWeight N h) (B : AdmissibleModule W M₁)
    (hBA : B.toWeakModule = A.toWeakModule)
    (T : Submodule (↥SubexpPS) ↥(QSeriesAt (h - W.centralCharge / 24)))
    {p j : ℤ} {a : V} {w : M₁} (ha : a ∈ W.grading p) (hw : w ∈ B.lev j)
    (hT : ∀ d : ℤ, d < j + p + 1 → ∀ x ∈ B.lev d,
      blockRestrict (trace_mem_QSeriesAt Y hcw) x ∈ T) :
    blockRestrict (trace_mem_QSeriesAt Y hcw) (mode (A.YM a) (-2) w) ∈ T := by
  let S := blockRestrict (trace_mem_QSeriesAt Y hcw)
  let P : Submodule ℂ M₁ := (T.restrictScalars ℂ).comap S
  have hP : ∀ d : ℤ, d < j + p + 1 → B.lev d ≤ P := hT
  rcases lt_trichotomy p 0 with hp | hp | hp
  · rw [W.positivity p hp, Submodule.mem_bot] at ha
    simp only [ha, map_zero, mode_zero, LinearMap.zero_apply]
    exact T.zero_mem
  · subst p
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (vacuumGradeZero_holds W ha)
    have hv : mode (A.YM W.vacuum) (-2) w = 0 := by
      exact (A.toWeakModule.act_vacuum (-2) w).trans (if_neg (by norm_num))
    simp only [map_smul, mode_smul, LinearMap.smul_apply, hv, smul_zero, map_zero]
    exact T.zero_mem
  · have ha' : a ∈ W.grading (p.toNat : ℤ) := by rwa [Int.toNat_of_nonneg hp.le]
    have hsq : S (sqAct A a p.toNat (-2) w) ∈ T :=
      trace_sqAct_negTwo_mem Y hcw T ha' (by omega) w fun m =>
        sqAct_mem_lower B hBA ha hw (by omega) P hP
    have hdef : S (sqActDefect A a p.toNat w) ∈ T := sqActDefect_mem_lower B hBA ha hw P hP
    have heq := congrArg S (sqAct_neg_two_eq A a p.toNat w)
    rw [map_add] at heq
    have hm := T.sub_mem hsq hdef
    rwa [heq, add_sub_cancel_right] at hm

/-- Homogeneous C₂ representatives generate the entire trace span. -/
theorem trace_mem_span_of_C2_generators (Y : IntertwiningOperator A N N) {h : ℂ}
    (hcw : HasConformalWeight N h) (B : AdmissibleModule W M₁)
    (hBA : B.toWeakModule = A.toWeakModule) {U : Set M₁}
    (hU : ∀ s ∈ U, ∃ k, s ∈ B.lev k)
    (htop : (⊤ : Submodule ℂ M₁) = Submodule.span ℂ U ⊔ C2M B.toWeakModule) (w : M₁) :
    blockRestrict (trace_mem_QSeriesAt Y hcw) w ∈
      Submodule.span (↥SubexpPS) ((blockRestrict (trace_mem_QSeriesAt Y hcw)) '' U) := by
  let S := blockRestrict (trace_mem_QSeriesAt Y hcw)
  let T := Submodule.span (↥SubexpPS) (S '' U)
  let P : Submodule ℂ M₁ := (T.restrictScalars ℂ).comap S
  have hUP : Submodule.span ℂ U ≤ P := Submodule.span_le.mpr fun u hu =>
    Submodule.subset_span ⟨u, hu, rfl⟩
  have hlev : ∀ k : ℤ, B.lev k ≤ P := by
    intro k
    rcases lt_or_ge k 0 with hk | hk
    · rw [B.lev_eq_bot_of_neg k hk]; exact bot_le
    obtain ⟨K, rfl⟩ : ∃ K : ℕ, k = (K : ℤ) := ⟨k.toNat, by omega⟩
    induction K using Nat.strong_induction_on with
    | _ K IH =>
      have hlow : ∀ d : ℤ, d < (K : ℤ) → B.lev d ≤ P := by
        intro d hd
        rcases lt_or_ge d 0 with h0 | h0
        · rw [B.lev_eq_bot_of_neg d h0]; exact bot_le
        · obtain ⟨D, rfl⟩ : ∃ D : ℕ, d = (D : ℤ) := ⟨d.toNat, by omega⟩
          exact IH D (by exact_mod_cast hd) (by positivity)
      have hproj : ∀ s ∈ Submodule.span ℂ U, levProj B (K : ℤ) s ∈ Submodule.span ℂ U := by
        intro s hs
        induction hs using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨d, hd⟩ := hU z hz
          by_cases he : (K : ℤ) = d
          · rw [he, levProj_of_mem B hd]; exact Submodule.subset_span hz
          · rw [levProj_of_mem_ne B hd he]; exact Submodule.zero_mem _
        | zero => rw [map_zero]; exact Submodule.zero_mem _
        | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
        | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
      intro x hx
      have hxS : x ∈ Submodule.span ℂ U ⊔ C2M B.toWeakModule := by rw [← htop]; trivial
      obtain ⟨s, hs, c, hc, rfl⟩ := Submodule.mem_sup.mp hxS
      rw [← levProj_of_mem B hx, map_add]
      refine P.add_mem (hUP (hproj s hs)) ?_
      have hD := levProj_C2M B (K : ℤ) hc
      refine (Submodule.span_le.mpr ?_) hD
      rintro _ ⟨a, p, j, m, ha, hm, hjk, rfl⟩
      change S (mode (B.toWeakModule.YM a) (-2) m) ∈ T
      rw [hBA]
      exact trace_negTwo_mem_lower Y hcw B hBA T ha hm (fun d hd => hlow d (by omega))
  exact induction_lev B (motive := fun w => w ∈ P) w P.zero_mem
    (fun _ _ hx hy => P.add_mem hx hy) (fun k x hx => hlev k hx)

/-- Finite generation for general intertwiners from insertion-module C₂-cofiniteness.
An ordinary module already has an admissible refinement; no single-coset hypothesis
on A is needed. -/
theorem traceSpanFinite_of_moduleC2 (Y : IntertwiningOperator A N N) {h : ℂ}
    (hAC2 : ModuleC2Cofinite A.toWeakModule) (hcw : HasConformalWeight N h) :
    TraceSpanFinite Y hcw := by
  classical
  obtain ⟨U, hU, htop⟩ := exists_finset_homog (N := A.toAdmissible) hAC2
  let S := blockRestrict (trace_mem_QSeriesAt Y hcw)
  have heq : blockSpanS (trace_mem_QSeriesAt Y hcw) =
      Submodule.span (↥SubexpPS) (S '' (U : Set M₁)) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      exact trace_mem_span_of_C2_generators Y hcw A.toAdmissible rfl hU htop w
    · apply Submodule.span_mono
      rintro _ ⟨w, _, rfl⟩
      exact ⟨w, rfl⟩
  change (blockSpanS (trace_mem_QSeriesAt Y hcw)).FG
  rw [heq]
  exact Submodule.fg_span (U.finite_toSet.image S)

/-- Absolute convergence on the unit disc for any C₂-cofinite ordinary insertion module. -/
theorem summable_trace_of_moduleC2 (Y : IntertwiningOperator A N N) {h q : ℂ}
    (hAC2 : ModuleC2Cofinite A.toWeakModule) (hcw : HasConformalWeight N h)
    (hq : ‖q‖ < 1) (w : M₁) :
    Summable (fun n : ℕ => ‖trace Y w (h - W.centralCharge / 24 + n) * q ^ n‖) :=
  summable_trace_of_fg_closed Y hcw (traceSpanFinite_of_moduleC2 Y hAC2 hcw)
    (traceDerivativeClosed_holds Y hcw) hq w

theorem hasSum_trace_of_moduleC2 (Y : IntertwiningOperator A N N) {h : ℂ}
    (hAC2 : ModuleC2Cofinite A.toWeakModule) (hcw : HasConformalWeight N h)
    (w : M₁) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * (h - W.centralCharge / 24)) *
        (trace Y w (h - W.centralCharge / 24 + n) * qParam τ ^ n))
      (traceFunction Y h w τ) :=
  hasSum_trace_of_fg_closed Y hcw (traceSpanFinite_of_moduleC2 Y hAC2 hcw)
    (traceDerivativeClosed_holds Y hcw) w τ

end VOA.Huang.GenusOne
