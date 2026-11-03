import VOA.Huang.GenusOneBlocks

/-!
# Eisenstein finite generation for insertion blocks

The C₂ induction runs over `GSeries = ℂ[G₂,G₄,G₆]`, not merely the larger
subexponential coefficient ring. It applies to every formal insertion block.
Sources: Miyamoto, math/0010180, Lemmas 4.4–4.5; Zhu, §5.3.
The equations below have Eisenstein coefficients; weight-homogeneous scalar MLDE
covariance and trace realization are not inferred from this finiteness theorem.
-/
namespace VOA.Huang.GenusOne
open VOA Module VOA.Huang.FusionC2 VOA.Huang.LWBottomRecovery VOA.Huang.BottomRecovery
open scoped BigOperators
universe u
variable {V M₁ M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V} {A : OrdVModule W M₁} {N : OrdVModule W M}

/-- Lift the collected minus-two relation to a submodule of restricted q-series. -/
theorem block_sqAct_negTwo_mem_G (S₀ : M₁ →ₗ[ℂ] FormalQSeries) {b : ℂ}
    (hsupp : ∀ w, S₀ w ∈ QSeriesAt b) (hS : IsInsertionFormalBlock A S₀)
    (T : Submodule (↥GSeries) ↥(QSeriesAt (b)))
    {p : ℕ} {a : V} (ha : a ∈ W.grading (p : ℤ)) (hp : 1 ≤ p) (w : M₁)
    (htail : ∀ m : ℕ, blockRestrict hsupp
      (sqAct A a p (2 * (m + 1) - 2 : ℤ) w) ∈ T) :
    blockRestrict hsupp (sqAct A a p (-2) w) ∈ T := by
  classical
  let S := blockRestrict hsupp
  let c (m : ℕ) : ↥GSeries :=
    ((2 * (m + 1) - 1 : ℕ) : ℂ) •
      (⟨PowerSeries.mk (zhuG (m + 1)), mk_zhuG_mem_GSeries (by omega : 1 ≤ m + 1)⟩ : ↥GSeries)
  obtain ⟨K, hK⟩ := sqAct_eventually_zero A a p w
  have hz : ∀ m : ℕ, K.toNat + 1 ≤ m → sqAct A a p (2 * (m + 1) - 2 : ℤ) w = 0 :=
    fun m hm => hK _ (by omega)
  have heq : S (sqAct A a p (-2) w) =
      -(∑ m ∈ Finset.range (K.toNat + 1), c m • S (sqAct A a p (2 * (m + 1) - 2 : ℤ) w)) := by
    apply Subtype.ext
    rw [Submodule.coe_neg, Submodule.coe_sum]
    change S₀ (sqAct A a p (-2) w) = _
    have hr := hS.negTwo p hp a ha w
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
theorem block_negTwo_mem_lower_G (S₀ : M₁ →ₗ[ℂ] FormalQSeries) {b : ℂ}
    (hsupp : ∀ w, S₀ w ∈ QSeriesAt b) (hS : IsInsertionFormalBlock A S₀) (B : AdmissibleModule W M₁)
    (hBA : B.toWeakModule = A.toWeakModule)
    (T : Submodule (↥GSeries) ↥(QSeriesAt (b)))
    {p j : ℤ} {a : V} {w : M₁} (ha : a ∈ W.grading p) (hw : w ∈ B.lev j)
    (hT : ∀ d : ℤ, d < j + p + 1 → ∀ x ∈ B.lev d,
      blockRestrict hsupp x ∈ T) :
    blockRestrict hsupp (mode (A.YM a) (-2) w) ∈ T := by
  let S := blockRestrict hsupp
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
      block_sqAct_negTwo_mem_G S₀ hsupp hS T ha' (by omega) w fun m =>
        sqAct_mem_lower B hBA ha hw (by omega) P hP
    have hdef : S (sqActDefect A a p.toNat w) ∈ T := sqActDefect_mem_lower B hBA ha hw P hP
    have heq := congrArg S (sqAct_neg_two_eq A a p.toNat w)
    rw [map_add] at heq
    have hm := T.sub_mem hsq hdef
    rwa [heq, add_sub_cancel_right] at hm

/-- Homogeneous C₂ representatives generate the entire trace span. -/
theorem block_mem_span_C2_G (S₀ : M₁ →ₗ[ℂ] FormalQSeries) {b : ℂ}
    (hsupp : ∀ w, S₀ w ∈ QSeriesAt b) (hS : IsInsertionFormalBlock A S₀) (B : AdmissibleModule W M₁)
    (hBA : B.toWeakModule = A.toWeakModule) {U : Set M₁}
    (hU : ∀ s ∈ U, ∃ k, s ∈ B.lev k)
    (htop : (⊤ : Submodule ℂ M₁) = Submodule.span ℂ U ⊔ C2M B.toWeakModule) (w : M₁) :
    blockRestrict hsupp w ∈
      Submodule.span (↥GSeries) ((blockRestrict hsupp) '' U) := by
  let S := blockRestrict hsupp
  let T := Submodule.span (↥GSeries) (S '' U)
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
      exact block_negTwo_mem_lower_G S₀ hsupp hS B hBA T ha hm (fun d hd => hlow d (by omega))
  exact induction_lev B (motive := fun w => w ∈ P) w P.zero_mem
    (fun _ _ hx hy => P.add_mem hx hy) (fun k x hx => hlev k hx)

/-- Finite generation for general intertwiners from insertion-module C₂-cofiniteness.
An ordinary module already has an admissible refinement; no single-coset hypothesis
on A is needed. -/
theorem fg_insertionBlockSpan_G (S₀ : M₁ →ₗ[ℂ] FormalQSeries) {b : ℂ}
    (hsupp : ∀ w, S₀ w ∈ QSeriesAt b) (hS : IsInsertionFormalBlock A S₀)
    (hAC2 : ModuleC2Cofinite A.toWeakModule) :
    (Submodule.span (↥GSeries) (Set.range (blockRestrict hsupp))).FG := by
  classical
  obtain ⟨U, hU, htop⟩ := exists_finset_homog (N := A.toAdmissible) hAC2
  let S := blockRestrict hsupp
  have heq : Submodule.span (↥GSeries) (Set.range (blockRestrict hsupp)) =
      Submodule.span (↥GSeries) (S '' (U : Set M₁)) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      exact block_mem_span_C2_G S₀ hsupp hS A.toAdmissible rfl hU htop w
    · apply Submodule.span_mono
      rintro _ ⟨w, _, rfl⟩
      exact ⟨w, rfl⟩
  change (Submodule.span (↥GSeries) (Set.range (blockRestrict hsupp))).FG
  rw [heq]
  exact Submodule.fg_span (U.finite_toSet.image S)


/-- The Euler derivative of each block value lies in its Eisenstein span.
This is a generator statement; no differential closure of the coefficient ring
is needed. -/
theorem block_qD_mem_G (S : M₁ →ₗ[ℂ] FormalQSeries) {b : ℂ}
    (hsupp : ∀ w, S w ∈ QSeriesAt b) (hS : IsInsertionFormalBlock A S) (w : M₁) :
    qD b (blockRestrict hsupp w) ∈
      Submodule.span (↥GSeries) (Set.range (blockRestrict hsupp)) := by
  classical
  let T := Submodule.span (↥GSeries) (Set.range (blockRestrict hsupp))
  obtain ⟨K, hK⟩ := sqL_tail_eventually_zero A w
  let c (m : ℕ) : ↥GSeries :=
    ⟨PowerSeries.mk (zhuG (m + 1)), mk_zhuG_mem_GSeries (by omega)⟩
  have heq : qD b (blockRestrict hsupp w) = blockRestrict hsupp (sqL A (-2) w) -
      ∑ m ∈ Finset.range K, c m • blockRestrict hsupp (sqL A (2 * (m + 1) - 2 : ℤ) w) := by
    apply Subtype.ext
    rw [qD_coe, Submodule.coe_sub, Submodule.coe_sum]
    change qDeriv (S w) = S (sqL A (-2) w) - _
    rw [show qDeriv (S w) = S (sqL A (-2) w) -
        ∑ᶠ m : ℕ, qConv (zhuG (m + 1)) (S (sqL A (2 * (m + 1) - 2 : ℤ) w)) from
      (eq_sub_iff_add_eq.mpr (hS.omega w).symm)]
    congr 1
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range K) (fun m hm => ?_)]
    · exact Finset.sum_congr rfl fun m _ => (psSMul_mk _ _).symm
    · simp only [Function.mem_support, Finset.mem_coe, Finset.mem_range] at hm ⊢
      by_contra hn
      exact hm (by rw [hK m (by omega), map_zero, qConv_zero_right])
  rw [heq]
  exact T.sub_mem (Submodule.subset_span ⟨_, rfl⟩)
    (T.sum_mem fun m _ => T.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩))

/-- An actual finite first-order Eisenstein system on block values of insertion
vectors, together with generation of every block value. Coefficients may depend
on the block. This does not assert modular weight compatibility. -/
theorem exists_eisenstein_system (S : M₁ →ₗ[ℂ] FormalQSeries) {b : ℂ}
    (hsupp : ∀ w, S w ∈ QSeriesAt b) (hS : IsInsertionFormalBlock A S)
    (hAC2 : ModuleC2Cofinite A.toWeakModule) :
    ∃ (U : Finset M₁) (B : U → U → ↥GSeries),
      (∀ k : U, qD b (blockRestrict hsupp k.val) =
        ∑ l : U, B k l • blockRestrict hsupp l.val) ∧
      (∀ w, ∃ c : U → ↥GSeries, blockRestrict hsupp w =
        ∑ l : U, c l • blockRestrict hsupp l.val) := by
  classical
  obtain ⟨U, hU, htop⟩ := exists_finset_homog (N := A.toAdmissible) hAC2
  have hrange : (blockRestrict hsupp) '' (U : Set M₁) =
      Set.range (fun l : U => blockRestrict hsupp l.val) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩
    · rintro ⟨w, rfl⟩; exact ⟨w.val, w.property, rfl⟩
  have hgen : ∀ w, blockRestrict hsupp w ∈
      Submodule.span (↥GSeries) (Set.range (fun l : U => blockRestrict hsupp l.val)) := by
    intro w
    rw [← hrange]
    exact block_mem_span_C2_G S hsupp hS A.toAdmissible rfl hU htop w
  have hle : Submodule.span (↥GSeries) (Set.range (blockRestrict hsupp)) ≤
      Submodule.span (↥GSeries) (Set.range (fun l : U => blockRestrict hsupp l.val)) :=
    Submodule.span_le.mpr (by rintro _ ⟨w, rfl⟩; exact hgen w)
  have hsys : ∀ k : U, ∃ c : U → ↥GSeries,
      qD b (blockRestrict hsupp k.val) = ∑ l : U, c l • blockRestrict hsupp l.val := by
    intro k
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (↥GSeries)).mp
      (hle (block_qD_mem_G S hsupp hS k.val))
    exact ⟨c, hc.symm⟩
  choose B hB using hsys
  refine ⟨U, B, hB, fun w => ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (↥GSeries)).mp (hgen w)
  exact ⟨c, hc.symm⟩

/-- The system is unconditional for irreducible insertions over a C₂-cofinite VOA. -/
theorem exists_trace_eisenstein_system (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Y : IntertwiningOperator A N N) {h : ℂ} (hcw : HasConformalWeight N h) :
    ∃ (U : Finset M₁) (B : U → U → ↥GSeries),
      (∀ k : U, qD (h - W.centralCharge / 24)
        (blockRestrict (trace_mem_QSeriesAt Y hcw) k.val) =
        ∑ l : U, B k l • blockRestrict (trace_mem_QSeriesAt Y hcw) l.val) ∧
      (∀ w, ∃ c : U → ↥GSeries, blockRestrict (trace_mem_QSeriesAt Y hcw) w =
        ∑ l : U, c l • blockRestrict (trace_mem_QSeriesAt Y hcw) l.val) :=
  exists_eisenstein_system (trace Y) (trace_mem_QSeriesAt Y hcw)
    (isInsertionFormalBlock_trace Y) (moduleC2_of_irreducible hC2 hA)

set_option synthInstance.maxHeartbeats 200000 in
-- The nested submodule carries several scalar towers; synthesis needs a larger budget.
/-- A positive-order monic relation among the `L[-2]` descendants. This is a
relation on descendants, not a scalar differential equation for an arbitrary vector. -/
theorem exists_monic_sqL_relation {S : M₁ →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsInsertionFormalBlock A S)
    (hAC2 : ModuleC2Cofinite A.toWeakModule) (v : M₁) :
    ∃ (s : ℕ) (G : ℕ → PowerSeries ℂ), 1 ≤ s ∧ (∀ i, G i ∈ GSeries) ∧
      S ((⇑(sqL A (-2)))^[s] v)
        = ∑ i ∈ Finset.range s, psSMul (G i) (S ((⇑(sqL A (-2)))^[i] v)) := by
  classical
  set 𝔐 : Submodule (↥GSeries) ↥(QSeriesAt hbase) :=
    Submodule.span (↥GSeries)
      (Set.range (blockRestrict hsupp : M₁ →ₗ[ℂ] ↥(QSeriesAt hbase))) with h𝔐
  haveI : IsNoetherianRing (↥GSeries) := isNoetherianRing_GSeries
  haveI hnoe : IsNoetherian (↥GSeries) ↥𝔐 :=
    isNoetherian_of_fg_of_noetherian _ (fg_insertionBlockSpan_G S hsupp hS hAC2)
  set x : ℕ → ↥𝔐 := fun i =>
    ⟨blockRestrict hsupp ((⇑(sqL A (-2)))^[i] v), Submodule.subset_span ⟨_, rfl⟩⟩ with hxdef
  have hmono : Monotone (fun r : ℕ =>
      Submodule.span (↥GSeries) (Set.range (fun i : Fin (r + 1) => x i))) := by
    intro r r' hrr
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i.1, by omega⟩, rfl⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr hnoe ⟨_, hmono⟩
  have hmem : x (n + 1) ∈ Submodule.span (↥GSeries)
      (Set.range (fun i : Fin (n + 1) => x i)) := by
    have := hn (n + 1) (by omega)
    change Submodule.span (↥GSeries) (Set.range (fun i : Fin (n + 1) => x i))
      = Submodule.span (↥GSeries) (Set.range (fun i : Fin (n + 1 + 1) => x i)) at this
    rw [this]
    exact Submodule.subset_span ⟨⟨n + 1, by omega⟩, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (↥GSeries)).mp hmem
  refine ⟨n + 1, fun i => if h : i < n + 1 then ((c ⟨i, h⟩ : ↥GSeries) : PowerSeries ℂ) else 0,
    by omega, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases h : i < n + 1
    · rw [dif_pos h]; exact (c ⟨i, h⟩).2
    · rw [dif_neg h]; exact zero_mem _
  · set φ : ↥𝔐 →+ FormalQSeries :=
      ((QSeriesAt hbase).subtype.toAddMonoidHom).comp (𝔐.subtype.toAddMonoidHom) with hφ
    have hφsmul : ∀ (g : ↥GSeries) (i : ℕ),
        φ ((g • x i : ↥𝔐)) = psSMul ((g : PowerSeries ℂ)) (S ((⇑(sqL A (-2)))^[i] v)) :=
      fun _ _ => rfl
    have hφx : ∀ i : ℕ, φ (x i) = S ((⇑(sqL A (-2)))^[i] v) := fun _ => rfl
    have hL := congrArg φ hc
    rw [map_sum, hφx] at hL
    rw [← hL]
    dsimp only
    have hterm : ∀ i : Fin (n + 1),
        φ ((c i • x (i : ℕ) : ↥𝔐))
          = psSMul (if h : (i : ℕ) < n + 1 then ((c ⟨(i : ℕ), h⟩ : ↥GSeries) : PowerSeries ℂ)
              else 0) (S ((⇑(sqL A (-2)))^[(i : ℕ)] v)) := by
      intro i
      rw [hφsmul (c i) (i : ℕ), dif_pos i.2]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i)]
    exact Fin.sum_univ_eq_sum_range
      (fun i : ℕ => psSMul (if h : i < n + 1 then ((c ⟨i, h⟩ : ↥GSeries) : PowerSeries ℂ) else 0)
        (S ((⇑(sqL A (-2)))^[i] v))) (n + 1)

end VOA.Huang.GenusOne
