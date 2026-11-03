import VOA.Huang.GenusOneLinearSlash
import VOA.Modularity.BlockFiniteDim

/-!
# Determination of insertion blocks by finitely many values at one point

This is the module version of Zhu's analytic determinacy argument. It proves
uniqueness directly from the omega recursion and holomorphy; C₂ reduction then
reduces the data at the point to a finite homogeneous set. It does not assert
Frobenius existence or realization of the initial data by intertwiners.
Source: Zhu, JAMS 9 (1996), §5.3; Miyamoto, math/0010180, §4.
-/
namespace VOA.Huang.GenusOne
open VOA Complex
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M} {F : M → ℂ → ℂ}

theorem insertion_omega_finsum_eq_sum (hF : IsInsertionAnalyticBlock A F)
    {v : M} {K : ℕ}
    (hK : ∀ m : ℕ, K ≤ m → sqL A (2 * (m + 1) - 2 : ℤ) v = 0) (z : ℂ) :
    (∑ᶠ m : ℕ, zhuGC (m + 1) z * F (sqL A (2 * (m + 1) - 2 : ℤ) v) z) =
      ∑ m ∈ Finset.range K, zhuGC (m + 1) z * F (sqL A (2 * (m + 1) - 2 : ℤ) v) z := by
  apply finsum_eq_finsetSum_of_support_subset
  intro m hm
  simp only [Function.mem_support, Finset.mem_coe, Finset.mem_range] at hm ⊢
  by_contra hn
  exact hm (by rw [hK m (by omega), hF.zerov, mul_zero])

theorem IsInsertionAnalyticBlock.analyticAt (hF : IsInsertionAnalyticBlock A F)
    {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0)
    (x : M) : AnalyticAt ℂ (F x) z₀ :=
  ((hF.holo x).analyticOnNhd (isOpen_imGT 0)) z₀ hz₀

/-- **The `ω`-law solved for the derivative**: `F(v)′` is a finite combination of *values* of
`F`, with holomorphic Eisenstein coefficients. -/
theorem IsInsertionAnalyticBlock.deriv_eq_on (hF : IsInsertionAnalyticBlock A F) (v : M) {K : ℕ}
    (hK : ∀ m : ℕ, K ≤ m → sqL A (2 * (m + 1) - 2 : ℤ) v = 0) {z : ℂ} (hz : z ∈ imGT 0) :
    _root_.deriv (F v) z
      = 2 * (Real.pi : ℂ) * Complex.I * (F (sqL A (-2) v) z
          - ∑ m ∈ Finset.range K, zhuGC (m + 1) z * F (sqL A (2 * (m + 1) - 2 : ℤ) v) z) := by
  have hlaw := hF.omega v z hz
  rw [insertion_omega_finsum_eq_sum hF hK z] at hlaw
  have hkey : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F v) z
      = F (sqL A (-2) v) z
        - ∑ m ∈ Finset.range K, zhuGC (m + 1) z * F (sqL A (2 * (m + 1) - 2 : ℤ) v) z := by
    rw [hlaw]; ring
  calc _root_.deriv (F v) z
      = 2 * (Real.pi : ℂ) * Complex.I
          * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F v) z) := by
        rw [← mul_assoc, mul_inv_cancel₀ two_pi_I_ne_zero, one_mul]
    _ = _ := by rw [hkey]

/-- **All derivatives vanish.**  If a block vanishes at `z₀` on *every* vector, then every
`iteratedDeriv` of every `g·F(v)` (with `g` analytic at `z₀`) vanishes at `z₀` — because
differentiating only ever produces new combinations of the same shape. -/
theorem insertion_iteratedDeriv_coeff_eq_zero (hF : IsInsertionAnalyticBlock A F)
    {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0)
    (hall : ∀ x : M, F x z₀ = 0) (k : ℕ) :
    ∀ (g : ℂ → ℂ), AnalyticAt ℂ g z₀ → ∀ v : M,
      iteratedDeriv k (fun z => g z * F v z) z₀ = 0 := by
  induction k with
  | zero =>
      intro g _ v
      rw [iteratedDeriv_zero]
      show g z₀ * F v z₀ = 0
      rw [hall v, mul_zero]
  | succ k ih =>
      intro g hg v
      obtain ⟨K, hK⟩ := sqL_tail_eventually_zero A v
      set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hc
      set a₁ : ℂ → ℂ := fun z => _root_.deriv g z * F v z with ha₁
      set a₂ : ℂ → ℂ := fun z => (c * g z) * F (sqL A (-2) v) z with ha₂
      set b : ℕ → ℂ → ℂ := fun m z =>
        (-c * g z * zhuGC (m + 1) z) * F (sqL A (2 * (m + 1) - 2 : ℤ) v) z with hb
      set H : ℂ → ℂ := fun z => a₁ z + a₂ z with hH
      set B : ℂ → ℂ := fun z => ∑ m ∈ Finset.range K, b m z with hB
      have hEq : _root_.deriv (fun z => g z * F v z) =ᶠ[nhds z₀] fun z => H z + B z := by
        filter_upwards [hg.eventually_analyticAt, (isOpen_imGT 0).mem_nhds hz₀] with w hgw hw
        rw [deriv_fun_mul hgw.differentiableAt (hF.analyticAt hw v).differentiableAt,
          hF.deriv_eq_on v hK hw, hH, hB, ha₁, ha₂, hb]
        simp only
        rw [show g w * (c * (F (sqL A (-2) v) w
              - ∑ m ∈ Finset.range K, zhuGC (m + 1) w * F (sqL A (2 * (m + 1) - 2 : ℤ) v) w))
            = (c * g w) * F (sqL A (-2) v) w
              + (-c * g w) * ∑ m ∈ Finset.range K,
                  zhuGC (m + 1) w * F (sqL A (2 * (m + 1) - 2 : ℤ) v) w from by ring,
          Finset.mul_sum, ← add_assoc]
        congr 1
        exact Finset.sum_congr rfl (fun m _ => by ring)
      have ha₁an : AnalyticAt ℂ a₁ z₀ := hg.deriv.mul (hF.analyticAt hz₀ v)
      have ha₂an : AnalyticAt ℂ a₂ z₀ := (analyticAt_const.mul hg).mul (hF.analyticAt hz₀ _)
      have hban : ∀ m ∈ Finset.range K, AnalyticAt ℂ (b m) z₀ := fun m _ =>
        ((analyticAt_const.mul hg).mul (analyticAt_zhuGC (m + 1) hz₀)).mul (hF.analyticAt hz₀ _)
      have hAan : AnalyticAt ℂ H z₀ := ha₁an.add ha₂an
      have hBan : AnalyticAt ℂ B z₀ := Finset.analyticAt_fun_sum _ hban
      rw [iteratedDeriv_succ', Filter.EventuallyEq.iteratedDeriv_eq k hEq,
        iteratedDeriv_add_of_analyticAt k hAan hBan,
        iteratedDeriv_add_of_analyticAt k ha₁an ha₂an,
        iteratedDeriv_sum_of_analyticAt (Finset.range K) b k hban,
        ih (_root_.deriv g) hg.deriv v,
        ih (fun z => c * g z) (analyticAt_const.mul hg) (sqL A (-2) v)]
      have hz : ∀ m ∈ Finset.range K, iteratedDeriv k (b m) z₀ = 0 := fun m _ =>
        ih (fun z => -c * g z * zhuGC (m + 1) z)
          ((analyticAt_const.mul hg).mul (analyticAt_zhuGC (m + 1) hz₀)) _
      rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
      ring

/-- **A block vanishing at one point of `ℍ` on every vector vanishes identically.** -/
theorem IsInsertionAnalyticBlock.eq_zero_of_eq_zero_at (hF : IsInsertionAnalyticBlock A F) {z₀ : ℂ}
    (hz₀ : z₀ ∈ imGT 0) (hall : ∀ x : M, F x z₀ = 0) :
    ∀ (v : M), ∀ z ∈ imGT 0, F v z = 0 := by
  intro v
  have hloc : ∀ᶠ z in nhds z₀, F v z = 0 := by
    refine eventuallyEq_zero_of_iteratedDeriv_eq_zero (hF.analyticAt hz₀ v) (fun k => ?_)
    have h := insertion_iteratedDeriv_coeff_eq_zero hF hz₀ hall k (fun _ => 1) analyticAt_const v
    simpa using h
  intro z hz
  have := eqOn_imGT_of_eventuallyEq (hF.holo v) (differentiableOn_const 0) hz₀
    (by filter_upwards [hloc] with w hw using hw) hz
  exact this



open VOA.Huang.FusionC2 VOA.Huang.LWBottomRecovery VOA.Huang.BottomRecovery

/-- The collected relation forces a minus-two product to vanish when lower levels do. -/
theorem IsInsertionAnalyticBlock.negTwo_eq_zero_of_lower
    (hF : IsInsertionAnalyticBlock A F) {z : ℂ} (hz : z ∈ imGT 0)
    (B : AdmissibleModule W M) (hBA : B.toWeakModule = A.toWeakModule)
    {p j : ℤ} {a : V} {w : M} (ha : a ∈ W.grading p) (hw : w ∈ B.lev j)
    (hlo : ∀ d : ℤ, d < j + p + 1 → ∀ x ∈ B.lev d, F x z = 0) :
    F (mode (A.YM a) (-2) w) z = 0 := by
  let E : M →ₗ[ℂ] ℂ := (LinearMap.proj z).comp hF.linear
  let P : Submodule ℂ M := LinearMap.ker E
  have hP : ∀ d : ℤ, d < j + p + 1 → B.lev d ≤ P := hlo
  rcases lt_trichotomy p 0 with hp | rfl | hp
  · rw [W.positivity p hp, Submodule.mem_bot] at ha
    simp only [ha, map_zero, mode_zero, LinearMap.zero_apply, hF.zerov]
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (vacuumGradeZero_holds W ha)
    have hv : mode (A.YM W.vacuum) (-2) w = 0 :=
      (A.toWeakModule.act_vacuum (-2) w).trans (if_neg (by norm_num))
    simp only [map_smul, mode_smul, LinearMap.smul_apply, hv, smul_zero, hF.zerov]
  · have ha' : a ∈ W.grading (p.toNat : ℤ) := by rwa [Int.toNat_of_nonneg hp.le]
    have htail : ∀ m : ℕ, F (sqAct A a p.toNat (2 * (m + 1) - 2 : ℤ) w) z = 0 := by
      intro m
      exact sqAct_mem_lower B hBA ha hw (by omega) P hP
    have hrec := hF.negTwo p.toNat (by omega) a ha' w z hz
    simp only [htail, mul_zero, finsum_zero, add_zero] at hrec
    have hdef : F (sqActDefect A a p.toNat w) z = 0 :=
      sqActDefect_mem_lower B hBA ha hw P hP
    rw [sqAct_neg_two_eq, hF.addv, hdef, add_zero] at hrec
    exact hrec

/-- C₂ representatives determine every insertion value at a fixed point. -/
theorem IsInsertionAnalyticBlock.eq_zero_at_of_vanish
    (hF : IsInsertionAnalyticBlock A F) {z : ℂ} (hz : z ∈ imGT 0)
    (B : AdmissibleModule W M) (hBA : B.toWeakModule = A.toWeakModule) {U : Set M}
    (hU : ∀ s ∈ U, ∃ k, s ∈ B.lev k)
    (htop : (⊤ : Submodule ℂ M) = Submodule.span ℂ U ⊔ C2M B.toWeakModule)
    (hvan : ∀ s ∈ U, F s z = 0) (w : M) : F w z = 0 := by
  let E : M →ₗ[ℂ] ℂ := (LinearMap.proj z).comp hF.linear
  let P : Submodule ℂ M := LinearMap.ker E
  have hUP : Submodule.span ℂ U ≤ P := Submodule.span_le.mpr hvan
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
      change F (mode (B.toWeakModule.YM a) (-2) m) z = 0
      rw [hBA]
      exact hF.negTwo_eq_zero_of_lower hz B hBA ha hm (fun d hd => hlow d (by omega))
  exact induction_lev B (motive := fun w => w ∈ P) w P.zero_mem
    (fun _ _ hx hy => P.add_mem hx hy) (fun k x hx => hlev k hx)

/-- A finite set of insertion vectors at a single point determines the full block. -/
theorem exists_finite_insertion_determining_set
    (hAC2 : ModuleC2Cofinite A.toWeakModule) :
    ∃ U : Finset M, ∀ (F : M → ℂ → ℂ), IsInsertionAnalyticBlock A F →
      ∀ z₀ ∈ imGT 0, (∀ w ∈ U, F w z₀ = 0) →
        ∀ w z, z ∈ imGT 0 → F w z = 0 := by
  obtain ⟨U, hU, htop⟩ := exists_finset_homog (N := A.toAdmissible) hAC2
  refine ⟨U, fun F hF z₀ hz₀ hvan => ?_⟩
  exact hF.eq_zero_of_eq_zero_at hz₀
    (hF.eq_zero_at_of_vanish hz₀ A.toAdmissible rfl hU htop hvan)

end VOA.Huang.GenusOne
