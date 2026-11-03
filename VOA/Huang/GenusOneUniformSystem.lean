import VOA.Huang.GenusOneEisensteinEvaluation
import VOA.Huang.GenusOneSpanningReduction

/-! # One Eisenstein system for every analytic insertion block

The C₂ induction is applied to simultaneous evaluations of all blocks. Thus
both the generating vectors and the matrix coefficients are chosen before
the analytic block. No assumed formal expansion enters this construction.
The coefficients lie in the formal Eisenstein ring, so their q-series are
subexponential and regular at q = 0. Frobenius extraction is a separate step.
Source: Miyamoto, math/0010180, Lemmas 4.4–4.5 and Theorem 4.9.
-/
namespace VOA.Huang.GenusOne.Uniform
open VOA Module VOA.Huang.FusionC2 VOA.Huang.LWBottomRecovery VOA.Huang.BottomRecovery
open scoped BigOperators
universe u
variable {V M₁ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] {W : VertexOperatorAlgebra V} {A : OrdVModule W M₁}

section Reduction
variable {Q : Type*} [AddCommGroup Q] [Module ℂ Q] [Module ↥GSeries Q]
  [IsScalarTower ℂ ↥GSeries Q]

/-- The algebraic part of the minus-two recursion needed by weight induction. -/
def NegTwoSpan (A : OrdVModule W M₁) (S : M₁ →ₗ[ℂ] Q) : Prop :=
  ∀ (p : ℕ), 1 ≤ p → ∀ a ∈ W.grading (p : ℤ), ∀ w,
    S (sqAct A a p (-2) w) ∈ Submodule.span ↥GSeries
      (Set.range fun m : ℕ => S (sqAct A a p (2 * (m + 1) - 2 : ℤ) w))

/-- C₂ reduction step, with the Eisenstein tail absorbed into the coefficient ring. -/
theorem negTwo_mem_lower (S : M₁ →ₗ[ℂ] Q)
    (hneg : NegTwoSpan A S) (B : AdmissibleModule W M₁)
    (hBA : B.toWeakModule = A.toWeakModule)
    (T : Submodule (↥GSeries) Q)
    {p j : ℤ} {a : V} {w : M₁} (ha : a ∈ W.grading p) (hw : w ∈ B.lev j)
    (hT : ∀ d : ℤ, d < j + p + 1 → ∀ x ∈ B.lev d,
      S x ∈ T) :
    S (mode (A.YM a) (-2) w) ∈ T := by
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
      (Submodule.span_le.mpr (by
        rintro _ ⟨m, rfl⟩
        exact sqAct_mem_lower B hBA ha hw (by omega) P hP))
          (hneg p.toNat (by omega) a ha' w)
    have hdef : S (sqActDefect A a p.toNat w) ∈ T := sqActDefect_mem_lower B hBA ha hw P hP
    have heq := congrArg S (sqAct_neg_two_eq A a p.toNat w)
    rw [map_add] at heq
    have hm := T.sub_mem hsq hdef
    rwa [heq, add_sub_cancel_right] at hm

/-- Homogeneous C₂ representatives generate the entire trace span. -/
theorem mem_span_C2 (S : M₁ →ₗ[ℂ] Q)
    (hneg : NegTwoSpan A S) (B : AdmissibleModule W M₁)
    (hBA : B.toWeakModule = A.toWeakModule) {U : Set M₁}
    (hU : ∀ s ∈ U, ∃ k, s ∈ B.lev k)
    (htop : (⊤ : Submodule ℂ M₁) = Submodule.span ℂ U ⊔ C2M B.toWeakModule) (w : M₁) :
    S w ∈
      Submodule.span (↥GSeries) (S '' U) := by
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
      exact negTwo_mem_lower S hneg B hBA T ha hm (fun d hd => hlow d (by omega))
  exact induction_lev B (motive := fun w => w ∈ P) w P.zero_mem
    (fun _ _ hx hy => P.add_mem hx hy) (fun k x hx => hlev k hx)


end Reduction

/-- Values simultaneously indexed by all analytic blocks and all points of ℍ. -/
def Values (A : OrdVModule W M₁) := insertionAnalyticBlocks A → UpperHalfPlane → ℂ

noncomputable instance : AddCommGroup (Values A) :=
  inferInstanceAs (AddCommGroup (insertionAnalyticBlocks A → UpperHalfPlane → ℂ))
noncomputable instance : Module ℂ (Values A) :=
  inferInstanceAs (Module ℂ (insertionAnalyticBlocks A → UpperHalfPlane → ℂ))
noncomputable instance : Module (UpperHalfPlane → ℂ) (Values A) :=
  inferInstanceAs (Module (UpperHalfPlane → ℂ)
    (insertionAnalyticBlocks A → UpperHalfPlane → ℂ))
noncomputable instance : Module ↥GSeries (Values A) :=
  Module.compHom (Values A) eisensteinEvalHom.toRingHom

instance : IsScalarTower ℂ ↥GSeries (Values A) where
  smul_assoc c f x := by
    funext F τ
    change eisensteinEval (c • f) τ * x F τ = c * (eisensteinEval f τ * x F τ)
    rw [eisensteinEval_smul, mul_assoc]

/-- Insertion evaluation into the simultaneous module. -/
noncomputable def values : M₁ →ₗ[ℂ] Values A where
  toFun w F τ := F.val w τ
  map_add' x y := by funext F τ; exact F.property.addv x y τ
  map_smul' c x := by funext F τ; exact F.property.smulv c x τ

@[simp] theorem values_apply (w : M₁) (F : insertionAnalyticBlocks A) (τ : UpperHalfPlane) :
    values (A := A) w F τ = F.val w τ := rfl

@[simp] theorem values_smul (g : ↥GSeries) (x : Values A)
    (F : insertionAnalyticBlocks A) (τ : UpperHalfPlane) :
    (g • x) F τ = eisensteinEval g τ * x F τ := rfl

/-- Evaluation is linear despite restriction of the Eisenstein scalars. -/
noncomputable def eval (F : insertionAnalyticBlocks A) (τ : UpperHalfPlane) :
    Values A →ₗ[ℂ] ℂ where
  toFun x := x F τ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem values_sum {J : Type*} (s : Finset J) (x : J → Values A)
    (F : insertionAnalyticBlocks A) (τ : UpperHalfPlane) :
    (∑ j ∈ s, x j) F τ = ∑ j ∈ s, x j F τ := map_sum (eval F τ) _ _

/-- The minus-two relation holds in the simultaneous module, before a block is chosen. -/
theorem values_negTwoSpan : NegTwoSpan A (values (A := A)) := by
  classical
  intro p hp a ha w
  obtain ⟨K, hK⟩ := sqAct_tail_eventually_zero A a p w
  let c (m : ℕ) : ↥GSeries := ((2 * (m + 1) - 1 : ℕ) : ℂ) •
    (⟨PowerSeries.mk (zhuG (m + 1)), mk_zhuG_mem_GSeries (by omega)⟩ : ↥GSeries)
  have he : values (A := A) (sqAct A a p (-2) w) =
      -(∑ m ∈ Finset.range K, c m • values (sqAct A a p (2 * (m + 1) - 2 : ℤ) w)) := by
    funext F τ
    have h := F.property.negTwo p hp a ha w τ τ.im_pos
    rw [insertionNegTwoSum F.property.zerov hK τ, add_eq_zero_iff_eq_neg] at h
    change F.val (sqAct A a p (-2) w) τ = -_
    rw [h]
    congr 1
    rw [values_sum]
    change _ = ∑ m ∈ Finset.range K,
      eisensteinEval (c m) τ * F.val (sqAct A a p (2 * (m + 1) - 2 : ℤ) w) τ
    apply Finset.sum_congr rfl
    intro m _
    change _ = eisensteinEval ((((2 * (m + 1) - 1 : ℕ) : ℂ) •
      (⟨PowerSeries.mk (zhuG (m + 1)), mk_zhuG_mem_GSeries (by omega)⟩ : ↥GSeries))) τ * _
    rw [eisensteinEval_smul, eisensteinEval_zhuG (m + 1) (by omega), mul_assoc]
  rw [he]
  exact Submodule.neg_mem _ (Submodule.sum_mem _ fun m _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩))

/-- A finite family generates every simultaneous insertion value over the
formal Eisenstein ring. The coefficients are uniform in the analytic block. -/
theorem exists_uniform_generators (hAC2 : ModuleC2Cofinite A.toWeakModule) :
    ∃ U : Finset M₁, ∀ w, ∃ c : U → ↥GSeries,
      values (A := A) w = ∑ l : U, c l • values l.val := by
  classical
  obtain ⟨U, hU, htop⟩ := exists_finset_homog (N := A.toAdmissible) hAC2
  refine ⟨U, fun w => ?_⟩
  have h := mem_span_C2 (values (A := A)) values_negTwoSpan A.toAdmissible rfl hU htop w
  have hr : values (A := A) '' (U : Set M₁) = Set.range (fun l : U => values l.val) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩
    · rintro ⟨w, rfl⟩; exact ⟨w.val, w.property, rfl⟩
  rw [hr] at h
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ↥GSeries).mp h
  exact ⟨c, hc.symm⟩

/-- A single finite Euler system and generating formula for *all* analytic
blocks. The same U, B and c work on all of ℍ, including arbitrarily near the cusp. -/
theorem exists_uniform_analytic_system (hAC2 : ModuleC2Cofinite A.toWeakModule) :
    ∃ (U : Finset M₁) (B : U → U → ↥GSeries) (c : M₁ → U → ↥GSeries),
      ∀ (F : M₁ → ℂ → ℂ), IsInsertionAnalyticBlock A F →
        (∀ (k : U) (τ : UpperHalfPlane),
          (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F k.val) τ =
            ∑ l : U, eisensteinEval (B k l) τ * F l.val τ) ∧
        (∀ (w : M₁) (τ : UpperHalfPlane),
          F w τ = ∑ l : U, eisensteinEval (c w l) τ * F l.val τ) := by
  classical
  obtain ⟨U, hU⟩ := exists_uniform_generators hAC2
  choose c hc using hU
  let T := Submodule.span ↥GSeries (Set.range (fun l : U => values (A := A) l.val))
  have hmem (w : M₁) : values (A := A) w ∈ T := by
    rw [hc]
    exact T.sum_mem fun l _ => T.smul_mem _ (Submodule.subset_span ⟨l, rfl⟩)
  have hsys (k : U) : ∃ b : U → ↥GSeries, ∀ (F : insertionAnalyticBlocks A)
      (τ : UpperHalfPlane),
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F.val k.val) τ =
        ∑ l : U, eisensteinEval (b l) τ * F.val l.val τ := by
    obtain ⟨K, hK⟩ := sqL_tail_eventually_zero A k.val
    let g (m : ℕ) : ↥GSeries :=
      ⟨PowerSeries.mk (zhuG (m + 1)), mk_zhuG_mem_GSeries (by omega)⟩
    let d : Values A := values (sqL A (-2) k.val) -
      ∑ m ∈ Finset.range K, g m • values (sqL A (2 * (m + 1) - 2 : ℤ) k.val)
    have hd : d ∈ T := T.sub_mem (hmem _) (T.sum_mem fun m _ => T.smul_mem _ (hmem _))
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ↥GSeries).mp hd
    refine ⟨b, fun F τ => ?_⟩
    have hv := congrArg (eval F τ) hb
    simp only [d, map_sub, map_sum] at hv
    have he := F.property.omega k.val τ τ.im_pos
    rw [insertionOmegaSum F.property.zerov hK τ] at he
    change (∑ l : U, eisensteinEval (b l) τ * F.val l.val τ) =
      F.val (sqL A (-2) k.val) τ -
        ∑ m ∈ Finset.range K, eisensteinEval (g m) τ *
          F.val (sqL A (2 * (m + 1) - 2 : ℤ) k.val) τ at hv
    have eg (m : ℕ) : eisensteinEval (g m) τ = zhuGC (m + 1) τ :=
      eisensteinEval_zhuG (m + 1) (by omega) τ
    simp only [eg] at hv
    rw [hv, he, add_sub_cancel_right]
  choose B hB using hsys
  refine ⟨U, B, c, fun F hF => ⟨fun k τ => hB k ⟨F, hF⟩ τ, fun w τ => ?_⟩⟩
  have hv := congrArg (eval ⟨F, hF⟩ τ) (hc w)
  simpa only [map_sum] using hv

end VOA.Huang.GenusOne.Uniform
