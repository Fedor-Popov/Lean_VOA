import VOA.Huang.GenusOneCloseDefect
import VOA.Huang.GenusOneCloseExpansion

/-!
# Coefficient comparison: analytic relations give formal relations

If an insertion function is the `q`-evaluation of a convergent formal family
supported at `b`, every analytic block relation (with a possible omega defect)
holds formally, by uniqueness of `q`-expansions on the upper half-plane. This
is the coefficient comparison in Miyamoto, math/0010180, §4 (before Lemma 4.11).
The family expansion theorem packages `exists_expansion` linearly in the
insertion vector.
-/
namespace VOA.Huang.GenusOne.Close
open VOA Complex
open scoped BigOperators Real
universe u

/-! ## Convergent series supported at a base point -/

/-- Supported at `b` and convergent on the whole upper half-plane. -/
def Good (b : ℂ) (χ : FormalQSeries) : Prop :=
  χ ∈ QSeriesAt b ∧ ∀ z ∈ imGT 0, Summable (fun n : ℕ => qTerm χ b n z)

variable {b : ℂ}

theorem Good.subexp {χ : FormalQSeries} (h : Good b χ) :
    Subexponential (fun n : ℕ => ‖χ (b + (n : ℂ))‖) :=
  subexp_of_summable χ b h.2

theorem good_zero : Good b 0 :=
  ⟨(QSeriesAt b).zero_mem, fun z _ => by
    simp [qTerm]⟩

theorem qTerm_add (χ ψ : FormalQSeries) (n : ℕ) (z : ℂ) :
    qTerm (χ + ψ) b n z = qTerm χ b n z + qTerm ψ b n z := by
  simp only [qTerm, Pi.add_apply]; ring

theorem qTerm_smul (c : ℂ) (χ : FormalQSeries) (n : ℕ) (z : ℂ) :
    qTerm (c • χ) b n z = c * qTerm χ b n z := by
  simp only [qTerm, Pi.smul_apply, smul_eq_mul]; ring

theorem Good.add {χ ψ : FormalQSeries} (hχ : Good b χ) (hψ : Good b ψ) : Good b (χ + ψ) :=
  ⟨(QSeriesAt b).add_mem hχ.1 hψ.1, fun z hz => ((hχ.2 z hz).add (hψ.2 z hz)).congr
    fun n => (qTerm_add χ ψ n z).symm⟩

theorem Good.smul {χ : FormalQSeries} (hχ : Good b χ) (c : ℂ) : Good b (c • χ) :=
  ⟨(QSeriesAt b).smul_mem c hχ.1, fun z hz => ((hχ.2 z hz).mul_left c).congr
    fun n => (qTerm_smul c χ n z).symm⟩

theorem Good.sub {χ ψ : FormalQSeries} (hχ : Good b χ) (hψ : Good b ψ) : Good b (χ - ψ) := by
  simpa [sub_eq_add_neg] using hχ.add (hψ.smul (-1))

theorem Good.finsetSum {κ : Type*} (s : Finset κ) (g : κ → FormalQSeries)
    (hg : ∀ i ∈ s, Good b (g i)) : Good b (∑ i ∈ s, g i) :=
  ⟨Submodule.sum_mem _ fun i hi => (hg i hi).1, fun z _ =>
    summable_qTerm_finset s g b z fun i hi => (hg i hi).2 z (by assumption)⟩

theorem Good.finsum {κ : Type*} (g : κ → FormalQSeries) (hfin : (Function.support g).Finite)
    (hg : ∀ i, Good b (g i)) : Good b (∑ᶠ i, g i) := by
  rw [finsum_eq_finsetSum_of_support_subset g (s := hfin.toFinset) (by simp)]
  exact Good.finsetSum _ g fun i _ => hg i

theorem Good.qConv {χ : FormalQSeries} (hχ : Good b χ) (j : ℕ) :
    Good b (qConv (zhuG j) χ) :=
  ⟨qConv_mem_QSeriesAt _ hχ.1, fun _ hz => summable_qTerm_qConv (zhuG j) χ b
    (QSeriesAt.support_neg hχ.1) (summable_norm_zhuG_qexp j hz)
    (summable_norm_qTerm χ b hχ.subexp hz)⟩

theorem qEvalC_qConv_zhuG' {χ : FormalQSeries} (hχ : Good b χ) (j : ℕ) {z : ℂ}
    (hz : z ∈ imGT 0) : qEvalC (qConv (zhuG j) χ) b z = zhuGC j z * qEvalC χ b z :=
  qEvalC_qConv (zhuG j) χ b (QSeriesAt.support_neg hχ.1) (summable_norm_zhuG_qexp j hz)
    (summable_norm_qTerm χ b hχ.subexp hz)

theorem Good.qDeriv {χ : FormalQSeries} (hχ : Good b χ) : Good b (qDeriv χ) :=
  ⟨fun e he => by
    change e * χ e = 0
    rw [hχ.1 e he, mul_zero], fun _ hz =>
    summable_qTerm_qDeriv χ b hχ.subexp hz⟩

theorem qEvalC_sub' {χ ψ : FormalQSeries} (hχ : Good b χ) (hψ : Good b ψ) {z : ℂ}
    (hz : z ∈ imGT 0) : qEvalC (χ - ψ) b z = qEvalC χ b z - qEvalC ψ b z := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ ψ, qEvalC_add _ _ _ (hχ.2 z hz)
    ((hψ.smul (-1)).2 z hz), qEvalC_smul]
  ring

/-- Equal evaluations on the upper half-plane force equal series. -/
theorem eq_of_good {χ ψ : FormalQSeries} (hχ : Good b χ) (hψ : Good b ψ)
    (he : ∀ z ∈ imGT 0, qEvalC χ b z = qEvalC ψ b z) : χ = ψ := by
  have h := eq_zero_of_qEvalC (hχ.sub hψ).1 (hχ.sub hψ).2
    (fun z hz => by rw [qEvalC_sub' hχ hψ hz, he z hz, sub_self])
  exact sub_eq_zero.mp h

/-! ## Analytic defect relations -/

variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M}

/-- The analytic block relations with an inhomogeneous omega term `e`, imposed
only on the upper half-plane. -/
structure IsAnalyticDefect (A : OrdVModule W M) (H e : M → ℂ → ℂ) : Prop where
  vanish : ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ v : M, ∀ z ∈ imGT 0,
    H (sqAct A a ka 0 v) z = 0
  negTwo : ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ (v : M), ∀ z ∈ imGT 0,
    H (sqAct A a ka (-2) v) z
      + ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 1) z * H (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) z) = 0
  omega : ∀ (v : M), ∀ z ∈ imGT 0,
    H (sqL A (-2) v) z
      = (2 * (π : ℂ) * I)⁻¹ * _root_.deriv (H v) z
        + ∑ᶠ m : ℕ, zhuGC (m + 1) z * H (sqL A (2 * (m + 1) - 2 : ℤ) v) z + e v z

theorem isAnalyticDefect_of_block {F : M → ℂ → ℂ} (hF : IsInsertionAnalyticBlock A F) :
    IsAnalyticDefect A F (fun _ _ => 0) where
  vanish ka hka a ha v z _ := by rw [hF.vanish ka hka a ha v]; rfl
  negTwo := hF.negTwo
  omega v z hz := by rw [add_zero]; exact hF.omega v z hz

/-- **Coefficient comparison.** -/
theorem isDefectBlock_of_analytic {H e : M → ℂ → ℂ} (hH : IsAnalyticDefect A H e)
    (S E : M →ₗ[ℂ] FormalQSeries) (hS : ∀ w, Good b (S w)) (hE : ∀ w, Good b (E w))
    (hHS : ∀ w, ∀ z ∈ imGT 0, H w z = qEvalC (S w) b z)
    (heE : ∀ w, ∀ z ∈ imGT 0, e w z = qEvalC (E w) b z) :
    IsDefectBlock A S E where
  vanish k hk a ha w := by
    apply eq_of_good (hS _) good_zero
    intro z hz
    rw [← hHS _ z hz, hH.vanish k hk a ha w z hz, qEvalC_zero]
  negTwo k hk a ha w := by
    obtain ⟨K, hK⟩ := sqAct_tail_eventually_zero A a k w
    let c : ℕ → FormalQSeries → FormalQSeries := fun m χ =>
      ((2 * (m + 1) - 1 : ℕ) : ℂ) • qConv (zhuG (m + 1)) χ
    have hfin := tail_finite S _ ⟨K, hK⟩ c (fun m => by simp [c])
    have hgood : ∀ m, Good b (c m (S (sqAct A a k (2 * (m + 1) - 2 : ℤ) w))) :=
      fun m => ((hS _).qConv _).smul _
    apply eq_of_good ((hS _).add (Good.finsum _ hfin hgood)) good_zero
    intro z hz
    rw [qEvalC_add _ _ _ ((hS _).2 z hz) ((Good.finsum _ hfin hgood).2 z hz),
      qEvalC_finsum _ _ hfin (fun m => (hgood m).2 z hz), qEvalC_zero, ← hHS _ z hz,
      ← hH.negTwo k hk a ha w z hz]
    congr 1
    refine finsum_congr fun m => ?_
    simp only [c]
    rw [qEvalC_smul, qEvalC_qConv_zhuG' (hS _) _ hz, ← hHS _ z hz]
  omega w := by
    obtain ⟨K, hK⟩ := sqL_tail_eventually_zero A w
    let c : ℕ → FormalQSeries → FormalQSeries := fun m χ => qConv (zhuG (m + 1)) χ
    have hfin := tail_finite S _ ⟨K, hK⟩ c (fun m => by simp [c])
    have hgood : ∀ m, Good b (c m (S (sqL A (2 * (m + 1) - 2 : ℤ) w))) :=
      fun m => (hS _).qConv _
    have hR := ((hS w).qDeriv.add (Good.finsum _ hfin hgood)).add (hE w)
    apply eq_of_good (hS _) hR
    intro z hz
    have hderiv : _root_.deriv (H w) z = _root_.deriv (qEvalC (S w) b) z := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [(isOpen_imGT 0).mem_nhds hz] with y hy using hHS w y hy
    rw [qEvalC_add _ _ _ (((hS w).qDeriv.add (Good.finsum _ hfin hgood)).2 z hz) ((hE w).2 z hz),
      qEvalC_add _ _ _ ((hS w).qDeriv.2 z hz) ((Good.finsum _ hfin hgood).2 z hz),
      qEvalC_finsum _ _ hfin (fun m => (hgood m).2 z hz), qEvalC_qDeriv _ _ (hS w).subexp hz,
      ← hHS _ z hz, hH.omega w z hz, hderiv, ← heE w z hz]
    congr 2
    refine finsum_congr fun m => ?_
    simp only [c]
    rw [qEvalC_qConv_zhuG' (hS _) _ hz, ← hHS _ z hz]

/-! ## Expansion of a linear family -/

open Classical in
/-- The formal series with prescribed coefficients on `b + ℕ`. -/
noncomputable def seqAt (b : ℂ) (a : ℕ → ℂ) : FormalQSeries := fun e =>
  if h : ∃ n : ℕ, e = b + (n : ℂ) then a (Classical.choose h) else 0

theorem seqAt_apply (a : ℕ → ℂ) (n : ℕ) : seqAt b a (b + (n : ℂ)) = a n := by
  have h : ∃ m : ℕ, b + (n : ℂ) = b + (m : ℂ) := ⟨n, rfl⟩
  rw [seqAt, dif_pos h]
  have hs := Classical.choose_spec h
  have hc : ((n : ℕ) : ℂ) = ((Classical.choose h : ℕ) : ℂ) := by linear_combination hs
  rw [← Nat.cast_injective hc]

theorem seqAt_mem (a : ℕ → ℂ) : seqAt b a ∈ QSeriesAt b := by
  intro e he
  rw [seqAt, dif_neg]
  rintro ⟨n, hn⟩
  exact he n hn

theorem exists_family_expansion (Φ : M → ℂ → ℂ) (r : ℂ) (K : ℝ)
    (hholo : ∀ w, DifferentiableOn ℂ (Φ w) (imGT 0))
    (hadd : ∀ v w, ∀ z ∈ imGT 0, Φ (v + w) z = Φ v z + Φ w z)
    (hsmul : ∀ (c : ℂ) v, ∀ z ∈ imGT 0, Φ (c • v) z = c * Φ v z)
    (hper : ∀ w, ∀ z ∈ imGT 0, Φ w (z + 1) = cexp (2 * π * I * r) * Φ w z)
    (hbd : ∀ w, ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ z.im →
      ‖Φ w z‖ ≤ C * Real.exp (K * z.im)) :
    ∃ S : M →ₗ[ℂ] FormalQSeries, (∀ w, Good (expBase r K) (S w)) ∧
      ∀ w, ∀ z ∈ imGT 0, Φ w z = qEvalC (S w) (expBase r K) z := by
  classical
  set b := expBase r K with hb
  have hex : ∀ w, ∃ a : ℕ → ℂ, ∀ z ∈ imGT 0, HasSum
      (fun n : ℕ => a n * cexp (2 * π * I * n * z)) (cexp (-(2 * π * I * b * z)) * Φ w z) := by
    intro w
    obtain ⟨C, hC⟩ := hbd w
    exact exists_expansion (Φ w) r K C (hholo w) (hper w) hC
  choose a ha using hex
  let s : M → FormalQSeries := fun w => seqAt b (a w)
  have hterm : ∀ w n z, qTerm (s w) b n z = a w n * cexp (2 * π * I * n * z) := by
    intro w n z
    simp only [s, qTerm, seqAt_apply]
  have hgood : ∀ w, Good b (s w) := fun w =>
    ⟨seqAt_mem _, fun z hz => ((ha w z hz).summable).congr fun n => (hterm w n z).symm⟩
  have heval : ∀ w, ∀ z ∈ imGT 0, Φ w z = qEvalC (s w) b z := by
    intro w z hz
    rw [qEvalC, qSeriesC, tsum_congr (hterm w · z), (ha w z hz).tsum_eq, ← mul_assoc,
      ← Complex.exp_add, show 2 * π * I * z * b + -(2 * π * I * b * z) = 0 by ring,
      Complex.exp_zero, one_mul]
  have hadd' : ∀ v w, s (v + w) = s v + s w := by
    intro v w
    apply eq_of_good (hgood _) ((hgood v).add (hgood w))
    intro z hz
    rw [qEvalC_add _ _ _ ((hgood v).2 z hz) ((hgood w).2 z hz), ← heval _ z hz,
      ← heval _ z hz, ← heval _ z hz, hadd v w z hz]
  have hsmul' : ∀ (c : ℂ) w, s (c • w) = c • s w := by
    intro c w
    apply eq_of_good (hgood _) ((hgood w).smul c)
    intro z hz
    rw [qEvalC_smul, ← heval _ z hz, ← heval _ z hz, hsmul c w z hz]
  exact ⟨⟨⟨s, hadd'⟩, hsmul'⟩, hgood, heval⟩

end VOA.Huang.GenusOne.Close
