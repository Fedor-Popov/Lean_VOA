import VOA.Classification.COne.McRaeM2LogBraidedTranslate
import VOA.Huang.HexagonCloseChart4

/-! # Half-plane continuation of completed logarithmic products

Every row series of a homogeneous completed logarithmic product solves a rational
Fuchsian equation whose only finite pole is at `x = 1`
(`exists_ratFuchsian_log_product_homogeneous`, extracted from the proof of
`summable_log_product_homogeneous`). The proved Möbius-chart continuation
(`fuchsian_halfPlane_continuation`) therefore continues each row to each open half
plane `s·Im x > 0` (`exists_rowEval_halfPlane`), and the whole completed product
continues, holomorphically in both branches, to `{s·Im e^{λ₂-λ₁} > 0}`
(`exists_prodValue_halfPlane`). This is the logarithmic analogue of
`ProductHalfPlaneContinuation`; it uses only `C₂`-cofiniteness. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogHuangODEProduct
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries VOA.Huang.FuchsianODE VOA.Huang.Convergence
open VOA.Huang.HuangODEAlgebra
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- The genuine row series of a homogeneous logarithmic product is a shifted
solution of a rational Fuchsian equation with its only finite pole at `x = 1`. -/
theorem exists_ratFuchsian_log_product_homogeneous (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    {α₁ α₂ α₃ : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x ∈ N₁.weight α₁) (hy : y ∈ N₂.weight α₂) (hz : z ∈ N₃.weight α₃)
    (f : M₄ →ₗ[ℂ] ℂ) (a b : ℂ) (k l : ℕ) :
    ∃ (K : ℕ) (ν : ℂ) (Q : PowerSeries ℂ), RatFuchsian 1 ν Q ∧
      ∀ n : ℕ, coeff (n+K) Q = f (Y₁.1 (a+n) k x (Y₂.1 (b-n) l y z)) := by
  classical
  let α₄ := α₁+α₂+α₃-a-b-2
  obtain ⟨h₁,N₁',he₁,hl₁⟩ := exists_cosetBase N₁.toGW α₁
  obtain ⟨h₂,N₂',he₂,hl₂⟩ := exists_cosetBase N₂.toGW α₂
  obtain ⟨h₃,N₃',he₃,hl₃⟩ := exists_cosetBase N₃.toGW α₃
  obtain ⟨h₄,N₄',he₄,hl₄⟩ := exists_cosetBase N₄.toGW α₄
  have hx' : x ∈ N₁.weight (h₁+N₁') := he₁ ▸ hx
  have hy' : y ∈ N₂.weight (h₂+N₂') := he₂ ▸ hy
  have hz' : z ∈ N₃.weight (h₃+N₃') := he₃ ▸ hz
  obtain ⟨B₁,hC₁⟩ := exists_C1Graded hC2 N₁ hfg₁ hl₁
  obtain ⟨B₂,hC₂⟩ := exists_C1Graded hC2 N₂ hfg₂ hl₂
  obtain ⟨B₃,hC₃⟩ := exists_C1Graded hC2 N₃ hfg₃ hl₃
  obtain ⟨B₄,hD₄⟩ := exists_DualC1Graded hC2 N₄ hfg₄ hl₄
  obtain ⟨K₁,hK₁⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  obtain ⟨K₂,hK₂⟩ := uniform_log_degree_of_finGen N₂ N₃ N₅ hfg₂ hfg₃ hfg₅
  have hJ₁ (q : ℕ) := logCoefficient_isGradedJacobi Y₁.2 q
  have hJ₂ (q : ℕ) := logCoefficient_isGradedJacobi Y₂.2 q
  let s := N₁'+N₂'+N₃'+N₄'
  obtain ⟨K,hUB⟩ := exists_unifBase_family (A₂ := N₂.toGW) (A₃ := N₃.toGW) (A₅ := N₅.toGW)
    (fun q n => Y₂.1 n q) hJ₂ h₂ h₃ b s
  let ν := b-(s : ℂ)+K
  let c := h₁+h₂+h₃-h₄-2
  obtain ⟨NN,hFG,hmem⟩ := exists_joint_fg (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) (h₄ := h₄)
    (ν := ν) hJ₁ hJ₂ hl₁ hl₂ hl₃ hl₄ hUB hC₁ hC₂ hC₃ hD₄
    (fun n q hq => hK₁ Y₁ n q hq) (fun n q hq => hK₂ Y₂ n q hq)
  let Q : (ℕ × ℕ) → ℕ → PowerSeries ℂ := fun p j =>
    QT (fun n => Y₁.1 n p.1) (fun n => Y₂.1 n p.2) c ν f x
      ((⇑(Lm1 N₂.toWeakModule))^[j] y) z N₄' (s+j)
  have hQmem : ∀ p j, Q p j ∈ NN := by
    intro p j
    have hh := hmem p.1 p.2 N₁' (N₂'+j) N₃' N₄' f x
      ((⇑(Lm1 N₂.toWeakModule))^[j] y) z hx'
      (Lm1_iterate_mem_weight (A₂ := N₂.toGW) hy' j) hz'
    simpa only [Q,c,s,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh
  let lam : ℕ → ℂ := fun j => -(ν+((s+j : ℕ) : ℂ)+1)
  let next : ℕ × ℕ → ℕ × ℕ := fun p => (p.1,p.2+1)
  let d : ℕ × ℕ → ℂ := fun p => (p.2 : ℂ)+1
  have hQ : ∀ p j, Q p (j+1)=thetaShift (lam j) (Q p j)+d p • Q (next p) j := by
    intro p j
    dsimp only [Q,lam,d,next]
    rw [Function.iterate_succ_apply',show s+(j+1)=s+j+1 by omega]
    exact QT_LogLm1 (A₂ := N₂.toGW) (A₃ := N₃.toGW) (A₅ := N₅.toGW)
      (Y₁ := Y₁.1) (Y₂ := Y₂.1) Y₂.2 c ν f x
      ((⇑(Lm1 N₂.toWeakModule))^[j] y) z p.1 p.2 N₄' (s+j)
  have hRat := ratFuchsian_of_coupled_fg NN hFG Q next d lam hQ hQmem (k,l) 0
  have hcoeff (n : ℕ) : coeff (n+K) (Q (k,l) 0) =
      f (Y₁.1 (a+n) k x (Y₂.1 (b-n) l y z)) := by
    simp only [Q,Function.iterate_zero,id,Nat.add_zero,QT,coeff_prodQ]
    have hc : c=a+b-(N₁' : ℂ)-N₂'-N₃'+N₄' := by
      dsimp only [c,α₄] at *
      linear_combination he₄-he₁-he₂-he₃
    have ha : c-ν-2*N₄'+((n+K : ℕ) : ℂ)=a+n := by
      rw [hc]
      dsimp [ν,s]
      push_cast
      ring
    have hb : ν+((s : ℕ) : ℂ)-((n+K : ℕ) : ℂ)=b-n := by
      dsimp [ν]
      push_cast
      ring
    rw [ha,hb]
  exact ⟨K, 0, Q (k,l) 0, hRat, hcoeff⟩

end VOA.Huang.LogHuangODEProduct

namespace VOA.Huang.LogBraided
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.LogAssocExpansion
open VOA.Huang.Convergence VOA.Huang.FuchsianODE
open VOA.Huang.TensorCat.HexagonClose (Lhs isOpen_Lhs fuchsian_halfPlane_continuation)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- A shifted rational Fuchsian row continues to each open half plane. -/
theorem exists_rowEval_halfPlane {c : ℕ → ℂ} {K : ℕ} {ν : ℂ} {Q : PowerSeries ℂ}
    (hQ : RatFuchsian 1 ν Q) (hc : ∀ n : ℕ, PowerSeries.coeff (n+K) Q = c n)
    {s : ℝ} (hs : s * s = 1) :
    ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Lhs s) ∧
      ∀ w ∈ Lhs s, ‖w‖ < 1 → Ψ w = rowEval c w := by
  have hsum : ∀ w : ℂ, ‖w‖ < 1 → Summable fun n => PowerSeries.coeff n Q * w^n :=
    fun w hw => (summable_of_ratFuchsian (by norm_num) hQ hw).of_norm
  obtain ⟨s₀, bb, cc, p, hcp, hG⟩ := hQ
  have hcp' : ∀ i < s₀, (1 - PowerSeries.X) ^ bb * cc i = (p i : PowerSeries ℂ) := by
    intro i hi
    have h := hcp i hi
    rwa [map_one, one_mul] at h
  obtain ⟨Ψ₀, hΨ₀a, hΨ₀⟩ := fuchsian_halfPlane_continuation hcp' hG hs
  have hne : ∀ w ∈ Lhs s, w ≠ 0 := by
    intro w hw h0
    have : 0 < s * w.im := hw
    rw [h0, Complex.zero_im, mul_zero] at this
    exact lt_irrefl _ this
  refine ⟨fun w => (Ψ₀ w - ∑ n∈Finset.range K, PowerSeries.coeff n Q * w^n) / w^K,
    fun w hw => ?_, fun w hw hw1 => ?_⟩
  · refine ((hΨ₀a w hw).sub ?_).div (analyticAt_id.pow K) (pow_ne_zero K (hne w hw))
    exact Finset.analyticAt_fun_sum _ fun n _ => analyticAt_const.mul (analyticAt_id.pow n)
  · show (Ψ₀ w - ∑ n∈Finset.range K, PowerSeries.coeff n Q * w^n) / w^K = rowEval c w
    rw [hΨ₀ w hw hw1, VOA.Huang.FrobeniusLog.psEval, ← (hsum w hw1).sum_add_tsum_nat_add K,
      add_sub_cancel_left, rowEval]
    have he : ∑' n : ℕ, PowerSeries.coeff (n+K) Q * w^(n+K) = w^K * ∑' n : ℕ, c n * w^n := by
      rw [← tsum_mul_left]
      refine tsum_congr fun n => ?_
      rw [hc, pow_add]; ring
    rw [he, mul_div_cancel_left₀ _ (pow_ne_zero K (hne w hw))]

/-- **Half-plane continuation of a completed logarithmic product**, jointly
holomorphic in the two branches. -/
theorem exists_prodValue_halfPlane (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (K L : ℕ) {a b c : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ) {s : ℝ} (hs : s * s = 1) :
    ∃ Φ : ℂ × ℂ → ℂ, DifferentiableOn ℂ Φ {p : ℂ × ℂ | 0 < s * (Complex.exp (p.2-p.1)).im} ∧
      ∀ p : ℂ × ℂ, p.2.re < p.1.re → 0 < s * (Complex.exp (p.2-p.1)).im →
        prodValue hC2 N₅ hfg₅ Y₁.1 Y₂.1 K L f x y z a b c β p.1 p.2 = Φ p := by
  have hex : ∀ (mu : ℂ) (k l : ℕ), ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Lhs s) ∧
      ∀ w ∈ Lhs s, ‖w‖ < 1 → Ψ w = rowEval (prodRow Y₁.1 Y₂.1 f x y z
        (a+lowerSpectrumRep hC2 N₅ hfg₅ mu-β-1) (b+c-lowerSpectrumRep hC2 N₅ hfg₅ mu-1) k l) w := by
    intro mu k l
    obtain ⟨K', ν, Q, hQ, hc⟩ :=
      VOA.Huang.LogHuangODEProduct.exists_ratFuchsian_log_product_homogeneous hC2
        N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hx hy hz f
        (a+lowerSpectrumRep hC2 N₅ hfg₅ mu-β-1) (b+c-lowerSpectrumRep hC2 N₅ hfg₅ mu-1) k l
    exact exists_rowEval_halfPlane hQ hc hs
  choose Ψ hΨa hΨ using hex
  refine ⟨fun p => ∑ mu∈spectrumCosets hC2 N₅ hfg₅, ∑ k∈Finset.range K, ∑ l∈Finset.range L,
      Complex.exp (p.1*(β-a-lowerSpectrumRep hC2 N₅ hfg₅ mu)) *
        Complex.exp (p.2*(lowerSpectrumRep hC2 N₅ hfg₅ mu-b-c)) * p.1^k * p.2^l *
        Ψ mu k l (Complex.exp (p.2-p.1)), fun p hp => ?_, fun p hlt hp => ?_⟩
  · refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.fun_sum fun mu _ => DifferentiableAt.fun_sum fun k _ =>
      DifferentiableAt.fun_sum fun l _ => ?_
    have h1 : DifferentiableAt ℂ (fun p : ℂ × ℂ => Ψ mu k l (Complex.exp (p.2-p.1))) p :=
      ((hΨa mu k l _ hp).differentiableAt).comp p
        ((differentiableAt_snd.sub differentiableAt_fst).cexp)
    refine DifferentiableAt.mul ?_ h1
    fun_prop
  · unfold prodValue
    refine Finset.sum_congr rfl fun mu _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => ?_
    rw [hΨ mu k l _ hp (norm_exp_sub_lt_one hlt)]

end VOA.Huang.LogBraided
