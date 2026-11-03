import VOA.Huang.PentagonCloseUniq

/-! Genuine generalized power-log series have unique coefficients on a
positive real interval. Every logarithmic polynomial is retained; overlapping
finite exponent progressions are assigned once and never counted twice. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePoint
open VOA VOA.Huang.FrobeniusLog VOA.Huang.LogRemovalCoeff VOA.Huang.AssocConverse
open scoped BigOperators

/-- Real-ray uniqueness for genuine finite-degree logarithmic polynomials
with actual absolutely summable coefficients on the normalized unit scale. -/
theorem loggps_coeff_zero_core (S : Finset ℂ) (c₀ : ℂ) (A : ℂ → Polynomial ℂ)
    (K : ℕ) (hdegree : ∀ w,(A w).natDegree≤K)
    (hsupp : ∀ w,A w≠0 → ∃ h∈S,∃ n : ℕ,w=h+n)
    (hcoeff : ∀ k : ℕ,Summable (fun w : ℂ => ‖(A w).coeff k‖))
    (hsum : ∀ r : ℝ,0<r → r≤1 →
      Summable (fun w => (A w).eval ((Real.log r : ℝ) : ℂ)*(r : ℂ)^(w-c₀)))
    (hz : ∀ r : ℝ,0<r → r<1 →
      ∑' w,(A w).eval ((Real.log r : ℝ) : ℂ)*(r : ℂ)^(w-c₀)=0) :
    ∀ w k,(A w).coeff k=0 := by
  classical
  let own : ℂ → ℂ := fun w => if h : ∃ h∈S,∃ n : ℕ,w=h+n then h.choose else 0
  have own_spec (w : ℂ) (h : ∃ h∈S,∃ n : ℕ,w=h+n) :
      own w∈S ∧ ∃ n : ℕ,w=own w+n := by
    simp only [own,dif_pos h]
    exact h.choose_spec
  let ι := {x // x∈S}
  let lam : ι → ℂ := fun j => (j : ℂ)-c₀
  let p : ι → ℕ → Polynomial ℂ := fun j n =>
    if own ((j : ℂ)+n)=j then A ((j : ℂ)+n) else 0
  let M : ℕ → ℝ := fun k => ∑' w : ℂ,‖(A w).coeff k‖
  have hM (k : ℕ) : 0≤M k := tsum_nonneg fun _ => norm_nonneg _
  have hbM (w : ℂ) (k : ℕ) : ‖(A w).coeff k‖≤M k :=
    (hcoeff k).le_tsum w (fun _ _ => norm_nonneg _)
  have hp : ∀ j,LogGood (p j) := by
    intro j
    refine ⟨⟨K,fun n => ?_⟩,fun k r hr => ?_⟩
    · dsimp only [p]
      split_ifs
      · exact hdegree _
      · simp
    · refine ⟨M k,fun n => ?_⟩
      have hb : ‖(p j n).coeff k‖≤M k := by
        dsimp only [p]
        split_ifs
        · exact hbM _ k
        · simpa using hM k
      calc
        ‖(p j n).coeff k‖≤M k := hb
        _ ≤M k*r^n := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hr.le) (hM k)
  have hz' : ∀ t : ℝ,-1<t → t<0 → ∑ j,logFun (lam j) (p j) t=0 := by
    intro t ht ht0
    let r : ℝ := Real.exp t
    have hr0 : 0<r := Real.exp_pos t
    have hr1 : r<1 := Real.exp_lt_one_iff.mpr ht0
    have hrne : (r : ℂ)≠0 := by exact_mod_cast hr0.ne'
    have hcp (z : ℂ) : (r : ℂ)^z=Complex.exp (z*t) := by
      rw [Complex.cpow_def_of_ne_zero hrne,← Complex.ofReal_log hr0.le]
      dsimp only [r]
      rw [Real.log_exp,mul_comm]
    let f : ℂ → ℂ := fun w => (A w).eval ((Real.log r : ℝ) : ℂ)*(r : ℂ)^(w-c₀)
    have hf : Summable f := hsum r hr0 hr1.le
    let g : ι → ℂ → ℂ := fun j w => if own w=j then f w else 0
    have hg (j : ι) : Summable (g j) := by
      refine Summable.of_norm_bounded hf.norm fun w => ?_
      dsimp only [g]
      split_ifs
      · exact le_rfl
      · simp
    have hlog (j : ι) : logFun (lam j) (p j) t=∑' w,g j w := by
      have hinj : Function.Injective (fun n : ℕ => (j : ℂ)+n) := by
        intro m n he
        exact_mod_cast add_left_cancel he
      have hsub : Function.support (g j)⊆Set.range (fun n : ℕ => (j : ℂ)+n) := by
        intro w hw
        simp only [Function.mem_support,g] at hw
        split_ifs at hw with he
        · have hAw : A w≠0 := fun h0 => hw (by simp [f,h0])
          obtain ⟨_,n,hn⟩ := own_spec w (hsupp w hAw)
          exact ⟨n,by rw [hn,he]⟩
        · exact absurd rfl hw
      rw [← hinj.tsum_eq hsub,logFun]
      apply tsum_congr
      intro n
      dsimp only [p,g,f]
      split_ifs
      · rw [hcp]
        dsimp only [r]
        rw [Real.log_exp,mul_comm]
        congr 2
        dsimp only [lam]
        ring
      · simp
    have hsumg (w : ℂ) : ∑ j,g j w=f w := by
      by_cases hA : A w=0
      · simp [g,f,hA]
      · obtain ⟨hS,_⟩ := own_spec w (hsupp w hA)
        rw [Finset.sum_eq_single (⟨own w,hS⟩ : ι)]
        · simp [g]
        · intro j hj hjne
          dsimp only [g]
          rw [if_neg]
          exact fun he => hjne (Subtype.ext he.symm)
        · intro h
          exact absurd (Finset.mem_univ _) h
    simp_rw [hlog]
    rw [← Summable.tsum_finsetSum (fun j hj => hg j)]
    simp_rw [hsumg]
    exact hz r hr0 hr1
  have he := log_coeff_zero_of_real_interval lam p hp (a := -1) (by norm_num) hz'
  intro w k
  by_cases hA : A w=0
  · simp [hA]
  obtain ⟨hS,n₀,hn₀⟩ := own_spec w (hsupp w hA)
  have hh := he (w-c₀) k
  rw [Finset.sum_eq_single (⟨own w,hS⟩ : ι)] at hh
  · have hw' : w-c₀=lam ⟨own w,hS⟩+n₀ := by
      dsimp only [lam]
      linear_combination hn₀
    rw [hw',exCoeff_of_eq] at hh
    dsimp only [p] at hh
    rw [← hn₀,if_pos rfl] at hh
    exact hh
  · intro j hj hjne
    by_cases hex : ∃ n : ℕ,lam j+n=w-c₀
    · obtain ⟨n,hn⟩ := hex
      have hjn : (j : ℂ)+n=w := by
        dsimp only [lam] at hn
        linear_combination hn
      rw [← hn,exCoeff_of_eq]
      dsimp only [p]
      rw [hjn,if_neg]
      · simp
      · exact fun he => hjne (Subtype.ext he.symm)
    · exact exCoeff_of_forall_ne (fun n hn => hex ⟨n,hn⟩) _ _
  · intro h
    exact absurd (Finset.mem_univ _) h

end VOA.Huang.LogAssocFivePoint
