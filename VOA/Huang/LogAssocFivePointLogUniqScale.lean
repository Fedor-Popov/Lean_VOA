import VOA.Huang.LogAssocFivePointLogUniq

/-! Real sewing uniqueness at every genuine positive radius. The actual
logarithmic polynomials transform by Taylor shift under a change of scale;
all logarithmic degrees remain present in the exact coefficient identity. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePoint
open scoped BigOperators

/-- Every fixed polynomial linear functional is absolutely summable on a
uniform-degree family with absolutely summable original coefficients. -/
theorem summable_polynomial_linear_bounded_degree (A : ℂ → Polynomial ℂ)
    (K : ℕ) (hdegree : ∀ w,(A w).natDegree≤K)
    (hcoeff : ∀ k : ℕ,Summable (fun w : ℂ => ‖(A w).coeff k‖))
    (L : Polynomial ℂ →ₗ[ℂ] ℂ) : Summable (fun w : ℂ => L (A w)) := by
  have hh : Summable (fun w : ℂ =>
      ∑ i∈Finset.range (K+1),(A w).coeff i*L ((Polynomial.X : Polynomial ℂ)^i)) :=
    summable_sum fun i hi => (hcoeff i).of_norm.mul_right _
  refine hh.congr fun w => ?_
  have he : L (A w)=∑ i∈Finset.range (K+1),(A w).coeff i*L ((Polynomial.X : Polynomial ℂ)^i) := by
    calc
      L (A w)=L (∑ i∈Finset.range (K+1),Polynomial.C ((A w).coeff i)*(Polynomial.X : Polynomial ℂ)^i) :=
        congrArg L (Polynomial.as_sum_range_C_mul_X_pow' (A w) (Nat.lt_succ_of_le (hdegree w)))
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul]
  exact he.symm

/-- Scaling the real variable genuinely Taylor-shifts the logarithmic
polynomial and multiplies the complex exponent coefficient. -/
theorem loggps_scale_term (A : ℂ → Polynomial ℂ) (c₀ : ℂ)
    {q r : ℝ} (hq : 0<q) (hr : 0<r) (w : ℂ) :
    (Polynomial.taylor (Real.log q : ℂ) (((q : ℂ)^(w-c₀)) • A w)).eval (Real.log r : ℂ)*
      (r : ℂ)^(w-c₀)=
    (A w).eval (Real.log (q*r) : ℂ)*((q*r : ℝ) : ℂ)^(w-c₀) := by
  rw [Polynomial.taylor_eval,Polynomial.eval_smul,smul_eq_mul]
  have hlog : (Real.log r : ℂ)+(Real.log q : ℂ)=(Real.log (q*r) : ℂ) := by
    rw [← Complex.ofReal_add,Real.log_mul hq.ne' hr.ne',add_comm]
  rw [hlog,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hq.le hr.le]
  ring

/-- True full power-log series with finite (possibly overlapping) exponent
progressions and genuine absolute coefficient convergence have unique
coefficients on every positive real sewing interval. -/
theorem loggps_coeff_zero (S : Finset ℂ) (c₀ : ℂ) (A : ℂ → Polynomial ℂ)
    (K : ℕ) (hdegree : ∀ w,(A w).natDegree≤K)
    (hsupp : ∀ w,A w≠0 → ∃ h∈S,∃ n : ℕ,w=h+n)
    {R : ℝ} (hR : 0<R)
    (hcoeff : ∀ (r : ℝ),0<r → r<R → ∀ k : ℕ,
      Summable (fun w : ℂ => (A w).coeff k*(r : ℂ)^(w-c₀)))
    (hsum : ∀ r : ℝ,0<r → r<R →
      Summable (fun w => (A w).eval (Real.log r : ℂ)*(r : ℂ)^(w-c₀)))
    (hz : ∀ r : ℝ,0<r → r<R →
      ∑' w,(A w).eval (Real.log r : ℂ)*(r : ℂ)^(w-c₀)=0) :
    ∀ w k,(A w).coeff k=0 := by
  have hq : 0<R/2 := by linarith
  have hqR : R/2<R := by linarith
  let B : ℂ → Polynomial ℂ := fun w => (((R/2 : ℝ) : ℂ)^(w-c₀)) • A w
  let C : ℂ → Polynomial ℂ := fun w => Polynomial.taylor (Real.log (R/2) : ℂ) (B w)
  have hBdegree : ∀ w,(B w).natDegree≤K := by
    intro w
    exact (Polynomial.natDegree_smul_le _ _).trans (hdegree w)
  have hBcoeff : ∀ k : ℕ,Summable (fun w : ℂ => ‖(B w).coeff k‖) := by
    intro k
    have hh := (hcoeff (R/2) hq hqR k).norm
    refine hh.congr fun w => ?_
    simp only [B,Polynomial.coeff_smul,smul_eq_mul,mul_comm]
  have hCdegree : ∀ w,(C w).natDegree≤K := by
    intro w
    simpa only [C,Polynomial.natDegree_taylor] using hBdegree w
  have hCsupp : ∀ w,C w≠0 → ∃ h∈S,∃ n : ℕ,w=h+n := by
    intro w hw
    apply hsupp w
    exact fun hz => hw (by simp [C,B,hz])
  have hCcoeff : ∀ k : ℕ,Summable (fun w : ℂ => ‖(C w).coeff k‖) := by
    intro k
    have hh := summable_polynomial_linear_bounded_degree B K hBdegree hBcoeff
      ((Polynomial.lcoeff ℂ k).comp (Polynomial.taylor (Real.log (R/2) : ℂ)))
    exact hh.norm
  have hr (r : ℝ) (hr0 : 0<r) (hr1 : r≤1) : 0<R/2*r ∧ R/2*r<R := by
    constructor
    · exact mul_pos hq hr0
    · nlinarith
  have hscale (r : ℝ) (hr0 : 0<r) (w : ℂ) :
      (C w).eval (Real.log r : ℂ)*(r : ℂ)^(w-c₀)=
        (A w).eval (Real.log (R/2*r) : ℂ)*((R/2*r : ℝ) : ℂ)^(w-c₀) :=
    loggps_scale_term A c₀ hq hr0 w
  have hcore := loggps_coeff_zero_core S c₀ C K hCdegree hCsupp hCcoeff
    (fun r hr0 hr1 => (hsum _ (hr r hr0 hr1).1 (hr r hr0 hr1).2).congr
      (fun w => (hscale r hr0 w).symm))
    (fun r hr0 hr1 => (tsum_congr (hscale r hr0)).trans
      (hz _ (hr r hr0 hr1.le).1 (hr r hr0 hr1.le).2))
  intro w k
  have hC0 : C w=0 := by
    apply Polynomial.ext
    intro k
    simpa only [Polynomial.coeff_zero] using hcore w k
  have hB0 : B w=0 := by
    apply (Polynomial.taylor_injective (Real.log (R/2) : ℂ))
    simpa only [C,map_zero] using hC0
  have hn : ((R/2 : ℝ) : ℂ)^(w-c₀)≠0 := by
    exact (Complex.cpow_ne_zero_iff).mpr (Or.inl (by exact_mod_cast hq.ne'))
  have hA0 : A w=0 := (smul_eq_zero.mp hB0).resolve_left hn
  simp [hA0]

end VOA.Huang.LogAssocFivePoint
