import VOA.Huang.LogHuangODEIterPointMain
import VOA.Huang.LogHuangODEProductMain
import VOA.Huang.HuangODEIterPoint

/-! Actual logarithmic coset coefficients have convergent collision-point
Frobenius expansions. All scalar coefficients come from true logarithmic
intertwining operators on finitely generated generalized modules. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogHuangODEIterPoint
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries VOA.Huang.FuchsianODE VOA.Huang.Convergence
open VOA.Huang.HuangODEAlgebra VOA.Huang.LogHuangODEProduct
open VOA.Huang.HuangODEIterPoint
open VOA.Huang.AssocExpansion
open VOA.Huang.FrobeniusLog
open scoped BigOperators

/-- Absolute convergence throughout the unit disc bounds the coefficients
subexponentially. This direction uses the actual convergent terms. -/
theorem subexp_of_summable_unitDisc {G : PowerSeries ℂ}
    (hs : ∀ t : ℂ, ‖t‖<1 → Summable fun n => ‖coeff n G*t^n‖) : G∈SubexpPS := by
  apply mem_subexpPS.mpr
  intro r hr
  have hr0 : 0<r := lt_trans zero_lt_one hr
  have ht : ‖((r⁻¹ : ℝ) : ℂ)‖<1 := by
    rw [Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hr0.le)]
    exact inv_lt_one_of_one_lt₀ hr
  obtain ⟨C,hC⟩ := ((hs _ ht).tendsto_cofinite_zero).bddAbove_range_of_cofinite
  refine ⟨C,fun n => ?_⟩
  have hh : ‖coeff n G*((r⁻¹ : ℝ) : ℂ)^n‖≤C := hC ⟨n,rfl⟩
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hr0.le),
    inv_pow] at hh
  have hrn : 0<r^n := pow_pos hr0 n
  calc ‖coeff n G‖=‖coeff n G‖*(r^n)⁻¹*r^n := by field_simp
    _≤C*r^n := mul_le_mul_of_nonneg_right hh hrn.le

/-- A polynomial monic collision relation is an actual analytic Euler equation. -/
theorem analytic_collision_equation {H : PowerSeries ℂ} (hH : H∈SubexpPS)
    (κ σ : ℂ)
    (hrel : ∃ (m : ℕ) (r : ℕ → PowerSeries ℂ), (∀ k,r k∈ratRing 0) ∧
      (DOp κ σ)^[m] H=∑ k∈Finset.range m,r k*(DOp κ σ)^[k] H) :
    ∃ (m : ℕ), 1 ≤ m ∧ ∃ c : ℕ → PowerSeries ℂ, (∀ i < m,c i∈SubexpPS) ∧
      ∀ t∈overlapDomain,
        iteratedDeriv m (Ev κ σ H) t +
          ∑ i∈Finset.range m,psEval (c i) (Complex.exp t)*iteratedDeriv i (Ev κ σ H) t=0 := by
  obtain ⟨m,r,hr,hm⟩ := hrel
  obtain ⟨m',r',hr',hm'1,hrel'⟩ : ∃ (m' : ℕ) (r' : ℕ → PowerSeries ℂ),
      (∀ k,r' k∈ratRing 0) ∧ 1 ≤ m' ∧
      (DOp κ σ)^[m'] H=∑ k∈Finset.range m',r' k*(DOp κ σ)^[k] H := by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · have h0 : H=0 := by simpa using hm
      exact ⟨1,fun _ => 0,fun _ => Subalgebra.zero_mem _,le_rfl,by simp [h0]⟩
    · exact ⟨m,r,hr,hpos,hm⟩
  choose c hc hcev using fun k => exists_subexp_of_mem_ratRing_zero (hr' k)
  refine ⟨m',hm'1,fun k => -c k,fun i _ => SubexpPS.neg_mem (hc i),fun t ht => ?_⟩
  have hu : ‖Complex.exp t‖<1 := by
    rw [Complex.norm_exp]
    exact Real.exp_lt_one_iff.mpr ht.1
  rw [iteratedDeriv_Ev κ σ hH m' t ht,hrel',
    Ev_sum_mul κ σ _ (fun k _ => subexp_of_mem_ratRing_zero (hr' k))
      (fun k _ => DOp_iterate_mem κ σ hH k) ht,← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [iteratedDeriv_Ev κ σ hH k t ht,psEval_neg,hcev k _ hu]
  simp only [xt]
  ring

/-- The actual analytic collision function has a finite convergent log-Frobenius expansion. -/
theorem collision_frobenius_expansion {H : PowerSeries ℂ} (hH : H∈SubexpPS)
    (κ σ : ℂ)
    (hrel : ∃ (m : ℕ) (r : ℕ → PowerSeries ℂ), (∀ k,r k∈ratRing 0) ∧
      (DOp κ σ)^[m] H=∑ k∈Finset.range m,r k*(DOp κ σ)^[k] H) :
    ∃ (ι : Type) (_ : Fintype ι) (lam : ι → ℂ) (p : ι → ℕ → Polynomial ℂ) (a : ι → ℂ),
      (∀ j,LogGood (p j)) ∧
      ∀ t∈overlapDomain,Ev κ σ H t=∑ j,a j*logFun (lam j) (p j) t := by
  obtain ⟨m,hm,c,hc,hode⟩ := analytic_collision_equation hH κ σ hrel
  have hd : DifferentiableOn ℂ (Ev κ σ H) overlapDomain :=
    fun t ht => (hasDerivAt_Ev κ σ hH ht).differentiableAt.differentiableWithinAt
  obtain ⟨ι,hi,lam,p,a,hcard,hp,hroot,he⟩ :=
    fundamental_system hm hc isOpen_overlapDomain isPreconnected_overlapDomain
      overlapDomain_subset overlapDomain_nonempty hd hode
  exact ⟨ι,hi,lam,p,a,fun j => logGood_of_logFuchsianEq hm hc (hp j),he⟩

end VOA.Huang.LogHuangODEIterPoint
