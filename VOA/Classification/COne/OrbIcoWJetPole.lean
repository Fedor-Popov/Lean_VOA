import VOA.Classification.COne.OrbIcoWJetApprox

/-! Removing a certified resonant pivot with a continuous remainder.
An order-v denominator loses v jet orders. This is cancellation on the
punctured neighborhood, with no division at the special fiber. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoW
open OrbOdd Polynomial Filter Topology

/-- The actual denominator factors by the certified pivot order, and its
remaining continuous factor has the certified nonzero value at the fiber. -/
theorem JetApprox.pivot_factor {d v : ℕ} {den : ℂ → ℂ} {D : ℂ[X]}
    (hden : JetApprox d den D) (hv : v < d)
    (hbefore : ∀ i < v, D.coeff i=0) :
    ∃ u : ℂ → ℂ, ContinuousAt u 1 ∧ u 1=D.coeff v ∧
      ∀ᶠ t in 𝓝[≠] (1 : ℂ), den t=(t-1)^v*u t := by
  obtain ⟨a,ha⟩ := Polynomial.X_pow_dvd_iff.mpr hbefore
  have ha0 : a.eval 0=D.coeff v := by
    rw [ha]
    exact a.coeff_zero_eq_eval_zero.symm.trans
      (by simpa only [zero_add] using (Polynomial.coeff_X_pow_mul a v 0).symm)
  obtain ⟨r,hr,hden⟩ := hden
  let u : ℂ → ℂ := fun t => a.eval (t-1)+(t-1)^(d-v)*r t
  have hu : ContinuousAt u 1 := by dsimp [u]; fun_prop
  refine ⟨u,hu,?_,?_⟩
  · simp only [u,sub_self,zero_pow (by omega : d-v≠0),zero_mul,add_zero]
    exact ha0
  · filter_upwards [hden] with t ht
    rw [ht,ha,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X]
    dsimp [u]
    rw [mul_add,← mul_assoc,← pow_add,show v+(d-v)=d by omega]

/-- A certified undivided error equation determines the quotient jet across
any nonzero pivot, with exactly its order of precision loss. -/
theorem JetApprox.cancel_pivot {d v : ℕ} {den f : ℂ → ℂ} {D J : ℂ[X]}
    (hden : JetApprox d den D) (hv : v < d)
    (hbefore : ∀ i < v, D.coeff i=0) (hpivot : D.coeff v≠0)
    (herr : JetApprox d (fun t => den t*(f t-J.eval (t-1))) 0) :
    JetApprox (d-v) f J := by
  obtain ⟨u,hu,hu1,hden⟩ := hden.pivot_factor hv hbefore
  have hu0 : u 1≠0 := by rwa [hu1]
  obtain ⟨r,hr,herr⟩ := herr
  refine ⟨fun t => r t/u t,hr.div hu hu0,?_⟩
  have hun : ∀ᶠ t in 𝓝[≠] (1 : ℂ), u t≠0 :=
    (hu.eventually_ne hu0).filter_mono nhdsWithin_le_nhds
  have htn : ∀ᶠ t in 𝓝[≠] (1 : ℂ), t≠1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using ht
  filter_upwards [hden,herr,hun,htn] with t hd he hu ht
  have he' : u t*(f t-J.eval (t-1))=(t-1)^(d-v)*r t := by
    have htv : (t-1)^v≠0 := pow_ne_zero _ (sub_ne_zero.mpr ht)
    apply mul_left_cancel₀ htv
    rw [← mul_assoc,← hd]
    rw [he,Polynomial.eval_zero,zero_add]
    rw [← mul_assoc,← pow_add,show v+(d-v)=d by omega]
  have hdiv : f t-J.eval (t-1)=((t-1)^(d-v)*r t)/u t :=
    (eq_div_iff hu).mpr (by simpa only [mul_comm] using he')
  calc
    f t=J.eval (t-1)+(f t-J.eval (t-1)) := by ring
    _=J.eval (t-1)+(t-1)^(d-v)*(r t/u t) := by rw [hdiv]; ring

end VOA.Classification.COne.OrbIcoW
