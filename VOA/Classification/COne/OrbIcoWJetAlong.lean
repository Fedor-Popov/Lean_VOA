import VOA.Classification.COne.OrbIcoWJetPole

/-! Continuous-remainder jets along arbitrary punctured approach filters.
This permits the actual generic Ward family on the nonreal parameter locus. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoW
open OrbOdd Polynomial Filter Topology

/-- A polynomial jet through order d-1 with a continuous local remainder. -/
def JetApproxAlong (l : Filter ℂ) (d : ℕ) (f : ℂ → ℂ) (p : ℂ[X]) : Prop :=
  ∃ g : ℂ → ℂ, ContinuousAt g 1 ∧
    ∀ᶠ t in l, f t=p.eval (t-1)+(t-1)^d*g t

abbrev JetApproxAlongPL (l : Filter ℂ) (d : ℕ) (f : ℂ → ℂ) (J : Jet) : Prop := JetApproxAlong l d f (zp J)

namespace JetApproxAlong
variable {l : Filter ℂ}
variable {d e : ℕ} {f g : ℂ → ℂ} {p q : ℂ[X]}

/-- Polynomial functions have a zero remainder at every order. -/
theorem polynomial (d : ℕ) (p : ℂ[X]) : JetApproxAlong l d (fun t => p.eval (t-1)) p :=
  ⟨fun _ => 0,continuousAt_const,Eventually.of_forall (fun t => by simp)⟩

theorem congr (h : JetApproxAlong l d f p) (he : f =ᶠ[l] g) : JetApproxAlong l d g p := by
  obtain ⟨r,hr,hf⟩ := h
  refine ⟨r,hr,?_⟩
  filter_upwards [hf,he] with t ht he
  rwa [← he]

/-- Lowering jet precision multiplies the continuous remainder by a power. -/
theorem weaken (h : JetApproxAlong l d f p) (he : e ≤ d) : JetApproxAlong l e f p := by
  obtain ⟨r,hr,hf⟩ := h
  refine ⟨fun t => (t-1)^(d-e)*r t,by fun_prop,?_⟩
  filter_upwards [hf] with t ht
  rw [ht,← mul_assoc,← pow_add,show e+(d-e)=d by omega]

theorem add (hf : JetApproxAlong l d f p) (hg : JetApproxAlong l d g q) :
    JetApproxAlong l d (fun t => f t+g t) (p+q) := by
  obtain ⟨r,hr,hf⟩ := hf
  obtain ⟨s,hs,hg⟩ := hg
  refine ⟨fun t => r t+s t,hr.add hs,?_⟩
  filter_upwards [hf,hg] with t ht hu
  rw [ht,hu,Polynomial.eval_add]
  ring

theorem neg (hf : JetApproxAlong l d f p) : JetApproxAlong l d (fun t => -f t) (-p) := by
  obtain ⟨r,hr,hf⟩ := hf
  refine ⟨fun t => -r t,hr.neg,?_⟩
  filter_upwards [hf] with t ht
  rw [ht,Polynomial.eval_neg]
  ring

theorem sub (hf : JetApproxAlong l d f p) (hg : JetApproxAlong l d g q) :
    JetApproxAlong l d (fun t => f t-g t) (p-q) := by
  simpa only [sub_eq_add_neg] using JetApproxAlong.add hf hg.neg

theorem scale (c : ℂ) (hf : JetApproxAlong l d f p) :
    JetApproxAlong l d (fun t => c*f t) (Polynomial.C c*p) := by
  obtain ⟨r,hr,hf⟩ := hf
  refine ⟨fun t => c*r t,continuousAt_const.mul hr,?_⟩
  filter_upwards [hf] with t ht
  rw [ht,Polynomial.eval_mul,Polynomial.eval_C]
  ring

theorem mul (hf : JetApproxAlong l d f p) (hg : JetApproxAlong l d g q) :
    JetApproxAlong l d (fun t => f t*g t) (p*q) := by
  obtain ⟨r,hr,hf⟩ := hf
  obtain ⟨s,hs,hg⟩ := hg
  refine ⟨fun t => p.eval (t-1)*s t+q.eval (t-1)*r t+(t-1)^d*r t*s t,by fun_prop,?_⟩
  filter_upwards [hf,hg] with t ht hu
  rw [ht,hu,Polynomial.eval_mul]
  ring

/-- Changing the polynomial by a degree-d multiple preserves the approximation. -/
theorem of_remainder (hf : JetApproxAlong l d f p) (hq : Polynomial.X^d ∣ p-q) :
    JetApproxAlong l d f q := by
  obtain ⟨a,ha⟩ := hq
  have hp : p=q+Polynomial.X^d*a := by linear_combination ha
  obtain ⟨r,hr,hf⟩ := hf
  refine ⟨fun t => a.eval (t-1)+r t,by fun_prop,?_⟩
  filter_upwards [hf] with t ht
  rw [ht,hp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X]
  ring

/-- Positive jet precision gives the actual punctured limit. -/
theorem tendsto (hf : JetApproxAlong l d f p) (hd : 0 < d) (hl : l ≤ 𝓝[≠] (1 : ℂ)) :
    Tendsto f (l) (𝓝 (p.eval 0)) := by
  obtain ⟨r,hr,hf⟩ := hf
  have hc : ContinuousAt (fun t => p.eval (t-1)+(t-1)^d*r t) 1 := by fun_prop
  have hlim : Tendsto (fun t => p.eval (t-1)+(t-1)^d*r t)
      (l) (𝓝 (p.eval ((1 : ℂ)-1)+((1 : ℂ)-1)^d*r 1)) :=
    hc.tendsto.mono_left (hl.trans nhdsWithin_le_nhds)
  have he : p.eval ((1 : ℂ)-1)+((1 : ℂ)-1)^d*r 1=p.eval 0 := by
    simp [Nat.ne_of_gt hd]
  rw [he] at hlim
  exact hlim.congr' (hf.mono fun t ht => ht.symm)

/-- When the actual function is continuous at the special fiber, its value is
exactly the certified constant coefficient. -/
theorem value (hf : JetApproxAlong l d f p) (hd : 0 < d) (hc : ContinuousAt f 1)
    [NeBot l] (hl : l ≤ 𝓝[≠] (1 : ℂ)) :
    f 1=p.eval 0 :=
  tendsto_nhds_unique (hc.tendsto.mono_left (hl.trans nhdsWithin_le_nhds)) (hf.tendsto hd hl)

end JetApproxAlong

/-- Restrict a proved punctured jet to any approach filter. -/
theorem JetApprox.along {l : Filter ℂ} {d : ℕ} {f : ℂ → ℂ} {p : ℂ[X]}
    (hf : JetApprox d f p) (hl : l ≤ 𝓝[≠] (1 : ℂ)) : JetApproxAlong l d f p := by
  obtain ⟨r,hr,h⟩ := hf
  exact ⟨r,hr,h.filter_mono hl⟩

/-- The actual denominator factors by the certified pivot order, and its
remaining continuous factor has the certified nonzero value at the fiber. -/
theorem JetApproxAlong.pivot_factor {l : Filter ℂ} {d v : ℕ} {den : ℂ → ℂ} {D : ℂ[X]}
    (hl : l ≤ 𝓝[≠] (1 : ℂ)) (hden : JetApproxAlong l d den D) (hv : v < d)
    (hbefore : ∀ i < v, D.coeff i=0) :
    ∃ u : ℂ → ℂ, ContinuousAt u 1 ∧ u 1=D.coeff v ∧
      ∀ᶠ t in l, den t=(t-1)^v*u t := by
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
theorem JetApproxAlong.cancel_pivot {l : Filter ℂ} {d v : ℕ} {den f : ℂ → ℂ} {D J : ℂ[X]}
    (hl : l ≤ 𝓝[≠] (1 : ℂ)) (hden : JetApproxAlong l d den D) (hv : v < d)
    (hbefore : ∀ i < v, D.coeff i=0) (hpivot : D.coeff v≠0)
    (herr : JetApproxAlong l d (fun t => den t*(f t-J.eval (t-1))) 0) :
    JetApproxAlong l (d-v) f J := by
  obtain ⟨u,hu,hu1,hden⟩ := JetApproxAlong.pivot_factor hl hden hv hbefore
  have hu0 : u 1≠0 := by rwa [hu1]
  obtain ⟨r,hr,herr⟩ := herr
  refine ⟨fun t => r t/u t,hr.div hu hu0,?_⟩
  have hun : ∀ᶠ t in l, u t≠0 :=
    (hu.eventually_ne hu0).filter_mono (hl.trans nhdsWithin_le_nhds)
  have htn0 : ∀ᶠ t in 𝓝[≠] (1 : ℂ), t≠1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using ht
  have htn : ∀ᶠ t in l, t≠1 := htn0.filter_mono hl
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
