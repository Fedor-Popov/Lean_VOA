import VOA.Classification.COne.OrbIcoWJetAlgebra
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Topology.Algebra.Polynomial

/-! Continuous-remainder jets on a punctured neighborhood of the resonant point.
These approximations do not assume existence of derivatives of the actual
Ward coefficients. They retain an explicit continuous remainder. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoW
open OrbOdd Polynomial Filter Topology

/-- A polynomial jet through order d-1 with a continuous local remainder. -/
def JetApprox (d : ℕ) (f : ℂ → ℂ) (p : ℂ[X]) : Prop :=
  ∃ g : ℂ → ℂ, ContinuousAt g 1 ∧
    ∀ᶠ t in 𝓝[≠] (1 : ℂ), f t=p.eval (t-1)+(t-1)^d*g t

abbrev JetApproxPL (d : ℕ) (f : ℂ → ℂ) (J : Jet) : Prop := JetApprox d f (zp J)

namespace JetApprox
variable {d e : ℕ} {f g : ℂ → ℂ} {p q : ℂ[X]}

/-- Polynomial functions have a zero remainder at every order. -/
theorem polynomial (d : ℕ) (p : ℂ[X]) : JetApprox d (fun t => p.eval (t-1)) p :=
  ⟨fun _ => 0,continuousAt_const,Eventually.of_forall (fun t => by simp)⟩

theorem congr (h : JetApprox d f p) (he : f =ᶠ[𝓝[≠] (1 : ℂ)] g) : JetApprox d g p := by
  obtain ⟨r,hr,hf⟩ := h
  refine ⟨r,hr,?_⟩
  filter_upwards [hf,he] with t ht he
  rwa [← he]

/-- Lowering jet precision multiplies the continuous remainder by a power. -/
theorem weaken (h : JetApprox d f p) (he : e ≤ d) : JetApprox e f p := by
  obtain ⟨r,hr,hf⟩ := h
  refine ⟨fun t => (t-1)^(d-e)*r t,by fun_prop,?_⟩
  filter_upwards [hf] with t ht
  rw [ht,← mul_assoc,← pow_add,show e+(d-e)=d by omega]

theorem add (hf : JetApprox d f p) (hg : JetApprox d g q) :
    JetApprox d (fun t => f t+g t) (p+q) := by
  obtain ⟨r,hr,hf⟩ := hf
  obtain ⟨s,hs,hg⟩ := hg
  refine ⟨fun t => r t+s t,hr.add hs,?_⟩
  filter_upwards [hf,hg] with t ht hu
  rw [ht,hu,Polynomial.eval_add]
  ring

theorem neg (hf : JetApprox d f p) : JetApprox d (fun t => -f t) (-p) := by
  obtain ⟨r,hr,hf⟩ := hf
  refine ⟨fun t => -r t,hr.neg,?_⟩
  filter_upwards [hf] with t ht
  rw [ht,Polynomial.eval_neg]
  ring

theorem sub (hf : JetApprox d f p) (hg : JetApprox d g q) :
    JetApprox d (fun t => f t-g t) (p-q) := by
  simpa only [sub_eq_add_neg] using JetApprox.add hf hg.neg

theorem scale (c : ℂ) (hf : JetApprox d f p) :
    JetApprox d (fun t => c*f t) (Polynomial.C c*p) := by
  obtain ⟨r,hr,hf⟩ := hf
  refine ⟨fun t => c*r t,continuousAt_const.mul hr,?_⟩
  filter_upwards [hf] with t ht
  rw [ht,Polynomial.eval_mul,Polynomial.eval_C]
  ring

theorem mul (hf : JetApprox d f p) (hg : JetApprox d g q) :
    JetApprox d (fun t => f t*g t) (p*q) := by
  obtain ⟨r,hr,hf⟩ := hf
  obtain ⟨s,hs,hg⟩ := hg
  refine ⟨fun t => p.eval (t-1)*s t+q.eval (t-1)*r t+(t-1)^d*r t*s t,by fun_prop,?_⟩
  filter_upwards [hf,hg] with t ht hu
  rw [ht,hu,Polynomial.eval_mul]
  ring

/-- Changing the polynomial by a degree-d multiple preserves the approximation. -/
theorem of_remainder (hf : JetApprox d f p) (hq : Polynomial.X^d ∣ p-q) :
    JetApprox d f q := by
  obtain ⟨a,ha⟩ := hq
  have hp : p=q+Polynomial.X^d*a := by linear_combination ha
  obtain ⟨r,hr,hf⟩ := hf
  refine ⟨fun t => a.eval (t-1)+r t,by fun_prop,?_⟩
  filter_upwards [hf] with t ht
  rw [ht,hp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X]
  ring

/-- Positive jet precision gives the actual punctured limit. -/
theorem tendsto (hf : JetApprox d f p) (hd : 0 < d) :
    Tendsto f (𝓝[≠] (1 : ℂ)) (𝓝 (p.eval 0)) := by
  obtain ⟨r,hr,hf⟩ := hf
  have hc : ContinuousAt (fun t => p.eval (t-1)+(t-1)^d*r t) 1 := by fun_prop
  have hlim : Tendsto (fun t => p.eval (t-1)+(t-1)^d*r t)
      (𝓝[≠] (1 : ℂ)) (𝓝 (p.eval ((1 : ℂ)-1)+((1 : ℂ)-1)^d*r 1)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have he : p.eval ((1 : ℂ)-1)+((1 : ℂ)-1)^d*r 1=p.eval 0 := by
    simp [Nat.ne_of_gt hd]
  rw [he] at hlim
  exact hlim.congr' (hf.mono fun t ht => ht.symm)

/-- When the actual function is continuous at the special fiber, its value is
exactly the certified constant coefficient. -/
theorem value (hf : JetApprox d f p) (hd : 0 < d) (hc : ContinuousAt f 1) :
    f 1=p.eval 0 :=
  tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) (hf.tendsto hd)

end JetApprox

/-- Truncating a rational coefficient list changes only order P+1 and higher. -/
theorem jetCut_remainder (P : ℕ) (J : Jet) :
    Polynomial.X^(P+1) ∣ zp J-zp (jetCut P J) := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro n hn
  rw [Polynomial.coeff_sub,coeff_jetCut P J (by omega),sub_self]

/-- Exact list truncation therefore preserves its continuous-remainder jet. -/
theorem JetApproxPL.cut {P : ℕ} {f : ℂ → ℂ} {J : Jet}
    (hf : JetApproxPL (P+1) f J) : JetApproxPL (P+1) f (jetCut P J) :=
  hf.of_remainder (jetCut_remainder P J)

theorem JetApproxPL.add {P : ℕ} {f g : ℂ → ℂ} {a b : Jet}
    (hf : JetApproxPL (P+1) f a) (hg : JetApproxPL (P+1) g b) :
    JetApproxPL (P+1) (fun t => f t+g t) (jetAdd P a b) := by
  apply JetApproxPL.cut
  change JetApprox (P+1) (fun t => f t+g t) (zp (paddL a b))
  rw [zp_paddL]
  exact JetApprox.add hf hg

theorem JetApproxPL.mul {P : ℕ} {f g : ℂ → ℂ} {a b : Jet}
    (hf : JetApproxPL (P+1) f a) (hg : JetApproxPL (P+1) g b) :
    JetApproxPL (P+1) (fun t => f t*g t) (jetMul P a b) := by
  apply JetApproxPL.cut
  change JetApprox (P+1) (fun t => f t*g t) (zp (pmulL a b))
  rw [zp_pmulL]
  exact JetApprox.mul hf hg

end VOA.Classification.COne.OrbIcoW
