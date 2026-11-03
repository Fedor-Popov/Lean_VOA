import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleMono
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! Whole polynomial/current gradings for the actual sparse D4 operators.
All degrees are integral, so lowering C degree needs no truncated subtraction. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
noncomputable section

section General
variable {K σ : Type*} [CommRing K]

theorem graded_deriv_sum [Fintype σ] (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    (p : MvPolynomial σ K) :
    D p = ∑ i, D (MvPolynomial.X i) * MvPolynomial.pderiv i p := by
  classical
  have he : D = ∑ i, D (MvPolynomial.X i) • MvPolynomial.pderiv i := by
    apply MvPolynomial.derivation_ext
    intro j
    change D (MvPolynomial.X j) = (Derivation.coeFnAddMonoidHom
      (∑ i, D (MvPolynomial.X i) • MvPolynomial.pderiv i)) (MvPolynomial.X j)
    rw [map_sum,Finset.sum_apply]
    simp [Derivation.smul_apply,smul_eq_mul,MvPolynomial.pderiv_X,Pi.single_apply]
  conv_lhs => rw [he]
  change (Derivation.coeFnAddMonoidHom
    (∑ i, D (MvPolynomial.X i) • MvPolynomial.pderiv i)) p = _
  rw [map_sum,Finset.sum_apply]
  simp only [Derivation.coeFnAddMonoidHom_apply,Derivation.smul_apply,smul_eq_mul]

theorem graded_deriv [Finite σ] (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    (w : σ → ℤ) (δ : ℤ)
    (hX : ∀ i, (D (MvPolynomial.X i)).IsWeightedHomogeneous w (w i + δ))
    {p : MvPolynomial σ K} {n : ℤ} (hp : p.IsWeightedHomogeneous w n) :
    (D p).IsWeightedHomogeneous w (n + δ) := by
  letI := Fintype.ofFinite σ
  rw [graded_deriv_sum]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro i _
  have hd := hp.pderiv (i:= i) (show n-w i + w i = n by omega)
  convert (hX i).mul hd using 1
  omega

/-- A nonzero polynomial cannot have a larger degree for smaller variable weights. -/
theorem graded_compare {w v : σ → ℤ} (hw : ∀ i, w i ≤ v i)
    {p : MvPolynomial σ K} {n d : ℤ}
    (hp : p.IsWeightedHomogeneous w n) (hq : p.IsWeightedHomogeneous v d)
    (hne : p ≠ 0) : n ≤ d := by
  obtain ⟨e,he⟩ := MvPolynomial.exists_coeff_ne_zero hne
  rw [← hp he,← hq he]
  simp only [Finsupp.weight_apply,nsmul_eq_mul]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hw i) (Nat.cast_nonneg _))

theorem graded_negative_zero {w : σ → ℤ} (hw : ∀ i, 0 ≤ w i)
    {p : MvPolynomial σ K} {n : ℤ} (hp : p.IsWeightedHomogeneous w n) (hn : n < 0) : p = 0 := by
  classical
  by_contra hne
  have hz : p.IsWeightedHomogeneous (fun _ => (0:ℤ)) 0 := by
    intro e _
    simp [Finsupp.weight_apply]
  have hh := graded_compare hw hz hp hne
  omega

end General

section Series
variable {K σ : Type*} [CommRing K]

def affineSeriesGrade (w : σ → ℤ) (n t : ℤ)
    (f : PowerSeries (MvPolynomial σ K)) : Prop :=
  ∀ s, (PowerSeries.coeff s f).IsWeightedHomogeneous w (n + t*s)

theorem affineSeriesGrade_one (w : σ → ℤ) (t : ℤ) :
    affineSeriesGrade w 0 t (1 : PowerSeries (MvPolynomial σ K)) := by
  intro s
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · subst s
    simpa only [Nat.cast_zero,mul_zero,add_zero] using MvPolynomial.isWeightedHomogeneous_one K w
  · exact MvPolynomial.isWeightedHomogeneous_zero K w _

theorem affineSeriesGrade_mul {w : σ → ℤ} {n d t : ℤ}
    {f g : PowerSeries (MvPolynomial σ K)}
    (hf : affineSeriesGrade w n t f) (hg : affineSeriesGrade w d t g) :
    affineSeriesGrade w (n + d) t (f*g) := by
  intro s
  rw [PowerSeries.coeff_mul]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro x hx
  have he := Finset.mem_antidiagonal.mp hx
  convert (hf x.1).mul (hg x.2) using 1
  rw [← he,Nat.cast_add]
  ring

theorem affineSeriesGrade_pow {w : σ → ℤ} {n t : ℤ}
    {f : PowerSeries (MvPolynomial σ K)} (hf : affineSeriesGrade w n t f) (r : ℕ) :
    affineSeriesGrade w ((r:ℤ)*n) t (f^r) := by
  induction r with
  | zero => simpa only [pow_zero,Nat.cast_zero,zero_mul] using affineSeriesGrade_one w t
  | succ r ih =>
      rw [pow_succ]
      convert affineSeriesGrade_mul ih hf using 1
      push_cast
      ring
end Series

variable (K : Type*) [CommRing K]

def modeWeight (m : ℕ) (w : Fin 9 → ℤ) (t : ℤ) : Fin 9 × Fin m → ℤ := fun x => w x.1 + t*x.2.val

theorem mode_graded (m : ℕ) (w : Fin 9 → ℤ) (t : ℤ) (i : Fin 9) (s : ℕ) :
    (mode K m i s).IsWeightedHomogeneous (modeWeight m w t) (w i + t*s) := by
  by_cases hs : s < m
  · rw [mode,dif_pos hs]
    exact MvPolynomial.isWeightedHomogeneous_X K _ _
  · rw [mode,dif_neg hs]
    exact MvPolynomial.isWeightedHomogeneous_zero K _ _

theorem color_seed_graded (m : ℕ) (w : Fin 9 → ℤ) (t : ℤ) (c : Fin 9) (r s : ℕ) :
    (PowerSeries.coeff s (colorCurrent K m c^r)).IsWeightedHomogeneous
      (modeWeight m w t) ((r:ℤ)*w c + t*s) := by
  apply affineSeriesGrade_pow (n:= w c)
  intro s
  rw [colorCurrent,PowerSeries.coeff_mk]
  exact mode_graded K m w t c s

/-- A sparse color shift plus mode k shifts current degree by exactly k. -/
theorem deriv_graded (m : ℕ) (w : Fin 9 → ℤ) (t δ : ℤ) (a : Fin 18) (k : ℕ)
    (ha : ∀ i, coeff a i = 0 ∨ w (target a i) = w i + δ)
    {p : Ring K m} {n : ℤ} (hp : p.IsWeightedHomogeneous (modeWeight m w t) n) :
    (deriv K m a k p).IsWeightedHomogeneous (modeWeight m w t) (n + δ + t*k) := by
  have hh := graded_deriv (deriv K m a k) (modeWeight m w t) (δ + t*k) (fun x => ?_) hp
  · convert hh using 1
    ring
  · rw [deriv_X]
    rcases ha x.1 with hz | hw
    · rw [hz,zero_zsmul]
      exact MvPolynomial.isWeightedHomogeneous_zero K _ _
    · have h := (MvPolynomial.weightedHomogeneousSubmodule K (modeWeight m w t)
          (w (target a x.1) + t*(k + x.2.val))).smul_mem
          (coeff a x.1 : K) (mode_graded K m w t (target a x.1) (k + x.2.val))
      rw [Int.cast_smul_eq_zsmul K] at h
      change (coeff a x.1 • mode K m (target a x.1) (k + x.2.val)).IsWeightedHomogeneous _ _ at h
      convert h using 1
      simp only [modeWeight,hw]
      ring

end
#print axioms graded_compare
#print axioms color_seed_graded
#print axioms deriv_graded
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
