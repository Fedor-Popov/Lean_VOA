import VOA.DeligneAudit.DeligneFusionCVBound
import Mathlib.Data.Nat.Choose.Sum

/-!
# CV relations with a lower cutoff on current modes

`QFrom F p r s` is the coefficient of degree `s` in the `r`th power of
the current series with modes below `p` deleted. The usual CV relations
imply the same vanishing region for this series. This is the cutoff step
used before SRK equations (8.24)--(8.26).

The normalization here uses ordinary powers, as does `CVsl2.Q`; multiplying
by the nonzero scalar `r!` converts the divided-power convention.
-/

namespace VOA.DeligneAudit.CVsl2

open VOA.DeligneAudit.CVPart

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Current modes with all indices below the cutoff deleted. -/
def fromMode (F : ℕ → Module.End ℂ V) (p : ℕ) (k : ℕ) : Module.End ℂ V :=
  if p ≤ k then F k else 0

/-- Ordinary-power coefficient with a lower cutoff on every current mode. -/
def QFrom (F : ℕ → Module.End ℂ V) (p r s : ℕ) : Module.End ℂ V :=
  Q (fromMode F p) r s

/-- Two current series commute when their coefficients commute pairwise. -/
theorem current_series_commute {F G : ℕ → Module.End ℂ V}
    (hFG : ∀ i j, F i * G j = G j * F i) :
    Commute (Garland.Fs F) (Garland.Fs G) := by
  change Garland.Fs F * Garland.Fs G = Garland.Fs G * Garland.Fs F
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_mul, Garland.Fs, PowerSeries.coeff_mk]
  rw [← Finset.Nat.sum_antidiagonal_swap
    (f := fun x : ℕ × ℕ => G x.1 * F x.2)]
  exact Finset.sum_congr rfl fun x _ => hFG x.1 x.2

/-- CV's unshifted relations imply the relations with every mode at least `p`. -/
theorem cvrel_cutoff {F : ℕ → Module.End ℂ V}
    (hFF : ∀ i j, F i * F j = F j * F i)
    {ξ : List ℕ} {y : V} (hR : CVRel F ξ y) (p r s : ℕ) (hr : 1 ≤ r)
    (hrs : 1 + r * p + T p ξ ≤ s + r) : QFrom F p r s y = 0 := by
  classical
  by_cases hp : p = 0
  · subst p
    have heq : fromMode F 0 = F := by ext k; simp [fromMode]
    simpa only [QFrom, heq] using hR r s 0 hr hrs
  have hp1 : 1 ≤ p := by omega
  let L : ℕ → Module.End ℂ V := fun k => if k < p then -F k else 0
  have hLL : ∀ i j, L i * L j = L j * L i := by
    intro i j
    by_cases hi : i < p <;> by_cases hj : j < p
    · simpa only [L, if_pos hi, if_pos hj, neg_mul, mul_neg, neg_neg] using hFF i j
    · simp [L, hi, hj]
    · simp [L, hi, hj]
    · simp [L, hi, hj]
  have hLF : ∀ i j, L i * F j = F j * L i := by
    intro i j
    by_cases hi : i < p
    · simpa only [L, if_pos hi, neg_mul, mul_neg, neg_inj] using hFF i j
    · simp [L, hi]
  have hfrom : Garland.Fs (fromMode F p) = Garland.Fs L + Garland.Fs F := by
    apply PowerSeries.ext
    intro k
    simp only [Garland.Fs, PowerSeries.coeff_mk, map_add, fromMode, L]
    by_cases hk : p ≤ k
    · simp [hk, show ¬k < p by omega]
    · simp [hk, show k < p by omega]
  have hterm (m : ℕ × ℕ) (hm : m ∈ Finset.antidiagonal r) :
      (PowerSeries.coeff s (Garland.Fs L ^ m.1 * Garland.Fs F ^ m.2)) y = 0 := by
    have hmr : m.1 + m.2 = r := Finset.mem_antidiagonal.mp hm
    rw [PowerSeries.coeff_mul, LinearMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun n hn => ?_
    have hns : n.1 + n.2 = s := Finset.mem_antidiagonal.mp hn
    rw [Module.End.mul_apply]
    by_cases hq : (p - 1) * m.1 < n.1
    · change Q L m.1 n.1 _ = 0
      exact Q_high hLL (fun k hk => by simp [L, show ¬k < p by omega]) m.1 n.1 hq
    have hmul : (p - 1) * m.1 + m.1 = m.1 * p := by
      rw [mul_comm (p - 1), ← Nat.mul_succ]
      congr 1
      omega
    have hreg : 1 + m.1 * p + m.2 * p + T p ξ ≤ n.1 + n.2 + m.1 + m.2 := by
      calc
        _ = 1 + r * p + T p ξ := by rw [← hmr, Nat.add_mul]; omega
        _ ≤ s + r := hrs
        _ = _ := by omega
    by_cases hb : m.2 = 0
    · have hn2 : n.2 ≠ 0 := by omega
      simp only [hb, pow_zero, PowerSeries.coeff_one, if_neg hn2, LinearMap.zero_apply,
        map_zero]
    · have hcv : Q F m.2 n.2 y = 0 := hR m.2 n.2 p (by omega) (by omega)
      change (PowerSeries.coeff n.1 (Garland.Fs L ^ m.1)) (Q F m.2 n.2 y) = 0
      rw [hcv, map_zero]
  have hpow := (current_series_commute hLF).add_pow' r
  rw [← hfrom] at hpow
  have hcoeff := congrArg
    (fun P : PowerSeries (Module.End ℂ V) => (PowerSeries.coeff s P) y) hpow
  simp only [map_sum, map_nsmul, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply] at hcoeff
  change (PowerSeries.coeff s (Garland.Fs (fromMode F p) ^ r)) y = 0
  rw [hcoeff]
  exact Finset.sum_eq_zero fun m hm => by rw [hterm m hm]; simp

end

end VOA.DeligneAudit.CVsl2

#print axioms VOA.DeligneAudit.CVsl2.cvrel_cutoff
