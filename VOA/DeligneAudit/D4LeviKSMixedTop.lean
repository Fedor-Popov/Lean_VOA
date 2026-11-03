import VOA.DeligneAudit.D4LeviKSMixedWick

/-! Separation of full and partial contractions in the mixed Wick relations. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def mixedTop (a b : ℕ → Module.End ℂ V)
    (k s : ℕ) (xs : List ℕ) (B : PowerSeries (Module.End ℂ V)) :
    Module.End ℂ V :=
  ∑ q ∈ Finset.antidiagonal s,
    topSum a b k q.1 xs * PowerSeries.coeff q.2 B

noncomputable def mixedLower (f a b : ℕ → Module.End ℂ V)
    (k s : ℕ) (xs : List ℕ) (B : PowerSeries (Module.End ℂ V)) :
    Module.End ℂ V :=
  ∑ q ∈ Finset.antidiagonal s,
    lowerSum f a b k q.1 xs * PowerSeries.coeff q.2 B

/-- The full contractions equal the negative of the partial contractions,
    with the nonzero Wick factorial retained explicitly. -/
theorem mixed_top_eq_lower (w : V) (f a b : ℕ → Module.End ℂ V)
    (hfa : ∀ i j, f i * a j - a j * f i = b (i + j))
    (hfb : ∀ i j, f i * b j = b j * f i)
    (hab : ∀ i j, a i * b j = b j * a i)
    (k s : ℕ) (xs : List ℕ) (B : PowerSeries (Module.End ℂ V))
    (hkill : (PowerSeries.coeff s (fCurrent f ^ k * B)) w = 0) :
    (((-1 : Module.End ℂ V) ^ k * (k.factorial : Module.End ℂ V)) *
      mixedTop a b k s xs B) w = -(mixedLower f a b k s xs B) w := by
  have h := mixed_wick_zero w f a b hfa hfb hab k s xs B hkill
  have hsum :
      (∑ q ∈ Finset.antidiagonal s,
        ((choices xs).map (conversionTerm f a b k q.1)).sum *
          PowerSeries.coeff q.2 B) =
      ((-1 : Module.End ℂ V) ^ k * (k.factorial : Module.End ℂ V)) *
          mixedTop a b k s xs B + mixedLower f a b k s xs B := by
    simp_rw [conversion_sum_split, add_mul, mul_assoc]
    rw [Finset.sum_add_distrib]
    simp only [mixedTop, mixedLower, Finset.mul_sum]
  rw [hsum, LinearMap.add_apply] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Higher-key absorption of partial contractions implies the graded mixed
    relation for the full contractions. -/
theorem mixed_top_mem_of_lower (w : V) (f a b : ℕ → Module.End ℂ V)
    (hfa : ∀ i j, f i * a j - a j * f i = b (i + j))
    (hfb : ∀ i j, f i * b j = b j * f i)
    (hab : ∀ i j, a i * b j = b j * a i)
    (k s : ℕ) (xs : List ℕ) (B : PowerSeries (Module.End ℂ V))
    (hkill : (PowerSeries.coeff s (fCurrent f ^ k * B)) w = 0)
    (N : Submodule ℂ V) (hlower : mixedLower f a b k s xs B w ∈ N) :
    mixedTop a b k s xs B w ∈ N := by
  let c : ℂ := (-1 : ℂ) ^ k * (k.factorial : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))
  have heq := mixed_top_eq_lower w f a b hfa hfb hab k s xs B hkill
  have hmap : algebraMap ℂ (Module.End ℂ V) c =
      (-1 : Module.End ℂ V) ^ k * (k.factorial : Module.End ℂ V) := by
    simp [c, map_mul, map_pow, map_neg, map_natCast]
  have hsmul : c • mixedTop a b k s xs B w =
      -(mixedLower f a b k s xs B w) := by
    rw [← hmap, Module.End.mul_apply] at heq
    simpa only [show ∀ v : V,
      (algebraMap ℂ (Module.End ℂ V) c) v = c • v from by
        intro v
        simp] using heq
  have hm : c • mixedTop a b k s xs B w ∈ N := by
    rw [hsmul]
    exact N.neg_mem hlower
  have hm' := N.smul_mem c⁻¹ hm
  simpa [smul_smul, inv_mul_cancel₀ hc] using hm'

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.mixed_top_eq_lower
#print axioms VOA.DeligneAudit.D4Levi.mixed_top_mem_of_lower
