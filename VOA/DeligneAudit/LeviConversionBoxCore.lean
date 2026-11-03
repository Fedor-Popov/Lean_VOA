import VOA.DeligneAudit.LeviConversion

/-! The top-contraction consequence of Lemma C for complex-linear submodules. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

variable {A V : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup V]
  [Module A V] [Module ℂ V]

/-- Every positional choice partitions the input letters. -/
theorem choices_length {ι : Type*} (xs : List ι) (p : List ι × List ι)
    (hp : p ∈ choices xs) : p.1.length + p.2.length = xs.length := by
  induction xs generalizing p with
  | nil =>
    simp [choices] at hp
    rcases hp with rfl
    rfl
  | cons x xs ih =>
    simp only [choices, List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      simp only [List.length_cons]
      have h := ih q hq
      omega
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      simp only [List.length_cons]
      have h := ih q hq
      omega

/-- A lower Wick term has strictly more uncontracted `a` letters. -/
theorem lowerTerm_more_a_letters (xs : List ℕ) (k : ℕ)
    (p : List ℕ × List ℕ) (hp : p ∈ choices (xs ++ List.replicate k 0))
    (hpk : p.2.length < k) : xs.length < p.1.length := by
  have h := choices_length (xs ++ List.replicate k 0) p hp
  simp only [List.length_append, List.length_replicate] at h
  omega

/-- Pointwise absorption of every lower Wick term implies absorption of their sum. -/
theorem lowerSum_mem_of_higher_terms (f a b : ℕ → A)
    (k s : ℕ) (xs : List ℕ) (R : A) (v : V) (N : Submodule ℂ V)
    (hHigher : ∀ p ∈ choices xs, p.2.length < k →
      conversionTerm f a b k s p • (R • v) ∈ N) :
    lowerSum f a b k s xs • (R • v) ∈ N := by
  rw [lowerSum, List.sum_smul]
  apply N.list_sum_mem
  intro w hw
  simp only [List.map_map, Function.comp_def] at hw
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
  by_cases h : p.2.length < k
  · simpa [h] using hHigher p hp h
  · simp [h]

/-- Lemma C modulo a complex-linear higher-term space. -/
theorem topSum_mem_higher_linear (f a b : ℕ → A)
    (hfa : ∀ i j, f i * a j - a j * f i = b (i + j))
    (hfb : ∀ i j, f i * b j = b j * f i)
    (hab : ∀ i j, a i * b j = b j * a i)
    (k s : ℕ) (xs : List ℕ) (R : A) (v : V)
    (hRf : ∀ i, R * f i = f i * R)
    (hkill : PowerSeries.coeff s (fCurrent f ^ k) • v = 0)
    (hscalar : ∀ c : ℂ, ∀ w : V, (algebraMap ℂ A c) • w = c • w)
    (N : Submodule ℂ V)
    (hlower : lowerSum f a b k s xs • (R • v) ∈ N) :
    topSum a b k s xs • (R • v) ∈ N := by
  let c : ℂ := (-1 : ℂ) ^ k * (k.factorial : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))
  have hmap : algebraMap ℂ A c = (-1 : A) ^ k * (k.factorial : A) := by
    simp [c, map_mul, map_pow, map_neg, map_natCast]
  have h := lemmaC f a b hfa hfb hab k s xs R v hRf hkill
  have heq : (algebraMap ℂ A c) • (topSum a b k s xs • (R • v)) =
      -(lowerSum f a b k s xs • (R • v)) := by
    simpa only [hmap, mul_smul] using h
  have hmem : c • (topSum a b k s xs • (R • v)) ∈ N := by
    rw [← hscalar c, heq]
    exact N.neg_mem hlower
  have hmem' := N.smul_mem c⁻¹ hmem
  simpa [smul_smul, inv_mul_cancel₀ hc] using hmem'

end
end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.topSum_mem_higher_linear
#print axioms VOA.DeligneAudit.LeviConversion.lowerSum_mem_of_higher_terms
#print axioms VOA.DeligneAudit.LeviConversion.lowerTerm_more_a_letters
