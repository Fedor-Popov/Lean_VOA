import VOA.DeligneAudit.LeviConversionTop

/-! The top contraction lies in any submodule that absorbs the lower terms. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

variable {A V : Type*} [Ring A] [AddCommGroup V] [Module A V]

/-- The algebraic quotient consequence of Lemma C. The invertibility input is
automatic in a complex algebra; the theorem itself works over any ring. -/
theorem topSum_mem_higher (f a b : ℕ → A)
    (hfa : ∀ i j, f i * a j - a j * f i = b (i + j))
    (hfb : ∀ i j, f i * b j = b j * f i)
    (hab : ∀ i j, a i * b j = b j * a i)
    (k s : ℕ) (xs : List ℕ) (R : A) (v : V)
    (hRf : ∀ i, R * f i = f i * R)
    (hkill : PowerSeries.coeff s (fCurrent f ^ k) • v = 0)
    (N : Submodule A V)
    (hlower : lowerSum f a b k s xs • (R • v) ∈ N)
    (hinv : ∃ d : A, d * ((-1 : A) ^ k * (k.factorial : A)) = 1) :
    topSum a b k s xs • (R • v) ∈ N := by
  obtain ⟨d, hd⟩ := hinv
  have h := lemmaC f a b hfa hfb hab k s xs R v hRf hkill
  have hs : (((-1 : A) ^ k * (k.factorial : A)) * topSum a b k s xs) •
      (R • v) ∈ N := by
    rw [h]
    exact N.neg_mem hlower
  have hdmem := N.smul_mem d hs
  have heq : d • (((-1 : A) ^ k * (k.factorial : A) *
      topSum a b k s xs) • (R • v)) = topSum a b k s xs • (R • v) := by
    rw [← mul_smul, ← mul_assoc, hd, one_mul]
  exact heq ▸ hdmem

/-- In a complex algebra the factorial coefficient has a left inverse. -/
theorem topScalar_leftInverse [Algebra ℂ A] (k : ℕ) :
    ∃ d : A, d * ((-1 : A) ^ k * (k.factorial : A)) = 1 := by
  let c : ℂ := (-1 : ℂ) ^ k * (k.factorial : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))
  refine ⟨algebraMap ℂ A c⁻¹, ?_⟩
  have hmap : algebraMap ℂ A c = (-1 : A) ^ k * (k.factorial : A) := by
    simp [c, map_mul, map_pow, map_neg, map_natCast]
  rw [← hmap, ← map_mul, inv_mul_cancel₀ hc, map_one]

/-- The top conversion sum belongs to the higher submodule over any complex algebra. -/
theorem topSum_mem_higher_complex [Algebra ℂ A] (f a b : ℕ → A)
    (hfa : ∀ i j, f i * a j - a j * f i = b (i + j))
    (hfb : ∀ i j, f i * b j = b j * f i)
    (hab : ∀ i j, a i * b j = b j * a i)
    (k s : ℕ) (xs : List ℕ) (R : A) (v : V)
    (hRf : ∀ i, R * f i = f i * R)
    (hkill : PowerSeries.coeff s (fCurrent f ^ k) • v = 0)
    (N : Submodule A V)
    (hlower : lowerSum f a b k s xs • (R • v) ∈ N) :
    topSum a b k s xs • (R • v) ∈ N :=
  topSum_mem_higher f a b hfa hfb hab k s xs R v hRf hkill N hlower
    (topScalar_leftInverse k)

end
end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.topSum_mem_higher
#print axioms VOA.DeligneAudit.LeviConversion.topSum_mem_higher_complex
