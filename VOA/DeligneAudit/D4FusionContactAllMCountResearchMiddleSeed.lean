import VOA.DeligneAudit.D4FusionContactAllMCountResearchMiddle

/-! # The actual grouped-seed error has only strict middle modes -/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial
open BoundaryPair

noncomputable section

variable {m : ℕ} (b : BoundaryPair m)

def middleIndices : Finset (ℕ × ℕ) :=
  ((Finset.antidiagonal (b.lower.val+b.top.val)).erase (b.lower.val,b.top.val)).erase
    (b.top.val,b.lower.val)

theorem middleSeed_eq_sum : middleSeed b = (1/2:ℂ) •
    ∑ x ∈ middleIndices b, modeX m 0 x.1 * modeX m 0 x.2 := by
  let S := Finset.antidiagonal (b.lower.val+b.top.val)
  let f := fun x : ℕ × ℕ => modeX m 0 x.1 * modeX m 0 x.2
  have h0 : (b.lower.val,b.top.val) ∈ S := by simp [S]
  have h1 : (b.top.val,b.lower.val) ∈ S.erase (b.lower.val,b.top.val) := by
    have hlt := b.lt
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      have := congrArg Prod.fst he
      omega
    · simp [S,Nat.add_comm]
  have hs0 := Finset.add_sum_erase S f h0
  have hs1 := Finset.add_sum_erase (S.erase (b.lower.val,b.top.val)) f h1
  have he : MvPolynomial.rename b.embed twoSeed = f (b.lower.val,b.top.val) := by
    simp [twoSeed,embed,embedMode,f,modeX,b.lower.isLt,b.top.isLt]
  rw [middleSeed,groupedSeed_whole,he]
  simp only [pow_two,PowerSeries.coeff_mul,Polynomial.AllM.current,
    PowerSeries.coeff_mk]
  change (1/2:ℂ) • (∑ x ∈ S, f x) - f (b.lower.val,b.top.val) =
    (1/2:ℂ) • ∑ x ∈ middleIndices b, f x
  rw [← hs0,← hs1]
  have hf : f (b.top.val,b.lower.val) = f (b.lower.val,b.top.val) := mul_comm _ _
  rw [hf]
  change (1/2:ℂ) • (f (b.lower.val,b.top.val) +
    (f (b.lower.val,b.top.val) + ∑ x ∈ middleIndices b, f x)) -
      f (b.lower.val,b.top.val) = (1/2:ℂ) • ∑ x ∈ middleIndices b, f x
  module

theorem middleSeed_mem : middleSeed b ∈ middleSpan b := by
  rw [middleSeed_eq_sum]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro x hx
  have hmem := hx
  simp only [middleIndices,Finset.mem_erase,Finset.mem_antidiagonal] at hmem
  have hn0 : ¬ (x.1 = b.lower.val ∧ x.2 = b.top.val) := by
    intro he
    exact hmem.2.1 (Prod.ext he.1 he.2)
  have hn1 : ¬ (x.1 = b.top.val ∧ x.2 = b.lower.val) := by
    intro he
    exact hmem.1 (Prod.ext he.1 he.2)
  by_cases h0 : x.1 < m
  · by_cases h1 : x.2 < m
    · have hlast := b.last
      have hlt := b.lt
      have hi : b.lower.val < x.1 ∧ x.1 < b.top.val := by omega
      have hj : b.lower.val < x.2 ∧ x.2 < b.top.val := by omega
      simp only [modeX,dif_pos h0,dif_pos h1]
      exact middle_product_mem b {
        left := (0,⟨x.1,h0⟩), right := (0,⟨x.2,h1⟩),
        left_lower := hi.1, left_upper := hi.2,
        right_lower := hj.1, right_upper := hj.2, mode_sum := hmem.2.2}
    · simp only [modeX,dif_neg h1,mul_zero]
      exact (middleSpan b).zero_mem
  · simp only [modeX,dif_neg h0,zero_mul]
    exact (middleSpan b).zero_mem

end
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch

#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.middleSeed_mem
