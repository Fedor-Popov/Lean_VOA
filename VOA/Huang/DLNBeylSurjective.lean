import VOA.Huang.DLNReduction

/-!
# Surjectivity of reduction `SL₂(ℤ) → SL₂(ℤ/N)`

An elementary proof (Shimura, *Introduction to the arithmetic theory of automorphic
functions*, Lemma 1.38): lift the bottom row to a coprime integral pair by shifting `d`
inside its residue class, complete it by Bézout, and correct the top row by a multiple
of the bottom row.
-/

namespace VOA.Huang.DLNBeyl

open VOA.Huang.DLN

/-- Shifting `d` inside its residue class modulo `N` makes it coprime to `c ≠ 0`, provided
no prime divides all three of `c`, `d`, `N`. -/
theorem exists_coprime_shift (c d N : ℕ) (hc : c ≠ 0)
    (h : ∀ p, p.Prime → p ∣ c → p ∣ d → ¬ p ∣ N) :
    ∃ k : ℕ, Nat.Coprime c (d + k * N) := by
  classical
  let ps : Finset ℕ := {p ∈ c.primeFactors | ¬ p ∣ d}
  refine ⟨ps.prod id, Nat.coprime_of_dvd ?_⟩
  intro p pp hpc hpn
  by_cases hpd : p ∣ d
  · have h' := Nat.dvd_sub hpn hpd
    rw [add_comm, Nat.add_sub_cancel] at h'
    rcases pp.dvd_mul.mp h' with h'' | h''
    · have ⟨q, hq, hq'⟩ := (pp.prime.dvd_finsetProd_iff id).mp h''
      rw [Finset.mem_filter, Nat.mem_primeFactors,
        ← (Nat.prime_dvd_prime_iff_eq pp hq.1.1).mp hq'] at hq
      exact hq.2 hpd
    · exact h p pp hpc hpd h''
  · have pps : p ∈ ps :=
      Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨pp, hpc, hc⟩, hpd⟩
    have h' := Nat.dvd_sub hpn ((Finset.dvd_prod_of_mem id pps).mul_right N)
    rw [Nat.add_sub_cancel] at h'
    exact hpd h'

/-- **Reduction modulo a positive integer is surjective on `SL₂`.** -/
theorem reduction_surjective (N : ℕ) [NeZero N] : Function.Surjective (reduction N) := by
  intro M
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have := M.2
    rwa [Matrix.det_fin_two] at this
  set a : ℕ := (M 0 0).val with ha
  set b : ℕ := (M 0 1).val with hb
  set c : ℕ := (M 1 0).val with hc
  set d : ℕ := (M 1 1).val with hd
  have hM00 : ((a : ℤ) : ZMod N) = M 0 0 := by simp [ha]
  have hM01 : ((b : ℤ) : ZMod N) = M 0 1 := by simp [hb]
  have hM10 : ((c : ℤ) : ZMod N) = M 1 0 := by simp [hc]
  have hM11 : ((d : ℤ) : ZMod N) = M 1 1 := by simp [hd]
  have hA : ((a : ℕ) : ZMod N) = M 0 0 := by simp [ha]
  have hB : ((b : ℕ) : ZMod N) = M 0 1 := by simp [hb]
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  -- no prime divides `c + N`, `d`, and `N`
  have hprime : ∀ p, p.Prime → p ∣ c + N → p ∣ d → ¬ p ∣ N := by
    intro p pp hpc hpd hpN
    have hpc' : p ∣ c := (Nat.dvd_add_left hpN).mp hpc
    have hdetp := congrArg (ZMod.castHom hpN (ZMod p)) hdet
    simp only [map_sub, map_mul, map_one] at hdetp
    have e10 : ZMod.castHom hpN (ZMod p) (M 1 0) = 0 := by
      rw [← hM10]
      simp only [Int.cast_natCast, map_natCast]
      exact (ZMod.natCast_eq_zero_iff c p).mpr hpc'
    have e11 : ZMod.castHom hpN (ZMod p) (M 1 1) = 0 := by
      rw [← hM11]
      simp only [Int.cast_natCast, map_natCast]
      exact (ZMod.natCast_eq_zero_iff d p).mpr hpd
    rw [e10, e11] at hdetp
    haveI : Fact p.Prime := ⟨pp⟩
    simp at hdetp
  obtain ⟨k, hk⟩ := exists_coprime_shift (c + N) d N (by omega) hprime
  set c' : ℤ := ((c + N : ℕ) : ℤ) with hc'
  set d' : ℤ := ((d + k * N : ℕ) : ℤ) with hd'
  have hcop : IsCoprime c' d' := Nat.isCoprime_iff_coprime.mpr hk
  obtain ⟨u, v, huv⟩ := hcop
  set x : ℤ := v
  set y : ℤ := -u
  have hxy : x * d' - y * c' = 1 := by simp only [x, y]; linear_combination huv
  set t : ℤ := x * (b : ℤ) - y * (a : ℤ)
  let γ : SL2Z := ⟨!![x + t * c', y + t * d'; c', d'], by
    rw [Matrix.det_fin_two_of]; linear_combination hxy⟩
  refine ⟨γ, ?_⟩
  have hc'N : ((c' : ℤ) : ZMod N) = M 1 0 := by
    rw [← hM10, hc']; push_cast; simp
  have hd'N : ((d' : ℤ) : ZMod N) = M 1 1 := by
    rw [← hM11, hd']; push_cast; simp
  have hxyN : (x : ZMod N) * M 1 1 - (y : ZMod N) * M 1 0 = 1 := by
    rw [← hc'N, ← hd'N]; exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) hxy
  ext i j
  fin_cases i <;> fin_cases j
  · change ((x + t * c' : ℤ) : ZMod N) = M 0 0
    push_cast [t]
    rw [hc'N, hA, hB]
    linear_combination (-(x : ZMod N)) * hdet + M 0 0 * hxyN
  · change ((y + t * d' : ℤ) : ZMod N) = M 0 1
    push_cast [t]
    rw [hd'N, hA, hB]
    linear_combination (-(y : ZMod N)) * hdet + M 0 1 * hxyN
  · exact hc'N
  · exact hd'N

end VOA.Huang.DLNBeyl
