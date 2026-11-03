import VOA.DeligneAudit.SL4TRemainderMatrix
import Mathlib.Algebra.Polynomial.RingDivision

/-! # Transport of remainder columns when the full-flag cutoff decreases -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {A D : Type*} [CommRing A] [CommRing D]

theorem alphabetCharacteristic_map (f : A →+* D) (xs : List A) :
    (alphabetCharacteristic xs).map f = alphabetCharacteristic (xs.map f) := by
  rw [alphabetCharacteristic, ← reflect_map, alphabetElementary_map,
    alphabetCharacteristic, List.length_map]

theorem alphabetPowerRemainder_map (f : A →+* D) (xs : List A) (m l : ℕ) :
    f (alphabetPowerRemainder xs m l) = alphabetPowerRemainder (xs.map f) m l := by
  rw [alphabetPowerRemainder, ← coeff_map, map_modByMonic f
    (alphabetCharacteristic_monic xs), alphabetCharacteristic_map]
  simp only [Polynomial.map_pow, Polynomial.map_X, alphabetPowerRemainder]

/-- A nilpotent deleted root truncates the geometric expansion of the characteristic. -/
theorem alphabetCharacteristic_delete_truncated (xs : List A) (z : A) (k : ℕ)
    (hk : k ≤ xs.length) (hz : z ^ (k + 1) = 0)
    (he : D4Levi.ksEPoly (xs ++ [z]) = 1) :
    alphabetCharacteristic xs =
      ∑ e ∈ Finset.range (k + 1), Polynomial.C (z ^ e) * X ^ (xs.length - e) := by
  classical
  rw [alphabetCharacteristic_delete_expansion xs z he]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro e he hnot
  have hbound : k + 1 ≤ e := by simpa using hnot
  rw [pow_eq_zero_of_le hbound hz, map_zero, zero_mul]

/-- The column relation follows directly by deleting one characteristic factor.
This form does not require a formula for the individual remainder entries. -/
theorem alphabetRemainder_shift_of_nilpotent (ys zs : List A) (z : A) (N k c l : ℕ)
    (hN : 0 < N) (hlen : (ys ++ zs).length + 1 = N + k)
    (he : D4Levi.ksEPoly ((ys ++ zs) ++ [z]) = 1) (hz : z ^ (k + 1) = 0) :
    z ^ k * alphabetPowerRemainder ys (N - 1 + c) l +
      ∑ e ∈ Finset.range k, z ^ e * alphabetPowerRemainder ys (N + c + k - 1 - e) l = 0 := by
  classical
  have hp := alphabetCharacteristic_delete_truncated (ys ++ zs) z k (by omega) hz he
  have hd : alphabetCharacteristic ys ∣ alphabetCharacteristic (ys ++ zs) * X ^ c := by
    rw [alphabetCharacteristic_append]
    exact ⟨alphabetCharacteristic zs * X ^ c, by ring⟩
  have hzero := (modByMonic_eq_zero_iff_dvd (alphabetCharacteristic_monic ys)).mpr hd
  rw [hp, Finset.sum_mul] at hzero
  change modByMonicHom (alphabetCharacteristic ys)
    (∑ e ∈ Finset.range (k + 1),
      (Polynomial.C (z ^ e) * X ^ ((ys ++ zs).length - e)) * X ^ c) = 0 at hzero
  simp only [mul_assoc, ← pow_add] at hzero
  simp only [← smul_eq_C_mul, map_sum, map_smul] at hzero
  have hc := congrArg (fun p : A[X] => p.coeff l) hzero
  simp only [finsetSum_coeff, coeff_smul, smul_eq_mul, coeff_zero,
    modByMonicHom_apply] at hc
  change (∑ e ∈ Finset.range (k + 1),
    z ^ e * alphabetPowerRemainder ys ((ys ++ zs).length - e + c) l) = 0 at hc
  rw [Finset.sum_range_succ, add_comm,
    show (ys ++ zs).length - k + c = N - 1 + c by omega] at hc
  have hs : (∑ e ∈ Finset.range k,
      z ^ e * alphabetPowerRemainder ys (N + c + k - 1 - e) l) =
      ∑ e ∈ Finset.range k,
        z ^ e * alphabetPowerRemainder ys ((ys ++ zs).length - e + c) l := by
    apply Finset.sum_congr rfl
    intro e he
    have he' := Finset.mem_range.mp he
    rw [show N + c + k - 1 - e = (ys ++ zs).length - e + c by omega]
  rw [hs]
  exact hc

/-- The cutoff-shift relation holds entrywise modulo the next power of the deleted root. -/
theorem alphabetRemainder_shift_mem (ys zs : List A) (z : A) (N k c l : ℕ)
    (hN : 0 < N) (hlen : (ys ++ zs).length + 1 = N + k)
    (he : D4Levi.ksEPoly ((ys ++ zs) ++ [z]) = 1) :
    z ^ k * alphabetPowerRemainder ys (N - 1 + c) l +
      ∑ e ∈ Finset.range k, z ^ e * alphabetPowerRemainder ys (N + c + k - 1 - e) l ∈
        Ideal.span {z ^ (k + 1)} := by
  let I : Ideal A := Ideal.span {z ^ (k + 1)}
  let q := Ideal.Quotient.mk I
  have hq : D4Levi.ksEPoly ((ys.map q ++ zs.map q) ++ [q z]) = 1 := by
    have h := congrArg (Polynomial.map q) he
    simpa only [alphabetElementary_map, List.map_append, List.map_cons,
      List.map_nil, Polynomial.map_one] using h
  have hz : q z ^ (k + 1) = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q _ = 0
  simp only [map_add, map_sum, map_mul, map_pow, alphabetPowerRemainder_map]
  exact alphabetRemainder_shift_of_nilpotent (ys.map q) (zs.map q) (q z) N k c l hN
    (by simpa only [List.length_append, List.length_map] using hlen) hq hz

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_map
#print axioms VOA.DeligneAudit.SL4T.alphabetPowerRemainder_map
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_delete_truncated
#print axioms VOA.DeligneAudit.SL4T.alphabetRemainder_shift_of_nilpotent
#print axioms VOA.DeligneAudit.SL4T.alphabetRemainder_shift_mem
