import VOA.DeligneAudit.D4CharCauchyShift

/-!
Rank-two gP coefficients. Central shifts reduce the proof to C(2,2), avoiding
coefficient extraction from C(2,3). All row lengths and degrees remain arbitrary.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open VOA.DeligneGaussian

noncomputable section

variable {R : Type*} [CommRing R]

theorem gtQ_two_eq (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) (a b : ℕ) :
    gtQ q h u 2 ![(a : ℤ), (b : ℤ)] =
      gtInvPoch q h (a - b : ℕ) * gtInvPoch q h b *
        gtEval q u 2 ![(a : ℤ), (b : ℤ)] := by
  rw [gtQ, gtNormUnit_succ]
  simp [gtInvPoch_nat]

/-- The determinant shift in two variables, with natural row coordinates. -/
theorem gtEval_two_shift (q : R) (u : ℕ → Rˣ) (a b d : ℕ) :
    gtEval q u 2 ![((a + d : ℕ) : ℤ), ((b + d : ℕ) : ℤ)] =
      ((u 0 : R) * (u 1 : R)) ^ d * gtEval q u 2 ![(a : ℤ), (b : ℤ)] := by
  have he : ![((a + d : ℕ) : ℤ), ((b + d : ℕ) : ℤ)] =
      fun i => (![(a : ℤ), (b : ℤ)] : Fin 2 → ℤ) i + d := by
    ext i
    fin_cases i <;> simp
  rw [he, gtEval_central_shift]
  simp [Fin.prod_univ_succ, mul_pow]

/-- Removing the last part of a two-row Q polynomial leaves a one-row Q. -/
theorem gtQ_two_oneRow (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (c d : ℕ) (hd : d ≤ c) :
    gtQ q h u 2 ![(c : ℤ), (d : ℤ)] =
      gtInvPoch q h d * ((u 0 : R) * (u 1 : R)) ^ d *
        gtOneRowCoeff q h u 2 (c - d) := by
  have he : gtEval q u 2 ![(c : ℤ), (d : ℤ)] =
      ((u 0 : R) * (u 1 : R)) ^ d *
        gtEval q u 2 ![((c - d : ℕ) : ℤ), 0] := by
    simpa only [Nat.sub_add_cancel hd, zero_add] using
      gtEval_two_shift q u (c - d) 0 d
  rw [gtQ_two_eq, he]
  simp only [gtOneRowCoeff, gtQ_oneRow_eq]
  have hr : gtOneRow 1 (c - d) = ![((c - d : ℕ) : ℤ), 0] := by
    ext i
    fin_cases i <;> rfl
  rw [hr]
  ring

/-- The upper row indexed by b interlaces (c,d) and has degree increment k. -/
theorem gtGP_two_interlaces (c d k b : ℕ) (hd : d ≤ c)
    (hb : b ≤ min k (c - d)) :
    (![(c : ℤ), (d : ℤ)] : Fin 2 → ℤ) ∈
      gtRows ![((c + k - b : ℕ) : ℤ), ((d + b : ℕ) : ℤ), 0] := by
  apply (mem_gtRows _ _).mpr
  intro i
  fin_cases i
  · change ((d + b : ℕ) : ℤ) ≤ c ∧ (c : ℤ) ≤ (c + k - b : ℕ)
    omega
  · change (0 : ℤ) ≤ d ∧ (d : ℤ) ≤ (d + b : ℕ)
    omega

/-- The gP branching factor times b_kappa is the C(2,2) coefficient times 1/(q)_d. -/
theorem gtGP_two_normalized (q : R) (h : PochhammerUnits q)
    (c d k b : ℕ) (hd : d ≤ c) (hb : b ≤ min k (c - d)) :
    gtPsi q ![((c + k - b : ℕ) : ℤ), ((d + b : ℕ) : ℤ), 0]
        ![(c : ℤ), (d : ℤ)] *
      (gtNormUnit q h ![((c + k - b : ℕ) : ℤ), ((d + b : ℕ) : ℤ)] : R) =
    gtInvPoch q h d * (gtInvPoch q h (k - b : ℕ) *
      gtInvPoch q h (c - d - b : ℕ) * gtInvPoch q h b) := by
  have hn := gtPsi_normalized q h
    ![((c + k - b : ℕ) : ℤ), ((d + b : ℕ) : ℤ), 0]
    ![(c : ℤ), (d : ℤ)] (gtGP_two_interlaces c d k b hd hb)
  have h₁ : ((c + k - b : ℕ) : ℤ) - c = ((k - b : ℕ) : ℤ) := by omega
  have h₂ : (c : ℤ) - (d + b : ℕ) = ((c - d - b : ℕ) : ℤ) := by omega
  have h₃ : ((d + b : ℕ) : ℤ) - d = (b : ℤ) := by omega
  rw [gtNormUnit_succ]
  simp only [Fin.prod_univ_succ, Fin.succ_zero_eq_one,
    Fin.castSucc_zero, Fin.castSucc_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one, Units.val_mul] at hn ⊢
  simp only [sub_zero, h₁, h₂, h₃, Int.toNat_natCast] at hn
  simp only [← gtInvPoch_nat] at hn
  convert hn using 1
  ring

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtQ_two_eq
#print axioms VOA.DeligneAudit.D4Char.gtEval_two_shift
#print axioms VOA.DeligneAudit.D4Char.gtQ_two_oneRow
#print axioms VOA.DeligneAudit.D4Char.gtGP_two_interlaces
#print axioms VOA.DeligneAudit.D4Char.gtGP_two_normalized
