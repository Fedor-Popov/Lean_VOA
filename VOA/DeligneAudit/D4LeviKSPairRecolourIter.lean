import VOA.DeligneAudit.D4LeviKSPairRecolourInvariant

/-! Iterate the symmetric recolouring conversion. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pairAdjoint_append (F : ℕ → Module.End ℂ V)
    (rs ss : List ℕ) (A : Module.End ℂ V) :
    pairAdjoint F (rs ++ ss) A = pairAdjoint F ss (pairAdjoint F rs A) := by
  induction rs generalizing A with
  | nil => rfl
  | cons r rs ih =>
      simp only [List.cons_append, pairAdjoint]
      exact ih _

/-- The scalar accumulated after `k` conversions. -/
def pairIterCoefficient (a b : ℕ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => -(a + (b - k) : ℂ) * pairIterCoefficient a b k

theorem pairIterCoefficient_descFactorial (a b k : ℕ) (hk : k ≤ b) :
    pairIterCoefficient a b k =
      (-1 : ℂ) ^ k * (Nat.descFactorial (a + b) k : ℂ) := by
  induction k with
  | zero => simp [pairIterCoefficient]
  | succ k ih =>
      have hk' : k ≤ b := by omega
      rw [pairIterCoefficient, ih hk', Nat.descFactorial_succ, pow_succ]
      have hnat : a + b - k = a + (b - k) := by omega
      rw [hnat]
      push_cast
      rw [Nat.cast_sub hk']
      ring

theorem pairRecolour_adjoint_iterated
    (ρ : CurrentModule D4sector.f V) (a b c : ℕ)
    (γ : ℕ → ℕ) (P : MvPolynomial (PairSource a b c) ℂ)
    (hP : P ∈ pairSourceSymmetric a b c)
    (k : ℕ) (hk : k ≤ b) :
    pairAdjoint (ρ.op (17 : Fin 28)) ((List.range k).map γ)
        (pairRecolourOperator ρ a b c 0 P) =
      pairIterCoefficient a b k •
        pairRecolourOperator ρ a b c k
          (pairEarlierXFactor a b c k (fun y => γ y.val) * P) := by
  induction k with
  | zero =>
      simp [pairAdjoint, pairIterCoefficient, pairEarlierXFactor]
  | succ k ih =>
      have hk' : k < b := by omega
      rw [List.range_succ, List.map_append, pairAdjoint_append]
      simp only [List.map_singleton]
      rw [ih (Nat.le_of_lt hk')]
      rw [pairAdjoint_smul]
      have hstep := pairRecolour_adjoint_shifted ρ a b c k hk'
        (fun y : Fin b => γ y.val) P hP
      rw [hstep]
      rw [smul_neg, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      rw [pairIterCoefficient, ← neg_smul]
      congr 1
      rw [Nat.cast_add, Nat.cast_sub (Nat.le_of_lt hk')]
      ring

theorem pairRecolour_adjoint_full
    (ρ : CurrentModule D4sector.f V) (a b c : ℕ)
    (γ : ℕ → ℕ) (P : MvPolynomial (PairSource a b c) ℂ)
    (hP : P ∈ pairSourceSymmetric a b c) :
    pairAdjoint (ρ.op (17 : Fin 28)) ((List.range b).map γ)
        (pairRecolourOperator ρ a b c 0 P) =
      ((-1 : ℂ) ^ b * (Nat.descFactorial (a + b) b : ℂ)) •
        pairRecolourOperator ρ a b c b
          (pairEarlierXFactor a b c b (fun y => γ y.val) * P) := by
  rw [pairRecolour_adjoint_iterated ρ a b c γ P hP b le_rfl]
  rw [pairIterCoefficient_descFactorial a b b le_rfl]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairAdjoint_append
#print axioms VOA.DeligneAudit.D4Levi.pairIterCoefficient_descFactorial
#print axioms VOA.DeligneAudit.D4Levi.pairRecolour_adjoint_iterated
#print axioms VOA.DeligneAudit.D4Levi.pairRecolour_adjoint_full
