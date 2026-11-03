import VOA.DeligneAudit.D4CharDemazureCharacter

/-! Specialization of the integer-row GT recursion to the existing natural Hilbert polynomials. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open Polynomial VOA.DeligneGaussian

noncomputable section

theorem rsSum_gtRows_nat {A : Type*} [AddCommMonoid A] {N : ℕ}
    (lam : Fin (N + 1) → ℕ) (f : (Fin N → ℤ) → A) :
    (∑ μ ∈ gtRows (fun i => (lam i : ℤ)), f μ) =
      ∑ μ ∈ Fintype.piFinset (fun i => Finset.Icc (lam i.succ) (lam i.castSucc)),
        f (fun i => (μ i : ℤ)) := by
  classical
  refine Finset.sum_bij' (fun μ _ i => (μ i).toNat) (fun μ _ i => (μ i : ℤ))
    ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    rw [Fintype.mem_piFinset]
    intro i
    have hi := (mem_gtRows _ _).mp hμ i
    apply Finset.mem_Icc.mpr
    dsimp only
    constructor <;> omega
  · intro μ hμ
    rw [mem_gtRows]
    intro i
    have hi := Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hμ) i)
    dsimp only
    constructor <;> omega
  · intro μ hμ
    funext i
    have hi := (mem_gtRows _ _).mp hμ i
    exact Int.toNat_of_nonneg (by omega)
  · intro μ _
    funext i
    simp
  · intro μ hμ
    congr 1
    funext i
    have hi := (mem_gtRows _ _).mp hμ i
    exact (Int.toNat_of_nonneg (by omega)).symm

theorem rsSum_piFinset_cons {A : Type*} [AddCommMonoid A] {N : ℕ}
    (s : Finset ℕ) (ss : Fin N → Finset ℕ) (f : (Fin (N + 1) → ℕ) → A) :
    (∑ μ ∈ Fintype.piFinset (Fin.cons s ss), f μ) =
      ∑ a ∈ s, ∑ μ ∈ Fintype.piFinset ss, f (Fin.cons a μ) := by
  classical
  calc
    _ = ∑ p ∈ s.product (Fintype.piFinset ss), f (Fin.cons p.1 p.2) := by
      refine Finset.sum_bij' (fun μ _ => (μ 0, Fin.tail μ))
        (fun p _ => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_
      · intro μ hμ
        simp only [Fintype.mem_piFinset, Fin.forall_fin_succ, Fin.cons_zero,
          Fin.cons_succ] at hμ
        simpa [Finset.mem_product, Fintype.mem_piFinset, Fin.tail] using hμ
      · intro p hp
        simpa [Finset.mem_product, Fintype.mem_piFinset, Fin.forall_fin_succ] using hp
      · intro μ _
        exact Fin.cons_self_tail μ
      · intro p _
        simp
      · intro μ _
        rw [Fin.cons_self_tail]
    _ = _ := by rw [Finset.product_eq_sprod, Finset.sum_product]

theorem rsSum_gtRows_three_nat {A : Type*} [AddCommMonoid A]
    (a b c : ℕ) (f : (Fin 2 → ℤ) → A) :
    (∑ μ ∈ gtRows ![(a : ℤ), (b : ℤ), (c : ℤ)], f μ) =
      ∑ i ∈ Finset.Icc b a, ∑ j ∈ Finset.Icc c b, f ![(i : ℤ), (j : ℤ)] := by
  have hn := rsSum_gtRows_nat (![a, b, c] : Fin 3 → ℕ) f
  change (∑ μ ∈ gtRows ![(a : ℤ), (b : ℤ), (c : ℤ)], f μ) = _ at hn
  rw [hn]
  have hs : (fun i : Fin 2 => Finset.Icc ((![a, b, c] : Fin 3 → ℕ) i.succ)
      ((![a, b, c] : Fin 3 → ℕ) i.castSucc)) =
        Fin.cons (Finset.Icc b a) (Fin.cons (Finset.Icc c b) ![]) := by
    funext i
    fin_cases i <;> rfl
  rw [hs]
  simp only [rsSum_piFinset_cons, Fintype.piFinset_of_isEmpty, Finset.sum_singleton]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp
  congr 1
  ext r
  fin_cases r <;> rfl


theorem rsSum_gtRows_four_nat {A : Type*} [AddCommMonoid A]
    (a b c d : ℕ) (f : (Fin 3 → ℤ) → A) :
    (∑ μ ∈ gtRows ![(a : ℤ), (b : ℤ), (c : ℤ), (d : ℤ)], f μ) =
      ∑ i ∈ Finset.Icc b a, ∑ j ∈ Finset.Icc c b, ∑ k ∈ Finset.Icc d c,
        f ![(i : ℤ), (j : ℤ), (k : ℤ)] := by
  have hn := rsSum_gtRows_nat (![a, b, c, d] : Fin 4 → ℕ) f
  change (∑ μ ∈ gtRows ![(a : ℤ), (b : ℤ), (c : ℤ), (d : ℤ)], f μ) = _ at hn
  rw [hn]
  have hs : (fun i : Fin 3 => Finset.Icc ((![a, b, c, d] : Fin 4 → ℕ) i.succ)
      ((![a, b, c, d] : Fin 4 → ℕ) i.castSucc)) =
        Fin.cons (Finset.Icc b a) (Fin.cons (Finset.Icc c b)
          (Fin.cons (Finset.Icc d c) ![])) := by
    funext i
    fin_cases i <;> rfl
  rw [hs]
  simp only [rsSum_piFinset_cons, Fintype.piFinset_of_isEmpty, Finset.sum_singleton]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp
  congr 1
  ext r
  fin_cases r <;> rfl


/-- GL2 at unit variables agrees exactly with the existing coefficient polynomial. -/
theorem rsGT_gl2Poly (a b : ℕ) :
    gtEval (X : ℚ[X]) (fun _ => 1) 2 ![(a : ℤ), (b : ℤ)] = A2.gl2Poly a b := by
  rw [gtEval, sum_gtRows_two_nat, A2.gl2Poly]
  apply Finset.sum_congr rfl
  intro i _
  simp [gtPsi, gtEval_one, Fin.prod_univ_succ, Int.toNat_sub]

/-- GL3 at unit variables agrees exactly with A2.gl3Poly at every natural row. -/
theorem rsGT_gl3Poly (a b c : ℕ) :
    gtEval (X : ℚ[X]) (fun _ => 1) 3 ![(a : ℤ), (b : ℤ), (c : ℤ)] =
      A2.gl3Poly a b c := by
  rw [gtEval, rsSum_gtRows_three_nat, A2.gl3Poly]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [gtPsi, rsGT_gl2Poly, Fin.prod_univ_succ, Int.toNat_sub]

/-- The GL4 GT/Hilbert bridge at all natural rows and all polynomial degrees. -/
theorem rsGT_gl4Poly (a b c d : ℕ) :
    gtEval (X : ℚ[X]) (fun _ => 1) 4 ![(a : ℤ), (b : ℤ), (c : ℤ), (d : ℤ)] =
      gl4Poly a b c d := by
  rw [gtEval, rsSum_gtRows_four_nat, gl4Poly]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp [gtPsi, rsGT_gl3Poly, Fin.prod_univ_succ, Int.toNat_sub, mul_assoc]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.rsSum_gtRows_nat
#print axioms VOA.DeligneAudit.D4Char.rsSum_piFinset_cons
#print axioms VOA.DeligneAudit.D4Char.rsSum_gtRows_three_nat
#print axioms VOA.DeligneAudit.D4Char.rsSum_gtRows_four_nat
#print axioms VOA.DeligneAudit.D4Char.rsGT_gl2Poly
#print axioms VOA.DeligneAudit.D4Char.rsGT_gl3Poly
#print axioms VOA.DeligneAudit.D4Char.rsGT_gl4Poly
