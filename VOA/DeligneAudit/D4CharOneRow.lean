import VOA.DeligneAudit.D4CharEuler

/-! One-row GT branching, uniformly in rank and degree. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open VOA.DeligneGaussian

noncomputable section

variable {R : Type*} [CommRing R]

/-- A one-row partition, in N + 1 variables. -/
def gtOneRow (N k : ℕ) : Fin (N + 1) → ℤ := Fin.cons (k : ℤ) (fun _ => 0)

theorem gtOneRow_apply (N k : ℕ) (i : Fin (N + 1)) :
    gtOneRow N k i = if i = 0 then k else 0 := by
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [gtOneRow]

theorem gtOneRow_dominant (N k : ℕ) : Antitone (gtOneRow N k) := by
  intro i j hij
  by_cases hj : j = 0
  · subst j
    have hi : i = 0 := le_antisymm hij (Fin.zero_le _)
    subst i
    exact le_rfl
  · simp only [gtOneRow_apply, if_neg hj]
    split_ifs <;> omega

theorem gtOneRow_nonneg (N k : ℕ) (i : Fin (N + 1)) : 0 ≤ gtOneRow N k i := by
  rw [gtOneRow_apply]
  split_ifs <;> omega

@[simp] theorem gtOneRow_sum (N k : ℕ) : (∑ i, gtOneRow N k i) = k := by
  simp [gtOneRow, Fin.sum_univ_succ]

theorem gtOneRow_snoc (N k : ℕ) :
    Fin.snoc (α := fun _ => ℤ) (gtOneRow N k) 0 = gtOneRow (N + 1) k := by
  have hz : Fin.snoc (α := fun _ => ℤ) (fun _ : Fin N => 0) 0 = fun _ => 0 := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  simp only [gtOneRow, ← Fin.cons_snoc_eq_snoc_cons, hz]

theorem gtGap_oneRow (N k : ℕ) (i : Fin (N + 1)) :
    gtGap (gtOneRow N k) i = if i = 0 then k else 0 := by
  simp only [gtGap, gtOneRow_snoc]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [gtOneRow]
  · simp [gtOneRow, Fin.castSucc_succ]

theorem gtNormUnit_oneRow (q : R) (h : PochhammerUnits q) (N k : ℕ) :
    gtNormUnit q h (gtOneRow N k) = (gtPochUnit q h k)⁻¹ := by
  simp [gtNormUnit, gtGap_oneRow, Fin.prod_univ_succ]

/-- Interlacing one-row partitions is exactly choosing a smaller row length. -/
theorem mem_gtRows_oneRow (N k : ℕ) (μ : Fin (N + 1) → ℤ) :
    μ ∈ gtRows (gtOneRow (N + 1) k) ↔ ∃ j ≤ k, μ = gtOneRow N j := by
  constructor
  · intro hμ
    have hm := (mem_gtRows _ _).mp hμ
    have h0 : 0 ≤ μ 0 ∧ μ 0 ≤ k := by simpa [gtOneRow] using hm 0
    refine ⟨(μ 0).toNat, by omega, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [gtOneRow, Fin.cons_zero]
      omega
    · have hj : μ j.succ = 0 := by
        have ht := hm j.succ
        simp only [gtOneRow, Fin.castSucc_succ, Fin.cons_succ] at ht
        omega
      simpa [gtOneRow] using hj
  · rintro ⟨j, hj, rfl⟩
    apply (mem_gtRows _ _).mpr
    intro i
    refine Fin.cases ?_ (fun t => ?_) i
    · simpa [gtOneRow] using And.intro (Int.natCast_nonneg j) (Int.ofNat_le.mpr hj)
    · simp [gtOneRow, Fin.castSucc_succ]

theorem sum_gtRows_oneRow {A : Type*} [AddCommMonoid A] (N k : ℕ)
    (f : (Fin (N + 1) → ℤ) → A) :
    (∑ μ ∈ gtRows (gtOneRow (N + 1) k), f μ) =
      ∑ j ∈ Finset.range (k + 1), f (gtOneRow N j) := by
  classical
  refine Finset.sum_bij' (fun μ _ => (μ 0).toNat) (fun j _ => gtOneRow N j)
    ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    obtain ⟨j, hj, rfl⟩ := (mem_gtRows_oneRow N k μ).mp hμ
    simpa [gtOneRow] using hj
  · intro j hj
    exact (mem_gtRows_oneRow N k _).mpr ⟨j, by simpa using hj, rfl⟩
  · intro μ hμ
    obtain ⟨j, _, rfl⟩ := (mem_gtRows_oneRow N k μ).mp hμ
    simp [gtOneRow]
  · intro j _
    simp [gtOneRow]
  · intro μ hμ
    obtain ⟨j, _, rfl⟩ := (mem_gtRows_oneRow N k μ).mp hμ
    simp [gtOneRow]

theorem gtPsi_oneRow (q : R) (N k j : ℕ) :
    gtPsi q (gtOneRow (N + 1) k) (gtOneRow N j) = qbinom q k (k - j) := by
  simp [gtPsi, Fin.prod_univ_succ, gtOneRow, Fin.castSucc_succ]

/-- The one-row specialization of the original GT recursion. -/
theorem gtEval_oneRow_branching (q : R) (u : ℕ → Rˣ) (N k : ℕ) :
    gtEval q u (N + 2) (gtOneRow (N + 1) k) =
      ∑ j ∈ Finset.range (k + 1), qbinom q k (k - j) * (u (N + 1) : R) ^ (k - j) *
        gtEval q u (N + 1) (gtOneRow N j) := by
  rw [gtEval, sum_gtRows_oneRow]
  apply Finset.sum_congr rfl
  intro j hj
  have hle : j ≤ k := by simpa using hj
  rw [gtPsi_oneRow, gtOneRow_sum, gtOneRow_sum, ← Int.natCast_sub hle, zpow_natCast]
  rfl

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtOneRow_dominant
#print axioms VOA.DeligneAudit.D4Char.gtNormUnit_oneRow
#print axioms VOA.DeligneAudit.D4Char.mem_gtRows_oneRow
#print axioms VOA.DeligneAudit.D4Char.sum_gtRows_oneRow
#print axioms VOA.DeligneAudit.D4Char.gtPsi_oneRow
#print axioms VOA.DeligneAudit.D4Char.gtEval_oneRow_branching
