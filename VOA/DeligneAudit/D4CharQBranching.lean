import VOA.DeligneAudit.D4CharQNormalization

/-! The explicit normalized branching product and its degree-zero boundary. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open VOA.DeligneGaussian

noncomputable section

variable {R : Type*} [CommRing R]

/-- Cancel each Gaussian numerator against its Pochhammer normalization. -/
theorem gtPsi_normalized (q : R) (h : PochhammerUnits q) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) (hμ : μ ∈ gtRows lam) :
    gtPsi q lam μ * (∏ i : Fin N,
      (((gtPochUnit q h (lam i.castSucc - lam i.succ).toNat)⁻¹ : Rˣ) : R)) =
    ∏ i : Fin N, (((gtPochUnit q h (lam i.castSucc - μ i).toNat)⁻¹ : Rˣ) : R) *
      (((gtPochUnit q h (μ i - lam i.succ).toNat)⁻¹ : Rˣ) : R) := by
  rw [gtPsi, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hm := (mem_gtRows lam μ).mp hμ i
  have hk : (lam i.castSucc - μ i).toNat ≤ (lam i.castSucc - lam i.succ).toNat := by
    omega
  have he : (lam i.castSucc - lam i.succ).toNat - (lam i.castSucc - μ i).toNat =
      (μ i - lam i.succ).toNat := by omega
  simpa only [he] using gtGaussian_normalized q h _ _ hk

/-- Lemma 3.2(d): the explicit product, including the last-part denominator. -/
theorem gtQBranch_product (q : R) (h : PochhammerUnits q) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) (hμ : μ ∈ gtRows lam) :
    gtQBranch q h lam μ =
      (∏ i : Fin N, CarrierChain.qpochGen q (gtGap μ i) *
        (((gtPochUnit q h (lam i.castSucc - μ i).toNat)⁻¹ : Rˣ) : R) *
        (((gtPochUnit q h (μ i - lam i.succ).toNat)⁻¹ : Rˣ) : R)) *
      (((gtPochUnit q h (lam (Fin.last N)).toNat)⁻¹ : Rˣ) : R) := by
  rw [gtQBranch, gtNormUnit_succ, Units.val_mul, Units.coe_prod, gtNormUnit_inv_val,
    Units.coe_prod]
  simp only [gtPochUnit_val]
  rw [← mul_assoc, gtPsi_normalized q h lam μ hμ]
  simp only [Finset.prod_mul_distrib]
  ring

/-- Appending a zero does not alter b_lambda. -/
theorem gtNormUnit_snoc_zero (q : R) (h : PochhammerUnits q) {N : ℕ}
    (μ : Fin N → ℤ) :
    gtNormUnit q h (Fin.snoc (α := fun _ => ℤ) μ 0) = gtNormUnit q h μ := by
  rw [gtNormUnit_succ]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Int.toNat_zero, gtPochUnit_zero,
    inv_one, mul_one]
  simp [gtNormUnit, gtGap]

/-- A degree-zero branch of a nonnegative partition is exactly deletion of a final zero. -/
theorem gtRows_degree_zero {N : ℕ} (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ)
    (hμ : μ ∈ gtRows lam) (hpos : 0 ≤ lam (Fin.last N))
    (hs : (∑ i, lam i) = ∑ i, μ i) :
    lam = Fin.snoc (α := fun _ => ℤ) μ 0 := by
  have hle : (∑ i, μ i) ≤ ∑ i : Fin N, lam i.castSucc :=
    Finset.sum_le_sum fun i _ => ((mem_gtRows lam μ).mp hμ i).2
  rw [Fin.sum_univ_castSucc] at hs
  have hz : lam (Fin.last N) = 0 := by omega
  have he : μ = fun i => lam i.castSucc := gtRows_eq_top_of_sum hμ (by omega)
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hz
  · simpa using (congrFun he j).symm

/-- The coefficient of the unique degree-zero normalized branch is one. -/
theorem gtQBranch_degree_zero (q : R) (h : PochhammerUnits q) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) (hμ : μ ∈ gtRows lam)
    (hpos : 0 ≤ lam (Fin.last N)) (hs : (∑ i, lam i) = ∑ i, μ i) :
    gtQBranch q h lam μ = 1 := by
  have he := gtRows_degree_zero lam μ hμ hpos hs
  subst lam
  rw [gtQBranch, gtNormUnit_snoc_zero]
  have hpsi : gtPsi q (Fin.snoc (α := fun _ => ℤ) μ 0) μ = 1 := by
    simp [gtPsi]
  rw [hpsi, one_mul]
  exact Units.mul_inv _

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtPsi_normalized
#print axioms VOA.DeligneAudit.D4Char.gtQBranch_product
#print axioms VOA.DeligneAudit.D4Char.gtNormUnit_snoc_zero
#print axioms VOA.DeligneAudit.D4Char.gtRows_degree_zero
#print axioms VOA.DeligneAudit.D4Char.gtQBranch_degree_zero
