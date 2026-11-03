import VOA.DeligneAudit.D4CharPieriEStep

/-! Zero-extended GT coefficients and a common finite box for the Pieri induction. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

variable {R : Type*} [CommRing R]

noncomputable section

/-- The branching coefficient, zero outside the interlacing region. -/
def gtPsiZero (q : R) {N : ℕ} (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) : R :=
  ∏ i, intQbinom q (lam i.castSucc - lam i.succ) (lam i.castSucc - μ i)

theorem gtPsiZero_of_mem (q : R) {N : ℕ} (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ)
    (hμ : μ ∈ gtRows lam) : gtPsiZero q lam μ = gtPsi q lam μ := by
  apply Finset.prod_congr rfl
  intro i _
  have h := (mem_gtRows lam μ).mp hμ i
  simp only [intQbinom, show 0 ≤ lam i.castSucc - lam i.succ by omega,
    show 0 ≤ lam i.castSucc - μ i by omega, and_self, if_true]

theorem gtPsiZero_of_not_mem (q : R) {N : ℕ} (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ)
    (hμ : μ ∉ gtRows lam) : gtPsiZero q lam μ = 0 := by
  classical
  have hh : ¬ ∀ i, lam i.succ ≤ μ i ∧ μ i ≤ lam i.castSucc := by
    simpa only [mem_gtRows] using hμ
  obtain ⟨i, hi⟩ := not_forall.mp hh
  unfold gtPsiZero
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_cases hu : μ i ≤ lam i.castSucc
  · exact intQbinom_above q _ _ (by omega)
  · exact intQbinom_lower_neg q _ _ (by omega)

/-- Branching over any finite box containing all interlacing rows. -/
theorem gtEval_sum_box (q : R) (u : ℕ → Rˣ) {N : ℕ} (lam : Fin (N + 1) → ℤ)
    (B : Finset (Fin N → ℤ)) (hB : gtRows lam ⊆ B) :
    gtEval q u (N + 1) lam =
      ∑ μ ∈ B, gtPsiZero q lam μ *
        ((u N) ^ ((∑ i, lam i) - ∑ i, μ i) : Rˣ) * gtEval q u N μ := by
  classical
  rw [gtEval]
  calc
    _ = ∑ μ ∈ gtRows lam, gtPsiZero q lam μ *
        ((u N) ^ ((∑ i, lam i) - ∑ i, μ i) : Rˣ) * gtEval q u N μ := by
      apply Finset.sum_congr rfl
      intro μ hμ
      rw [gtPsiZero_of_mem q lam μ hμ]
    _ = _ := Finset.sum_subset hB fun μ _ hμ => by
      rw [gtPsiZero_of_not_mem q lam μ hμ, zero_mul, zero_mul]

def pieriRaise {N : ℕ} (lam : Fin N → ℤ) (s : Fin N → Bool) : Fin N → ℤ :=
  fun i => lam i + pieriBit (s i)

def pieriLower {N : ℕ} (μ : Fin N → ℤ) (s : Fin N → Bool) : Fin N → ℤ :=
  fun i => μ i - pieriBit (s i)

theorem pieriBit_bounds (b : Bool) : 0 ≤ pieriBit b ∧ pieriBit b ≤ 1 := by
  cases b <;> simp [pieriBit]

/-- A common finite summation box for every binary raising of the top row. -/
def pieriRowBox {N : ℕ} (lam : Fin (N + 1) → ℤ) : Finset (Fin N → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (lam i.succ) (lam i.castSucc + 1)

theorem mem_pieriRowBox {N : ℕ} (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) :
    μ ∈ pieriRowBox lam ↔ ∀ i, lam i.succ ≤ μ i ∧ μ i ≤ lam i.castSucc + 1 := by
  simp [pieriRowBox, Fintype.mem_piFinset]

theorem gtRows_raise_subset_box {N : ℕ} (lam : Fin (N + 1) → ℤ)
    (s : Fin (N + 1) → Bool) : gtRows (pieriRaise lam s) ⊆ pieriRowBox lam := by
  intro μ hμ
  rw [mem_pieriRowBox]
  intro i
  have hi := (mem_gtRows _ μ).mp hμ i
  have hb₁ := pieriBit_bounds (s i.castSucc)
  have hb₂ := pieriBit_bounds (s i.succ)
  dsimp [pieriRaise] at hi
  omega

theorem raise_gtRow_mem_box {N : ℕ} (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ)
    (hμ : μ ∈ gtRows lam) (t : Fin N → Bool) : pieriRaise μ t ∈ pieriRowBox lam := by
  rw [mem_pieriRowBox]
  intro i
  have hi := (mem_gtRows lam μ).mp hμ i
  have hb := pieriBit_bounds (t i)
  dsimp [pieriRaise]
  omega

/-- Reindex a shifted interlacing sum in the same common box used on the other side. -/
theorem gtPsiZero_raise_sum (q : R) {N : ℕ} (lam : Fin (N + 1) → ℤ)
    (t : Fin N → Bool) (f : (Fin N → ℤ) → R) :
    (∑ μ ∈ gtRows lam, gtPsi q lam μ * f (pieriRaise μ t)) =
      ∑ ν ∈ pieriRowBox lam, gtPsiZero q lam (pieriLower ν t) * f ν := by
  classical
  let B := (gtRows lam).image fun μ => pieriRaise μ t
  have hinj : Function.Injective (fun μ : Fin N → ℤ => pieriRaise μ t) := by
    intro μ ν h
    funext i
    have := congrFun h i
    dsimp [pieriRaise] at this
    omega
  have hB : B ⊆ pieriRowBox lam := by
    intro ν hν
    obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hν
    exact raise_gtRow_mem_box lam μ hμ t
  calc
    _ = ∑ ν ∈ B, gtPsiZero q lam (pieriLower ν t) * f ν := by
      rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
      apply Finset.sum_congr rfl
      intro μ hμ
      have he : pieriLower (pieriRaise μ t) t = μ := by
        ext i
        simp [pieriLower, pieriRaise]
      rw [he, gtPsiZero_of_mem q lam μ hμ]
    _ = _ := Finset.sum_subset hB fun ν _ hν => by
      have hn : pieriLower ν t ∉ gtRows lam := by
        intro h
        apply hν
        apply Finset.mem_image.mpr
        refine ⟨pieriLower ν t, h, ?_⟩
        ext i
        simp [pieriRaise, pieriLower]
      rw [gtPsiZero_of_not_mem q lam _ hn, zero_mul]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtPsiZero_of_mem
#print axioms VOA.DeligneAudit.D4Char.gtPsiZero_of_not_mem
#print axioms VOA.DeligneAudit.D4Char.gtEval_sum_box
#print axioms VOA.DeligneAudit.D4Char.gtRows_raise_subset_box
#print axioms VOA.DeligneAudit.D4Char.raise_gtRow_mem_box
#print axioms VOA.DeligneAudit.D4Char.gtPsiZero_raise_sum
