import VOA.DeligneAudit.D4CharLeviCount

/-!
# Gelfand--Tsetlin q-Whittaker polynomials

Integer rows allow negative highest weights directly. Branching always deletes the last
variable. `gtEval` permits substitution into any commutative ring with unit variables;
`gtP` is the actual Laurent polynomial over the integral polynomial ring in q.
There is no restriction on the highest weight or on the rank.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open VOA.DeligneGaussian

noncomputable section

/-- The finite set of rows interlacing an integer row. -/
def gtRows {N : ℕ} (lam : Fin (N + 1) → ℤ) : Finset (Fin N → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (lam i.succ) (lam i.castSucc)

theorem mem_gtRows {N : ℕ} (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) :
    μ ∈ gtRows lam ↔ ∀ i, lam i.succ ≤ μ i ∧ μ i ≤ lam i.castSucc := by
  simp [gtRows, Fintype.mem_piFinset]

/-- The product of Gaussian binomials attached to one interlacing step. -/
def gtPsi {R : Type*} [CommRing R] (q : R) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) : R :=
  ∏ i, qbinom q (lam i.castSucc - lam i.succ).toNat (lam i.castSucc - μ i).toNat

/-- GT branching, evaluated at arbitrary unit variables. -/
def gtEval {R : Type*} [CommRing R] (q : R) (u : ℕ → Rˣ) :
    (N : ℕ) → (Fin N → ℤ) → R
  | 0, _ => 1
  | N + 1, lam =>
      ∑ μ ∈ gtRows lam,
        gtPsi q lam μ * ((u N) ^ ((∑ i, lam i) - ∑ i, μ i) : Rˣ) * gtEval q u N μ

/-- Finitely supported Laurent exponents in countably many variable names. -/
abbrev GTLaurent := AddMonoidAlgebra (Polynomial ℤ) (ℕ →₀ ℤ)

/-- The ith formal Laurent variable is a unit. -/
def gtVariable (i : ℕ) : GTLaurentˣ where
  val := AddMonoidAlgebra.single (Finsupp.single i 1) 1
  inv := AddMonoidAlgebra.single (Finsupp.single i (-1)) 1
  val_inv := by
    simp [AddMonoidAlgebra.single_mul_single]
    rfl
  inv_val := by
    simp [AddMonoidAlgebra.single_mul_single]
    rfl

/-- The GL_N GT q-Whittaker Laurent polynomial over ℤ[q]. -/
def gtP (N : ℕ) (lam : Fin N → ℤ) : GTLaurent :=
  gtEval (AddMonoidAlgebra.single 0 Polynomial.X) gtVariable N lam

theorem gtEval_zero {R : Type*} [CommRing R] (q : R) (u : ℕ → Rˣ)
    (lam : Fin 0 → ℤ) : gtEval q u 0 lam = 1 := rfl

theorem gtEval_one {R : Type*} [CommRing R] (q : R) (u : ℕ → Rˣ)
    (lam : Fin 1 → ℤ) : gtEval q u 1 lam = ((u 0) ^ lam 0 : Rˣ) := by
  simp [gtEval, gtRows, gtPsi, Fintype.piFinset_of_isEmpty]

/-- Every interlacing row of a dominant row is dominant. -/
theorem gtRows_dominant {N : ℕ} {lam : Fin (N + 1) → ℤ} (hlam : Antitone lam)
    {μ : Fin N → ℤ} (hμ : μ ∈ gtRows lam) : Antitone μ := by
  have hm := (mem_gtRows lam μ).mp hμ
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hij
  · exact le_rfl
  · exact (hm j).2.trans ((hlam (show i.succ ≤ j.castSucc by
      change i.val + 1 ≤ j.val
      exact hij)).trans (hm i).1)

/-- Central shifts preserve both interlacing and its Gaussian branching weight. -/
theorem gtRows_shift {N : ℕ} (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) (c : ℤ) :
    (fun i => μ i + c) ∈ gtRows (fun i => lam i + c) ↔ μ ∈ gtRows lam := by
  simp only [mem_gtRows, add_le_add_iff_right]

theorem gtPsi_shift {R : Type*} [CommRing R] (q : R) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) (c : ℤ) :
    gtPsi q (fun i => lam i + c) (fun i => μ i + c) = gtPsi q lam μ := by
  simp [gtPsi]

/-- The degree of the last variable changes by c under a central shift. -/
theorem gt_degree_shift {N : ℕ} (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) (c : ℤ) :
    (∑ i, (lam i + c)) - (∑ i, (μ i + c)) = (∑ i, lam i) - (∑ i, μ i) + c := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.mem_gtRows
#print axioms VOA.DeligneAudit.D4Char.gtEval_zero
#print axioms VOA.DeligneAudit.D4Char.gtEval_one
#print axioms VOA.DeligneAudit.D4Char.gtRows_dominant
#print axioms VOA.DeligneAudit.D4Char.gtRows_shift
#print axioms VOA.DeligneAudit.D4Char.gtPsi_shift
#print axioms VOA.DeligneAudit.D4Char.gt_degree_shift
