import VOA.DeligneAudit.D4CharPieriPaths

/-!
# The E-step identity of STEP2, section 4

This is the full finite binary-state identity, for arbitrary length, nonnegative upper
indices, and arbitrary integer lower indices. The parameter q is a unit so that every
integer power in the paper has its literal meaning, even outside the Gaussian support.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

variable {R : Type*} [CommRing R]

noncomputable section

def pieriStateWeight (z : R) (s : Bool) : R := if s then z else 1

def pieriStateSize {n : ℕ} (s : Fin n → Bool) : ℕ := ∑ i, (s i).toNat

theorem pieriStateWeight_prod (z : R) {n : ℕ} (s : Fin n → Bool) :
    (∏ i, pieriStateWeight z (s i)) = z ^ pieriStateSize s := by
  have h : ∀ b : Bool, pieriStateWeight z b = z ^ b.toNat := by
    intro b
    cases b <;> simp [pieriStateWeight]
  simp only [h, Finset.prod_pow_eq_pow_sum, pieriStateSize]

def pieriBond (q : Rˣ) (d : ℤ) (s t : Bool) : R :=
  if t && !s then 1 - pieriPower q d else 1

theorem pieriLeftMatrix_gaussian (q : Rˣ) (z : R) (a b : ℤ) (ha : 0 ≤ a)
    (s t : Bool) :
    pieriLeftMatrix z (intGaussianPieriEdge q a b ha) s t =
      pieriW q a b s t * pieriStateWeight z t := by
  obtain ⟨h00, h11, h10, h01⟩ := pieriW_entries q a b ha
  cases s <;> cases t <;>
    simp only [h00, h11, h10, h01, pieriLeftMatrix, intGaussianPieriEdge,
      pieriStateWeight, Bool.false_eq_true, ↓reduceIte, mul_one] <;> ring

theorem pieriRightMatrix_gaussian (q : Rˣ) (z : R) (ap bp a b : ℤ) (ha : 0 ≤ a)
    (s t : Bool) :
    pieriRightMatrix z (pieriPower q (ap - bp)) (intGaussianPieriEdge q a b ha) s t =
      pieriBond q (ap - bp + b + 1) s t * pieriStateWeight z t *
        intQbinom (q : R) a (b + pieriBit t) := by
  have hp : pieriPower q (ap - bp + b + 1) =
      pieriPower q (ap - bp) * pieriPower q (b + 1) := by
    rw [← pieriPower_add]
    congr 1
    omega
  cases s <;> cases t <;>
    simp [pieriRightMatrix, intGaussianPieriEdge, pieriStateWeight, pieriBond,
      pieriBit, hp]

theorem pieri_gaussian_left_path (q : Rˣ) (z : R) (n : ℕ)
    (a b : Fin (n + 1) → ℤ) (ha : ∀ i, 0 ≤ a i) (s : Fin (n + 2) → Bool) :
    pieriSelect (1, z) (s 0) *
      (∏ i, pieriLeftMatrix z (intGaussianPieriEdge q (a i) (b i) (ha i))
        (s i.castSucc) (s i.succ)) =
    z ^ pieriStateSize s * ∏ i, pieriW q (a i) (b i) (s i.castSucc) (s i.succ) := by
  simp_rw [pieriLeftMatrix_gaussian]
  rw [Finset.prod_mul_distrib, ← pieriStateWeight_prod,
    Fin.prod_univ_succ (fun i => pieriStateWeight z (s i))]
  have h : pieriSelect (1, z) (s 0) = pieriStateWeight z (s 0) := rfl
  rw [h]
  ring

theorem pieri_gaussian_right_path (q : Rˣ) (z : R) (n : ℕ)
    (a b : Fin (n + 1) → ℤ) (ha : ∀ i, 0 ≤ a i) (t : Fin (n + 1) → Bool) :
    pieriSelect
        (intQbinom (q : R) (a 0) (b 0), z * intQbinom (q : R) (a 0) (b 0 + 1)) (t 0) *
      (∏ i : Fin n, pieriRightMatrix z (pieriPower q (a i.castSucc - b i.castSucc))
        (intGaussianPieriEdge q (a i.succ) (b i.succ) (ha i.succ))
        (t i.castSucc) (t i.succ)) =
    z ^ pieriStateSize t *
      (∏ i, intQbinom (q : R) (a i) (b i + pieriBit (t i))) *
      ∏ i : Fin n, pieriBond q (a i.castSucc - b i.castSucc + b i.succ + 1)
        (t i.castSucc) (t i.succ) := by
  simp_rw [pieriRightMatrix_gaussian]
  have h : pieriSelect
      (intQbinom (q : R) (a 0) (b 0), z * intQbinom (q : R) (a 0) (b 0 + 1)) (t 0) =
      pieriStateWeight z (t 0) * intQbinom (q : R) (a 0) (b 0 + pieriBit (t 0)) := by
    cases t 0 <;> simp [pieriSelect, pieriStateWeight, pieriBit]
  rw [h, ← pieriStateWeight_prod]
  simp only [Finset.prod_mul_distrib, Fin.prod_univ_succ]
  ring

/-- E-step, with all integer boundary cases included and no restriction on chain length. -/
theorem pieri_e_step (q : Rˣ) (z : R) (n : ℕ)
    (a b : Fin (n + 1) → ℤ) (ha : ∀ i, 0 ≤ a i) :
    (∑ s : Fin (n + 2) → Bool, z ^ pieriStateSize s *
      ∏ i, pieriW q (a i) (b i) (s i.castSucc) (s i.succ)) =
    (1 + z) * ∑ t : Fin (n + 1) → Bool, z ^ pieriStateSize t *
      (∏ i, intQbinom (q : R) (a i) (b i + pieriBit (t i))) *
      ∏ i : Fin n, pieriBond q (a i.castSucc - b i.castSucc + b i.succ + 1)
        (t i.castSucc) (t i.succ) := by
  have h := pieri_transfer_binary z n
    (fun i => intGaussianPieriEdge q (a i) (b i) (ha i))
  simp_rw [pieri_gaussian_left_path] at h
  change _ = (1 + z) * ∑ t : Fin (n + 1) → Bool,
    pieriSelect
        (intQbinom (q : R) (a 0) (b 0), z * intQbinom (q : R) (a 0) (b 0 + 1)) (t 0) *
      ∏ i : Fin n, pieriRightMatrix z (pieriPower q (a i.castSucc - b i.castSucc))
        (intGaussianPieriEdge q (a i.succ) (b i.succ) (ha i.succ))
        (t i.castSucc) (t i.succ) at h
  simpa only [pieri_gaussian_right_path] using h

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.pieriStateWeight_prod
#print axioms VOA.DeligneAudit.D4Char.pieriLeftMatrix_gaussian
#print axioms VOA.DeligneAudit.D4Char.pieriRightMatrix_gaussian
#print axioms VOA.DeligneAudit.D4Char.pieri_gaussian_left_path
#print axioms VOA.DeligneAudit.D4Char.pieri_gaussian_right_path
#print axioms VOA.DeligneAudit.D4Char.pieri_e_step
