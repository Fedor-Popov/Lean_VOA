import VOA.DeligneAudit.SL4TFullFlagRank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Top-row remainder minors and the full-flag stratum quotients -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {A D : Type*} [CommRing A] [CommRing D]

/-- A top-row minor, with arbitrary column indices; repeated columns give zero. -/
def remainderTopMinor (xs : List A) (N j : ℕ) (cols : Fin j → ℕ) : A :=
  Matrix.det fun a b : Fin j =>
    alphabetPowerRemainder xs (N + cols b) (xs.length - j + a.val)

/-- The ideal of all minors on the highest `j` rows of the remainder matrix. -/
def remainderTopIdeal (xs : List A) (N j : ℕ) : Ideal A :=
  Ideal.span (Set.range (remainderTopMinor xs N j))

theorem remainderTopMinor_mem (xs : List A) (N j : ℕ) (cols : Fin j → ℕ) :
    remainderTopMinor xs N j cols ∈ remainderTopIdeal xs N j :=
  Ideal.subset_span ⟨cols, rfl⟩

theorem remainderTopMinor_map (f : A →+* D) (xs : List A) (N j : ℕ)
    (cols : Fin j → ℕ) :
    f (remainderTopMinor xs N j cols) = remainderTopMinor (xs.map f) N j cols := by
  rw [remainderTopMinor, RingHom.map_det]
  unfold remainderTopMinor
  congr 1
  ext a b
  exact (alphabetPowerRemainder_map f xs _ _).trans (by rw [List.length_map])

theorem remainderTopIdeal_map (f : A →+* D) (xs : List A) (N j : ℕ) :
    (remainderTopIdeal xs N j).map f = remainderTopIdeal (xs.map f) N j := by
  rw [remainderTopIdeal, Ideal.map_span, ← Set.range_comp]
  simp only [Function.comp_def, remainderTopMinor_map, remainderTopIdeal]

/-- Increasing the cutoff only removes available columns from the same remainder matrix. -/
theorem remainderTopIdeal_cutoff_mono (xs : List A) (N j : ℕ) :
    remainderTopIdeal xs (N + 1) j ≤ remainderTopIdeal xs N j := by
  apply Ideal.span_le.mpr
  rintro x ⟨cols, rfl⟩
  have he : remainderTopMinor xs (N + 1) j cols =
      remainderTopMinor xs N j (fun b => cols b + 1) := by
    unfold remainderTopMinor
    congr 1
    funext a b
    rw [show N + 1 + cols b = N + (cols b + 1) by omega]
  rw [he]
  exact remainderTopMinor_mem xs N j _

/-- Below the characteristic degree, powers reduce to themselves. -/
theorem alphabetPowerRemainder_of_small (xs : List A) (m l : ℕ) (hm : m < xs.length) :
    alphabetPowerRemainder xs m l = if l = m then 1 else 0 := by
  nontriviality A
  rw [alphabetPowerRemainder, (Polynomial.modByMonic_eq_self_iff
    (alphabetCharacteristic_monic xs)).mpr, Polynomial.coeff_X_pow]
  rw [Polynomial.degree_X_pow,
    Polynomial.degree_eq_natDegree (alphabetCharacteristic_monic xs).ne_zero,
    alphabetCharacteristic_natDegree]
  exact_mod_cast hm

/-- If the cutoff starts below the top rows, consecutive columns give a unit minor. -/
theorem remainderTopIdeal_eq_top (xs : List A) (N j : ℕ) (hj : j ≤ xs.length)
    (hN : N + j ≤ xs.length) : remainderTopIdeal xs N j = ⊤ := by
  classical
  apply (Ideal.eq_top_iff_one _).mpr
  let cols : Fin j → ℕ := fun b => xs.length - j + b.val - N
  have hm : remainderTopMinor xs N j cols = 1 := by
    unfold remainderTopMinor
    have he : (fun a b : Fin j => alphabetPowerRemainder xs (N + cols b)
        (xs.length - j + a.val)) = (1 : Matrix (Fin j) (Fin j) A) := by
      ext a b
      rw [alphabetPowerRemainder_of_small xs _ _ (by dsimp [cols]; omega),
        Matrix.one_apply]
      congr 1
      simp only [cols]
      apply propext
      constructor
      · intro h
        apply Fin.ext
        omega
      · intro h
        subst b
        omega
    rw [he, Matrix.det_one]
  rw [← hm]
  exact remainderTopMinor_mem xs N j cols

/-- The root alphabet selected by a set of full-flag positions. -/
def fullFlagSubalphabet {B : ℕ} (Y : Finset (Fin B)) :
    List (MvPolynomial (Fin B) ℂ) := Y.toList.map MvPolynomial.X

/-- The full-flag quotient with a top-minor stratum imposed. -/
abbrev FullFlagStratumRing (B N j : ℕ) (Y : Finset (Fin B)) :=
  MvPolynomial (Fin B) ℂ ⧸
    (fullFlagTruncationIdeal B N ⊔ remainderTopIdeal (fullFlagSubalphabet Y) N j)

theorem fullFlagStratum_finite (B N j : ℕ) (Y : Finset (Fin B)) :
    FiniteDimensional ℂ (FullFlagStratumRing B N j Y) := by
  letI := fullFlag_finite B N
  exact Module.Finite.of_surjective
    (Ideal.Quotient.factorₐ ℂ
      (show fullFlagTruncationIdeal B N ≤
        fullFlagTruncationIdeal B N ⊔ remainderTopIdeal (fullFlagSubalphabet Y) N j from
          le_sup_left)).toLinearMap
    (Ideal.Quotient.factor_surjective le_sup_left)

/-- A labeled configuration with `k` doubled sites and `B - 2k` single sites. -/
abbrev FullFlagConfiguration (B k : ℕ) :=
  {f : Fin B → Fin (B - k) // ∀ a,
    (Finset.univ.filter fun i => f i = a).card = if a.val < k then 2 else 1}

/-- The number of doubled sites entirely contained in the chosen set of positions. -/
def fullFlagDoublesIn {B k : ℕ} (Y : Finset (Fin B)) (f : FullFlagConfiguration B k) : ℕ :=
  (Finset.univ.filter fun a => a.val < k ∧ ∀ i, f.val i = a → i ∈ Y).card

/-- The configurations below a top-minor stratum. -/
abbrev FullFlagStratumConfiguration (B k j : ℕ) (Y : Finset (Fin B)) :=
  {f : FullFlagConfiguration B k // fullFlagDoublesIn Y f < j}

/-- The remaining stratum-refined spanning bound, with its exact polynomial presentation
and its labeled configuration count. This is a proposition, not an asserted theorem. -/
def FullFlagStratumRankBound : Prop :=
  ∀ B k j (Y : Finset (Fin B)), 2 * k ≤ B →
    Module.finrank ℂ (FullFlagStratumRing B (B - k) j Y) ≤
      Nat.card (FullFlagStratumConfiguration B k j Y)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.remainderTopMinor_mem
#print axioms VOA.DeligneAudit.SL4T.remainderTopMinor_map
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_map
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_cutoff_mono
#print axioms VOA.DeligneAudit.SL4T.alphabetPowerRemainder_of_small
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_eq_top
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_finite
