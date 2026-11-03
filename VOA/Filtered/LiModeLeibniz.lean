import VOA.Filtered.LiMultiplicativity

/-!
# The one-step Li estimate for the vertex-mode Leibniz rule

All correction terms in the commutator formula lie one Li step above the
principal n-mode action on the commutative product. This is the state-level
input for the Poisson vertex Leibniz identity, with no character assumptions.
-/

namespace VOA
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The Leibniz defect of a nonnegative mode gains one Li-filtration step. -/
theorem adjointGfil_mode_leibniz_defect (W : VertexOperatorAlgebra V)
    {p q r : ℤ} (n : ℕ) {x y z : V}
    (hx : x ∈ Gfil (adjointWeakModule W) ({W.vacuum} : Set V) p)
    (hy : y ∈ Gfil (adjointWeakModule W) ({W.vacuum} : Set V) q)
    (hz : z ∈ Gfil (adjointWeakModule W) ({W.vacuum} : Set V) r) :
    W.smul x (n : ℤ) (W.smul y (-1) z) -
        W.smul (W.smul x (n : ℤ) y) (-1) z -
        W.smul y (-1) (W.smul x (n : ℤ) z) ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V) (p + q + r - (n : ℤ) + 1) := by
  let F : ℤ → V := fun j => cbz (n : ℤ) j •
    W.smul (W.smul x j y) ((n : ℤ) - 1 - j) z
  have hsupport : Function.support F ⊆ (Finset.Icc 0 (n : ℤ) : Set ℤ) := by
    intro j hj
    by_contra hj'
    simp only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hj'
    apply hj
    rcases hj' with hneg | hlarge
    · simp only [F, cbz_apply_neg _ hneg, zero_smul]
    · simp only [F, cbz_eq_zero_of_lt (by positivity) hlarge, zero_smul]
  have hcomm : W.smul x (n : ℤ) (W.smul y (-1) z) -
      W.smul y (-1) (W.smul x (n : ℤ) z) = ∑ j ∈ Finset.Icc 0 (n : ℤ), F j := by
    have h := mode_commutator (adjointWeakModule W) x y z (n : ℤ) (-1)
    change W.smul x (n : ℤ) (W.smul y (-1) z) -
      W.smul y (-1) (W.smul x (n : ℤ) z) = ∑ᶠ j, F j at h
    rw [finsum_eq_finsetSum_of_support_subset F hsupport] at h
    exact h
  have hnn : (n : ℤ) ∈ Finset.Icc 0 (n : ℤ) := by simp
  have hFn : F (n : ℤ) = W.smul (W.smul x (n : ℤ) y) (-1) z := by
    simp [F, cbz_natCast_eq_choose (le_refl n)]
  have hdefect : W.smul x (n : ℤ) (W.smul y (-1) z) -
        W.smul (W.smul x (n : ℤ) y) (-1) z -
        W.smul y (-1) (W.smul x (n : ℤ) z) =
      ∑ j ∈ (Finset.Icc 0 (n : ℤ)).erase (n : ℤ), F j := by
    calc
      _ = (W.smul x (n : ℤ) (W.smul y (-1) z) -
          W.smul y (-1) (W.smul x (n : ℤ) z)) -
          W.smul (W.smul x (n : ℤ) y) (-1) z := by abel
      _ = _ := by
        rw [hcomm, ← Finset.sum_erase_add _ F hnn, hFn, add_sub_cancel_right]
  rw [hdefect]
  apply Submodule.sum_mem
  intro j hj
  obtain ⟨hjn, hjmem⟩ := Finset.mem_erase.mp hj
  obtain ⟨hj0, hjn'⟩ := Finset.mem_Icc.mp hjmem
  have hjlt : j < (n : ℤ) := by omega
  have hmode : 0 ≤ (n : ℤ) - 1 - j := by omega
  have hxy := adjointGfil_smul_nonneg_mem W j.toNat hx hy
  rw [Int.toNat_of_nonneg hj0] at hxy
  have hout := adjointGfil_smul_nonneg_mem W ((n : ℤ) - 1 - j).toNat hxy hz
  rw [Int.toNat_of_nonneg hmode] at hout
  have heq : (p + q - j) + r - ((n : ℤ) - 1 - j) = p + q + r - (n : ℤ) + 1 := by ring
  rw [heq] at hout
  exact Submodule.smul_mem _ _ hout

/-- Natural-index form of the state-level Li Leibniz estimate. -/
theorem liFiltration_mode_leibniz_defect (W : VertexOperatorAlgebra V)
    {p q r n : ℕ} (hn : n ≤ p + q + r) {x y z : V}
    (hx : x ∈ liFiltration W p) (hy : y ∈ liFiltration W q)
    (hz : z ∈ liFiltration W r) :
    W.smul x (n : ℤ) (W.smul y (-1) z) -
        W.smul (W.smul x (n : ℤ) y) (-1) z -
        W.smul y (-1) (W.smul x (n : ℤ) z) ∈
      liFiltration W (p + q + r - n + 1) := by
  have h := adjointGfil_mode_leibniz_defect W n hx hy hz
  simpa only [liFiltration, Nat.cast_add, Nat.cast_sub hn, Nat.cast_one] using h

end VOA
