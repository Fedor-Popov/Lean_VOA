import VOA.Classification.COne.OrbOctaRProbe

/-! Only two negative-mode images have to be tested by a coefficient functional.
This is a statement about actual Virasoro operators, independent of a Fock evaluator. -/

set_option Elab.async false

noncomputable section
namespace VOA.Classification.COne.OrbOctaR
open VOA VertexOperatorAlgebra OrbC2c

section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (A : VertexOperatorAlgebra V)

def twoBadRanges : Submodule ℂ V := (A.L (-1)).range ⊔ (A.L (-3)).range

private theorem negative_comm (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (x : V) :
    A.L (-(m : ℤ)) (A.L (-(n : ℤ)) x) -
      A.L (-(n : ℤ)) (A.L (-(m : ℤ)) x) =
        ((n : ℂ) - m) • A.L (-((m + n : ℕ) : ℤ)) x := by
  have h := LinearMap.congr_fun (A.L_virasoro (-(m : ℤ)) (-(n : ℤ))) x
  rw [if_neg (by omega), add_zero] at h
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply] at h
  simpa only [Int.cast_neg, Int.cast_natCast, Nat.cast_add, neg_sub_neg, neg_add] using h

private theorem neg_three_range (n : ℕ) (hn : 3 ≤ n) (x : V) :
    A.L (-(n : ℤ)) x ∈ twoBadRanges A := by
  induction n, hn using Nat.le_induction generalizing x with
  | base => exact Submodule.mem_sup_right ⟨x, rfl⟩
  | succ n hn ih =>
    have h1 : A.L (-1) (A.L (-(n : ℤ)) x) ∈ twoBadRanges A :=
      Submodule.mem_sup_left ⟨_, rfl⟩
    have h2 := ih (A.L (-1) x)
    have h := Submodule.sub_mem _ h1 h2
    have hc := negative_comm A 1 n (by omega) (by omega) x
    norm_num only [Nat.cast_one, neg_add_rev, Nat.cast_add] at hc
    rw [hc] at h
    have hn0 : (n : ℂ) - 1 ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast (show n ≠ 1 by omega)
    have hh := (Submodule.smul_mem_iff _ hn0).mp h
    simpa only [Nat.cast_add, Nat.cast_one, neg_add_rev, add_comm] using hh

private theorem neg_two_preserves {x : V} (hx : x ∈ twoBadRanges A) :
    A.L (-2) x ∈ twoBadRanges A := by
  obtain ⟨u, ⟨v, rfl⟩, w, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  apply Submodule.add_mem
  · have hc := negative_comm A 2 1 (by omega) (by omega) v
    norm_num at hc
    have h1 : A.L (-1) (A.L (-2) v) ∈ twoBadRanges A :=
      Submodule.mem_sup_left ⟨_, rfl⟩
    have h3 : A.L (-3) v ∈ twoBadRanges A := Submodule.mem_sup_right ⟨_, rfl⟩
    have he : A.L (-2) (A.L (-1) v) = A.L (-1) (A.L (-2) v) - A.L (-3) v := by
      rw [sub_eq_add_neg, ← hc]
      module
    rw [he]
    exact Submodule.sub_mem _ h1 h3
  · have hc := negative_comm A 2 3 (by omega) (by omega) z
    norm_num at hc
    have h3 : A.L (-3) (A.L (-2) z) ∈ twoBadRanges A :=
      Submodule.mem_sup_right ⟨_, rfl⟩
    have h5 := neg_three_range A 5 (by omega) z
    have he : A.L (-2) (A.L (-3) z) = A.L (-3) (A.L (-2) z) + A.L (-5) z := by
      rw [← hc]
      module
    rw [he]
    exact Submodule.add_mem _ h3 h5

/-- Every discarded word lies in the sum of the L(-1) and L(-3) images. -/
theorem virError_le_twoBadRanges (x : V) : virError A x ≤ twoBadRanges A := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨ks, hks⟩, rfl⟩
  change virWord A ks x ∈ twoBadRanges A
  induction ks with
  | nil => simp at hks
  | cons k ks ih =>
    rw [virWord]
    by_cases hk0 : k = 0
    · subst k
      exact Submodule.mem_sup_left ⟨_, rfl⟩
    by_cases hk1 : k = 1
    · subst k
      exact neg_two_preserves A (ih (by simpa using hks))
    · have h := neg_three_range A (k + 1) (by omega) (virWord A ks x)
      simpa only [Nat.cast_add, Nat.cast_one, neg_add, sub_eq_add_neg] using h

/-- A linear functional only has to annihilate these two operator images. -/
theorem virError_le_ker_of_two_modes (f : V →ₗ[ℂ] ℂ)
    (h1 : ∀ v, f (A.L (-1) v) = 0) (h3 : ∀ v, f (A.L (-3) v) = 0) (x : V) :
    virError A x ≤ f.ker := by
  refine le_trans (virError_le_twoBadRanges A x) (sup_le ?_ ?_)
  · rintro _ ⟨v, rfl⟩
    exact h1 v
  · rintro _ ⟨v, rfl⟩
    exact h3 v

end General
end VOA.Classification.COne.OrbOctaR
