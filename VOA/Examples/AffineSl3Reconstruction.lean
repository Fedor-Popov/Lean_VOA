/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3SugawaraResidue
import VOA.Examples.AffineSl3WordFields
import VOA.Core.ReconstructionExistence

/-!
# Basis-free state-field reconstruction for the actual sl3 vacuum

The eight-current word states span by actual matrix coordinates and the
general vacuum spanning theorem. Proved Sugawara translation covariance
then gives a well-defined all-states field assignment, with creation,
locality, regularity and translation covariance. Only k+3 nonzero is
required; no ordered-word independence or covariance premise remains.
This is not yet a proof of all conformal VOA axioms or simple rigidity.
-/
namespace VOA.AffineSl3
open VOA VOA.AffineLie Module
noncomputable section
set_option maxHeartbeats 4000000
/-- The identity field is `T`-covariant for any `T` (`[T, 1_m] = 0 = ∂_z 1`). -/
theorem idFieldA_DCovariant (k : ℂ) : Reconstruction.DCovariant (Ltrans k) (idFieldA k) := by
  have e : ∀ j : ℤ, idFieldA k j = if j = 0 then (1 : End ℂ (Vacuum k)) else 0 :=
    fun j => rfl
  intro m
  show Ltrans k * (idFieldA k m) - (idFieldA k m) * Ltrans k = ((m + 1 : ℤ)) • (idFieldA k (m + 1))
  rw [e m, e (m + 1)]
  split_ifs with h0 h1 h1
  · omega
  · simp
  · rw [show (m + 1 : ℤ) = 0 from h1]; simp
  · simp

/-- The generator fields `genFieldA = (i!)⁻¹ ∂_z^i Jᵃ(z)` inherit `T`-covariance from `Jᵃ(z)`. -/
theorem genFieldA_DCovariant (k : ℂ)
    (hJ : ∀ a : Fin 8, Reconstruction.DCovariant (Ltrans k) (Jfield k a)) (a : Fin 8) (i : ℕ) :
    Reconstruction.DCovariant (Ltrans k) (genFieldA k a i) := by
  rw [genFieldA]
  exact Reconstruction.DCovariant.smul ((i.factorial : ℂ)⁻¹)
    (Reconstruction.DCovariant.deriv_iterate (hJ a) i)

/-- Every iterated word field `YwordA k l` is `T`-covariant (induction over the word, the
`Core` `DCovariant.nprod` closure for the step, `idFieldA_DCovariant` for the base). -/
theorem YwordA_DCovariant (k : ℂ)
    (hJ : ∀ a : Fin 8, Reconstruction.DCovariant (Ltrans k) (Jfield k a)) :
    ∀ l : List (Fin 8 × ℕ), Reconstruction.DCovariant (Ltrans k) (YwordA k l)
  | [] => by rw [YwordA_nil]; exact idFieldA_DCovariant k
  | (ai :: rest) => by
      rw [YwordA_cons]
      exact Reconstruction.DCovariant.nprod (genFieldA_isField k ai.1 ai.2)
        (YwordA_isField k rest) (genFieldA_DCovariant k hJ ai.1 ai.2)
        (YwordA_DCovariant k hJ rest)

/-! ## §3  The word states span `Vacuum k` (`hspan` for the reconstruction)

The creation monomials `negWord` span `Vacuum k` (`negSpan_eq_top`); each is a `ℂ`-combination
of the basis-word states `wordStateA` (Chevalley-basis decomposition of each loop generator),
so the `wordStateA l` span — the cyclicity datum the reconstruction consumes. -/

/-- Chevalley-basis decomposition: `x = ∑_c x_c·eₐ`. -/
theorem basis_decomp (x : Sl3) : x = ∑ c : Fin 8, coordinates x c • generator c := by
  exact (reconstruct x).symm

/-- Each current mode `Jᵃ_{-n-1}` maps `span(range wordStateA)` into itself (a word state maps
to a longer word state). -/
theorem J_mem_span_wordState (k : ℂ) (a : Fin 8) (n : ℕ) {y : Vacuum k}
    (hy : y ∈ Submodule.span ℂ (Set.range (wordStateA k))) :
    J k a (-(n : ℤ) - 1) y ∈ Submodule.span ℂ (Set.range (wordStateA k)) := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, rfl⟩ := hz
      exact Submodule.subset_span ⟨(a, n) :: l, wordStateA_cons k (a, n) l⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add p q _ _ ihp ihq => rw [map_add]; exact Submodule.add_mem _ ihp ihq
  | smul c p _ ihp => rw [map_smul]; exact Submodule.smul_mem _ c ihp

/-- Every creation monomial `negWord L` lies in `span(range wordStateA)` (induction over the
word, basis-decomposing each loop generator). -/
theorem negWord_mem_span (k : ℂ) (L : List (Sl3 × ℕ)) :
    negWord form form_invariant k L ∈
      Submodule.span ℂ (Set.range (wordStateA k)) := by
  induction L with
  | nil => rw [negWord_nil]; exact Submodule.subset_span ⟨[], rfl⟩
  | cons xn L' ih =>
      obtain ⟨x, n⟩ := xn
      rw [negWord_cons]
      have heq : vacuumRho form form_invariant k
            (ofLoop form form_invariant x (-(n : ℤ) - 1))
            (negWord form form_invariant k L')
          = ∑ c : Fin 8, coordinates x c • (J k c (-(n : ℤ) - 1)
              (negWord form form_invariant k L')) := by
        rw [← loopMul_apply]
        conv_lhs => rw [basis_decomp x]
        rw [map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [map_smul, LinearMap.smul_apply]
        rfl
      rw [heq]
      exact Submodule.sum_mem _ (fun c _ =>
        Submodule.smul_mem _ _ (J_mem_span_wordState k c n ih))

/-- **The word states span** `Vacuum k` (`hspan`): `span(range wordStateA) = ⊤`. -/
theorem wordStateA_span (k : ℂ) : Submodule.span ℂ (Set.range (wordStateA k)) = ⊤ := by
  rw [eq_top_iff, ← negSpan_eq_top form form_invariant k, negSpan, Submodule.span_le]
  rintro _ ⟨L, rfl⟩
  exact negWord_mem_span k L

/-- At every noncritical level, the actual word fields descend to an all-states
linear field assignment. All creation, locality, regularity and translation
conditions are proved internally; no covariance or PBW premise remains. -/
theorem affineYA_exists (k : ℂ) (hk : k+3 ≠ 0) :
    ∃ YA : Vacuum k →ₗ[ℂ] FormalDist (End ℂ (Vacuum k)),
      (∀ l : List (Fin 8 × ℕ), YA (wordStateA k l) = YwordA k l) ∧
      (∀ u : Vacuum k, IsField (YA u)) ∧
      (∀ u v : Vacuum k, Local (YA u) (YA v)) ∧
      (∀ u : Vacuum k, (YA u) 0 (vacuumA k) = u) ∧
      (∀ u : Vacuum k, ∀ q : ℤ, q < 0 → (YA u) q (vacuumA k) = 0) ∧
      (∀ u : Vacuum k, Reconstruction.DCovariant (Ltrans k) (YA u)) :=
  Reconstruction.reconstruct (vacuumA k) (wordStateA k) (YwordA k) (Ltrans k)
    (wordStateA_span k) (YwordA_isField k) (YwordA_local k)
    (fun l => YwordA_vacuum_base k l) (fun l q hq => YwordA_vacuum_neg k l hq)
    (Ltrans_vacuum k) (YwordA_DCovariant k (SugawaraCov.Jfield_DCovariant k hk))


end
end VOA.AffineSl3
