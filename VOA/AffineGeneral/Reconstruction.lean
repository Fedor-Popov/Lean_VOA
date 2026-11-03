/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov, Leonardo Rastelli
-/
import VOA.AffineGeneral.SugawaraResidue
import VOA.AffineGeneral.WordFields
import VOA.Core.ReconstructionExistence

/-!
# Basis-free state-field reconstruction for the actual sl3 vacuum

*General-`𝔤` port* of `VOA/Examples/AffineSl3Reconstruction.lean` (generated mechanically from that file):
the index type is `ι`, the Lie data is `D : LieData κ ι`, the dual Coxeter number is `D.h`.  Where the
text below says sl₃, `Fin 8`, `6` or `3`, read `𝔤`, `ι`, `2 * D.h` and `D.h`.

The eight-current word states span by actual matrix coordinates and the
general vacuum spanning theorem. Proved Sugawara translation covariance
then gives a well-defined all-states field assignment, with creation,
locality, regularity and translation covariance. Only k+3 nonzero is
required; no ordered-word independence or covariance premise remains.
This is not yet a proof of all conformal VOA axioms or simple rigidity.
-/
namespace VOA.AffineGeneral

open LieData
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (D : LieData κ ι)
open VOA VOA.AffineLie Module
noncomputable section
set_option maxHeartbeats 4000000
/-- The identity field is `T`-covariant for any `T` (`[T, 1_m] = 0 = ∂_z 1`). -/
theorem idFieldA_DCovariant (k : ℂ) : Reconstruction.DCovariant (Ltrans D k) (idFieldA D k) := by
  have e : ∀ j : ℤ, idFieldA D k j = if j = 0 then (1 : End ℂ (Vacuum D k)) else 0 :=
    fun j => rfl
  intro m
  show Ltrans D k * (idFieldA D k m) - (idFieldA D k m) * Ltrans D k = ((m + 1 : ℤ)) • (idFieldA D k (m + 1))
  rw [e m, e (m + 1)]
  split_ifs with h0 h1 h1
  · omega
  · simp
  · rw [show (m + 1 : ℤ) = 0 from h1]; simp
  · simp

/-- The generator fields `genFieldA = (i!)⁻¹ ∂_z^i Jᵃ(z)` inherit `T`-covariance from `Jᵃ(z)`. -/
theorem genFieldA_DCovariant (k : ℂ)
    (hJ : ∀ a : ι, Reconstruction.DCovariant (Ltrans D k) (Jfield D k a)) (a : ι) (i : ℕ) :
    Reconstruction.DCovariant (Ltrans D k) (genFieldA D k a i) := by
  rw [genFieldA]
  exact Reconstruction.DCovariant.smul ((i.factorial : ℂ)⁻¹)
    (Reconstruction.DCovariant.deriv_iterate (hJ a) i)

/-- Every iterated word field `YwordA k l` is `T`-covariant (induction over the word, the
`Core` `DCovariant.nprod` closure for the step, `idFieldA_DCovariant` for the base). -/
theorem YwordA_DCovariant (k : ℂ)
    (hJ : ∀ a : ι, Reconstruction.DCovariant (Ltrans D k) (Jfield D k a)) :
    ∀ l : List (ι × ℕ), Reconstruction.DCovariant (Ltrans D k) (YwordA D k l)
  | [] => by rw [YwordA_nil]; exact idFieldA_DCovariant D k
  | (ai :: rest) => by
      rw [YwordA_cons]
      exact Reconstruction.DCovariant.nprod (genFieldA_isField D k ai.1 ai.2)
        (YwordA_isField D k rest) (genFieldA_DCovariant D k hJ ai.1 ai.2)
        (YwordA_DCovariant k hJ rest)

/-! ## §3  The word states span `Vacuum k` (`hspan` for the reconstruction)

The creation monomials `negWord` span `Vacuum k` (`negSpan_eq_top`); each is a `ℂ`-combination
of the basis-word states `wordStateA` (Chevalley-basis decomposition of each loop generator),
so the `wordStateA l` span — the cyclicity datum the reconstruction consumes. -/

/-- Chevalley-basis decomposition: `x = ∑_c x_c·eₐ`. -/
theorem basis_decomp (x : 𝔤) : x = ∑ c : ι, coordinates D x c • D.generator c := by
  exact (reconstruct D x).symm

/-- Each current mode `Jᵃ_{-n-1}` maps `span(range wordStateA)` into itself (a word state maps
to a longer word state). -/
theorem J_mem_span_wordState (k : ℂ) (a : ι) (n : ℕ) {y : Vacuum D k}
    (hy : y ∈ Submodule.span ℂ (Set.range (wordStateA D k))) :
    J D k a (-(n : ℤ) - 1) y ∈ Submodule.span ℂ (Set.range (wordStateA D k)) := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, rfl⟩ := hz
      exact Submodule.subset_span ⟨(a, n) :: l, wordStateA_cons D k (a, n) l⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add p q _ _ ihp ihq => rw [map_add]; exact Submodule.add_mem _ ihp ihq
  | smul c p _ ihp => rw [map_smul]; exact Submodule.smul_mem _ c ihp

/-- Every creation monomial `negWord L` lies in `span(range wordStateA)` (induction over the
word, basis-decomposing each loop generator). -/
theorem negWord_mem_span (k : ℂ) (L : List (𝔤 × ℕ)) :
    negWord κ D.invariant k L ∈
      Submodule.span ℂ (Set.range (wordStateA D k)) := by
  induction L with
  | nil => rw [negWord_nil]; exact Submodule.subset_span ⟨[], rfl⟩
  | cons xn L' ih =>
      obtain ⟨x, n⟩ := xn
      rw [negWord_cons]
      have heq : vacuumRho κ D.invariant k
            (ofLoop κ D.invariant x (-(n : ℤ) - 1))
            (negWord κ D.invariant k L')
          = ∑ c : ι, coordinates D x c • (J D k c (-(n : ℤ) - 1)
              (negWord κ D.invariant k L')) := by
        rw [← loopMul_apply]
        conv_lhs => rw [basis_decomp D x]
        rw [map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [map_smul, LinearMap.smul_apply]
        rfl
      rw [heq]
      exact Submodule.sum_mem _ (fun c _ =>
        Submodule.smul_mem _ _ (J_mem_span_wordState D k c n ih))

/-- **The word states span** `Vacuum k` (`hspan`): `span(range wordStateA) = ⊤`. -/
theorem wordStateA_span (k : ℂ) : Submodule.span ℂ (Set.range (wordStateA D k)) = ⊤ := by
  rw [eq_top_iff, ← negSpan_eq_top κ D.invariant k, negSpan, Submodule.span_le]
  rintro _ ⟨L, rfl⟩
  exact negWord_mem_span D k L

/-- At every noncritical level, the actual word fields descend to an all-states
linear field assignment. All creation, locality, regularity and translation
conditions are proved internally; no covariance or PBW premise remains. -/
theorem affineYA_exists (k : ℂ) (hk : k+D.h ≠ 0) :
    ∃ YA : Vacuum D k →ₗ[ℂ] FormalDist (End ℂ (Vacuum D k)),
      (∀ l : List (ι × ℕ), YA (wordStateA D k l) = YwordA D k l) ∧
      (∀ u : Vacuum D k, IsField (YA u)) ∧
      (∀ u v : Vacuum D k, Local (YA u) (YA v)) ∧
      (∀ u : Vacuum D k, (YA u) 0 (vacuumA D k) = u) ∧
      (∀ u : Vacuum D k, ∀ q : ℤ, q < 0 → (YA u) q (vacuumA D k) = 0) ∧
      (∀ u : Vacuum D k, Reconstruction.DCovariant (Ltrans D k) (YA u)) :=
  Reconstruction.reconstruct (vacuumA D k) (wordStateA D k) (YwordA D k) (Ltrans D k)
    (wordStateA_span D k) (YwordA_isField D k) (YwordA_local D k)
    (fun l => YwordA_vacuum_base D k l) (fun l q hq => YwordA_vacuum_neg D k l hq)
    (Ltrans_vacuum D k) (YwordA_DCovariant D k (SugawaraCov.Jfield_DCovariant D k hk))


end
end VOA.AffineGeneral
