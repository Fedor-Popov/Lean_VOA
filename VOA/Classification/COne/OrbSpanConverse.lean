import VOA.Classification.COne.OrbSpanGlue
import VOA.Modules.FiniteGenerationProof

/-! # OrbSpan: the graded descent is also necessary

If the seeds are homogeneous, `DongJiangVirasoroSpan` implies `GradedDescent` (project the
spanning expression to weight `N`; negative Virasoro words land in `lowerDesc N`, `O₂` is graded).
So the reductions of `OrbSpanGlue` lose nothing.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbSpan
open VOA VertexOperatorAlgebra OrbC2b OrbC2c
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

theorem L_mem_grading_conv {ℓ : ℤ} {v : V} (hv : v ∈ W.grading ℓ) (m : ℤ) :
    W.L m v ∈ W.grading (ℓ - m) := by
  have h := W.grading_mode W.conformalVector W.conformal_mem v hv (m + 1)
  rw [show (2 + ℓ - (m + 1) - 1) = ℓ - m from by ring] at h
  exact h

/-- Projection to weight `N` commutes with a negative Virasoro mode. -/
theorem piHom_L_neg (N : ℤ) (k : ℕ) (y : V) :
    piHom W N (W.L (-(k : ℤ) - 1) y) = W.L (-(k : ℤ) - 1) (piHom W (N - k - 1) y) := by
  have hy : y ∈ ⨆ i, W.grading i := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction W.grading
    (motive := fun y => piHom W N (W.L (-(k : ℤ) - 1) y) =
      W.L (-(k : ℤ) - 1) (piHom W (N - k - 1) y)) hy ?_ ?_ ?_
  · intro j y hy
    have hL : W.L (-(k : ℤ) - 1) y ∈ W.grading (j + k + 1) := by
      have := L_mem_grading_conv W hy (-(k : ℤ) - 1)
      rwa [show j - (-(k : ℤ) - 1) = j + k + 1 by ring] at this
    by_cases hj : j + k + 1 = N
    · rw [piHom_of_mem W (hj ▸ hL), piHom_of_mem W (show y ∈ W.grading (N - k - 1) by
        rw [show N - k - 1 = j by omega]; exact hy)]
    · rw [piHom_of_mem_ne W hj hL, piHom_of_mem_ne W (show j ≠ N - k - 1 by omega) hy,
        map_zero]
  · simp
  · intro y z hy hz
    simp only [map_add, hy, hz]

theorem piHom_virWord_mem (u v : V) (hT : ∀ t ∈ djSeedSet W u v, ∃ d, t ∈ W.grading d)
    (N : ℤ) (ks : List ℕ) {s : V} (hs : s ∈ djSeeds W u v) :
    piHom W N (virWord W ks s) ∈ O₂ W ⊔ Submodule.span ℂ (djSeedSet W u v) ⊔ lowerDesc W N := by
  cases ks with
  | nil =>
    rcases hs with hs | hs
    · obtain ⟨d, hd⟩ := hT s hs
      by_cases hdN : d = N
      · subst hdN
        rw [virWord, piHom_of_mem W hd]
        exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span hs))
      · rw [virWord, piHom_of_mem_ne W hdN hd]; exact Submodule.zero_mem _
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (piHom_maps_O₂ W N hs))
  | cons k ks =>
    rw [virWord, piHom_L_neg]
    apply Submodule.mem_sup_right
    exact Submodule.subset_span ⟨k, _, piHom_mem W _ _, rfl⟩

/-- **Necessity.** With homogeneous seeds, the Dong--Jiang span gives the graded descent. -/
theorem gradedDescent_of_dongJiang (u v : V) (hT : ∀ t ∈ djSeedSet W u v, ∃ d, t ∈ W.grading d)
    (h : DongJiangVirasoroSpan W u v) : GradedDescent W (djSeedSet W u v) := by
  intro N x hx
  have hall : ∀ y ∈ djSpan W u v,
      piHom W N y ∈ O₂ W ⊔ Submodule.span ℂ (djSeedSet W u v) ⊔ lowerDesc W N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨ks, ⟨s, hs⟩⟩, rfl⟩ := hz
      exact piHom_virWord_mem W u v hT N ks hs
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy
  have hx' := hall x (by rw [show djSpan W u v = ⊤ from h]; trivial)
  rwa [piHom_of_mem W hx] at hx'

theorem djSeedSet_homogeneous {u v : V} {a b : ℤ} (hu : u ∈ W.grading a) (hv : v ∈ W.grading b) :
    ∀ t ∈ djSeedSet W u v, ∃ d, t ∈ W.grading d := by
  rintro t (ht | ⟨n, rfl⟩)
  · rcases ht with rfl | rfl | rfl
    · exact ⟨0, W.vacuum_mem⟩
    · exact ⟨a, hu⟩
    · exact ⟨b, hv⟩
  · exact ⟨_, W.smul_mem_grading hu hu n⟩

/-- **Exactness of the primary reduction** (given the primary decomposition). -/
theorem dongJiangVirasoroSpan_iff_primary (hD : VirPrimaryDecomp W) {u v : V} {a b : ℤ}
    (hu : u ∈ W.grading a) (hv : v ∈ W.grading b) :
    DongJiangVirasoroSpan W u v ↔ PrimaryC2Reduction W (djSeedSet W u v) := by
  constructor
  · intro h N
    exact le_trans inf_le_left
      (gradedDescent_of_dongJiang W u v (djSeedSet_homogeneous W hu hv) h N)
  · exact dongJiangVirasoroSpan_of_primary W u v hD

end VOA.Classification.COne.OrbSpan
