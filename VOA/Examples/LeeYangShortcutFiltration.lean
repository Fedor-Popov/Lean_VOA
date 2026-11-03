import VOA.Examples.VirasoroGoodFiltration
import VOA.Core.SimpleImage

/-!
# The generator test for filtered Virasoro images

A conformal vector of filtration degree at most one controls the entire
Virasoro PBW filtration, provided the target flag is compatible with modes.
The theorem applies to any central charge and does not require simplicity,
an identification of the target, or a character computation.

The Kähler geometry used by the transfer assembly supplies only a bigrading
and ghost-number compatibility. Connecting its filtration to a target VOA
flag compatible with modes remains a separate geometric obligation.
-/

namespace VOA.LeeYangShortcut

open VirModule VirSimple VirGoodFil VertexOperatorAlgebra

universe u
variable {E : Type u} [AddCommGroup E] [Module ℂ E]
variable {c : ℂ} {W : VertexOperatorAlgebra E}

/-- Every creation word has filtered degree at most its length if the vacuum
has degree zero and applying a Virasoro creation mode raises degree by at
most one. This is the minimal operator-level PBW induction. -/
theorem negWord_image_mem_of_creation
    (φ : VirUniv c →ₗ[ℂ] E) (F : ℕ → ℤ → Submodule ℂ E)
    (hvac : φ (vacVec c) ∈ F 0 0)
    (hstep : ∀ (p : ℕ) (n : ℤ) (i : ℕ) (x : VirUniv c),
      φ x ∈ F p n → φ (Lop c (-(i : ℤ) - 2) x) ∈ F (p + 1) (n + i + 2))
    (w : List ℕ) : φ (negWordVir c w) ∈ F w.length (energyVir w : ℤ) := by
  induction w with
  | nil => exact hvac
  | cons i w ih =>
      simpa only [negWordVir_cons, List.length_cons, energyVir_cons,
        Nat.cast_add, Nat.cast_ofNat, add_comm, add_left_comm, add_assoc] using
        hstep w.length (energyVir w : ℤ) i (negWordVir c w) ih

/-- The vacuum and creation-mode tests imply filtering of every universal
PBW prefix. Sorted-word independence is not needed. -/
theorem virFil_map_le_of_creation
    (φ : VirUniv c →ₗ[ℂ] E) (F : ℕ → ℤ → Submodule ℂ E)
    (hmono : ∀ n, Monotone fun p => F p n)
    (hvac : φ (vacVec c) ∈ F 0 0)
    (hstep : ∀ (p : ℕ) (n : ℤ) (i : ℕ) (x : VirUniv c),
      φ x ∈ F p n → φ (Lop c (-(i : ℤ) - 2) x) ∈ F (p + 1) (n + i + 2))
    (p : ℕ) (n : ℤ) : (virFil c p n).map φ ≤ F p n := by
  rw [Submodule.map_le_iff_le_comap, virFil, Submodule.span_le]
  rintro _ ⟨w, -, hn, hp, rfl⟩
  change φ (negWordVir c w) ∈ F p n
  have hw := negWord_image_mem_of_creation φ F hvac hstep w
  rw [hn] at hw
  exact hmono n hp hw

/-- Mode compatibility and the single conformal-vector degree bound provide
the creation-mode test. -/
theorem virFil_map_le_of_conformal_degree_one
    (φ : VirUniv c →ₗ[ℂ] E) (F : GradedFlag W)
    (hmodes : F.ModeCompatible)
    (hω : W.conformalVector ∈ F.piece 1 2)
    (hvac : φ (vacVec c) = W.vacuum)
    (hL : ∀ m x, φ (Lop c m x) = W.L m (φ x))
    (p : ℕ) (n : ℤ) : (virFil c p n).map φ ≤ F.piece p n := by
  apply virFil_map_le_of_creation φ F.piece (fun n => F.monotone n)
  · rw [hvac, F.vacuum_zero]
    exact Submodule.mem_span_singleton_self _
  · intro q m i x hx
    rw [hL]
    have hm := hmodes (k := -(i : ℤ) - 2 + 1) hω hx
    have he : (2 : ℤ) + m - (-(i : ℤ) - 2 + 1) - 1 = m + i + 2 := by ring
    simpa only [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def,
      Nat.add_comm 1 q, he] using hm

/-- A conformal VOA homomorphism is filtered as soon as its target conformal
vector has degree at most one in a mode-compatible flag. -/
theorem virFil_map_le_of_hom
    (φ : VirUniv c →ₗ[ℂ] E)
    (hφ : IsVOAHom (virasoroVOA c) W φ)
    (hconformal : φ (virasoroVOA c).conformalVector = W.conformalVector)
    (F : GradedFlag W) (hmodes : F.ModeCompatible)
    (hω : W.conformalVector ∈ F.piece 1 2)
    (p : ℕ) (n : ℤ) : (virFil c p n).map φ ≤ F.piece p n := by
  apply virFil_map_le_of_conformal_degree_one φ F hmodes hω hφ.map_vacuum
  intro m x
  have h := hφ.map_L hconformal m x
  simpa only [VertexOperatorAlgebra.L_def, virasoroVOA, virYA_omega,
    mode_YomegaVir, add_sub_cancel_right] using h

/-- If the universal map descends through the simple quotient, the same
generator test gives filtering for the actual simple Virasoro PBW flag. -/
theorem goodFil_map_le_of_factor
    (φ : VirUniv c →ₗ[ℂ] E)
    (ψ : (VirUniv c ⧸ maxIdealVir c) →ₗ[ℂ] E)
    (hfactor : ψ.comp (maxIdealVir c).mkQ = φ)
    (F : ℕ → ℤ → Submodule ℂ E)
    (hfiltered : ∀ p n, (virFil c p n).map φ ≤ F p n)
    (p : ℕ) (n : ℤ) : (goodFil c p n).map ψ ≤ F p n := by
  rw [goodFil, ← Submodule.map_comp, hfactor]
  exact hfiltered p n

end VOA.LeeYangShortcut
