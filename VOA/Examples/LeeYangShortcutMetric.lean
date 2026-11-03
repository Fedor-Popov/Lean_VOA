import VOA.Examples.LeeYangTransferAssemblyInputs
import VOA.Examples.VirasoroQuotientForm

/-!
# The precise metric obligations in the Virasoro-image shortcut

Normalized Virasoro-adjoint bilinear forms are unique on the simple Virasoro
quotient. This provides the final isometry step once the cohomology form has
been proved Virasoro-adjoint and vacuum-normalized.

Those conditions are not fields of the existing `ConcreteGUData`. Its
weightwise `GUData` admits the simultaneous change `B ↦ -B`, `ρ ↦ -ρ`,
which leaves the sesquilinear form, positivity, and every Kähler datum fixed.
The verified sign-change lemmas below record this missing compatibility;
they do not assert that the desired graded-unitarity endpoint is false.
-/

namespace VOA.LeeYangShortcut

open VertexOperatorAlgebra VirModule VirSimple VirQuotForm
open GradedUnitaryCohomology LeeYangTransferAssembly

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

noncomputable section

/-- The simple Virasoro quotient inherits uniqueness of normalized
Virasoro-adjoint forms from its universal quotient presentation. -/
theorem normalizedInvariantForm_eq_Bsimp (c : ℂ)
    (B : InvariantForm (virasoroSimple c)) (hB : B.Normalized) :
    B.form = (Bsimp c).form := by
  let Bpull : InvariantForm (virasoroVOA c) :=
    { form := B.form.compl₁₂ (maxIdealVir c).mkQ (maxIdealVir c).mkQ
      virasoro_adj := by
        intro n x y
        change B.form ((maxIdealVir c).mkQ ((virasoroVOA c).L n x))
            ((maxIdealVir c).mkQ y) =
          B.form ((maxIdealVir c).mkQ x)
            ((maxIdealVir c).mkQ ((virasoroVOA c).L (-n) y))
        rw [mkQ_L, mkQ_L]
        exact B.virasoro_adj n _ _ }
  have hnorm : Bpull.Normalized := hB
  have heq := VirFormSym.invariantForm_ext hnorm (Bpull_normalized c)
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := virasoroSimple_mkQ_surjective (c := c) x
  obtain ⟨y, rfl⟩ := virasoroSimple_mkQ_surjective (c := c) y
  exact LinearMap.congr_fun (LinearMap.congr_fun heq x) y

/-- A bilinear form on an arbitrary image space agrees with `Bsimp` on a
simple Virasoro parameterization if its pullback is Virasoro-adjoint and has
vacuum norm one. These are explicit mathematical obligations, independent
of finite-dimensional character arguments. -/
theorem imageForm_eq_Bsimp {K : Type u} [AddCommGroup K] [Module ℂ K]
    (c : ℂ) (β : LinearMap.BilinForm ℂ K)
    (i : (VirUniv c ⧸ maxIdealVir c) →ₗ[ℂ] K)
    (hadj : ∀ n x y,
      β (i ((virasoroSimple c).L n x)) (i y) =
        β (i x) (i ((virasoroSimple c).L (-n) y)))
    (hvac : β (i (virasoroSimple c).vacuum) (i (virasoroSimple c).vacuum) = 1)
    (x y : VirUniv c ⧸ maxIdealVir c) :
    β (i x) (i y) = (Bsimp c).form x y := by
  let B : InvariantForm (virasoroSimple c) :=
    { form := β.compl₁₂ i i
      virasoro_adj := hadj }
  have hB : B.Normalized := hvac
  exact LinearMap.congr_fun
    (LinearMap.congr_fun (normalizedInvariantForm_eq_Bsimp c B hB) x) y

/-- An antilinear endomorphism of the simple Virasoro VOA is determined by
its vacuum value and commutation with Virasoro modes. This is the exact
compatibility needed to identify a cohomological conjugation. -/
theorem virasoroSimple_conjugation_ext (c : ℂ)
    (f g : (VirUniv c ⧸ maxIdealVir c) →ₗ⋆[ℂ] (VirUniv c ⧸ maxIdealVir c))
    (hvac : f (virasoroSimple c).vacuum = g (virasoroSimple c).vacuum)
    (hf : ∀ n x, f ((virasoroSimple c).L n x) = (virasoroSimple c).L n (f x))
    (hg : ∀ n x, g ((virasoroSimple c).L n x) = (virasoroSimple c).L n (g x)) :
    f = g := by
  have hword (w : List ℕ) :
      f ((maxIdealVir c).mkQ (negWordVir c w)) =
        g ((maxIdealVir c).mkQ (negWordVir c w)) := by
    induction w with
    | nil => exact hvac
    | cons a w ih =>
        rw [negWordVir_cons, ← virasoroVOA_L_eq_Lop, mkQ_L, hf, hg, ih]
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := virasoroSimple_mkQ_surjective (c := c) z
  have hx : x ∈ Submodule.span ℂ (Set.range (negWordVir c)) := by
    have htop : Submodule.span ℂ (Set.range (negWordVir c)) = ⊤ := negSpanVir_eq_top c
    rw [htop]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨w, rfl⟩ := hx; exact hword w
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => simp only [map_smulₛₗ, hx]

variable {K : Type u} [AddCommGroup K] [Module ℂ K]

/-- Simultaneously negating the bilinear form and conjugation preserves all
existing `GUData` fields and leaves the sesquilinear form unchanged. -/
def signTwistGUData {C : KahlerComplex K} (G : GUData C) : GUData C where
  B := -G.B
  ρ := -G.ρ
  h := G.h
  h_eq := by
    intro x y
    simpa using G.h_eq x y
  P_eq := G.P_eq
  ρ_maps := by
    intro j x hx
    exact Submodule.neg_mem _ (G.ρ_maps j x hx)
  ρ_onto := by
    intro j y hy
    obtain ⟨x, hx, hxy⟩ := G.ρ_onto j y hy
    refine ⟨-x, Submodule.neg_mem _ hx, ?_⟩
    simpa using hxy

@[simp] theorem signTwistGUData_B {C : KahlerComplex K} (G : GUData C) (x y : K) :
    (signTwistGUData G).B x y = -G.B x y := rfl

@[simp] theorem signTwistGUData_rho {C : KahlerComplex K} (G : GUData C) (x : K) :
    (signTwistGUData G).ρ x = -G.ρ x := rfl

@[simp] theorem signTwistGUData_h {C : KahlerComplex K} (G : GUData C) :
    (signTwistGUData G).h = G.h := rfl

/-- The existing weightwise GU identities cannot force a prescribed vacuum
normalization: the simultaneous sign change preserves those identities. -/
theorem signTwistGUData_not_both_normalized {C : KahlerComplex K}
    (G : GUData C) (v : K) :
    ¬ (G.B v v = 1 ∧ (signTwistGUData G).B v v = 1) := by
  rintro ⟨h, ht⟩
  rw [signTwistGUData_B, h] at ht
  norm_num at ht

/-- Likewise these identities do not force a nonzero distinguished vector to
be fixed by the conjugation. -/
theorem signTwistGUData_not_both_fix {C : KahlerComplex K}
    (G : GUData C) (v : K) (hv : v ≠ 0) :
    ¬ (G.ρ v = v ∧ (signTwistGUData G).ρ v = v) := by
  rintro ⟨h, ht⟩
  rw [signTwistGUData_rho, h] at ht
  have hsum : -v + v = 0 := neg_add_cancel v
  rw [ht] at hsum
  have hz : (2 : ℂ) • v = 0 := by simpa only [two_smul] using hsum
  exact hv ((smul_eq_zero.mp hz).resolve_left (by norm_num))

/-- This ambiguity persists for the exact concrete field used by the old
assembly; the geometry, differential, and character fields are unchanged. -/
def signTwistConcreteGUData {S : ConcreteKahlerGeometry} (G : ConcreteGUData S) :
    ConcreteGUData S where
  data n hp := signTwistGUData (G.data n hp)

end
end VOA.LeeYangShortcut
