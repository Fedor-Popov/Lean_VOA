import VOA.Huang.LogAssocCoefficients
import VOA.Huang.LogAssocAssociator
import VOA.Huang.LogAssocConvergence
import VOA.Huang.LogHuangODEModes
import VOA.Modules.LogTensorArDualPairing

/-! Actual generalized-weight support and outside-mode truncation for
logarithmic collision coefficient functionals. No ordinary module premise. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficientCompatibility
open VOA VOA.LogTensor VOA.LogTensor.Pz Filter Topology
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- A genuine scalar functional vanishes on every foreign generalized weight. -/
def SupportedAt (N : LogVModule W M) (f : M →ₗ[ℂ] ℂ) (b : ℂ) : Prop :=
  ∀ a : ℂ, a≠b → ∀ x : M, x∈N.weight a → f x=0

theorem supportedAt_comp_mode {N : LogVModule W M} {f : M →ₗ[ℂ] ℂ} {b : ℂ}
    (hf : SupportedAt N f b) {d : ℤ} {u : V} (hu : u ∈ W.grading d) (q : ℤ) :
    SupportedAt N (f ∘ₗ mode (N.YM u) q) (b-d+q+1) := by
  intro a ha x hx
  simp only [LinearMap.comp_apply]
  apply hf (a+d-q-1) _ _ (N.mode_mem_weight hu hx q)
  intro he
  apply ha
  linear_combination he

theorem eq_zero_of_supportedAt_bot {N : LogVModule W M} {f : M →ₗ[ℂ] ℂ} {b : ℂ}
    (hf : SupportedAt N f b) (hb : N.weight b=⊥) : f=0 := by
  apply LinearMap.ext
  intro x
  refine LogFin.induction_on N (C := fun x => f x=0) x ?_ ?_ ?_
  · intro a x hx
    by_cases ha : a=b
    · subst a
      have hz : x=0 := by simpa only [hb,Submodule.mem_bot] using hx
      rw [hz,map_zero]
    · exact hf a ha x hx
  · exact map_zero f
  · intro x y hx hy
    rw [map_add,hx,hy,add_zero]

/-- Generalized lower boundedness gives the actual finite outside-mode bound. -/
theorem exists_comp_mode_vanish {N : LogVModule W M} {f : M →ₗ[ℂ] ℂ} {b : ℂ}
    (hf : SupportedAt N f b) {d : ℤ} {u : V} (hu : u ∈ W.grading d) (p : ℤ) :
    ∃ R : ℕ, ∀ i : ℕ, R ≤ i → f ∘ₗ mode (N.YM u) (p-i)=0 := by
  obtain ⟨B,hB⟩ := N.boundedBelow
  obtain ⟨R,hR⟩ := exists_nat_gt ((b-d+p+1).re-B)
  refine ⟨R,fun i hi => eq_zero_of_supportedAt_bot (supportedAt_comp_mode hf hu (p-i)) ?_⟩
  by_contra hne
  have hb := hB (b-(d : ℂ)+((p-(i : ℤ) : ℤ) : ℂ)+1) hne
  have hRi : (R : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  simp only [Complex.add_re,Complex.sub_re,Complex.intCast_re,Complex.one_re] at hR hb
  push_cast at hb
  linarith

/-- Actual homogeneous restricted-dual vectors give supported functionals. -/
theorem restrictedDual_supportedAt (N : LogVModule W M) {b : ℂ}
    (r : C2Rigid.RestrictedDual N.toGW) (hr : r ∈ (contraLog N).weight b) :
    SupportedAt N (C2Rigid.dualPairingFlip N.toGW r) b := by
  intro a ha x hx
  exact Ar.pair_weights_zero N hx hr (Ne.symm ha)

/-- A true weak-module action has a finite natural-number truncation bound. -/
theorem exists_nat_truncation (N : LogVModule W M) (u : V) (x : M) :
    ∃ R : ℕ, ∀ i : ℕ, R ≤ i → mode (N.YM u) i x=0 := by
  obtain ⟨R,hR⟩ := N.truncation u x
  exact ⟨R.toNat,fun i hi => hR i (by omega)⟩

end VOA.Huang.LogAssocCoefficientCompatibility
