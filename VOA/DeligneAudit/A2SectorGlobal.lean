/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.HeightOneGlobalization
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Height-one globalization for a free submodule of a torsion-free module

Let `R` be a noetherian UFD, `N` a torsion-free `R`-module and `M ⊆ N` a free submodule of finite
rank.  A vector `x ∈ N` with `s₀ • x ∈ M` for some `s₀ ≠ 0`, and with a local denominator witness
`s ∉ p`, `s • x ∈ M` at every height-one prime `p`, lies in `M`.  This is the normality step of
B8; no ambient fraction-field vector space is needed.
-/

namespace VOA.DeligneAudit.SectorGlobal

open VOA.HeightOneGlobalization

noncomputable section

variable {R N ι : Type*} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]

/-- **Globalization for free submodules.** -/
theorem mem_of_local_witnesses [UniqueFactorizationMonoid R] [IsNoetherianRing R] [Finite ι]
    (htf : ∀ (s : R) (x : N), s ≠ 0 → s • x = 0 → x = 0)
    (M : Submodule R N) (b : Module.Basis ι R M) (x : N)
    (h0 : ∃ s : R, s ≠ 0 ∧ s • x ∈ M)
    (hloc : ∀ p : HeightOnePrime R, ∃ s : R, s ∉ p.asIdeal ∧ s • x ∈ M) : x ∈ M := by
  classical
  letI := Fintype.ofFinite ι
  let K := FractionRing R
  obtain ⟨s₀, hs₀, hx₀⟩ := h0
  let a : ι → R := fun i => b.repr ⟨s₀ • x, hx₀⟩ i
  have hs₀K : algebraMap R K s₀ ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hs₀
  -- the rational coordinates are integral
  have hint : ∀ i, IsLocalization.IsInteger R (algebraMap R K (a i) * (algebraMap R K s₀)⁻¹) := by
    intro i
    apply isInteger_of_mem_heightOneLocalizations
    intro p
    obtain ⟨s, hs, hsx⟩ := hloc p
    have hcomm : s • (⟨s₀ • x, hx₀⟩ : M) = s₀ • (⟨s • x, hsx⟩ : M) := by
      apply Subtype.ext
      simp only [SetLike.val_smul]
      rw [smul_comm]
    have hc := congrArg (fun y => b.repr y i) hcomm
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
    change ∃ (u t : R) (_ : t ∈ p.asIdeal.primeCompl),
      algebraMap R K (a i) * (algebraMap R K s₀)⁻¹ = algebraMap R K u * (algebraMap R K t)⁻¹
    refine ⟨b.repr ⟨s • x, hsx⟩ i, s, hs, ?_⟩
    have hs0' : s ≠ 0 := by
      intro h; apply hs; rw [h]; exact p.asIdeal.zero_mem
    have hsK : algebraMap R K s ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective R K).ne hs0'
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff hs₀K hsK, ← map_mul, ← map_mul]
    congr 1
    simp only [a]
    linear_combination hc
  choose r hr using hint
  -- the integral vector
  let x' : M := ∑ i, r i • b i
  have hx' : s₀ • (x' : N) = s₀ • x := by
    have hrs : ∀ i, s₀ * r i = a i := by
      intro i
      apply IsFractionRing.injective R K
      rw [map_mul, hr i, mul_comm, mul_assoc, inv_mul_cancel₀ hs₀K, mul_one]
    have : s₀ • x' = (⟨s₀ • x, hx₀⟩ : M) := by
      rw [← b.sum_repr ⟨s₀ • x, hx₀⟩, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, hrs]
    have h := congrArg Subtype.val this
    simpa using h
  have hsub : s₀ • ((x' : N) - x) = 0 := by rw [smul_sub, hx', sub_self]
  have heq := htf s₀ _ hs₀ hsub
  rw [sub_eq_zero] at heq
  rw [← heq]
  exact x'.2

end

end VOA.DeligneAudit.SectorGlobal

section AxiomAudit
#print axioms VOA.DeligneAudit.SectorGlobal.mem_of_local_witnesses
end AxiomAudit
