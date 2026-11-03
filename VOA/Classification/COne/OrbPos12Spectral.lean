import VOA.Classification.COne.OrbPos12Monodromy
import Mathlib.LinearAlgebra.Lagrange

/-! Actual spectral idempotents in the algebra of ordinary-module endomorphisms.
These are U-linear projections on the induced object. Algebra-action linearity
and identification with group sectors are separate, unproved requirements. -/
noncomputable section
namespace VOA.Classification.COne.OrbPos12
open CategoryTheory VOA VOA.Huang.TensorCat VOA.Huang.FusionUnit
open Polynomial

section Algebra
variable {R : Type*} [Ring R] [Algebra ℂ R]

theorem aeval_mul_eigen (f x : R) (c : ℂ) (hx : f * x = c • x) (p : ℂ[X]) :
    aeval f p * x = p.eval c • x := by
  have hp (n : ℕ) : f ^ n * x = c ^ n • x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_assoc, ih, mul_smul_comm, hx, smul_smul, pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, add_mul, eval_add, hp, hq, add_smul]
  | monomial n a =>
    rw [aeval_monomial, eval_monomial, mul_assoc, hp,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul]

/-- Lagrange polynomials give a complete orthogonal family for any split,
squarefree annihilator. No finite-dimensionality of `R` is used. -/
theorem spectralResolution_of_nodal (f : R) (s : Finset ℂ) (hs : s.Nonempty)
    (hf : aeval f (Lagrange.nodal s id) = 0) :
    ∃ p : ℂ → R, (∑ c ∈ s, p c) = 1 ∧
      (∀ c ∈ s, p c * p c = p c ∧ f * p c = c • p c) ∧
      ∀ c ∈ s, ∀ d ∈ s, c ≠ d → p c * p d = 0 := by
  classical
  let p (c : ℂ) : R := aeval f (Lagrange.basis s id c)
  have he (c : ℂ) (hc : c ∈ s) : f * p c = c • p c := by
    have hpoly : (Polynomial.X - Polynomial.C c) * Lagrange.basis s id c =
        Polynomial.C (Lagrange.nodalWeight s id c) * Lagrange.nodal s id := by
      rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hc,
        ← Lagrange.nodal_erase_eq_nodal_div hc, Lagrange.nodal_eq_mul_nodal_erase hc]
      simp only [id_eq]
      ring
    have hh := congrArg (aeval f) hpoly
    simp only [map_mul, map_sub, aeval_X, aeval_C, hf, mul_zero] at hh
    change (f - algebraMap ℂ R c) * p c = 0 at hh
    rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      sub_eq_zero] at hh
    exact hh
  refine ⟨p, ?_, ?_, ?_⟩
  · change (∑ c ∈ s, (aeval f) (Lagrange.basis s id c)) = 1
    rw [← map_sum, Lagrange.sum_basis Function.injective_id.injOn hs, map_one]
  · intro c hc
    refine ⟨?_, he c hc⟩
    change aeval f (Lagrange.basis s id c) * p c = p c
    have hv : (Lagrange.basis s id c).eval c = 1 :=
      Lagrange.eval_basis_self Function.injective_id.injOn hc
    rw [aeval_mul_eigen f (p c) c (he c hc), hv, one_smul]
  · intro c hc d hd hcd
    change aeval f (Lagrange.basis s id c) * p d = 0
    have hv : (Lagrange.basis s id c).eval d = 0 :=
      Lagrange.eval_basis_of_ne (v := id) hcd hd
    rw [aeval_mul_eigen f (p d) d (he d hd), hv, zero_smul]

/-- Every finite-order element of a complex algebra admits finite spectral
idempotents, with eigenvalues which are roots of unity. -/
theorem spectralResolution_of_finiteOrder (f : R) (hf : IsOfFinOrder f) :
    ∃ (n : ℕ) (s : Finset ℂ) (p : ℂ → R), 0 < n ∧ (∑ c ∈ s, p c) = 1 ∧
      (∀ c ∈ s, c ^ n = 1 ∧ p c * p c = p c ∧ f * p c = c • p c) ∧
      ∀ c ∈ s, ∀ d ∈ s, c ≠ d → p c * p d = 0 := by
  classical
  obtain ⟨n, hn, hfn⟩ := hf.exists_pow_eq_one
  let P : ℂ[X] := Polynomial.X ^ n - Polynomial.C 1
  have hmon : P.Monic := monic_X_pow_sub_C 1 hn.ne'
  have hsep : P.Separable := separable_X_pow_sub_C 1 (by exact_mod_cast hn.ne') one_ne_zero
  let s := P.roots.toFinset
  have hs : s.Nonempty := by
    refine ⟨1, ?_⟩
    rw [Multiset.mem_toFinset, mem_roots hmon.ne_zero]
    simp [P, IsRoot]
  have hnod : Lagrange.nodal s id = P := by
    rw [(IsAlgClosed.splits P).eq_prod_roots_of_monic hmon]
    unfold Lagrange.nodal s
    rw [← Multiset.toFinset_eq (Polynomial.nodup_roots hsep)]
    rfl
  have hz : aeval f (Lagrange.nodal s id) = 0 := by
    rw [hnod]
    simp [P, hfn]
  obtain ⟨p, hsum, hp, horth⟩ := spectralResolution_of_nodal f s hs hz
  refine ⟨n, s, p, hn, hsum, ?_, horth⟩
  intro c hc
  have hr : P.IsRoot c := (mem_roots hmon.ne_zero).mp (Multiset.mem_toFinset.mp hc)
  refine ⟨?_, hp c hc⟩
  simpa [P, IsRoot, sub_eq_zero] using hr
end Algebra

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Spectral projections of the induced monodromy are actual U-morphisms.
The statement deliberately does not assert A-linearity or labels in G. -/
theorem inducedMonodromy_spectralResolution (hW : StronglyRational W) (F : FusionChoice W)
    (X A : Ordinary W) :
    ∃ (n : ℕ) (s : Finset ℂ) (p : ℂ → (tensorObj F X A ⟶ tensorObj F X A)),
      0 < n ∧ (∑ c ∈ s, p c) = 𝟙 _ ∧
      (∀ c ∈ s, c ^ n = 1 ∧ p c ≫ p c = p c ∧
        p c ≫ (monodromyAut F X A).hom = c • p c) ∧
      ∀ c ∈ s, ∀ d ∈ s, c ≠ d → p d ≫ p c = 0 := by
  let f : CategoryTheory.End (tensorObj F X A) := (monodromyAut F X A).hom
  have hf : IsOfFinOrder f :=
    (CategoryTheory.Aut.toEnd _).isOfFinOrder (monodromyAut_finiteOrder hW F X A)
  exact spectralResolution_of_finiteOrder f hf

end VOA.Classification.COne.OrbPos12
