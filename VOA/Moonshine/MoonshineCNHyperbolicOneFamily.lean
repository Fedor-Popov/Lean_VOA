import VOA.Moonshine.MoonshineCNHyperbolicForm
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # One-family vacua and their evaluation quotient

The parameter `a` permits either light-cone choice. At `a = 0` these
are the b-free polynomials. Their restricted form is evaluation at zero
in both arguments; its radical is exactly the augmentation subspace.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial HeisenbergN

/-- Polynomials using just the indicated isotropic family. -/
def hypOneFamily (a : Fin 2) : Submodule ℂ hypFock :=
  (supported ℂ {v : ℕ × Fin 2 | v.2 = a}).toSubmodule

theorem hypOneFamily_mem_iff (a : Fin 2) (p : hypFock) :
    p ∈ hypOneFamily a ↔ ∀ v ∈ p.vars, v.2 = a :=
  mem_supported

theorem hypOneFamily_coeff (a : Fin 2) (p : hypFock) (hp : p ∈ hypOneFamily a)
    (d : (ℕ × Fin 2) →₀ ℕ) (hd : coeff d p ≠ 0) (v : ℕ × Fin 2)
    (hv : v.2 ≠ a) : d v = 0 := by
  by_contra h
  exact hv ((hypOneFamily_mem_iff a p).mp hp v
    ((mem_vars_iff_mem_support v).mpr
      ⟨d, mem_support_iff.mpr hd, Finsupp.mem_support_iff.mpr h⟩))

theorem hypOneFamily_iff_pderiv (a : Fin 2) (p : hypFock) :
    p ∈ hypOneFamily a ↔ ∀ j : ℕ, pderiv (j, a.rev) p = 0 := by
  constructor
  · intro hp j
    apply pderiv_eq_zero_of_notMem_vars
    intro hv
    have he := (hypOneFamily_mem_iff a p).mp hp (j, a.rev) hv
    fin_cases a <;> simp at he
  · intro hp
    rw [hypOneFamily_mem_iff]
    rintro ⟨j, b⟩ hv
    by_contra h
    have he : b = a.rev := by fin_cases a <;> fin_cases b <;> simp_all
    subst b
    obtain ⟨d, hd, hv⟩ := (mem_vars_iff_mem_support (j, a.rev)).mp hv
    have hc := coeff_X_mul_pderiv_self (j, a.rev) d p
    rw [hp j, mul_zero, coeff_zero] at hc
    have hz : (d (j, a.rev) : ℂ) = 0 :=
      (mul_eq_zero.mp hc.symm).resolve_right (mem_support_iff.mp hd)
    exact Finsupp.mem_support_iff.mp hv (by exact_mod_cast hz)

/-- Exact common-kernel description for either isotropic family. -/
theorem hypOneFamily_iff_oscillator (a : Fin 2) (charge : ℂ) (p : hypFock) :
    p ∈ hypOneFamily a ↔ ∀ j : ℕ, hypOscillator a charge (j + 1 : ℤ) p = 0 := by
  rw [hypOneFamily_iff_pderiv]
  apply forall_congr'
  intro j
  rw [hypOscillator_positive_apply, smul_eq_zero]
  have hn : (j + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  simp [hn]

theorem hypOneFamily_eq_range (a : Fin 2) :
    hypOneFamily a = LinearMap.range (rename (fun j : ℕ => (j, a))).toLinearMap := by
  apply Submodule.ext
  intro p
  rw [hypOneFamily_mem_iff, LinearMap.mem_range]
  constructor
  · intro hp
    exact exists_rename_eq_of_vars_subset_range p (fun j : ℕ => (j, a))
      (fun _ _ h => (Prod.mk.inj h).1) (by
        intro v hv
        exact ⟨v.1, by simpa using congrArg (fun b => (v.1, b)) (hp v hv).symm⟩)
  · rintro ⟨q, rfl⟩ v hv
    obtain ⟨j, _, he⟩ := Finset.mem_image.mp (vars_rename (fun j : ℕ => (j, a)) q hv)
    exact (congrArg Prod.snd he).symm

theorem hypOneFamily_constant_mem (a : Fin 2) (c : ℂ) :
    MvPolynomial.C c ∈ hypOneFamily a := by
  rw [hypOneFamily_mem_iff]
  simp

/-- The form restricted to one isotropic family is the product of evaluations. -/
theorem hypOneFamily_form (a : Fin 2) (p q : hypFock)
    (hp : p ∈ hypOneFamily a) (hq : q ∈ hypOneFamily a) :
    hypForm p q = coeff 0 p * coeff 0 q := by
  rw [hypOneFamily_eq_range, LinearMap.mem_range] at hp
  obtain ⟨f, rfl⟩ := hp
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [AlgHom.toLinearMap_apply, rename_C]
    rw [show (MvPolynomial.C c : hypFock) = monomial 0 c from rfl, hypForm_monomial]
    simp
  | add f g hf hg =>
    simpa only [map_add, LinearMap.add_apply, coeff_add, add_mul] using congrArg₂ (· + ·) hf hg
  | mul_X f j hf =>
    simp only [AlgHom.toLinearMap_apply, map_mul, rename_X]
    rw [mul_comm _ (X (j, a)), hypForm_creation_adjoint,
      (hypOneFamily_iff_pderiv a q).mp hq j]
    change _ = constantCoeff (X (j, a) * rename (fun j : ℕ => (j, a)) f) * coeff 0 q
    simp

/-- Evaluation on the one-family subspace. -/
def hypOneFamilyEval (a : Fin 2) : hypOneFamily a →ₗ[ℂ] ℂ :=
  (lcoeff ℂ 0).comp (hypOneFamily a).subtype

def hypOneFamilyAugmentation (a : Fin 2) : Submodule ℂ (hypOneFamily a) :=
  LinearMap.ker (hypOneFamilyEval a)

theorem hypOneFamilyEval_surjective (a : Fin 2) :
    Function.Surjective (hypOneFamilyEval a) := by
  intro c
  exact ⟨⟨MvPolynomial.C c, hypOneFamily_constant_mem a c⟩, by simp [hypOneFamilyEval]⟩

theorem hypOneFamily_radical_iff (a : Fin 2) (p : hypOneFamily a) :
    (∀ q : hypOneFamily a, hypForm p q = 0) ↔ p ∈ hypOneFamilyAugmentation a := by
  change _ ↔ coeff 0 p.val = 0
  constructor
  · intro h
    have he := h ⟨MvPolynomial.C 1, hypOneFamily_constant_mem a 1⟩
    rw [hypOneFamily_form a _ _ p.property (hypOneFamily_constant_mem a 1)] at he
    simpa using he
  · intro h q
    rw [hypOneFamily_form a _ _ p.property q.property, h, zero_mul]

/-- The concrete one-family radical quotient is evaluation at zero. -/
def hypOneFamilyQuotientEquiv (a : Fin 2) :
    (hypOneFamily a ⧸ hypOneFamilyAugmentation a) ≃ₗ[ℂ] ℂ :=
  LinearMap.quotKerEquivOfSurjective (hypOneFamilyEval a) (hypOneFamilyEval_surjective a)

theorem hypOneFamilyQuotientEquiv_mk (a : Fin 2) (p : hypOneFamily a) :
    hypOneFamilyQuotientEquiv a (Submodule.Quotient.mk p) = coeff 0 p.val := rfl

theorem hypOneFamily_decomposition (a : Fin 2) (p : hypOneFamily a) :
    ∃ q : hypOneFamilyAugmentation a,
      p.val = MvPolynomial.C (coeff 0 p.val) + q.val.val := by
  let q : hypOneFamily a := p - ⟨MvPolynomial.C (coeff 0 p.val),
    hypOneFamily_constant_mem a _⟩
  have hq : q ∈ hypOneFamilyAugmentation a := by
    change coeff 0 (p.val - MvPolynomial.C (coeff 0 p.val)) = 0
    simp
  exact ⟨⟨q, hq⟩, by change p.val = _ + (p.val - _); ring⟩

end VOA.Moonshine.ConwayNorton
