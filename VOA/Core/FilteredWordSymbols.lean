/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.PolynomialMinimumSymbol
import VOA.Core.OrderedExponentWord

/-!
# Leading polynomial symbols of actual filtered words

An actual operator raises creation length by at most one and agrees in
coordinates with multiplication by a linear polynomial, up to a
length-preserving error. Word induction multiplies these symbols. The
coordinate map need not be an isomorphism or even injective.
-/
namespace VOA
noncomputable section
open MvPolynomial
open Module (End)
variable {V σ α : Type*} [AddCommGroup V] [Module ℂ V]

/-- An actual finite operator word evaluated on a specified starting vector. -/
def filteredWord (T : α → End ℂ V) (v : V) : List α → V
  | [] => v
  | a::l => T a (filteredWord T v l)

/-- One-step length bounds imply the expected bound on every actual word. -/
theorem filteredWord_length (F : ℕ → Submodule ℂ V) (T : α → End ℂ V) (v : V)
    (hv : v∈F 0) (hT : ∀ a d u,u∈F d → T a u∈F (d+1)) (l : List α) :
    filteredWord T v l∈F l.length := by
  induction l with
  | nil => exact hv
  | cons a l ih => exact hT a l.length _ ih

/-- All actual finite words have the product of their linear leading symbols.
The proof bounds both the new operator error and the previous word error. -/
theorem filteredWord_symbol (F : ℕ → Submodule ℂ V) (T : α → End ℂ V) (v : V)
    (φ : V →ₗ[ℂ] MvPolynomial σ ℂ) (f : α → MvPolynomial σ ℂ)
    (hv : v∈F 0) (hφ : φ v=1)
    (hT : ∀ a d u,u∈F d → T a u∈F (d+1))
    (hf : ∀ a,(f a).IsWeightedHomogeneous (fun _ => (-1 : ℤ)) (-1))
    (he : ∀ a d u,u∈F d → φ (T a u)-f a*φ u∈
      PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) (-(d : ℤ)))
    (l : List α) : PolynomialMinimum.Symbol (fun _ => (-1 : ℤ)) (-(l.length : ℤ))
      (φ (filteredWord T v l)) ((l.map f).prod) := by
  induction l with
  | nil =>
      refine ⟨?_,?_⟩
      · simpa using (isWeightedHomogeneous_one ℂ (fun _ : σ => (-1 : ℤ)))
      · simp only [filteredWord,List.map_nil,List.prod_nil,hφ,sub_self]
        exact Submodule.zero_mem _
  | cons a l ih =>
      constructor
      · have hh := (hf a).mul ih.homogeneous
        convert hh using 1 <;> simp <;> ring
      · have hnew := he a l.length (filteredWord T v l) (filteredWord_length F T v hv hT l)
        have hold := PolynomialMinimum.mul_mem (PolynomialMinimum.homogeneous_mem (hf a)) ih.remainder
        have hold' : f a*(φ (filteredWord T v l)-(l.map f).prod)∈
            PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) (-(l.length : ℤ)) := by
          convert hold using 1 <;> congr 1 <;> ring
        have hh := (PolynomialMinimum.AtLeast (fun _ : σ => (-1 : ℤ)) (-(l.length : ℤ))).add_mem hnew hold'
        have hid : φ (T a (filteredWord T v l))-f a*(l.map f).prod=
            (φ (T a (filteredWord T v l))-f a*φ (filteredWord T v l))+
              f a*(φ (filteredWord T v l)-(l.map f).prod) := by ring
        simp only [filteredWord,List.map_cons,List.prod_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
        rw [show -((l.length : ℤ)+1)+1=-(l.length : ℤ) by ring,hid]
        exact hh

/-- Independent product symbols imply independence of the corresponding
actual ordered states, even if the polynomial coordinate map has a kernel. -/
theorem filteredOrderedWord_independent [LinearOrder α]
    (F : ℕ → Submodule ℂ V) (T : α → End ℂ V) (v : V)
    (φ : V →ₗ[ℂ] MvPolynomial σ ℂ) (f : α → MvPolynomial σ ℂ)
    (hv : v∈F 0) (hφ : φ v=1)
    (hT : ∀ a d u,u∈F d → T a u∈F (d+1))
    (hf : ∀ a,(f a).IsWeightedHomogeneous (fun _ => (-1 : ℤ)) (-1))
    (he : ∀ a d u,u∈F d → φ (T a u)-f a*φ u∈
      PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) (-(d : ℤ)))
    (hind : LinearIndependent ℂ (fun e : α →₀ ℕ => ((orderedExponentWord e).map f).prod)) :
    LinearIndependent ℂ (fun e : α →₀ ℕ => filteredWord T v (orderedExponentWord e)) := by
  apply LinearIndependent.of_comp φ
  exact PolynomialMinimum.linearIndependent_of_symbols
    (fun e => -((orderedExponentWord e).length : ℤ)) _ _
    (fun e => filteredWord_symbol F T v φ f hv hφ hT hf he (orderedExponentWord e)) hind

end
end VOA
