/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.CyclicEvalAssembly

/-!
# Cyclic dual vectors: the Cartan calculus and transfer along injective intertwiners

`CyclicEval.CyclicDual` (input (A) of the coset note) carries, besides the cyclic vector `w` and
its relations, an algebra map `π : C[H_1, H_2, …] → End M` with `π(H_{i+1}) = -ρ(h_{i+1})` and a
commutation field. Both are formal consequences of the commutation of the Cartan modes. This file
proves:

* `cartanCalc` — the polynomial calculus of any commuting family `-ρ(hpos i)` (via the commutative
  subalgebra they generate), with `cartanCalc_X`;
* `algHom_comp_eq_of_X` — two such calculi are intertwined by every linear map that intertwines
  the generators;
* `CyclicVector` — input (A) with the formal fields removed: a cyclic functional with support,
  charge and the Cartan relations computed by `cartanCalc`;
* `CyclicVector.toCyclicDual` / `CyclicDual.toCyclicVector` — the two formulations agree
  (so nothing is lost);
* `CyclicDual.comap` — **transfer along an injective intertwiner**: if `f : M → M'` is
  injective, intertwines the mode actions and respects the conformal grading, a cyclic dual
  vector of `M'` pulls back to one of `M`. This is the shape of the step in
  the affine cyclic-dual bridge: cyclicity of the polynomial image
  `A_r^*` gives full physical cyclicity of `(gr_r A)^*` exactly when `gr_r A → A_r` is injective
  (strictness).

Everything is proved outright.
-/

namespace VOA.SymbolModel

open VOA.CyclicEval VOA.InvariantSymbol MvPolynomial

noncomputable section

section Calc

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {κ : Type*}
variable (ρ : κ → Module.End ℂ M) (hpos : ℕ → κ)

/-- The positive Cartan modes commute pairwise. -/
def CartanCommute : Prop := ∀ i j, Commute (ρ (hpos i)) (ρ (hpos j))

/-- The generators `-ρ(h_{i+1})`. -/
def cartanGens : Set (Module.End ℂ M) := Set.range fun i => -ρ (hpos i)

theorem cartanGens_comm (hc : CartanCommute ρ hpos) :
    ∀ a ∈ cartanGens ρ hpos, ∀ b ∈ cartanGens ρ hpos, a * b = b * a := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  rw [neg_mul_neg, neg_mul_neg]
  exact (hc i j).eq

/-- **The Cartan calculus** `F ↦ F(-ρ(h_1), -ρ(h_2), …)` of a commuting family. -/
def cartanCalc (hc : CartanCommute ρ hpos) : MvPolynomial ℕ ℂ →ₐ[ℂ] Module.End ℂ M :=
  letI : CommRing (Algebra.adjoin ℂ (cartanGens ρ hpos)) :=
    { (Algebra.adjoin ℂ (cartanGens ρ hpos)).toRing with
      mul_comm := (Algebra.isMulCommutative_adjoin ℂ (cartanGens_comm ρ hpos hc)).is_comm.comm }
  (Algebra.adjoin ℂ (cartanGens ρ hpos)).val.comp
    (MvPolynomial.aeval fun i => ⟨-ρ (hpos i), Algebra.subset_adjoin ⟨i, rfl⟩⟩)

@[simp] theorem cartanCalc_X (hc : CartanCommute ρ hpos) (i : ℕ) :
    cartanCalc ρ hpos hc (X i) = -ρ (hpos i) := by
  simp [cartanCalc]

variable {ρ hpos}

/-- Any algebra map with `π(H_{i+1}) = -ρ(h_{i+1})` forces the generators to commute. -/
theorem cartanCommute_of_algHom (π : MvPolynomial ℕ ℂ →ₐ[ℂ] Module.End ℂ M)
    (hπ : ∀ i, π (X i) = -ρ (hpos i)) : CartanCommute ρ hpos := by
  intro i j
  have h : Commute (π (X i)) (π (X j)) := (Commute.all (X i) (X j)).map π
  rw [hπ, hπ] at h
  simpa using h.neg_left.neg_right

/-- An algebra map is determined by the generators: it equals `cartanCalc`. -/
theorem eq_cartanCalc (hc : CartanCommute ρ hpos) (π : MvPolynomial ℕ ℂ →ₐ[ℂ] Module.End ℂ M)
    (hπ : ∀ i, π (X i) = -ρ (hpos i)) : π = cartanCalc ρ hpos hc :=
  MvPolynomial.algHom_ext fun i => by rw [hπ, cartanCalc_X]

/-- **Intertwining of two calculi.** -/
theorem algHom_comp_eq_of_X {M' : Type*} [AddCommGroup M'] [Module ℂ M']
    (π : MvPolynomial ℕ ℂ →ₐ[ℂ] Module.End ℂ M) (π' : MvPolynomial ℕ ℂ →ₐ[ℂ] Module.End ℂ M')
    (f : M →ₗ[ℂ] M') (h : ∀ i, f ∘ₗ π (X i) = π' (X i) ∘ₗ f) (F : MvPolynomial ℕ ℂ) :
    f ∘ₗ π F = π' F ∘ₗ f := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    ext x
    simp
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← LinearMap.comp_assoc, hp, LinearMap.comp_assoc, h i, ← LinearMap.comp_assoc]

end Calc

section Words

variable {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
variable {κ : Type*} {ρ : κ → Module.End ℂ M} {ρ' : κ → Module.End ℂ M'}

theorem word_intertwine (f : M →ₗ[ℂ] M') (hf : ∀ k, f ∘ₗ ρ k = ρ' k ∘ₗ f) (l : List κ)
    (m : M) : f (word ρ l m) = word ρ' l (f m) := by
  induction l generalizing m with
  | nil => simp [word]
  | cons k l ih =>
    simp only [word, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
    have := LinearMap.congr_fun (hf k) ((l.map ρ).prod m)
    simp only [LinearMap.comp_apply] at this
    rw [this, ih]

end Words

section Vector

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {κ : Type*}
variable (ρ : κ → Module.End ℂ M) (hz : κ) (hpos : ℕ → κ) (Mdeg : ℤ → Submodule ℂ M)

/-- **Input (A) with the formal fields removed**: a cyclic functional of conformal degree `r`,
`h₀`-charge `2r` (negative-transpose action), annihilated by the Cartan ideal `I_r` computed by
the calculus of the commuting Cartan modes. -/
structure CyclicVector (hc : CartanCommute ρ hpos) (r : ℕ) where
  w : Module.Dual ℂ M
  cyclic : ∀ m : M, (∀ l : List κ, w (word ρ l m) = 0) → m = 0
  supp : ∀ d : ℤ, d ≠ (r : ℤ) → ∀ m ∈ Mdeg d, w m = 0
  charge : w ∘ₗ ρ hz = (-(2 * (r : ℂ))) • w
  cartan : ∀ F ∈ cartanIdeal r, w ∘ₗ cartanCalc ρ hpos hc F = 0

variable {ρ hz hpos Mdeg}

/-- A `CyclicVector` is a `CyclicDual` (given that `h₀` commutes with the positive Cartan
modes). -/
def CyclicVector.toCyclicDual {hc : CartanCommute ρ hpos} {r : ℕ}
    (V : CyclicVector ρ hz hpos Mdeg hc r) (h0 : ∀ i, Commute (ρ hz) (ρ (hpos i))) :
    CyclicDual ρ hz hpos Mdeg r where
  w := V.w
  cyclic := V.cyclic
  supp := V.supp
  charge := V.charge
  comm := h0
  π := cartanCalc ρ hpos hc
  π_X := cartanCalc_X ρ hpos hc
  cartan := V.cartan

/-- Conversely, every `CyclicDual` gives a `CyclicVector`: the two formulations of input (A)
are equivalent. -/
def _root_.VOA.CyclicEval.CyclicDual.toCyclicVector {r : ℕ} (D : CyclicDual ρ hz hpos Mdeg r)
    (hc : CartanCommute ρ hpos) : CyclicVector ρ hz hpos Mdeg hc r where
  w := D.w
  cyclic := D.cyclic
  supp := D.supp
  charge := D.charge
  cartan F hF := by rw [← eq_cartanCalc hc D.π D.π_X]; exact D.cartan F hF

end Vector

section Comap

variable {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
variable {κ : Type*} {ρ : κ → Module.End ℂ M} {ρ' : κ → Module.End ℂ M'} {hz : κ}
variable {hpos : ℕ → κ} {Mdeg : ℤ → Submodule ℂ M} {Mdeg' : ℤ → Submodule ℂ M'}

theorem commute_of_injective (f : M →ₗ[ℂ] M') (hinj : Function.Injective f)
    (hf : ∀ k, f ∘ₗ ρ k = ρ' k ∘ₗ f) {k k' : κ} (h : Commute (ρ' k) (ρ' k')) :
    Commute (ρ k) (ρ k') := by
  apply LinearMap.ext
  intro m
  apply hinj
  have e1 := fun k m => LinearMap.congr_fun (hf k) m
  simp only [LinearMap.comp_apply] at e1
  simp only [Module.End.mul_apply, e1]
  exact LinearMap.congr_fun h.eq (f m)

/-- **Transfer of a cyclic dual vector along an injective intertwiner.** If `f : M → M'` is
injective, intertwines the mode actions and respects the conformal grading, then a cyclic dual
vector of `M'` pulls back to one of `M` (with `w = w' ∘ f`). -/
def _root_.VOA.CyclicEval.CyclicDual.comap {r : ℕ} (D : CyclicDual ρ' hz hpos Mdeg' r)
    (f : M →ₗ[ℂ] M')
    (hinj : Function.Injective f) (hf : ∀ k, f ∘ₗ ρ k = ρ' k ∘ₗ f)
    (hdeg : ∀ d, ∀ m ∈ Mdeg d, f m ∈ Mdeg' d) : CyclicDual ρ hz hpos Mdeg r :=
  have hc' : CartanCommute ρ' hpos := cartanCommute_of_algHom D.π D.π_X
  have hc : CartanCommute ρ hpos := fun i j => commute_of_injective f hinj hf (hc' i j)
  { w := D.w ∘ₗ f
    cyclic := fun m hm => hinj (by
      rw [map_zero]
      refine D.cyclic (f m) fun l => ?_
      rw [← word_intertwine f hf]
      exact hm l)
    supp := fun d hd m hm => D.supp d hd (f m) (hdeg d m hm)
    charge := by
      rw [LinearMap.comp_assoc, hf, ← LinearMap.comp_assoc, D.charge, LinearMap.smul_comp]
    comm := fun i => commute_of_injective f hinj hf (D.comm i)
    π := cartanCalc ρ hpos hc
    π_X := cartanCalc_X ρ hpos hc
    cartan := fun F hF => by
      have h := algHom_comp_eq_of_X (cartanCalc ρ hpos hc) D.π f (fun i => by
        rw [cartanCalc_X, D.π_X, LinearMap.comp_neg, LinearMap.neg_comp, hf]) F
      rw [LinearMap.comp_assoc, h, ← LinearMap.comp_assoc, D.cartan F hF, LinearMap.zero_comp] }

@[simp] theorem _root_.VOA.CyclicEval.CyclicDual.comap_w {r : ℕ} (D : CyclicDual ρ' hz hpos Mdeg' r)
    (f : M →ₗ[ℂ] M') (hinj : Function.Injective f) (hf : ∀ k, f ∘ₗ ρ k = ρ' k ∘ₗ f)
    (hdeg : ∀ d, ∀ m ∈ Mdeg d, f m ∈ Mdeg' d) : (D.comap f hinj hf hdeg).w = D.w ∘ₗ f := rfl

end Comap

end

end VOA.SymbolModel
