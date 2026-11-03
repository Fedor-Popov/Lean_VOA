/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.CyclicEvalOscillator
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Cyclic evaluation of invariant tensors

This file proves, for abstract modules, the inverse-system step of the coset
global-fusion strictness argument (dual orientation and total energy; highest-weight algebra
relations), in the form used by
`InvariantSymbolAssembly.LeadingCyclicEvaluation`.

## Setting

* `M` (in the note: `gr_r A`, the `r`-th corrected-filtration layer of `L_{-4/3}(sl₂)`) and `B`
  (in the note: `L_1(sl₂)`), with operator families `ρ, σ : κ → End` (the induced
  nonnegative-mode actions, indexed by `κ`; for `sl₂[t]` take `κ = Fin 3 × ℕ`).
* An invariant tensor is `x : M ⊗ B` with `(ρ k ⊗ 1 + 1 ⊗ σ k) x = 0` for all `k` (`IsInv`).
* `contract u : M ⊗ B → B`, `m ⊗ b ↦ u(m) b` — for invariant `x`, contraction against the
  restricted dual is the equivariant map `Φ_x : M^∨ → B` of the note, and
  `contract u x = Φ_x(u)`.
* `CyclicDual` (input (A) of the note): a functional `w` on `M` that is **cyclic** (the
  functionals `w ∘ ρ(k_1) ∘ ⋯ ∘ ρ(k_ℓ)` separate the points of `M`), supported in conformal
  degree `r`, of `h₀`-weight `-2r` under the negative-transpose dual action (so `Φ_x(w)` has
  charge `+2r`), and annihilated by the symmetric-center Cartan ideal:
  `w ∘ F(-ρ(h_1), -ρ(h_2), …) = 0` for `F ∈ I_r` (relation (A1), in the negative-transpose
  dual action).
* `FockCoordinates` (the standard level-one lattice realization of the charge-`r` sector):
  an injective coordinate map of each charge-`2r` energy-`E` space of `B` into
  `C[a_1, a_2, …]` of weighted degree `E - r²`, intertwining `h_{i+1}` with `2(i+1)∂_{a_i}`.

## Results (all proved outright)

* `contract_comp_of_isInv` — for invariant `x`, `Φ_x(u ∘ ρ k) = -σ k Φ_x(u)`;
* `eq_zero_of_contract_cyclic` — **cyclicity makes evaluation injective**: an invariant `x`
  with `Φ_x(w) = 0` is zero (no finite-dimensionality needed);
* `oscD_fock_contract` — `φ(Φ_x(w ∘ π F)) = F(2∂_{a_1}, 4∂_{a_2}, …) φ(Φ_x(w))`;
* `cyclicEvaluation` — the composite `φ ∘ Φ_·(w)` on any space `V` embedded in the invariants
  of total weight `N` is injective, lands in weighted degree `N - r(r+1)`, and is annihilated by
  `I_r` through `modePairing`: exactly the hypotheses of
  `finrank_le_gapTwoCoefficient_of_cyclicEvaluation`.

On injectivity (re-checked against the notes): evaluation `Φ ↦ Φ(w_r)` is injective on the
invariants because `w_r` is cyclic in the **full** `M^∨ = (gr_r A)^∨`; on the actual leading
cohomology it is injective only after composing with an injective Koszul identification. Note that
cyclicity of the Wronskian image `A_r^*` alone is not enough: `CyclicDual.cyclic` must hold for
the full physical `gr_r A` (this is where the strictness squeeze enters).
-/

namespace VOA.CyclicEval

open MvPolynomial VOA.InvariantSymbol TensorProduct
open scoped BigOperators

noncomputable section

section Contract

variable {M B : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup B] [Module ℂ B]

/-- Contraction `m ⊗ b ↦ u(m) b` (the value `Φ_x(u)` of the equivariant map of `x`). -/
def contract (u : Module.Dual ℂ M) : M ⊗[ℂ] B →ₗ[ℂ] B :=
  TensorProduct.lift ((LinearMap.lsmul ℂ B).comp u)

@[simp] theorem contract_tmul (u : Module.Dual ℂ M) (m : M) (b : B) :
    contract u (m ⊗ₜ[ℂ] b) = u m • b := by
  simp [contract]

theorem contract_rTensor (u : Module.Dual ℂ M) (f : Module.End ℂ M) (x : M ⊗[ℂ] B) :
    contract u (f.rTensor B x) = contract (u ∘ₗ f) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m b => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem contract_lTensor (u : Module.Dual ℂ M) (g : Module.End ℂ B) (x : M ⊗[ℂ] B) :
    contract u (g.lTensor M x) = g (contract u x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem contract_add (u v : Module.Dual ℂ M) (x : M ⊗[ℂ] B) :
    contract (u + v) x = contract u x + contract v x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m b => simp [add_smul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel

theorem contract_smul (c : ℂ) (u : Module.Dual ℂ M) (x : M ⊗[ℂ] B) :
    contract (c • u) x = c • contract u x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m b => simp [smul_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

theorem contract_zero (x : M ⊗[ℂ] B) : contract (0 : Module.Dual ℂ M) x = 0 := by
  have := contract_smul (0 : ℂ) (0 : Module.Dual ℂ M) x
  rwa [zero_smul, zero_smul] at this

theorem contract_neg (u : Module.Dual ℂ M) (x : M ⊗[ℂ] B) :
    contract (-u) x = -contract u x := by
  rw [← neg_one_smul ℂ u, contract_smul, neg_one_smul]

/-- **Separation.** If the contractions of `x` against a point-separating family of functionals
all vanish, then `x = 0`. -/
theorem eq_zero_of_contract_separating (U : Set (Module.Dual ℂ M))
    (hsep : ∀ m : M, (∀ u ∈ U, u m = 0) → m = 0) (x : M ⊗[ℂ] B)
    (hx : ∀ u ∈ U, contract u x = 0) : x = 0 := by
  classical
  let bB := Module.Free.chooseBasis ℂ B
  let e := TensorProduct.equivFinsuppOfBasisRight (M := M) bB
  have key : ∀ (u : Module.Dual ℂ M) i (y : M ⊗[ℂ] B),
      u (e y i) = bB.coord i (contract u y) := by
    intro u i y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul m b =>
      simp only [e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul, Finsupp.mapRange_apply,
        map_smul, smul_eq_mul, contract_tmul, Module.Basis.coord_apply]
      ring
    | add y z hy hz => rw [map_add, Finsupp.add_apply, map_add, hy, hz, map_add, map_add]
  have he : e x = 0 := by
    ext i
    rw [Finsupp.zero_apply]
    apply hsep
    intro u hu
    rw [key, hx u hu, map_zero]
  exact e.injective (by rw [he, map_zero])

end Contract

section Invariants

variable {M B : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup B] [Module ℂ B]
variable {κ : Type*} (ρ : κ → Module.End ℂ M) (σ : κ → Module.End ℂ B)

/-- Invariance of a tensor under the diagonal action `ρ k ⊗ 1 + 1 ⊗ σ k`. -/
def IsInv (x : M ⊗[ℂ] B) : Prop := ∀ k, (ρ k).rTensor B x + (σ k).lTensor M x = 0

variable {ρ σ}

/-- For an invariant tensor, `Φ_x(u ∘ ρ k) = -σ k Φ_x(u)` (the negative-transpose dual action
is intertwined with the action on `B`). -/
theorem contract_comp_of_isInv {x : M ⊗[ℂ] B} (hx : IsInv ρ σ x) (u : Module.Dual ℂ M) (k : κ) :
    contract (u ∘ₗ ρ k) x = -σ k (contract u x) := by
  rw [← contract_rTensor, eq_neg_of_add_eq_zero_left (hx k), map_neg, contract_lTensor]

/-- Mode words `ρ(k_1) ⋯ ρ(k_ℓ)`. -/
def word (ρ : κ → Module.End ℂ M) (l : List κ) : Module.End ℂ M := (l.map ρ).prod

theorem exists_contract_word {x : M ⊗[ℂ] B} (hx : IsInv ρ σ x) (l : List κ) :
    ∃ T : Module.End ℂ B, ∀ u : Module.Dual ℂ M,
      contract (u ∘ₗ word ρ l) x = T (contract u x) := by
  induction l with
  | nil => exact ⟨1, fun u => by simp [word]; rfl⟩
  | cons k l ih =>
    obtain ⟨T, hT⟩ := ih
    refine ⟨-(T * σ k), fun u => ?_⟩
    have : u ∘ₗ word ρ (k :: l) = (u ∘ₗ ρ k) ∘ₗ word ρ l := by
      simp only [word, List.map_cons, List.prod_cons, Module.End.mul_eq_comp,
        LinearMap.comp_assoc]
    rw [this, hT, contract_comp_of_isInv hx, map_neg]
    rfl

/-- **Cyclicity makes evaluation injective.** If `w` is cyclic (the functionals
`w ∘ ρ(k_1) ⋯ ρ(k_ℓ)` separate points), an invariant tensor with `Φ_x(w) = 0` is zero. -/
theorem eq_zero_of_contract_cyclic (w : Module.Dual ℂ M)
    (hcyc : ∀ m : M, (∀ l : List κ, w (word ρ l m) = 0) → m = 0)
    {x : M ⊗[ℂ] B} (hx : IsInv ρ σ x) (h0 : contract w x = 0) : x = 0 := by
  refine eq_zero_of_contract_separating {u | ∃ l, u = w ∘ₗ word ρ l} ?_ x ?_
  · intro m hm
    exact hcyc m fun l => hm _ ⟨l, rfl⟩
  · rintro _ ⟨l, rfl⟩
    obtain ⟨T, hT⟩ := exists_contract_word hx l
    rw [hT, h0, map_zero]

end Invariants

section Cyclic

variable {M B : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup B] [Module ℂ B]
variable {κ : Type*} (ρ : κ → Module.End ℂ M) (σ : κ → Module.End ℂ B)
variable (hz : κ) (hpos : ℕ → κ)
variable (Mdeg : ℤ → Submodule ℂ M) (Bdeg : ℤ → Submodule ℂ B)

/-- The total-weight-`N` part of `M ⊗ B`. -/
def tensorWeight (N : ℤ) : Submodule ℂ (M ⊗[ℂ] B) :=
  ⨆ d : ℤ, Submodule.map₂ (TensorProduct.mk ℂ M B) (Mdeg d) (Bdeg (N - d))

/-- **Input (A) of the coset note for one filtration degree `r`**: a cyclic functional on `M`
with the highest Cartan relations. Here `hz` indexes `h₀` and `hpos i` indexes `h_{i+1}`. -/
structure CyclicDual (r : ℕ) where
  /-- The cyclic vector `w_r` of the restricted dual `M^∨`. -/
  w : Module.Dual ℂ M
  /-- Cyclicity: the translates `w ∘ ρ(k_1) ⋯ ρ(k_ℓ)` separate the points of `M`. -/
  cyclic : ∀ m : M, (∀ l : List κ, w (word ρ l m) = 0) → m = 0
  /-- `w` has source conformal degree `r`. -/
  supp : ∀ d : ℤ, d ≠ (r : ℤ) → ∀ m ∈ Mdeg d, w m = 0
  /-- `w` has weight `2r` under the negative-transpose dual action of `h₀`. -/
  charge : w ∘ₗ ρ hz = (-(2 * (r : ℂ))) • w
  /-- `h₀` commutes with the positive Cartan modes on `M`. -/
  comm : ∀ i, Commute (ρ hz) (ρ (hpos i))
  /-- The polynomial calculus of the negative-transpose Cartan action: `H_{i+1} ↦ -ρ(h_{i+1})`. -/
  π : MvPolynomial ℕ ℂ →ₐ[ℂ] Module.End ℂ M
  π_X : ∀ i, π (X i) = -ρ (hpos i)
  /-- Relation (A1): the symmetric-center Cartan ideal annihilates `w`. -/
  cartan : ∀ F ∈ cartanIdeal r, w ∘ₗ π F = 0

/-- **The level-one Fock coordinates of the charge-`r` sector** of `B`: `C[a_1, a_2, …] e^{rα}`,
energy `r² + oscillator weight`, `h₀ = 2r`, `h_{i+1} = 2(i+1)∂_{a_i}`. -/
structure FockCoordinates (r : ℕ) where
  φ : B →ₗ[ℂ] MvPolynomial ℕ ℂ
  inj : ∀ (E : ℤ) (b : B), b ∈ Bdeg E → σ hz b = (2 * (r : ℂ)) • b → φ b = 0 → b = 0
  degree : ∀ (E : ℤ) (b : B), b ∈ Bdeg E → σ hz b = (2 * (r : ℂ)) • b →
    IsWeightedHomogeneous modeWeightZ (φ b) (E - (r : ℤ) * r)
  intertwine : ∀ b : B, σ hz b = (2 * (r : ℂ)) • b → ∀ i, φ (σ (hpos i) b) = oscGen i (φ b)

variable {ρ σ hz hpos Mdeg Bdeg}

theorem contract_mem_of_tensorWeight {r : ℕ} (w : Module.Dual ℂ M)
    (hsupp : ∀ d : ℤ, d ≠ (r : ℤ) → ∀ m ∈ Mdeg d, w m = 0) {N : ℤ} {x : M ⊗[ℂ] B}
    (hx : x ∈ tensorWeight Mdeg Bdeg N) : contract w x ∈ Bdeg (N - r) := by
  refine Submodule.iSup_induction _ (motive := fun x => contract w x ∈ Bdeg (N - r)) hx ?_
    (by simp) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact add_mem hx hy)
  intro d y hy
  rw [Submodule.map₂_eq_span_image2] at hy
  refine Submodule.span_induction (p := fun y _ => contract w y ∈ Bdeg (N - r)) ?_ (by simp)
    (fun x y _ _ hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact add_mem hx hy)
    (fun c x _ hx => by beta_reduce at hx ⊢; rw [map_smul]; exact Submodule.smul_mem _ c hx) hy
  rintro _ ⟨m, hm, b, hb, rfl⟩
  change contract w (m ⊗ₜ[ℂ] b) ∈ _
  rw [contract_tmul]
  by_cases hd : d = (r : ℤ)
  · subst hd; exact Submodule.smul_mem _ _ hb
  · rw [hsupp d hd m hm, zero_smul]; exact Submodule.zero_mem _

variable {r : ℕ} (D : CyclicDual ρ hz hpos Mdeg r)

include D in
theorem commute_π (F : MvPolynomial ℕ ℂ) : Commute (ρ hz) (D.π F) := by
  induction F using MvPolynomial.induction_on with
  | C a => rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]; exact Algebra.commutes a _ |>.symm
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | mul_X p i hp => rw [map_mul, D.π_X]; exact hp.mul_right (D.comm i).neg_right

/-- The contractions against `w ∘ π F` stay in the charge-`2r` sector. -/
theorem charge_contract_π {x : M ⊗[ℂ] B} (hx : IsInv ρ σ x) (F : MvPolynomial ℕ ℂ) :
    σ hz (contract (D.w ∘ₗ D.π F) x) = (2 * (r : ℂ)) • contract (D.w ∘ₗ D.π F) x := by
  have h1 := contract_comp_of_isInv hx (D.w ∘ₗ D.π F) hz
  have h2 : (D.w ∘ₗ D.π F) ∘ₗ ρ hz = (-(2 * (r : ℂ))) • (D.w ∘ₗ D.π F) := by
    rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← (commute_π D F).eq,
      Module.End.mul_eq_comp, ← LinearMap.comp_assoc, D.charge, LinearMap.smul_comp]
  rw [h2, contract_smul] at h1
  rw [neg_smul] at h1
  exact (neg_inj.mp h1).symm

/-- **The Fock image of the Cartan-translated contractions**:
`φ(Φ_x(w ∘ π F)) = F(2∂_{a_1}, 4∂_{a_2}, …) φ(Φ_x(w))`. -/
theorem oscD_fock_contract (Φ : FockCoordinates σ hz hpos Bdeg r) {x : M ⊗[ℂ] B}
    (hx : IsInv ρ σ x) (F : MvPolynomial ℕ ℂ) :
    Φ.φ (contract (D.w ∘ₗ D.π F) x) = oscD F (Φ.φ (contract D.w x)) := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul, contract_smul, map_smul,
      LinearMap.smul_apply]
    rfl
  | add p q hp hq =>
    rw [map_add, LinearMap.comp_add, contract_add, map_add, hp, hq, map_add,
      LinearMap.add_apply]
  | mul_X p i hp =>
    have hcomp : D.w ∘ₗ D.π (p * X i) = -((D.w ∘ₗ D.π p) ∘ₗ ρ (hpos i)) := by
      rw [map_mul, D.π_X, mul_neg, Module.End.mul_eq_comp, LinearMap.comp_neg,
        LinearMap.comp_assoc]
    rw [hcomp, contract_neg, contract_comp_of_isInv hx, neg_neg,
      Φ.intertwine _ (charge_contract_π D hx p), hp, mul_comm, map_mul, oscD_X,
      Module.End.mul_apply]

/-- **The cyclic evaluation of a space of invariant tensors.** Any `V` embedded linearly and
injectively in the invariants of total weight `N` evaluates injectively into the oscillator
polynomials of weighted degree `N - r(r+1)`, with image annihilated by the Cartan ideal through
`modePairing`. -/
theorem cyclicEvaluation (Φ : FockCoordinates σ hz hpos Bdeg r) {V : Type*} [AddCommGroup V]
    [Module ℂ V] (N : ℤ) (ι : V →ₗ[ℂ] M ⊗[ℂ] B) (hι : Function.Injective ι)
    (hinv : ∀ v, IsInv ρ σ (ι v)) (hwt : ∀ v, ι v ∈ tensorWeight Mdeg Bdeg N) :
    Function.Injective (Φ.φ ∘ₗ contract D.w ∘ₗ ι) ∧
    (∀ v, IsWeightedHomogeneous modeWeightZ ((Φ.φ ∘ₗ contract D.w ∘ₗ ι) v)
      (N - r * (r + 1))) ∧
    (∀ v (F : MvPolynomial ℕ ℂ), F ∈ cartanIdeal r →
      modePairing F ((Φ.φ ∘ₗ contract D.w ∘ₗ ι) v) = 0) := by
  have hcharge : ∀ v, σ hz (contract D.w (ι v)) = (2 * (r : ℂ)) • contract D.w (ι v) := by
    intro v
    have := charge_contract_π D (hinv v) 1
    simpa only [map_one, LinearMap.comp_id] using this
  refine ⟨?_, ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    rw [Submodule.mem_bot]
    have hb := Φ.inj _ _ (contract_mem_of_tensorWeight D.w D.supp (hwt v)) (hcharge v) hv
    exact hι (by rw [eq_zero_of_contract_cyclic D.w D.cyclic (hinv v) hb, map_zero])
  · intro v
    have h := Φ.degree _ _ (contract_mem_of_tensorWeight D.w D.supp (hwt v)) (hcharge v)
    have he : (N - r) - (r : ℤ) * r = N - r * (r + 1) := by ring
    rw [he] at h
    exact h
  · intro v F hF
    have h := oscD_fock_contract D Φ (hinv v) F
    rw [D.cartan F hF, contract_zero, map_zero] at h
    change modePairing F (Φ.φ (contract D.w (ι v))) = 0
    rw [← constantCoeff_oscD, ← h, map_zero]

end Cyclic

end

end VOA.CyclicEval
