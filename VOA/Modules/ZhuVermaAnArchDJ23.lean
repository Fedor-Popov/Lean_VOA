/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUFullRho

/-!
# Dong–Jiang Lemma 2.3 named, and the representative-level commutator of `M(U)`

Dong–Jiang's Lemma 4.7 (the commutator formula `[a_p, b_q] = ∑_i C(p,i)(a_i b)_{p+q−i}` on `M(U)`,
the `hbracket` input of the `V̂`-representation) rests on two purely `𝒱`-level ideal-membership
statements about the general product `∗ⁿ_{m,p}` — no module structure involved:

* **`DJ23Comm`** (DJ Lemma 2.3): for `p₁ + p₂ − m = N ≥ 0`,
  `a ∗^N_{m,p₁} b − b ∗^N_{m,p₂} a − Res_z (1+z)^{wt a − 1 + m − p₂} Y(a,z)b ∈ O'_{N,m}`,
  the residue written as the (finite) mode sum `∑ᶠ i, C(wt a − 1 + m − p₂, i)·a₍ᵢ₎b`.
  DJ prove it from the skew relation `Y(v,z)u ≡ (1+z)^{…}Y(u,−z/(1+z))v (mod O')` together with
  Appendix Proposition 5.1 (`A_{p₁,p₂}(z) = 1`, engine-verified for `0 ≤ p₁,p₂ ≤ 7`).
  **Not yet formalized in the repo** — neither is the skew relation it rests on.

* **`DJ48Bdry`** (DJ Lemma 4.8', the `la4.8` boundary lemma): the same relation when one of
  `p₁, p₂` is negative, i.e. when one of the two mode compositions is identically zero.

This file names both and **proves the mathematical core**: `anmGen_commutator_interior`, the
representative-level commutator in the interior regime, derived from `DJ23Comm` together with the
two proved unconditional results

* `mUFullCompAssoc_holds` (DJ Thm 2.9 ψ-associativity on the full ideal), and
* `anmGen_OnmFull_right_unconditional` (DJ Lemma 2.8, right inclusion),

so the entire `M(U)` commutator formula is reduced to the two pure-`𝒱` Dong–Jiang leaves above.

## Index bookkeeping (engine-verified)

For `a` of weight `K` at source level `n` and modes `p, q`, the three levels involved are
`n₁ = wt b − q − 1 + n` (the `b_q` target), `n₂ = K − p − 1 + n` (the `a_p` target) and
`N = K + wt b − p − q − 2 + n` (the common target).  Then `n₁ + n₂ − n = N`, so `DJ23Comm` applies
at base level `m := n` with `p₁ := n₁`, `p₂ := n₂`, and its residue exponent
`K − 1 + n − n₂` is exactly `p`.  (Both identities checked symbolically over
`0 ≤ K, wt b, n ≤ 3`, `−2 ≤ p, q ≤ 3`.)

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §2 (Lemma 2.3, Lemma 2.4), §4 (Lemma 4.7, Lemma `la4.8`), Appendix
(Prop 5.1); `ZhuVermaAnArchMUFullAction` (`mUFullCompAssoc_holds`), `ZhuVermaAnArchDJ28Final`
(`anmGen_OnmFull_right_unconditional`), `ZhuVermaAnArchMUFullRho` (`MUFullBracket`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped TensorProduct DirectSum BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The residue `Res_z (1+z)^E Y(a,z)b` as a finite mode sum. -/

/-- `Res_z (1+z)^E Y(a,z)b = ∑_{i ≥ 0} C(E,i)·a₍ᵢ₎b`, the sum being finite by VOA regularity. -/
noncomputable def resExp (W : VertexOperatorAlgebra 𝒱) (E : ℤ) (a b : 𝒱) : 𝒱 :=
  ∑ᶠ i : ℕ, gBinom E i • W.smul a i b

/-- The mode family `i ↦ C(E,i)·a₍ᵢ₎b` has finite support (VOA regularity). -/
theorem resExp_support_finite (W : VertexOperatorAlgebra 𝒱) (E : ℤ) (a b : 𝒱) :
    (Function.support fun i : ℕ => gBinom E i • W.smul a i b).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
  refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Iio]
  by_contra hcon
  rw [not_lt] at hcon
  exact hi (by rw [hNz i (by omega), smul_zero])

/-! ## The two Dong–Jiang leaves. -/

/-- **DJ Lemma 2.3** — the cross relation between the two orders of the general product.  For
homogeneous `a` of weight `K` and `p₁ + p₂ − m = N ≥ 0`,

  `a ∗^N_{m,p₁} b − b ∗^N_{m,p₂} a − Res_z (1+z)^{K−1+m−p₂} Y(a,z)b ∈ O'_{N,m}(𝒱)`.

DJ's proof: rewrite `b ∗^N_{m,p₂} a` by the skew relation
`Y(b,z)a ≡ (1+z)^{−K−wt b−2m+p₁+p₂} Y(a,−z/(1+z))b (mod O'_{N,m})`, collect, and apply Appendix
Prop 5.1 (`A_{p₁,p₂}(z) = 1`).  A carried `Prop` — never an axiom. -/
def DJ23Comm (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (K : ℤ) (a : 𝒱), a ∈ W.grading K → ∀ (b : 𝒱) (m p₁ p₂ N : ℕ),
    (N : ℤ) = (p₁ : ℤ) + (p₂ : ℤ) - (m : ℤ) →
      anmGen W N m p₁ a b - anmGen W N m p₂ b a
          - resExp W (K - 1 + (m : ℤ) - (p₂ : ℤ)) a b
        ∈ Onm W N m

/-- **DJ Lemma `la4.8`** — the boundary companion of Lemma 2.3, used when one of the two mode
compositions in `[a_p, b_q]` is identically zero (`p₁ < 0` or `p₂ < 0`, where the corresponding
product `∗` is not even defined).  DJ state it as: for `p₁ ≥ 0 > p₂` with `p₁ + p₂ − m ≥ 0`,
`a ∗^{p₁+p₂−m}_{m,p₁} b − Res_z (1+z)^{wt a − 1 + m − p₂} Y(a,z)b ∈ O'_{p₁+p₂−m,m}`, and
symmetrically for `p₂ ≥ 0 > p₁`.  Here `p₂ < 0` is encoded by the integer `d = p₂`. -/
def DJ48Bdry (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (K : ℤ) (a : 𝒱), a ∈ W.grading K → ∀ (b : 𝒱) (m p₁ N : ℕ) (d : ℤ),
    d < 0 → (N : ℤ) = (p₁ : ℤ) + d - (m : ℤ) →
      anmGen W N m p₁ a b - resExp W (K - 1 + (m : ℤ) - d) a b ∈ Onm W N m

/-! ## Linearity of the general product over the residue's finite mode sum. -/

theorem anmGen_resExp_left (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (E : ℤ) (a b g : 𝒱) :
    anmGen W n m p (resExp W E a b) g
      = ∑ᶠ i : ℕ, gBinom E i • anmGen W n m p (W.smul a i b) g := by
  have hfin := resExp_support_finite W E a b
  have h := map_finsum (anmGenLeftMap W n m p g) hfin
  simp only [anmGenLeftMap_apply] at h
  rw [resExp, h]
  exact finsum_congr fun i => by
    rw [show anmGen W n m p (gBinom E i • W.smul a i b) g
        = anmGenLeftMap W n m p g (gBinom E i • W.smul a i b) from rfl, map_smul,
      anmGenLeftMap_apply]

/-! ## The representative-level commutator — the core of DJ Lemma 4.7. -/

/-- **The representative-level commutator of `M(U)`, interior regime.**

For homogeneous `a` of weight `K`, levels `n, n₁, n₂, N` with `N = n₁ + n₂ − n`, and
`p = K − 1 + n − n₂`,

  `a ∗^N_{0,n₁}(b ∗^{n₁}_{0,n} g) − b ∗^N_{0,n₂}(a ∗^{n₂}_{0,n} g)
     ≡ ∑ᵢ C(p,i) · (a₍ᵢ₎b) ∗^N_{0,n} g   (mod O_{N,0})`,

which is exactly `[a_p, b_q] = ∑ᵢ C(p,i)(a₍ᵢ₎b)_{p+q−i}` read on representatives.  Proved from
`DJ23Comm` together with the two proved unconditional Dong–Jiang results
`mUFullCompAssoc_holds` (Thm 2.9) and `anmGen_OnmFull_right_unconditional` (Lemma 2.8 right). -/
theorem anmGen_commutator_interior (W : VertexOperatorAlgebra 𝒱) (hdj : DJ23Comm W)
    {K : ℤ} {a : 𝒱} (ha : a ∈ W.grading K) (b : 𝒱) {n n₁ n₂ N : ℕ} {p : ℤ}
    (hN : (N : ℤ) = (n₁ : ℤ) + (n₂ : ℤ) - (n : ℤ)) (hp : p = K - 1 + (n : ℤ) - (n₂ : ℤ)) (g : 𝒱) :
    anmGen W N 0 n₁ a (anmGen W n₁ 0 n b g) - anmGen W N 0 n₂ b (anmGen W n₂ 0 n a g)
        - ∑ᶠ i : ℕ, gBinom p i • anmGen W N 0 n (W.smul a i b) g
      ∈ OnmFull W N 0 := by
  -- the two ψ-associativity reassociations (proved, unconditional)
  have h₁ : anmGen W N 0 n₁ a (anmGen W n₁ 0 n b g)
      - anmGen W N 0 n (anmGen W N n n₁ a b) g ∈ OnmFull W N 0 :=
    mUFullCompAssoc_holds W N n n₁ a b g
  have h₂ : anmGen W N 0 n₂ b (anmGen W n₂ 0 n a g)
      - anmGen W N 0 n (anmGen W N n n₂ b a) g ∈ OnmFull W N 0 :=
    mUFullCompAssoc_holds W N n n₂ b a g
  -- DJ Lemma 2.3 at base level `n`, transported into the full ideal by Lemma 2.8's right inclusion
  have hD : anmGen W N n n₁ a b - anmGen W N n n₂ b a - resExp W p a b ∈ OnmFull W N n := by
    have := hdj K a ha b n n₁ n₂ N hN
    rw [← hp] at this
    exact Onm_le_OnmFull W N n this
  have h₃ : anmGen W N 0 n
      (anmGen W N n n₁ a b - anmGen W N n n₂ b a - resExp W p a b) g ∈ OnmFull W N 0 :=
    anmGen_OnmFull_right_unconditional W N 0 n g _ hD
  -- expand the left slot and identify the residue sum
  rw [show anmGen W N 0 n (anmGen W N n n₁ a b - anmGen W N n n₂ b a - resExp W p a b) g
      = anmGen W N 0 n (anmGen W N n n₁ a b) g - anmGen W N 0 n (anmGen W N n n₂ b a) g
        - anmGen W N 0 n (resExp W p a b) g from by
    have := (anmGenLeftMap W N 0 n g).map_sub
      (anmGen W N n n₁ a b - anmGen W N n n₂ b a) (resExp W p a b)
    have h' := (anmGenLeftMap W N 0 n g).map_sub
      (anmGen W N n n₁ a b) (anmGen W N n n₂ b a)
    simp only [anmGenLeftMap_apply] at this h'
    rw [this, h'], anmGen_resExp_left] at h₃
  -- reassemble
  have hcomb : anmGen W N 0 n₁ a (anmGen W n₁ 0 n b g)
      - anmGen W N 0 n₂ b (anmGen W n₂ 0 n a g)
      - ∑ᶠ i : ℕ, gBinom p i • anmGen W N 0 n (W.smul a i b) g
    = (anmGen W N 0 n₁ a (anmGen W n₁ 0 n b g) - anmGen W N 0 n (anmGen W N n n₁ a b) g)
      - (anmGen W N 0 n₂ b (anmGen W n₂ 0 n a g) - anmGen W N 0 n (anmGen W N n n₂ b a) g)
      + (anmGen W N 0 n (anmGen W N n n₁ a b) g - anmGen W N 0 n (anmGen W N n n₂ b a) g
          - ∑ᶠ i : ℕ, gBinom p i • anmGen W N 0 n (W.smul a i b) g) := by abel
  rw [hcomb]
  exact (OnmFull W N 0).add_mem ((OnmFull W N 0).sub_mem h₁ h₂) h₃

/-! ## The operator-level commutator on `M(U)` generators (interior regime). -/

/-- `a ∗ⁿ_{m,p} (·)` is zero on a zero left factor. -/
private theorem anmGen_left_zero (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (v : 𝒱) :
    anmGen W n m p 0 v = 0 := by
  have := anmGen_smul_left W n m p (0 : ℂ) 0 v
  simpa using this

/-- The commutator's OPE family has finite support at the level of representatives. -/
theorem commSum_repr_support_finite (W : VertexOperatorAlgebra 𝒱) (N n : ℕ) (p : ℤ) (a b g : 𝒱) :
    (Function.support fun i : ℕ => gBinom p i • anmGen W N 0 n (W.smul a i b) g).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
  refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Iio]
  by_contra hcon
  rw [not_lt] at hcon
  exact hi (by rw [hNz i (by omega), anmGen_left_zero, smul_zero])

/-- The commutator's OPE family has finite support at the level of `M(U)` operators. -/
theorem commSum_op_support_finite (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (N n : ℕ) (p : ℤ)
    (a b : 𝒱) (y : MUPieceFull W U n) :
    (Function.support fun i : ℕ => gBinom p i • oFullU W U N n (W.smul a i b) y).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
  refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Iio]
  by_contra hcon
  rw [not_lt] at hcon
  refine hi ?_
  rw [hNz i (by omega)]
  have h0 : oFullU W U N n (0 : 𝒱) = 0 := by
    have := oFullU_smul_acting W U N n (0 : ℂ) 0
    simpa using this
  rw [h0]
  simp

/-- **DJ Lemma 4.7 on generators, interior regime** — the commutator formula for the `M(U)` mode
operators, read on a generator `[g] ⊗ w` of the level-`n` piece:

  `a_p b_q ([g]⊗w) − b_q a_p ([g]⊗w) = ∑ᵢ C(p,i) · (a₍ᵢ₎b)_{p+q−i} ([g]⊗w)`,

with `n₁` the `b_q` target, `n₂` the `a_p` target, `N = n₁ + n₂ − n` the common target and
`p = wt a − 1 + n − n₂`.  Obtained from the representative-level core
`anmGen_commutator_interior` by descending through `mkAnmFull` and `⊗ w`. -/
theorem oFullU_commutator_interior_tmul (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hdj : DJ23Comm W) {K : ℤ} {a : 𝒱} (ha : a ∈ W.grading K) (b : 𝒱) {n n₁ n₂ N : ℕ} {p : ℤ}
    (hN : (N : ℤ) = (n₁ : ℤ) + (n₂ : ℤ) - (n : ℤ)) (hp : p = K - 1 + (n : ℤ) - (n₂ : ℤ))
    (g : 𝒱) (w : U.carrier) :
    oFullU W U N n₁ a (oFullU W U n₁ n b (mkAnmFull W n 0 g ⊗ₜ[ℂ] w))
        - oFullU W U N n₂ b (oFullU W U n₂ n a (mkAnmFull W n 0 g ⊗ₜ[ℂ] w))
      = ∑ᶠ i : ℕ, gBinom p i • oFullU W U N n (W.smul a i b) (mkAnmFull W n 0 g ⊗ₜ[ℂ] w) := by
  -- `⊗ w` as a linear map, to move the OPE finsum across the tensor factor
  let φ : AnmFull W N 0 →ₗ[ℂ] MUPieceFull W U N :=
    { toFun := fun z => z ⊗ₜ[ℂ] w
      map_add' := fun z₁ z₂ => TensorProduct.add_tmul z₁ z₂ w
      map_smul' := fun c z => TensorProduct.smul_tmul' c z w }
  have hfin₁ := commSum_repr_support_finite W N n p a b g
  have hfin₂ : (Function.support fun i : ℕ =>
      mkAnmFull W N 0 (gBinom p i • anmGen W N 0 n (W.smul a i b) g)).Finite := by
    refine Set.Finite.subset hfin₁ (fun i hi => ?_)
    rw [Function.mem_support] at hi ⊢
    intro hz
    exact hi (by rw [hz, map_zero])
  -- the right-hand side, pushed onto representatives
  have hRHS : (∑ᶠ i : ℕ, gBinom p i • oFullU W U N n (W.smul a i b) (mkAnmFull W n 0 g ⊗ₜ[ℂ] w))
      = mkAnmFull W N 0 (∑ᶠ i : ℕ, gBinom p i • anmGen W N 0 n (W.smul a i b) g) ⊗ₜ[ℂ] w := by
    calc (∑ᶠ i : ℕ, gBinom p i • oFullU W U N n (W.smul a i b) (mkAnmFull W n 0 g ⊗ₜ[ℂ] w))
        = ∑ᶠ i : ℕ, φ (mkAnmFull W N 0 (gBinom p i • anmGen W N 0 n (W.smul a i b) g)) := by
          refine finsum_congr fun i => ?_
          rw [oFullU_tmul]
          show _ = ((gBinom p i • anmGen W N 0 n (W.smul a i b) g |> mkAnmFull W N 0)) ⊗ₜ[ℂ] w
          rw [map_smul, TensorProduct.smul_tmul']
      _ = φ (∑ᶠ i : ℕ, mkAnmFull W N 0 (gBinom p i • anmGen W N 0 n (W.smul a i b) g)) :=
          (map_finsum φ hfin₂).symm
      _ = φ (mkAnmFull W N 0 (∑ᶠ i : ℕ, gBinom p i • anmGen W N 0 n (W.smul a i b) g)) := by
          rw [map_finsum (mkAnmFull W N 0) hfin₁]
      _ = mkAnmFull W N 0 (∑ᶠ i : ℕ, gBinom p i • anmGen W N 0 n (W.smul a i b) g) ⊗ₜ[ℂ] w := rfl
  rw [hRHS, oFullU_tmul, oFullU_tmul, oFullU_tmul, oFullU_tmul, ← TensorProduct.sub_tmul,
    ← map_sub]
  congr 1
  rw [← sub_eq_zero, ← map_sub, mkAnmFull, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact anmGen_commutator_interior W hdj ha b hN hp g

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.resExp
  #print axioms VOA.anmGen_resExp_left
  #print axioms VOA.anmGen_commutator_interior
  #print axioms VOA.oFullU_commutator_interior_tmul
-/
