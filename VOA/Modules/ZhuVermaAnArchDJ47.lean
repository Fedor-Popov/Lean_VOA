/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ48

/-!
# Dong–Jiang Lemma 4.7 — the representative-level commutator in **every** regime

`ZhuVermaAnArchDJ23Final` closed the *interior* regime of DJ Lemma 4.7 (both intermediate levels
nonnegative).  This file adds the two boundary regimes, in which one of the two mode compositions is
identically zero because its intermediate level is negative:

* `anmGen_commutator_bdryA` — the `b`-target `n₁` is negative, so `a_m b_k = 0`;
* `anmGen_commutator_bdryB` — the `a`-target `n₂` is negative, so `b_k a_m = 0`.

Both follow from the proved composition associativity `mUFullCompAssoc_holds` (DJ Thm 2.9) together
with the corresponding boundary lemma `dj48_case2` / `dj48_case1`, transported into the full ideal by
`anmGen_OnmFull_right_unconditional` (DJ Lemma 2.8 right) — exactly the pattern of the interior case.

The negativity of the missing level is recorded, as in `ZhuVermaAnArchDJ48`, by the single `ℕ`-level
inequality `N + n < n₂` (resp. `N + n < n₁`): from `N = n₁ + n₂ − n`, one level is negative precisely
when the other exceeds `N + n`.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §4 (Lemma 4.7, Lemma `la4.8`); `ZhuVermaAnArchDJ48` (`dj48_case1`,
`dj48_case2`), `ZhuVermaAnArchDJ23` (`anmGen_resExp_left`, `resExp`),
`ZhuVermaAnArchMUFullAction` (`mUFullCompAssoc_holds`), `ZhuVermaAnArchDJ28Final`
(`anmGen_OnmFull_right_unconditional`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped TensorProduct DirectSum BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Boundary regime A: the `b`-target is negative (`a_m b_k = 0`). -/

/-- **DJ Lemma 4.7, boundary regime A** — the `b`-target level `n₁ = N + n − n₂` is negative
(equivalently `N + n < n₂`), so the composition `a_m b_k` vanishes and only `−b_k a_m` survives:

  `−b ∗^N_{0,n₂}(a ∗^{n₂}_{0,n} g) ≡ ∑ᵢ C(p,i)·(a₍ᵢ₎b) ∗^N_{0,n} g   (mod O_{N,0})`,

with `p = wt a − 1 + n − n₂`. -/
theorem anmGen_commutator_bdryA (W : VertexOperatorAlgebra 𝒱) {K M : ℕ} {a b : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hb : b ∈ W.grading (M : ℤ)) {n n₂ N : ℕ} {p : ℤ}
    (hlt : (N : ℤ) + (n : ℤ) < (n₂ : ℤ)) (hp : p = (K : ℤ) - 1 + (n : ℤ) - (n₂ : ℤ)) (g : 𝒱) :
    -anmGen W N 0 n₂ b (anmGen W n₂ 0 n a g)
        - ∑ᶠ i : ℕ, gBinom p i • anmGen W N 0 n (W.smul a i b) g
      ∈ OnmFull W N 0 := by
  -- reassociate (proved, unconditional)
  have h₂ : anmGen W N 0 n₂ b (anmGen W n₂ 0 n a g)
      - anmGen W N 0 n (anmGen W N n n₂ b a) g ∈ OnmFull W N 0 :=
    mUFullCompAssoc_holds W N n n₂ b a g
  -- the boundary swap (DJ `la4.8` case 2) at base level `n`
  have hD : -anmGen W N n n₂ b a - resExp W p a b ∈ OnmFull W N n := by
    have := dj48_case2 W ha hb n n₂ N hlt
    rw [← hp] at this
    exact Onm_le_OnmFull W N n this
  have h₃ : anmGen W N 0 n (-anmGen W N n n₂ b a - resExp W p a b) g ∈ OnmFull W N 0 :=
    anmGen_OnmFull_right_unconditional W N 0 n g _ hD
  rw [show anmGen W N 0 n (-anmGen W N n n₂ b a - resExp W p a b) g
      = -anmGen W N 0 n (anmGen W N n n₂ b a) g - anmGen W N 0 n (resExp W p a b) g from by
    have h1 := (anmGenLeftMap W N 0 n g).map_sub (-anmGen W N n n₂ b a) (resExp W p a b)
    have h2 := (anmGenLeftMap W N 0 n g).map_neg (anmGen W N n n₂ b a)
    simp only [anmGenLeftMap_apply] at h1 h2
    rw [h1, h2], anmGen_resExp_left] at h₃
  have hcomb : -anmGen W N 0 n₂ b (anmGen W n₂ 0 n a g)
      - ∑ᶠ i : ℕ, gBinom p i • anmGen W N 0 n (W.smul a i b) g
    = -(anmGen W N 0 n₂ b (anmGen W n₂ 0 n a g) - anmGen W N 0 n (anmGen W N n n₂ b a) g)
      + (-anmGen W N 0 n (anmGen W N n n₂ b a) g
          - ∑ᶠ i : ℕ, gBinom p i • anmGen W N 0 n (W.smul a i b) g) := by abel
  rw [hcomb]
  exact (OnmFull W N 0).add_mem ((OnmFull W N 0).neg_mem h₂) h₃

/-! ## Boundary regime B: the `a`-target is negative (`b_k a_m = 0`). -/

/-- **DJ Lemma 4.7, boundary regime B** — the `a`-target level `n₂ = N + n − n₁` is negative
(equivalently `N + n < n₁`), so the composition `b_k a_m` vanishes and only `a_m b_k` survives:

  `a ∗^N_{0,n₁}(b ∗^{n₁}_{0,n} g) ≡ ∑ᵢ C(p,i)·(a₍ᵢ₎b) ∗^N_{0,n} g   (mod O_{N,0})`,

with `p = wt a − 1 + n₁ − N` (the mode index; `n₂ < 0` makes `wt a − 1 + n − n₂` equal to it). -/
theorem anmGen_commutator_bdryB (W : VertexOperatorAlgebra 𝒱) {K : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (b : 𝒱) {n n₁ N : ℕ} {p : ℤ}
    (hlt : (N : ℤ) + (n : ℤ) < (n₁ : ℤ)) (hp : p = (K : ℤ) - 1 + (n₁ : ℤ) - (N : ℤ)) (g : 𝒱) :
    anmGen W N 0 n₁ a (anmGen W n₁ 0 n b g)
        - ∑ᶠ i : ℕ, gBinom p i • anmGen W N 0 n (W.smul a i b) g
      ∈ OnmFull W N 0 := by
  have h₁ : anmGen W N 0 n₁ a (anmGen W n₁ 0 n b g)
      - anmGen W N 0 n (anmGen W N n n₁ a b) g ∈ OnmFull W N 0 :=
    mUFullCompAssoc_holds W N n n₁ a b g
  -- the boundary identity (DJ `la4.8` case 1) at base level `n` — an exact equality
  have hD : anmGen W N n n₁ a b = resExp W p a b := by
    rw [hp]
    exact dj48_case1 W ha b n n₁ N hlt
  rw [hD] at h₁
  rw [anmGen_resExp_left] at h₁
  exact h₁

/-! ## Descending a representative-level congruence to the `M(U)` operators. -/

/-- **The descent helper.**  If a linear operator `Φ : M(U)(n) → M(U)(N)` is induced on generators
by a representative-level map `φ : 𝒱 → 𝒱`, and `φ g` agrees with the OPE tail
`∑ᵢ C(p,i)·(a₍ᵢ₎b) ∗^N_{0,n} g` modulo `O_{N,0}`, then `Φ` **is** the corresponding operator OPE
tail — on every element of `M(U)(n)`, not just generators. -/
theorem oFullU_eq_of_repr_mem (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {n N : ℕ} {p : ℤ}
    (a b : 𝒱) (Φ : MUPieceFull W U n →ₗ[ℂ] MUPieceFull W U N) (φ : 𝒱 → 𝒱)
    (hΦ : ∀ (g : 𝒱) (w : U.carrier),
      Φ (mkAnmFull W n 0 g ⊗ₜ[ℂ] w) = mkAnmFull W N 0 (φ g) ⊗ₜ[ℂ] w)
    (hmem : ∀ g : 𝒱,
      φ g - ∑ᶠ i : ℕ, gBinom p i • anmGen W N 0 n (W.smul a i b) g ∈ OnmFull W N 0)
    (x : MUPieceFull W U n) :
    Φ x = ∑ᶠ i : ℕ, gBinom p i • oFullU W U N n (W.smul a i b) x := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [map_zero]
    refine (finsum_eq_zero_of_forall_eq_zero fun i => ?_).symm
    rw [map_zero, smul_zero]
  | tmul t w =>
    obtain ⟨g, rfl⟩ := (OnmFull W n 0).mkQ_surjective t
    show Φ (mkAnmFull W n 0 g ⊗ₜ[ℂ] w)
      = ∑ᶠ i : ℕ, gBinom p i • oFullU W U N n (W.smul a i b) (mkAnmFull W n 0 g ⊗ₜ[ℂ] w)
    rw [hΦ g w]
    -- push the OPE tail onto representatives
    let ψ : AnmFull W N 0 →ₗ[ℂ] MUPieceFull W U N :=
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
    have hRHS : (∑ᶠ i : ℕ, gBinom p i • oFullU W U N n (W.smul a i b)
          (mkAnmFull W n 0 g ⊗ₜ[ℂ] w))
        = mkAnmFull W N 0 (∑ᶠ i : ℕ, gBinom p i • anmGen W N 0 n (W.smul a i b) g) ⊗ₜ[ℂ] w := by
      calc (∑ᶠ i : ℕ, gBinom p i • oFullU W U N n (W.smul a i b) (mkAnmFull W n 0 g ⊗ₜ[ℂ] w))
          = ∑ᶠ i : ℕ, ψ (mkAnmFull W N 0 (gBinom p i • anmGen W N 0 n (W.smul a i b) g)) := by
            refine finsum_congr fun i => ?_
            rw [oFullU_tmul]
            show _ = ((gBinom p i • anmGen W N 0 n (W.smul a i b) g |> mkAnmFull W N 0))
              ⊗ₜ[ℂ] w
            rw [map_smul, TensorProduct.smul_tmul']
        _ = ψ (∑ᶠ i : ℕ, mkAnmFull W N 0 (gBinom p i • anmGen W N 0 n (W.smul a i b) g)) :=
            (map_finsum ψ hfin₂).symm
        _ = ψ (mkAnmFull W N 0 (∑ᶠ i : ℕ, gBinom p i • anmGen W N 0 n (W.smul a i b) g)) := by
            rw [map_finsum (mkAnmFull W N 0) hfin₁]
        _ = _ := rfl
    rw [hRHS, ← sub_eq_zero, ← TensorProduct.sub_tmul, ← map_sub,
      show mkAnmFull W N 0 (φ g - ∑ᶠ i : ℕ, gBinom p i • anmGen W N 0 n (W.smul a i b) g) = 0 from by
        rw [mkAnmFull, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hmem g]
    exact TensorProduct.zero_tmul _ _
  | add x y hx hy =>
    rw [map_add, hx, hy]
    rw [← finsum_add_distrib (commSum_op_support_finite W U N n p a b x)
      (commSum_op_support_finite W U N n p a b y)]
    exact finsum_congr fun i => by rw [map_add, smul_add]

/-! ## The three regimes at the operator level, on all of `M(U)(n)`. -/

/-- **Interior regime, operator level** (both intermediate levels nonnegative). -/
theorem oFullU_comm_interior_gen (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {K : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading K) (b : 𝒱) {n n₁ n₂ N : ℕ} {p : ℤ}
    (hN : (N : ℤ) = (n₁ : ℤ) + (n₂ : ℤ) - (n : ℤ)) (hp : p = K - 1 + (n : ℤ) - (n₂ : ℤ))
    (x : MUPieceFull W U n) :
    oFullU W U N n₁ a (oFullU W U n₁ n b x) - oFullU W U N n₂ b (oFullU W U n₂ n a x)
      = ∑ᶠ i : ℕ, gBinom p i • oFullU W U N n (W.smul a i b) x := by
  have h := oFullU_eq_of_repr_mem W U a b
    ((oFullU W U N n₁ a).comp (oFullU W U n₁ n b) - (oFullU W U N n₂ b).comp (oFullU W U n₂ n a))
    (fun g => anmGen W N 0 n₁ a (anmGen W n₁ 0 n b g) - anmGen W N 0 n₂ b (anmGen W n₂ 0 n a g))
    (fun g w => by
      show oFullU W U N n₁ a (oFullU W U n₁ n b (mkAnmFull W n 0 g ⊗ₜ[ℂ] w))
        - oFullU W U N n₂ b (oFullU W U n₂ n a (mkAnmFull W n 0 g ⊗ₜ[ℂ] w)) = _
      rw [oFullU_tmul, oFullU_tmul, oFullU_tmul, oFullU_tmul, ← TensorProduct.sub_tmul, ← map_sub])
    (fun g => anmGen_commutator_interior_uncond W ha b hN hp g) x
  simpa only [LinearMap.sub_apply, LinearMap.comp_apply] using h

/-- **Boundary regime A, operator level** — the `b`-target is negative, so `a_m b_k = 0`. -/
theorem oFullU_comm_bdryA_gen (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {K M : ℕ} {a b : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hb : b ∈ W.grading (M : ℤ)) {n n₂ N : ℕ} {p : ℤ}
    (hlt : (N : ℤ) + (n : ℤ) < (n₂ : ℤ)) (hp : p = (K : ℤ) - 1 + (n : ℤ) - (n₂ : ℤ))
    (x : MUPieceFull W U n) :
    -oFullU W U N n₂ b (oFullU W U n₂ n a x)
      = ∑ᶠ i : ℕ, gBinom p i • oFullU W U N n (W.smul a i b) x := by
  have h := oFullU_eq_of_repr_mem W U a b
    (-(oFullU W U N n₂ b).comp (oFullU W U n₂ n a))
    (fun g => -anmGen W N 0 n₂ b (anmGen W n₂ 0 n a g))
    (fun g w => by
      show -oFullU W U N n₂ b (oFullU W U n₂ n a (mkAnmFull W n 0 g ⊗ₜ[ℂ] w)) = _
      rw [oFullU_tmul, oFullU_tmul, ← TensorProduct.neg_tmul, ← map_neg])
    (fun g => anmGen_commutator_bdryA W ha hb hlt hp g) x
  simpa only [LinearMap.neg_apply, LinearMap.comp_apply] using h

/-- **Boundary regime B, operator level** — the `a`-target is negative, so `b_k a_m = 0`. -/
theorem oFullU_comm_bdryB_gen (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {K : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (b : 𝒱) {n n₁ N : ℕ} {p : ℤ}
    (hlt : (N : ℤ) + (n : ℤ) < (n₁ : ℤ)) (hp : p = (K : ℤ) - 1 + (n₁ : ℤ) - (N : ℤ))
    (x : MUPieceFull W U n) :
    oFullU W U N n₁ a (oFullU W U n₁ n b x)
      = ∑ᶠ i : ℕ, gBinom p i • oFullU W U N n (W.smul a i b) x := by
  have h := oFullU_eq_of_repr_mem W U a b
    ((oFullU W U N n₁ a).comp (oFullU W U n₁ n b))
    (fun g => anmGen W N 0 n₁ a (anmGen W n₁ 0 n b g))
    (fun g w => by
      show oFullU W U N n₁ a (oFullU W U n₁ n b (mkAnmFull W n 0 g ⊗ₜ[ℂ] w)) = _
      rw [oFullU_tmul, oFullU_tmul])
    (fun g => anmGen_commutator_bdryB W ha b hlt hp g) x
  simpa only [LinearMap.comp_apply] using h

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.anmGen_commutator_bdryA
  #print axioms VOA.anmGen_commutator_bdryB
-/
