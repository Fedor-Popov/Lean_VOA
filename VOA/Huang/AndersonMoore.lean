/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.IModDataReduced

/-!
# `DLMRationalityInput` from the Anderson–Moore theorem

`DLMRationalityInput` (rationality of `c` and of every conformal weight of a strongly rational
VOA) is a theorem *about VOAs*. Its VOA content is exactly Zhu's theorem: the characters
`ch_a = Σ_n dim (M_a)_{h_a+n} q^{h_a + n - c/24}` are honest `q`-series with non-negative integer
coefficients whose span is `S`-invariant. What remains is a statement about such `q`-series alone:

* `AndersonMooreInput` — if finitely many functions `f_i(τ) = Σ_m a_{i,m} e^{2πi(λ_i + m)τ}` on
  `ℍ` (`a_{i,m} ∈ ℕ`, `a_{i,0} ≠ 0`) span an `S`-invariant space (`f_i(-1/τ) = Σ_j S_ij f_j(τ)`;
  `T`-invariance is automatic), then every exponent `λ_i` is rational.

*Source.* G. Anderson and G. Moore, *Rationality in conformal field theory*, Commun. Math. Phys.
117 (1988) 441–450 (the characters satisfy a Fuchsian equation whose solutions have integral
expansions; Katz's theorem on globally nilpotent connections forces quasi-unipotent local
monodromy, i.e. `e^{2πiλ_i}` roots of unity). Used in this form by Dong–Li–Mason, CMP 214 (2000),
Thm 11.3. The Prop says nothing about VOAs.

## Main results

* `dlmRationalityInput_of_andersonMoore` : `ZhuPBWBottomInput → AndersonMooreInput →
  DLMRationalityInput`. Zhu's `S`-law for the canonical family, the integral `q`-expansions
  (`hasSum_character`), the nonvanishing leading coefficient and the vacuum exponent `-c/24` are
  all supplied by the library.
* `dlmRationalityInput_of_andersonMoore_pbw` : the PBW datum from `VOA.pbw`.
-/

open Complex Finset Module

noncomputable section

namespace VOA.Huang.AndersonMoore

open VOA VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.IModDataReduced
  VOA.Huang.ZhuFiniteIrr VOA.Huang.ZhuSemisimple VOA.VHat VOA.VHat.DLM3

universe u

/-- **The Anderson–Moore theorem** (rational exponents of integral `S`-invariant `q`-series).

For finitely many functions `f_i : ℍ → ℂ` given by convergent expansions
`f_i(τ) = Σ_m a_{i,m} e^{2πi(λ_i + m)τ}` with `a_{i,m} ∈ ℕ` and `a_{i,0} ≠ 0`, if the family is
closed under `τ ↦ -1/τ` (`f_i(Sτ) = Σ_j S_ij f_j(τ)`), then every `λ_i` is rational.

*Source.* Anderson–Moore, CMP 117 (1988); DLM, CMP 214 (2000), proof of Thm 11.3. Since
`f_i(τ+1) = e^{2πiλ_i} f_i(τ)`, the span is a finite-dimensional `SL₂(ℤ)`-invariant space of
weight-`0` holomorphic functions of moderate growth, i.e. the hypothesis of Anderson–Moore.

*Not vacuous.* The hypotheses are satisfied by the characters of every strongly rational VOA
(`dlmRationalityInput_of_andersonMoore`); the hypothesis `a_{i,0} ≠ 0` pins `λ_i` (without it,
`f_i ≡ 0` would allow any `λ_i`). -/
def AndersonMooreInput : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℂ) (coeff : Fin n → ℕ → ℕ) (f : Fin n → UpperHalfPlane → ℂ)
    (S : Fin n → Fin n → ℂ),
    (∀ i, coeff i 0 ≠ 0) →
    (∀ i (τ : UpperHalfPlane), HasSum (fun m : ℕ => (coeff i m : ℂ) *
        cexp (2 * Real.pi * I * (lam i + m) * τ)) (f i τ)) →
    (∀ i (τ : UpperHalfPlane), f i (ModularGroup.S • τ) = ∑ j, S i j * f j τ) →
    ∀ i, ∃ q : ℚ, (q : ℂ) = lam i

section Proof

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- The lowest weight space of a module of conformal weight `h` is nonzero-dimensional. -/
theorem finrank_weight_ne_zero {M : Type u} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M)
    {h : ℂ} (hcw : HasConformalWeight N h) : finrank ℂ (N.weight (h + ((0 : ℕ) : ℂ))) ≠ 0 := by
  haveI := N.finrank h
  rw [Nat.cast_zero, add_zero]
  intro h0
  exact hcw.1 (Submodule.finrank_eq_zero.1 h0)

/-- **For a strongly rational VOA, all exponents `h_a - c/24` of the canonical family are
rational, given the Anderson–Moore theorem** (`Pr` the PBW datum). -/
theorem rational_exponents (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hSR : StronglyRational W) (hAM : AndersonMooreInput) (c : Φ W) :
    ∃ q : ℚ, (q : ℂ) = conformalWeightOf (canonicalIrrModule c) - W.centralCharge / 24 := by
  classical
  have hss := isSemisimpleRing_A_of_admissiblyRational Pr hSR.rational
  haveI : Finite (Φ W) := finite_Φ_of_C2Cofinite Pr hSR.c2Cofinite hss
  letI : Fintype (Φ W) := Fintype.ofFinite (Φ W)
  obtain ⟨D, hM, hh, hZ⟩ := zhuModularity_canonical_of_Pr (W := W) Pr hSR.c2Cofinite hss
  let e : Φ W ≃ Fin (Fintype.card (Φ W)) := Fintype.equivFin (Φ W)
  let hw : Φ W → ℂ := fun c => conformalWeightOf (canonicalIrrModule c)
  have hcw : ∀ c, HasConformalWeight (canonicalIrrModule c).isMod (hw c) := fun c =>
    hasConformalWeight_conformalWeightOf _
  refine hAM (Fintype.card (Φ W)) (fun i => hw (e.symm i) - W.centralCharge / 24)
    (fun i m => finrank ℂ ((canonicalIrrModule (e.symm i)).isMod.weight (hw (e.symm i) + m)))
    (fun i τ => traceFun D.Mfam D.h (e.symm i) W.vacuum τ)
    (fun i j => D.repS (e.symm i) (e.symm j))
    (fun i => finrank_weight_ne_zero _ (hcw (e.symm i))) ?_ ?_ (e c) |>.imp
      (fun q hq => by rw [hq, Equiv.symm_apply_apply])
  · intro i τ
    have h := hasSum_character _ (hcw (e.symm i)) hSR.c2Cofinite τ
    have ht : traceFun D.Mfam D.h (e.symm i) W.vacuum τ =
        qEvalAt (torusOnePoint (canonicalIrrModule (e.symm i)).isMod W.vacuum)
          (hw (e.symm i) - W.centralCharge / 24) τ := by
      simp only [traceFun, hh, hw]
      rw [hM]
    beta_reduce
    rw [ht]
    refine h.congr_fun (fun m => ?_)
    congr 3
    ring
  · intro i τ
    have hlaw := hZ ModularGroup.S 0 W.vacuum (vacuum_mem_sqWeightSpace_zero W) (e.symm i) τ
    rw [pow_zero, one_mul, D.rep_S] at hlaw
    beta_reduce
    rw [hlaw]
    exact (Equiv.sum_comp e.symm (fun j => Matrix.of D.repS (e.symm i) j *
      traceFun D.Mfam D.h j W.vacuum τ)).symm

end Proof

/-- **`DLMRationalityInput` from the Anderson–Moore theorem** (and the PBW datum). -/
theorem dlmRationalityInput_of_andersonMoore (hPBW : ZhuPBWBottomInput.{u})
    (hAM : AndersonMooreInput) : DLMRationalityInput.{u} := by
  classical
  intro 𝒱 _ _ W hSR
  obtain ⟨Pr⟩ := hPBW 𝒱 W
  -- the vacuum exponent gives `c`
  let X0 : IrrModule W := adjointIrr W hSR.simple
  obtain ⟨q0, hq0⟩ := rational_exponents Pr hSR hAM X0.toΦ
  rw [conformalWeightOf_vacuumClass W hSR.simple, zero_sub] at hq0
  have hc : ((-24 * q0 : ℚ) : ℂ) = W.centralCharge := by
    push_cast; rw [hq0]; ring
  refine ⟨⟨_, hc⟩, ?_⟩
  intro M _ _ N hN h hcwN
  let X : IrrModule W := ⟨M, N, hN⟩
  obtain ⟨q, hq⟩ := rational_exponents Pr hSR hAM X.toΦ
  obtain ⟨f⟩ : IrrModule.Iso W (canonicalIrrModule X.toΦ) X :=
    Quotient.exact (canonicalIrrModule_toΦ X.toΦ)
  have hh : conformalWeightOf (canonicalIrrModule X.toΦ) = h :=
    hasConformalWeight_unique
      (ModuleEquiv.hasConformalWeight f (hasConformalWeight_conformalWeightOf _)) hcwN
  rw [hh] at hq
  refine ⟨q + (-24 * q0) / 24, ?_⟩
  push_cast
  rw [hq, hq0]
  ring

/-- The same with the PBW datum supplied by the theorem `VOA.pbw`. -/
theorem dlmRationalityInput_of_andersonMoore_pbw (hAM : AndersonMooreInput) :
    DLMRationalityInput.{u} :=
  dlmRationalityInput_of_andersonMoore zhuPBWBottomInput_of_pbw hAM

end VOA.Huang.AndersonMoore
