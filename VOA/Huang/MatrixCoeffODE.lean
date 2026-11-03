/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# The commutative-algebra engine of Huang's differential equations (engine)

Huang, *Differential equations and intertwining operators* (CCM 7 (2005), §1), derives the
differential equations for products of intertwining operators from three algebraic facts, none of
which involves vertex algebras:

1. **(Prop. 1.1 ⟹ Cor. 1.2)** a module `T` with an exhaustive filtration `F`, a submodule `J`, and
   an index `N` such that every filtration step beyond `N` lies in `J` plus the earlier steps,
   satisfies `T = J + F_N`; if `F_N` is finitely generated, so is `T/J`.
   (`le_sup_of_filtration`, `finite_quotient_of_filtration`.)
2. **(Cor. 1.3)** over a Noetherian ring, any sequence `q₀, q₁, …` in a finitely generated module
   satisfies a monic relation `q_m = Σ_{k<m} a_k q_k`.  (`exists_monic_relation`.)
3. The ring `R = ℂ[z₁^{±1}, z₂^{±1}, (z₁ − z₂)^{−1}]` is Noetherian (`HuangRing`, a localisation of
   `ℂ[z₁, z₂]` at `z₁ z₂ (z₁ − z₂)`).

Combining 1–3: with `t_k = w₀ ⊗ L(−1)^k w₁ ⊗ w₂ ⊗ w₃ ∈ T` the classes satisfy a monic
`R`-relation, and *every* `R`-linear `φ : T → 𝔉` killing `J` and intertwining `t_k ↦ ∂^k φ(t₀)`
turns it into the linear ODE `∂^m φ(t₀) = Σ_{k<m} a_k ∂^k φ(t₀)`, with coefficients
**independent of `φ`** (Huang, Remark 1.5): `exists_ode_of_finite_quotient`.

What is *not* here (the VOA-specific part, in `HuangODE*`): the
generators `𝒜, ℬ, 𝒞, 𝒟` of `J`, the verification `φ(J) = 0` from the Jacobi identity, the
`C₁`-cofiniteness reduction that supplies the step hypothesis of (1), and the regularity
refinement (Huang §2).

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.MatrixCoeffODE

open scoped BigOperators

/-! ## 1. Filtrations and finite generation (Huang Prop. 1.1, Cor. 1.2) -/

section Filtration

variable {R T : Type*} [CommRing R] [AddCommGroup T] [Module R T]
variable {ι : Type*} [Preorder ι] [WellFoundedLT ι]

/-- **Huang's Prop. 1.1, abstractly.**  If every filtration step not below `N` lies in `J` plus
the strictly earlier steps, then every step lies in `J + F_N`. -/
theorem le_sup_of_filtration (F : ι → Submodule R T) (hmono : Monotone F) (J : Submodule R T)
    (N : ι) (hstep : ∀ n, ¬ n ≤ N → F n ≤ J ⊔ ⨆ m, ⨆ (_ : m < n), F m) :
    ∀ n, F n ≤ J ⊔ F N := by
  intro n
  induction n using WellFoundedLT.induction with
  | _ n ih =>
    by_cases hn : n ≤ N
    · exact le_sup_of_le_right (hmono hn)
    · refine le_trans (hstep n hn) (sup_le le_sup_left ?_)
      exact iSup₂_le fun m hm => ih m hm

/-- **Huang's Cor. 1.2, abstractly.**  Under the hypotheses of `le_sup_of_filtration`, with an
exhaustive filtration and `F_N` finitely generated, `T/J` is a finitely generated `R`-module. -/
theorem finite_quotient_of_filtration (F : ι → Submodule R T) (hmono : Monotone F)
    (hexh : ∀ t : T, ∃ n, t ∈ F n) (J : Submodule R T) (N : ι) (hFN : (F N).FG)
    (hstep : ∀ n, ¬ n ≤ N → F n ≤ J ⊔ ⨆ m, ⨆ (_ : m < n), F m) :
    Module.Finite R (T ⧸ J) := by
  have hall := le_sup_of_filtration F hmono J N hstep
  have htop : (F N).map J.mkQ = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨t, rfl⟩ := J.mkQ_surjective x
    obtain ⟨n, hn⟩ := hexh t
    obtain ⟨j, hj, f, hf, rfl⟩ := Submodule.mem_sup.mp (hall n hn)
    refine ⟨f, hf, ?_⟩
    simp [(Submodule.Quotient.mk_eq_zero J).mpr hj]
  exact ⟨htop ▸ hFN.map J.mkQ⟩

end Filtration

/-! ## 2. Monic relations over a Noetherian ring (Huang Cor. 1.3) -/

section Relation

variable {R Q : Type*} [CommRing R] [AddCommGroup Q] [Module R Q]

/-- In a Noetherian module, every sequence eventually lies in the span of its predecessors. -/
theorem exists_mem_span_of_isNoetherian [IsNoetherian R Q] (q : ℕ → Q) :
    ∃ m, q m ∈ Submodule.span R (q '' Set.Iio m) := by
  let f : ℕ →o Submodule R Q :=
    ⟨fun n => Submodule.span R (q '' Set.Iio n), fun a b hab =>
      Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hab))⟩
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian (R := R) (M := Q)).mpr inferInstance f
  refine ⟨n, ?_⟩
  have h : q n ∈ f (n + 1) := Submodule.subset_span ⟨n, Nat.lt_succ_self n, rfl⟩
  rwa [← hn (n + 1) (Nat.le_succ n)] at h

/-- **Huang's Cor. 1.3, abstractly.**  Over a Noetherian ring, any sequence in a finitely
generated module satisfies a monic linear relation `q_m = Σ_{k<m} a_k q_k`. -/
theorem exists_monic_relation [IsNoetherianRing R] [Module.Finite R Q] (q : ℕ → Q) :
    ∃ (m : ℕ) (a : ℕ → R), q m = ∑ k ∈ Finset.range m, a k • q k := by
  classical
  obtain ⟨m, hm⟩ := exists_mem_span_of_isNoetherian (R := R) q
  have hrange : q '' Set.Iio m = Set.range (fun k : Fin m => q k) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, hk⟩, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨k, k.isLt, rfl⟩
  rw [hrange, Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  refine ⟨m, fun k => if h : k < m then c ⟨k, h⟩ else 0, ?_⟩
  rw [← hc, Finset.sum_range (fun k => (if h : k < m then c ⟨k, h⟩ else 0) • q k)]
  exact Finset.sum_congr rfl fun k _ => by simp [k.isLt]

end Relation

/-! ## 3. The ring `ℂ[z₁^{±1}, z₂^{±1}, (z₁ − z₂)^{−1}]` -/

/-- The denominator `z₁ z₂ (z₁ − z₂)` in `ℂ[z₁, z₂]` (`z₁ = X 0`, `z₂ = X 1`). -/
noncomputable abbrev huangDen : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.X 0 * MvPolynomial.X 1 * (MvPolynomial.X 0 - MvPolynomial.X 1)

/-- **Huang's ring** `R = ℂ[z₁^{±1}, z₂^{±1}, (z₁ − z₂)^{−1}]`. -/
abbrev HuangRing : Type := Localization.Away huangDen

instance : IsNoetherianRing HuangRing :=
  IsLocalization.isNoetherianRing (Submonoid.powers huangDen) HuangRing inferInstance

/-- `z₁`, `z₂`, `z₁ − z₂` are units of `HuangRing`. -/
theorem isUnit_huangDen : IsUnit (algebraMap (MvPolynomial (Fin 2) ℂ) HuangRing huangDen) :=
  IsLocalization.Away.algebraMap_isUnit huangDen

/-! ## 4. The differential equation (Huang Thm 1.4, algebraic half) -/

section ODE

variable {R T : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup T] [Module R T]

/-- **Huang's ODE, algebraic half.**  If `T/J` is finitely generated over a Noetherian ring,
then for any sequence `t : ℕ → T` there are `m` and `a : ℕ → R` — **depending only on `t` and
`J`** — such that every `R`-linear `φ : T → 𝔉` vanishing on `J` and carrying `t_k` to `D^k φ(t₀)`
satisfies the monic linear equation `D^m φ(t₀) = Σ_{k<m} a_k · D^k φ(t₀)`.  (Huang Remark 1.5: the
coefficients are independent of the intertwining operators.) -/
theorem exists_ode_of_finite_quotient (J : Submodule R T) [Module.Finite R (T ⧸ J)]
    (t : ℕ → T) :
    ∃ (m : ℕ) (a : ℕ → R), ∀ {𝔉 : Type*} [AddCommGroup 𝔉] [Module R 𝔉] (φ : T →ₗ[R] 𝔉)
      (_ : J ≤ LinearMap.ker φ) (D : 𝔉 → 𝔉) (_ : ∀ k, φ (t k) = D^[k] (φ (t 0))),
      D^[m] (φ (t 0)) = ∑ k ∈ Finset.range m, a k • D^[k] (φ (t 0)) := by
  obtain ⟨m, a, h⟩ := exists_monic_relation (R := R) (fun k => J.mkQ (t k))
  refine ⟨m, a, fun {𝔉} _ _ φ hφ D hD => ?_⟩
  have hmem : t m - ∑ k ∈ Finset.range m, a k • t k ∈ J := by
    rw [← Submodule.Quotient.mk_eq_zero]
    change J.mkQ _ = 0
    rw [map_sub, map_sum]
    simp only [map_smul]
    exact sub_eq_zero.mpr h
  have h0 := hφ hmem
  rw [LinearMap.mem_ker, map_sub, map_sum] at h0
  simp only [map_smul] at h0
  rw [← hD m, sub_eq_zero.mp h0]
  exact Finset.sum_congr rfl fun k _ => by rw [hD k]

end ODE

end VOA.Huang.MatrixCoeffODE
