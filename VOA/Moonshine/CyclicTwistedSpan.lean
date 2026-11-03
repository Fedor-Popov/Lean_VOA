/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.TwistedPlusModule
import VOA.Moonshine.CyclicVacuumTrick
import VOA.Moonshine.HeisenbergTwistedModuleSigma

/-!
# Orbit spans in an order-two twisted module  (Moonshine step M8f, twisted half — general)

Let `T` be a `g`-twisted `𝒱`-module of order `2` (`TwistedModule g 2 M`, `g² = 1`), and let
`A ⊆ 𝒱` be a `g`-stable subspace containing `𝟙` and closed under all `n`-th products.  For
`x ∈ M` put

  `Z_A(x) := span {u₍k/2₎ x | u ∈ A, k ∈ ℤ}`     (`orbitSpan`).

* `YM_mem_orbitSpan` — `Z_A(x)` is stable under every mode `u₍k/2₎`, `u ∈ A`.
  *Proof.*  Split `u` into its `g`-eigencomponents.  For `u ∈ 𝒱ʲ` take the twisted Jacobi
  identity with `(u, v, x)`, upper index `k ≥ K_u(x)` (so `u₍(k+2i)/2₎x = 0` for all `i ≥ 0`) and
  `ℓ = (p − k)/2`: it reads
  `Σ_{i ≥ 0} (−1)ⁱ C(ℓ,i) u₍(p−2i)/2₎ v₍(q+2i)/2₎ x = Σ_i C(k/2,i) (u₍ℓ₊ᵢ₎v)₍…₎ x ∈ Z_A(x)`,
  and the `i ≥ 1` terms are handled by descending induction on `q` (`v₍q/2₎ x = 0` for large
  `q`).  This is the twisted analogue of "the span of `u₍ₙ₎x` is a submodule"; it uses only the
  module Jacobi identity — no twisted × twisted operator.
* `self_mem_orbitSpan`, `orbitSpan_le_of_mem` — `x ∈ Z_A(x)`, and `y ∈ Z_A(x) ⇒ Z_A(y) ≤ Z_A(x)`.
* `mem_span_plus_of_mem_orbitSpan` — **the `+`-projection.**  For a `ThetaLift` `θ_M` of `g`,
  `x₀ ∈ M⁺` and `y ∈ M⁺ ∩ Z_A(x₀)`, `y` lies in the span of the `M⁺`-modes
  `mode (plusModule θ).YM u n x₀` with `u ∈ 𝒱^g ∩ A`.  (Apply `P = ½(1 + θ_M)`:
  `P(u₍k/2₎x₀) = (½(u + gu))₍k/2₎ x₀`, whose odd modes vanish.)

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
Unconditional (the hypotheses on `A` and `g` are displayed).
-/

set_option linter.style.longLine false

namespace VOA.TwistedCyclic

open Module (End)
open TwistedPlus

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {g : Aut W} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **The orbit span** `Z_A(x) = span {u₍k/2₎ x | u ∈ A, k ∈ ℤ}`. -/
def orbitSpan (T : TwistedModule g 2 M) (A : Submodule ℂ 𝒱) (x : M) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ u ∈ A, ∃ k : ℤ, y = T.YM u k x}

theorem YM_mem_orbitSpan_of_mem {T : TwistedModule g 2 M} {A : Submodule ℂ 𝒱} {u : 𝒱}
    (hu : u ∈ A) (k : ℤ) (x : M) : T.YM u k x ∈ orbitSpan T A x :=
  Submodule.subset_span ⟨u, hu, k, rfl⟩

theorem mem_twistedEigenspace_one {u : 𝒱} (hu : g u = -u) : u ∈ g.twistedEigenspace 2 1 := by
  rw [Aut.twistedEigenspace, Module.End.mem_eigenspace_iff, HeisenbergN.exp_twisted_two]
  simpa using hu

/-- One step: for `u ∈ 𝒱ʲ ∩ A`, `v ∈ A`, every `u₍p/2₎ v₍q/2₎ x` lies in `Z_A(x)`. -/
theorem YM_YM_mem_orbitSpan (T : TwistedModule g 2 M) (A : Submodule ℂ 𝒱)
    (hA : ∀ u ∈ A, ∀ (n : ℤ), ∀ v ∈ A, W.smul u n v ∈ A)
    {j : ℕ} {u : 𝒱} (huj : u ∈ g.twistedEigenspace 2 j) (hu : u ∈ A) {v : 𝒱} (hv : v ∈ A)
    (x : M) (p q : ℤ) : T.YM u p (T.YM v q x) ∈ orbitSpan T A x := by
  set Z := orbitSpan T A x
  obtain ⟨Ku, hKu⟩ := T.truncation u x
  obtain ⟨Kv, hKv⟩ := T.truncation v x
  suffices H : ∀ n : ℕ, ∀ q : ℤ, Kv - q ≤ n → ∀ p : ℤ, T.YM u p (T.YM v q x) ∈ Z from
    H (Kv - q).toNat q (by omega) p
  intro n
  induction n with
  | zero =>
      intro q hq p
      rw [hKv q (by omega), map_zero]
      exact Z.zero_mem
  | succ n ih =>
      intro q hq p
      by_cases hpj : (p + j) % ((2 : ℕ) : ℤ) ≠ 0
      · rw [T.support j u huj p hpj, LinearMap.zero_apply]
        exact Z.zero_mem
      push Not at hpj
      set c : ℕ := (Ku - p).toNat with hc
      set ℓ : ℤ := -(c : ℤ) with hℓ
      set k : ℤ := p + 2 * c with hk
      have hkK : Ku ≤ k := by omega
      have hkj : (k + j) % ((2 : ℕ) : ℤ) = 0 := by
        push_cast at hpj ⊢; omega
      have hJ := T.jacobi j u huj v x ℓ k q hkj
      set f : ℤ → M := fun i => (negOnePow i * cbz ℓ i) •
        (T.YM u (ℓ * ((2 : ℕ) : ℤ) + k - i * ((2 : ℕ) : ℤ)) (T.YM v (q + i * ((2 : ℕ) : ℤ)) x)
          - negOnePow ℓ • T.YM v (ℓ * ((2 : ℕ) : ℤ) + q - i * ((2 : ℕ) : ℤ))
              (T.YM u (k + i * ((2 : ℕ) : ℤ)) x)) with hf
      have hf' : ∀ i : ℤ, 0 ≤ i → f i = (negOnePow i * cbz ℓ i) •
          T.YM u (p - 2 * i) (T.YM v (q + 2 * i) x) := by
        intro i hi
        rw [hf]
        simp only
        rw [hKu (k + i * ((2 : ℕ) : ℤ)) (by push_cast; omega), map_zero, smul_zero, sub_zero]
        congr 3
        · rw [hk, hℓ]; push_cast; ring_nf
        · push_cast; ring_nf
      have hRHS : (∑ᶠ i : ℤ, f i) ∈ Z := by
        rw [hf, hJ]
        refine finsum_mem_submodule_of_forall Z _ fun i => Submodule.smul_mem _ _ ?_
        exact YM_mem_orbitSpan_of_mem (hA u hu _ v hv) _ x
      set B : ℤ := max (Kv - q) 0 with hB
      have hsupp : Function.support f ⊆ ↑(Finset.Icc (0 : ℤ) B) := by
        intro i hi
        rw [Function.mem_support] at hi
        simp only [Finset.coe_Icc, Set.mem_Icc]
        by_contra hcon
        apply hi
        rcases lt_or_ge i 0 with hneg | hnn
        · rw [hf]; simp only; rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
        · rw [hf' i hnn, hKv (q + 2 * i) (by omega), map_zero, smul_zero]
      rw [finsum_eq_sum_of_support_subset f hsupp,
        ← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl, le_max_right _ _⟩)] at hRHS
      have hrest : (∑ i ∈ (Finset.Icc (0 : ℤ) B).erase 0, f i) ∈ Z := by
        refine Submodule.sum_mem _ fun i hi => ?_
        rw [Finset.mem_erase, Finset.mem_Icc] at hi
        rw [hf' i hi.2.1]
        exact Submodule.smul_mem _ _ (ih (q + 2 * i) (by omega) _)
      have h0 := (Submodule.add_mem_iff_left Z hrest).mp hRHS
      rwa [hf' 0 le_rfl, show negOnePow 0 * cbz ℓ 0 = 1 by simp [negOnePow], one_smul,
        mul_zero, sub_zero, add_zero] at h0

variable (T : TwistedModule g 2 M) (A : Submodule ℂ 𝒱)
  (hA : ∀ u ∈ A, ∀ (n : ℤ), ∀ v ∈ A, W.smul u n v ∈ A) (hg : ∀ u ∈ A, g u ∈ A)
  (hgg : ∀ u, g (g u) = u)

include hA hg hgg in
/-- **`Z_A(x)` is stable under the modes of `A`.** -/
theorem YM_mem_orbitSpan {u : 𝒱} (hu : u ∈ A) (p : ℤ) {x y : M} (hy : y ∈ orbitSpan T A x) :
    T.YM u p y ∈ orbitSpan T A x := by
  set u₀ : 𝒱 := (1 / 2 : ℂ) • (u + g u)
  set u₁ : 𝒱 := (1 / 2 : ℂ) • (u - g u)
  have hsplit : u = u₀ + u₁ := by
    simp only [u₀, u₁, ← smul_add]
    rw [show u + g u + (u - g u) = (2 : ℂ) • u by rw [two_smul]; abel, smul_smul]
    norm_num
  have hgu₀ : g u₀ = u₀ := by
    simp only [u₀, map_smul, map_add]
    simp only [hgg, add_comm]
  have hgu₁ : g u₁ = -u₁ := by
    simp only [u₁, map_smul, map_sub]
    simp only [hgg, ← smul_neg, neg_sub]
  have hu₀ : u₀ ∈ A := A.smul_mem _ (A.add_mem hu (hg u hu))
  have hu₁ : u₁ ∈ A := A.smul_mem _ (A.sub_mem hu (hg u hu))
  rw [hsplit, map_add, Pi.add_apply, LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨v, hv, q, rfl⟩ := hz
        exact YM_YM_mem_orbitSpan T A hA (mem_twistedEigenspace_zero hgu₀) hu₀ hv x p q
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  · induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨v, hv, q, rfl⟩ := hz
        exact YM_YM_mem_orbitSpan T A hA (mem_twistedEigenspace_one hgu₁) hu₁ hv x p q
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

theorem self_mem_orbitSpan (hvac : W.vacuum ∈ A) (x : M) : x ∈ orbitSpan T A x := by
  have h := YM_mem_orbitSpan_of_mem (T := T) hvac (-2) x
  rwa [T.vacuum_YM, if_pos (by norm_num), Module.End.one_apply] at h

include hA hg hgg in
/-- `y ∈ Z_A(x) ⇒ Z_A(y) ≤ Z_A(x)`. -/
theorem orbitSpan_le_of_mem {x y : M} (hy : y ∈ orbitSpan T A x) :
    orbitSpan T A y ≤ orbitSpan T A x := by
  rw [orbitSpan, Submodule.span_le]
  rintro z ⟨u, hu, k, rfl⟩
  exact YM_mem_orbitSpan T A hA hg hgg hu k hy

/-! ## The `+`-projection -/

include hg hgg in
/-- **The `+`-projection.**  If `x₀ ∈ M⁺` and `y ∈ M⁺ ∩ Z_A(x₀)`, then `y` is a combination of
the `M⁺`-modes `u₍ₙ₎ x₀` with `u ∈ 𝒱^g ∩ A`. -/
theorem mem_span_plus_of_mem_orbitSpan (θ : ThetaLift T) (x₀ y : plusSub θ)
    (hy : (y : M) ∈ orbitSpan T A x₀) :
    y ∈ Submodule.span ℂ {z | ∃ u : (orbifold (Subgroup.zpowers g)).carrier, (u : 𝒱) ∈ A ∧
      ∃ n : ℤ, z = mode ((plusModule θ).YM u) n x₀} := by
  set S := Submodule.span ℂ {z | ∃ u : (orbifold (Subgroup.zpowers g)).carrier, (u : 𝒱) ∈ A ∧
      ∃ n : ℤ, z = mode ((plusModule θ).YM u) n x₀}
  set P : End ℂ M := (1 / 2 : ℂ) • (LinearMap.id + θ.op)
  have hx₀ : θ.op x₀ = x₀ := (mem_plusSub θ).mp x₀.2
  have hP : ∀ z ∈ orbitSpan T A x₀, P z ∈ S.map (plusSub θ).subtype := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨u, hu, k, rfl⟩ := hz
        set w : 𝒱 := (1 / 2 : ℂ) • (u + g u)
        have hgw : g w = w := by
          simp only [w, map_smul, map_add]
          simp only [hgg, add_comm]
        have hwA : w ∈ A := A.smul_mem _ (A.add_mem hu (hg u hu))
        have hwfix : w ∈ (orbifold (Subgroup.zpowers g)).carrier :=
          (VOA.mem_orbifold_zpowers_iff g w).mpr hgw
        have hPz : P (T.YM u k x₀) = T.YM w k x₀ := by
          have hc := θ.conj u k
          have hθ : θ.op (T.YM u k x₀) = T.YM (g u) k x₀ := by
            rw [hc]; simp only [LinearMap.comp_apply, hx₀]
          simp only [P, w, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, hθ,
            map_smul, map_add, Pi.smul_apply, Pi.add_apply]
        rw [hPz]
        obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
        · refine ⟨mode ((plusModule θ).YM ⟨w, hwfix⟩) n x₀,
            Submodule.subset_span ⟨⟨w, hwfix⟩, hwA, n, rfl⟩, ?_⟩
          rw [Submodule.subtype_apply, TwistedPlus.mode_plusModule]
        · rw [YM_odd_eq_zero hgw n, LinearMap.zero_apply]
          exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  have hPy : P y = y := by
    have : θ.op y = y := (mem_plusSub θ).mp y.2
    simp only [P, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, this]
    rw [← two_smul ℂ (y : M), smul_smul]; norm_num
  obtain ⟨y', hy', hyy⟩ := hP _ hy
  rw [hPy] at hyy
  have : y' = y := Subtype.ext hyy
  rwa [← this]

end VOA.TwistedCyclic
