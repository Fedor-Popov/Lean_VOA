/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkLevelBoxHeadline
import VOA.Classification.COne.SerreStarkQExp

/-!
# Serre–Stark S7: bounded denominators at `p ∣ N` come for free

The S3/S4 arithmetic (`eigenvalue_of_fg`, `eigen_pow_of_fg`, `seq_mul_sq_aux`,
`jordan_coeff_zero`) only ever uses integrality along `p`-towers at primes `p ∤ N`, and the
integrality argument works verbatim over the Noetherian ring `ℤ[1/M] ⊂ ℂ` (`zInv M`), over which
`1/p` is still not integral when `p ∤ M` (`not_isIntegral_inv_prime_zInv`). So the bounded
coefficient residual can be weakened to boundedness *away from a modulus prime to the tower prime*:

* `SerreStarkBoundedCoeffAway24`: for every `g ∈ M_{1/2}(N, χ)` (`24 ∣ N`) and every prime `p ∤ N`
  there are `M` with `p ∤ M` and a finitely generated `L ⊂ ℂ` with every coefficient in
  `awaySat M L = {z | ∃ e, M^e z ∈ L}`.

Main results:

* `iSerreStark24_of_away : SerreStarkBoundedCoeffAway24 → ISerreStark24` (the S3/S4 chain over
  `ℤ[1/M]`, with the proved level box `serreStarkLevelBox24`);
* `boundedCoeff24_of_iSerreStark24 : ISerreStark24 → SerreStarkBoundedCoeff24` (theta series
  `θ_{n₀,r,t}` have natural-number coefficients);
* `boundedCoeff24_of_away : SerreStarkBoundedCoeffAway24 → SerreStarkBoundedCoeff24`;
* `QExpPrinciple24Away k` (the integral-weight principle away from `p`, for every `p ∤ N`; it is
  implied by Katz's `q`-expansion principle over `ℤ[1/N]`) and
  `boundedCoeff24_of_qExpPrinciple24Away (j) : QExpPrinciple24Away (1 + j) →
  SerreStarkBoundedCoeff24`.

So the arithmetic at the primes dividing the level (the part of Shimura 3.52 / Katz–Conrad that
needs Eichler–Shimura or the moduli of `μ_N`-structures) is not an input.
-/

open Complex
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-! ## Integrality over `ℤ[1/M]` -/

/-- `x^k y ∈ L` for an `R`-f.g. `L` gives `x` integral over `R`. -/
theorem isIntegral_of_pow_mul_mem_R {R : Subalgebra ℤ ℂ} [IsNoetherianRing R]
    {L : Submodule R ℂ} (hL : L.FG) {x y : ℂ} (hy : y ≠ 0)
    (h : ∀ k : ℕ, x ^ k * y ∈ L) : IsIntegral R x := by
  set S := Submodule.span R (Set.range fun k : ℕ => x ^ k * y) with hSdef
  have hS : S ≤ L := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact h k)
  have hSfg : S.FG := Submodule.FG.of_le hL hS
  refine isIntegral_of_smul_mem_submodule (A := ℂ) (M := ℂ) S ?_ hSfg x ?_
  · intro hbot
    have : x ^ 0 * y ∈ S := Submodule.subset_span ⟨0, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    exact hy (by simpa using this)
  · intro n hn
    refine Submodule.span_induction (p := fun n _ => x • n ∈ S) ?_ ?_ ?_ ?_ hn
    · rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨k + 1, by
        change x ^ (k + 1) * y = x * (x ^ k * y); ring⟩
    · simp
    · intro a b _ _ ha hb
      rw [smul_add]; exact S.add_mem ha hb
    · intro r a _ ha
      rw [smul_comm]; exact S.smul_mem r ha

/-- The ring `ℤ[1/M] ⊂ ℂ`. -/
abbrev zInv (M : ℕ) : Subalgebra ℤ ℂ := Algebra.adjoin ℤ {((M : ℂ))⁻¹}

instance (M : ℕ) : IsNoetherianRing (zInv M) :=
  isNoetherianRing_of_fg (by
    simpa using Subalgebra.fg_adjoin_finset (R := ℤ) ({((M : ℂ))⁻¹} : Finset ℂ))

theorem mem_zInv {M : ℕ} (hM : M ≠ 0) {z : ℂ} (hz : z ∈ zInv M) :
    ∃ (a : ℤ) (e : ℕ), z = a / (M : ℂ) ^ e := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨1, 1, by rw [hx]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, e, rfl⟩ := hx
    obtain ⟨b, f, rfl⟩ := hy
    have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM
    refine ⟨a * M ^ f + b * M ^ e, e + f, ?_⟩
    push_cast
    field_simp
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨a, e, rfl⟩ := hx
    obtain ⟨b, f, rfl⟩ := hy
    exact ⟨a * b, e + f, by push_cast; rw [pow_add]; ring⟩

/-- `1/p` is not integral over `ℤ[1/M]` when `p ∤ M`. -/
theorem not_isIntegral_inv_prime_zInv {p M : ℕ} (hp : p.Prime) (hM : M ≠ 0) (hpM : ¬ p ∣ M) :
    ¬ IsIntegral (zInv M) ((p : ℂ)⁻¹) := by
  rintro ⟨P, hPm, hP⟩
  have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  set n := P.natDegree
  -- a common denominator `M^E` for the coefficients
  have hcom : ∀ s : Finset ℕ, ∃ E : ℕ, ∀ i ∈ s, ∃ b : ℤ,
      (M : ℂ) ^ E * ((P.coeff i : zInv M) : ℂ) = b := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert j s hj ih =>
      obtain ⟨E, hE⟩ := ih
      obtain ⟨a, e, hae⟩ := mem_zInv hM (P.coeff j).2
      refine ⟨E + e, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · refine ⟨a * (M : ℤ) ^ E, ?_⟩
        rw [hae]; push_cast; field_simp; ring
      · obtain ⟨b, hb⟩ := hE i hi
        refine ⟨b * (M : ℤ) ^ e, ?_⟩
        push_cast; rw [← hb]; ring
  obtain ⟨E, hE⟩ := hcom (Finset.range n)
  choose! b hb using hE
  rw [Polynomial.eval₂_eq_sum_range] at hP
  rw [Finset.sum_range_succ, hPm.coeff_natDegree] at hP
  have key : ((M : ℤ) ^ E : ℂ) =
      ((p : ℤ) * -(∑ i ∈ Finset.range n, b i * (p : ℤ) ^ (n - 1 - i)) : ℤ) := by
    push_cast
    have h2 : (M : ℂ) ^ E * (p : ℂ) ^ n * (∑ i ∈ Finset.range n,
        algebraMap (zInv M) ℂ (P.coeff i) * (p : ℂ)⁻¹ ^ i +
        algebraMap (zInv M) ℂ 1 * (p : ℂ)⁻¹ ^ n) = 0 := by rw [hP, mul_zero]
    rw [map_one, one_mul, mul_add, Finset.mul_sum] at h2
    have h3 : ∀ i ∈ Finset.range n, (M : ℂ) ^ E * (p : ℂ) ^ n *
        (algebraMap (zInv M) ℂ (P.coeff i) * (p : ℂ)⁻¹ ^ i) =
        (p : ℂ) * ((b i : ℂ) * (p : ℂ) ^ (n - 1 - i)) := by
      intro i hi
      have hin : i < n := Finset.mem_range.1 hi
      have e1 : (p : ℂ) ^ n = (p : ℂ) * (p : ℂ) ^ (n - 1 - i) * (p : ℂ) ^ i := by
        rw [mul_assoc, ← pow_add, ← pow_succ']; congr 1; omega
      have ea : algebraMap (zInv M) ℂ (P.coeff i) = ((P.coeff i : zInv M) : ℂ) := rfl
      rw [e1, ← hb i hi, ea, inv_pow]
      field_simp
    rw [Finset.sum_congr rfl h3, ← Finset.mul_sum] at h2
    have e4 : (M : ℂ) ^ E * (p : ℂ) ^ n * (p : ℂ)⁻¹ ^ n = (M : ℂ) ^ E := by
      rw [inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp'), mul_one]
    rw [e4] at h2
    linear_combination h2
  have key' : (M : ℤ) ^ E = (p : ℤ) * -(∑ i ∈ Finset.range n, b i * (p : ℤ) ^ (n - 1 - i)) := by
    exact_mod_cast key
  have hdvd : (p : ℤ) ∣ (M : ℤ) ^ E := ⟨_, key'⟩
  have : (p : ℤ) ∣ (M : ℤ) := Int.Prime.dvd_pow' hp hdvd
  exact hpM (by exact_mod_cast this)

/-- A root of unity is integral over any subring. -/
theorem isIntegral_of_pow_eq_one_R {R : Subalgebra ℤ ℂ} {z : ℂ} {n : ℕ} (hn : 0 < n)
    (h : z ^ n = 1) : IsIntegral R z :=
  IsIntegral.of_pow hn (by rw [h]; exact isIntegral_one)

/-! ## Saturation away from `M` and the weakened residual -/

/-- `{z | ∃ e, M^e z ∈ L}`: the `ℤ[1/M]`-saturation of `L`, as an additive subgroup. -/
def awaySat (M : ℕ) (L : Submodule ℤ ℂ) : Submodule ℤ ℂ where
  carrier := {z | ∃ e : ℕ, (M : ℂ) ^ e * z ∈ L}
  add_mem' := by
    rintro a b ⟨e, he⟩ ⟨f, hf⟩
    refine ⟨e + f, ?_⟩
    have h1 := L.smul_mem ((M : ℤ) ^ f) he
    have h2 := L.smul_mem ((M : ℤ) ^ e) hf
    rw [zsmul_eq_mul] at h1 h2
    push_cast at h1 h2
    have : (M : ℂ) ^ (e + f) * (a + b) =
        (M : ℂ) ^ f * ((M : ℂ) ^ e * a) + (M : ℂ) ^ e * ((M : ℂ) ^ f * b) := by ring
    rw [this]
    exact L.add_mem h1 h2
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c z ⟨e, he⟩
    exact ⟨e, by rw [mul_smul_comm]; exact L.smul_mem c he⟩

theorem mem_awaySat_of_mem {M : ℕ} {L : Submodule ℤ ℂ} {z : ℂ} (hz : z ∈ L) : z ∈ awaySat M L :=
  ⟨0, by simpa using hz⟩

/-- **Residual (bounded coefficients away from the tower prime).** For `24 ∣ N`, every
`g ∈ M_{1/2}(N, χ)` and every prime `p ∤ N`, there are `M` with `p ∤ M` and a finitely generated
`L ⊂ ℂ` such that `M^e a(n) ∈ L` for some `e = e(n)`, for every `n`.

TRUE: it is implied by `SerreStarkBoundedCoeff24` (`boundedCoeffAway_of_boundedCoeff`, `M = 1`),
and conversely implies it (`boundedCoeff24_of_away`). It follows from Katz's `q`-expansion
principle over `ℤ[1/N]` (take `M = N`) via `QExpPrinciple24Away`. -/
def SerreStarkBoundedCoeffAway24 : Prop :=
  ∀ (N : ℕ) (_hN : 0 < N) (_h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (g : mSpace N χ) (p : ℕ),
    p.Prime → p.Coprime N →
      ∃ M : ℕ, ¬ p ∣ M ∧ ∃ L : Submodule ℤ ℂ, L.FG ∧ ∀ n, mCoeff g n ∈ awaySat M L

theorem boundedCoeffAway_of_boundedCoeff (hB : SerreStarkBoundedCoeff24) :
    SerreStarkBoundedCoeffAway24 := by
  intro N hN h24 χ g p hp _
  obtain ⟨L, hL, haL⟩ := hB N hN h24 χ g
  exact ⟨1, hp.not_dvd_one, L, hL, fun n => mem_awaySat_of_mem (haL n)⟩

/-- Transfer of an away-saturated f.g. group to a f.g. `ℤ[1/M']`-module, `M ∣ M'`. -/
theorem span_zInv_of_awaySat {M M' : ℕ} (hMM : M ∣ M') (hM' : M' ≠ 0) {L : Submodule ℤ ℂ}
    (hL : L.FG) :
    (Submodule.span (zInv M') (L : Set ℂ)).FG ∧
      ∀ z ∈ awaySat M L, z ∈ Submodule.span (zInv M') (L : Set ℂ) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨s, rfl⟩ := hL
    exact ⟨s, by rw [Submodule.span_span_of_tower]⟩
  · rintro z ⟨e, he⟩
    obtain ⟨c, hc⟩ := hMM
    have hM0 : (M : ℂ) ≠ 0 := by
      rintro h; apply hM'; rw [hc, show M = 0 by exact_mod_cast h, zero_mul]
    have hinv : (M : ℂ)⁻¹ ∈ zInv M' := by
      have h1 : (M : ℂ)⁻¹ = (c : ℂ) * ((M' : ℂ))⁻¹ := by
        have hc0 : (c : ℂ) ≠ 0 := by
          rintro h; apply hM'; rw [hc, show c = 0 by exact_mod_cast h, mul_zero]
        rw [hc]; push_cast; field_simp
      rw [h1]
      exact Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ c)
        (Algebra.subset_adjoin (Set.mem_singleton _))
    have hu : ((M : ℂ)⁻¹) ^ e ∈ zInv M' := Subalgebra.pow_mem _ hinv e
    have hz : z = (⟨_, hu⟩ : zInv M') • ((M : ℂ) ^ e * z) := by
      change z = ((M : ℂ)⁻¹) ^ e * ((M : ℂ) ^ e * z)
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hM0, one_pow, one_mul]
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span he)

theorem awayData (hB : SerreStarkBoundedCoeffAway24) {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N)
    (χ : DirichletCharacter ℂ N) (g : mSpace N χ) {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) :
    ∃ M : ℕ, ¬ p ∣ M ∧ M ≠ 0 ∧ ∃ L : Submodule (zInv M) ℂ, L.FG ∧ ∀ n, mCoeff g n ∈ L := by
  obtain ⟨M, hpM, L, hL, haL⟩ := hB N hN h24 χ g p hp hpN
  have hM0 : M ≠ 0 := by rintro rfl; exact hpM (dvd_zero p)
  obtain ⟨h1, h2⟩ := span_zInv_of_awaySat dvd_rfl hM0 hL
  exact ⟨M, hpM, hM0, _, h1, fun n => h2 _ (haL n)⟩

theorem awayData2 (hB : SerreStarkBoundedCoeffAway24) {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N)
    (χ : DirichletCharacter ℂ N) (g h : mSpace N χ) {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) :
    ∃ M : ℕ, ¬ p ∣ M ∧ M ≠ 0 ∧ ∃ La : Submodule (zInv M) ℂ, La.FG ∧ (∀ n, mCoeff g n ∈ La) ∧
      ∃ Lb : Submodule (zInv M) ℂ, Lb.FG ∧ ∀ n, mCoeff h n ∈ Lb := by
  obtain ⟨Ma, hpa, La, hLa, haL⟩ := hB N hN h24 χ g p hp hpN
  obtain ⟨Mb, hpb, Lb, hLb, hbL⟩ := hB N hN h24 χ h p hp hpN
  have hM0 : Ma * Mb ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · rintro rfl; exact hpa (dvd_zero p)
    · rintro rfl; exact hpb (dvd_zero p)
  have hpM : ¬ p ∣ Ma * Mb := fun hd => (hp.dvd_mul.1 hd).elim hpa hpb
  obtain ⟨a1, a2⟩ := span_zInv_of_awaySat (dvd_mul_right Ma Mb) hM0 hLa
  obtain ⟨b1, b2⟩ := span_zInv_of_awaySat (dvd_mul_left Mb Ma) hM0 hLb
  exact ⟨Ma * Mb, hpM, hM0, _, a1, fun n => a2 _ (haL n), _, b1, fun n => b2 _ (hbL n)⟩

/-! ## The S3/S4 cores over a Noetherian subring `R ⊂ ℂ` -/

section EigenvalueR

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (p : ℕ) [hpf : Fact p.Prime]
variable {R : Subalgebra ℤ ℂ} [IsNoetherianRing R]

/-- **The algebraic core of the eigenvalue lemma, over `R`** (`R ⊂ ℂ` Noetherian, `1/p` not
integral over `R`). Let `a` be a sequence in a finitely generated `R`-submodule of `ℂ`
with `heckeCoeff χ p a = c a`, `a(m) ≠ 0`, `p² ∤ m`, `p ∤ N`. Then `p ∤ m` and
`c = χ(p)(m/p)(1 + 1/p)`. -/
theorem eigenvalue_of_fgR (hpN : Nat.Coprime p N) (hpR : ¬ IsIntegral R ((p : ℂ)⁻¹)) {a : ℕ → ℂ}
    {L : Submodule R ℂ} (hL : L.FG)
    (haL : ∀ n, a n ∈ L) {c : ℂ} (hc : ∀ n, heckeCoeff χ p a n = c * a n) {m : ℕ}
    (ham : a m ≠ 0) (hm : ¬ p ^ 2 ∣ m) :
    ¬ p ∣ m ∧
      c = χ (p : ZMod N) * (legendreSym p (m : ℤ) : ℂ) * (1 + 1 / (p : ℂ)) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpf.out.ne_zero
  have hχ : χ (p : ZMod N) ≠ 0 :=
    chi_ne_zero_of_isUnit χ ((ZMod.isUnit_iff_coprime p N).2 hpN)
  obtain ⟨e, he, hχe⟩ := exists_pow_chi_eq_one χ ((ZMod.isUnit_iff_coprime p N).2 hpN)
  set x := χ (p : ZMod N) with hx
  set ε := x * (legendreSym p (m : ℤ) : ℂ) with hε
  set A : ℕ → ℂ := fun k => a (p ^ (2 * k) * m) with hA
  have hA0 : A 0 = a m := by simp [hA]
  -- the recurrences
  have r0 : A 1 + ε / p * A 0 = c * A 0 := by
    have := hc m
    rw [heckeCoeff_base χ p a hm] at this
    change a (p ^ (2 * 1) * m) + ε / p * a (p ^ (2 * 0) * m) = c * a (p ^ (2 * 0) * m)
    simp only [Nat.mul_zero, pow_zero, one_mul, Nat.mul_one]
    rw [hε]; linear_combination this
  have rk : ∀ k, A (k + 2) + x ^ 2 / p * A k = c * A (k + 1) := by
    intro k
    have := hc (p ^ (2 * (k + 1)) * m)
    rw [heckeCoeff_step χ p a m k] at this
    simpa [hA] using this
  -- the roots `β, γ` of `X² − cX + x²/p`
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, β * β - c * β + x ^ 2 / p = 0 := by
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (discrim 1 (-c) (x ^ 2 / p))
    obtain ⟨β, hβ⟩ := exists_quadratic_eq_zero (one_ne_zero) ⟨s, hs⟩
    exact ⟨β, by linear_combination hβ⟩
  set γ := c - β with hγ
  have hβγ : β * γ = x ^ 2 / p := by rw [hγ]; linear_combination -hβ
  -- the module generated by `L`, `β L`, `γ L`
  have hmem : ∀ (δ : ℂ) (k : ℕ), A (k + 1) - δ * A k ∈ L ⊔ L.map (LinearMap.mulLeft R δ) :=
    fun δ k => Submodule.sub_mem _ (Submodule.mem_sup_left (haL _))
      (Submodule.mem_sup_right (Submodule.mem_map_of_mem (haL _)))
  have hfg : ∀ δ : ℂ, (L ⊔ L.map (LinearMap.mulLeft R δ)).FG := fun δ => hL.sup (hL.map _)
  -- `Q_k = A_{k+1} − δ A_k` satisfies `Q_{k+1} = δ' Q_k` for `{δ, δ'} = {β, γ}`
  have hQ : ∀ δ δ' : ℂ, δ + δ' = c → δ * δ' = x ^ 2 / p → ∀ k,
      A (k + 1) - δ * A k = δ' ^ k * (A 1 - δ * A 0) := by
    intro δ δ' hs hpr k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, mul_comm (δ' ^ k) δ', mul_assoc, ← ih]
      have := rk k
      rw [← hs, ← hpr] at this
      linear_combination this
  have hint : ∀ δ δ' : ℂ, δ + δ' = c → δ * δ' = x ^ 2 / p → A 1 - δ * A 0 ≠ 0 →
      IsIntegral R δ' := fun δ δ' hs hpr hne =>
    isIntegral_of_pow_mul_mem_R (hfg δ) hne fun k => by rw [← hQ δ δ' hs hpr k]; exact hmem δ k
  -- one of the two `Q_0` vanishes, else `x²/p` would be integral
  obtain ⟨β', γ', hs', hpr', hQ0⟩ : ∃ β' γ' : ℂ, β' + γ' = c ∧ β' * γ' = x ^ 2 / p ∧
      A 1 = β' * A 0 := by
    by_cases h1 : A 1 - β * A 0 = 0
    · exact ⟨β, γ, by rw [hγ]; ring, hβγ, by linear_combination h1⟩
    by_cases h2 : A 1 - γ * A 0 = 0
    · exact ⟨γ, β, by rw [hγ]; ring, by rw [mul_comm]; exact hβγ, by linear_combination h2⟩
    exfalso
    have iγ := hint β γ (by rw [hγ]; ring) hβγ h1
    have iβ := hint γ β (by rw [hγ]; ring) (by rw [mul_comm]; exact hβγ) h2
    have ixinv : IsIntegral R (x ^ (e - 1)) := (isIntegral_of_pow_eq_one_R he hχe).pow _
    have key : (p : ℂ)⁻¹ = β * γ * (x ^ (e - 1)) ^ 2 := by
      rw [hβγ, ← pow_mul]
      have : x ^ 2 * x ^ ((e - 1) * 2) = 1 := by
        rw [← pow_add, show 2 + (e - 1) * 2 = 2 * e by omega, pow_mul', hχe, one_pow]
      field_simp
      linear_combination (-1) * this
    exact hpR (key ▸ ((iβ.mul iγ).mul (ixinv.pow 2)))
  -- read off `β' = c − ε/p`, `γ' = ε/p`
  have hA0' : A 0 ≠ 0 := by rw [hA0]; exact ham
  have hβ' : β' = c - ε / p := by
    apply mul_right_cancel₀ hA0'
    linear_combination -hQ0 + r0
  have hγ' : γ' = ε / p := by linear_combination hs' - hβ'
  have hx2 : x ^ 2 / p ≠ 0 := div_ne_zero (pow_ne_zero 2 hχ) hp0
  have hγ0 : γ' ≠ 0 := fun h0 => hx2 (by rw [← hpr', h0, mul_zero])
  have hleg0 : legendreSym p (m : ℤ) ≠ 0 := by
    intro h0; apply hγ0; rw [hγ', hε, h0]; simp
  have hpm : ¬ p ∣ m := by
    intro hd; apply hleg0
    rw [legendreSym.eq_zero_iff]
    exact_mod_cast (ZMod.natCast_eq_zero_iff m p).2 hd
  refine ⟨hpm, ?_⟩
  have hl2 : (legendreSym p (m : ℤ) : ℂ) ^ 2 = 1 := by
    have := legendreSym.sq_one p (a := (m : ℤ)) (by
      intro h0; exact hleg0 ((legendreSym.eq_zero_iff p _).2 h0))
    exact_mod_cast this
  -- `β' γ' = x²/p` with `γ' = ε/p` forces `β' = ε`
  have hβε : β' = ε := by
    have h1 : β' * (ε / p) = x ^ 2 / p := by rw [← hγ', hpr']
    have hε0 : ε ≠ 0 := by
      intro h0; apply hγ0; rw [hγ', h0, zero_div]
    have : β' * ε = ε * ε := by
      have e1 : β' * ε = x ^ 2 := by field_simp at h1; linear_combination h1
      rw [e1, hε]
      linear_combination (-(x ^ 2)) * hl2
    exact mul_right_cancel₀ hε0 this
  rw [← hs', hβε, hγ', hε]
  ring

end EigenvalueR

section PowR

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (p : ℕ) [hpf : Fact p.Prime]
variable {R : Subalgebra ℤ ℂ} [IsNoetherianRing R]

/-- **Lemma 3.3(a) of Achimescu–Saha.** For a `T(p²)`-eigensequence with coefficients in a
finitely generated `R`-submodule of `ℂ` (`1/p` not integral over `R`)
and `p² ∤ m`, `a(p^{2j} m) = (χ(p)(m/p))^j a(m)`. -/
theorem eigen_pow_of_fgR (hpN : Nat.Coprime p N) (hpR : ¬ IsIntegral R ((p : ℂ)⁻¹)) {a : ℕ → ℂ}
    {L : Submodule R ℂ} (hL : L.FG)
    (haL : ∀ n, a n ∈ L) {c : ℂ} (hc : ∀ n, heckeCoeff χ p a n = c * a n) {m : ℕ}
    (hm : ¬ p ^ 2 ∣ m) (j : ℕ) :
    a (p ^ (2 * j) * m) = (χ (p : ZMod N) * (legendreSym p (m : ℤ) : ℂ)) ^ j * a m := by
  set x := χ (p : ZMod N) with hx
  set ε := x * (legendreSym p (m : ℤ) : ℂ) with hε
  set A : ℕ → ℂ := fun k => a (p ^ (2 * k) * m) with hA
  have hA0 : A 0 = a m := by simp [hA]
  have r0 : A 1 + ε / p * A 0 = c * A 0 := by
    have := hc m
    rw [heckeCoeff_base χ p a hm] at this
    change a (p ^ (2 * 1) * m) + ε / p * a (p ^ (2 * 0) * m) = c * a (p ^ (2 * 0) * m)
    simp only [Nat.mul_zero, pow_zero, one_mul, Nat.mul_one]
    rw [hε]; linear_combination this
  have rk : ∀ k, A (k + 2) + x ^ 2 / p * A k = c * A (k + 1) := by
    intro k
    have := hc (p ^ (2 * (k + 1)) * m)
    rw [heckeCoeff_step χ p a m k] at this
    simpa [hA] using this
  suffices H : ∀ k, A k = ε ^ k * A 0 ∧ A (k + 1) = ε ^ (k + 1) * A 0 by
    have := (H j).1
    rw [hA0] at this
    simpa [hA] using this
  by_cases ham : a m = 0
  · have h0 : A 0 = 0 := by rw [hA0]; exact ham
    have h1 : A 1 = 0 := by rw [h0, mul_zero, mul_zero, add_zero] at r0; exact r0
    have Z : ∀ k, A k = 0 ∧ A (k + 1) = 0 := by
      intro k
      induction k with
      | zero => exact ⟨h0, h1⟩
      | succ k ih =>
        refine ⟨ih.2, ?_⟩
        have := rk k
        rw [ih.1, ih.2, mul_zero, mul_zero, add_zero] at this
        exact this
    intro k
    rw [(Z k).1, (Z k).2, h0]
    simp
  · have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpf.out.ne_zero
    obtain ⟨hpm, hcval⟩ := eigenvalue_of_fgR χ p hpN hpR hL haL hc ham hm
    have hleg0 : legendreSym p (m : ℤ) ≠ 0 := by
      intro h0
      rw [legendreSym.eq_zero_iff] at h0
      exact hpm ((ZMod.natCast_eq_zero_iff m p).1 (by exact_mod_cast h0))
    have hl2 : (legendreSym p (m : ℤ) : ℂ) ^ 2 = 1 := by
      have := legendreSym.sq_one p (a := (m : ℤ)) (by
        intro h0; exact hleg0 ((legendreSym.eq_zero_iff p _).2 h0))
      exact_mod_cast this
    have hx2 : x ^ 2 = ε ^ 2 := by rw [hε, mul_pow, hl2, mul_one]
    have hc' : c = ε * (1 + 1 / (p : ℂ)) := by rw [hcval, hε]
    have h1 : A 1 = ε * A 0 := by
      rw [hc'] at r0
      linear_combination r0
    intro k
    induction k with
    | zero => exact ⟨by simp, by simpa using h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have e := rk k
      rw [ih.1, ih.2, hc', hx2] at e
      linear_combination e

end PowR

/-- `a(n p²) = ε a(n)` with `ε = χ(p)(m/p)`, `n = p^{2k} m`, `p² ∤ m`, and in addition
`a(n) = ε^k a(m)` (sequence form). -/
theorem seq_mul_sq_auxR {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (p : ℕ) [hpf : Fact p.Prime]
    {R : Subalgebra ℤ ℂ} [IsNoetherianRing R]
    (hpN : Nat.Coprime p N) (hpR : ¬ IsIntegral R ((p : ℂ)⁻¹)) {a : ℕ → ℂ}
    {L : Submodule R ℂ} (hL : L.FG)
    (haL : ∀ n, a n ∈ L) {c : ℂ} (hc : ∀ n, heckeCoeff χ p a n = c * a n) {n : ℕ} (hn : 0 < n) :
    ∃ m k : ℕ, ¬ p ^ 2 ∣ m ∧ n = p ^ (2 * k) * m ∧
      a (n * p ^ 2) = χ (p : ZMod N) * (legendreSym p (m : ℤ) : ℂ) * a n ∧
      a n = (χ (p : ZMod N) * (legendreSym p (m : ℤ) : ℂ)) ^ k * a m ∧
      (a m ≠ 0 → ¬ p ∣ m) := by
  have hpp := hpf.out
  have hndvd : ∀ m, ¬ p ^ 2 ∣ m → a m ≠ 0 → ¬ p ∣ m := fun m hm ham =>
    (eigenvalue_of_fgR χ p hpN hpR hL haL hc ham hm).1
  obtain ⟨e, n', hpn', hne⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hpp.one_lt.ne'
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' e
  · have hm : ¬ p ^ 2 ∣ n' := fun h => hpn' ((dvd_pow_self p two_ne_zero).trans h)
    refine ⟨n', k, hm, by rw [hne, hk], ?_⟩
    have E := eigen_pow_of_fgR χ p hpN hpR hL haL hc hm
    have e1 : n * p ^ 2 = p ^ (2 * (k + 1)) * n' := by rw [hne, hk]; ring
    have e2 : n = p ^ (2 * k) * n' := by rw [hne, hk]
    refine ⟨?_, ?_, hndvd _ hm⟩
    · rw [e1, E (k + 1), e2, E k]; ring
    · rw [e2, E k]
  · have hm : ¬ p ^ 2 ∣ p * n' := by
      rintro ⟨u, hu⟩
      apply hpn'
      refine ⟨u, ?_⟩
      have : p * n' = p * (p * u) := by rw [hu]; ring
      exact Nat.eq_of_mul_eq_mul_left hpp.pos this
    refine ⟨p * n', k, hm, by rw [hne, hk]; ring, ?_⟩
    have E := eigen_pow_of_fgR χ p hpN hpR hL haL hc hm
    have e1 : n * p ^ 2 = p ^ (2 * (k + 1)) * (p * n') := by rw [hne, hk]; ring
    have e2 : n = p ^ (2 * k) * (p * n') := by rw [hne, hk]; ring
    refine ⟨?_, ?_, hndvd _ hm⟩
    · rw [e1, E (k + 1), e2, E k]; ring
    · rw [e2, E k]

section JordanR

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (p : ℕ) [hpf : Fact p.Prime]
variable {R : Subalgebra ℤ ℂ} [IsNoetherianRing R]

/-- **The algebraic core of semisimplicity.** If `heckeCoeff a = c a + b` and
`heckeCoeff b = c b`, with `a`, `b` in finitely generated `R`-submodules of `ℂ`
(`1/p` not integral over `R`), then `b(n) = 0` for
every `n > 0`. -/
theorem jordan_coeff_zeroR (hpN : Nat.Coprime p N) (hpR : ¬ IsIntegral R ((p : ℂ)⁻¹)) {a b : ℕ → ℂ}
    {La Lb : Submodule R ℂ}
    (hLa : La.FG) (hLb : Lb.FG) (haL : ∀ n, a n ∈ La) (hbL : ∀ n, b n ∈ Lb) {c : ℂ}
    (ha : ∀ n, heckeCoeff χ p a n = c * a n + b n) (hb : ∀ n, heckeCoeff χ p b n = c * b n) :
    ∀ n, 0 < n → b n = 0 := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpf.out.ne_zero
  have hp1 : (p : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hpf.out.one_lt.ne'
  have hu : IsUnit (p : ZMod N) := (ZMod.isUnit_iff_coprime p N).2 hpN
  obtain ⟨e, he, hχe⟩ := exists_pow_chi_eq_one χ hu
  set x := χ (p : ZMod N) with hx
  -- Step 1: `b m = 0` whenever `p² ∤ m`
  have step1 : ∀ m, ¬ p ^ 2 ∣ m → b m = 0 := by
    intro m hm
    by_contra hbm
    obtain ⟨hpm, hc⟩ := eigenvalue_of_fgR χ p hpN hpR hLb hbL hb hbm hm
    set ε := x * (legendreSym p (m : ℤ) : ℂ) with hε
    have hleg0 : legendreSym p (m : ℤ) ≠ 0 := by
      rw [Ne, legendreSym.eq_zero_iff]
      exact_mod_cast (ZMod.natCast_eq_zero_iff m p).not.2 hpm
    have hl2 : (legendreSym p (m : ℤ) : ℂ) ^ 2 = 1 := by
      have := legendreSym.sq_one p (a := (m : ℤ)) (by
        intro h0; exact hleg0 ((legendreSym.eq_zero_iff p _).2 h0))
      exact_mod_cast this
    have hεx : ε ^ 2 = x ^ 2 := by rw [hε, mul_pow, hl2, mul_one]
    have hc' : c = ε + ε / p := by rw [hc]; ring
    set A : ℕ → ℂ := fun k => a (p ^ (2 * k) * m) with hA
    set B : ℕ → ℂ := fun k => b (p ^ (2 * k) * m) with hB
    have hB0 : B 0 = b m := by simp [hB]
    have rA0 : A 1 + ε / p * A 0 = c * A 0 + B 0 := by
      have := ha m
      rw [heckeCoeff_base χ p a hm] at this
      change a (p ^ (2 * 1) * m) + ε / p * a (p ^ (2 * 0) * m) =
        c * a (p ^ (2 * 0) * m) + b (p ^ (2 * 0) * m)
      simp only [Nat.mul_zero, pow_zero, one_mul, Nat.mul_one]
      rw [hε]; linear_combination this
    have rA : ∀ k, A (k + 2) + x ^ 2 / p * A k = c * A (k + 1) + B (k + 1) := by
      intro k
      have := ha (p ^ (2 * (k + 1)) * m)
      rw [heckeCoeff_step χ p a m k] at this
      simpa [hA, hB] using this
    have rB0 : B 1 + ε / p * B 0 = c * B 0 := by
      have := hb m
      rw [heckeCoeff_base χ p b hm] at this
      change b (p ^ (2 * 1) * m) + ε / p * b (p ^ (2 * 0) * m) = c * b (p ^ (2 * 0) * m)
      simp only [Nat.mul_zero, pow_zero, one_mul, Nat.mul_one]
      rw [hε]; linear_combination this
    have rB : ∀ k, B (k + 2) + x ^ 2 / p * B k = c * B (k + 1) := by
      intro k
      have := hb (p ^ (2 * (k + 1)) * m)
      rw [heckeCoeff_step χ p b m k] at this
      simpa [hB] using this
    -- `B_{k+1} = ε B_k`
    have hBs : ∀ k, B (k + 1) = ε * B k := by
      intro k
      induction k with
      | zero => rw [hc'] at rB0; linear_combination rB0
      | succ k ih =>
        have := rB k
        rw [hc'] at this
        linear_combination this + (ε / p) * ih + (B k / p) * hεx
    have hBk : ∀ k, B k = ε ^ k * B 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [hBs, ih, pow_succ]; ring
    -- the defect sequence `D_k = A_{k+1} − ε A_k − ε^k S`, `S = B_0 p/(p − 1)`
    set S : ℂ := B 0 * p / (p - 1) with hS
    have hSrel : B 0 - S + S / p = 0 := by rw [hS]; field_simp; ring
    set D : ℕ → ℂ := fun k => A (k + 1) - ε * A k - ε ^ k * S with hD
    have hDs : ∀ k, D (k + 1) = ε / p * D k := by
      intro k
      simp only [hD]
      have e1 := rA k
      rw [hc', ← hεx, hBk (k + 1)] at e1
      linear_combination e1 + ε ^ (k + 1) * hSrel
    have hDk : ∀ k, D k = (ε / p) ^ k * D 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [hDs, ih, pow_succ]; ring
    have hD0 : D 0 = -(S / p) := by
      simp only [hD]
      rw [hc'] at rA0
      linear_combination rA0 + hSrel
    have hS0 : S ≠ 0 := by
      rw [hS]
      exact div_ne_zero (mul_ne_zero (by rw [hB0]; exact hbm) hp0) hp1
    have hD0' : D 0 ≠ 0 := by
      rw [hD0]; exact neg_ne_zero.2 (div_ne_zero hS0 hp0)
    -- `ε` is a root of unity
    have hεM : ε ^ (2 * e) = 1 := by
      rw [pow_mul, hεx, ← pow_mul, mul_comm, pow_mul, hχe, one_pow]
    have hM : 0 < 2 * e := by omega
    -- `D_k` lies in a finitely generated subgroup
    set L : Submodule R ℂ := La ⊔ La.map (LinearMap.mulLeft R ε) ⊔
      Submodule.span R (Set.range fun j : Fin (2 * e) => ε ^ (j : ℕ) * S) with hL
    have hLfg : L.FG := ((hLa.sup (hLa.map _)).sup (Submodule.fg_span (Set.finite_range _)))
    have hDmem : ∀ k, D k ∈ L := by
      intro k
      refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
      · exact Submodule.mem_sup_left (Submodule.mem_sup_left (haL _))
      · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_map_of_mem (haL _)))
      · refine Submodule.mem_sup_right (Submodule.subset_span ⟨⟨k % (2 * e), Nat.mod_lt _ hM⟩, ?_⟩)
        change ε ^ (k % (2 * e)) * S = ε ^ k * S
        conv_rhs => rw [← Nat.mod_add_div k (2 * e), pow_add, pow_mul, hεM, one_pow, mul_one]
    have hint : IsIntegral R (ε / p) :=
      isIntegral_of_pow_mul_mem_R hLfg hD0' fun k => by rw [← hDk k]; exact hDmem k
    have hεint : IsIntegral R (ε ^ (2 * e - 1)) :=
      (isIntegral_of_pow_eq_one_R hM hεM).pow _
    have key : (p : ℂ)⁻¹ = ε / p * ε ^ (2 * e - 1) := by
      have : ε * ε ^ (2 * e - 1) = 1 := by
        rw [← pow_succ', show 2 * e - 1 + 1 = 2 * e by omega, hεM]
      rw [div_mul_eq_mul_div, this, one_div]
    exact hpR (key ▸ hint.mul hεint)
  -- Step 2: strong induction
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hdvd : p ^ 2 ∣ n
    · obtain ⟨n', rfl⟩ := hdvd
      have hp2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hpf.out.one_lt
      have hn' : 0 < n' := Nat.pos_of_mul_pos_left hn
      have hlt : n' < p ^ 2 * n' := lt_mul_left hn' hp2
      have e1 := hb n'
      simp only [heckeCoeff] at e1
      rw [ih n' hlt hn'] at e1
      have h2 : (if p ^ 2 ∣ n' then b (n' / p ^ 2) else 0) = 0 := by
        split_ifs with h
        · have hq : 0 < n' / p ^ 2 := Nat.div_pos (Nat.le_of_dvd hn' h) (by positivity)
          exact ih _ ((Nat.div_le_self _ _).trans_lt hlt) hq
        · rfl
      rw [h2] at e1
      simpa using e1
    · exact step1 n hdvd

end JordanR

/-! ## The S3/S4 chain from `SerreStarkBoundedCoeffAway24` -/

/-- `a(n p²) = ε a(n)` with `ε = χ(p)(m/p)`, `n = p^{2k} m`, `p² ∤ m`, and in addition
`a(n) = ε^k a(m)`. -/
theorem mCoeff_mul_sq_prime_auxA (hB : SerreStarkBoundedCoeffAway24) {N : ℕ} (hN : 0 < N)
    (h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (g : mSpace N χ) (P : HPrime N) {c : ℂ}
    (hc : heckeEnd χ h24 P g = c • g) {n : ℕ} (hn : 0 < n) :
    ∃ m k : ℕ, ¬ P.1 ^ 2 ∣ m ∧ n = P.1 ^ (2 * k) * m ∧
      mCoeff g (n * P.1 ^ 2) =
        χ (P.1 : ZMod N) * (jacobiSym (m : ℤ) P.1 : ℂ) * mCoeff g n ∧
      mCoeff g n = (χ (P.1 : ZMod N) * (jacobiSym (m : ℤ) P.1 : ℂ)) ^ k * mCoeff g m ∧
      (mCoeff g m ≠ 0 → ¬ P.1 ∣ m) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : Fact P.1.Prime := ⟨P.2.1⟩
  obtain ⟨M, hpM, hM0, L, hL, haL⟩ := awayData hB hN h24 χ g P.2.1 P.2.2.2
  have hpR := not_isIntegral_inv_prime_zInv P.2.1 hM0 hpM
  have hc' : ∀ n, heckeCoeff χ P.1 (mCoeff g) n = c * mCoeff g n := fun n => by
    rw [← mCoeff_heckeEnd χ h24 P g n, hc, mCoeff_smul]
  obtain ⟨m, k, h1, h2, h3, h4, h5⟩ := seq_mul_sq_auxR χ P.1 P.2.2.2 hpR hL haL hc' hn
  refine ⟨m, k, h1, h2, ?_, ?_, h5⟩
  · rw [h3, jacobiSym.legendreSym.to_jacobiSym]
  · rw [h4, jacobiSym.legendreSym.to_jacobiSym]

/-- **Prime step.** For an eigenform supported on `t·□`, `a(n p²) = χ(p)(t/p) a(n)`. -/
theorem mCoeff_mul_sq_primeA (hB : SerreStarkBoundedCoeffAway24) {N : ℕ} (hN : 0 < N)
    (h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (g : mSpace N χ) (P : HPrime N) {c : ℂ}
    (hc : heckeEnd χ h24 P g = c • g) {t : ℕ}
    (hsupp : ∀ n, 0 < n → mCoeff g n ≠ 0 → ∃ x, n = t * x ^ 2) {n : ℕ} (hn : 0 < n) :
    mCoeff g (n * P.1 ^ 2) = χ (P.1 : ZMod N) * (jacobiSym (t : ℤ) P.1 : ℂ) * mCoeff g n := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : Fact P.1.Prime := ⟨P.2.1⟩
  obtain ⟨m, k, hm, hnm, h1, h2, h5⟩ := mCoeff_mul_sq_prime_auxA hB hN h24 χ g P hc hn
  by_cases han : mCoeff g n = 0
  · rw [h1, han, mul_zero, mul_zero]
  have ham : mCoeff g m ≠ 0 := by
    intro h0; apply han; rw [h2, h0, mul_zero]
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hnm; omega
    · exact h
  have hpm := h5 ham
  obtain ⟨x, rfl⟩ := hsupp m hm0 ham
  have hxp : Nat.Coprime x P.1 := by
    refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd P.2.1).2 fun hd => hpm ?_))
    exact Dvd.dvd.mul_left (Dvd.dvd.pow hd two_ne_zero) t
  rw [h1, jacobiSym_mul_sq hxp]

/-- **Multiplicativity** (Serre–Stark; Achimescu–Saha Theorem 3.1(3)). For a simultaneous
`T(p²)`-eigenform supported on `t·□` and `v` prime to `N`, `a(n v²) = χ(v)(t/v) a(n)`. -/
theorem mCoeff_mul_sq_of_coprimeA (hB : SerreStarkBoundedCoeffAway24) {N : ℕ} (hN : 0 < N)
    (h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (g : mSpace N χ)
    (hE : ∀ P : HPrime N, ∃ c : ℂ, heckeEnd χ h24 P g = c • g) {t : ℕ}
    (hsupp : ∀ n, 0 < n → mCoeff g n ≠ 0 → ∃ x, n = t * x ^ 2) :
    ∀ v : ℕ, v.Coprime N → ∀ n, 0 < n →
      mCoeff g (n * v ^ 2) = χ (v : ZMod N) * (jacobiSym (t : ℤ) v : ℂ) * mCoeff g n := by
  intro v
  induction v using Nat.recOnMul with
  | zero =>
    intro h
    rw [Nat.coprime_zero_left] at h
    subst h
    exact absurd h24 (by norm_num)
  | one => intro _ n _; simp
  | prime p hp =>
    intro hpN n hn
    obtain ⟨c, hc⟩ := hE (hPrimeOfCoprime h24 hp hpN)
    exact mCoeff_mul_sq_primeA hB hN h24 χ g (hPrimeOfCoprime h24 hp hpN) hc hsupp hn
  | mul a b iha ihb =>
    intro hab n hn
    have ha : a.Coprime N := Nat.Coprime.coprime_mul_right hab
    have hb : b.Coprime N := Nat.Coprime.coprime_mul_left hab
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha; subst ha; exact absurd h24 (by norm_num)
    have hb0 : b ≠ 0 := by rintro rfl; simp at hb; subst hb; exact absurd h24 (by norm_num)
    have hna : 0 < n * a ^ 2 := Nat.mul_pos hn (by positivity)
    rw [show n * (a * b) ^ 2 = n * a ^ 2 * b ^ 2 by ring, ihb hb _ hna, iha ha n hn,
      Nat.cast_mul, map_mul, jacobiSym.mul_right' _ ha0 hb0]
    push_cast
    ring

/-- For a simultaneous eigenform supported on `t·□` (`t` squarefree) with `a(t s₀²) ≠ 0`, every
prime factor of `t` divides `N`; hence `t ∣ N`. -/
theorem squarefree_dvd_of_eigenA (hB : SerreStarkBoundedCoeffAway24) {N : ℕ} (hN : 0 < N)
    (h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (g : mSpace N χ)
    (hE : ∀ P : HPrime N, ∃ c : ℂ, heckeEnd χ h24 P g = c • g) {t s₀ : ℕ} (ht : Squarefree t)
    (hs₀ : 0 < s₀) (ha : mCoeff g (s₀ ^ 2 * t) ≠ 0) : t ∣ N := by
  haveI : NeZero N := ⟨hN.ne'⟩
  refine squarefree_dvd_of_primes hN.ne' ht fun q hq hqt => ?_
  by_contra hqN
  have hqN' : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hq).2 hqN
  let P := hPrimeOfCoprime h24 hq hqN'
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨c, hc⟩ := hE P
  have hn : 0 < s₀ ^ 2 * t := Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero ht.ne_zero)
  obtain ⟨m, k, hm, hnm, -, h2, h5⟩ := mCoeff_mul_sq_prime_auxA hB hN h24 χ g P hc hn
  have ham : mCoeff g m ≠ 0 := by intro h0; apply ha; rw [h2, h0, mul_zero]
  have hqm : ¬ q ∣ m := h5 ham
  -- the `q`-adic valuation of `s₀² t` is odd, so `q ∣ m`
  apply hqm
  have hv : (s₀ ^ 2 * t).factorization q = 2 * s₀.factorization q + 1 := by
    rw [Nat.factorization_mul (pow_pos hs₀ 2).ne' ht.ne_zero, Nat.factorization_pow]
    have h1 : t.factorization q = 1 := by
      have := ht.natFactorization_le_one q
      have := (hq.dvd_iff_one_le_factorization ht.ne_zero).1 hqt
      omega
    simp [h1]
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hnm; omega
  change s₀ ^ 2 * t = q ^ (2 * k) * m at hnm
  have hv' : (s₀ ^ 2 * t).factorization q = 2 * k + m.factorization q := by
    rw [hnm, Nat.factorization_mul (pow_pos hq.pos _).ne' hm0, Nat.factorization_pow]
    simp [hq.factorization_self]
  have : 1 ≤ m.factorization q := by omega
  exact (hq.dvd_iff_one_le_factorization hm0).2 this

/-- **The eigenvalue lemma from bounded coefficients.** -/
theorem eigenvalueLemma_of_boundedCoeffA (hB : SerreStarkBoundedCoeffAway24) :
    SerreStarkEigenvalueLemma24 := by
  intro N hN h24 χ P g c m hc ham hm
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : Fact P.1.Prime := ⟨P.2.1⟩
  obtain ⟨M, hpM, hM0, L, hL, haL⟩ := awayData hB hN h24 χ g P.2.1 P.2.2.2
  have hpR := not_isIntegral_inv_prime_zInv P.2.1 hM0 hpM
  have hc' : ∀ n, heckeCoeff χ P.1 (mCoeff g) n = c * mCoeff g n := fun n => by
    rw [← mCoeff_heckeEnd χ h24 P g n, hc, mCoeff_smul]
  obtain ⟨h1, h2⟩ := eigenvalue_of_fgR χ P.1 P.2.2.2 hpR hL haL hc' ham hm
  refine ⟨h1, ?_⟩
  rw [h2, jacobiSym.legendreSym.to_jacobiSym]

/-- **`T(p²)` has no Jordan blocks** (under bounded coefficients). -/
theorem heckeEnd_eigen_of_sqA (hB : SerreStarkBoundedCoeffAway24) {N : ℕ} (hN : 0 < N)
    (h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (P : HPrime N) (c : ℂ) (g : mSpace N χ)
    (h2 : ((heckeEnd χ h24 P - c • 1) ^ 2 : Module.End ℂ (mSpace N χ)) g = 0) :
    (heckeEnd χ h24 P - c • 1) g = 0 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : Fact P.1.Prime := ⟨P.2.1⟩
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  set T := heckeEnd χ h24 P
  set h := (T - c • 1) g with hh
  have hTg : T g = c • g + h := by
    rw [hh, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]; abel
  have hTh : T h = c • h := by
    have : (T - c • 1) h = 0 := by rw [hh, ← Module.End.mul_apply, ← sq]; exact h2
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
    exact this
  obtain ⟨M, hpM, hM0, La, hLa, haL, Lb, hLb, hbL⟩ := awayData2 hB hN h24 χ g h P.2.1 P.2.2.2
  have hpR := not_isIntegral_inv_prime_zInv P.2.1 hM0 hpM
  have ha : ∀ n, heckeCoeff χ P.1 (mCoeff g) n = c * mCoeff g n + mCoeff h n := fun n => by
    rw [← mCoeff_heckeEnd χ h24 P g n, show heckeEnd χ h24 P g = T g from rfl, hTg, mCoeff_add,
      mCoeff_smul]
  have hb : ∀ n, heckeCoeff χ P.1 (mCoeff h) n = c * mCoeff h n := fun n => by
    rw [← mCoeff_heckeEnd χ h24 P h n, show heckeEnd χ h24 P h = T h from rfl, hTh, mCoeff_smul]
  exact eq_zero_of_mCoeff_pos hN h4 h
    (jordan_coeff_zeroR χ P.1 P.2.2.2 hpR hLa hLb haL hbL ha hb)

theorem heckeEnd_eigen_of_powA (hB : SerreStarkBoundedCoeffAway24) {N : ℕ} (hN : 0 < N)
    (h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (P : HPrime N) (c : ℂ) :
    ∀ (k : ℕ) (g : mSpace N χ),
      ((heckeEnd χ h24 P - c • 1) ^ k : Module.End ℂ (mSpace N χ)) g = 0 →
      (heckeEnd χ h24 P - c • 1) g = 0 := by
  intro k
  induction k with
  | zero => intro g hg; rw [pow_zero, Module.End.one_apply] at hg; rw [hg, map_zero]
  | succ k ih =>
    intro g hg
    rw [pow_succ, Module.End.mul_apply] at hg
    have := ih _ hg
    exact heckeEnd_eigen_of_sqA hB hN h24 χ P c g (by rw [sq, Module.End.mul_apply]; exact this)

/-- Under bounded coefficients, generalised simultaneous eigenvectors are eigenvectors, so the
eigenform residual gives the generalised-eigenvector residual. -/
theorem genEigen_of_boundedCoeff_of_eigenformA (hB : SerreStarkBoundedCoeffAway24)
    (hE : SerreStarkEigenform24) : SerreStarkGenEigen24 := by
  intro N hN h24 χ μ g hg
  refine hE N hN h24 χ g fun P => ⟨μ P, ?_⟩
  have hgP : g ∈ (heckeEnd χ h24 P).maxGenEigenspace (μ P) := (Submodule.mem_iInf _).1 hg P
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hgP
  have := heckeEnd_eigen_of_powA hB hN h24 χ P (μ P) k g hk
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
  exact this

/-- **Reduction.** Bounded coefficients and the square-class residual give `ISerreStark` at
every level divisible by `24` (no Petersson input, no separate eigenvalue lemma). -/
theorem iSerreStark24_of_boundedCoeff_of_squareClassA (hB : SerreStarkBoundedCoeffAway24)
    (hQ : SerreStarkSquareClass24) : ISerreStark24 :=
  iSerreStark24_of_genEigen (genEigen_of_boundedCoeff_of_eigenformA hB
    (eigenform_of_eigenvalueLemma_of_squareClass (eigenvalueLemma_of_boundedCoeffA hB) hQ))

/-- **Reduction.** Bounded coefficients and the level-box residual give the square-class
residual. -/
theorem squareClass_of_boundedCoeff_of_levelBoxA (hB : SerreStarkBoundedCoeffAway24)
    (hL : SerreStarkLevelBox24) : SerreStarkSquareClass24 := by
  intro N hN h24 χ g hE hsq
  haveI : NeZero N := ⟨hN.ne'⟩
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  by_cases hall : ∀ n, 0 < n → mCoeff g n = 0
  · have := eq_zero_of_mCoeff_pos hN h4 g hall
    rw [this]
    exact Submodule.zero_mem _
  push Not at hall
  obtain ⟨n₀, hn₀, ha₀⟩ := hall
  obtain ⟨t, s₀, ht, hs₀, hn₀e, hsupp⟩ := exists_squarefree_class hsq hn₀ ha₀
  have htN : t ∣ N := squarefree_dvd_of_eigenA hB hN h24 χ g hE ht hs₀ (hn₀e ▸ ha₀)
  have h4t : 4 * t ∣ N := four_mul_dvd_of_squarefree h24 ht htN
  have hN1 : 1 < N := by have := Nat.le_of_dvd hN h24; omega
  set ψ := eigenChar χ h4t hN1
  have hmult := mCoeff_mul_sq_of_coprimeA hB hN h24 χ g hE hsupp
  have hcls : IsClassForm N _ ψ t (extH (g : ℍ → ℂ)) := by
    refine ⟨(extH_of_mem g.2).thetaType, fun n hn h => hsupp n hn h, fun n v hn hv => ?_⟩
    change mCoeff g (n * v ^ 2) = _ * mCoeff g n
    rw [hmult v hv n hn, eigenChar_natCast χ h4t hN1 hv]
  have := mem_span_of_levelBox hL hN h24 (eigenChar_isPrimitive χ h4t hN1)
    (conductor_eigenChar_dvd χ h4t hN1) ht htN hcls
  rwa [restrictUpper_extH] at this

/-- **Reduction.** Bounded coefficients and the level-box residual give `ISerreStark` at every
level divisible by `24`. -/
theorem iSerreStark24_of_boundedCoeff_of_levelBoxA (hB : SerreStarkBoundedCoeffAway24)
    (hL : SerreStarkLevelBox24) : ISerreStark24 :=
  iSerreStark24_of_boundedCoeff_of_squareClassA hB (squareClass_of_boundedCoeff_of_levelBoxA hB hL)

/-- **`ISerreStark24` from bounded coefficients away from the tower primes.** -/
theorem iSerreStark24_of_away (hB : SerreStarkBoundedCoeffAway24) : ISerreStark24 :=
  iSerreStark24_of_boundedCoeff_of_levelBoxA hB serreStarkLevelBox24

/-! ## Back to bounded coefficients: `θ_{n₀,r,t}` has natural-number coefficients -/

/-- The exponent map `m ↦ t (n₀ + r m)²`. -/
def rIdx (n₀ r : ℤ) (t : ℕ) (m : ℤ) : ℕ := t * (n₀ + r * m).natAbs ^ 2

/-- The `k`-th coefficient of `θ_{n₀,r,t}`: `#{m : t (n₀ + r m)² = k}`. -/
def rankOneCoeff (n₀ r : ℤ) (t k : ℕ) : ℂ := ∑' _b : rIdx n₀ r t ⁻¹' {k}, (1 : ℂ)

theorem finite_rIdx_fiber (n₀ : ℤ) {r : ℤ} (hr : r ≠ 0) {t : ℕ} (ht : 1 ≤ t) (k : ℕ) :
    (rIdx n₀ r t ⁻¹' {k}).Finite := by
  have hinj : Function.Injective fun m : ℤ => n₀ + r * m := fun a b h => by
    have : r * a = r * b := by simpa using h
    exact mul_left_cancel₀ hr this
  refine ((Set.finite_Icc (-(k : ℤ)) k).preimage hinj.injOn).subset fun m hm => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff, rIdx] at hm
  set b := n₀ + r * m
  have h1 : b.natAbs ≤ k := by
    rw [← hm]
    calc b.natAbs ≤ b.natAbs ^ 2 := Nat.le_self_pow two_ne_zero _
      _ ≤ t * b.natAbs ^ 2 := Nat.le_mul_of_pos_left _ ht
  have h2 : |b| ≤ k := by rw [Int.abs_eq_natAbs]; exact_mod_cast h1
  exact ⟨by linarith [(abs_le.1 h2).1], (abs_le.1 h2).2⟩

theorem rankOneCoeff_nat (n₀ : ℤ) {r : ℤ} (hr : r ≠ 0) {t : ℕ} (ht : 1 ≤ t) (k : ℕ) :
    ∃ z : ℕ, rankOneCoeff n₀ r t k = z := by
  haveI : Finite (rIdx n₀ r t ⁻¹' {k}) := (finite_rIdx_fiber n₀ hr ht k).to_subtype
  letI := Fintype.ofFinite (rIdx n₀ r t ⁻¹' {k})
  refine ⟨Fintype.card (rIdx n₀ r t ⁻¹' {k}), ?_⟩
  rw [rankOneCoeff, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

theorem hasSum_rankOneTheta (n₀ : ℤ) {r : ℤ} (hr : r ≠ 0) {t : ℕ} (ht : 1 ≤ t) {τ : ℂ}
    (hτ : 0 < τ.im) :
    HasSum (fun k : ℕ => rankOneCoeff n₀ r t k * cexp (2 * Real.pi * I * k * τ))
      (rankOneTheta n₀ r t τ) := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hs := summable_rankOneThetaTerm n₀ hr ht' hτ
  have hF := hs.hasSum.tsum_fiberwise (rIdx n₀ r t)
  refine hF.congr_fun fun k => ?_
  rw [rankOneCoeff, ← tsum_mul_right]
  refine tsum_congr fun ⟨b, hb⟩ => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb
  have e : ((t * (n₀ + r * b).natAbs ^ 2 : ℕ) : ℤ) = t * (n₀ + r * b) ^ 2 := by
    push_cast; rw [sq_abs]
  have hk : ((k : ℕ) : ℂ) = (((t : ℕ) : ℝ) : ℂ) * ((n₀ + r * b : ℤ) : ℂ) ^ 2 := by
    rw [← hb, rIdx, show (((t * (n₀ + r * b).natAbs ^ 2 : ℕ)) : ℂ) =
      (((t * (n₀ + r * b).natAbs ^ 2 : ℕ) : ℤ) : ℂ) by norm_cast, e]
    push_cast; ring
  rw [one_mul, rankOneThetaTerm, hk]
  congr 1
  ring

/-- `ISerreStark24` gives bounded coefficients (the `θ_{n₀,r,t}` have coefficients in `ℕ`). -/
theorem boundedCoeff24_of_iSerreStark24 (hI : ISerreStark24) : SerreStarkBoundedCoeff24 := by
  intro N hN h24 χ g
  obtain ⟨s, coef, hdata, hf⟩ := hI N (extH (g : ℍ → ℂ)) hN h24 (extH_of_mem g.2).thetaType
  have hr : ∀ i ∈ s, ((i.2.1 : ℕ) : ℤ) ≠ 0 := fun i hi => by
    have := (hdata i hi).1; omega
  set L : Submodule ℤ ℂ := ⨆ i : s, Submodule.span ℤ {coef i} with hL
  refine ⟨L, Submodule.fg_iSup _ fun i => Submodule.fg_span_singleton _, fun n => ?_⟩
  have hcoeff : mCoeff g n = ∑ i ∈ s, coef i * rankOneCoeff i.1 i.2.1 i.2.2 n := by
    unfold mCoeff
    refine (extH_of_mem g.2).thetaType.coeff_eq_of_hasSum
      (c := fun n => ∑ i ∈ s, coef i * rankOneCoeff i.1 i.2.1 i.2.2 n) (fun τ hτ => ?_) n
    rw [hf τ hτ]
    have := hasSum_sum (s := s) fun i hi =>
      (hasSum_rankOneTheta i.1 (hr i hi) (hdata i hi).2.1 hτ).mul_left (coef i)
    refine this.congr_fun fun k => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hcoeff]
  refine Submodule.sum_mem _ fun i hi => ?_
  obtain ⟨z, hz⟩ := rankOneCoeff_nat i.1 (hr i hi) (hdata i hi).2.1 n
  rw [hz]
  refine Submodule.mem_iSup_of_mem ⟨i, hi⟩ (Submodule.mem_span_singleton.2 ⟨z, ?_⟩)
  rw [zsmul_eq_mul, mul_comm]
  push_cast
  rfl

/-- **Bounded denominators at `p ∣ N` are free.** -/
theorem boundedCoeff24_of_away (hB : SerreStarkBoundedCoeffAway24) : SerreStarkBoundedCoeff24 :=
  boundedCoeff24_of_iSerreStark24 (iSerreStark24_of_away hB)

/-! ## The integral-weight principle away from `p` -/

/-- **`q`-expansion principle away from each `p ∤ N`, weight `k`, `Γ₁(N)`, `24 ∣ N`.** For every
`F ∈ M_k(Γ₁(N))` and every prime `p ∤ N` there are `M` with `p ∤ M` and a finitely generated
`L ⊂ ℂ` with every `q`-expansion coefficient in `awaySat M L`.

TRUE for `k ≥ 1`: it is implied by `QExpPrinciple24 k` (`M = 1`); it also follows from Katz's
`q`-expansion principle over `ℤ[1/N]` (`M = N`; Katz, *p-adic properties of modular schemes and
modular forms*, 1973, §1.6; Diamond–Im §12.3), which needs no input at the primes dividing `N`. -/
def QExpPrinciple24Away (k : ℤ) : Prop :=
  ∀ (N : ℕ) (_hN : 0 < N) (_h24 : 24 ∣ N)
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) (p : ℕ),
    p.Prime → p.Coprime N →
      ∃ M : ℕ, ¬ p ∣ M ∧ ∃ L : Submodule ℤ ℂ, L.FG ∧
        ∀ n, PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 F) ∈ awaySat M L

theorem qExpPrinciple24Away_of_qExpPrinciple24 {k : ℤ} (hQ : QExpPrinciple24 k) :
    QExpPrinciple24Away k := by
  intro N hN h24 F p hp _
  obtain ⟨L, hL, hc⟩ := hQ N hN h24 F
  exact ⟨1, hp.not_dvd_one, L, hL, fun n => mem_awaySat_of_mem (hc n)⟩

/-- **Katz's form: bounded denominators away from the level.** Every `F ∈ M_k(Γ₁(N))`
(`24 ∣ N`) has its `q`-expansion coefficients in `awaySat N L` for a finitely generated `L`, i.e.
in a finitely generated `ℤ[1/N]`-submodule of `ℂ`.

TRUE for `k ≥ 1`: Katz's `q`-expansion principle over `ℤ[1/N]` (Katz 1973, §1.6; Diamond–Im
§12.3), or Shimura Thm 3.52 plus the Eisenstein basis. It is stronger than `QExpPrinciple24Away`. -/
def QExpPrinciple24OverZInvN (k : ℤ) : Prop :=
  ∀ (N : ℕ) (_hN : 0 < N) (_h24 : 24 ∣ N)
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k),
    ∃ L : Submodule ℤ ℂ, L.FG ∧
      ∀ n, PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 F) ∈ awaySat N L

theorem qExpPrinciple24Away_of_overZInvN {k : ℤ} (hQ : QExpPrinciple24OverZInvN k) :
    QExpPrinciple24Away k := by
  intro N hN h24 F p hp hpN
  obtain ⟨L, hL, hc⟩ := hQ N hN h24 F
  exact ⟨N, (Nat.Prime.coprime_iff_not_dvd hp).1 hpN, L, hL, hc⟩

theorem qExpPrinciple24OverZInvN_of_qExpPrinciple24 {k : ℤ} (hQ : QExpPrinciple24 k) :
    QExpPrinciple24OverZInvN k := by
  intro N hN h24 F
  obtain ⟨L, hL, hc⟩ := hQ N hN h24 F
  exact ⟨L, hL, fun n => mem_awaySat_of_mem (hc n)⟩

/-- The θ-division of S6, away from `p`. -/
theorem boundedCoeffAway_of_qExpPrinciple24Away (j : ℕ) (hQ : QExpPrinciple24Away (1 + j)) :
    SerreStarkBoundedCoeffAway24 := by
  intro N hN h24 χ g p hp hpN
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  have hf := (extH_of_mem g.2).thetaType
  obtain ⟨M, hpM, L, hL, hcoeff⟩ := hQ N hN h24
    (thetaMultiple h4 hf (isThetaTypeForm_thetaRef h24) j) p hp hpN
  refine ⟨M, hpM, L, hL, fun n => ?_⟩
  rw [qExpansion_thetaMultiple h24 hf j] at hcoeff
  have ht : PowerSeries.constantCoeff (thetaInt ^ (2 * j + 1)) = 1 := by
    rw [map_pow, constantCoeff_thetaInt, one_pow]
  exact mem_of_mul_map_int _ ht hcoeff n

/-- **The q-expansion principle away from `p` suffices.** -/
theorem boundedCoeff24_of_qExpPrinciple24Away (j : ℕ) (hQ : QExpPrinciple24Away (1 + j)) :
    SerreStarkBoundedCoeff24 :=
  boundedCoeff24_of_away (boundedCoeffAway_of_qExpPrinciple24Away j hQ)

/-- Katz's form over `ℤ[1/N]`, weight two. -/
theorem boundedCoeff24_of_qExpPrinciple24OverZInvN_two (hQ : QExpPrinciple24OverZInvN 2) :
    SerreStarkBoundedCoeff24 :=
  boundedCoeff24_of_qExpPrinciple24Away 1 (by simpa using qExpPrinciple24Away_of_overZInvN hQ)

/-- Weight two. -/
theorem boundedCoeff24_of_qExpPrinciple24Away_two (hQ : QExpPrinciple24Away 2) :
    SerreStarkBoundedCoeff24 :=
  boundedCoeff24_of_qExpPrinciple24Away 1 (by simpa using hQ)

end SSHecke

end VOA.Classification.COne
