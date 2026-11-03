/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkProofEigen

/-!
# Serre–Stark S3-6: integrality gives the eigenvalue lemma and semisimplicity

We isolate one arithmetic input,

* `SerreStarkBoundedCoeff24`: the `q`-expansion coefficients of every `g ∈ M_{1/2}(N, χ)`
  (`24 ∣ N`) lie in a finitely generated additive subgroup of `ℂ`

(Serre–Stark's "coefficients algebraic with bounded denominators"), and prove from it, by a
purely algebraic integrality argument replacing Serre–Stark's `p`-adic one:

* `eigenvalueLemma_of_boundedCoeff`: Serre–Stark's eigenvalue lemma
  (`SerreStarkEigenvalueLemma24`): a `T(p²)`-eigenform with `a(m) ≠ 0`, `p² ∤ m`, has `p ∤ m` and
  eigenvalue `χ(p) (m/p) (1 + 1/p)`;
* `heckeEnd_eigen_of_sq`: `T(p²)` has no Jordan blocks: `(T − c)² g = 0 → (T − c) g = 0`
  (this replaces the Petersson residual `HeckeSemisimple24`);
* `iSerreStark24_of_boundedCoeff_of_squareClass`: `SerreStarkBoundedCoeff24` and the
  square-class residual `SerreStarkSquareClass24` give `ISerreStark24`.

The integrality argument: if `x^k y` (`y ≠ 0`) lies in a fixed finitely generated subgroup of `ℂ`
for all `k`, then `x` is integral over `ℤ` (`isIntegral_of_pow_mul_mem`); and `1/p` is not.
-/

open Complex
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-! ## Integrality -/

/-- If `x^k y` (`y ≠ 0`) lies in a fixed finitely generated `ℤ`-submodule of `ℂ` for every `k`,
then `x` is integral over `ℤ`. -/
theorem isIntegral_of_pow_mul_mem {L : Submodule ℤ ℂ} (hL : L.FG) {x y : ℂ} (hy : y ≠ 0)
    (h : ∀ k : ℕ, x ^ k * y ∈ L) : IsIntegral ℤ x := by
  set S := Submodule.span ℤ (Set.range fun k : ℕ => x ^ k * y) with hSdef
  have hS : S ≤ L := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact h k)
  refine isIntegral_of_smul_mem_submodule (A := ℂ) (M := ℂ) S ?_ (hL.of_le hS) x ?_
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

/-- `1/p` is not an algebraic integer. -/
theorem not_isIntegral_inv_prime {p : ℕ} (hp : p.Prime) : ¬ IsIntegral ℤ ((p : ℂ)⁻¹) := by
  intro h
  let f : ℚ →ₐ[ℤ] ℂ := (Algebra.ofId ℚ ℂ).restrictScalars ℤ
  have hf : Function.Injective f := (algebraMap ℚ ℂ).injective
  have h' : IsIntegral ℤ ((p : ℚ)⁻¹) := by
    rw [← isIntegral_algHom_iff f hf]
    convert h using 1
    simp [f]
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h'
  have hz' : (z : ℚ) * p = 1 := by
    rw [show (algebraMap ℤ ℚ z) = (z : ℚ) from rfl] at hz
    rw [hz]; exact inv_mul_cancel₀ (by exact_mod_cast hp.ne_zero)
  have : z * (p : ℤ) = 1 := by exact_mod_cast hz'
  have hd : (p : ℤ) ∣ 1 := ⟨z, by linarith⟩
  have := Int.eq_one_of_dvd_one (by positivity) hd
  exact hp.one_lt.ne' (by exact_mod_cast this)

/-- A root of unity is an algebraic integer. -/
theorem isIntegral_of_pow_eq_one {z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ n = 1) :
    IsIntegral ℤ z :=
  IsIntegral.of_pow hn (by rw [h]; exact isIntegral_one)

/-- Values of a Dirichlet character at units are roots of unity. -/
theorem exists_pow_chi_eq_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {u : ZMod N}
    (hu : IsUnit u) : ∃ n : ℕ, 0 < n ∧ χ u ^ n = 1 := by
  obtain ⟨v, rfl⟩ := hu
  refine ⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos, ?_⟩
  rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]

/-! ## Linearity of coefficients -/

theorem mCoeff_add {N : ℕ} {χ : DirichletCharacter ℂ N} (g h : mSpace N χ) (n : ℕ) :
    mCoeff (g + h) n = mCoeff g n + mCoeff h n := by
  unfold mCoeff
  rw [Submodule.coe_add, extH_add]
  exact (extH_of_mem g.2).thetaType.coeff_add (extH_of_mem h.2).thetaType n

theorem mCoeff_smul {N : ℕ} {χ : DirichletCharacter ℂ N} (c : ℂ) (g : mSpace N χ) (n : ℕ) :
    mCoeff (c • g) n = c * mCoeff g n := by
  unfold mCoeff
  rw [Submodule.coe_smul, extH_smul]
  exact (extH_of_mem g.2).thetaType.coeff_smul c n

theorem mCoeff_sub {N : ℕ} {χ : DirichletCharacter ℂ N} (g h : mSpace N χ) (n : ℕ) :
    mCoeff (g - h) n = mCoeff g n - mCoeff h n := by
  rw [show g - h = g + (-1 : ℂ) • h by rw [neg_one_smul, sub_eq_add_neg], mCoeff_add,
    mCoeff_smul]
  ring

/-! ## The arithmetic residual -/

/-- **Residual (bounded coefficients).** For `24 ∣ N`, the `q`-expansion coefficients of every
`g ∈ M_{1/2}(N, χ)` lie in a finitely generated `ℤ`-submodule of `ℂ`.

TRUE: `M_{1/2}(N, χ)` has a basis of forms whose coefficients are algebraic with bounded
denominators in a fixed number field (Serre–Stark, LNM 627, §3 and §5, via `f ↦ fθ` and the
`q`-expansion principle for integral weight, Shimura, *Introduction to the arithmetic theory of
automorphic functions*, Thm 3.52); `g` is a finite combination of them. It also follows from
Theorem A: the `θ_{ψ,t}` have coefficients in `ℤ[ψ]`. -/
def SerreStarkBoundedCoeff24 : Prop :=
  ∀ (N : ℕ) (_hN : 0 < N) (_h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (g : mSpace N χ),
    ∃ L : Submodule ℤ ℂ, L.FG ∧ ∀ n, mCoeff g n ∈ L

/-! ## The recurrence along `m p^{2k}` -/

section Recurrence

variable {N : ℕ} (χ : DirichletCharacter ℂ N) (p : ℕ) [hpf : Fact p.Prime]

theorem heckeCoeff_base (a : ℕ → ℂ) {m : ℕ} (hm : ¬ p ^ 2 ∣ m) :
    heckeCoeff χ p a m =
      a (p ^ 2 * m) + χ (p : ZMod N) * (legendreSym p (m : ℤ) : ℂ) / p * a m := by
  simp [heckeCoeff, hm]

theorem heckeCoeff_step (a : ℕ → ℂ) (m k : ℕ) :
    heckeCoeff χ p a (p ^ (2 * (k + 1)) * m) =
      a (p ^ (2 * (k + 2)) * m) + χ (p : ZMod N) ^ 2 / p * a (p ^ (2 * k) * m) := by
  have hdvd : p ^ 2 ∣ p ^ (2 * (k + 1)) * m :=
    Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) m
  have hleg : legendreSym p ((p ^ (2 * (k + 1)) * m : ℕ) : ℤ) = 0 := by
    rw [legendreSym.eq_zero_iff]
    push_cast
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ZMod.natCast_self]; simp
  have hdiv : p ^ (2 * (k + 1)) * m / p ^ 2 = p ^ (2 * k) * m := by
    rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add, mul_assoc,
      Nat.mul_div_cancel_left _ (pow_pos hpf.out.pos 2)]
  have hmul : p ^ 2 * (p ^ (2 * (k + 1)) * m) = p ^ (2 * (k + 2)) * m := by
    rw [← mul_assoc, ← pow_add]; ring_nf
  simp only [heckeCoeff, hleg, hdvd, if_true, hdiv, hmul]
  push_cast
  ring

end Recurrence

/-! ## The eigenvalue lemma -/

section Eigenvalue

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (p : ℕ) [hpf : Fact p.Prime]

/-- **The algebraic core of the eigenvalue lemma.** Let `a` be a sequence in a finitely generated
subgroup of `ℂ` with `heckeCoeff χ p a = c a`, `a(m) ≠ 0`, `p² ∤ m`, `p ∤ N`. Then `p ∤ m` and
`c = χ(p)(m/p)(1 + 1/p)`. -/
theorem eigenvalue_of_fg (hpN : Nat.Coprime p N) {a : ℕ → ℂ} {L : Submodule ℤ ℂ} (hL : L.FG)
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
  have hmem : ∀ (δ : ℂ) (k : ℕ), A (k + 1) - δ * A k ∈ L ⊔ L.map (LinearMap.mulLeft ℤ δ) :=
    fun δ k => Submodule.sub_mem _ (Submodule.mem_sup_left (haL _))
      (Submodule.mem_sup_right (Submodule.mem_map_of_mem (haL _)))
  have hfg : ∀ δ : ℂ, (L ⊔ L.map (LinearMap.mulLeft ℤ δ)).FG := fun δ => hL.sup (hL.map _)
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
      IsIntegral ℤ δ' := fun δ δ' hs hpr hne =>
    isIntegral_of_pow_mul_mem (hfg δ) hne fun k => by rw [← hQ δ δ' hs hpr k]; exact hmem δ k
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
    have ixinv : IsIntegral ℤ (x ^ (e - 1)) := (isIntegral_of_pow_eq_one he hχe).pow _
    have key : (p : ℂ)⁻¹ = β * γ * (x ^ (e - 1)) ^ 2 := by
      rw [hβγ, ← pow_mul]
      have : x ^ 2 * x ^ ((e - 1) * 2) = 1 := by
        rw [← pow_add, show 2 + (e - 1) * 2 = 2 * e by omega, pow_mul', hχe, one_pow]
      field_simp
      linear_combination (-1) * this
    exact not_isIntegral_inv_prime hpf.out (key ▸ ((iβ.mul iγ).mul (ixinv.pow 2)))
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

end Eigenvalue

/-- **The eigenvalue lemma from bounded coefficients.** -/
theorem eigenvalueLemma_of_boundedCoeff (hB : SerreStarkBoundedCoeff24) :
    SerreStarkEigenvalueLemma24 := by
  intro N hN h24 χ P g c m hc ham hm
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : Fact P.1.Prime := ⟨P.2.1⟩
  obtain ⟨L, hL, haL⟩ := hB N hN h24 χ g
  have hc' : ∀ n, heckeCoeff χ P.1 (mCoeff g) n = c * mCoeff g n := fun n => by
    rw [← mCoeff_heckeEnd χ h24 P g n, hc, mCoeff_smul]
  obtain ⟨h1, h2⟩ := eigenvalue_of_fg χ P.1 P.2.2.2 hL haL hc' ham hm
  refine ⟨h1, ?_⟩
  rw [h2, jacobiSym.legendreSym.to_jacobiSym]

/-! ## No Jordan blocks -/

section Jordan

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (p : ℕ) [hpf : Fact p.Prime]

/-- **The algebraic core of semisimplicity.** If `heckeCoeff a = c a + b` and
`heckeCoeff b = c b`, with `a`, `b` in finitely generated subgroups of `ℂ`, then `b(n) = 0` for
every `n > 0`. -/
theorem jordan_coeff_zero (hpN : Nat.Coprime p N) {a b : ℕ → ℂ} {La Lb : Submodule ℤ ℂ}
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
    obtain ⟨hpm, hc⟩ := eigenvalue_of_fg χ p hpN hLb hbL hb hbm hm
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
    set L : Submodule ℤ ℂ := La ⊔ La.map (LinearMap.mulLeft ℤ ε) ⊔
      Submodule.span ℤ (Set.range fun j : Fin (2 * e) => ε ^ (j : ℕ) * S) with hL
    have hLfg : L.FG := ((hLa.sup (hLa.map _)).sup (Submodule.fg_span (Set.finite_range _)))
    have hDmem : ∀ k, D k ∈ L := by
      intro k
      refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
      · exact Submodule.mem_sup_left (Submodule.mem_sup_left (haL _))
      · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_map_of_mem (haL _)))
      · refine Submodule.mem_sup_right (Submodule.subset_span ⟨⟨k % (2 * e), Nat.mod_lt _ hM⟩, ?_⟩)
        change ε ^ (k % (2 * e)) * S = ε ^ k * S
        conv_rhs => rw [← Nat.mod_add_div k (2 * e), pow_add, pow_mul, hεM, one_pow, mul_one]
    have hint : IsIntegral ℤ (ε / p) :=
      isIntegral_of_pow_mul_mem hLfg hD0' fun k => by rw [← hDk k]; exact hDmem k
    have hεint : IsIntegral ℤ (ε ^ (2 * e - 1)) :=
      (isIntegral_of_pow_eq_one hM hεM).pow _
    have key : (p : ℂ)⁻¹ = ε / p * ε ^ (2 * e - 1) := by
      have : ε * ε ^ (2 * e - 1) = 1 := by
        rw [← pow_succ', show 2 * e - 1 + 1 = 2 * e by omega, hεM]
      rw [div_mul_eq_mul_div, this, one_div]
    exact not_isIntegral_inv_prime hpf.out (key ▸ hint.mul hεint)
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

end Jordan

/-! ## Forms with only a constant term vanish -/

/-- The matrix `(1 0; N 1)`. -/
def lowerMat (N : ℕ) : SL(2, ℤ) :=
  ⟨!![1, 0; (N : ℤ), 1], by simp [Matrix.det_fin_two]⟩

/-- An element of `M_{1/2}(N, χ)` (`4 ∣ N`) whose positive-index coefficients all vanish is zero. -/
theorem eq_zero_of_mCoeff_pos {N : ℕ} (hN : 0 < N) (h4 : 4 ∣ N) {χ : DirichletCharacter ℂ N}
    (g : mSpace N χ) (hg : ∀ n, 0 < n → mCoeff g n = 0) : g = 0 := by
  have hf := extH_of_mem g.2
  set a0 := mCoeff g 0
  have hconst : ∀ τ : ℂ, 0 < τ.im → extH (g : ℍ → ℂ) τ = a0 := by
    intro τ hτ
    have hs := hf.thetaType.hasSum_coeff hτ
    have hs' : HasSum (fun n : ℕ => mCoeff g n * cexp (2 * Real.pi * I * n * τ))
        (mCoeff g 0 * cexp (2 * Real.pi * I * (0 : ℕ) * τ)) := by
      refine hasSum_single 0 fun n hn => ?_
      rw [hg n (Nat.pos_of_ne_zero hn), zero_mul]
    have := hs.unique hs'
    simpa using this
  have ha0 : a0 = 0 := by
    by_contra h0
    have hI : (0 : ℝ) < (I : ℂ).im := by simp
    have hγ : lowerMat N ∈ CongruenceSubgroup.Gamma0 N := by
      rw [CongruenceSubgroup.Gamma0_mem]; simp [lowerMat]
    have hlaw := hf.character (lowerMat N) hγ I hI
    rw [hconst _ (im_mobius_pos _ hI), hconst _ hI] at hlaw
    have h11 : ((lowerMat N 1 1 : ℤ) : ZMod N) = 1 := by simp [lowerMat]
    rw [h11, map_one, one_mul] at hlaw
    have heq : thetaRef I = thetaRef (mobius (lowerMat N) I) := by
      apply mul_left_cancel₀ h0; linear_combination hlaw
    have hc4 : (4 : ℤ) ∣ lowerMat N 1 0 := by
      simp [lowerMat]; exact_mod_cast h4
    have hnorm := norm_thetaRef_mobius hc4 hI
    rw [← heq] at hnorm
    have hθ : ‖thetaRef I‖ ≠ 0 := norm_ne_zero_iff.2 (thetaRef_ne_zero_of_im_pos hI)
    have h1 : ‖((lowerMat N 1 0 : ℤ) : ℂ) * I + ((lowerMat N 1 1 : ℤ) : ℂ)‖ ^ (1 / 2 : ℝ) = 1 := by
      have := hnorm
      field_simp at this
      linarith [this]
    have hgt : 1 < ‖((lowerMat N 1 0 : ℤ) : ℂ) * I + ((lowerMat N 1 1 : ℤ) : ℂ)‖ := by
      have hz := Complex.abs_im_le_norm
        (((lowerMat N 1 0 : ℤ) : ℂ) * I + ((lowerMat N 1 1 : ℤ) : ℂ))
      have him : (((lowerMat N 1 0 : ℤ) : ℂ) * I + ((lowerMat N 1 1 : ℤ) : ℂ)).im = N := by
        simp [lowerMat]
      rw [him] at hz
      have : (1 : ℝ) < N := by
        have : 4 ≤ N := Nat.le_of_dvd hN h4
        exact_mod_cast (by omega : 1 < N)
      linarith [abs_of_pos (show (0 : ℝ) < N by positivity)]
    have := Real.one_lt_rpow hgt (by norm_num : (0 : ℝ) < 1 / 2)
    linarith
  apply Subtype.ext
  funext τ
  rw [← extH_apply (g := (g : ℍ → ℂ)) τ.2, hconst _ τ.2, ha0]
  rfl

/-! ## Semisimplicity of `T(p²)` -/

/-- **`T(p²)` has no Jordan blocks** (under bounded coefficients). -/
theorem heckeEnd_eigen_of_sq (hB : SerreStarkBoundedCoeff24) {N : ℕ} (hN : 0 < N)
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
  obtain ⟨La, hLa, haL⟩ := hB N hN h24 χ g
  obtain ⟨Lb, hLb, hbL⟩ := hB N hN h24 χ h
  have ha : ∀ n, heckeCoeff χ P.1 (mCoeff g) n = c * mCoeff g n + mCoeff h n := fun n => by
    rw [← mCoeff_heckeEnd χ h24 P g n, show heckeEnd χ h24 P g = T g from rfl, hTg, mCoeff_add,
      mCoeff_smul]
  have hb : ∀ n, heckeCoeff χ P.1 (mCoeff h) n = c * mCoeff h n := fun n => by
    rw [← mCoeff_heckeEnd χ h24 P h n, show heckeEnd χ h24 P h = T h from rfl, hTh, mCoeff_smul]
  exact eq_zero_of_mCoeff_pos hN h4 h
    (jordan_coeff_zero χ P.1 P.2.2.2 hLa hLb haL hbL ha hb)

theorem heckeEnd_eigen_of_pow (hB : SerreStarkBoundedCoeff24) {N : ℕ} (hN : 0 < N)
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
    exact heckeEnd_eigen_of_sq hB hN h24 χ P c g (by rw [sq, Module.End.mul_apply]; exact this)

/-- Under bounded coefficients, generalised simultaneous eigenvectors are eigenvectors, so the
eigenform residual gives the generalised-eigenvector residual. -/
theorem genEigen_of_boundedCoeff_of_eigenform (hB : SerreStarkBoundedCoeff24)
    (hE : SerreStarkEigenform24) : SerreStarkGenEigen24 := by
  intro N hN h24 χ μ g hg
  refine hE N hN h24 χ g fun P => ⟨μ P, ?_⟩
  have hgP : g ∈ (heckeEnd χ h24 P).maxGenEigenspace (μ P) := (Submodule.mem_iInf _).1 hg P
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hgP
  have := heckeEnd_eigen_of_pow hB hN h24 χ P (μ P) k g hk
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
  exact this

/-- **Reduction.** Bounded coefficients and the square-class residual give `ISerreStark` at
every level divisible by `24` (no Petersson input, no separate eigenvalue lemma). -/
theorem iSerreStark24_of_boundedCoeff_of_squareClass (hB : SerreStarkBoundedCoeff24)
    (hQ : SerreStarkSquareClass24) : ISerreStark24 :=
  iSerreStark24_of_genEigen (genEigen_of_boundedCoeff_of_eigenform hB
    (eigenform_of_eigenvalueLemma_of_squareClass (eigenvalueLemma_of_boundedCoeff hB) hQ))

/-! ## Bounded coefficients follow from Theorem A -/

/-- The exponent map `n ↦ t |n|²`. -/
def sqIdx (t : ℕ) (n : ℤ) : ℕ := t * n.natAbs ^ 2

/-- The `k`-th coefficient of `θ_{ψ,t}`: `Σ_{t n² = k} ψ(n)`. -/
def charThetaCoeff (r : ℕ) (ψ : DirichletCharacter ℂ r) (t k : ℕ) : ℂ :=
  ∑' b : sqIdx t ⁻¹' {k}, ψ ((b : ℤ) : ZMod r)

theorem finite_sqIdx_fiber {t : ℕ} (ht : 1 ≤ t) (k : ℕ) : (sqIdx t ⁻¹' {k}).Finite := by
  refine (Set.finite_Icc (-(k : ℤ)) k).subset fun b hb => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff, sqIdx] at hb
  have h1 : b.natAbs ≤ k := by
    rw [← hb]
    calc b.natAbs ≤ b.natAbs ^ 2 := Nat.le_self_pow two_ne_zero _
      _ ≤ t * b.natAbs ^ 2 := Nat.le_mul_of_pos_left _ ht
  have h2 : |b| ≤ k := by rw [Int.abs_eq_natAbs]; exact_mod_cast h1
  exact ⟨by linarith [(abs_le.1 h2).1], (abs_le.1 h2).2⟩

theorem charThetaCoeff_mem {r : ℕ} [NeZero r] (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t)
    (k : ℕ) : charThetaCoeff r ψ t k ∈ Submodule.span ℤ (Set.range ψ) := by
  haveI : Finite (sqIdx t ⁻¹' {k}) := (finite_sqIdx_fiber ht k).to_subtype
  letI := Fintype.ofFinite (sqIdx t ⁻¹' {k})
  rw [charThetaCoeff, tsum_fintype]
  exact Submodule.sum_mem _ fun b _ => Submodule.subset_span ⟨_, rfl⟩

theorem hasSum_charTheta {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t) {τ : ℂ}
    (hτ : 0 < τ.im) :
    HasSum (fun k : ℕ => charThetaCoeff r ψ t k * cexp (2 * Real.pi * I * k * τ))
      (charTheta r ψ t τ) := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hs : Summable fun n : ℤ => ψ (n : ZMod r) * thetaExp t τ n := by
    refine Summable.of_norm_bounded (summable_thetaExp ht' hτ).norm fun n => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one ψ _)
  have hF := hs.hasSum.tsum_fiberwise (sqIdx t)
  refine hF.congr_fun fun k => ?_
  rw [charThetaCoeff, ← tsum_mul_right]
  refine tsum_congr fun ⟨b, hb⟩ => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb
  have e : ((t * b.natAbs ^ 2 : ℕ) : ℤ) = t * b ^ 2 := by
    push_cast; rw [sq_abs]
  have hk : ((k : ℕ) : ℂ) = (((t : ℕ) : ℝ) : ℂ) * ((b : ℤ) : ℂ) ^ 2 := by
    rw [← hb, sqIdx, show (((t * b.natAbs ^ 2 : ℕ)) : ℂ) =
      (((t * b.natAbs ^ 2 : ℕ) : ℤ) : ℂ) by norm_cast, e]
    push_cast; ring
  congr 1
  rw [thetaExp, hk]
  congr 1
  ring

theorem thetaTypeCoeff_charTheta {N : ℕ} (h24 : 24 ∣ N) {r t : ℕ} (hr : 0 < r) (ht : 1 ≤ t)
    (hdiv : 4 * t * r ^ 2 ∣ N) (ψ : DirichletCharacter ℂ r) (k : ℕ) :
    thetaTypeCoeff (charTheta r ψ t) k = charThetaCoeff r ψ t k :=
  (isThetaTypeForm_charTheta h24 hr ht hdiv ψ).coeff_eq_of_hasSum
    (fun _ hτ => hasSum_charTheta ψ ht hτ) k

/-- `SerreStarkBoundedCoeff24` is no stronger than Serre–Stark's Theorem A. -/
theorem boundedCoeff_of_theoremA (hA : SerreStarkTheoremA) : SerreStarkBoundedCoeff24 := by
  intro N hN h24 χ g
  have hspan := mem_span_of_theoremA hA hN h24 χ g
  rw [← restrictUpper_extH (g : ℍ → ℂ)] at hspan
  obtain ⟨m, r, t, ψ, c, hdata, hfg⟩ := exists_charTheta_of_mem_span hspan
  have hr : ∀ i, 0 < r i := fun i => by
    rcases Nat.eq_zero_or_pos (r i) with h | h
    · have := (hdata i).2.2.2; rw [h] at this; simp at this; omega
    · exact h
  haveI : ∀ i, NeZero (r i) := fun i => ⟨(hr i).ne'⟩
  set L : Submodule ℤ ℂ := ⨆ i, (Submodule.span ℤ (Set.range (ψ i))).map
    (LinearMap.mulLeft ℤ (c i)) with hL
  refine ⟨L, Submodule.fg_iSup _ fun i =>
    (Submodule.fg_span (Set.finite_range _)).map _, fun n => ?_⟩
  have hcoeff : mCoeff g n = ∑ i, c i * charThetaCoeff (r i) (ψ i) (t i) n := by
    unfold mCoeff
    refine (extH_of_mem g.2).thetaType.coeff_eq_of_hasSum
      (c := fun n => ∑ i, c i * charThetaCoeff (r i) (ψ i) (t i) n) (fun τ hτ => ?_) n
    rw [hfg τ hτ]
    have := hasSum_sum (s := Finset.univ) fun i _ =>
      (hasSum_charTheta (ψ i) (hdata i).2.2.1 hτ).mul_left (c i)
    refine this.congr_fun fun k => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hcoeff]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem
    (charThetaCoeff_mem (ψ i) (hdata i).2.2.1 n))

end SSHecke

end VOA.Classification.COne

