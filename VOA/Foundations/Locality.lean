/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.FormalCalculus
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Locality, the OPE, and normal ordering  (Gannon §5.1.2, pp. 316–317)

The structural results about pairs of `End(𝒱)`-valued distributions that the locality
axiom VA4 rests on.

* **Proposition 5.1.2.** For `f ∈ 𝒲⟦z₁^±, z₂^±⟧`, `(z₁ - z₂)ᴺ f(z₁,z₂) = 0` (some `N`)
  **iff** `f` is a finite sum of derivatives of the formal delta:
  `f(z₁,z₂) = ∑_{j=0}^{N-1} cⱼ(z₂) ∂_{z₂}^j δ(z₁/z₂)`. Two distributions `a(z), b(z)` are
  **mutually local** when `f(z₁,z₂) := [a(z₁), b(z₂)]` satisfies this.
* **Normal-ordered product** (5.1.6b): `:a(z₁)b(z₂): := a₊(z₁)b(z₂) + b(z₂)a₋(z₁)` with
  `a₊ = ∑_{n≥0} aₙ zⁿ`, `a₋ = ∑_{n<0} aₙ zⁿ`.

## Implementation notes
* We use `δ(z₁/z₂) = ∑_{k} z₁ᵏ z₂^{-k-1}` (Gannon's normalization, coefficient of
  `z₁ᵐz₂ⁿ` is `[m+n+1=0]`); this makes the coefficient recovery clean.
* `deltaDeriv j c` realizes `c(z₂) · ∂_{z₂}^j δ(z₁/z₂)` with the *plain* `j`-th derivative;
  its coefficient is `(∏_{i<j}(-m-1-i)) · c_{m+n+1+j}` (a falling factorial). With this
  convention the recovery in Prop 5.1.2 is `cⱼ = (1/j!)·Res_{z₁}((z₁-z₂)ʲ f)` — the `j!`
  is the price of using plain rather than divided powers (see `cCoeff`).
* `normalOrdered` is the genuine **two-variable** product (Gannon 5.1.6b), which is
  algebraically defined coefficient-by-coefficient. The same-variable `:a(z)b(z):` is only
  defined for *fields* (where `aₙv = 0` for `n ≫ 0`), which is not available at this level.

## Dependencies
* `VOA.Foundations.FormalCalculus`.

## Status
Complete & `sorry`-free / axiom-free for the core: `bracketDist`,
`Local`, `normalOrdered`, the `deltaDeriv` building block, the recovery `cCoeff`, and
**Proposition 5.1.2** (`local_iff_deltaSum`, both directions). The *optional* singular-OPE
decomposition (5.1.6a) and the explicit `cʲ₍ₖ₎` formula (5.1.6c) are **not formalised** here
(the recovered coefficient `cCoeff j (bracketDist a b)` already provides `cʲ`).

## References
* Gannon §5.1.2, eqs. (5.1.6); Kac, *Vertex Algebras for Beginners*, Thm 2.3;
  Lepowsky–Li, *Introduction to VOAs and Their Representations*, Ch. 3.
-/

namespace VOA

universe u v

open scoped BigOperators

/-! ## A falling-factorial finite-difference identity -/

/-- The forward difference of a falling factorial: `Δ[x⁽ʲ⁺¹⁾] = (j+1)·x⁽ʲ⁾`, i.e.
`∏_{i<j+1}(y+1-i) - ∏_{i<j+1}(y-i) = (j+1)·∏_{i<j}(y-i)`. This is the discrete analogue
of `d/dx xʲ⁺¹ = (j+1)xʲ`, and is the engine behind the peeling step in Proposition 5.1.2. -/
theorem fallingDiff (y : ℤ) (j : ℕ) :
    (∏ i ∈ Finset.range (j + 1), (y + 1 - (i : ℤ))) - ∏ i ∈ Finset.range (j + 1), (y - (i : ℤ))
      = ((j : ℤ) + 1) * ∏ i ∈ Finset.range j, (y - (i : ℤ)) := by
  rw [Finset.prod_range_succ' (fun i => y + 1 - (i : ℤ)) j,
      Finset.prod_range_succ (fun i => y - (i : ℤ)) j]
  have h : (∏ i ∈ Finset.range j, (y + 1 - ((i + 1 : ℕ) : ℤ)))
      = ∏ i ∈ Finset.range j, (y - (i : ℤ)) :=
    Finset.prod_congr rfl fun i _ => by push_cast; ring
  rw [h]; push_cast; ring

/-! ## The delta-derivative building block (general coefficients `𝒲`) -/

section Delta

variable {𝒲 : Type u} [AddCommGroup 𝒲] [Module ℂ 𝒲]

/-- The building block `deltaDeriv j c = c(z₂) · ∂_{z₂}^j δ(z₁/z₂)` of Proposition 5.1.2,
as a `ℂ`-linear map in the coefficient distribution `c`. Its `z₁ᵐz₂ⁿ`-coefficient is the
falling factorial `(∏_{i<j}(-m-1-i)) · c_{m+n+1+j}` (Gannon §5.1.2, eq. before 5.1.6). -/
def deltaDeriv (j : ℕ) : FormalDist 𝒲 →ₗ[ℂ] FormalDist₂ 𝒲 where
  toFun c := fun m n => (∏ i ∈ Finset.range j, (-m - 1 - (i : ℤ))) • c (m + n + 1 + j)
  map_add' c d := by
    ext m n
    change (∏ i ∈ Finset.range j, (-m - 1 - (i : ℤ))) • (c + d) (m + n + 1 + j)
         = (∏ i ∈ Finset.range j, (-m - 1 - (i : ℤ))) • c (m + n + 1 + j)
         + (∏ i ∈ Finset.range j, (-m - 1 - (i : ℤ))) • d (m + n + 1 + j)
    rw [show (c + d) (m + n + 1 + j) = c (m + n + 1 + j) + d (m + n + 1 + j) from rfl, smul_add]
  map_smul' a c := by
    ext m n
    change (∏ i ∈ Finset.range j, (-m - 1 - (i : ℤ))) • (a • c) (m + n + 1 + j)
         = a • ((∏ i ∈ Finset.range j, (-m - 1 - (i : ℤ))) • c (m + n + 1 + j))
    rw [show (a • c) (m + n + 1 + j) = a • c (m + n + 1 + j) from rfl, smul_comm]

@[simp] theorem deltaDeriv_apply (j : ℕ) (c : FormalDist 𝒲) (m n : ℤ) :
    deltaDeriv j c m n = (∏ i ∈ Finset.range j, (-m - 1 - (i : ℤ))) • c (m + n + 1 + j) := rfl

/-- The recovered coefficient `cⱼ = Res_{z₁}((z₁-z₂)ʲ f)`: the `z₁⁻¹`-coefficient of
`(z₁-z₂)ʲ f` (Gannon §5.1.2). (Up to the `j!` of the plain-power convention.) -/
def cCoeff (j : ℕ) (f : FormalDist₂ 𝒲) : FormalDist 𝒲 := fun n => mulBySubPow j f (-1) n

@[simp] theorem cCoeff_apply (j : ℕ) (f : FormalDist₂ 𝒲) (n : ℤ) :
    cCoeff j f n = mulBySubPow j f (-1) n := rfl

/-! ### The peeling identities -/

/-- **Peel-off** identity (Gannon's induction step, p. 316):
`(z₁-z₂)·(c·∂ʲ⁺¹δ) = (j+1)·(c·∂ʲδ)`. Proven via the falling-factorial finite
difference `fallingDiff`. -/
theorem mulBySub_deltaDeriv (j : ℕ) (c : FormalDist 𝒲) :
    mulBySub (deltaDeriv (j + 1) c) = ((j : ℤ) + 1) • deltaDeriv j c := by
  ext m n
  have ek1 : (m - 1) + n + 1 + ((j + 1 : ℕ) : ℤ) = m + n + 1 + ((j : ℕ) : ℤ) := by push_cast; ring
  have ek2 : m + (n - 1) + 1 + ((j + 1 : ℕ) : ℤ) = m + n + 1 + ((j : ℕ) : ℤ) := by push_cast; ring
  have e1 : (∏ i ∈ Finset.range (j + 1), (-(m - 1) - 1 - (i : ℤ)))
      = ∏ i ∈ Finset.range (j + 1), ((-m - 1) + 1 - (i : ℤ)) :=
    Finset.prod_congr rfl fun i _ => by ring
  have e2 : (∏ i ∈ Finset.range (j + 1), (-m - 1 - (i : ℤ)))
      = ∏ i ∈ Finset.range (j + 1), ((-m - 1) - (i : ℤ)) :=
    Finset.prod_congr rfl fun i _ => by ring
  have e3 : (∏ i ∈ Finset.range j, (-m - 1 - (i : ℤ)))
      = ∏ i ∈ Finset.range j, ((-m - 1) - (i : ℤ)) :=
    Finset.prod_congr rfl fun i _ => by ring
  rw [mulBySub_apply]
  change deltaDeriv (j + 1) c (m - 1) n - deltaDeriv (j + 1) c m (n - 1)
     = ((j : ℤ) + 1) • deltaDeriv j c m n
  rw [deltaDeriv_apply, deltaDeriv_apply, deltaDeriv_apply, ek1, ek2, e1, e2, e3, ← sub_smul,
      fallingDiff (-m - 1) j, mul_smul]

/-- The `j = 0` base of the peel-off: `(z₁-z₂)·(c·δ) = 0`. -/
theorem mulBySub_deltaDeriv_zero (c : FormalDist 𝒲) : mulBySub (deltaDeriv 0 c) = 0 := by
  ext m n
  rw [mulBySub_apply]
  change deltaDeriv 0 c (m - 1) n - deltaDeriv 0 c m (n - 1) = (0 : 𝒲)
  rw [deltaDeriv_apply, deltaDeriv_apply,
      show (m - 1) + n + 1 + ((0 : ℕ) : ℤ) = m + n from by push_cast; ring,
      show m + (n - 1) + 1 + ((0 : ℕ) : ℤ) = m + n from by push_cast; ring]
  simp

/-- The two ways to strip a factor from `(z₁-z₂)ᴺ⁺¹` agree: `(z₁-z₂)ᴺ⁺¹ f = (z₁-z₂)ᴺ
((z₁-z₂)f)`. (`mulBySubPow` commutes with `mulBySub`.) -/
theorem mulBySubPow_succ' (N : ℕ) (f : FormalDist₂ 𝒲) :
    mulBySubPow (N + 1) f = mulBySubPow N (mulBySub f) := by
  induction N with
  | zero => simp [mulBySubPow_one]
  | succ k ih =>
    rw [mulBySubPow_succ, LinearMap.comp_apply, ih, ← LinearMap.comp_apply, ← mulBySubPow_succ]

/-- Iterating the peel-off `N` times: `(z₁-z₂)ᴺ·(c·∂ᴺδ) = N!·(c·δ)` (Gannon's induction,
giving the factorial that appears in the coefficient recovery). -/
theorem mulBySubPow_deltaDeriv_self (N : ℕ) (c : FormalDist 𝒲) :
    mulBySubPow N (deltaDeriv N c) = (N.factorial : ℤ) • deltaDeriv 0 c := by
  induction N with
  | zero => simp
  | succ k ih =>
    have hc : ((k : ℤ) + 1) * (k.factorial : ℤ) = ((k + 1).factorial : ℤ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [mulBySubPow_succ', mulBySub_deltaDeriv, map_zsmul, ih, smul_smul, hc]

/-- `(z₁-z₂)ʲ⁺¹·(c·∂ʲδ) = 0`: one more factor than the order of the derivative kills it. -/
theorem mulBySubPow_succ_deltaDeriv (j : ℕ) (c : FormalDist 𝒲) :
    mulBySubPow (j + 1) (deltaDeriv j c) = 0 := by
  rw [mulBySubPow_succ, LinearMap.comp_apply, mulBySubPow_deltaDeriv_self, map_zsmul,
      mulBySub_deltaDeriv_zero, smul_zero]

/-- `(z₁-z₂)ᴺ·(c·∂ʲδ) = 0` whenever `j < N`: the building blocks of the decomposition are
annihilated by high enough powers (the easy direction of Proposition 5.1.2). -/
theorem mulBySubPow_deltaDeriv_eq_zero {j N : ℕ} (h : j + 1 ≤ N) (c : FormalDist 𝒲) :
    mulBySubPow N (deltaDeriv j c) = 0 := by
  induction N, h using Nat.le_induction with
  | base => exact mulBySubPow_succ_deltaDeriv j c
  | succ n _ ih => rw [mulBySubPow_succ, LinearMap.comp_apply, ih, map_zero]

/-- The `N = 1` heart of Proposition 5.1.2: if `(z₁-z₂)f = 0` then `f = c·δ(z₁/z₂)` with
`c = Res_{z₁} f`. Proven by the antidiagonal-invariance argument (`f` is constant along
`m+n = const`). -/
theorem eq_deltaDeriv_zero_of_mulBySub_eq_zero {f : FormalDist₂ 𝒲} (hf : mulBySub f = 0) :
    f = deltaDeriv 0 (fun n => f (-1) n) := by
  have hrel : ∀ a b : ℤ, f (a - 1) b = f a (b - 1) := fun a b => by
    have h := congrFun (congrFun hf a) b
    rw [mulBySub_apply, show (0 : FormalDist₂ 𝒲) a b = (0 : 𝒲) from rfl, sub_eq_zero] at h
    exact h
  have hstep : ∀ m n : ℤ, f m n = f (m - 1) (n + 1) := fun m n => by
    have h := hrel m (n + 1)
    rw [show n + 1 - 1 = n from by ring] at h
    exact h.symm
  have hstep' : ∀ m n : ℤ, f m n = f (m + 1) (n - 1) := fun m n => by
    have h := hrel (m + 1) n
    rw [show m + 1 - 1 = m from by ring] at h
    exact h
  have hgen : ∀ (d : ℤ) (m n : ℤ), f m n = f (m - d) (n + d) := by
    intro d
    induction d using Int.induction_on with
    | zero => intro m n; simp
    | succ k ih =>
        intro m n
        rw [ih m n, hstep (m - (k : ℤ)) (n + (k : ℤ)),
            show m - (k : ℤ) - 1 = m - ((k : ℤ) + 1) from by ring,
            show n + (k : ℤ) + 1 = n + ((k : ℤ) + 1) from by ring]
    | pred k ih =>
        intro m n
        rw [ih m n, hstep' (m - -(k : ℤ)) (n + -(k : ℤ)),
            show m - -(k : ℤ) + 1 = m - (-(k : ℤ) - 1) from by ring,
            show n + -(k : ℤ) - 1 = n + (-(k : ℤ) - 1) from by ring]
  ext m n
  rw [hgen (m + 1) m n, deltaDeriv_apply]
  simp only [Finset.range_zero, Finset.prod_empty, one_smul, Nat.cast_zero]
  rw [show m - (m + 1) = (-1 : ℤ) from by ring, show n + (m + 1) = m + n + 1 + 0 from by ring]

/-- **Existence** half of Proposition 5.1.2: if `(z₁-z₂)ᴺ f = 0` then `f` is a finite sum
`∑_{j<N} cⱼ · ∂ʲδ(z₁/z₂)`. Proven by induction on `N`, peeling off the top term
`deltaDeriv (N-1) cₙ₋₁` (with `cₙ₋₁ = (1/(N-1)!)·Res_{z₁}((z₁-z₂)ᴺ⁻¹f)`) and applying the
induction hypothesis to the remainder. -/
theorem exists_deltaSum_of_mulBySubPow_eq_zero (N : ℕ) (f : FormalDist₂ 𝒲)
    (hf : mulBySubPow N f = 0) :
    ∃ c : Fin N → FormalDist 𝒲, f = ∑ j : Fin N, deltaDeriv (j : ℕ) (c j) := by
  induction N generalizing f with
  | zero => exact ⟨Fin.elim0, by simpa using hf⟩
  | succ k ih =>
    have hg : mulBySub (mulBySubPow k f) = 0 := by
      rw [← LinearMap.comp_apply, ← mulBySubPow_succ]; exact hf
    let cN : FormalDist 𝒲 := (k.factorial : ℂ)⁻¹ • fun n => mulBySubPow k f (-1) n
    have htop : mulBySubPow k (deltaDeriv k cN) = mulBySubPow k f := by
      rw [mulBySubPow_deltaDeriv_self, eq_deltaDeriv_zero_of_mulBySub_eq_zero hg, ← map_zsmul]
      congr 1
      ext n
      change (k.factorial : ℤ) • ((k.factorial : ℂ)⁻¹ • mulBySubPow k f (-1) n)
         = mulBySubPow k f (-1) n
      rw [← Int.cast_smul_eq_zsmul ℂ (k.factorial : ℤ), Int.cast_natCast, smul_smul,
          mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_smul]
    have hf' : mulBySubPow k (f - deltaDeriv k cN) = 0 := by rw [map_sub, htop, sub_self]
    obtain ⟨c', hc'⟩ := ih (f - deltaDeriv k cN) hf'
    refine ⟨Fin.snoc c' cN, ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
    rw [← hc', sub_add_cancel]

/-- **Proposition 5.1.2** (Gannon §5.1.2, pp. 316–317; Kac, *VA for Beginners*, Thm 2.3).
A two-variable distribution is annihilated by `(z₁-z₂)ᴺ` **iff** it is a finite sum of
`δ(z₁/z₂)`-derivatives `∑_{j<N} cⱼ(z₂) ∂_{z₂}ʲ δ(z₁/z₂)`. This is the technical heart that
makes mutual locality equivalent to the Jacobi identity for vertex algebras.
(Stated for all `N`; Gannon's `1 ≤ N` is inessential.) -/
theorem local_iff_deltaSum (f : FormalDist₂ 𝒲) (N : ℕ) :
    mulBySubPow N f = 0 ↔
      ∃ c : Fin N → FormalDist 𝒲, f = ∑ j : Fin N, deltaDeriv (j : ℕ) (c j) := by
  refine ⟨exists_deltaSum_of_mulBySubPow_eq_zero N f, ?_⟩
  rintro ⟨c, rfl⟩
  rw [map_sum]
  exact Finset.sum_eq_zero fun j _ =>
    mulBySubPow_deltaDeriv_eq_zero (Nat.succ_le_of_lt j.isLt) (c j)

/-! ### Smoke tests -/

/-- A single `δ`-derivative is annihilated by one power of `(z₁-z₂)`. -/
example (c : FormalDist 𝒲) : mulBySubPow 1 (deltaDeriv 0 c) = 0 :=
  mulBySubPow_succ_deltaDeriv 0 c

/-- Proposition 5.1.2 produces the explicit `δ`-decomposition from the locality bound. -/
example (f : FormalDist₂ 𝒲) (h : mulBySubPow 1 f = 0) :
    ∃ c : Fin 1 → FormalDist 𝒲, f = ∑ j : Fin 1, deltaDeriv (j : ℕ) (c j) :=
  (local_iff_deltaSum f 1).mp h

end Delta

/-! ## Mutual locality and normal ordering (operator-valued distributions) -/

section Operators

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- The commutator two-variable distribution `[a(z₁), b(z₂)]` of two `End ℂ V`-valued
distributions: `(bracketDist a b) m n = aₘ bₙ - bₙ aₘ` (Gannon §5.1.2, before 5.1.6). -/
def bracketDist (a b : FormalDist (Module.End ℂ V)) : FormalDist₂ (Module.End ℂ V) :=
  fun m n => a m * b n - b n * a m

@[simp] theorem bracketDist_apply (a b : FormalDist (Module.End ℂ V)) (m n : ℤ) :
    bracketDist a b m n = a m * b n - b n * a m := rfl

/-- Two `End ℂ V`-valued distributions are **mutually local** when some power of `(z₁-z₂)`
annihilates their commutator (Gannon §5.1.2, the locality condition behind VA4). -/
def Local (a b : FormalDist (Module.End ℂ V)) : Prop :=
  ∃ N : ℕ, mulBySubPow N (bracketDist a b) = 0

/-- The **normal-ordered product** `:a(z₁)b(z₂):` (Gannon 5.1.6b): the positive `z₁`-modes
of `a` move to the left of `b`, the negative ones to the right. As a two-variable
distribution it is algebraically defined coefficient-by-coefficient. -/
def normalOrdered (a b : FormalDist (Module.End ℂ V)) : FormalDist₂ (Module.End ℂ V) :=
  fun m n => if 0 ≤ m then a m * b n else b n * a m

@[simp] theorem normalOrdered_apply (a b : FormalDist (Module.End ℂ V)) (m n : ℤ) :
    normalOrdered a b m n = if 0 ≤ m then a m * b n else b n * a m := rfl

/-- Distributions whose commutator vanishes are local (with `N = 0`): the base case of
mutual locality. -/
theorem local_of_bracketDist_eq_zero {a b : FormalDist (Module.End ℂ V)}
    (h : bracketDist a b = 0) : Local a b :=
  ⟨0, by rw [mulBySubPow_zero]; exact congrArg _ h⟩

/-- Smoke test: two distributions with vanishing commutator are mutually local (`N = 0`). -/
example (a b : FormalDist (Module.End ℂ V)) (h : bracketDist a b = 0) : Local a b :=
  local_of_bracketDist_eq_zero h

/-! ### The `ε`-twisted commutator: super-locality (Axis B)

For a **super** vertex algebra the commutator carries the Koszul sign

  `[a(z₁), b(z₂)] = a(z₁)b(z₂) − (−1)^{|a||b|} b(z₂)a(z₁)`,

so locality is a statement about a *sign-twisted* bracket.  Rather than duplicating the
locality apparatus we abstract the sign as a scalar parameter `ε : ℂ`: the ordinary
(bosonic) theory is the instance `ε = 1` (`bracketDistε_one`) and the super theory the
instance `ε = (−1)^{|a||b|}`.  Every downstream result that never *inspects* the sign is
then shared verbatim between the two.

This is deliberately independent of the weight grading: half-integer moding (Axis A) and
parity (Axis B) are separate generalizations, and no spin–statistics relation between them
is assumed here.
-/

/-- The **`ε`-twisted commutator** `[a(z₁), b(z₂)]_ε` of two `End ℂ V`-valued distributions:
`(bracketDistε ε a b) m n = aₘ bₙ − ε · (bₙ aₘ)`.  Taking `ε = 1` gives the ordinary
commutator `bracketDist`; taking `ε = (−1)^{|a||b|}` gives the super-commutator. -/
def bracketDistε (ε : ℂ) (a b : FormalDist (Module.End ℂ V)) : FormalDist₂ (Module.End ℂ V) :=
  fun m n => a m * b n - ε • (b n * a m)

@[simp] theorem bracketDistε_apply (ε : ℂ) (a b : FormalDist (Module.End ℂ V)) (m n : ℤ) :
    bracketDistε ε a b m n = a m * b n - ε • (b n * a m) := rfl

/-- At `ε = 1` the twisted commutator is the ordinary one: the bosonic theory is the
instance `ε = 1` of the super theory. -/
theorem bracketDistε_one (a b : FormalDist (Module.End ℂ V)) :
    bracketDistε 1 a b = bracketDist a b := by
  apply FormalDist₂.ext; intro m n
  simp

/-- **`ε`-twisted mutual locality.**  Some power of `(z₁-z₂)` annihilates the `ε`-twisted
commutator.  `Localε 1` is ordinary locality (`localε_one_iff`). -/
def Localε (ε : ℂ) (a b : FormalDist (Module.End ℂ V)) : Prop :=
  ∃ N : ℕ, mulBySubPow N (bracketDistε ε a b) = 0

/-- `Localε 1` is ordinary mutual locality, so VA4 is the `ε = 1` instance of super-VA4. -/
theorem localε_one_iff (a b : FormalDist (Module.End ℂ V)) :
    Localε 1 a b ↔ Local a b := by
  unfold Localε Local
  rw [bracketDistε_one]

/-- The `ε`-twisted commutator is additive in its left argument. -/
theorem bracketDistε_add_left (ε : ℂ) (a₁ a₂ b : FormalDist (Module.End ℂ V)) :
    bracketDistε ε (a₁ + a₂) b = bracketDistε ε a₁ b + bracketDistε ε a₂ b := by
  apply FormalDist₂.ext; intro m n
  change (a₁ m + a₂ m) * b n - ε • (b n * (a₁ m + a₂ m))
      = (a₁ m * b n - ε • (b n * a₁ m)) + (a₂ m * b n - ε • (b n * a₂ m))
  rw [add_mul, mul_add, smul_add, sub_add_sub_comm]

/-- The `ε`-twisted commutator is additive in its right argument. -/
theorem bracketDistε_add_right (ε : ℂ) (a b₁ b₂ : FormalDist (Module.End ℂ V)) :
    bracketDistε ε a (b₁ + b₂) = bracketDistε ε a b₁ + bracketDistε ε a b₂ := by
  apply FormalDist₂.ext; intro m n
  change a m * (b₁ n + b₂ n) - ε • ((b₁ n + b₂ n) * a m)
      = (a m * b₁ n - ε • (b₁ n * a m)) + (a m * b₂ n - ε • (b₂ n * a m))
  rw [mul_add, add_mul, smul_add, sub_add_sub_comm]

/-- **`ε`-antisymmetry.**  Swapping the two slots inverts the sign:
`[a,b]_ε (m,n) = −ε · [b,a]_{ε⁻¹} (n,m)`.  For the super case `ε = ±1` one has `ε⁻¹ = ε`,
recovering the familiar `[a,b] = −(−1)^{|a||b|}[b,a]`. -/
theorem bracketDistε_swap {ε : ℂ} (hε : ε ≠ 0) (a b : FormalDist (Module.End ℂ V)) (m n : ℤ) :
    bracketDistε ε a b m n = -(ε • bracketDistε ε⁻¹ b a n m) := by
  change a m * b n - ε • (b n * a m) = -(ε • (b n * a m - ε⁻¹ • (a m * b n)))
  rw [smul_sub, smul_smul, mul_inv_cancel₀ hε, one_smul, neg_sub]

/-- Distributions whose `ε`-twisted commutator vanishes are `ε`-local (with `N = 0`). -/
theorem localε_of_bracketDistε_eq_zero {ε : ℂ} {a b : FormalDist (Module.End ℂ V)}
    (h : bracketDistε ε a b = 0) : Localε ε a b :=
  ⟨0, by rw [mulBySubPow_zero]; exact congrArg _ h⟩

/-- Everything is `ε`-local with the zero distribution (on the right). -/
theorem localε_zero_right (ε : ℂ) (a : FormalDist (Module.End ℂ V)) : Localε ε a 0 := by
  refine localε_of_bracketDistε_eq_zero ?_
  apply FormalDist₂.ext; intro m n
  change a m * (0 : Module.End ℂ V) - ε • ((0 : Module.End ℂ V) * a m) = 0
  simp

/-- Everything is `ε`-local with the zero distribution (on the left). -/
theorem localε_zero_left (ε : ℂ) (b : FormalDist (Module.End ℂ V)) : Localε ε 0 b := by
  refine localε_of_bracketDistε_eq_zero ?_
  apply FormalDist₂.ext; intro m n
  change (0 : Module.End ℂ V) * b n - ε • (b n * (0 : Module.End ℂ V)) = 0
  simp


/-! ### Proposition 5.1.2 is sign-agnostic

`local_iff_deltaSum` is stated for an *arbitrary* two-variable distribution, so the whole
`δ`-decomposition apparatus — and with it the OPE — transfers to the `ε`-twisted setting
with no new work.  This is the structural reason the super theory is a refactor rather than
a rewrite: the sign lives only in *which* two-variable distribution one feeds in.
-/

/-- **Proposition 5.1.2, `ε`-generically.**  Two fields are `ε`-local exactly when their
`ε`-twisted commutator is a finite sum of `δ`-derivatives. -/
theorem localε_iff_deltaSum (ε : ℂ) (a b : FormalDist (Module.End ℂ V)) :
    Localε ε a b ↔ ∃ (N : ℕ) (c : Fin N → FormalDist (Module.End ℂ V)),
      bracketDistε ε a b = ∑ j : Fin N, deltaDeriv (j : ℕ) (c j) := by
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, (local_iff_deltaSum _ N).1 hN⟩
  · rintro ⟨N, c, hc⟩
    exact ⟨N, (local_iff_deltaSum _ N).2 ⟨c, hc⟩⟩

/-- A field pair whose `ε`-twisted commutator is a single `δ` (no derivatives) is `ε`-local
with `N = 1`.  This is the shape every free-field example takes. -/
theorem localε_of_bracketDistε_eq_delta {ε : ℂ} {a b c : FormalDist (Module.End ℂ V)}
    (h : bracketDistε ε a b = deltaDeriv 0 c) : Localε ε a b :=
  ⟨1, by rw [h]; exact mulBySubPow_succ_deltaDeriv 0 c⟩

/-! ### The free-field locality criterion

The canonical (anti)commutation relations in one statement.  Taking `ε = 1` gives the
bosonic CCR and `ε = -1` the fermionic CAR; in both cases the criterion is that the
`ε`-twisted commutator depends only on `m + n` through a `δ`.

**A finiteness remark.**  A nonzero `δ`-type commutator never has *finite support* in the
mode indices: `δ`-derivatives have infinite support along a diagonal (`localε_iff_deltaSum`).
This constrains the *mode support*, not the dimension of the underlying space; no statement
about finite-dimensional examples is proved or implied here.
-/

/-- **The free-field locality criterion.**  If the `ε`-twisted commutator of `a` and `b` is
`δ_{m+n+1,0}` times a fixed operator `S`, then `a` and `b` are `ε`-local with `N = 1`.

* `ε = 1`  — the canonical *commutation* relations (bosons);
* `ε = -1` — the canonical *anticommutation* relations (fermions). -/
theorem localε_of_car {ε : ℂ} {a b : FormalDist (Module.End ℂ V)} (S : Module.End ℂ V)
    (h : ∀ m n : ℤ, a m * b n - ε • (b n * a m) = if m + n + 1 = 0 then S else 0) :
    Localε ε a b := by
  refine localε_of_bracketDistε_eq_delta (c := fun k => if k = 0 then S else 0) ?_
  apply FormalDist₂.ext; intro m n
  change a m * b n - ε • (b n * a m)
      = (∏ i ∈ Finset.range 0, (-m - 1 - (i : ℤ))) • (if m + n + 1 + 0 = 0 then S else 0)
  rw [h m n]
  simp

/-- The fermionic case, spelled out: canonical **anti**commutation relations give locality
at `ε = -1`, the Koszul sign of two odd fields (`koszul 1 1 = -1`). -/
theorem localε_neg_one_of_anticomm {a b : FormalDist (Module.End ℂ V)}
    (S : Module.End ℂ V) (h : ∀ m n : ℤ, a m * b n + b n * a m = if m + n + 1 = 0 then S else 0) :
    Localε (-1) a b := by
  refine localε_of_car S fun m n => ?_
  rw [neg_smul, one_smul, sub_neg_eq_add]
  exact h m n

end Operators

end VOA
