/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent14

/-!
# The CORRECTED `A_n(𝒱)` ideal/algebra architecture (Dong–Li–Mason).

The predicates `LeftDescends`/`RightDescends`/`AnBimoduleInputs` rest on two FALSE/incomplete
specifications:

* **Bug A.**  `gen_mem` ranges over `g ∈ O W = O₀(𝒱)` (Zhu's n=0 ideal), asserting `O₀ *ₙ 𝒱 ⊆ Oₙ`.
  This is FALSE for `n ≥ 1` (free-boson counterexample, robust even against the enlarged `Oₙ` below).
* **Bug B.**  `On W n := span{circ W n a b}` (`ZhuVermaAn.lean:135`) omits the `(L(-1)+L(0))𝒱`
  generator family.  Per Dong–Li–Mason (J. Algebra 206 (1998), eq. 2.1),
  `O_n(V) = span{u ∘_n v} + {(L(-1)+L(0))u}`, and the second family is **a genuine, irreducible
  generator for `n ≥ 1`** (Addabbo–Barron prove this; engine-confirmed:
  `(L(-1)+L(0))(α(-1)𝟙) ∉ span{circ₁}`).  At `n = 0` it is redundant (`(L(-1)+L(0))u = u ∘₀ 𝟙 ∈ O(V)`).

This file introduces the **corrected** objects alongside the earlier ones and proves the
structural facts that are immediate.  The genuine remaining content — the absorption identity and
the level-matched left tower — is stated precisely (NOT `sorry`'d, NOT axiomatized) and proved in
later files.

## What is proved here (all engine-verified TRUE on the rank-1 free boson)
* `OnL 𝒱` — the `(L(-1)+L(0))𝒱` generator span; `OnFull 𝒱 n := On 𝒱 n ⊔ OnL 𝒱` — the corrected `O_n`.
* `On_le_OnFull`, `OnL_le_OnFull`, `circ_mem_OnFull`, `Pres_mem_OnFull`, `Lgen_mem_OnFull` — the
  containments and the two generator-family memberships in the corrected `O_n`.
* `AnIdeal 𝒱 n` — the corrected 2-sided-ideal hypothesis, both inclusions under the SINGLE product
  `leftProd = *ₙ` (Dong–Li–Mason Lemma 2.2): `Oₙ *ₙ 𝒱 ⊆ Oₙ` (left slot) and `𝒱 *ₙ Oₙ ⊆ Oₙ` (right slot).
  Holding `AnIdeal 𝒱 n` ⟹ `A_n(𝒱) = 𝒱/OnFull` is an associative algebra (the boss-approved corrected
  target, replacing the false `AnBimoduleInputs`).

## The precise targets (engine-verified TRUE, to be proved)
* **(ABS)** the Dong–Li–Mason absorption identity (engine-verified exact, n = 0,1,2):
  `leftProd W n ((L(-1)+L(0))u) v = (-1)^n · C(2n,n) · (2n+1) · circ W n u v`.
  ⟹ the `OnL`-generator case of `AnIdeal.left` is *immediate* (RHS `∈ On ⊆ OnFull`).
* **(L1∘)** the `circ`-generator case `leftProd W n (circ W n c d) b ∈ OnFull W n` — the level-matched
  LEFT mirror of the proven right chain `RightCircTowerEq` (`ZhuVermaAnDescent19/20/21`), with shift
  `2n+2` on BOTH sides (a clean mirror, NOT the depth-0-circle cross-assembly of `Descent22–26`).
* **(R1)** the right slot `𝒱 *ₙ Oₙ ⊆ Oₙ` — extend the proven `leftProd_On_mem_On` to the `OnL`
  generators (again via (ABS): `leftProd a ((L(-1)+L(0))c)` reduces to a `circ` product).

## References
Dong–Li–Mason, J. Algebra 206 (1998) 67–96 (`q-alg/9612010`); Dong–Jiang, Math. Z. 259 (2008) 799–826;
H. Li, `hep-th/9406211`; Frenkel–Zhu, Duke 66 (1992); Zhu, J. AMS 9 (1996); Gannon §5.3.2 Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The ABS core absorption identity (the genuine new content of (ABS), isolated & proved). -/

/-- **ABS core absorption identity** `m·C(m+n,n) = (m+n)·C(m+n-1,n)`.  This is exactly the
per-pole coefficient relation that, via the integration-by-parts reorganization of `leftProd`, makes
the Dong–Li–Mason absorption identity (ABS) collapse — the single-variable `T(p)=0` mechanism, with
no hypergeometric `j`-sum.  Proof: Pascal `C(m+n,n)=C(m+n-1,n)+C(m+n-1,n-1)` then the lower
absorption `m·C(m+n-1,n-1) = n·C(m+n-1,n)`. -/
theorem cbz_upper_shift (m n : ℕ) :
    (m : ℂ) * cbz ((m : ℤ) + n) n = ((m : ℤ) + n) * cbz ((m : ℤ) + n - 1) n := by
  rcases Nat.eq_zero_or_pos (m + n) with h0 | hpos
  · obtain ⟨rfl, rfl⟩ : m = 0 ∧ n = 0 := by omega
    norm_num
  · have hnat : (m : ℤ) + n - 1 = ((m + n - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hpos]; ring
    have hpascal : cbz ((m : ℤ) + n) n
        = cbz ((m : ℤ) + n - 1) n + cbz ((m : ℤ) + n - 1) ((n : ℤ) - 1) := by
      simpa using cbz_pascal ((m : ℤ) + n) n
    have habs : cbz ((m : ℤ) + n - 1) n * (n : ℂ)
        = cbz ((m : ℤ) + n - 1) ((n : ℤ) - 1) * (m : ℂ) := by
      have hca := cbz_absorption (m + n - 1) (n : ℤ)
      rw [← hnat] at hca
      push_cast [Nat.cast_sub hpos] at hca
      linear_combination hca
    rw [hpascal, mul_add]
    have hkey : (m : ℂ) * cbz ((m : ℤ) + n - 1) ((n : ℤ) - 1)
        = (n : ℂ) * cbz ((m : ℤ) + n - 1) n := by linear_combination -habs
    rw [hkey]; push_cast; ring

/-- **ABS integration-by-parts coefficient identity (★IBP).**  The per-`(ν,m)` coefficient of
`leftProd(L₋₁u,v) + M•leftProd(u,v)` equals the coefficient of the reorganized pole form
`m·R(n+m+1) + (n+m+1)·R(n+m+2)`, `R(p)=∑_i C(M+n,i) u₍ᵢ₋ₚ₎v`.  Reduces (after Pascal on `C(M+1+n,·)`)
to `cbz_absorption (M+n) (ν+n+m+2)` — the integration-by-parts step of (ABS), with no `j`-sum. -/
theorem abs_ibp_coeff (M n m : ℕ) (ν : ℤ) :
    -((ν : ℂ) + 1) * cbz ((M : ℤ) + 1 + n) (ν + n + m + 2)
        + (M : ℂ) * cbz ((M : ℤ) + n) (ν + n + m + 1)
      = (m : ℂ) * cbz ((M : ℤ) + n) (ν + n + m + 1)
        + ((n : ℂ) + m + 1) * cbz ((M : ℤ) + n) (ν + n + m + 2) := by
  have hp : cbz ((M : ℤ) + 1 + n) (ν + n + m + 2)
      = cbz ((M : ℤ) + n) (ν + n + m + 2) + cbz ((M : ℤ) + n) (ν + n + m + 1) := by
    have h := cbz_pascal_up ((M : ℤ) + n) (ν + n + m + 2)
    rw [show ((M : ℤ) + n + 1) = (M : ℤ) + 1 + n from by ring,
        show (ν + n + m + 2 - 1) = ν + n + m + 1 from by ring] at h
    exact h
  have ha : cbz ((M : ℤ) + n) (ν + n + m + 2) * (ν + (n : ℂ) + m + 2)
      = cbz ((M : ℤ) + n) (ν + n + m + 1) * ((M : ℂ) - ν - m - 1) := by
    have h := cbz_absorption (M + n) (ν + n + m + 2)
    rw [show (((M + n : ℕ) : ℤ)) = (M : ℤ) + n from by push_cast; ring,
        show (ν + (n : ℤ) + m + 2 - 1) = ν + n + m + 1 from by ring] at h
    push_cast at h
    linear_combination h
  linear_combination (norm := (push_cast; ring1)) (-((ν : ℂ) + 1)) * hp - ha

/-- **ABS per-mode scalar identity.**  The full `j`-sum coefficient of `u₍ν₎v` in
`leftProd W n ((L₋₁+L₀)u) v` collapses to that of `(-1)^n C(2n,n)(2n+1)•circ W n u v`.  Proof:
rewrite the per-`j` bracket via `abs_ibp_coeff` (integration by parts), then telescope with
`D j := (-1)^j·j·C(j+n,n)·C(M+n,ν+n+j+1)` — each summand `= D j - D(j+1)` by `cbz_upper_shift`,
so the sum is `D 0 - D(n+1) = -D(n+1)`, and `(n+1)C(2n+1,n) = (2n+1)C(2n,n)` (again
`cbz_upper_shift`) gives the result.  This is the entire combinatorial content of (ABS). -/
theorem abs_scalar (M n : ℕ) (ν : ℤ) :
    (∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j * cbz ((j : ℤ) + n) n *
        (-((ν : ℂ) + 1) * cbz ((M : ℤ) + 1 + n) (ν + n + j + 2)
          + (M : ℂ) * cbz ((M : ℤ) + n) (ν + n + j + 1)))
      = (-1 : ℂ) ^ n * cbz (2 * (n : ℤ)) n * (2 * (n : ℂ) + 1)
          * cbz ((M : ℤ) + n) (ν + 2 * n + 2) := by
  set D : ℕ → ℂ := fun j =>
    (-1 : ℂ) ^ j * (j : ℂ) * cbz ((j : ℤ) + n) n * cbz ((M : ℤ) + n) (ν + n + j + 1) with hD
  have hterm : ∀ j ∈ Finset.range (n + 1),
      (-1 : ℂ) ^ j * cbz ((j : ℤ) + n) n *
        (-((ν : ℂ) + 1) * cbz ((M : ℤ) + 1 + n) (ν + n + j + 2)
          + (M : ℂ) * cbz ((M : ℤ) + n) (ν + n + j + 1)) = D j - D (j + 1) := by
    intro j _
    rw [abs_ibp_coeff M n j ν]
    have hsh := cbz_upper_shift (j + 1) n
    rw [show (((j + 1 : ℕ) : ℤ)) = (j : ℤ) + 1 from by push_cast; ring] at hsh
    rw [show ((j : ℤ) + 1 + n - 1) = (j : ℤ) + n from by ring] at hsh
    simp only [hD]
    rw [show (((j + 1 : ℕ) : ℤ)) = (j : ℤ) + 1 from by push_cast; ring,
        show (ν + n + ((j : ℤ) + 1) + 1) = ν + n + j + 2 from by ring]
    linear_combination (norm := (push_cast [pow_succ]; ring1))
      (-((-1 : ℂ) ^ j * cbz ((M : ℤ) + n) (ν + n + j + 2))) * hsh
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub' D (n + 1)]
  have hsh := cbz_upper_shift (n + 1) n
  rw [show (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 from by push_cast; ring] at hsh
  rw [show ((n : ℤ) + 1 + n - 1) = 2 * (n : ℤ) from by ring] at hsh
  simp only [hD]
  rw [show (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 from by push_cast; ring,
      show (ν + n + ((n : ℤ) + 1) + 1) = ν + 2 * n + 2 from by ring]
  linear_combination (norm := (push_cast [pow_succ]; ring1))
    ((-1 : ℂ) ^ n * cbz ((M : ℤ) + n) (ν + 2 * n + 2)) * hsh

/-! ## The corrected `O_n(𝒱)` (Bug-B fix): add the `(L(-1)+L(0))𝒱` generator family. -/

/-- **`OnL 𝒱`** — the span of the Dong–Li–Mason `(L(-1)+L(0))𝒱` generator family (Zhu's `O(𝒱)`
generators `(L₋₁u+L₀u)`).  Same family for every level `n` — it is what `On W n` omits. -/
def OnL (W : VertexOperatorAlgebra 𝒱) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ a : 𝒱, x = W.L (-1) a + W.L 0 a}

/-- **`OnFull 𝒱 n`** — the CORRECTED `O_n(𝒱) = span{u ∘ₙ v} + {(L(-1)+L(0))u}` (Dong–Li–Mason
eq. 2.1).  At `n = 0` it equals `On W 0 = O(𝒱)` (the `OnL` generators are then `u ∘₀ 𝟙 ∈ O(𝒱)`);
for `n ≥ 1` it contains the circle-only `On W n` (strict containment is expected but **not
proved**). -/
def OnFull (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Submodule ℂ 𝒱 :=
  On W n ⊔ OnL W

@[simp] theorem On_le_OnFull (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : On W n ≤ OnFull W n :=
  le_sup_left

@[simp] theorem OnL_le_OnFull (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : OnL W ≤ OnFull W n :=
  le_sup_right

/-- Every `(L(-1)+L(0))a` lies in the `OnL` generator span. -/
theorem Lgen_mem_OnL (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) :
    W.L (-1) a + W.L 0 a ∈ OnL W :=
  Submodule.subset_span ⟨a, rfl⟩

/-- Circle products are in the corrected `O_n`. -/
theorem circ_mem_OnFull (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a b : 𝒱) :
    circ W n a b ∈ OnFull W n :=
  On_le_OnFull W n (circ_mem_On W n a b)

/-- The depth-`(n,d)` higher-pole residues are in the corrected `O_n` (keystone `Pres_mem_On`). -/
theorem Pres_mem_OnFull (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (M : ℤ)) (b : 𝒱) (d : ℕ) :
    PresOn W M n d a b ∈ OnFull W n :=
  On_le_OnFull W n (Pres_mem_On W n ha b d)

/-- The `(L(-1)+L(0))a` generators are in the corrected `O_n`. -/
theorem Lgen_mem_OnFull (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a : 𝒱) :
    W.L (-1) a + W.L 0 a ∈ OnFull W n :=
  OnL_le_OnFull W n (Lgen_mem_OnL W a)

/-! ## The corrected 2-sided-ideal hypothesis (replaces the false `AnBimoduleInputs`).

`A_n(𝒱) = 𝒱/O_n` is an associative algebra iff `O_n` is a 2-sided ideal under the SINGLE Frenkel–Zhu
product `*ₙ = leftProd` (Dong–Li–Mason Lemma 2.2 / Thm 2.3).  Both inclusions use `leftProd`: the
LEFT ideal is `g` in the first slot, the RIGHT ideal is `g` in the second slot.  (`rightProd`-based
fields are not used: `rightProd ≠ leftProd  (mod O_n)`, so `rightProd` is NOT the algebra's right
multiplication.) -/

/-- **The corrected `A_n(𝒱)`-ideal hypothesis.**  `OnFull 𝒱 n` is a 2-sided ideal under `leftProd`
(`= *ₙ`).  This is the boss-approved corrected target (Dong–Li–Mason Lemma 2.2), replacing the FALSE
`AnBimoduleInputs` (which used `O₀` in the acting slot and a `rightProd` field). -/
structure AnIdeal (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop where
  /-- **Left ideal** `Oₙ *ₙ 𝒱 ⊆ Oₙ`: `g` in the first (acting) slot, over the corrected `Oₙ`. -/
  left : ∀ g ∈ OnFull W n, ∀ b : 𝒱, leftProd W n g b ∈ OnFull W n
  /-- **Right ideal** `𝒱 *ₙ Oₙ ⊆ Oₙ`: `g` in the second slot ranges over the corrected `Oₙ`. -/
  right : ∀ a : 𝒱, ∀ g ∈ OnFull W n, leftProd W n a g ∈ OnFull W n

/-- The corrected left ideal, fed on circle/`OnL` generators, descends to `leftProd`-stability on
all of `OnFull` (left slot).  This `comap`/`span_le` wrapper reduces `AnIdeal.left` to its two
generator families — the genuine remaining content (ABS) + (L1∘). -/
theorem AnIdeal_left_of_gens (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hcirc : ∀ c d : 𝒱, ∀ b : 𝒱, leftProd W n (circ W n c d) b ∈ OnFull W n)
    (hL : ∀ a : 𝒱, ∀ b : 𝒱, leftProd W n (W.L (-1) a + W.L 0 a) b ∈ OnFull W n) :
    ∀ g ∈ OnFull W n, ∀ b : 𝒱, leftProd W n g b ∈ OnFull W n := by
  intro g hg b
  -- `OnFull = On ⊔ OnL`: split `g = y + z`; `leftProdFstL W n b` is ℂ-linear, so `comap`/`span_le`.
  rw [OnFull, Submodule.mem_sup] at hg
  obtain ⟨y, hy, z, hz, rfl⟩ := hg
  rw [leftProd_add_left]
  refine (OnFull W n).add_mem ?_ ?_
  · -- `y ∈ On W n = span{circ}`.
    have hle : On W n ≤ (OnFull W n).comap (leftProdFstL W n b) := by
      rw [On_eq_span, Submodule.span_le]
      rintro x ⟨c, d, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, leftProdFstL_apply]
      exact hcirc c d b
    have hx : y ∈ (OnFull W n).comap (leftProdFstL W n b) := hle hy
    rwa [Submodule.mem_comap, leftProdFstL_apply] at hx
  · -- `z ∈ OnL W = span{(L₋₁+L₀)a}`.
    have hle : OnL W ≤ (OnFull W n).comap (leftProdFstL W n b) := by
      rw [OnL, Submodule.span_le]
      rintro x ⟨a, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, leftProdFstL_apply]
      exact hL a b
    have hx : z ∈ (OnFull W n).comap (leftProdFstL W n b) := hle hz
    rwa [Submodule.mem_comap, leftProdFstL_apply] at hx

/-- The corrected right ideal, fed on circle/`OnL` generators, descends to `leftProd`-stability on
all of `OnFull` (right slot).  `comap`/`span_le` via the second-slot linear map `leftProdR W n a`. -/
theorem AnIdeal_right_of_gens (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hcirc : ∀ a c d : 𝒱, leftProd W n a (circ W n c d) ∈ OnFull W n)
    (hL : ∀ a c : 𝒱, leftProd W n a (W.L (-1) c + W.L 0 c) ∈ OnFull W n) :
    ∀ a : 𝒱, ∀ g ∈ OnFull W n, leftProd W n a g ∈ OnFull W n := by
  intro a g hg
  rw [OnFull, Submodule.mem_sup] at hg
  obtain ⟨y, hy, z, hz, rfl⟩ := hg
  rw [leftProd_add_right]
  refine (OnFull W n).add_mem ?_ ?_
  · have hle : On W n ≤ (OnFull W n).comap (leftProdR W n a) := by
      rw [On_eq_span, Submodule.span_le]
      rintro x ⟨c, d, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, leftProdR_apply]
      exact hcirc a c d
    have hx : y ∈ (OnFull W n).comap (leftProdR W n a) := hle hy
    rwa [Submodule.mem_comap, leftProdR_apply] at hx
  · have hle : OnL W ≤ (OnFull W n).comap (leftProdR W n a) := by
      rw [OnL, Submodule.span_le]
      rintro x ⟨c, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, leftProdR_apply]
      exact hL a c
    have hx : z ∈ (OnFull W n).comap (leftProdR W n a) := hle hz
    rwa [Submodule.mem_comap, leftProdR_apply] at hx

/-- **`hRcirc` is already proved.**  `leftProd W n a (circ W n c d) ∈ OnFull W n`: the second-slot
circle generator lands via the unconditional `leftProd_On_mem_On` (`𝒱 *ₙ Oₙ ⊆ Oₙ`, `ZhuVermaAnDescent4`),
then `On W n ⊆ OnFull W n`.  So the right-circle core needs no new work. -/
theorem leftProd_circ_right_mem_OnFull (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a c d : 𝒱) :
    leftProd W n a (circ W n c d) ∈ OnFull W n :=
  On_le_OnFull W n (leftProd_On_mem_On W n a (circ W n c d) (circ_mem_On W n c d))

/-- **`AnIdeal` from the four generator-family memberships.**  The corrected 2-sided ideal reduces to
exactly: the left/right `leftProd` of a `circ W n` generator (the **L1∘** tower, left-mirror of the
proven `RightCircTowerEq`), and the left/right `leftProd` of an `(L₋₁+L₀)` generator (immediate from
the **(ABS)** absorption identity).  This is the complete wiring; only these four memberships remain. -/
theorem AnIdeal_of_gens (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hLcirc : ∀ c d b : 𝒱, leftProd W n (circ W n c d) b ∈ OnFull W n)
    (hLgen : ∀ c b : 𝒱, leftProd W n (W.L (-1) c + W.L 0 c) b ∈ OnFull W n)
    (hRcirc : ∀ a c d : 𝒱, leftProd W n a (circ W n c d) ∈ OnFull W n)
    (hRgen : ∀ a c : 𝒱, leftProd W n a (W.L (-1) c + W.L 0 c) ∈ OnFull W n) :
    AnIdeal W n where
  left := AnIdeal_left_of_gens W n hLcirc hLgen
  right := AnIdeal_right_of_gens W n hRcirc hRgen

/-!
## Summary: the corrected ideal architecture, and the reduction to three cores + `M(U)`

Proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`):
corrected `OnFull`/`OnL`; `circ_mem_OnFull`/`Pres_mem_OnFull`/`Lgen_mem_OnFull`; the `AnIdeal`
structure; `AnIdeal_left_of_gens`/`AnIdeal_right_of_gens` (`comap`/`span_le` reductions of each ideal
side to its `circ`/`OnL` families); `AnIdeal_of_gens` (`AnIdeal` from the FOUR generator memberships);
and `leftProd_circ_right_mem_OnFull` — the `hRcirc` core discharged (via `leftProd_On_mem_On`).

So `AnIdeal 𝒱 n` reduces to exactly THREE memberships (all engine-verified TRUE; NONE faked):
* **(ABS)** `leftProd W n ((L₋₁+L₀)a) b = (-1)^n · cbz (2n) n · (2n+1) • circ W n a b`  ⟹ `hLgen`.
  Crux = the scalar identity (verified exact, n=0..3, all M,μ; a finite alternating `cbz` `j`-sum):
  `∑_{j=0}^{n} (-1)^j C(j+n,n)·[-(μ+1)·C(M+1+n,μ+n+j+2)+M·C(M+n,μ+n+j+1)] = (-1)^n C(2n,n)(2n+1)·C(M+n,μ+2n+2)`.
* **(hRgen)** `leftProd W n a ((L₋₁+L₀)c) ∈ OnFull W n`  (`𝒱 *ₙ O^L ⊆ Oₙ`, right slot).
* **(L1∘=hLcirc)** `leftProd W n (circ W n c d) b ∈ OnFull W n` — the level-matched LEFT tower, mirror
  of the proven right chain `RightCircTowerEq` (`ZhuVermaAnDescent19/20/21`), shift `2n+2` BOTH sides.

The later steps: `A_n(𝒱)=𝒱/OnFull` associative (DLM3 Thm 2.3); surjection `A_n ↠ A_0`
(`OnFull W n ⊆ OnFull W 0`); `M(U)` via DLM3 **Construction A** (pull `U` back along `V̂(0) ↠ A_n(𝒱)`,
PBW-induce over `U(P_n)`, quotient by associativity defects — a substantial new development); the
irreducible quotient `L(U)`; and the bijection `Φ(𝒱) ↔ Irr A(𝒱)` (Thm 5.3.4) via the universal property.
-/

end VOA
