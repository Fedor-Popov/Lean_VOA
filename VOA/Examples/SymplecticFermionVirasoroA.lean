/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.SymplecticFermionY
import VOA.Examples.SymplecticFermionGrading
import VOA.Examples.HeisenbergCentral

/-!
# The symplectic-fermion conformal vector and the Virasoro algebra at `c = -2`

The library's first **super** Virasoro computation.  Everything here is about the single state

`ωSF = -χ⁰₋₁χ¹₋₁|0⟩`

and the field `Y(ωSF, z)` it generates.

## Deriving the normalisation (it is not guessed)

`χᵃ` has conformal weight `1`, so `ω` sits at weight `2` and is a multiple `κ·χ⁰₋₁χ¹₋₁|0⟩`; the
symplectic form fixes which pair of species appears, and `κ` is fixed by *demanding* that `χᵃ` be
a weight-one primary.  From the contraction `χᵃ(z)χᵇ(w) ~ ωᵃᵇ/(z-w)²` implied by `chi_anticomm`,
Wick's theorem for two odd fields gives

`:χ⁰χ¹:(z) χᶜ(w) ~ [ω¹ᶜ χ⁰(z) - ω⁰ᶜ χ¹(z)]/(z-w)² = -χᶜ(z)/(z-w)²`

for **both** `c = 0` and `c = 1` (the two cases use the two different entries of `ω`, and the
antisymmetry of `ω` is what makes them agree).  Comparing with the primary OPE
`T(z)φ(w) ~ h·φ(w)/(z-w)² + ∂φ(w)/(z-w)` at `h = 1` forces `κ = -1`, i.e.

`L(z) = -:χ⁰(z)χ¹(z):`,   `ωSF = L₋₂|0⟩ = -χ⁰₋₁χ¹₋₁|0⟩`.

With that normalisation `L₂ωSF = -|0⟩`, and `L₂ω = (c/2)|0⟩` gives `c = -2`.  Both statements are
proved below (`LSF_two_omega`, and the full relation `LSF_virasoro`), so the `-2` is a *result*,
never an input.

## The route

Modes rather than fields.  `chiM a p := chi a (-p-1)` is the honest mode `χᵃ_p`, and in that
indexing the anticommutator (`chiM_anticomm`) is the clean `{χᵃ_p, χᵇ_q} = p·δ_{p+q,0}·ωᵃᵇ`.  The
Virasoro modes are the normal-ordered bilinears

`Lₙ = -∑ⱼ :χ⁰_j χ¹_{n-j}:`,  `:χ⁰_jχ¹_{n-j}: = χ⁰_jχ¹_{n-j}` for `j < 0`, `= -χ¹_{n-j}χ⁰_j` else,

and `LSF_eq_mode` identifies them with `mode (YSF ωSF) (n+1)`, so nothing here is a *different*
Virasoro from the vertex-algebra one.

The two computations are then:

* **`LSF_comm_chiM`** — `[Lₘ, χᶜ_p] = -p·χᶜ_{m+p}`, weight-one primarity.  A single per-term
  identity `sfTerm_bracket_chiM` (which comes out *the same* in both branches of the normal
  ordering, because the anticommutators are scalars) plus a two-point finsum collapse.
* **`LSF_virasoro`** — the full relation.  This mirrors, step for step, the free-boson
  computation in `Examples/HeisenbergCentral.lean`: split the per-term bracket into an
  `F`-family and a `G`-family, reindex `F` by `i = m + j` — which changes the normal-ordering
  **gate** from `j < 0` to `i < m` — and collect the mismatch.  The mismatch is one
  anticommutator per lattice point of the finite window between the two gates, i.e. a scalar,
  and it resums to `(m³-m)/6`.  With the overall sign of `L = -:χ⁰χ¹:` that is
  `(m³-m)/12 · (-2)`.

## What the Koszul signs do (and do not) cost

Nothing, in the end.  `Lₘ` is **even**, so `[Lₘ, ·]` is an ordinary derivation on products of odd
operators, and the two branches of the normal ordering give the same formula.  The odd/odd signs
are entirely absorbed into the definition of `sfTerm` (the explicit `-` on the `j ≥ 0` branch)
and into `chiM_anticomm` being an *anti*commutator.  This is why the free-boson template transfers
essentially verbatim, with `k = 1` and one global sign.
-/

namespace VOA.SympFerm

open CliffordAlgebra
open Module (End)
open VOA.Reconstruction

/-! ## §0  The modes `χᵃ_p` and the canonical anticommutation relations

`FormalDist` is indexed by the `z`-exponent, so `chi a j = χᵃ_{-j-1}`.  Every computation below
is about honest modes, so we give them their own name and restate the CAR in mode indexing —
where the awkward `(-j-1)` factor of `chi_anticomm` becomes simply the mode number. -/

/-- **The mode `χᵃ_p`.**  The `z`-exponent index `j` and the mode index `p` are related by
`j = -p-1`, so this is just `chi` read in the other indexing. -/
noncomputable def chiM (a : Fin 2) (p : ℤ) : End ℂ FockSF := chi a (-p - 1)

theorem chiM_def (a : Fin 2) (p : ℤ) : chiM a p = chi a (-p - 1) := rfl

theorem chi_eq_chiM (a : Fin 2) (j : ℤ) : chi a j = chiM a (-j - 1) := by
  rw [chiM_def, show -(-j - 1) - 1 = j from by ring]

/-- The scalar in `{χᵃ_p, χᵇ_q}`: the mode number times the symplectic form, gated on `p+q = 0`. -/
noncomputable def carC (a b : Fin 2) (p q : ℤ) : ℂ :=
  if p + q = 0 then (p : ℂ) * sfOmega a b else 0

theorem carC_apply (a b : Fin 2) (p q : ℤ) :
    carC a b p q = if p + q = 0 then (p : ℂ) * sfOmega a b else 0 := rfl

/-- **The CAR in mode indexing**: `{χᵃ_p, χᵇ_q} = p·δ_{p+q,0}·ωᵃᵇ`.  This is `chi_anticomm`
with the index flip performed; the point is that the coefficient is now literally the mode
number `p`, which is what every counting argument below uses. -/
theorem chiM_anticomm (a b : Fin 2) (p q : ℤ) :
    chiM a p * chiM b q + chiM b q * chiM a p = carC a b p q • (1 : End ℂ FockSF) := by
  rw [chiM_def, chiM_def, chi_anticomm, carC_apply]
  congr 1
  by_cases h : p + q = 0
  · rw [if_pos h, if_pos (show (-p - 1) + (-q - 1) + 2 = 0 from by omega),
      show (-(-p - 1) - 1 : ℤ) = p from by ring]
  · rw [if_neg h, if_neg (show ¬ ((-p - 1) + (-q - 1) + 2 = 0) from by omega)]

/-- The CAR applied to a vector. -/
theorem chiM_anticomm_apply (a b : Fin 2) (p q : ℤ) (x : FockSF) :
    chiM a p (chiM b q x) + chiM b q (chiM a p x) = carC a b p q • x := by
  have h := congrArg (fun (S : End ℂ FockSF) => S x) (chiM_anticomm a b p q)
  simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply] using h

/-- Moving one mode past another: the form used in every commutator computation. -/
theorem chiM_swap (a b : Fin 2) (p q : ℤ) (x : FockSF) :
    chiM a p (chiM b q x) = -(chiM b q (chiM a p x)) + carC a b p q • x := by
  rw [← chiM_anticomm_apply a b p q x]; abel

/-- Positive modes (and the zero mode) annihilate the vacuum. -/
theorem chiM_vacuum (a : Fin 2) {p : ℤ} (hp : 0 ≤ p) : chiM a p vacSF = 0 :=
  chi_neg_vac a (-p - 1) (by omega)

/-- The creation modes are the Clifford generators: `χᵃ_{-k-1}|·⟩ = ι(single (k,a) 1)·(·)`. -/
theorem chiM_eq_creBase (a : Fin 2) (k : ℕ) : chiM a (-(k : ℤ) - 1) = creBase (k, a) := by
  rw [chiM_def, show -(-(k : ℤ) - 1) - 1 = (k : ℤ) from by ring, chi,
    if_pos (by positivity : (0 : ℤ) ≤ (k : ℤ))]
  change creBase ((k : ℤ).toNat, a) = creBase (k, a)
  rw [Int.toNat_natCast]

/-! ## §1  The Virasoro field, its modes, and the mode formula

`L(z) = -:χ⁰(z)χ¹(z):`.  The normal-ordered product is the repo's `nprodε` at the Koszul sign
`ε = koszul 1 1 = -1`, so `L` is literally the word field of `[(0,0),(0,1)]` up to the sign — a
fact recorded in §2.  Here we only extract the mode formula. -/

/-- The bare normal-ordered product `:χ⁰(z)χ¹(z):`, at the odd/odd Koszul sign. -/
noncomputable def sfNPField : FormalDist (End ℂ FockSF) :=
  nprodε (-1) (chi_isField 0) (chi_isField 1)

/-- **The Virasoro modes** `Lₙ = -∑ⱼ :χ⁰_jχ¹_{n-j}:`.  The `z`-exponent of `Lₙ` is `-n-2`
because `L` has conformal weight `2`. -/
noncomputable def LSF (n : ℤ) : End ℂ FockSF := -(sfNPField (-n - 2))

theorem LSF_def (n : ℤ) : LSF n = -(sfNPField (-n - 2)) := rfl

/-- The single normal-ordered pair `:χ⁰_j χ¹_{n-j}:`.  The explicit `-` on the `j ≥ 0` branch is
the Koszul sign of two odd fields — it is what makes the difference `S - S̃` in §5 an
*anti*commutator, hence a scalar. -/
noncomputable def sfTerm (n j : ℤ) : End ℂ FockSF :=
  if j < 0 then chiM 0 j * chiM 1 (n - j) else -(chiM 1 (n - j) * chiM 0 j)

theorem sfTerm_apply (n j : ℤ) (x : FockSF) :
    sfTerm n j x
      = if j < 0 then chiM 0 j (chiM 1 (n - j) x) else -(chiM 1 (n - j) (chiM 0 j x)) := by
  rw [sfTerm]
  by_cases h : j < 0
  · rw [if_pos h, if_pos h, Module.End.mul_apply]
  · rw [if_neg h, if_neg h, LinearMap.neg_apply, Module.End.mul_apply]

/-- The index flip `j ↦ -j-1` between the mode index of `χ⁰` and the `z`-exponent index that
`nprodε` sums over. -/
def sfFlip : ℤ ≃ ℤ where
  toFun j := -j - 1
  invFun j := -j - 1
  left_inv j := by dsimp only; ring
  right_inv j := by dsimp only; ring

@[simp] theorem sfFlip_apply (j : ℤ) : sfFlip j = -j - 1 := rfl

/-- The summand of `nprodε` at `z`-exponent `-n-2`, reindexed to the mode picture, **is**
`sfTerm`.  Both the gate (`0 ≤ -j-1 ↔ j < 0`) and the second index (`χ¹_{n-j}`) match. -/
theorem normalOrderedε_eq_sfTerm (n j : ℤ) :
    normalOrderedε (-1) (chi 0) (chi 1) (-j - 1) ((-n - 2) - (-j - 1)) = sfTerm n j := by
  rw [normalOrderedε_apply, sfTerm, show (-n - 2) - (-j - 1) = -(n - j) - 1 from by ring,
    ← chiM_def, ← chiM_def]
  by_cases h : j < 0
  · rw [if_pos (show (0 : ℤ) ≤ -j - 1 from by omega), if_pos h]
  · rw [if_neg (show ¬ ((0 : ℤ) ≤ -j - 1) from by omega), if_neg h, neg_one_smul]

/-- The mode-picture family has finite support: transported from the `nprodε` diagonal. -/
theorem sfTerm_support_finite (n : ℤ) (x : FockSF) :
    (Function.support (fun j : ℤ => sfTerm n j x)).Finite := by
  have h := normalOrderedε_diag_support_finite (-1) (chi_isField 0) (chi_isField 1) (-n - 2) x
  refine Set.Finite.subset (h.image (fun m => -m - 1)) ?_
  intro j hj
  rw [Function.mem_support] at hj
  exact ⟨-j - 1, by rw [Function.mem_support, normalOrderedε_eq_sfTerm]; exact hj,
    (by omega : -(-j - 1) - 1 = j)⟩

/-- **The mode formula** `Lₙ = -∑ⱼ :χ⁰_jχ¹_{n-j}:`, the form every computation below uses. -/
theorem LSF_apply (n : ℤ) (x : FockSF) : LSF n x = -∑ᶠ j : ℤ, sfTerm n j x := by
  rw [LSF_def, LinearMap.neg_apply, sfNPField, nprodε_apply, ← finsum_comp_equiv sfFlip]
  congr 1
  exact finsum_congr fun j => by rw [sfFlip_apply, normalOrderedε_eq_sfTerm]

/-- `Lₙ` distributes over the (finite) family: the form needed to push `Lₙ` inside a sum. -/
theorem LSF_of_finsum {f : ℤ → FockSF} (n : ℤ) (hf : (Function.support f).Finite) :
    LSF n (∑ᶠ j : ℤ, f j) = ∑ᶠ j : ℤ, LSF n (f j) :=
  map_finsum (LSF n).toAddMonoidHom hf

/-! ## §2  The conformal vector, and `Y(ωSF, z)` is the Virasoro field

The plumbing that makes `LSF` the vertex-algebra Virasoro rather than a private construction.
`YwordSF [(0,0),(0,1)]` unfolds to exactly `sfNPField`, once the length-one word is collapsed
(`nprodε` at `ε = 1` against `idField` is the identity operation on fields). -/

section Plumbing

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- `nprodε` depends on its field arguments only through their values, not through the
`IsField` witnesses (which are proof-irrelevant). -/
theorem nprodε_congr' (ε : ℂ) {a b a' b' : FormalDist (End ℂ V)}
    (ha : IsField a) (hb : IsField b) (ha' : IsField a') (hb' : IsField b')
    (h1 : a = a') (h2 : b = b') : nprodε ε ha hb = nprodε ε ha' hb' := by
  subst h1; subst h2; rfl

/-- At `ε = 1` the super normal-ordered product is the bosonic one. -/
theorem nprodε_one' {a b : FormalDist (End ℂ V)} (ha : IsField a) (hb : IsField b) :
    nprodε (1 : ℂ) ha hb = nprod ha hb := by
  refine FormalDist.ext fun s => LinearMap.ext fun x => ?_
  rw [nprodε_apply, nprod_apply]
  exact finsum_congr fun m => by rw [normalOrderedε_one]

end Plumbing

/-- The undifferentiated generator field is just `χᵃ`. -/
theorem sfGenField_zero_eq (a : Fin 2) : sfGenField a 0 = chi a := by
  rw [sfGenField]
  simp

/-- A length-one word field is the corresponding generator field: normal ordering against
`idField` (at Koszul sign `1`, since the empty word is even) does nothing. -/
theorem YwordSF_singleton (p : ℕ × Fin 2) : YwordSF [p] = sfGenField p.2 p.1 := by
  rw [YwordSF_cons]
  have h0 : koszul 1 ((([] : SFWord).length : ℕ) : ZMod 2) = 1 := by simp
  rw [h0, nprodε_one']
  exact nprod_idField _

/-- **The conformal vector** `ωSF = -χ⁰₋₁χ¹₋₁|0⟩`.  The sign is forced by weight-one
primarity of `χᵃ`; see the module docstring. -/
noncomputable def ωSF : FockSF := -(stWordSF [(0, 0), (0, 1)])

/-- The word field of `[(0,0),(0,1)]` **is** `:χ⁰χ¹:`: the outer product is at Koszul sign
`koszul 1 1 = -1`, and the two factors collapse to the undifferentiated generators. -/
theorem YwordSF_conformal :
    YwordSF [((0 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))] = sfNPField := by
  rw [YwordSF_cons]
  have h1 : koszul 1 ((([((0 : ℕ), (1 : Fin 2))] : SFWord).length : ℕ) : ZMod 2) = -1 := by
    simp
  rw [h1, sfNPField]
  exact nprodε_congr' _ _ _ _ _ (sfGenField_zero_eq 0)
    (by rw [YwordSF_singleton]; exact sfGenField_zero_eq 1)

/-- **`Y(ωSF, z)` is the Virasoro field** `-:χ⁰(z)χ¹(z):`. -/
theorem YSF_omega (s : ℤ) : YSF ωSF s = -(sfNPField s) := by
  rw [ωSF, map_neg, YSF_word, YwordSF_conformal]
  rfl

/-- **`LSF` is the vertex-algebra Virasoro**: `Lₙ = ω₍ₙ₊₁₎`, the mode convention of
`SuperVertexOperatorAlgebra.L`. -/
theorem LSF_eq_mode (n : ℤ) : LSF n = mode (YSF ωSF) (n + 1) := by
  rw [mode, show -(n + 1) - 1 = -n - 2 from by ring, YSF_omega, LSF_def]


/-! ## §3  Weight-one primarity: `[Lₘ, χᶜ_p] = -p·χᶜ_{m+p}`

The one genuinely super computation.  `Lₘ` is a sum of products of **two** odd operators, hence
even, so `[Lₘ, ·]` is an ordinary commutator; but each individual factor must be moved past `χᶜ`
with an *anti*commutator.  The two branches of the normal ordering are handled by the same
algebra and produce literally the same right-hand side (`sfTerm_bracket_chiM`) — the Koszul sign in
the `j ≥ 0` branch cancels against the extra transposition needed there. -/

/-- Every element of `Fin 2` is `0` or `1`, in the form the rewriting below wants. -/
theorem sfFin2_cases (c : Fin 2) : c = 0 ∨ c = 1 := by revert c; decide

@[simp] theorem sfOmega_zero_one : sfOmega 0 1 = 1 := by
  norm_num [sfOmega, sfSign, show ((0 : Fin 2) + 1 = 1) from rfl]

@[simp] theorem sfOmega_one_zero : sfOmega 1 0 = -1 := by
  norm_num [sfOmega, sfSign, show ((1 : Fin 2) + 1 = 0) from rfl]

theorem carC_eq_zero_of_ne (a b : Fin 2) {p q : ℤ} (h : p + q ≠ 0) : carC a b p q = 0 := by
  rw [carC_apply, if_neg h]

/-- **The per-term bracket** `[:χ⁰_jχ¹_{n-j}:, χᶜ_r]`.  Both anticommutators are scalars, so
the answer is a two-term combination of *single* modes — and it is the **same** formula on both
sides of the normal-ordering gate. -/
theorem sfTerm_bracket_chiM (n j : ℤ) (c : Fin 2) (r : ℤ) (x : FockSF) :
    sfTerm n j (chiM c r x) - chiM c r (sfTerm n j x)
      = carC 1 c (n - j) r • chiM 0 j x - carC 0 c j r • chiM 1 (n - j) x := by
  rw [sfTerm_apply, sfTerm_apply]
  by_cases h : j < 0
  · rw [if_pos h, if_pos h, chiM_swap 1 c (n - j) r x]
    simp only [map_add, map_neg, map_smul]
    rw [chiM_swap 0 c j r (chiM 1 (n - j) x)]
    abel
  · rw [if_neg h, if_neg h, chiM_swap 0 c j r x]
    simp only [map_add, map_neg, map_smul]
    rw [chiM_swap 1 c (n - j) r (chiM 0 j x)]
    abel

/-- Applying an operator preserves the finiteness of the per-term family. -/
theorem sfTerm_map_support_finite (n : ℤ) (S : End ℂ FockSF) (x : FockSF) :
    (Function.support (fun j : ℤ => S (sfTerm n j x))).Finite := by
  refine Set.Finite.subset (sfTerm_support_finite n x) ?_
  intro j hj
  rw [Function.mem_support] at hj ⊢
  exact fun h => hj (by rw [h, map_zero])

/-- The resummed per-term brackets.  Each of the two families is supported at a **single**
lattice point (`j = n+r` and `j = -r` respectively), and the two contributions combine, via the
antisymmetry of `ω`, into the same expression `r·χᶜ_{n+r}` for either species `c`. -/
theorem sfTerm_sum_bracket_chiM (n : ℤ) (c : Fin 2) (r : ℤ) (x : FockSF) :
    (∑ᶠ j : ℤ, (sfTerm n j (chiM c r x) - chiM c r (sfTerm n j x)))
      = (r : ℂ) • chiM c (n + r) x := by
  have hf : (Function.support (fun j : ℤ => carC 1 c (n - j) r • chiM 0 j x)).Finite := by
    refine Set.Finite.subset (Set.finite_singleton (n + r)) ?_
    intro j hj
    rw [Function.mem_support] at hj
    rw [Set.mem_singleton_iff]
    by_contra hne
    exact hj (by rw [carC_eq_zero_of_ne 1 c (show n - j + r ≠ 0 from by omega), zero_smul])
  have hg : (Function.support (fun j : ℤ => carC 0 c j r • chiM 1 (n - j) x)).Finite := by
    refine Set.Finite.subset (Set.finite_singleton (-r)) ?_
    intro j hj
    rw [Function.mem_support] at hj
    rw [Set.mem_singleton_iff]
    by_contra hne
    exact hj (by rw [carC_eq_zero_of_ne 0 c (show j + r ≠ 0 from by omega), zero_smul])
  rw [show (∑ᶠ j : ℤ, (sfTerm n j (chiM c r x) - chiM c r (sfTerm n j x)))
        = ∑ᶠ j : ℤ, (carC 1 c (n - j) r • chiM 0 j x - carC 0 c j r • chiM 1 (n - j) x) from
      finsum_congr fun j => sfTerm_bracket_chiM n j c r x,
    finsum_sub_distrib hf hg,
    finsum_eq_single (fun j : ℤ => carC 1 c (n - j) r • chiM 0 j x) (n + r)
      (fun j hj => by
        change carC 1 c (n - j) r • chiM 0 j x = 0
        rw [carC_eq_zero_of_ne 1 c (show n - j + r ≠ 0 from by omega), zero_smul]),
    finsum_eq_single (fun j : ℤ => carC 0 c j r • chiM 1 (n - j) x) (-r)
      (fun j hj => by
        change carC 0 c j r • chiM 1 (n - j) x = 0
        rw [carC_eq_zero_of_ne 0 c (show j + r ≠ 0 from by omega), zero_smul]),
    show n - (n + r) = -r from by ring, show n - -r = n + r from by ring,
    carC_apply, carC_apply, if_pos (show -r + r = 0 from by ring),
    if_pos (show -r + r = 0 from by ring)]
  rcases sfFin2_cases c with rfl | rfl
  · rw [sfOmega_one_zero, sfOmega_same]
    push_cast
    module
  · rw [sfOmega_same, sfOmega_zero_one]
    push_cast
    module

/-- **`χᵃ` is a weight-one primary**: `[Lₘ, χᶜ_p] = -p·χᶜ_{m+p}`.

This single relation carries all of §4: at `m = -1` it *is* the defining property of the
translation operator `T`, and at `m = 0` it *is* the statement that `χᶜ_{-k-1}` raises the
conformal weight by `k+1`. -/
theorem LSF_comm_chiM (n : ℤ) (c : Fin 2) (r : ℤ) :
    LSF n * chiM c r - chiM c r * LSF n = (-(r : ℂ)) • chiM c (n + r) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LSF_apply, LSF_apply, map_neg, map_finsum (chiM c r) (sfTerm_support_finite n x),
    show (-∑ᶠ j : ℤ, sfTerm n j (chiM c r x)) - -(∑ᶠ j : ℤ, chiM c r (sfTerm n j x))
        = -((∑ᶠ j : ℤ, sfTerm n j (chiM c r x)) - ∑ᶠ j : ℤ, chiM c r (sfTerm n j x)) from by abel,
    ← finsum_sub_distrib (sfTerm_support_finite n (chiM c r x))
      (sfTerm_map_support_finite n (chiM c r) x),
    sfTerm_sum_bracket_chiM, neg_smul]

/-- The vector form of `LSF_comm_chiM`. -/
theorem LSF_comm_chiM_apply (n : ℤ) (c : Fin 2) (r : ℤ) (x : FockSF) :
    LSF n (chiM c r x) - chiM c r (LSF n x) = (-(r : ℂ)) • chiM c (n + r) x := by
  have h := congrArg (fun (S : End ℂ FockSF) => S x) (LSF_comm_chiM n c r)
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] using h

/-! ## §4  `L₋₁ = T` and `L₀` is the weight operator

Both are operator identities on a Fock space with no basis in sight, so both are proved the same
way: an operator is determined by its value on the vacuum together with its commutators with the
creation operators, because the creation monomials span (`stWordSF_span`). -/

/-- `creBase` is the cons operation on word states. -/
theorem creBase_stWordSF (p : ℕ × Fin 2) (rest : SFWord) :
    creBase p (stWordSF rest) = stWordSF (p :: rest) := by
  rw [stWordSF_cons, creBase]
  rfl

/-- **A rigidity lemma**: an operator on `FockSF` is pinned down by its value on the vacuum
and its commutators with the creation operators.  The proof is an induction on words followed by
`stWordSF_span`; it is stated once because §4 uses it twice. -/
theorem eq_of_vac_of_creBase {A B : End ℂ FockSF} (hvac : A vacSF = B vacSF)
    (hcre : ∀ (p : ℕ × Fin 2) (y : FockSF),
      A (creBase p y) - creBase p (A y) = B (creBase p y) - creBase p (B y)) : A = B := by
  have hword : ∀ l : SFWord, A (stWordSF l) = B (stWordSF l) := by
    intro l
    induction l with
    | nil => rw [stWordSF_nil]; exact hvac
    | cons p rest ih =>
        rw [← creBase_stWordSF]
        have h := hcre p (stWordSF rest)
        have hA : A (creBase p (stWordSF rest))
            = creBase p (A (stWordSF rest))
              + (B (creBase p (stWordSF rest)) - creBase p (B (stWordSF rest))) := by
          rw [← h]; abel
        rw [hA, ih]
        abel
  refine LinearMap.ext_on stWordSF_span ?_
  rintro _ ⟨l, rfl⟩
  exact hword l

/-- Every term of `Lₙ` kills the vacuum once `n ≥ -1`: one of the two factors is a nonnegative
mode. -/
theorem sfTerm_vacuum {n : ℤ} (hn : -1 ≤ n) (j : ℤ) : sfTerm n j vacSF = 0 := by
  rw [sfTerm_apply]
  by_cases h : j < 0
  · rw [if_pos h, chiM_vacuum 1 (show (0 : ℤ) ≤ n - j from by omega), map_zero]
  · rw [if_neg h, chiM_vacuum 0 (show (0 : ℤ) ≤ j from by omega), map_zero, neg_zero]

/-- `Lₙ|0⟩ = 0` for `n ≥ -1`: the vacuum is `SL(2)`-invariant. -/
theorem LSF_vacuum {n : ℤ} (hn : -1 ≤ n) : LSF n vacSF = 0 := by
  rw [LSF_apply, show (∑ᶠ j : ℤ, sfTerm n j vacSF) = ∑ᶠ _j : ℤ, (0 : FockSF) from
    finsum_congr fun j => sfTerm_vacuum hn j, finsum_zero, neg_zero]

/-- The lowest creation mode, in the form `chiM_eq_creBase` cannot state directly. -/
theorem chiM_neg_one (a : Fin 2) : chiM a (-1) = creBase (0, a) := by
  have h := chiM_eq_creBase a 0
  rwa [show -((0 : ℕ) : ℤ) - 1 = -1 from by norm_num] at h

/-- **`ωSF = L₋₂|0⟩`**, so `ωSF` really is the state the Virasoro field creates.  Only the
`j = -1` term survives: for `j ≤ -2` the right factor `χ¹_{-2-j}` is a nonnegative mode, and for
`j ≥ 0` the right factor `χ⁰_j` is. -/
theorem LSF_neg_two_vacuum : LSF (-2) vacSF = ωSF := by
  rw [LSF_apply, ωSF]
  congr 1
  rw [finsum_eq_single _ (-1) (fun j hj => by
    rw [sfTerm_apply]
    by_cases h : j < 0
    · rw [if_pos h, chiM_vacuum 1 (show (0 : ℤ) ≤ -2 - j from by omega), map_zero]
    · rw [if_neg h, chiM_vacuum 0 (show (0 : ℤ) ≤ j from by omega), map_zero, neg_zero]),
    sfTerm_apply, if_pos (show (-1 : ℤ) < 0 from by norm_num),
    show (-2 : ℤ) - -1 = -1 from by ring, chiM_neg_one, chiM_neg_one]
  change creBase (0, (0 : Fin 2)) (creBase (0, (1 : Fin 2)) (stWordSF [])) = _
  rw [creBase_stWordSF, creBase_stWordSF]

/-- **`L₋₁ = T`**: the Virasoro mode `L₋₁` is the translation operator that
`reconstructε` was fed.  Weight-one primarity at `m = -1` is exactly `T_creBase`. -/
theorem LSF_neg_one_eq_T : LSF (-1) = T := by
  refine eq_of_vac_of_creBase (by rw [LSF_vacuum le_rfl, T_one]) (fun p y => ?_)
  have hX : chiM p.2 (-(p.1 : ℤ) - 1) = creBase p := chiM_eq_creBase p.2 p.1
  have hL : LSF (-1) * creBase p - creBase p * LSF (-1)
      = ((p.1 : ℂ) + 1) • creBase (p.1 + 1, p.2) := by
    rw [← hX, LSF_comm_chiM,
      show (-1 : ℤ) + (-(p.1 : ℤ) - 1) = -((p.1 + 1 : ℕ) : ℤ) - 1 from by push_cast; ring,
      chiM_eq_creBase]
    congr 1
    push_cast
    ring
  have key : LSF (-1) * creBase p - creBase p * LSF (-1) = T * creBase p - creBase p * T := by
    rw [hL, T_creBase]
  have h := congrArg (fun (S : End ℂ FockSF) => S y) key
  simpa only [LinearMap.sub_apply, Module.End.mul_apply] using h

/-- **`L₀` is the conformal weight operator** built in `SymplecticFermionGrading`.  The two
constructions are completely different — `L₀` here is a normal-ordered bilinear in the modes,
there it is the `ε`-component of a dual-number algebra map — and they agree because both are
determined by `[·, χᵃ_{-k-1}] = (k+1)χᵃ_{-k-1}` and killing the vacuum. -/
theorem LSF_zero_eq_L0SF : LSF 0 = L0SF := by
  refine eq_of_vac_of_creBase (by rw [LSF_vacuum (by norm_num), vacSF, L0SF_one]) (fun p y => ?_)
  have hX : chiM p.2 (-(p.1 : ℤ) - 1) = creBase p := chiM_eq_creBase p.2 p.1
  have hL : LSF 0 (creBase p y) - creBase p (LSF 0 y) = ((p.1 : ℂ) + 1) • creBase p y := by
    rw [← hX, LSF_comm_chiM_apply,
      show (0 : ℤ) + (-(p.1 : ℤ) - 1) = -(p.1 : ℤ) - 1 from by ring, hX]
    congr 1
    push_cast
    ring
  have hR : L0SF (creBase p y) - creBase p (L0SF y) = ((p.1 : ℂ) + 1) • creBase p y := by
    change L0SF (ι QSF (Finsupp.single p (1 : ℂ)) * y)
        - ι QSF (Finsupp.single p (1 : ℂ)) * L0SF y = _
    rw [L0SF_mul, add_sub_cancel_left, L0SF_gen, smul_mul_assoc]
    rfl
  rw [hL, hR]

/-- **VOA2 for symplectic fermions**: `L₀` acts on the weight-`h` space as `h`. -/
theorem LSF_zero_grading {h : ℂ} {v : FockSF} (hv : v ∈ gradingSF h) : LSF 0 v = h • v := by
  rw [LSF_zero_eq_L0SF]
  exact Module.End.mem_eigenspace_iff.mp (gradingSF_le_eigenspace h hv)

/-- `ωSF` has conformal weight `2`. -/
theorem omega_mem_grading : ωSF ∈ gradingSF 2 := by
  have h := stWordSF_mem_gradingSF [((0 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))]
  rw [show (sfWeight [((0 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))] : ℂ) = 2 from by
    norm_num [sfWeight]] at h
  exact Submodule.neg_mem _ h

/-- `L₀ωSF = 2ωSF`. -/
theorem LSF_zero_omega : LSF 0 ωSF = (2 : ℂ) • ωSF := LSF_zero_grading omega_mem_grading


/-! ## §5  The Virasoro relation and the central charge `c = -2`

Step for step the free-boson computation of `Examples/HeisenbergCentral`, which is why the
*scalar* window resummation `window_sum` is imported from there rather than redone: it is a
statement about `∑_{i} (i-m)·(gate mismatch)` and knows nothing about which theory produced it.
Everything else is redone, because the operator content is different: two species, an
anticommutator instead of a commutator, and the Koszul sign inside the normal ordering.

The mechanism, in one sentence: `[Lₘ, ·]` shifts the *left* index of the pair `(j, n-j)` by `m`,
so after reindexing `i = m+j` the family is normal-ordered with respect to the **wrong gate**
(`i < m` instead of `i < 0`); repairing the gate costs one anticommutator per lattice point in
between, and those anticommutators are the scalars that add up to the central term. -/

/-- Moving `Lₘ` past a single mode.  The `Lₘ`-covariance of `χᶜ` in the form the per-term
computation consumes. -/
theorem LSF_move (m : ℤ) (c : Fin 2) (r : ℤ) (x : FockSF) :
    LSF m (chiM c r x) = chiM c r (LSF m x) + (-(r : ℂ)) • chiM c (m + r) x := by
  have h := LSF_comm_chiM_apply m c r x
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

/-- The `F`-family: the half of the per-term bracket in which the **left** index has been
shifted, `(j, n-j) ↦ (m+j, n-j)`, still gated at `j < 0`.  This is the piece whose gate is
wrong after reindexing. -/
noncomputable def sfFfam (m n j : ℤ) (x : FockSF) : FockSF :=
  (-(j : ℂ)) • (if j < 0 then chiM 0 (m + j) (chiM 1 (n - j) x)
                else -(chiM 1 (n - j) (chiM 0 (m + j) x)))

/-- The `G`-family: the half in which the **right** index is shifted.  It is already exactly a
multiple of `sfTerm (m+n)`, so it contributes only to the bulk. -/
noncomputable def sfGfam (m n j : ℤ) (x : FockSF) : FockSF :=
  (-((n - j : ℤ) : ℂ)) • sfTerm (m + n) j x

/-- The **shifted-gate** pair: `sfTerm (m+n)` but normal-ordered at the gate `i < m`. -/
noncomputable def sfTilS (m n i : ℤ) (x : FockSF) : FockSF :=
  if i < m then chiM 0 i (chiM 1 (m + n - i) x) else -(chiM 1 (m + n - i) (chiM 0 i x))

/-- **The per-term bracket splits as `F + G`.**  `Lₘ` is even, so `[Lₘ, ·]` is a plain
derivation over the product of the two odd modes; each factor contributes one family. -/
theorem LSF_comm_sfTerm (m n j : ℤ) (x : FockSF) :
    LSF m (sfTerm n j x) - sfTerm n j (LSF m x) = sfFfam m n j x + sfGfam m n j x := by
  rw [sfTerm_apply, sfTerm_apply, sfFfam, sfGfam, sfTerm_apply]
  by_cases h : j < 0
  · simp only [if_pos h]
    rw [LSF_move, LSF_move]
    simp only [map_add, map_smul]
    rw [show m + (n - j) = m + n - j from by ring]
    abel
  · simp only [if_neg h]
    rw [map_neg, LSF_move, LSF_move]
    simp only [map_add, map_smul, smul_neg]
    rw [show m + (n - j) = m + n - j from by ring]
    abel

/-- The shift `i ↦ i - m` used to reindex the `F`-family. -/
def sfShift (m : ℤ) : ℤ ≃ ℤ where
  toFun i := i - m
  invFun i := i + m
  left_inv i := by dsimp only; ring
  right_inv i := by dsimp only; ring

@[simp] theorem sfShift_apply (m i : ℤ) : sfShift m i = i - m := rfl

/-- **Reindexing the `F`-family moves the normal-ordering gate.**  After `i = m + j` the pair
is `(i, m+n-i)` — the same pair the bulk term carries — but ordered by `i < m`, not `i < 0`.
That discrepancy is the entire source of the central charge. -/
theorem sfFfam_reindex (m n i : ℤ) (x : FockSF) :
    sfFfam m n (i - m) x = (-((i - m : ℤ) : ℂ)) • sfTilS m n i x := by
  rw [sfFfam, sfTilS]
  congr 1
  by_cases hi : i < m
  · rw [if_pos (show i - m < 0 from by omega), if_pos hi,
      show m + (i - m) = i from by ring, show n - (i - m) = m + n - i from by ring]
  · rw [if_neg (show ¬ (i - m < 0) from by omega), if_neg hi,
      show m + (i - m) = i from by ring, show n - (i - m) = m + n - i from by ring]

/-- The scalar picked up at one lattice point of the gate mismatch. -/
noncomputable def winScalarSF (m n i : ℤ) : ℂ :=
  if m + n = 0 then
    (if (i < 0 ∧ ¬ i < m) then (i : ℂ)
     else if (¬ i < 0 ∧ i < m) then -(i : ℂ) else 0)
  else 0

/-- **The gate mismatch is a scalar.**  Where the two gates agree the two orderings are
literally the same operator; where they disagree the difference is the anticommutator
`{χ⁰_i, χ¹_{m+n-i}} = i·δ_{m+n,0}` — central, and nonzero only on the diagonal `m+n = 0`. -/
theorem S_sub_sfTilS (m n i : ℤ) (x : FockSF) :
    sfTerm (m + n) i x - sfTilS m n i x = winScalarSF m n i • x := by
  have hPQ : chiM 0 i (chiM 1 (m + n - i) x) - (-(chiM 1 (m + n - i) (chiM 0 i x)))
      = (if m + n = 0 then (i : ℂ) else 0) • x := by
    rw [sub_neg_eq_add, chiM_anticomm_apply, carC_apply, sfOmega_zero_one, mul_one]
    congr 1
    by_cases hmn : m + n = 0
    · rw [if_pos hmn, if_pos (show i + (m + n - i) = 0 from by omega)]
    · rw [if_neg hmn, if_neg (show ¬ (i + (m + n - i) = 0) from by omega)]
  have hflip : -(chiM 1 (m + n - i) (chiM 0 i x)) - chiM 0 i (chiM 1 (m + n - i) x)
      = -(chiM 0 i (chiM 1 (m + n - i) x) - (-(chiM 1 (m + n - i) (chiM 0 i x)))) := by abel
  rw [sfTerm_apply, sfTilS, winScalarSF]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn] at hPQ ⊢
    by_cases h0 : i < 0 <;> by_cases hm : i < m
    · rw [if_pos h0, if_pos hm, sub_self, if_neg (by tauto), if_neg (by tauto), zero_smul]
    · rw [if_pos h0, if_neg hm, hPQ, if_pos (show i < 0 ∧ ¬ i < m from ⟨h0, hm⟩)]
    · rw [if_neg h0, if_pos hm, if_neg (show ¬ (i < 0 ∧ ¬ i < m) from by tauto),
        if_pos (show ¬ i < 0 ∧ i < m from ⟨h0, hm⟩), hflip, hPQ, neg_smul]
    · rw [if_neg h0, if_neg hm, sub_self, if_neg (by tauto), if_neg (by tauto), zero_smul]
  · rw [if_neg hmn, zero_smul] at hPQ
    rw [if_neg hmn, zero_smul]
    by_cases h0 : i < 0 <;> by_cases hm : i < m
    · rw [if_pos h0, if_pos hm, sub_self]
    · rw [if_pos h0, if_neg hm]
      exact hPQ
    · rw [if_neg h0, if_pos hm, hflip, hPQ, neg_zero]
    · rw [if_neg h0, if_neg hm, sub_self]

/-! ### Finiteness of the families -/

theorem sfGfam_support_finite (m n : ℤ) (x : FockSF) :
    (Function.support (fun j : ℤ => sfGfam m n j x)).Finite := by
  apply Set.Finite.subset (sfTerm_support_finite (m + n) x)
  intro j hj
  rw [Function.mem_support] at hj ⊢
  rw [sfGfam] at hj
  exact fun h => hj (by rw [h, smul_zero])

theorem sfWeightedS_support_finite (s : ℤ) (c : ℤ → ℂ) (x : FockSF) :
    (Function.support (fun i : ℤ => c i • sfTerm s i x)).Finite := by
  apply Set.Finite.subset (sfTerm_support_finite s x)
  intro i hi
  rw [Function.mem_support] at hi ⊢
  exact fun h => hi (by rw [h, smul_zero])

theorem sfR_support_finite (m n : ℤ) (x : FockSF) :
    (Function.support (fun j : ℤ =>
      LSF m (sfTerm n j x) - sfTerm n j (LSF m x))).Finite := by
  apply Set.Finite.subset
    ((sfTerm_support_finite n x).union (sfTerm_support_finite n (LSF m x)))
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_union, Function.mem_support, Function.mem_support]
  by_contra h
  push Not at h
  apply hj
  rw [h.1, h.2, map_zero, sub_zero]

theorem sfFfam_support_finite (m n : ℤ) (x : FockSF) :
    (Function.support (fun j : ℤ => sfFfam m n j x)).Finite := by
  apply Set.Finite.subset ((sfR_support_finite m n x).union (sfGfam_support_finite m n x))
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_union, Function.mem_support, Function.mem_support]
  by_contra h
  push Not at h
  apply hj
  have hR := LSF_comm_sfTerm m n j x
  rw [h.1, h.2, add_zero] at hR
  exact hR.symm

theorem sfReindexedF_support_finite (m n : ℤ) (x : FockSF) :
    (Function.support (fun i : ℤ => (-((i - m : ℤ) : ℂ)) • sfTilS m n i x)).Finite := by
  apply Set.Finite.subset ((sfFfam_support_finite m n x).image (fun j => j + m))
  intro i hi
  rw [Function.mem_support, ← sfFfam_reindex] at hi
  exact ⟨i - m, by rw [Function.mem_support]; exact hi, (by ring : i - m + m = i)⟩

/-! ### The master identity: bulk plus boundary window -/

/-- The commutator of two Virasoro modes as one finsum of per-term brackets. -/
theorem LSF_comm_eq_finsum (m n : ℤ) (x : FockSF) :
    LSF m (LSF n x) - LSF n (LSF m x)
      = -∑ᶠ j : ℤ, (LSF m (sfTerm n j x) - sfTerm n j (LSF m x)) := by
  rw [finsum_sub_distrib (sfTerm_map_support_finite n (LSF m) x)
      (sfTerm_support_finite n (LSF m x)),
    LSF_apply n x, map_neg, map_finsum (LSF m) (sfTerm_support_finite n x),
    LSF_apply n (LSF m x)]
  abel

/-- **The Virasoro commutator, split into bulk and boundary window.**  The bulk
`(m-n)L_{m+n}` is what survives the reindexing; the window is the finite sum of gate
mismatches, each of which `S_sub_sfTilS` has already shown to be a scalar. -/
theorem LSF_comm_bulk_window (m n : ℤ) (x : FockSF) :
    LSF m (LSF n x) - LSF n (LSF m x)
      = (((m : ℂ) - n) • LSF (m + n) x)
        - ∑ᶠ i : ℤ, (((i : ℂ) - m) • (sfTerm (m + n) i x - sfTilS m n i x)) := by
  rw [LSF_comm_eq_finsum m n x,
    show (∑ᶠ j : ℤ, (LSF m (sfTerm n j x) - sfTerm n j (LSF m x)))
        = ∑ᶠ j : ℤ, (sfFfam m n j x + sfGfam m n j x) from
      finsum_congr fun j => LSF_comm_sfTerm m n j x,
    finsum_add_distrib (sfFfam_support_finite m n x) (sfGfam_support_finite m n x),
    show (∑ᶠ j : ℤ, sfFfam m n j x)
        = ∑ᶠ i : ℤ, (-((i - m : ℤ) : ℂ)) • sfTilS m n i x from by
      rw [← finsum_comp_equiv (sfShift m) (f := fun j => sfFfam m n j x)]
      exact finsum_congr fun i => by rw [sfShift_apply, sfFfam_reindex],
    show (∑ᶠ j : ℤ, sfGfam m n j x)
        = ∑ᶠ j : ℤ, (-((n - j : ℤ) : ℂ)) • sfTerm (m + n) j x from
      finsum_congr fun j => by rw [sfGfam],
    ← finsum_add_distrib (sfReindexedF_support_finite m n x)
      (sfWeightedS_support_finite (m + n) (fun i => -((n - i : ℤ) : ℂ)) x),
    show (∑ᶠ i : ℤ, ((-((i - m : ℤ) : ℂ)) • sfTilS m n i x
            + (-((n - i : ℤ) : ℂ)) • sfTerm (m + n) i x))
        = ∑ᶠ i : ℤ, (((m : ℂ) - n) • sfTerm (m + n) i x
            + ((i : ℂ) - m) • (sfTerm (m + n) i x - sfTilS m n i x)) from
      finsum_congr fun i => by push_cast; module,
    finsum_add_distrib (sfWeightedS_support_finite (m + n) (fun _ => (m : ℂ) - n) x)
      (by
        apply Set.Finite.subset
          ((sfWeightedS_support_finite (m + n) (fun i => (i : ℂ) - m) x).union
            (sfReindexedF_support_finite m n x))
        intro i hi
        rw [Function.mem_support] at hi
        rw [Set.mem_union, Function.mem_support, Function.mem_support]
        by_contra h
        push Not at h
        apply hi
        obtain ⟨h1, h2⟩ := h
        have h2' : ((i : ℂ) - m) • sfTilS m n i x = 0 := by
          have hz : (-((i - m : ℤ) : ℂ)) • sfTilS m n i x = 0 := h2
          rw [neg_smul, neg_eq_zero] at hz
          rw [show ((i : ℂ) - m) = ((i - m : ℤ) : ℂ) from by push_cast; ring]
          exact hz
        rw [smul_sub, h1, h2', sub_zero]),
    neg_add]
  have hA : -∑ᶠ i : ℤ, ((m : ℂ) - n) • sfTerm (m + n) i x = ((m : ℂ) - n) • LSF (m + n) x := by
    rw [LSF_apply, ← smul_finsum' ((m : ℂ) - n) (sfTerm_support_finite (m + n) x), ← smul_neg]
  rw [hA]
  abel

/-! ### The window resums to the central term -/

theorem winScalarSF_eq (m n i : ℤ) : winScalarSF m n i = winScalar 1 m n i := by
  rw [winScalarSF, winScalar]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn]
    split_ifs <;> ring
  · rw [if_neg hmn, if_neg hmn]

/-- **The boundary window resums to `(m³-m)/6`.**  This is a statement about integers and
nothing else, so it is imported from the free-boson computation (`window_sum` at `k = 1`)
rather than redone: the mismatch window and its arithmetic are model-independent. -/
theorem window_sum_SF (m n : ℤ) :
    (∑ᶠ i : ℤ, ((i : ℂ) - m) * winScalarSF m n i)
      = if m + n = 0 then ((m : ℂ) ^ 3 - m) / 6 else 0 := by
  have h : (∑ᶠ i : ℤ, ((i : ℂ) - m) * winScalarSF m n i)
      = ∑ᶠ i : ℤ, ((i : ℂ) - m) * winScalar 1 m n i :=
    finsum_congr fun i => by rw [winScalarSF_eq]
  rw [h, window_sum 1 m n]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn]; ring
  · rw [if_neg hmn, if_neg hmn]

/-! ### The Virasoro relation -/

/-- **The Virasoro relations for symplectic fermions, central charge `c = -2`:**

`[Lₘ, Lₙ] = (m-n)L_{m+n} + δ_{m+n,0}·(m³-m)/12·c`,  `c = -2`.

The bulk is anomaly-free; the entire central term is the finite normal-ordering window
`window_sum_SF`, and the `-2` is the product of that window's `(m³-m)/6` with the overall sign
of `L = -:χ⁰χ¹:`.  Nothing in the derivation put a `-2` in by hand. -/
theorem LSF_virasoro (m n : ℤ) :
    LSF m * LSF n - LSF n * LSF m
      = ((m : ℂ) - n) • LSF (m + n)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 * (-2) else 0) • (1 : End ℂ FockSF) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
    LSF_comm_bulk_window m n x,
    show (∑ᶠ i : ℤ, (((i : ℂ) - m) • (sfTerm (m + n) i x - sfTilS m n i x)))
        = ∑ᶠ i : ℤ, (((i : ℂ) - m) * winScalarSF m n i) • x from
      finsum_congr fun i => by rw [S_sub_sfTilS m n i x, smul_smul],
    ← finsum_smul, window_sum_SF m n]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn]
    module
  · rw [if_neg hmn, if_neg hmn, zero_smul, sub_zero, add_zero]

/-- **The central charge, exhibited directly**: `L₂ωSF = (c/2)|0⟩ = -|0⟩`.  This is the classical
"double contraction" form of the statement `c = -2`, and here it is a *corollary* of the general
relation rather than an independent computation. -/
theorem LSF_two_omega : LSF 2 ωSF = -vacSF := by
  have h := congrArg (fun (S : End ℂ FockSF) => S vacSF) (LSF_virasoro 2 (-2))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply] at h
  rw [LSF_neg_two_vacuum, LSF_vacuum (by norm_num : (-1 : ℤ) ≤ 2), map_zero,
    LSF_vacuum (show (-1 : ℤ) ≤ 2 + -2 from by norm_num), sub_zero, smul_zero, zero_add,
    if_pos (by norm_num : (2 : ℤ) + -2 = 0)] at h
  rw [h]
  norm_num

/-- **`ωSF` is quasi-primary**: `L₁ωSF = 0`.  The `m = 1, n = -2` relation has no central term
(`1 + (-2) ≠ 0`), and `L₋₁|0⟩ = 0`. -/
theorem LSF_one_omega : LSF 1 ωSF = 0 := by
  have h := congrArg (fun (S : End ℂ FockSF) => S vacSF) (LSF_virasoro 1 (-2))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply] at h
  rw [LSF_neg_two_vacuum, LSF_vacuum (by norm_num : (-1 : ℤ) ≤ 1), map_zero,
    LSF_vacuum (show (-1 : ℤ) ≤ 1 + -2 from by norm_num), sub_zero, smul_zero, zero_add,
    if_neg (by norm_num : ¬ ((1 : ℤ) + -2 = 0)), zero_smul] at h
  exact h

/-! ## §6  The statement in `SuperVertexOperatorAlgebra` shape

`Core/SuperVertexOperatorAlgebra` states VOA1 as a Lie bracket of `mode (Y ω) (·+1)` with the
scalar *inside* the `if`.  Restating `LSF_virasoro` in exactly that shape means the eventual
instance can cite it verbatim, with `conformalVector := ωSF` and `centralCharge := -2`. -/

/-- **The central charge of the symplectic-fermion vertex superalgebra.** -/
def sfCentralCharge : ℂ := -2

/-- **VOA1, verbatim in the form `SuperVertexOperatorAlgebra.virasoro` demands**, with
`conformalVector := ωSF` and `centralCharge := sfCentralCharge = -2`. -/
theorem YSF_omega_virasoro (m n : ℤ) :
    ⁅mode (YSF ωSF) (m + 1), mode (YSF ωSF) (n + 1)⁆
      = ((m : ℂ) - n) • mode (YSF ωSF) (m + n + 1)
        + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * sfCentralCharge) • (1 : End ℂ FockSF)
           else 0) := by
  rw [← LSF_eq_mode, ← LSF_eq_mode, ← LSF_eq_mode, Ring.lie_def, LSF_virasoro, sfCentralCharge]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn]
  · rw [if_neg hmn, if_neg hmn, zero_smul]

end VOA.SympFerm
