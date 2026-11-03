/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergNFock
import VOA.Examples.HeisenbergVertex
import VOA.Core.Dong
import VOA.Core.Reconstruction
import VOA.Core.Skew
import VOA.Core.Identities
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The rank-`r` Heisenberg vertex-algebra layer  (Gannon §5.2.2, rank `r`)

The mechanical rank-`r` generalization of the rank-1 Heisenberg vertex-algebra layer
(`Examples/HeisenbergVertex`, `Examples/HeisenbergCreation`, `Examples/HeisenbergGrading`,
`Examples/HeisenbergStructure`).  Everything is re-derived under the dedicated namespace
`VOA.HeisenbergN`; no rank-1 short-names are shadowed.  Building on the Fock layer
(`Examples.HeisenbergNFock`: the basic currents `αᵃ(z)`, their modes the oscillators
`oscN r k a n`, their self/cross-locality, and the weighted grading `gradingWN`), this file
constructs the general vertex operator `YN r k : FockN r →ₗ[ℂ] FormalDist (End ℂ (FockN r))`
together with all five vertex-algebra axioms.

## The construction
* **Derivative currents** `dcurrentN r k a j := ∂_z^j αᵃ(z)`; the scaled generator fields
  `genFieldN r k a i := (i!)⁻¹·∂^i αᵃ = Y(aᵃ₋(i+1)1, z)`.  Each is a field and any two are
  mutually local across all `(i,a)`/`(j,b)` families.
* **`YN` on monomials.**  A monomial `∏ X_{(iₜ,aₜ)}` is encoded by its exponent vector
  `(ℕ × Fin r) →₀ ℕ`; the field `YmonN` is the iterated normal-ordered product of the
  `genFieldN`s over the corresponding word `List (ℕ × Fin r)`.  `YN` is the `ℂ`-linear
  extension via `Finsupp.linearCombination`.
* **VA2** `YN_vacuum : YN r k 1 = idFieldN`; `YN_current : YN r k (aᵃ₋₁1) = αᵃ(z)`.
* **VA4** every two monomial fields are mutually local (`YmonN_local`, iterated `dong_neg`);
  bilinear extension to all `u, v` (`YN_local`).
* **VA3** `YN_creation`: `(YN u)₍₋₁₎1 = u`, `(YN u)₍ₙ₎1 = 0` for `n ≥ 0`.
* **VA1/VA5** the `ℤ`-graded `gradingZN`, the grading mode law `va1N_grading_mode`, regularity
  `va5N_regularity`, the internal direct-sum decomposition `gradingZN_isInternal`,
  finite-dimensionality `gradingZN_finrank`, `gradingZN_zero_eq_span_vacuum`, `gradingZN_positivity`.

## Status
Fully axiom-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).

## References
* Gannon §5.2.2, eqs. (5.2.5); FLM Ch. 8; Kac §3.5; Lepowsky–Li Ch. 6.
-/

namespace VOA

namespace HeisenbergN

open scoped BigOperators
open MvPolynomial
open Module (End)

variable {r : ℕ}

/-! ## §1  The derivative currents and the scaled generator fields -/

/-- The **derivative currents** `dcurrentN r k a j := ∂_z^j αᵃ(z)`, the `j`-th formal derivative
of the basic current `αᵃ(z) = Y(aᵃ₋₁1, z)` (Gannon 5.2.5). -/
noncomputable def dcurrentN (r : ℕ) (k : ℂ) (a : Fin r) (j : ℕ) :
    FormalDist (End ℂ (FockN r)) :=
  (deriv^[j]) (currentN r k a)

@[simp] theorem dcurrentN_zero (r : ℕ) (k : ℂ) (a : Fin r) :
    dcurrentN r k a 0 = currentN r k a := rfl

theorem dcurrentN_succ (r : ℕ) (k : ℂ) (a : Fin r) (j : ℕ) :
    dcurrentN r k a (j + 1) = deriv (dcurrentN r k a j) := by
  rw [dcurrentN, dcurrentN, Function.iterate_succ', Function.comp_apply]

/-- **The basic current is a field**: `αᵃ(z)` is lower-truncated (its high annihilation modes
`aᵃₙ` vanish on any fixed polynomial once `n` exceeds its variable indices). -/
theorem currentN_isField (r : ℕ) (k : ℂ) (a : Fin r) : IsField (currentN r k a) := by
  intro p
  refine ⟨-(((p.vars.sup (fun u => u.1) : ℕ) : ℤ)) - 2, fun n hn => ?_⟩
  rw [currentN_apply]
  have hpos : 0 < -n - 1 := by omega
  rw [oscN_apply_pos r k a hpos]
  have hzero : pderiv ((-n - 1 - 1).toNat, a) p = 0 := by
    apply pderiv_eq_zero_of_notMem_vars
    intro hmem
    have hle : ((-n - 1 - 1).toNat, a).1 ≤ p.vars.sup (fun u => u.1) :=
      Finset.le_sup (f := fun u => u.1) hmem
    simp only at hle
    omega
  rw [hzero, smul_zero, smul_zero]

/-- **The derivative currents are fields** (the derivative of a field is a field). -/
theorem dcurrentN_isField (r : ℕ) (k : ℂ) (a : Fin r) (j : ℕ) :
    IsField (dcurrentN r k a j) :=
  (currentN_isField r k a).deriv_iterate j

/-- **The modes of the derivative currents** (Gannon 5.2.5): a falling-factorial multiple of
the oscillator, `mode (∂^j αᵃ) m = (∏_{i<j} -(m-i))·aᵃ_{m-j}`. -/
theorem dcurrentN_mode (r : ℕ) (k : ℂ) (a : Fin r) (j : ℕ) (m : ℤ) :
    mode (dcurrentN r k a j) m
      = (∏ i ∈ Finset.range j, (-(m - (i : ℤ)))) • oscN r k a (m - j) := by
  induction j generalizing m with
  | zero => simp only [dcurrentN, Function.iterate_zero, id_eq, Finset.range_zero,
      Finset.prod_empty, one_smul, Nat.cast_zero, sub_zero]; exact currentN_mode r k a m
  | succ p ih =>
    rw [dcurrentN_succ, mode_deriv, ih (m - 1), smul_smul]
    have hco : (-m) * (∏ i ∈ Finset.range p, (-(m - 1 - (i : ℤ))))
             = ∏ i ∈ Finset.range (p + 1), (-(m - (i : ℤ))) := by
      rw [Finset.prod_range_succ']
      have heq : (∏ i ∈ Finset.range p, (-(m - ((i : ℕ) + 1 : ℤ))))
               = ∏ i ∈ Finset.range p, (-(m - 1 - (i : ℤ))) :=
        Finset.prod_congr rfl fun i _ => by ring
      simp only [Nat.cast_add, Nat.cast_one]
      rw [heq]; ring
    rw [hco]
    congr 2
    omega

/-- **The derivative currents are mutually local** (Gannon 5.2.5c): `Local (∂^i αᵃ)(∂^j αᵇ)`,
from the self/cross-locality of the basic currents together with locality-preservation under
`∂_z`. -/
theorem dcurrentN_local (r : ℕ) (k : ℂ) (a b : Fin r) (i j : ℕ) :
    Local (dcurrentN r k a i) (dcurrentN r k b j) :=
  (((currentN_local r k a b)).deriv_iterate_left i).deriv_iterate_right j

/-- The **scaled generator field** `genFieldN r k a i := (i!)⁻¹·∂_z^i αᵃ(z)`.  In the
vertex-operator indexing it is exactly `Y(aᵃ₋(i+1)1, z)` (Gannon 5.2.5). -/
noncomputable def genFieldN (r : ℕ) (k : ℂ) (a : Fin r) (i : ℕ) :
    FormalDist (End ℂ (FockN r)) :=
  (i.factorial : ℂ)⁻¹ • dcurrentN r k a i

theorem genFieldN_isField (r : ℕ) (k : ℂ) (a : Fin r) (i : ℕ) :
    IsField (genFieldN r k a i) := by
  intro x; obtain ⟨B, hB⟩ := dcurrentN_isField r k a i x
  exact ⟨B, fun n hn => by
    show ((i.factorial : ℂ)⁻¹ • dcurrentN r k a i n) x = 0
    rw [LinearMap.smul_apply, hB n hn, smul_zero]⟩

/-- `genFieldN r k a 0 = αᵃ(z)`: the lowest generator field is the bare basic current. -/
theorem genFieldN_zero (r : ℕ) (k : ℂ) (a : Fin r) : genFieldN r k a 0 = currentN r k a := by
  rw [genFieldN, dcurrentN_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]

set_option maxHeartbeats 1000000 in
/-- **The generator fields are mutually local** across all `(i,a)`/`(j,b)` families
(scale-invariance of `dcurrentN_local`). -/
theorem genFieldN_local (r : ℕ) (k : ℂ) (a b : Fin r) (i j : ℕ) :
    Local (genFieldN r k a i) (genFieldN r k b j) := by
  show Local ((i.factorial : ℂ)⁻¹ • dcurrentN r k a i) ((j.factorial : ℂ)⁻¹ • dcurrentN r k b j)
  exact Local.smulR _ (VertexOperatorAlgebra.Local.smul' _ (dcurrentN_local r k a b i j))

/-! ## §2  The identity field, the iterated normal-ordered product, and `YN` -/

/-- The **identity field** `Y(1,z) = id`: the constant distribution `id·z⁰`. -/
noncomputable def idFieldN (r : ℕ) : FormalDist (End ℂ (FockN r)) :=
  fun j => if j = 0 then LinearMap.id else 0

@[simp] theorem idFieldN_apply (r : ℕ) (j : ℤ) :
    (idFieldN r) j = if j = 0 then LinearMap.id else 0 := rfl

theorem idFieldN_isField (r : ℕ) : IsField (idFieldN r) := by
  intro x; exact ⟨0, fun n hn => by
    rw [idFieldN_apply, if_neg (by omega)]; rfl⟩

/-- The identity field commutes with every distribution: `[1(z₁),b(z₂)] = 0`. -/
theorem bracketDist_idFieldN_left (r : ℕ) (b : FormalDist (End ℂ (FockN r))) :
    bracketDist (idFieldN r) b = 0 := by
  apply FormalDist₂.ext; intro m n
  rw [bracketDist_apply, idFieldN_apply]
  show (if m = 0 then LinearMap.id else 0 : End ℂ (FockN r)) * b n
      - b n * (if m = 0 then LinearMap.id else 0) = (0 : FormalDist₂ (End ℂ (FockN r))) m n
  by_cases h : m = 0
  · rw [if_pos h, show (LinearMap.id : End ℂ (FockN r)) = 1 from rfl, one_mul, mul_one, sub_self]
    rfl
  · rw [if_neg h, zero_mul, mul_zero, sub_zero]; rfl

theorem Local_idFieldN_left (r : ℕ) (b : FormalDist (End ℂ (FockN r))) :
    Local (idFieldN r) b :=
  local_of_bracketDist_eq_zero (bracketDist_idFieldN_left r b)

theorem Local_idFieldN_right (r : ℕ) (b : FormalDist (End ℂ (FockN r))) :
    Local b (idFieldN r) :=
  (Local_idFieldN_left r b).symm

/-- `:a(z) 1: = a(z)`: the normal-ordered product with the identity field is the identity. -/
theorem nprod_idFieldN {r : ℕ} {a : FormalDist (End ℂ (FockN r))} (ha : IsField a) :
    nprod ha (idFieldN_isField r) = a := by
  funext s
  apply LinearMap.ext; intro x
  rw [nprod_apply, finsum_eq_single _ s]
  · rw [normalOrdered_apply]
    have hid : (idFieldN r) (s - s) = LinearMap.id := by
      rw [idFieldN_apply, if_pos (by ring)]
    by_cases h : 0 ≤ s
    · rw [if_pos h, hid]; rfl
    · rw [if_neg h, hid]; rfl
  · intro m hm
    rw [normalOrdered_apply]
    have hid : (idFieldN r) (s - m) = 0 := by
      rw [idFieldN_apply, if_neg (by omega)]
    by_cases h : 0 ≤ m
    · rw [if_pos h, hid]; simp
    · rw [if_neg h, hid]; simp

/-- The iterated normal-ordered product over a list of generator indices `(i,a)`, paired with
its field witness.  `[]` ↦ the identity field; `(i,a) :: rest` ↦ `:(genFieldN i a)(YwordN rest):`. -/
noncomputable def YwordNF (r : ℕ) (k : ℂ) :
    List (ℕ × Fin r) → { f : FormalDist (End ℂ (FockN r)) // IsField f }
  | [] => ⟨idFieldN r, idFieldN_isField r⟩
  | (ia :: rest) =>
      let p := YwordNF r k rest
      ⟨nprod (genFieldN_isField r k ia.2 ia.1) p.2,
        (genFieldN_isField r k ia.2 ia.1).nprod p.2⟩

/-- The iterated normal-ordered product `YwordN k [(i₁,a₁),…] = :(∂^{i₁}αᵃ¹/i₁!)⋯:`. -/
noncomputable def YwordN (r : ℕ) (k : ℂ) (l : List (ℕ × Fin r)) :
    FormalDist (End ℂ (FockN r)) := (YwordNF r k l).1

theorem YwordN_isField (r : ℕ) (k : ℂ) (l : List (ℕ × Fin r)) :
    IsField (YwordN r k l) := (YwordNF r k l).2

@[simp] theorem YwordN_nil (r : ℕ) (k : ℂ) : YwordN r k [] = idFieldN r := rfl

theorem YwordN_cons (r : ℕ) (k : ℂ) (ia : ℕ × Fin r) (rest : List (ℕ × Fin r)) :
    YwordN r k (ia :: rest)
      = nprod (genFieldN_isField r k ia.2 ia.1) (YwordN_isField r k rest) := rfl

/-- The list of generator indices of a monomial exponent vector `a : (ℕ × Fin r) →₀ ℕ`: each
variable `(i,b)` (with exponent `a (i,b)`) contributes `a (i,b)` copies of `(i,b)`.  The support
is enumerated via `Finset.toList` (no canonical order is needed: only the multiset of generators
matters for the state and its weight). -/
noncomputable def monoWordN (a : (ℕ × Fin r) →₀ ℕ) : List (ℕ × Fin r) :=
  a.support.toList.flatMap (fun ia => List.replicate (a ia) ia)

/-- `YN(u,z)` on a monomial `u = ∏ X_{(i,b)}^{a_{(i,b)}}` (exponent vector `a`): the iterated
normal-ordered product of the generator fields (Gannon 5.2.5). -/
noncomputable def YmonN (r : ℕ) (k : ℂ) (a : (ℕ × Fin r) →₀ ℕ) :
    FormalDist (End ℂ (FockN r)) := YwordN r k (monoWordN a)

theorem YmonN_isField (r : ℕ) (k : ℂ) (a : (ℕ × Fin r) →₀ ℕ) :
    IsField (YmonN r k a) := YwordN_isField r k _

/-- **The general vertex operator** `YN : FockN r →ₗ[ℂ] FormalDist (End ℂ (FockN r))` — the
`ℂ`-linear extension of `YmonN` off the monomial basis of `FockN r` (Gannon §5.2). -/
noncomputable def YN (r : ℕ) (k : ℂ) : FockN r →ₗ[ℂ] FormalDist (End ℂ (FockN r)) :=
  Finsupp.linearCombination ℂ (YmonN r k)

theorem YN_monomial (r : ℕ) (k : ℂ) (a : (ℕ × Fin r) →₀ ℕ) (c : ℂ) :
    YN r k (monomial a c) = c • YmonN r k a :=
  Finsupp.linearCombination_single ℂ c a

theorem YN_monomial_one (r : ℕ) (k : ℂ) (a : (ℕ × Fin r) →₀ ℕ) :
    YN r k (monomial a 1) = YmonN r k a := by
  rw [YN_monomial, one_smul]

/-! ## §3  VA2 — the vacuum field, and the basic current -/

@[simp] theorem monoWordN_zero : monoWordN (0 : (ℕ × Fin r) →₀ ℕ) = [] := by
  rw [monoWordN]; simp

/-- **VA2 / the vacuum field**: `YN(1,z) = idFieldN`. -/
theorem YN_vacuum (r : ℕ) (k : ℂ) : YN r k (vacuumN r) = idFieldN r := by
  rw [vacuumN, show (1 : FockN r) = monomial 0 1 from by rw [monomial_zero', map_one],
      YN_monomial_one, YmonN, monoWordN_zero, YwordN_nil]

theorem YN_vacuum_apply (r : ℕ) (k : ℂ) (j : ℤ) :
    YN r k (vacuumN r) j = if j = 0 then LinearMap.id else 0 := by
  rw [YN_vacuum, idFieldN_apply]

/-- The single creation state `aᵃ₋₁1 = X_{(0,a)}` as a monomial. -/
theorem oscN_neg_one_vacuum (r : ℕ) (k : ℂ) (a : Fin r) :
    oscN r k a (-1) (vacuumN r) = X (0, a) := by
  rw [oscN_apply_neg r k a (by norm_num), vacuumN, mul_one]
  norm_num

theorem X_zero_eq_monomialN (r : ℕ) (a : Fin r) :
    (X (0, a) : FockN r) = monomial (Finsupp.single (0, a) 1) 1 := by
  rw [X]

/-- `monoWordN (single (0,a) 1) = [(0,a)]`: the single-creation state has the one generator. -/
theorem monoWordN_single (r : ℕ) (a : Fin r) :
    monoWordN (Finsupp.single ((0 : ℕ), a) 1) = [((0 : ℕ), a)] := by
  unfold monoWordN
  rw [show (Finsupp.single ((0 : ℕ), a) 1 : (ℕ × Fin r) →₀ ℕ).support = {((0 : ℕ), a)} from
    Finsupp.support_single ((0 : ℕ), a) (by norm_num : (1 : ℕ) ≠ 0)]
  simp

/-- **The basic current** `YN(aᵃ₋₁1, z) = αᵃ(z)` (Gannon 5.2.5b). -/
theorem YN_current (r : ℕ) (k : ℂ) (a : Fin r) :
    YN r k (oscN r k a (-1) (vacuumN r)) = currentN r k a := by
  rw [oscN_neg_one_vacuum, X_zero_eq_monomialN, YN_monomial_one, YmonN, monoWordN_single]
  show nprod (genFieldN_isField r k a 0) (idFieldN_isField r) = currentN r k a
  rw [nprod_idFieldN, genFieldN_zero]

/-! ## §4  VA4 — locality of all monomial fields, assembled by iterated Dong -/

/-- A generator field is local with every iterated product `YwordN` (induction on the word). -/
theorem genFieldN_local_YwordN (r : ℕ) (k : ℂ) :
    ∀ (l : List (ℕ × Fin r)) (i : ℕ) (a : Fin r),
      Local (genFieldN r k a i) (YwordN r k l) := by
  intro l
  induction l with
  | nil => intro i a; rw [YwordN_nil]; exact Local_idFieldN_right r _
  | cons jb rest ih =>
      intro i a
      have hab : Local (genFieldN r k jb.2 jb.1) (YwordN r k rest) := ih jb.1 jb.2
      have hac : Local (genFieldN r k jb.2 jb.1) (genFieldN r k a i) :=
        genFieldN_local r k jb.2 a jb.1 i
      have hbc : Local (YwordN r k rest) (genFieldN r k a i) := (ih i a).symm
      have hmain : Local (nprod (genFieldN_isField r k jb.2 jb.1) (YwordN_isField r k rest))
          (genFieldN r k a i) :=
        dong_neg (genFieldN_isField r k jb.2 jb.1) (YwordN_isField r k rest) hab hac hbc
      rw [YwordN_cons]
      exact hmain.symm

/-- **Every two iterated products are mutually local** (induction on the first word). -/
theorem YwordN_local (r : ℕ) (k : ℂ) :
    ∀ (l₁ l₂ : List (ℕ × Fin r)), Local (YwordN r k l₁) (YwordN r k l₂) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; rw [YwordN_nil]; exact Local_idFieldN_left r _
  | cons ia rest ih =>
      intro l₂
      have hab : Local (genFieldN r k ia.2 ia.1) (YwordN r k rest) :=
        genFieldN_local_YwordN r k rest ia.1 ia.2
      have hac : Local (genFieldN r k ia.2 ia.1) (YwordN r k l₂) :=
        genFieldN_local_YwordN r k l₂ ia.1 ia.2
      have hbc : Local (YwordN r k rest) (YwordN r k l₂) := ih l₂
      have hmain : Local (nprod (genFieldN_isField r k ia.2 ia.1) (YwordN_isField r k rest))
          (YwordN r k l₂) :=
        dong_neg (genFieldN_isField r k ia.2 ia.1) (YwordN_isField r k rest) hab hac hbc
      rw [YwordN_cons]
      exact hmain

/-- **VA4 for the monomial basis**: every two monomial fields are mutually local. -/
theorem YmonN_local (r : ℕ) (k : ℂ) (a b : (ℕ × Fin r) →₀ ℕ) :
    Local (YmonN r k a) (YmonN r k b) :=
  YwordN_local r k (monoWordN a) (monoWordN b)

/-! ### VA4 bilinear extension to all states -/

/-- `YN k u` as the explicit finite sum of its scaled monomial fields. -/
theorem YN_eq_support_sum (r : ℕ) (k : ℂ) (u : FockN r) :
    YN r k u = ∑ a ∈ u.support, (u a) • YmonN r k a := by
  rw [show YN r k u = Finsupp.linearCombination ℂ (YmonN r k) u from rfl,
      Finsupp.linearCombination_apply]
  rfl

theorem smul_YmonN_local (r : ℕ) (k : ℂ) (ca cb : ℂ) (a b : (ℕ × Fin r) →₀ ℕ) :
    Local (ca • YmonN r k a) (cb • YmonN r k b) :=
  Local.smulR cb (VertexOperatorAlgebra.Local.smul' ca (YmonN_local r k a b))

theorem smul_YmonN_local_YN (r : ℕ) (k : ℂ) (ca : ℂ) (a : (ℕ × Fin r) →₀ ℕ) (v : FockN r) :
    Local (ca • YmonN r k a) (YN r k v) := by
  classical
  rw [YN_eq_support_sum r k v]
  refine (VertexOperatorAlgebra.Local.sum v.support (fun b => (v b) • YmonN r k b)
    (fun b _ => ?_)).symm
  exact smul_YmonN_local r k (v b) ca b a

/-- **VA4 (locality), general states.**  `YN(u,z)` and `YN(v,z)` are mutually local for
ARBITRARY `u v : FockN r`. -/
theorem YN_local (r : ℕ) (k : ℂ) (u v : FockN r) : Local (YN r k u) (YN r k v) := by
  classical
  rw [YN_eq_support_sum r k u]
  exact VertexOperatorAlgebra.Local.sum u.support (fun a => (u a) • YmonN r k a)
    (fun a _ => smul_YmonN_local_YN r k (u a) a v)

/-! ## §5  VA3 — creation: regularity of `YN(u,z)` on the vacuum -/

/-- Raw `z^s`-coefficient of `dcurrentN r k a j`. -/
theorem dcurrentN_coeff (r : ℕ) (k : ℂ) (a : Fin r) (j : ℕ) (s : ℤ) :
    dcurrentN r k a j s
      = (∏ i ∈ Finset.range j, ((s : ℤ) + 1 + i)) • oscN r k a (-(s + j) - 1) := by
  have h := dcurrentN_mode r k a j (-s - 1)
  rw [mode_apply, show -(-s - 1) - 1 = s from by ring] at h
  rw [h, show (-s - 1 : ℤ) - j = -(s + j) - 1 from by ring]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by ring

/-- Raw `z^s`-coefficient of `genFieldN r k a i`. -/
theorem genFieldN_coeff (r : ℕ) (k : ℂ) (a : Fin r) (i : ℕ) (s : ℤ) :
    genFieldN r k a i s
      = (((∏ l ∈ Finset.range i, ((s : ℤ) + 1 + l) : ℤ) : ℂ) * (i.factorial : ℂ)⁻¹)
          • oscN r k a (-(s + i) - 1) := by
  show ((i.factorial : ℂ)⁻¹ • dcurrentN r k a i) s = _
  show (i.factorial : ℂ)⁻¹ • dcurrentN r k a i s = _
  rw [dcurrentN_coeff,
    ← Int.cast_smul_eq_zsmul ℂ (∏ l ∈ Finset.range i, ((s : ℤ) + 1 + l))
      (oscN r k a (-(s + i) - 1)),
    smul_smul, mul_comm]

theorem prod_range_zero_eq_factorialN (i : ℕ) :
    (∏ l ∈ Finset.range i, ((0:ℤ) + 1 + l)) = (i.factorial : ℤ) := by
  induction i with
  | zero => simp
  | succ p ih => rw [Finset.prod_range_succ, ih, Nat.factorial_succ]; push_cast; ring

/-- The falling-factorial coefficient `∏_{l<i}(j+1+l)` of `genFieldN` vanishes whenever
`-i ≤ j ≤ -1`. -/
theorem genFieldN_falling_factorial_eq_zero (i : ℕ) {j : ℤ} (hj1 : -(i : ℤ) ≤ j) (hj2 : j ≤ -1) :
    (∏ l ∈ Finset.range i, ((j : ℤ) + 1 + l)) = 0 := by
  apply Finset.prod_eq_zero (i := (-j - 1).toNat)
  · rw [Finset.mem_range]; omega
  · push_cast [Int.toNat_of_nonneg (show (0:ℤ) ≤ -j - 1 from by omega)]; ring

/-- **The negative coefficients of EVERY generator field `genFieldN r k a i` kill the vacuum**. -/
theorem genFieldN_neg_vacuum (r : ℕ) (k : ℂ) (a : Fin r) (i : ℕ) {m : ℤ} (hm : m < 0) :
    genFieldN r k a i m (vacuumN r) = 0 := by
  rw [genFieldN_coeff, LinearMap.smul_apply]
  by_cases hwin : -(i : ℤ) ≤ m
  · rw [genFieldN_falling_factorial_eq_zero i hwin (by omega)]; simp
  · rw [oscN_vacuum r k a _ (by omega), smul_zero]

/-- The `z⁰`-coefficient operator of a generator field is multiplication by `X (i,a)`. -/
theorem genFieldN_zero_apply (r : ℕ) (k : ℂ) (a : Fin r) (i : ℕ) (p : FockN r) :
    genFieldN r k a i 0 p = X (i, a) * p := by
  rw [genFieldN_coeff, LinearMap.smul_apply, prod_range_zero_eq_factorialN,
    oscN_apply_neg r k a (by omega : -(0 + (i:ℤ)) - 1 < 0)]
  rw [show (-(-(0 + (i:ℤ)) - 1) - 1).toNat = (i:ℕ) from by omega]
  rw [show ((i.factorial : ℤ) : ℂ) * (i.factorial : ℂ)⁻¹ = 1 from by
    rw [Int.cast_natCast]; exact mul_inv_cancel₀ (by exact_mod_cast (Nat.factorial_pos i).ne')]
  rw [one_smul]

/-! ### The `nprod_vacuum` decomposition (regularity threading) -/

/-- **`nprod`-on-vacuum, `j < 0` half**: the `m ≥ 0` summands all vanish. -/
theorem nprodN_vacuum_lt {r : ℕ} {a b : FormalDist (End ℂ (FockN r))} (ha : IsField a)
    (hb : IsField b) (hb_lt : ∀ l : ℤ, l < 0 → b l (vacuumN r) = 0) {j : ℤ} (hj : j < 0) :
    nprod ha hb j (vacuumN r)
      = ∑ᶠ m : ℤ, (if m < 0 then b (j - m) (a m (vacuumN r)) else 0) := by
  rw [nprod_apply]
  refine finsum_congr fun m => ?_
  rw [normalOrdered_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0, if_neg (by omega : ¬ m < 0), Module.End.mul_apply]
    rw [hb_lt (j - m) (by omega), map_zero]
  · rw [if_neg h0, if_pos (by omega : m < 0), Module.End.mul_apply]

/-- **`nprod`-on-vacuum, `j = 0` half**. -/
theorem nprodN_vacuum_zero {r : ℕ} {a b : FormalDist (End ℂ (FockN r))} (ha : IsField a)
    (hb : IsField b) (hb_lt : ∀ l : ℤ, l < 0 → b l (vacuumN r) = 0) :
    nprod ha hb 0 (vacuumN r)
      = a 0 (b 0 (vacuumN r))
        + ∑ᶠ m : ℤ, (if m < 0 then b (0 - m) (a m (vacuumN r)) else 0) := by
  rw [nprod_apply]
  have key : ∀ m : ℤ, normalOrdered a b m (0 - m) (vacuumN r)
      = (if m < 0 then b (0 - m) (a m (vacuumN r)) else 0)
        + (if m = 0 then a 0 (b 0 (vacuumN r)) else 0) := by
    intro m
    rw [normalOrdered_apply]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0, if_neg (by omega : ¬ m < 0), zero_add, Module.End.mul_apply]
      rcases h0.lt_or_eq with hpos | hz
      · rw [if_neg (by omega : ¬ m = 0)]
        rw [hb_lt (0 - m) (by omega), map_zero]
      · rw [← hz, if_pos rfl, sub_zero]
    · rw [if_neg h0, if_pos (by omega : m < 0),
        if_neg (by omega : ¬ m = 0), add_zero, Module.End.mul_apply]
  rw [finsum_congr key]
  have hfin1 : (Function.support
      (fun m : ℤ => if m < 0 then b (0 - m) (a m (vacuumN r)) else 0)).Finite := by
    obtain ⟨B, hB⟩ := ha (vacuumN r)
    apply Set.Finite.subset (Set.finite_Icc B (-1))
    intro m hm
    rw [Function.mem_support] at hm
    rw [Set.mem_Icc]
    by_cases h0 : m < 0
    · rw [if_pos h0] at hm
      refine ⟨?_, by omega⟩
      by_contra hlt
      exact hm (by rw [hB m (by omega), map_zero])
    · exact absurd (by rw [if_neg h0] at hm; exact hm) (by simp)
  have hfin2 : (Function.support
      (fun m : ℤ => if m = 0 then a 0 (b 0 (vacuumN r)) else 0)).Finite := by
    apply Set.Finite.subset (Set.finite_singleton 0)
    intro m hm
    rw [Function.mem_support] at hm
    by_contra hne
    exact hm (by rw [if_neg (by simpa using hne)])
  rw [finsum_add_distrib hfin1 hfin2, add_comm]
  congr 1
  rw [finsum_eq_single (fun m => if m = 0 then a 0 (b 0 (vacuumN r)) else 0) 0
      (fun m hm => if_neg hm), if_pos rfl]

/-- If `a`'s negative coefficients kill the vacuum, `nprod a b j 1 = 0` for `j < 0`. -/
theorem nprodN_creation_lt {r : ℕ} {a b : FormalDist (End ℂ (FockN r))} (ha : IsField a)
    (hb : IsField b) (hb_lt : ∀ l : ℤ, l < 0 → b l (vacuumN r) = 0)
    (ha_neg : ∀ m : ℤ, m < 0 → a m (vacuumN r) = 0) {j : ℤ} (hj : j < 0) :
    nprod ha hb j (vacuumN r) = 0 := by
  rw [nprodN_vacuum_lt ha hb hb_lt hj]
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases h0 : m < 0
  · rw [if_pos h0, ha_neg m h0, map_zero]
  · rw [if_neg h0]

/-- If `a`'s negative coefficients kill the vacuum, `nprod a b` creates `a₀(b₀1)` at `z⁰`. -/
theorem nprodN_creation_zero {r : ℕ} {a b : FormalDist (End ℂ (FockN r))} (ha : IsField a)
    (hb : IsField b) (hb_lt : ∀ l : ℤ, l < 0 → b l (vacuumN r) = 0)
    (ha_neg : ∀ m : ℤ, m < 0 → a m (vacuumN r) = 0) :
    nprod ha hb 0 (vacuumN r) = a 0 (b 0 (vacuumN r)) := by
  rw [nprodN_vacuum_zero ha hb hb_lt]
  rw [finsum_eq_zero_of_forall_eq_zero (fun m => ?_), add_zero]
  by_cases h0 : m < 0
  · rw [if_pos h0, ha_neg m h0, map_zero]
  · rw [if_neg h0]

/-- The monomial state created by a word `[(i₁,a₁),…]`: the product `∏ X_{(iₜ,aₜ)} · 1`. -/
noncomputable def wordStateN (l : List (ℕ × Fin r)) : FockN r :=
  (l.map (fun ia => (X ia : FockN r))).prod

@[simp] theorem wordStateN_nil : wordStateN ([] : List (ℕ × Fin r)) = (1 : FockN r) := rfl

@[simp] theorem wordStateN_cons (ia : ℕ × Fin r) (rest : List (ℕ × Fin r)) :
    wordStateN (ia :: rest) = X ia * wordStateN rest := rfl

/-- **VA3, general creation — both clauses, for every word `l`.** -/
theorem YwordN_creation (r : ℕ) (k : ℂ) (l : List (ℕ × Fin r)) :
    (∀ j : ℤ, j < 0 → YwordN r k l j (vacuumN r) = 0)
      ∧ YwordN r k l 0 (vacuumN r) = wordStateN l := by
  induction l with
  | nil =>
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [YwordN_nil, idFieldN_apply, if_neg (by omega)]; rfl
    · rw [YwordN_nil, idFieldN_apply, if_pos rfl, wordStateN_nil]; rfl
  | cons ia rest ih =>
    obtain ⟨ih_lt, ih_zero⟩ := ih
    have ha_neg : ∀ m : ℤ, m < 0 → genFieldN r k ia.2 ia.1 m (vacuumN r) = 0 := fun m hm =>
      genFieldN_neg_vacuum r k ia.2 ia.1 hm
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [YwordN_cons]
      exact nprodN_creation_lt (genFieldN_isField r k ia.2 ia.1) (YwordN_isField r k rest)
        ih_lt ha_neg hj
    · rw [YwordN_cons,
        nprodN_creation_zero (genFieldN_isField r k ia.2 ia.1) (YwordN_isField r k rest)
          ih_lt ha_neg]
      rw [ih_zero, genFieldN_zero_apply, wordStateN_cons]

theorem YwordN_creation_lt (r : ℕ) (k : ℂ) (l : List (ℕ × Fin r)) {j : ℤ} (hj : j < 0) :
    YwordN r k l j (vacuumN r) = 0 := (YwordN_creation r k l).1 j hj

theorem YwordN_creation_zero (r : ℕ) (k : ℂ) (l : List (ℕ × Fin r)) :
    YwordN r k l 0 (vacuumN r) = wordStateN l := (YwordN_creation r k l).2

/-- The created state of `monoWordN a` is the monomial `∏ X^{a}` of `a`. -/
theorem wordStateN_monoWordN (a : (ℕ × Fin r) →₀ ℕ) : wordStateN (monoWordN a) = monomial a 1 := by
  rw [wordStateN, monoWordN]
  rw [← Multiset.prod_coe, ← Multiset.map_coe, ← Multiset.coe_bind,
    Finset.coe_toList, Multiset.map_bind, Multiset.prod_bind]
  have hinner : ∀ ia : ℕ × Fin r,
      (Multiset.map (fun ia => (X ia : FockN r)) (Multiset.replicate (a ia) ia)).prod
        = X ia ^ a ia := by
    intro ia; rw [Multiset.map_replicate, Multiset.prod_replicate]
  simp only [Multiset.coe_replicate, hinner]
  rw [show (Multiset.map (fun ia => (X ia : FockN r) ^ a ia) a.support.val).prod
        = ∏ ia ∈ a.support, (X ia : FockN r) ^ a ia from rfl]
  rw [monomial_eq, map_one, one_mul, Finsupp.prod]

theorem YmonN_creation_lt (r : ℕ) (k : ℂ) (a : (ℕ × Fin r) →₀ ℕ) {j : ℤ} (hj : j < 0) :
    YmonN r k a j (vacuumN r) = 0 := YwordN_creation_lt r k (monoWordN a) hj

theorem YmonN_creation_zero (r : ℕ) (k : ℂ) (a : (ℕ × Fin r) →₀ ℕ) :
    YmonN r k a 0 (vacuumN r) = monomial a 1 := by
  rw [YmonN, YwordN_creation_zero, wordStateN_monoWordN]

/-! ### VA3 for every state, by linearity -/

/-- The "evaluate at `z`-power `j`, then act on the vacuum" functional, as a `ℂ`-linear map. -/
noncomputable def evalVacAtN (r : ℕ) (j : ℤ) :
    FormalDist (End ℂ (FockN r)) →ₗ[ℂ] FockN r where
  toFun f := f j (vacuumN r)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evalVacAtN_apply (r : ℕ) (j : ℤ) (f : FormalDist (End ℂ (FockN r))) :
    evalVacAtN r j f = f j (vacuumN r) := rfl

theorem YN_apply_vacuum_sum (r : ℕ) (k : ℂ) (u : FockN r) (j : ℤ) :
    YN r k u j (vacuumN r) = u.sum (fun a c => c • (YmonN r k a j (vacuumN r))) := by
  show evalVacAtN r j (YN r k u) = _
  show evalVacAtN r j (Finsupp.linearCombination ℂ (YmonN r k) u) = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, evalVacAtN_apply]

/-- **VA3 / general creation, `j < 0`, every state**: `YN(u,z)_j 1 = 0` for `j < 0`. -/
theorem YN_creation_lt (r : ℕ) (k : ℂ) (u : FockN r) {j : ℤ} (hj : j < 0) :
    YN r k u j (vacuumN r) = 0 := by
  rw [YN_apply_vacuum_sum, Finsupp.sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [YmonN_creation_lt r k a hj, smul_zero]

/-- **VA3 / the `z⁰`-coefficient creates `u`, every state**: `YN(u,0)1 = u`. -/
theorem YN_creation_zero (r : ℕ) (k : ℂ) (u : FockN r) : YN r k u 0 (vacuumN r) = u := by
  rw [YN_apply_vacuum_sum]
  rw [show u.sum (fun a c => c • (YmonN r k a 0 (vacuumN r)))
        = u.sum (fun a c => monomial a c) from
      Finsupp.sum_congr fun a _ => by
        rw [YmonN_creation_zero, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff u]
  rw [Finsupp.sum]
  rfl

/-- **VA3, mode form (regularity)**: `u₍ₙ₎1 = 0` for `n ≥ 0`, every state. -/
theorem mode_YN_creation_nonneg (r : ℕ) (k : ℂ) (u : FockN r) {n : ℤ} (hn : 0 ≤ n) :
    mode (YN r k u) n (vacuumN r) = 0 := by
  rw [mode_apply]; exact YN_creation_lt r k u (by omega)

/-- **VA3, mode form (the `(-1)`-mode creates `u`)**: `u₍₋₁₎1 = u`. -/
theorem mode_YN_creation_neg_one (r : ℕ) (k : ℂ) (u : FockN r) :
    mode (YN r k u) (-1) (vacuumN r) = u := by
  rw [mode_apply, show (-(-1 : ℤ) - 1) = 0 from by ring]; exact YN_creation_zero r k u

/-- **The full VA3 statement** for the rank-`r` Heisenberg Fock space. -/
theorem YN_creation (r : ℕ) (k : ℂ) (u : FockN r) :
    mode (YN r k u) (-1) (vacuumN r) = u
      ∧ ∀ n : ℤ, 0 ≤ n → mode (YN r k u) n (vacuumN r) = 0 :=
  ⟨mode_YN_creation_neg_one r k u, fun _ hn => mode_YN_creation_nonneg r k u hn⟩

/-! ## §6  VA1/VA5 — the `ℤ`-graded grading and the regularity / grading laws -/

/-- The `ℤ`-extension of the Fock grading: `gradingWN w` in non-negative weight, `⊥` below. -/
noncomputable def gradingZN (r : ℕ) (n : ℤ) : Submodule ℂ (FockN r) :=
  if 0 ≤ n then gradingWN r n.toNat else ⊥

theorem gradingZN_of_nonneg {r : ℕ} {n : ℤ} (hn : 0 ≤ n) :
    gradingZN r n = gradingWN r n.toNat := by
  rw [gradingZN, if_pos hn]

theorem gradingZN_of_neg {r : ℕ} {n : ℤ} (hn : n < 0) : gradingZN r n = ⊥ := by
  rw [gradingZN, if_neg (by omega)]

theorem mem_gradingZN_of_gradingWN {r : ℕ} {w : ℕ} {p : FockN r} (hp : p ∈ gradingWN r w) :
    p ∈ gradingZN r (w : ℤ) := by
  rw [gradingZN_of_nonneg (by positivity), Int.toNat_natCast]; exact hp

theorem zero_mem_gradingZN (r : ℕ) (n : ℤ) : (0 : FockN r) ∈ gradingZN r n :=
  (gradingZN r n).zero_mem

/-! ### VA5 — regularity -/

theorem IsFieldN.zero (r : ℕ) : IsField (0 : FormalDist (End ℂ (FockN r))) := by
  intro x; exact ⟨0, fun n _ => by show (0 : FormalDist (End ℂ (FockN r))) n x = 0; rfl⟩

theorem IsFieldN.add {r : ℕ} {a b : FormalDist (End ℂ (FockN r))} (ha : IsField a)
    (hb : IsField b) : IsField (a + b) := by
  intro x
  obtain ⟨Ba, hBa⟩ := ha x
  obtain ⟨Bb, hBb⟩ := hb x
  refine ⟨min Ba Bb, fun n hn => ?_⟩
  show a n x + b n x = 0
  rw [hBa n (lt_of_lt_of_le hn (min_le_left _ _)), hBb n (lt_of_lt_of_le hn (min_le_right _ _)),
    add_zero]

theorem IsFieldN.smul {r : ℕ} (c : ℂ) {a : FormalDist (End ℂ (FockN r))} (ha : IsField a) :
    IsField (c • a) := by
  intro x
  obtain ⟨B, hB⟩ := ha x
  refine ⟨B, fun n hn => ?_⟩
  show c • a n x = 0
  rw [hB n hn, smul_zero]

theorem IsFieldN.finsetSum {r : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → FormalDist (End ℂ (FockN r))) (hf : ∀ i ∈ s, IsField (f i)) :
    IsField (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (IsFieldN.zero r)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact IsFieldN.add (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- **`YN k u` is a field for every `u`**. -/
theorem YN_isField (r : ℕ) (k : ℂ) (u : FockN r) : IsField (YN r k u) := by
  classical
  rw [show YN r k u = Finsupp.linearCombination ℂ (YmonN r k) u from rfl,
      Finsupp.linearCombination_apply, Finsupp.sum]
  exact IsFieldN.finsetSum _ _ (fun a _ => IsFieldN.smul _ (YmonN_isField r k a))

/-- **VA5 (regularity).**  For every `u, v` the products `u₍ₙ₎v` vanish for all large `n`. -/
theorem va5N_regularity (r : ℕ) (k : ℂ) (u v : FockN r) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (YN r k u) n v = 0 := by
  obtain ⟨B, hB⟩ := YN_isField r k u v
  refine ⟨-B, fun n hn => ?_⟩
  rw [mode_apply]
  exact hB (-n - 1) (by omega)

/-! ### The oscillator is grading-covariant: `oscN k a n : F_w → F_{w-n}` -/

theorem pderivN_eq_zero_of_weight_lt {r : ℕ} {v : ℕ × Fin r} {w : ℕ} {p : FockN r}
    (hp : p ∈ gradingWN r w) (hlt : w < weightFnN v) : pderiv v p = 0 := by
  classical
  apply pderiv_eq_zero_of_notMem_vars
  intro hi
  rw [MvPolynomial.mem_vars_iff_mem_support] at hi
  obtain ⟨d, hd, hid⟩ := hi
  rw [mem_gradingWN] at hp
  have hwd : Finsupp.weight weightFnN d = w := hp (MvPolynomial.mem_support_iff.mp hd)
  have hle : weightFnN v ≤ Finsupp.weight weightFnN d :=
    Finsupp.le_weight_of_ne_zero' (w := weightFnN) (Finsupp.mem_support_iff.mp hid)
  omega

/-- **`oscN k a n` is grading-covariant**: it shifts weight by `-n`. -/
theorem oscN_mem_gradingZN (r : ℕ) (k : ℂ) (a : Fin r) (n : ℤ) {w : ℕ} {p : FockN r}
    (hp : p ∈ gradingWN r w) : oscN r k a n p ∈ gradingZN r ((w : ℤ) - n) := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have h := oscN_neg_weight r k a hn hp
    have hcast : ((w + (-n).toNat : ℕ) : ℤ) = (w : ℤ) - n := by
      rw [Nat.cast_add, Int.toNat_of_nonneg (by omega)]; ring
    rw [← hcast]; exact mem_gradingZN_of_gradingWN h
  · subst hn
    rw [oscN_zero, LinearMap.zero_apply, sub_zero]
    exact zero_mem_gradingZN r _
  · by_cases hwn : (n : ℤ) ≤ w
    · have h := oscN_pos_weight r k a hn (w := w) (w' := w - n.toNat) (by omega) hp
      have hcast : ((w - n.toNat : ℕ) : ℤ) = (w : ℤ) - n := by
        rw [Nat.cast_sub (by omega), Int.toNat_of_nonneg (le_of_lt hn)]
      rw [← hcast]; exact mem_gradingZN_of_gradingWN h
    · have hpd : pderiv ((n - 1).toNat, a) p = 0 := by
        apply pderivN_eq_zero_of_weight_lt hp
        rw [weightFnN_apply, show ((n - 1).toNat, a).1 = (n - 1).toNat from rfl,
          show (n - 1).toNat + 1 = n.toNat from by omega]
        omega
      rw [oscN_apply_pos r k a hn, hpd, smul_zero, smul_zero]
      exact zero_mem_gradingZN r _

/-! ### The basic graded fields and the graded-field structure -/

/-- A **graded field of weight `D`**: each coefficient `a j` sends `F_w` into `F_{D+w+j}`. -/
def GradedFieldN (r : ℕ) (a : FormalDist (End ℂ (FockN r))) (D : ℤ) : Prop :=
  ∀ (j : ℤ) (w : ℕ) (p : FockN r), p ∈ gradingWN r w → a j p ∈ gradingZN r (D + w + j)

theorem idFieldN_gradedField (r : ℕ) : GradedFieldN r (idFieldN r) 0 := by
  intro j w p hp
  rw [idFieldN_apply]
  by_cases hj : j = 0
  · rw [if_pos hj, LinearMap.id_apply, hj]
    simpa using mem_gradingZN_of_gradingWN hp
  · rw [if_neg hj, LinearMap.zero_apply]
    exact zero_mem_gradingZN r _

/-- The `zʲ`-coefficient of `genFieldN k a i` is a falling-factorial smul of `oscN k a (-j-1-i)`. -/
theorem genFieldN_coeff' (r : ℕ) (k : ℂ) (a : Fin r) (i : ℕ) (j : ℤ) :
    (genFieldN r k a i) j =
      (i.factorial : ℂ)⁻¹ •
        ((∏ p ∈ Finset.range i, (-(-j - 1 - (p : ℤ)))) • oscN r k a (-j - 1 - i)) := by
  have hmode : (genFieldN r k a i) j = mode (genFieldN r k a i) (-j - 1) := by
    rw [mode_apply]; congr 1; ring
  rw [hmode, genFieldN, mode_smul, dcurrentN_mode]

/-- **`genFieldN k a i` is a graded field of weight `i+1`**. -/
theorem genFieldN_gradedField (r : ℕ) (k : ℂ) (a : Fin r) (i : ℕ) :
    GradedFieldN r (genFieldN r k a i) ((i : ℤ) + 1) := by
  intro j w p hp
  rw [genFieldN_coeff']
  set c : ℂ := (i.factorial : ℂ)⁻¹ *
    (((∏ p ∈ Finset.range i, (-(-j - 1 - (p : ℤ)))) : ℤ) : ℂ) with hc
  have hcoeff : (i.factorial : ℂ)⁻¹ •
        ((∏ p ∈ Finset.range i, (-(-j - 1 - (p : ℤ)))) • oscN r k a (-j - 1 - i))
      = c • oscN r k a (-j - 1 - i) := by
    rw [hc, mul_smul, Int.cast_smul_eq_zsmul]
  rw [hcoeff, LinearMap.smul_apply]
  have hosc : oscN r k a (-j - 1 - i) p ∈ gradingZN r ((w : ℤ) - (-j - 1 - i)) :=
    oscN_mem_gradingZN r k a (-j - 1 - i) hp
  have htgt : ((w : ℤ) - (-j - 1 - i)) = (i : ℤ) + 1 + w + j := by ring
  rw [htgt] at hosc
  exact (gradingZN r _).smul_mem _ hosc

/-- A finite-support finsum of submodule elements lies in the submodule. -/
theorem finsumN_mem_submodule {r : ℕ} {ι : Type*} (S : Submodule ℂ (FockN r)) (g : ι → FockN r)
    (hfin : (Function.support g).Finite) (hmem : ∀ i, g i ∈ S) : (∑ᶠ i, g i) ∈ S := by
  rw [finsum_eq_finsetSum_of_support_subset g (s := hfin.toFinset)
    (by rw [hfin.coe_toFinset])]
  exact Submodule.sum_mem _ (fun i _ => hmem i)

/-- The `gradingZN`-input form of `GradedFieldN`. -/
theorem GradedFieldN.mem_gradingZN {r : ℕ} {a : FormalDist (End ℂ (FockN r))} {D : ℤ}
    (hga : GradedFieldN r a D) (j d : ℤ) {p : FockN r} (hp : p ∈ gradingZN r d) :
    a j p ∈ gradingZN r (D + d + j) := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [gradingZN_of_neg hd, Submodule.mem_bot] at hp
    rw [hp, map_zero]; exact zero_mem_gradingZN r _
  · rw [gradingZN_of_nonneg hd] at hp
    have := hga j d.toNat p hp
    rwa [Int.toNat_of_nonneg hd] at this

/-- **The normal-ordered product of graded fields is a graded field**, with weights adding. -/
theorem GradedFieldN.nprod {r : ℕ} {a b : FormalDist (End ℂ (FockN r))} (ha : IsField a)
    (hb : IsField b) {Da Db : ℤ} (hga : GradedFieldN r a Da) (hgb : GradedFieldN r b Db) :
    GradedFieldN r (nprod ha hb) (Da + Db) := by
  intro s w p hp
  rw [nprod_apply]
  apply finsumN_mem_submodule
  · exact normalOrdered_diag_support_finite ha hb s p
  · intro m
    rw [normalOrdered_apply]
    have hpz : p ∈ gradingZN r (w : ℤ) := mem_gradingZN_of_gradingWN hp
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0]
      show a m (b (s - m) p) ∈ gradingZN r (Da + Db + w + s)
      have hb' := hgb.mem_gradingZN (s - m) (w : ℤ) hpz
      have ha' := hga.mem_gradingZN m (Db + w + (s - m)) hb'
      have htgt : Da + (Db + (w : ℤ) + (s - m)) + m = Da + Db + w + s := by ring
      rwa [htgt] at ha'
    · rw [if_neg h0]
      show b (s - m) (a m p) ∈ gradingZN r (Da + Db + w + s)
      have ha' := hga.mem_gradingZN m (w : ℤ) hpz
      have hb' := hgb.mem_gradingZN (s - m) (Da + w + m) ha'
      have htgt : Db + (Da + (w : ℤ) + m) + (s - m) = Da + Db + w + s := by ring
      rwa [htgt] at hb'

/-! ### Words and monomials are graded fields of the state weight -/

/-- The (ℕ-valued) weight of a word `l`: the sum of the generator weights `∑ (iₜ+1)`. -/
def wordWeightNN (l : List (ℕ × Fin r)) : ℕ := (l.map (fun ia => ia.1 + 1)).sum

/-- The weight of a word, as an integer. -/
def wordWeightN (l : List (ℕ × Fin r)) : ℤ := (wordWeightNN l : ℤ)

@[simp] theorem wordWeightNN_nil : wordWeightNN ([] : List (ℕ × Fin r)) = 0 := rfl

@[simp] theorem wordWeightN_nil : wordWeightN ([] : List (ℕ × Fin r)) = 0 := rfl

theorem wordWeightNN_cons (ia : ℕ × Fin r) (rest : List (ℕ × Fin r)) :
    wordWeightNN (ia :: rest) = (ia.1 + 1) + wordWeightNN rest := by
  simp only [wordWeightNN, List.map_cons, List.sum_cons]

theorem wordWeightN_cons (ia : ℕ × Fin r) (rest : List (ℕ × Fin r)) :
    wordWeightN (ia :: rest) = ((ia.1 : ℤ) + 1) + wordWeightN rest := by
  rw [wordWeightN, wordWeightN, wordWeightNN_cons]; push_cast; ring

/-- **`YwordN k l` is a graded field of weight `wordWeightN l`**. -/
theorem YwordN_gradedField (r : ℕ) (k : ℂ) :
    ∀ l : List (ℕ × Fin r), GradedFieldN r (YwordN r k l) (wordWeightN l)
  | [] => by rw [YwordN_nil, wordWeightN_nil]; exact idFieldN_gradedField r
  | (ia :: rest) => by
      rw [YwordN_cons, wordWeightN_cons]
      exact GradedFieldN.nprod (genFieldN_isField r k ia.2 ia.1) (YwordN_isField r k rest)
        (genFieldN_gradedField r k ia.2 ia.1) (YwordN_gradedField r k rest)

theorem wordWeightNN_append (l₁ l₂ : List (ℕ × Fin r)) :
    wordWeightNN (l₁ ++ l₂) = wordWeightNN l₁ + wordWeightNN l₂ := by
  rw [wordWeightNN, wordWeightNN, wordWeightNN, List.map_append, List.sum_append]

theorem wordWeightNN_flatMap (L : List (ℕ × Fin r)) (g : (ℕ × Fin r) → List (ℕ × Fin r)) :
    wordWeightNN (L.flatMap g) = (L.map (fun ia => wordWeightNN (g ia))).sum := by
  induction L with
  | nil => simp [wordWeightNN]
  | cons ia rest ih =>
    rw [List.flatMap_cons, wordWeightNN_append, List.map_cons, List.sum_cons, ih]

theorem wordWeightNN_replicate (n : ℕ) (ia : ℕ × Fin r) :
    wordWeightNN (List.replicate n ia) = n * (ia.1 + 1) := by
  rw [wordWeightNN, List.map_replicate, List.sum_replicate, smul_eq_mul]

theorem wordWeightNN_monoWordN (a : (ℕ × Fin r) →₀ ℕ) :
    wordWeightNN (monoWordN a) = ∑ ia ∈ a.support, (a ia * (ia.1 + 1)) := by
  classical
  rw [monoWordN, wordWeightNN_flatMap]
  have hmap : a.support.toList.map
        (fun ia => wordWeightNN (List.replicate (a ia) ia))
       = a.support.toList.map (fun ia => (a ia * (ia.1 + 1))) :=
    List.map_congr_left (fun ia _ => wordWeightNN_replicate (a ia) ia)
  rw [hmap, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
  rfl

theorem wordWeightNN_monoWordN_eq_weight (a : (ℕ × Fin r) →₀ ℕ) :
    wordWeightNN (monoWordN a) = Finsupp.weight weightFnN a := by
  rw [wordWeightNN_monoWordN, Finsupp.weight_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro ia _
  rw [weightFnN_apply, smul_eq_mul]

/-- **`YmonN k a` is a graded field of the monomial's weighted degree**. -/
theorem YmonN_gradedField (r : ℕ) (k : ℂ) (a : (ℕ × Fin r) →₀ ℕ) :
    GradedFieldN r (YmonN r k a) ((Finsupp.weight weightFnN a : ℕ) : ℤ) := by
  rw [YmonN, ← wordWeightNN_monoWordN_eq_weight]
  exact YwordN_gradedField r k (monoWordN a)

/-! ### VA1 — the grading axiom for the general vertex operator -/

/-- **`YN k u` is a graded field of weight `w`** whenever `u ∈ F_w`. -/
theorem YN_gradedField_of_mem (r : ℕ) (k : ℂ) {w : ℕ} {u : FockN r} (hu : u ∈ gradingWN r w) :
    GradedFieldN r (YN r k u) (w : ℤ) := by
  classical
  intro j w' p hp
  rw [show YN r k u = Finsupp.linearCombination ℂ (YmonN r k) u from rfl,
      Finsupp.linearCombination_apply, Finsupp.sum]
  show (∑ a ∈ u.support, (u a) • YmonN r k a) j p ∈ gradingZN r ((w : ℤ) + w' + j)
  have hsum : (∑ a ∈ u.support, (u a) • YmonN r k a) j p
      = ∑ a ∈ u.support, ((u a) • YmonN r k a) j p := by
    rw [show ((∑ a ∈ u.support, (u a) • YmonN r k a) j : End ℂ (FockN r))
          = ∑ a ∈ u.support, ((u a) • YmonN r k a) j from
        (Finset.sum_apply (s := u.support) (g := fun a => (u a) • YmonN r k a) j),
      LinearMap.sum_apply]
  rw [hsum]
  apply Submodule.sum_mem
  intro a ha
  show ((u a) • YmonN r k a) j p ∈ gradingZN r ((w : ℤ) + w' + j)
  have heval : ((u a) • YmonN r k a) j p = (u a) • (YmonN r k a j p) := rfl
  rw [heval]
  have hcoeff : u.coeff a ≠ 0 := by
    rw [MvPolynomial.coeff]
    exact Finsupp.mem_support_iff.mp ha
  have hwa : Finsupp.weight weightFnN a = w := by
    rw [mem_gradingWN] at hu; exact hu hcoeff
  have hYmon : (YmonN r k a) j p ∈ gradingZN r (((Finsupp.weight weightFnN a : ℕ) : ℤ) + w' + j) :=
    YmonN_gradedField r k a j w' p hp
  rw [hwa] at hYmon
  exact (gradingZN r _).smul_mem _ hYmon

/-- **VA1 (grading), the structure-field form** with the `ℤ`-extended grading `gradingZN`. -/
theorem va1N_grading_mode (r : ℕ) (kk : ℂ) {k ℓ : ℤ} (u : FockN r) (hu : u ∈ gradingZN r k)
    (v : FockN r) (hv : v ∈ gradingZN r ℓ) (n : ℤ) :
    mode (YN r kk u) n v ∈ gradingZN r (k + ℓ - n - 1) := by
  rcases lt_or_ge k 0 with hk | hk
  · rw [gradingZN_of_neg hk, Submodule.mem_bot] at hu
    rw [hu, map_zero, mode_apply]
    show (0 : FormalDist (End ℂ (FockN r))) (-n - 1) v ∈ _
    rw [show (0 : FormalDist (End ℂ (FockN r))) (-n - 1) = 0 from rfl, LinearMap.zero_apply]
    exact zero_mem_gradingZN r _
  · rw [gradingZN_of_nonneg hk] at hu
    have hgf := YN_gradedField_of_mem r kk hu
    rw [mode_apply]
    have := hgf.mem_gradingZN (-n - 1) ℓ hv
    rw [Int.toNat_of_nonneg hk] at this
    have htgt : k + ℓ + (-n - 1) = k + ℓ - n - 1 := by ring
    rwa [htgt] at this

/-! ### VA1 `isInternal` — the internal direct-sum decomposition -/

theorem gradingWN_isInternal (r : ℕ) : DirectSum.IsInternal (gradingWN r) :=
  (MvPolynomial.weightedDecomposition ℂ (weightFnN (r := r))).isInternal

theorem gradingWN_iSupIndep (r : ℕ) : iSupIndep (gradingWN r) :=
  (gradingWN_isInternal r).submodule_iSupIndep

theorem gradingWN_iSup_eq_top (r : ℕ) : iSup (gradingWN r) = ⊤ :=
  (gradingWN_isInternal r).submodule_iSup_eq_top

theorem gradingZN_iSupIndep (r : ℕ) : iSupIndep (gradingZN r) := by
  rw [← iSupIndep_ne_bot]
  have hfinj : Function.Injective
      (fun i : {n : ℤ // gradingZN r n ≠ ⊥} => i.1.toNat) := by
    rintro ⟨m, hm⟩ ⟨n, hn⟩ h
    have hm0 : 0 ≤ m := by
      by_contra hlt; exact hm (gradingZN_of_neg (lt_of_not_ge hlt))
    have hn0 : 0 ≤ n := by
      by_contra hlt; exact hn (gradingZN_of_neg (lt_of_not_ge hlt))
    have h' : m.toNat = n.toNat := h
    have hmn : m = n := by
      rw [← Int.toNat_of_nonneg hm0, ← Int.toNat_of_nonneg hn0, h']
    exact Subtype.ext hmn
  have hcomp : (fun i : {n : ℤ // gradingZN r n ≠ ⊥} => gradingZN r i.1)
      = gradingWN r ∘ (fun i : {n : ℤ // gradingZN r n ≠ ⊥} => i.1.toNat) := by
    funext i
    obtain ⟨n, hn⟩ := i
    have hn0 : 0 ≤ n := by
      by_contra hlt; exact hn (gradingZN_of_neg (lt_of_not_ge hlt))
    simp only [Function.comp_apply]
    exact gradingZN_of_nonneg hn0
  rw [hcomp]
  exact (gradingWN_iSupIndep r).comp hfinj

theorem gradingZN_iSup_eq_top (r : ℕ) : iSup (gradingZN r) = ⊤ := by
  rw [eq_top_iff, ← gradingWN_iSup_eq_top r]
  refine iSup_le (fun w => ?_)
  have h : gradingWN r w = gradingZN r (w : ℤ) := by
    rw [gradingZN_of_nonneg (by positivity), Int.toNat_natCast]
  rw [h]
  exact le_iSup (gradingZN r) (w : ℤ)

/-- **VA1 `isInternal`.**  The `ℤ`-extended Fock grading `gradingZN` is a genuine internal
direct-sum decomposition `FockN r = ⊕ₙ gradingZN n` (with `gradingZN n = ⊥` for `n < 0`). -/
theorem gradingZN_isInternal (r : ℕ) : DirectSum.IsInternal (gradingZN r) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (gradingZN_iSupIndep r) (gradingZN_iSup_eq_top r)

/-! ### finrank — each graded piece is finite-dimensional -/

/-- The set of weight-`w` exponent vectors. -/
def weightDegSetN (r w : ℕ) : Set ((ℕ × Fin r) →₀ ℕ) :=
  {d : (ℕ × Fin r) →₀ ℕ | Finsupp.weight weightFnN d = w}

theorem weightDegSetN_entry_le {r w : ℕ} {d : (ℕ × Fin r) →₀ ℕ} (hd : d ∈ weightDegSetN r w)
    (i : ℕ × Fin r) : d i ≤ w := by
  have hle : d i ≤ Finsupp.weight weightFnN d :=
    Finsupp.le_weight weightFnN (by rw [weightFnN_apply]; omega) d
  rw [show Finsupp.weight weightFnN d = w from hd] at hle
  exact hle

theorem weightDegSetN_support_lt {r w : ℕ} {d : (ℕ × Fin r) →₀ ℕ} (hd : d ∈ weightDegSetN r w)
    {i : ℕ × Fin r} (hi : d i ≠ 0) : i.1 < w := by
  have hle : weightFnN i ≤ Finsupp.weight weightFnN d := Finsupp.le_weight_of_ne_zero' weightFnN hi
  rw [show Finsupp.weight weightFnN d = w from hd, weightFnN_apply] at hle
  omega

/-- **The weight-`w` exponent vectors form a finite set** (inject into `Fin w × Fin r → Fin (w+1)`). -/
theorem weightDegSetN_finite (r w : ℕ) : (weightDegSetN r w).Finite := by
  classical
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective
    (β := Fin w × Fin r → Fin (w + 1))
    (fun d i => ⟨d.1 (i.1, i.2), by
      have := weightDegSetN_entry_le d.2 (i.1, i.2); omega⟩) ?_
  rintro ⟨d, hd⟩ ⟨e, he⟩ h
  refine Subtype.ext (Finsupp.ext fun i => ?_)
  by_cases hiw : i.1 < w
  · have := congrFun h ⟨⟨i.1, hiw⟩, i.2⟩
    simpa using congrArg Fin.val this
  · have hdz : d i = 0 := by
      by_contra hne; exact hiw (weightDegSetN_support_lt hd hne)
    have hez : e i = 0 := by
      by_contra hne; exact hiw (weightDegSetN_support_lt he hne)
    rw [hdz, hez]

/-- The (finite) set of weight-`w` monomials `monomial d 1`. -/
noncomputable def weightMonSetN (r w : ℕ) : Set (FockN r) :=
  (fun d => (monomial d 1 : FockN r)) '' weightDegSetN r w

theorem weightMonSetN_finite (r w : ℕ) : (weightMonSetN r w).Finite :=
  (weightDegSetN_finite r w).image _

theorem gradingWN_le_span (r w : ℕ) :
    gradingWN r w ≤ Submodule.span ℂ (weightMonSetN r w) := by
  intro p hp
  rw [mem_gradingWN] at hp
  rw [MvPolynomial.as_sum p]
  refine Submodule.sum_mem _ (fun d hd => ?_)
  have hdw : Finsupp.weight weightFnN d = w := hp (MvPolynomial.mem_support_iff.mp hd)
  have hmem : (monomial d 1 : FockN r) ∈ weightMonSetN r w := ⟨d, hdw, rfl⟩
  have hscale : (monomial d (MvPolynomial.coeff d p) : FockN r)
      = (MvPolynomial.coeff d p) • monomial d 1 := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hscale]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem gradingWN_finiteDimensional (r w : ℕ) : FiniteDimensional ℂ (gradingWN r w) := by
  have hspan : FiniteDimensional ℂ (Submodule.span ℂ (weightMonSetN r w)) :=
    FiniteDimensional.span_of_finite ℂ (weightMonSetN_finite r w)
  exact Submodule.finiteDimensional_of_le (gradingWN_le_span r w)

/-- **finrank.**  Each `ℤ`-graded piece `gradingZN n` is finite-dimensional. -/
theorem gradingZN_finrank (r : ℕ) (n : ℤ) : FiniteDimensional ℂ (gradingZN r n) := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [gradingZN_of_neg hn]; infer_instance
  · rw [gradingZN_of_nonneg hn]; exact gradingWN_finiteDimensional r n.toNat

/-! ### VOA4a `vacuum_grade` and `positivity` -/

theorem gradingWN_zero_eq_span_one (r : ℕ) : gradingWN r 0 = ℂ ∙ (1 : FockN r) := by
  apply le_antisymm
  · intro p hp
    rw [mem_gradingWN] at hp
    have hconst : p = MvPolynomial.C (MvPolynomial.coeff 0 p) := by
      apply MvPolynomial.ext
      intro d
      rw [MvPolynomial.coeff_C]
      by_cases hd : d = 0
      · rw [if_pos hd.symm, hd]
      · rw [if_neg (Ne.symm hd)]
        by_contra hne
        apply hd
        have hdw : Finsupp.weight weightFnN d = 0 := hp hne
        refine Finsupp.ext (fun i => ?_)
        by_contra hdi
        have hle : weightFnN i ≤ Finsupp.weight weightFnN d :=
          Finsupp.le_weight_of_ne_zero' weightFnN hdi
        rw [hdw, weightFnN_apply] at hle
        omega
    rw [hconst, show (MvPolynomial.C (MvPolynomial.coeff 0 p) : FockN r)
        = (MvPolynomial.coeff 0 p) • 1 from by rw [smul_eq_C_mul, mul_one]]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact isWeightedHomogeneous_one ℂ weightFnN

/-- **VOA4a `vacuum_grade`.**  `gradingZN 0 = ℂ ∙ vacuumN`. -/
theorem gradingZN_zero_eq_span_vacuum (r : ℕ) : gradingZN r 0 = ℂ ∙ vacuumN r := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, gradingZN_of_nonneg (by norm_num),
      Int.toNat_natCast, gradingWN_zero_eq_span_one, vacuumN]

/-- **VOA4 `positivity`.**  `gradingZN n = ⊥` for `n < 0`. -/
theorem gradingZN_positivity (r : ℕ) (n : ℤ) (hn : n < 0) : gradingZN r n = ⊥ :=
  gradingZN_of_neg hn

/-! ## §7  Axiom audit -/


end HeisenbergN

end VOA
