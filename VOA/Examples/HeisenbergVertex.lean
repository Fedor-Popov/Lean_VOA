/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergFock
import VOA.Core.Dong
import VOA.Core.FieldOps
import VOA.Core.Reconstruction
import VOA.Foundations.Locality
import VOA.Core.Identities

/-!
# FRONT A — the general vertex-operator map `Y(u,z)` on the Heisenberg Fock space

Building on the Fock layer (`Examples.HeisenbergFock`: the basic current `α(z)`, its modes the
oscillators, and its self-locality), this file constructs the **general** vertex operator
`Y(u,z)` for every state `u` of the rank-1 Heisenberg Fock space, as a `ℂ`-linear map
`Y : Fock →ₗ[ℂ] FormalDist (End ℂ Fock)`, together with its core properties.

## The construction (Gannon §5.2)

* **Derivative currents** `dcurrent k j := ∂_z^j α(z)` (the `j`-th formal derivative of the
  basic current).  Its mode is a falling-factorial multiple of an oscillator
  (`dcurrent_mode`); it is a field (`dcurrent_isField`); and any two derivative currents are
  mutually local (`dcurrent_local`).  The scaled field `genField k i := (i!)⁻¹·∂^i α` is
  `Y(a₋(i+1)1, z)` (Gannon 5.2.5).
* **`Y` on monomials.**  For a monomial `a₋(i₁+1)…a₋(iᵣ+1)1` (encoded by its exponent
  vector `a : ℕ →₀ ℕ`) the field `Ymon k a` is the iterated normal-ordered product
  (`Core.Dong.nprod`) of the `genField`s, with the `(1/(mⱼ-1)!)` factors built into each
  `genField`.  `Y` is the `ℂ`-linear extension of `Ymon` (`Finsupp.linearCombination`).
* **VA2 / the identity field** `Y(1,z) = idField = id·z⁰`  (`Y_vacuum`).
* **The basic current** `Y(a₋₁1,z) = α(z)`  (`Y_current`).
* **Creation / VA3** the regularity of `Y(u,z)` on the vacuum (`Y_creation_vacuum_lt`,
  `Y_creation_vacuum_zero`): `(Y(u,z))_j 1 = 0` for `j < 0` and the `z⁰`-coefficient creates `u`.
* **Locality / VA4** every two monomial fields are mutually local (`Yword_local`,
  `Ymon_local`), assembled by iterating Dong's lemma (`dong_neg`) over the generators.

## Status
Scratch (Front A).  Fully axiom-clean (`#print axioms` = `[propext, Classical.choice,
Quot.sound]`) for every declaration below.

## References
* Gannon §5.2.2 (5.2.5); FLM Ch. 8; Kac §3.5; Lepowsky–Li Ch. 6.
-/

namespace VOA

open scoped BigOperators
open MvPolynomial
open Module (End)

universe u

variable {V : Type*} [AddCommGroup V] [Module ℂ V]



/-! ## §3  The derivative currents `dcurrent k j = ∂_z^j α(z)` -/

/-- The **derivative currents** `dcurrent k j := ∂_z^j α(z)`, the `j`-th formal derivative of
the basic current `α(z) = Y(a₋₁1, z)` (Gannon 5.2.5). -/
noncomputable def dcurrent (k : ℂ) (j : ℕ) : FormalDist (End ℂ Fock) :=
  (deriv^[j]) (current k)

@[simp] theorem dcurrent_zero (k : ℂ) : dcurrent k 0 = current k := rfl

theorem dcurrent_succ (k : ℂ) (j : ℕ) : dcurrent k (j + 1) = deriv (dcurrent k j) := by
  rw [dcurrent, dcurrent, Function.iterate_succ', Function.comp_apply]

/-- **The basic current is a field**: `α(z)` is lower-truncated (its high annihilation modes
`aₙ` vanish on any fixed polynomial once `n` exceeds its variable indices). -/
theorem current_isField (k : ℂ) : IsField (current k) := by
  intro p
  refine ⟨-(((p.vars.sup id : ℕ) : ℤ)) - 2, fun n hn => ?_⟩
  rw [current_apply]
  have hpos : 0 < -n - 1 := by omega
  rw [osc_apply_pos k hpos]
  have hzero : pderiv (-n - 1 - 1).toNat p = 0 := by
    apply pderiv_eq_zero_of_notMem_vars
    intro hmem
    have hle : (-n - 1 - 1).toNat ≤ p.vars.sup id := Finset.le_sup (f := id) hmem
    omega
  rw [hzero, smul_zero, smul_zero]

/-- The basic current is mutually local with itself (re-exported, `N = 2`). -/
theorem current_isLocal (k : ℂ) : Local (current k) (current k) := current_local k

/-- **The derivative currents are fields** (the derivative of a field is a field). -/
theorem dcurrent_isField (k : ℂ) (j : ℕ) : IsField (dcurrent k j) :=
  (current_isField k).deriv_iterate j

/-- **The modes of the derivative currents** (Gannon 5.2.5): a falling-factorial multiple of
the oscillator, `mode (∂^j α) m = (∏_{i<j} -(m-i))·a_{m-j}`. -/
theorem dcurrent_mode (k : ℂ) (j : ℕ) (m : ℤ) :
    mode (dcurrent k j) m = (∏ i ∈ Finset.range j, (-(m - (i : ℤ)))) • osc k (m - j) := by
  induction j generalizing m with
  | zero => simp only [dcurrent, Function.iterate_zero, id_eq, Finset.range_zero,
      Finset.prod_empty, one_smul, Nat.cast_zero, sub_zero]; exact current_mode k m
  | succ p ih =>
    rw [dcurrent_succ, mode_deriv, ih (m - 1), smul_smul]
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

/-- **The derivative currents are mutually local** (Gannon 5.2.5c): `Local (∂^i α)(∂^j α)`,
from the self-locality of `α` together with locality-preservation under `∂_z`. -/
theorem dcurrent_local (k : ℂ) (i j : ℕ) : Local (dcurrent k i) (dcurrent k j) :=
  ((current_isLocal k).deriv_iterate_left i).deriv_iterate_right j

/-! ## §4  The scaled generator fields `genField k i = (i!)⁻¹·∂^i α = Y(a₋(i+1)1, z)` -/

/-- The **scaled generator field** `genField k i := (i!)⁻¹·∂_z^i α(z)`.  In the vertex-operator
indexing it is exactly `Y(a₋(i+1)1, z) = (1/i!)∂^i α(z)` (Gannon 5.2.5: `a₋ₘ ↦ (1/(m-1)!)∂^{m-1}`
with `m = i+1`). -/
noncomputable def genField (k : ℂ) (i : ℕ) : FormalDist (End ℂ Fock) :=
  (i.factorial : ℂ)⁻¹ • dcurrent k i

theorem genField_isField (k : ℂ) (i : ℕ) : IsField (genField k i) := by
  intro x; obtain ⟨B, hB⟩ := dcurrent_isField k i x
  exact ⟨B, fun n hn => by
    show ((i.factorial : ℂ)⁻¹ • dcurrent k i n) x = 0
    rw [LinearMap.smul_apply, hB n hn, smul_zero]⟩

/-- `genField k 0 = α(z)`: the lowest generator field is the bare basic current. -/
theorem genField_zero (k : ℂ) : genField k 0 = current k := by
  rw [genField, dcurrent_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]

/-- Locality is invariant under scaling on the right (mirror of `Local.smul'`). -/
theorem Local.smulR (c : ℂ) {F G : FormalDist (End ℂ V)} (h : Local F G) :
    Local F (c • G) :=
  (VertexOperatorAlgebra.Local.smul' c h.symm).symm

set_option maxHeartbeats 1000000 in
/-- The generator fields are mutually local (scale-invariance of `dcurrent_local`). -/
theorem genField_local (k : ℂ) (i j : ℕ) : Local (genField k i) (genField k j) := by
  show Local ((i.factorial : ℂ)⁻¹ • dcurrent k i) ((j.factorial : ℂ)⁻¹ • dcurrent k j)
  exact Local.smulR _ (VertexOperatorAlgebra.Local.smul' _ (dcurrent_local k i j))

/-- A generator field is local with the identity field. -/
theorem genField_local_idField (k : ℂ) (i : ℕ) :
    Local (genField k i) (idField : FormalDist (End ℂ Fock)) :=
  Local_idField_right _

/-! ## §5  `Y` on monomial states: the iterated normal-ordered product

For a monomial `a₋(i₁+1)…a₋(iᵣ+1)1` we encode the multiset of indices `[i₁,…,iᵣ]` as a list,
and take the iterated `nprod` of the `genField`s — the field-closure of `nprod` (`IsField.nprod`)
lets us carry the field witness through the recursion. -/

/-- The iterated normal-ordered product over a list of generator indices, paired with its
field witness so the next `nprod` is well-typed.  `[]` ↦ the identity field;
`i :: rest` ↦ `:(genField k i)(Yword rest):`. -/
noncomputable def YwordF (k : ℂ) : List ℕ → { f : FormalDist (End ℂ Fock) // IsField f }
  | [] => ⟨idField, idField_isField⟩
  | (i :: rest) =>
      let p := YwordF k rest
      ⟨nprod (genField_isField k i) p.2, (genField_isField k i).nprod p.2⟩

/-- The iterated normal-ordered product `Yword k [i₁,…,iᵣ] = :(∂^{i₁}α/i₁!)⋯(∂^{iᵣ}α/iᵣ!):`. -/
noncomputable def Yword (k : ℂ) (l : List ℕ) : FormalDist (End ℂ Fock) := (YwordF k l).1

theorem Yword_isField (k : ℂ) (l : List ℕ) : IsField (Yword k l) := (YwordF k l).2

@[simp] theorem Yword_nil (k : ℂ) : Yword k [] = idField := rfl

theorem Yword_cons (k : ℂ) (i : ℕ) (rest : List ℕ) :
    Yword k (i :: rest) = nprod (genField_isField k i) (Yword_isField k rest) := rfl

/-- The list of generator indices of a monomial exponent vector `a : ℕ →₀ ℕ`: each variable
`i` (with exponent `a i`) contributes `a i` copies of `i`, in increasing order of `i`. -/
noncomputable def monoWord (a : ℕ →₀ ℕ) : List ℕ :=
  (a.support.sort (· ≤ ·)).flatMap (fun i => List.replicate (a i) i)

/-- `Y(u,z)` on a monomial `u = ∏ Xᵢ^{aᵢ}` (exponent vector `a`): the iterated normal-ordered
product of the generator fields (Gannon 5.2.5). -/
noncomputable def Ymon (k : ℂ) (a : ℕ →₀ ℕ) : FormalDist (End ℂ Fock) :=
  Yword k (monoWord a)

theorem Ymon_isField (k : ℂ) (a : ℕ →₀ ℕ) : IsField (Ymon k a) := Yword_isField k _

/-- **The general vertex operator** `Y : Fock →ₗ[ℂ] FormalDist (End ℂ Fock)` — the `ℂ`-linear
extension of `Ymon` off the monomial basis of `Fock = MvPolynomial ℕ ℂ` (Gannon §5.2). -/
noncomputable def Y (k : ℂ) : Fock →ₗ[ℂ] FormalDist (End ℂ Fock) :=
  Finsupp.linearCombination ℂ (Ymon k)

/-- `Y` on a monomial returns the iterated product, with the scalar pulled out. -/
theorem Y_monomial (k : ℂ) (a : ℕ →₀ ℕ) (c : ℂ) :
    Y k (monomial a c) = c • Ymon k a :=
  Finsupp.linearCombination_single ℂ c a

/-- `Y` on a bare monomial (`c = 1`). -/
theorem Y_monomial_one (k : ℂ) (a : ℕ →₀ ℕ) : Y k (monomial a 1) = Ymon k a := by
  rw [Y_monomial, one_smul]

/-! ## §6  VA2 — the vacuum field, and the basic current -/

/-- `monoWord 0 = []`: the empty monomial (the vacuum) has no generators. -/
@[simp] theorem monoWord_zero : monoWord (0 : ℕ →₀ ℕ) = [] := by
  rw [monoWord]; simp

/-- **VA2 / the vacuum field**: `Y(1,z) = id` (the identity field). -/
theorem Y_vacuum (k : ℂ) : Y k vacuum = idField := by
  rw [vacuum, show (1 : Fock) = monomial 0 1 from by rw [monomial_zero', map_one],
      Y_monomial_one, Ymon, monoWord_zero, Yword_nil]

/-- The vacuum field is the identity at `z⁰` and zero elsewhere: `(Y(1,z))_j = δ_{j,0}·id`. -/
theorem Y_vacuum_apply (k : ℂ) (j : ℤ) :
    Y k vacuum j = if j = 0 then LinearMap.id else 0 := by
  rw [Y_vacuum, idField_apply]

/-- The mode `1₍ₙ₎ = δ_{n,-1}·id` of the vacuum field (VA2). -/
theorem mode_Y_vacuum (k : ℂ) (n : ℤ) :
    mode (Y k vacuum) n = if n = -1 then LinearMap.id else 0 := by
  rw [mode_apply, Y_vacuum_apply]
  by_cases h : n = -1
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/-- The single creation state `a₋₁1 = X₀` as a monomial. -/
theorem osc_neg_one_vacuum (k : ℂ) : osc k (-1) vacuum = X 0 := by
  rw [osc_apply_neg k (by norm_num), vacuum, mul_one]
  norm_num

/-- `X 0` as a monomial (exponent vector `single 0 1`). -/
theorem X_zero_eq_monomial : (X 0 : Fock) = monomial (Finsupp.single 0 1) 1 := by
  rw [X]

/-- `monoWord (single 0 1) = [0]`: the single-creation state has the one generator `0`. -/
theorem monoWord_single_zero : monoWord (Finsupp.single 0 1) = [0] := by
  unfold monoWord
  rw [show (Finsupp.single 0 1 : ℕ →₀ ℕ).support = {0} from
    Finsupp.support_single 0 (by norm_num : (1 : ℕ) ≠ 0)]
  simp

/-- **The basic current** `Y(a₋₁1, z) = α(z)` (Gannon 5.2.5b): the field of the lowest
creation state is the bare current. -/
theorem Y_current (k : ℂ) : Y k (osc k (-1) vacuum) = current k := by
  rw [osc_neg_one_vacuum, X_zero_eq_monomial, Y_monomial_one, Ymon, monoWord_single_zero]
  show nprod (genField_isField k 0) (idField_isField) = current k
  rw [nprod_idField, genField_zero]

/-! ## §6b  VA3 — creation: regularity of `Y(u,z)` on the vacuum

`Y(u,z)1 = e^{zT}u` is regular at `z = 0`: the negative `z`-powers vanish on the vacuum and
the `z⁰`-coefficient reproduces `u`.  Proven here for the vacuum (`u = 1`) and the basic
current state (`u = a₋₁1`), the generators of the Fock space. -/

/-- **VA3 / regularity on the vacuum** for `u = 1`: the negative `z`-powers of `Y(1,z)` kill
the vacuum (`(Y(1,z))_j 1 = 0` for `j < 0`). -/
theorem Y_vacuum_creation_lt (k : ℂ) (j : ℤ) (hj : j < 0) :
    Y k vacuum j vacuum = 0 := by
  rw [Y_vacuum_apply, if_neg (by omega)]; rfl

/-- **VA3 / the `z⁰`-coefficient creates `u`** for `u = 1`: `(Y(1,z))_0 1 = 1`. -/
theorem Y_vacuum_creation_zero (k : ℂ) : Y k vacuum 0 vacuum = vacuum := by
  rw [Y_vacuum_apply, if_pos rfl]; rfl

/-- **VA3 / regularity on the vacuum** for `u = a₋₁1`: `(Y(a₋₁1,z))_j 1 = 0` for `j < 0`
(the corresponding mode `aₙ` with `n = -j-1 ≥ 0` annihilates the vacuum). -/
theorem Y_current_creation_lt (k : ℂ) (j : ℤ) (hj : j < 0) :
    Y k (osc k (-1) vacuum) j vacuum = 0 := by
  rw [Y_current, current_apply]
  exact osc_vacuum k (-j - 1) (by omega)

/-- **VA3 / the `z⁰`-coefficient creates `u`** for `u = a₋₁1`: `(Y(a₋₁1,z))_0 1 = a₋₁1`. -/
theorem Y_current_creation_zero (k : ℂ) :
    Y k (osc k (-1) vacuum) 0 vacuum = osc k (-1) vacuum := by
  rw [Y_current, current_apply, show (-(0 : ℤ) - 1 : ℤ) = -1 from by ring]

/-- The creation property in mode form (`Y(u,z) = ∑ u₍ₙ₎ z^{-n-1}`), as the prompt states it:
for `u = a₋₁1`, `u₍ₙ₎ 1 = 0` for `n ≥ 0`, and `u₍₋₁₎ 1 = u`. -/
theorem mode_Y_current_creation_nonneg (k : ℂ) (n : ℤ) (hn : 0 ≤ n) :
    mode (Y k (osc k (-1) vacuum)) n vacuum = 0 := by
  rw [mode_apply]; exact Y_current_creation_lt k (-n - 1) (by omega)

theorem mode_Y_current_creation_neg_one (k : ℂ) :
    mode (Y k (osc k (-1) vacuum)) (-1) vacuum = osc k (-1) vacuum := by
  rw [mode_apply, show (-(-1 : ℤ) - 1 : ℤ) = 0 from by ring]
  exact Y_current_creation_zero k

/-! ## §7  VA4 — locality of all monomial fields, assembled by iterated Dong

Every `Yword` is mutually local with every `Yword` (and with each generator), built by
iterating Dong's normal-product locality `dong_neg` over the generator fields, with the base
case the centrality of the identity field. -/

/-- A generator field is local with every iterated product `Yword` (induction on the word,
peeling one `nprod` via `dong_neg`).  The generator index is universally quantified so the
recursive `Local (genField j)(Yword rest)` is available at each step. -/
theorem genField_local_Yword (k : ℂ) : ∀ (l : List ℕ) (i : ℕ),
    Local (genField k i) (Yword k l) := by
  intro l
  induction l with
  | nil => intro i; rw [Yword_nil]; exact Local_idField_right _
  | cons j rest ih =>
      intro i
      have hab : Local (genField k j) (Yword k rest) := ih j
      have hac : Local (genField k j) (genField k i) := genField_local k j i
      have hbc : Local (Yword k rest) (genField k i) := (ih i).symm
      have hmain : Local (nprod (genField_isField k j) (Yword_isField k rest)) (genField k i) :=
        dong_neg (genField_isField k j) (Yword_isField k rest) hab hac hbc
      rw [Yword_cons]
      exact hmain.symm

/-- **Every two iterated products are mutually local** (induction on the first word). -/
theorem Yword_local (k : ℂ) : ∀ (l₁ l₂ : List ℕ), Local (Yword k l₁) (Yword k l₂) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; rw [Yword_nil]; exact Local_idField_left _
  | cons i rest ih =>
      intro l₂
      have hab : Local (genField k i) (Yword k rest) := genField_local_Yword k rest i
      have hac : Local (genField k i) (Yword k l₂) := genField_local_Yword k l₂ i
      have hbc : Local (Yword k rest) (Yword k l₂) := ih l₂
      have hmain : Local (nprod (genField_isField k i) (Yword_isField k rest)) (Yword k l₂) :=
        dong_neg (genField_isField k i) (Yword_isField k rest) hab hac hbc
      rw [Yword_cons]
      exact hmain

/-- **VA4 for the monomial basis**: every two monomial fields `Y(u,z), Y(v,z)` (for monomials
`u, v`) are mutually local (Gannon 5.2.5c). -/
theorem Ymon_local (k : ℂ) (a b : ℕ →₀ ℕ) : Local (Ymon k a) (Ymon k b) :=
  Yword_local k (monoWord a) (monoWord b)

/-- The self-locality of the basic current field, as a special case of `Ymon_local`. -/
theorem Y_current_self_local (k : ℂ) :
    Local (Y k (osc k (-1) vacuum)) (Y k (osc k (-1) vacuum)) := by
  rw [Y_current]; exact current_isLocal k

end VOA
