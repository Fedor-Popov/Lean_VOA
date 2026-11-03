/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergFock
import VOA.Examples.HeisenbergVertex
import VOA.Examples.HeisenbergVirasoro
import VOA.Examples.HeisenbergCreation
import VOA.Examples.HeisenbergConformal
import VOA.Examples.HeisenbergGrading
import VOA.Examples.HeisenbergStructure
import VOA.Examples.HeisenbergCentral
import VOA.Core.VertexOperatorAlgebra
import VOA.Core.Goddard
import VOA.Core.Dong

/-!
# The Heisenberg / free-boson VertexOperatorAlgebra

Assembles `heisenbergVOA k hk : VertexOperatorAlgebra Fock` from the Heisenberg API,
proves the central charge `= 1`, and closes the VOA3 translation axiom for ALL states.
-/

namespace VOA

open scoped BigOperators
open MvPolynomial
open Module (End)

universe u

/-! ## §0  Field-level helpers: `idField = 1`, the Leibniz product rule `∂:ab: = :∂a b: + :a ∂b:` -/

/-- The unit field of VA2 is the identity field: `idField = (1 : FormalDist (End ℂ Fock))`. -/
theorem idField_eq_one {V : Type u} [AddCommGroup V] [Module ℂ V] :
    (idField : FormalDist (End ℂ V)) = (1 : FormalDist (End ℂ V)) := by
  funext j; rw [idField_apply, FormalDist.one_apply]; rfl

section Leibniz
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- The `b`-derivative diagonal term of the Leibniz rule. -/
theorem NO_deriv_right_term (a b : FormalDist (End ℂ V)) (m s : ℤ) (x : V) :
    ((s + 1 - m : ℤ) • normalOrdered a b m (s + 1 - m)) x
      = normalOrdered a (deriv b) m (s - m) x := by
  rw [normalOrdered_apply, normalOrdered_apply, deriv_apply]
  rw [show (s - m + 1 : ℤ) = s + 1 - m from by ring]
  by_cases h : 0 ≤ m
  · rw [if_pos h, if_pos h, LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply,
      LinearMap.smul_apply, map_zsmul]
  · rw [if_neg h, if_neg h, LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply,
      LinearMap.smul_apply]

/-- The `a`-derivative diagonal term of the Leibniz rule (after the `m ↦ m-1` reindex). -/
theorem NO_deriv_left_term (a b : FormalDist (End ℂ V)) (m s : ℤ) (x : V) :
    normalOrdered (deriv a) b (m - 1) (s - (m - 1)) x
      = (m : ℤ) • normalOrdered a b m (s + 1 - m) x := by
  rw [normalOrdered_apply, normalOrdered_apply, deriv_apply]
  rw [show (m - 1 + 1 : ℤ) = m from by ring, show (s - (m - 1) : ℤ) = s + 1 - m from by ring]
  by_cases h : 0 ≤ m
  · by_cases h0 : (0 : ℤ) ≤ m - 1
    · rw [if_pos h0, if_pos h, smul_mul_assoc, LinearMap.smul_apply]
    · have hm0 : m = 0 := by omega
      subst hm0; rw [if_neg (by norm_num), if_pos (by norm_num)]; simp
  · rw [if_neg (by omega), if_neg h, mul_smul_comm, LinearMap.smul_apply]

/-- Predecessor reindexing of a `finsum` over `ℤ`. -/
theorem finsum_int_pred_shift {M : Type*} [AddCommMonoid M] (G : ℤ → M) :
    ∑ᶠ m : ℤ, G (m - 1) = ∑ᶠ m : ℤ, G m :=
  finsum_comp_equiv (Equiv.subRight (1 : ℤ)) (f := G)

/-- **Field Leibniz product rule** for the same-variable normal-ordered product:
`∂_z :a(z)b(z): = :(∂_z a)b: + :a(∂_z b):`. -/
theorem deriv_nprod {a b : FormalDist (End ℂ V)} (ha : IsField a) (hb : IsField b) :
    deriv (nprod ha hb) = nprod (ha.deriv) hb + nprod ha (hb.deriv) := by
  funext s
  ext x
  rw [deriv_apply]
  show ((s + 1 : ℤ) • (nprod ha hb (s + 1))) x = (nprod (ha.deriv) hb s + nprod ha (hb.deriv) s) x
  rw [LinearMap.smul_apply, nprod_apply, LinearMap.add_apply, nprod_apply, nprod_apply,
    smul_finsum' (s + 1 : ℤ) (normalOrdered_diag_support_finite ha hb (s + 1) x)]
  have hsplit : ∀ m : ℤ, (s + 1 : ℤ) • normalOrdered a b m (s + 1 - m) x
      = normalOrdered (deriv a) b (m - 1) (s - (m - 1)) x
        + normalOrdered a (deriv b) m (s - m) x := by
    intro m
    rw [NO_deriv_left_term, ← NO_deriv_right_term, LinearMap.smul_apply, ← add_smul]
    congr 1; ring
  rw [finsum_congr hsplit]
  have hfinL : (Function.support
      (fun m : ℤ => normalOrdered (deriv a) b (m - 1) (s - (m - 1)) x)).Finite := by
    have hbase := normalOrdered_diag_support_finite ha.deriv hb s x
    apply Set.Finite.subset (hbase.image (· + 1))
    intro m hm
    rw [Function.mem_support] at hm
    exact ⟨m - 1, by rw [Function.mem_support]; exact hm, by ring⟩
  rw [finsum_add_distrib hfinL (normalOrdered_diag_support_finite ha hb.deriv s x)]
  congr 1
  rw [← finsum_int_pred_shift (fun m : ℤ => normalOrdered (deriv a) b m (s - m) x)]

end Leibniz

/-! ## §1  Generator-field calculus: `genField k i = Y(Xᵢ)`, `∂ genField = (i+1) genField_{i+1}` -/

/-- The generator field is the vertex operator of the single-variable state `Xᵢ`:
`genField k i = Y(Xᵢ, z) = Y(a₋(i+1)1, z)`. -/
theorem genField_eq_Y_X (k : ℂ) (i : ℕ) : genField k i = Y k (X i : Fock) := by
  rw [X, Y_monomial_one, Ymon,
    show monoWord (Finsupp.single i 1) = [i] from by
      unfold monoWord
      rw [show (Finsupp.single i 1 : ℕ →₀ ℕ).support = {i} from by
        rw [Finsupp.support_single]; norm_num]
      simp [Finsupp.single_eq_same],
    Yword_singleton]

/-- `∂_z genField k i = (i+1)·genField k (i+1)`: the field derivative raises the generator
index, the `(i+1)` from `(i!)⁻¹·(i+1)! = i+1`. -/
theorem deriv_genField (k : ℂ) (i : ℕ) :
    deriv (genField k i) = ((i : ℂ) + 1) • genField k (i + 1) := by
  rw [genField, genField, map_smul, ← dcurrent_succ, smul_smul]
  congr 1
  rw [Nat.factorial_succ]; push_cast; field_simp

/-! ## §2  `D`-covariance of fields: `[D, a_m] = (m+1)·a_{m+1}` (the bracket form of `∂`) -/

/-- A field `a` is **`D`-covariant** (`D` a fixed operator) if `[D, a_m] = (m+1)•a_{m+1}`,
i.e. conjugating the coefficients by `D` reproduces the formal derivative `deriv a`.  This is
the operator (bracket) form of translation covariance `[D, Y(v,z)] = ∂_z Y(v,z)`. -/
def DCovariant {V : Type u} [AddCommGroup V] [Module ℂ V]
    (D : End ℂ V) (a : FormalDist (End ℂ V)) : Prop :=
  ∀ m : ℤ, D * a m - a m * D = ((m + 1 : ℤ)) • a (m + 1)

namespace DCovariant
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- `DCovariant` is closed under scaling. -/
theorem smul {D : End ℂ V} {a : FormalDist (End ℂ V)} (c : ℂ) (ha : DCovariant D a) :
    DCovariant D (c • a) := by
  intro m
  show D * (c • a m) - (c • a m) * D = ((m + 1 : ℤ)) • (c • a (m + 1))
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, ha m, smul_comm]

/-- The zero field is `D`-covariant. -/
theorem zero {D : End ℂ V} : DCovariant D (0 : FormalDist (End ℂ V)) := by
  intro m
  show D * (0 : FormalDist (End ℂ V)) m - (0 : FormalDist (End ℂ V)) m * D
      = ((m + 1 : ℤ)) • (0 : FormalDist (End ℂ V)) (m + 1)
  show D * 0 - 0 * D = ((m + 1 : ℤ)) • (0 : End ℂ V)
  rw [mul_zero, zero_mul, sub_zero, smul_zero]

/-- `DCovariant` is closed under addition. -/
theorem add {D : End ℂ V} {a b : FormalDist (End ℂ V)} (ha : DCovariant D a)
    (hb : DCovariant D b) : DCovariant D (a + b) := by
  intro m
  show D * ((a m) + (b m)) - ((a m) + (b m)) * D = ((m + 1 : ℤ)) • ((a (m + 1)) + (b (m + 1)))
  rw [mul_add, add_mul, smul_add, ← ha m, ← hb m]; abel

/-- `DCovariant` is closed under finite `ℂ`-linear combinations indexed by a `Finset`. -/
theorem finsetSum {ι : Type*} {D : End ℂ V} (s : Finset ι) (f : ι → FormalDist (End ℂ V))
    (hf : ∀ i ∈ s, DCovariant D (f i)) : DCovariant D (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (zero (D := D))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- `DCovariant` is closed under the formal derivative. -/
theorem deriv' {D : End ℂ V} {a : FormalDist (End ℂ V)} (ha : DCovariant D a) :
    DCovariant D (VOA.deriv a) := by
  intro m
  rw [deriv_apply, deriv_apply]
  show D * ((m + 1 : ℤ) • a (m + 1)) - ((m + 1 : ℤ) • a (m + 1)) * D
      = ((m + 1 : ℤ)) • ((m + 1 + 1 : ℤ) • a (m + 1 + 1))
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, ha (m + 1), smul_comm]

/-- Iterated-derivative covariance. -/
theorem deriv_iterate {D : End ℂ V} {a : FormalDist (End ℂ V)} (ha : DCovariant D a)
    (j : ℕ) : DCovariant D ((VOA.deriv^[j]) a) := by
  induction j with
  | zero => simpa using ha
  | succ p ih => rw [Function.iterate_succ', Function.comp_apply]; exact ih.deriv'

/-- `DCovariant` of the identity field: `[D, idField_m] = 0 = deriv idField`. -/
theorem idField {D : End ℂ V} : DCovariant D (VOA.idField : FormalDist (End ℂ V)) := by
  intro m
  simp only [idField_apply]
  by_cases h0 : m = 0
  · subst h0
    rw [if_pos rfl, if_neg (by norm_num : ¬ (0:ℤ) + 1 = 0), smul_zero,
      show (LinearMap.id : End ℂ V) = 1 from rfl, mul_one, one_mul, sub_self]
  · rw [if_neg h0, mul_zero, zero_mul, sub_zero]
    by_cases h1 : m + 1 = 0
    · rw [if_pos h1, show (m + 1 : ℤ) = 0 from h1, zero_smul]
    · rw [if_neg h1, smul_zero]

/-- per-term bracket identity: `[D,·]` of a `normalOrdered` term is the sum of the two
`deriv`-coefficient terms at the same index (Leibniz, no reindex). -/
theorem NO_term {D : End ℂ V} {a b : FormalDist (End ℂ V)} (ha : DCovariant D a)
    (hb : DCovariant D b) (p s : ℤ) (x : V) :
    D (normalOrdered a b p (s - p) x) - normalOrdered a b p (s - p) (D x)
      = normalOrdered (deriv a) b p (s - p) x + normalOrdered a (deriv b) p (s - p) x := by
  rw [normalOrdered_apply, normalOrdered_apply (a := deriv a),
    normalOrdered_apply (a := a) (b := deriv b), deriv_apply, deriv_apply]
  by_cases h : 0 ≤ p
  · rw [if_pos h, if_pos h, if_pos h]
    have key : D * (a p * b (s - p)) - (a p * b (s - p)) * D
        = ((p + 1 : ℤ) • a (p + 1)) * b (s - p) + a p * ((s - p + 1 : ℤ) • b (s - p + 1)) := by
      have e : D * (a p * b (s - p)) - (a p * b (s - p)) * D
          = (D * a p - a p * D) * b (s - p) + a p * (D * b (s - p) - b (s - p) * D) := by
        noncomm_ring
      rw [e, ha p, hb (s - p)]
    have hx := congrArg (fun (T : End ℂ V) => T x) key
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.mul_apply] using hx
  · rw [if_neg h, if_neg h, if_neg h]
    have key : D * (b (s - p) * a p) - (b (s - p) * a p) * D
        = b (s - p) * ((p + 1 : ℤ) • a (p + 1)) + ((s - p + 1 : ℤ) • b (s - p + 1)) * a p := by
      have e : D * (b (s - p) * a p) - (b (s - p) * a p) * D
          = b (s - p) * (D * a p - a p * D) + (D * b (s - p) - b (s - p) * D) * a p := by
        noncomm_ring
      rw [e, ha p, hb (s - p)]
    have hx := congrArg (fun (T : End ℂ V) => T x) key
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.mul_apply] using hx

/-- **`DCovariant` is closed under the normal-ordered product** (`:ab:` is `D`-covariant when
`a, b` are). -/
theorem nprod {D : End ℂ V} {a b : FormalDist (End ℂ V)} (haf : IsField a) (hbf : IsField b)
    (ha : DCovariant D a) (hb : DCovariant D b) :
    DCovariant D (VOA.nprod haf hbf) := by
  intro s
  apply LinearMap.ext
  intro x
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply,
    nprod_apply, nprod_apply, map_finsum D (normalOrdered_diag_support_finite haf hbf s x)]
  have hfinDL : (Function.support (fun p : ℤ => D (normalOrdered a b p (s - p) x))).Finite := by
    apply Set.Finite.subset (normalOrdered_diag_support_finite haf hbf s x)
    intro p hp
    rw [Function.mem_support] at hp ⊢
    exact fun hz => hp (by rw [hz, map_zero])
  rw [← finsum_sub_distrib hfinDL (normalOrdered_diag_support_finite haf hbf s (D x)),
    finsum_congr (fun p => NO_term ha hb p s x),
    finsum_add_distrib (normalOrdered_diag_support_finite haf.deriv hbf s x)
      (normalOrdered_diag_support_finite haf hbf.deriv s x),
    show (∑ᶠ p : ℤ, normalOrdered (deriv a) b p (s - p) x)
        = VOA.nprod haf.deriv hbf s x from (nprod_apply haf.deriv hbf s x).symm,
    show (∑ᶠ p : ℤ, normalOrdered a (deriv b) p (s - p) x)
        = VOA.nprod haf hbf.deriv s x from (nprod_apply haf hbf.deriv s x).symm]
  have hadd : (VOA.nprod haf.deriv hbf s) x + (VOA.nprod haf hbf.deriv s) x
      = (deriv (VOA.nprod haf hbf)) s x := by
    rw [deriv_nprod]; rfl
  rw [hadd, deriv_apply, LinearMap.smul_apply]

end DCovariant

/-! ## §3  Every Heisenberg field `Y k v` is `L₋₁`-covariant -/

/-- **Base**: the basic current `α(z)` is `L₋₁`-covariant: `[L₋₁, α_m] = (m+1)α_{m+1}`
(directly from the affine commutator `[L₋₁, aₙ] = -n a_{n-1}`, `L_comm_osc`). -/
theorem current_DCovariant (k : ℂ) (hk : k ≠ 0) :
    DCovariant (Lvir k (-1)) (current k) := by
  intro m
  rw [current_apply, current_apply, show -(m + 1) - 1 = -m - 2 from by ring]
  have h := L_comm_osc k hk (-1) (-m - 1)
  rw [show (-1 : ℤ) + (-m - 1) = -m - 2 from by ring] at h
  rw [h, show (-(((-m - 1 : ℤ)) : ℂ)) = ((m + 1 : ℤ) : ℂ) from by push_cast; ring,
    Int.cast_smul_eq_zsmul ℂ (m + 1) (osc k (-m - 2))]

/-- The generator fields `genField k i` are `L₋₁`-covariant (iterated derivative of `α`). -/
theorem genField_DCovariant (k : ℂ) (hk : k ≠ 0) (i : ℕ) :
    DCovariant (Lvir k (-1)) (genField k i) := by
  rw [genField, dcurrent]
  exact ((current_DCovariant k hk).deriv_iterate i).smul _

/-- The word fields `Yword k l` are `L₋₁`-covariant (induction over the word: `idField` base,
`nprod` with a `genField` for the step). -/
theorem Yword_DCovariant (k : ℂ) (hk : k ≠ 0) : ∀ l : List ℕ,
    DCovariant (Lvir k (-1)) (Yword k l)
  | [] => by rw [Yword_nil]; exact DCovariant.idField
  | (i :: rest) => by
      rw [Yword_cons]
      exact DCovariant.nprod (genField_isField k i) (Yword_isField k rest)
        (genField_DCovariant k hk i) (Yword_DCovariant k hk rest)

/-- The monomial fields `Ymon k a` are `L₋₁`-covariant. -/
theorem Ymon_DCovariant (k : ℂ) (hk : k ≠ 0) (a : ℕ →₀ ℕ) :
    DCovariant (Lvir k (-1)) (Ymon k a) :=
  Yword_DCovariant k hk (monoWord a)

/-- **Operator translation covariance** for EVERY state: `[L₋₁, Y(v,z)_m] = (m+1)•Y(v,z)_{m+1}`,
i.e. `Y k v` is `L₋₁`-covariant.  By `ℂ`-linearity of `Y k` from the monomial fields. -/
theorem Y_DCovariant (k : ℂ) (hk : k ≠ 0) (v : Fock) :
    DCovariant (Lvir k (-1)) (Y k v) := by
  classical
  rw [show Y k v = Finsupp.linearCombination ℂ (Ymon k) v from rfl,
    Finsupp.linearCombination_apply, Finsupp.sum]
  exact DCovariant.finsetSum _ _ (fun a _ => (Ymon_DCovariant k hk a).smul _)

/-! ## §3b  The bare `PreVertexAlgebra Fock` (VA1–VA5), for invoking Goddard uniqueness -/

/-- The Heisenberg / free-boson **vertex algebra** structure (VA1–VA5), level `k ≠ 0`.
All five axioms are proved; the grading is `gradingZ` (`gradingW` on `ℕ`, `⊥` below). -/
noncomputable def heisVA (k : ℂ) (_hk : k ≠ 0) : PreVertexAlgebra Fock where
  grading := gradingZ
  isInternal := gradingZ_isInternal
  finrank := gradingZ_finrank
  Y := Y k
  vacuum := vacuum
  vacuum_mem := mem_gradingZ_of_gradingW vacuum_mem_gradingW
  grading_mode := fun u hu v hv n => va1_grading_mode k u hu v hv n
  vacuum_Y := by rw [Y_vacuum, idField_eq_one]
  creation := fun u => Y_creation k u
  locality := fun u v => Y_local k u v
  regularity := fun u v => va5_regularity k u v

/-! ## §4  The creation recursion and VOA3 translation for ALL states -/

/-- **The creation recursion** from `L₋₁`-covariance: applying `[L₋₁,·]` to the vacuum tower of
`Y(v,z)` shifts the `z`-power index, `L₋₁((Y v)_m 1) = (m+1)·(Y v)_{m+1} 1`.  (`L₋₁ 1 = 0`, so
only the `L₋₁·(Y v)_m` half of the bracket survives.) -/
theorem Y_creation_recursion (k : ℂ) (hk : k ≠ 0) (v : Fock) (m : ℤ) :
    Lvir k (-1) ((Y k v) m vacuum) = ((m + 1 : ℤ)) • ((Y k v) (m + 1) vacuum) := by
  have h := congrArg (fun (T : End ℂ Fock) => T vacuum) (Y_DCovariant k hk v m)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [Lvir_vacuum k (by norm_num : (-1 : ℤ) ≤ -1), map_zero, sub_zero] at h
  exact h

/-- **The bridge `T = L₋₁`** for Heisenberg: `L₋₁ v = (Y v)_1 1 = mode (Y v) (-2) 1`
(the `m = 0` instance of the creation recursion, with `(Y v)_0 1 = v`). -/
theorem Lvir_neg_one_eq_smul_vacuum (k : ℂ) (hk : k ≠ 0) (v : Fock) :
    Lvir k (-1) v = (Y k v) 1 vacuum := by
  have h := Y_creation_recursion k hk v 0
  rw [Y_creation_zero, show (0 : ℤ) + 1 = 1 from rfl, one_smul] at h
  exact h

/-- Both candidate fields agree at index `0` (the bridge) and vanish for index `< 0`. -/
theorem translation_vacuum_cond_neg (k : ℂ) (v : Fock) {m : ℤ} (hm : m < 0) :
    (deriv (Y k v)) m vacuum = (Y k (Lvir k (-1) v)) m vacuum := by
  rw [Y_creation_lt k (Lvir k (-1) v) hm, deriv_apply]
  show (m + 1 : ℤ) • ((Y k v) (m + 1) vacuum) = 0
  rcases lt_or_eq_of_le (by omega : m ≤ -1) with hlt | he
  · rw [Y_creation_lt k v (by omega : (m + 1 : ℤ) < 0)]; simp
  · rw [show (m + 1 : ℤ) = 0 from by omega, zero_smul]

/-- **The vacuum condition for Goddard**: `(∂_z Y(v,z))_m 1 = (Y(L₋₁v,z))_m 1` for every `m`.
Both fields vanish below index `0`, agree at index `0` (the bridge `Lvir_neg_one_eq_smul_vacuum`),
and obey the same `L₋₁`-recursion — so they agree everywhere (upward induction on `m ≥ 0`). -/
theorem translation_vacuum_cond (k : ℂ) (hk : k ≠ 0) (v : Fock) (m : ℤ) :
    (deriv (Y k v)) m vacuum = (Y k (Lvir k (-1) v)) m vacuum := by
  by_cases hm : 0 ≤ m
  · -- upward induction on m = ↑j
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = (j : ℤ) := ⟨m.toNat, by omega⟩
    clear hm
    induction j with
    | zero =>
        rw [Nat.cast_zero, deriv_apply]
        show (0 + 1 : ℤ) • ((Y k v) (0 + 1) vacuum) = (Y k (Lvir k (-1) v)) 0 vacuum
        rw [show (0 : ℤ) + 1 = 1 from rfl,
          one_smul, Y_creation_zero k (Lvir k (-1) v), Lvir_neg_one_eq_smul_vacuum k hk v]
    | succ i ih =>
        -- L₋₁ (B i 1) = (i+1) B(i+1) 1 for both B; with the agreement at i, climb to i+1.
        have hrecB1 : Lvir k (-1) ((deriv (Y k v)) (i : ℤ) vacuum)
            = ((i : ℤ) + 1) • (deriv (Y k v)) ((i : ℤ) + 1) vacuum := by
          have e1 : (deriv (Y k v)) (i : ℤ) vacuum
              = ((i : ℤ) + 1) • ((Y k v) ((i : ℤ) + 1) vacuum) := by
            rw [deriv_apply]; rfl
          have e2 : (deriv (Y k v)) ((i : ℤ) + 1) vacuum
              = ((i : ℤ) + 1 + 1) • ((Y k v) ((i : ℤ) + 1 + 1) vacuum) := by
            rw [deriv_apply]; rfl
          rw [e1, e2, map_zsmul, Y_creation_recursion k hk v ((i : ℤ) + 1), smul_smul]
        have hrecB2 : Lvir k (-1) ((Y k (Lvir k (-1) v)) (i : ℤ) vacuum)
            = ((i : ℤ) + 1) • (Y k (Lvir k (-1) v)) ((i : ℤ) + 1) vacuum :=
          Y_creation_recursion k hk (Lvir k (-1) v) (i : ℤ)
        have hkey : ((i : ℤ) + 1) • (deriv (Y k v)) ((i : ℤ) + 1) vacuum
            = ((i : ℤ) + 1) • (Y k (Lvir k (-1) v)) ((i : ℤ) + 1) vacuum := by
          rw [← hrecB1, ← hrecB2, ih]
        have hc : (((i : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := by
          rw [Int.cast_ne_zero]; omega
        rw [← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1),
          ← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1)] at hkey
        rw [Nat.cast_succ]
        exact smul_right_injective Fock hc hkey
  · exact translation_vacuum_cond_neg k v (by omega)

/-- **VOA3 translation for ALL states** (Gannon 5.1.8): `Y(L₋₁v, z) = ∂_z Y(v,z)`, with
`L₋₁ = mode (Y ω) 0 = Lvir k (-1)`.  By Goddard uniqueness: `∂_z Y(v,z)` is local with every
`Y(b,z)` (`Local.derivL`) and creates the same vacuum tower as `Y(L₋₁v,z)`
(`translation_vacuum_cond`). -/
theorem translation_all (k : ℂ) (hk : k ≠ 0) (v : Fock) :
    Y k (Lvir k (-1) v) = deriv (Y k v) := by
  classical
  -- Build the bare PreVertexAlgebra to invoke Goddard uniqueness.
  refine (PreVertexAlgebra.goddard_uniqueness (heisVA k hk) (deriv (Y k v)) (Lvir k (-1) v)
    (fun b => ?_) (fun m => ?_)).symm
  · exact (Y_local k v b).derivL
  · exact translation_vacuum_cond k hk v m

/-- **VOA3 in the structure shape**: `Y(ω₍₀₎ v, z) = ∂_z Y(v,z)` with `L₋₁ = mode (Y ω) 0`. -/
theorem conf_translation (k : ℂ) (hk : k ≠ 0) (v : Fock) :
    Y k (mode (Y k (ω k)) 0 v) = deriv (Y k v) := by
  rw [← Lvir_neg_one_eq_mode]; exact translation_all k hk v

/-! ## §5  The full `VertexOperatorAlgebra Fock` (Heisenberg / free boson, level `k ≠ 0`) -/

/-- **The Heisenberg / free-boson vertex operator algebra** (Gannon §5.2; the rank-1
Heisenberg VOA `M(1)`), level `k ≠ 0`.  Conformal vector `ω = (1/2k)a₋₁a₋₁1`, central charge
`c = 1`.  Every VOA field is supplied by a proved lemma (VA1–VA5, VOA1–VOA4) with the VOA3
translation closed in this file via Goddard uniqueness + `L₋₁`-covariance. -/
noncomputable def heisenbergVOA (k : ℂ) (hk : k ≠ 0) : VertexOperatorAlgebra Fock where
  toPreVertexAlgebra := heisVA k hk
  conformalVector := ω k
  conformal_mem := omega_mem_gradingZ_two k
  centralCharge := 1
  virasoro := fun m n => conf_virasoro k hk m n
  L0_grading := fun v hv => conf_L0_grading k hk v hv
  translation := fun v => conf_translation k hk v
  vacuum_grade := gradingZ_zero_eq_span_vacuum
  positivity := fun n hn => gradingZ_positivity n hn

/-- **The central charge of the Heisenberg VOA is `1`** (Gannon §5.2; the free-boson `c = 1`). -/
theorem heisenberg_central_charge (k : ℂ) (hk : k ≠ 0) :
    (heisenbergVOA k hk).centralCharge = 1 := rfl

/-! ## §6  Axiom audit -/


end VOA
