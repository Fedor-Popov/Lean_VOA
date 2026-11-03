/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.Reconstruction
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The operator-first reconstruction theorem  (Gannon §5.1; Kac §4.5, the Existence theorem)

The *existence*-direction reconstruction: build the all-states vertex map `Y` on a **cyclic**
`ℂ`-module from a generating family of pairwise-local fields whose vacuum-creation tower spans,
WITHOUT a pre-existing `PreVertexAlgebra` structure (so it cannot invoke the in-VOA
`goddard_uniqueness`, which consumes the structure's own `V.Y` as test fields — circular).

The engine is the **non-circular standalone Goddard uniqueness** `Core.Goddard.goddard_zero`
(itself built only from the `(z₁-z₂)ᴺ` cancellation
`Foundations.IteratedLaurent.eq_zero_of_mulBySubPow_of_bddBelow`).  The translation operator `T`
(with `T vac = 0` and field-covariance of the generators) pins the *full* vacuum-creation tower
`(fld i)_p vac = (p!)⁻¹ Tᵖ (st i)`, which is exactly the data the standalone Goddard mechanism
needs to force a field that annihilates the vacuum to vanish.

This file builds, reusably in `Core`:

* **`DCovariant`** (translation covariance `[T, a_m] = (m+1) a_{m+1}`) and its closure under
  scaling, sums, `deriv`, and the normal-ordered product `nprod` — the module-polymorphic
  toolkit a cyclic example uses to verify `T`-covariance of its iterated word fields.
* **`creationTower`** — `DCovariant T g` + `T vac = 0` + `g 0 vac = u` force
  `g p vac = (p!)⁻¹ Tᵖ u` for every `p`.
* **`field_eq_zero_of_vacuum`** — the operator-first uniqueness: a field annihilating the
  vacuum at every degree, local with a creating test field for each of a spanning family of
  states, is the zero field.
* **`reconstructionData` / `reconstruct`** — package a generating family of pairwise-local
  `IsField`s on a cyclic module (whose creation tower spans, `T`-covariant) into the unique
  linear `YA` with `YA (st i) = fld i`, satisfying VA3 creation, VA4 locality, VA5 regularity,
  and translation covariance — the basis-free `Y` the affine `WakModule` and Virasoro `L(c,0)`
  examples consume to close their VOA instance.

## References
* Gannon §5.1.2–5.1.3; Kac, *VA for Beginners* §4.5 (Existence theorem); Frenkel–Ben-Zvi §4.4;
  Lepowsky–Li §3.5–3.6 (the reconstruction / "Frenkel–Kac–Radul–Wang" construction).
-/

namespace VOA.Reconstruction

open Module (End)

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-! ## §1  Translation covariance `DCovariant` and its closure

`DCovariant T a` says `[T, a_m] = (m+1)•a_{m+1}`, the operator (bracket) form of
`[T, a(z)] = ∂_z a(z)`.  (This duplicates, in `Core`, the `VOA.DCovariant` notion that
the free-boson `Examples.HeisenbergVOA` carries on its Fock space; here it is module-polymorphic
and used by the abstract reconstruction.) -/

/-- A field `a` is **`T`-covariant** if `[T, a_m] = (m+1)•a_{m+1}` (the bracket form of
`[T, a(z)] = ∂_z a(z)`). -/
def DCovariant (T : End ℂ V) (a : FormalDist (End ℂ V)) : Prop :=
  ∀ m : ℤ, T * a m - a m * T = ((m + 1 : ℤ)) • a (m + 1)

namespace DCovariant

/-- `DCovariant` is closed under scaling. -/
theorem smul {T : End ℂ V} {a : FormalDist (End ℂ V)} (c : ℂ) (ha : DCovariant T a) :
    DCovariant T (c • a) := by
  intro m
  show T * (c • a m) - (c • a m) * T = ((m + 1 : ℤ)) • (c • a (m + 1))
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, ha m, smul_comm]

/-- The zero field is `T`-covariant. -/
theorem zero {T : End ℂ V} : DCovariant T (0 : FormalDist (End ℂ V)) := by
  intro m
  show T * (0 : End ℂ V) - (0 : End ℂ V) * T = ((m + 1 : ℤ)) • (0 : End ℂ V)
  rw [mul_zero, zero_mul, sub_zero, smul_zero]

/-- `DCovariant` is closed under addition. -/
theorem add {T : End ℂ V} {a b : FormalDist (End ℂ V)} (ha : DCovariant T a)
    (hb : DCovariant T b) : DCovariant T (a + b) := by
  intro m
  show T * ((a m) + (b m)) - ((a m) + (b m)) * T = ((m + 1 : ℤ)) • ((a (m + 1)) + (b (m + 1)))
  rw [mul_add, add_mul, smul_add, ← ha m, ← hb m]; abel

/-- `DCovariant` is closed under finite `ℂ`-linear combinations indexed by a `Finset`. -/
theorem finsetSum {ι : Type*} {T : End ℂ V} (s : Finset ι) (f : ι → FormalDist (End ℂ V))
    (hf : ∀ i ∈ s, DCovariant T (f i)) : DCovariant T (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (zero (T := T))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- `DCovariant` is closed under the formal derivative. -/
theorem deriv' {T : End ℂ V} {a : FormalDist (End ℂ V)} (ha : DCovariant T a) :
    DCovariant T (VOA.deriv a) := by
  intro m
  rw [deriv_apply, deriv_apply]
  show T * ((m + 1 : ℤ) • a (m + 1)) - ((m + 1 : ℤ) • a (m + 1)) * T
      = ((m + 1 : ℤ)) • ((m + 1 + 1 : ℤ) • a (m + 1 + 1))
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, ha (m + 1), smul_comm]

/-- Iterated-derivative covariance. -/
theorem deriv_iterate {T : End ℂ V} {a : FormalDist (End ℂ V)} (ha : DCovariant T a)
    (j : ℕ) : DCovariant T ((VOA.deriv^[j]) a) := by
  induction j with
  | zero => simpa using ha
  | succ p ih => rw [Function.iterate_succ', Function.comp_apply]; exact ih.deriv'

end DCovariant

/-! ## §1b  The Leibniz product rule `∂_z :a(z)b(z): = :(∂a)b: + :a(∂b):`

The same module-polymorphic Leibniz rule the free boson uses (`Examples.HeisenbergVOA.deriv_nprod`);
re-proved here in `Core` (under the `Reconstruction` namespace) so the reconstruction's
`DCovariant.nprod` closure is `Core`-local and reusable. -/

/-- The `b`-derivative diagonal term of the Leibniz rule. -/
theorem NO_deriv_right_term (a b : FormalDist (End ℂ V)) (m s : ℤ) (x : V) :
    ((s + 1 - m : ℤ) • normalOrdered a b m (s + 1 - m)) x
      = normalOrdered a (VOA.deriv b) m (s - m) x := by
  rw [normalOrdered_apply, normalOrdered_apply, deriv_apply]
  rw [show (s - m + 1 : ℤ) = s + 1 - m from by ring]
  by_cases h : 0 ≤ m
  · rw [if_pos h, if_pos h, LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply,
      LinearMap.smul_apply, map_zsmul]
  · rw [if_neg h, if_neg h, LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply,
      LinearMap.smul_apply]

/-- The `a`-derivative diagonal term of the Leibniz rule (after the `m ↦ m-1` reindex). -/
theorem NO_deriv_left_term (a b : FormalDist (End ℂ V)) (m s : ℤ) (x : V) :
    normalOrdered (VOA.deriv a) b (m - 1) (s - (m - 1)) x
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
    VOA.deriv (nprod ha hb) = nprod (ha.deriv) hb + nprod ha (hb.deriv) := by
  funext s
  ext x
  rw [deriv_apply]
  show ((s + 1 : ℤ) • (nprod ha hb (s + 1))) x = (nprod (ha.deriv) hb s + nprod ha (hb.deriv) s) x
  rw [LinearMap.smul_apply, nprod_apply, LinearMap.add_apply, nprod_apply, nprod_apply,
    smul_finsum' (s + 1 : ℤ) (normalOrdered_diag_support_finite ha hb (s + 1) x)]
  have hsplit : ∀ m : ℤ, (s + 1 : ℤ) • normalOrdered a b m (s + 1 - m) x
      = normalOrdered (VOA.deriv a) b (m - 1) (s - (m - 1)) x
        + normalOrdered a (VOA.deriv b) m (s - m) x := by
    intro m
    rw [NO_deriv_left_term, ← NO_deriv_right_term, LinearMap.smul_apply, ← add_smul]
    congr 1; ring
  rw [finsum_congr hsplit]
  have hfinL : (Function.support
      (fun m : ℤ => normalOrdered (VOA.deriv a) b (m - 1) (s - (m - 1)) x)).Finite := by
    have hbase := normalOrdered_diag_support_finite ha.deriv hb s x
    apply Set.Finite.subset (hbase.image (· + 1))
    intro m hm
    rw [Function.mem_support] at hm
    exact ⟨m - 1, by rw [Function.mem_support]; exact hm, by ring⟩
  rw [finsum_add_distrib hfinL (normalOrdered_diag_support_finite ha hb.deriv s x)]
  congr 1
  rw [← finsum_int_pred_shift (fun m : ℤ => normalOrdered (VOA.deriv a) b m (s - m) x)]

namespace DCovariant

/-- per-term bracket identity: `[T,·]` of a `normalOrdered` term is the sum of the two
`deriv`-coefficient terms at the same index (Leibniz, no reindex). -/
theorem NO_term {T : End ℂ V} {a b : FormalDist (End ℂ V)} (ha : DCovariant T a)
    (hb : DCovariant T b) (p s : ℤ) (x : V) :
    T (normalOrdered a b p (s - p) x) - normalOrdered a b p (s - p) (T x)
      = normalOrdered (VOA.deriv a) b p (s - p) x
        + normalOrdered a (VOA.deriv b) p (s - p) x := by
  rw [normalOrdered_apply, normalOrdered_apply (a := VOA.deriv a),
    normalOrdered_apply (a := a) (b := VOA.deriv b), deriv_apply, deriv_apply]
  by_cases h : 0 ≤ p
  · rw [if_pos h, if_pos h, if_pos h]
    have key : T * (a p * b (s - p)) - (a p * b (s - p)) * T
        = ((p + 1 : ℤ) • a (p + 1)) * b (s - p) + a p * ((s - p + 1 : ℤ) • b (s - p + 1)) := by
      have e : T * (a p * b (s - p)) - (a p * b (s - p)) * T
          = (T * a p - a p * T) * b (s - p) + a p * (T * b (s - p) - b (s - p) * T) := by
        noncomm_ring
      rw [e, ha p, hb (s - p)]
    have hx := congrArg (fun (R : End ℂ V) => R x) key
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.mul_apply] using hx
  · rw [if_neg h, if_neg h, if_neg h]
    have key : T * (b (s - p) * a p) - (b (s - p) * a p) * T
        = b (s - p) * ((p + 1 : ℤ) • a (p + 1)) + ((s - p + 1 : ℤ) • b (s - p + 1)) * a p := by
      have e : T * (b (s - p) * a p) - (b (s - p) * a p) * T
          = b (s - p) * (T * a p - a p * T) + (T * b (s - p) - b (s - p) * T) * a p := by
        noncomm_ring
      rw [e, ha p, hb (s - p)]
    have hx := congrArg (fun (R : End ℂ V) => R x) key
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.mul_apply] using hx

/-- **`DCovariant` is closed under the normal-ordered product** (`:ab:` is `T`-covariant when
`a, b` are). -/
theorem nprod {T : End ℂ V} {a b : FormalDist (End ℂ V)} (haf : IsField a) (hbf : IsField b)
    (ha : DCovariant T a) (hb : DCovariant T b) :
    DCovariant T (VOA.nprod haf hbf) := by
  intro s
  apply LinearMap.ext
  intro x
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply,
    nprod_apply, nprod_apply, map_finsum T (normalOrdered_diag_support_finite haf hbf s x)]
  have hfinDL : (Function.support (fun p : ℤ => T (normalOrdered a b p (s - p) x))).Finite := by
    apply Set.Finite.subset (normalOrdered_diag_support_finite haf hbf s x)
    intro p hp
    rw [Function.mem_support] at hp ⊢
    exact fun hz => hp (by rw [hz, map_zero])
  rw [← finsum_sub_distrib hfinDL (normalOrdered_diag_support_finite haf hbf s (T x)),
    finsum_congr (fun p => NO_term ha hb p s x),
    finsum_add_distrib (normalOrdered_diag_support_finite haf.deriv hbf s x)
      (normalOrdered_diag_support_finite haf hbf.deriv s x),
    show (∑ᶠ p : ℤ, normalOrdered (VOA.deriv a) b p (s - p) x)
        = VOA.nprod haf.deriv hbf s x from (nprod_apply haf.deriv hbf s x).symm,
    show (∑ᶠ p : ℤ, normalOrdered a (VOA.deriv b) p (s - p) x)
        = VOA.nprod haf hbf.deriv s x from (nprod_apply haf hbf.deriv s x).symm]
  have hadd : (VOA.nprod haf.deriv hbf s) x + (VOA.nprod haf hbf.deriv s) x
      = (VOA.deriv (VOA.nprod haf hbf)) s x := by
    rw [deriv_nprod]; rfl
  rw [hadd, deriv_apply, LinearMap.smul_apply]

end DCovariant

/-! ## §2  Locality and field closure of finite `ℂ`-combinations

The basis-free `YA` of a state `u = ∑ cᵢ (st i)` is the matching field combination `∑ cᵢ (fld i)`.
For its VA4 locality and VA5 regularity we need: a finite `ℂ`-combination of pairwise-local fields
is local with each generator (hence with another such combination), and is again a field. -/

/-- Locality on the left is preserved by addition. -/
theorem Local.add_left {a b g : FormalDist (End ℂ V)} (h1 : Local a g) (h2 : Local b g) :
    Local (a + b) g := by
  obtain ⟨N1, hN1⟩ := h1
  obtain ⟨N2, hN2⟩ := h2
  refine ⟨max N1 N2, ?_⟩
  have hbd : bracketDist (a + b) g = bracketDist a g + bracketDist b g := by
    apply FormalDist₂.ext; intro m n
    rw [show (bracketDist a g + bracketDist b g) m n = bracketDist a g m n + bracketDist b g m n
        from rfl, bracketDist_apply, bracketDist_apply, bracketDist_apply]
    show (a m + b m) * g n - g n * (a m + b m) = a m * g n - g n * a m + (b m * g n - g n * b m)
    noncomm_ring
  rw [hbd, map_add, mulBySubPow_mono₂ (le_max_left N1 N2) hN1,
    mulBySubPow_mono₂ (le_max_right N1 N2) hN2, add_zero]

/-- The zero field is local with everything (on the left). -/
theorem Local.zero_left (g : FormalDist (End ℂ V)) : Local (0 : FormalDist (End ℂ V)) g := by
  refine local_of_bracketDist_eq_zero ?_
  apply FormalDist₂.ext; intro m n
  rw [bracketDist_apply]
  show (0 : FormalDist (End ℂ V)) m * g n - g n * (0 : FormalDist (End ℂ V)) m
      = (0 : FormalDist₂ (End ℂ V)) m n
  show (0 : End ℂ V) * g n - g n * (0 : End ℂ V) = (0 : End ℂ V)
  rw [zero_mul, mul_zero, sub_zero]

/-- A finite `Finset`-sum of fields each local with `g` is local with `g`. -/
theorem Local.sum_left {ι : Type*} (s : Finset ι) (f : ι → FormalDist (End ℂ V))
    (g : FormalDist (End ℂ V)) (h : ∀ i ∈ s, Local (f i) g) : Local (∑ i ∈ s, f i) g := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty]; exact Local.zero_left g
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact Local.add_left (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- The variable swap of a two-variable distribution (for locality symmetry). -/
private def swap₂ (G : FormalDist₂ (End ℂ V)) : FormalDist₂ (End ℂ V) := fun m n => G n m

private theorem swap₂_zero : swap₂ (0 : FormalDist₂ (End ℂ V)) = 0 := rfl

private theorem mulBySub_swap (G : FormalDist₂ (End ℂ V)) :
    mulBySub (swap₂ G) = - swap₂ (mulBySub G) := by
  apply FormalDist₂.ext; intro m n
  show G n (m - 1) - G (n - 1) m = -((mulBySub G) n m)
  rw [mulBySub_apply]; abel

private theorem mulBySubPow_swap_eq_zero : ∀ (N : ℕ) (G : FormalDist₂ (End ℂ V)),
    mulBySubPow N G = 0 → mulBySubPow N (swap₂ G) = 0 := by
  intro N; induction N with
  | zero => intro G hG; rw [mulBySubPow_zero] at hG
            have hz : G = 0 := by simpa using hG
            rw [mulBySubPow_zero, hz, swap₂_zero]; rfl
  | succ p ih =>
    intro G hG
    rw [mulBySubPow_succ', mulBySub_swap, map_neg]
    have h1 : mulBySubPow p (mulBySub G) = 0 := by rw [← mulBySubPow_succ']; exact hG
    rw [ih (mulBySub G) h1, neg_zero]

private theorem swap₂_bracketDist (a b : FormalDist (End ℂ V)) :
    swap₂ (bracketDist a b) = - bracketDist b a := by
  apply FormalDist₂.ext; intro m n
  show (bracketDist a b) n m = (- bracketDist b a) m n
  rw [bracketDist_apply]
  show a n * b m - b m * a n = -(bracketDist b a m n)
  rw [bracketDist_apply]; abel

/-- Mutual locality is symmetric. -/
theorem Local.symm {a b : FormalDist (End ℂ V)} (h : Local a b) : Local b a := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  have hs := mulBySubPow_swap_eq_zero N (bracketDist a b) hN
  rw [swap₂_bracketDist, map_neg, neg_eq_zero] at hs
  exact hs

/-- Locality is invariant under scaling on the right. -/
theorem Local.smulR (c : ℂ) {F G : FormalDist (End ℂ V)} (h : Local F G) : Local F (c • G) :=
  Local.symm (VertexOperatorAlgebra.Local.smul' c (Local.symm h))

/-- A finite `Finset`-sum of fields each local with `g` is local with `g` on the right. -/
theorem Local.sum_right {ι : Type*} (g : FormalDist (End ℂ V)) (s : Finset ι)
    (f : ι → FormalDist (End ℂ V)) (h : ∀ i ∈ s, Local g (f i)) : Local g (∑ i ∈ s, f i) :=
  Local.symm (Local.sum_left s f g (fun i hi => Local.symm (h i hi)))

/-- A finite `ℂ`-linear combination of generators (`Finsupp.linearCombination`) is local with any
field `g` local with every generator. -/
theorem Local_lc_left {ι : Type*} (fld : ι → FormalDist (End ℂ V)) (c : ι →₀ ℂ)
    (g : FormalDist (End ℂ V)) (h : ∀ i, Local (fld i) g) :
    Local (Finsupp.linearCombination ℂ fld c) g := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  exact Local.sum_left c.support (fun i => c i • fld i) g
    (fun i _ => VertexOperatorAlgebra.Local.smul' (c i) (h i))

/-- Two finite `ℂ`-linear combinations of pairwise-local generators are mutually local. -/
theorem Local_lc_lc {ι : Type*} (fld : ι → FormalDist (End ℂ V)) (c d : ι →₀ ℂ)
    (h : ∀ i j, Local (fld i) (fld j)) :
    Local (Finsupp.linearCombination ℂ fld c) (Finsupp.linearCombination ℂ fld d) := by
  rw [Finsupp.linearCombination_apply (v := fld) (l := d), Finsupp.sum]
  exact Local.sum_right _ d.support (fun j => d j • fld j)
    (fun j _ => Local.smulR (d j)
      (Local_lc_left fld c (fld j) (fun i => h i j)))

/-- A scalar multiple of a field is a field. -/
theorem isField_smul {a : FormalDist (End ℂ V)} (ha : IsField a) (c : ℂ) : IsField (c • a) := by
  intro x
  obtain ⟨B, hB⟩ := ha x
  exact ⟨B, fun n hn => by
    show (c • a n) x = 0
    rw [LinearMap.smul_apply, hB n hn, smul_zero]⟩

/-- A finite `Finset`-sum of fields is a field. -/
theorem isField_finsetSum {ι : Type*} (s : Finset ι) (f : ι → FormalDist (End ℂ V))
    (hf : ∀ i ∈ s, IsField (f i)) : IsField (∑ i ∈ s, f i) := by
  classical
  intro x
  induction s using Finset.induction with
  | empty => exact ⟨0, fun n _ => by rw [Finset.sum_empty]; rfl⟩
  | insert i s hi ih =>
      obtain ⟨B₁, hB₁⟩ := hf i (Finset.mem_insert_self i s) x
      obtain ⟨B₂, hB₂⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      refine ⟨min B₁ B₂, fun n hn => ?_⟩
      rw [Finset.sum_insert hi]
      show (f i n + (∑ j ∈ s, f j) n) x = 0
      rw [LinearMap.add_apply, hB₁ n (by omega), hB₂ n (by omega), add_zero]

/-- A finite `ℂ`-linear combination of fields is a field. -/
theorem isField_lc {ι : Type*} (fld : ι → FormalDist (End ℂ V)) (c : ι →₀ ℂ)
    (hf : ∀ i, IsField (fld i)) : IsField (Finsupp.linearCombination ℂ fld c) := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  exact isField_finsetSum c.support (fun i => c i • fld i)
    (fun i _ => isField_smul (hf i) (c i))

/-! ## §3  Evaluating a field combination at a coefficient and vector -/

/-- The `ℂ`-linear evaluation `g ↦ (g p) x` of a field at index `p` on the vector `x`. -/
def evalAt (p : ℤ) (x : V) : FormalDist (End ℂ V) →ₗ[ℂ] V where
  toFun g := (g p) x
  map_add' g h := by
    show ((g + h) p) x = (g p) x + (h p) x
    show (g p + h p) x = (g p) x + (h p) x
    rw [LinearMap.add_apply]
  map_smul' a g := by
    show ((a • g) p) x = a • ((g p) x)
    show (a • g p) x = a • ((g p) x)
    rw [LinearMap.smul_apply]

@[simp] theorem evalAt_apply (p : ℤ) (x : V) (g : FormalDist (End ℂ V)) :
    evalAt p x g = (g p) x := rfl

/-- Evaluating a field linear-combination at `(p, x)` is the scalar combination of the
evaluated generators: `(∑ cᵢ fldᵢ)_p x = ∑ cᵢ ((fldᵢ)_p x)`. -/
theorem lc_eval {ι : Type*} (fld : ι → FormalDist (End ℂ V)) (c : ι →₀ ℂ) (p : ℤ) (x : V) :
    (Finsupp.linearCombination ℂ fld c) p x
      = Finsupp.linearCombination ℂ (fun i => (fld i) p x) c := by
  have h := Finsupp.apply_linearCombination ℂ (evalAt p x) fld c
  simpa only [evalAt_apply] using h

/-! ## §4  The operator-first uniqueness (existence-direction Goddard)

A field annihilating the vacuum at every degree, mutually local with a creating test field for
each member of a spanning family of states, is the zero field — the engine that makes the
basis-free `YA` well-defined and linear. -/

/-- **Pointwise standalone Goddard.**  If `A` annihilates the vacuum at every degree and is local
with a test field `Gb` creating `b` from the vacuum as a power series, then `A m b = 0`.
(The single-test-field form of `Core.Goddard.goddard_zero`.) -/
theorem goddard_zero_at (vac b : V) (A Gb : FormalDist (End ℂ V))
    (hloc : Local A Gb) (hcre0 : Gb 0 vac = b) (hcreneg : ∀ q : ℤ, q < 0 → Gb q vac = 0)
    (hAvac : ∀ p : ℤ, A p vac = 0) (m : ℤ) : A m b = 0 := by
  obtain ⟨N, hN⟩ := hloc
  have hDeq : (fun p q : ℤ => A p ((Gb) q vac)) = applyVec vac (bracketDist A Gb) := by
    apply FormalDist₂.ext; intro p q
    show A p ((Gb) q vac) = applyVec vac (bracketDist A Gb) p q
    rw [applyVec_apply, bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.mul_apply, hAvac, map_zero, sub_zero]
  have hkill : mulBySubPow N (fun p q : ℤ => A p ((Gb) q vac)) = 0 := by
    rw [hDeq, ← applyVec_mulBySubPow, hN, applyVec_zero]
  have hbb : IsBddBelow₂ (fun p q : ℤ => A p ((Gb) q vac)) :=
    ⟨0, fun p q hq => by change A p ((Gb) q vac) = 0; rw [hcreneg q hq, map_zero]⟩
  have hD0 : (fun p q : ℤ => A p ((Gb) q vac)) = 0 :=
    eq_zero_of_mulBySubPow_of_bddBelow N _ hkill hbb
  have hfin := congrFun (congrFun hD0 m) 0
  change A m b = 0
  rw [← hcre0]; exact hfin

/-- **Operator-first uniqueness.**  A field `A` annihilating the vacuum at every degree, mutually
local with a creating test field `fld j` for each of a spanning family of states `st j`, is the
zero field. -/
theorem field_eq_zero_of_vacuum {ι : Type*} (vac : V) (A : FormalDist (End ℂ V))
    (st : ι → V) (fld : ι → FormalDist (End ℂ V))
    (hloc : ∀ j, Local A (fld j))
    (hcre0 : ∀ j, (fld j) 0 vac = st j)
    (hcreneg : ∀ j, ∀ q : ℤ, q < 0 → (fld j) q vac = 0)
    (hAvac : ∀ p : ℤ, A p vac = 0)
    (hspan : Submodule.span ℂ (Set.range st) = ⊤) :
    A = 0 := by
  funext m
  have hker : Submodule.span ℂ (Set.range st) ≤ LinearMap.ker (A m) := by
    rw [Submodule.span_le]
    rintro y ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact goddard_zero_at vac (st j) A (fld j) (hloc j) (hcre0 j) (hcreneg j) hAvac m
  rw [hspan] at hker
  exact LinearMap.ker_eq_top.mp (top_le_iff.mp hker)

/-- **Tower uniqueness**: two `T`-covariant fields creating the same vacuum base (and
annihilating the vacuum below `0`) have the *same* full vacuum-creation tower.  The induction
that pins `Y(u,z)|0⟩` from its constant term — the engine behind VOA3 translation. -/
theorem tower_unique {T : End ℂ V} {F G : FormalDist (End ℂ V)} {vac : V}
    (hF : DCovariant T F) (hG : DCovariant T G) (hTvac : T vac = 0)
    (hbase : F 0 vac = G 0 vac)
    (hFneg : ∀ q : ℤ, q < 0 → F q vac = 0) (hGneg : ∀ q : ℤ, q < 0 → G q vac = 0)
    (p : ℤ) : F p vac = G p vac := by
  by_cases hp : p < 0
  · rw [hFneg p hp, hGneg p hp]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) := ⟨p.toNat, by omega⟩
    clear hp
    induction n with
    | zero => rw [Nat.cast_zero]; exact hbase
    | succ i ih =>
        have hrec : ∀ H : FormalDist (End ℂ V), DCovariant T H →
            T (H (i : ℤ) vac) = ((i : ℤ) + 1) • H ((i : ℤ) + 1) vac := by
          intro H hH
          have h := congrArg (fun (R : End ℂ V) => R vac) (hH (i : ℤ))
          simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
          rwa [hTvac, map_zero, sub_zero] at h
        have hc : (((i : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := by rw [Int.cast_ne_zero]; omega
        have key : ((i : ℤ) + 1) • F ((i : ℤ) + 1) vac = ((i : ℤ) + 1) • G ((i : ℤ) + 1) vac := by
          rw [← hrec F hF, ← hrec G hG, ih]
        rw [← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1),
          ← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1)] at key
        rw [Nat.cast_succ]
        exact smul_right_injective V hc key

/-! ## §5  The reconstruction theorem -/

/-- `DCovariant` of a finite `ℂ`-linear combination of `T`-covariant generators. -/
theorem DCovariant_lc {ι : Type*} {T : End ℂ V} (fld : ι → FormalDist (End ℂ V)) (c : ι →₀ ℂ)
    (h : ∀ i, DCovariant T (fld i)) : DCovariant T (Finsupp.linearCombination ℂ fld c) := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  exact DCovariant.finsetSum c.support (fun i => c i • fld i)
    (fun i _ => (h i).smul (c i))

/-- **The operator-first reconstruction theorem** (Gannon §5.1; Kac §4.5, Existence theorem).
Given on a cyclic `ℂ`-module a generating family of pairwise-local `IsField`s `fld : ι → …` whose
vacuum-creation states `st i` span, together with a translation operator `T` (`T vac = 0`, each
generator `T`-covariant), there is a (unique) `ℂ`-linear `YA` with `YA (st i) = fld i`,
satisfying VA3 creation, VA4 locality, VA5 regularity, and translation covariance.  Built
basis-free from the standalone Goddard uniqueness `field_eq_zero_of_vacuum` (which the full
vacuum-creation tower — forced by `DCovariant T` and `T vac = 0` — feeds). -/
theorem reconstruct {ι : Type*} (vac : V) (st : ι → V) (fld : ι → FormalDist (End ℂ V))
    (T : End ℂ V)
    (hspan : Submodule.span ℂ (Set.range st) = ⊤)
    (hfield : ∀ i, IsField (fld i))
    (hlocal : ∀ i j, Local (fld i) (fld j))
    (hcre0 : ∀ i, (fld i) 0 vac = st i)
    (hcreneg : ∀ i, ∀ q : ℤ, q < 0 → (fld i) q vac = 0)
    (hTvac : T vac = 0)
    (hTcov : ∀ i, DCovariant T (fld i)) :
    ∃ YA : V →ₗ[ℂ] FormalDist (End ℂ V),
      (∀ i, YA (st i) = fld i) ∧
      (∀ u : V, IsField (YA u)) ∧
      (∀ u v : V, Local (YA u) (YA v)) ∧
      (∀ u : V, (YA u) 0 vac = u) ∧
      (∀ u : V, ∀ q : ℤ, q < 0 → (YA u) q vac = 0) ∧
      (∀ u : V, DCovariant T (YA u)) := by
  classical
  set S : (ι →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ st with hSdef
  set F : (ι →₀ ℂ) →ₗ[ℂ] FormalDist (End ℂ V) := Finsupp.linearCombination ℂ fld with hFdef
  have hSsurj : Function.Surjective S := by
    rw [← LinearMap.range_eq_top, hSdef, Finsupp.range_linearCombination, hspan]
  -- The vacuum-annihilation of any field combination whose state combination vanishes.
  have hFvac : ∀ c : (ι →₀ ℂ), S c = 0 → ∀ p : ℤ, (F c) p vac = 0 := by
    intro c hc p
    rcases lt_or_ge p 0 with hp | hp
    · rw [lc_eval, Finsupp.linearCombination_apply, Finsupp.sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [hcreneg i p hp, smul_zero]
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) := ⟨p.toNat, by omega⟩
      clear hp
      have hDcov : DCovariant T (F c) := DCovariant_lc fld c hTcov
      induction n with
      | zero =>
          rw [Nat.cast_zero, lc_eval]
          have hzc : Finsupp.linearCombination ℂ (fun i => (fld i) 0 vac) c = S c := by
            rw [hSdef, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
            exact Finsupp.sum_congr (fun i _ => by rw [hcre0 i])
          rw [hzc, hc]
      | succ n ih =>
          have hrec : T ((F c) (n : ℤ) vac) = ((n : ℤ) + 1) • (F c) ((n : ℤ) + 1) vac := by
            have h := congrArg (fun (R : End ℂ V) => R vac) (hDcov (n : ℤ))
            simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
            rwa [hTvac, map_zero, sub_zero] at h
          rw [ih] at hrec
          rw [map_zero] at hrec
          have hc' : (((n : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := by
            rw [Int.cast_ne_zero]; omega
          have hz : ((n : ℤ) + 1) • (F c) ((n : ℤ) + 1) vac = 0 := hrec.symm
          rw [← Int.cast_smul_eq_zsmul ℂ ((n : ℤ) + 1)] at hz
          have := smul_eq_zero.mp hz
          rcases this with h0 | h0
          · exact absurd h0 hc'
          · rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) from by push_cast; ring] at h0
            exact h0
  -- Well-definedness: `ker S ≤ ker F`.
  have hker : LinearMap.ker S ≤ LinearMap.ker F := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    refine field_eq_zero_of_vacuum vac (F c) st fld (fun j => ?_) hcre0 hcreneg
      (hFvac c hc) hspan
    exact Local_lc_left fld c (fld j) (fun i => hlocal i j)
  -- Build `YA` by factoring `F` through the surjection `S`.
  let YA : V →ₗ[ℂ] FormalDist (End ℂ V) :=
    (Submodule.liftQ (LinearMap.ker S) F hker).comp
      (S.quotKerEquivOfSurjective hSsurj).symm.toLinearMap
  have hYAcomp : ∀ c : (ι →₀ ℂ), YA (S c) = F c := by
    intro c
    show (Submodule.liftQ (LinearMap.ker S) F hker).comp
        (S.quotKerEquivOfSurjective hSsurj).symm.toLinearMap (S c) = F c
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  refine ⟨YA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `YA (st i) = fld i`
    intro i
    have hst : st i = S (Finsupp.single i 1) := by
      rw [hSdef, Finsupp.linearCombination_single, one_smul]
    rw [hst, hYAcomp, hFdef, Finsupp.linearCombination_single, one_smul]
  · -- IsField
    intro u
    obtain ⟨c, rfl⟩ := hSsurj u
    rw [hYAcomp]; exact isField_lc fld c hfield
  · -- Locality
    intro u v
    obtain ⟨c, rfl⟩ := hSsurj u
    obtain ⟨d, rfl⟩ := hSsurj v
    rw [hYAcomp, hYAcomp]; exact Local_lc_lc fld c d hlocal
  · -- creation base: `(YA u) 0 vac = u`
    intro u
    obtain ⟨c, rfl⟩ := hSsurj u
    rw [hYAcomp, lc_eval]
    have hzc : Finsupp.linearCombination ℂ (fun i => (fld i) 0 vac) c = S c := by
      rw [hSdef, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
      exact Finsupp.sum_congr (fun i _ => by rw [hcre0 i])
    rw [hzc]
  · -- creation tower below 0
    intro u q hq
    obtain ⟨c, rfl⟩ := hSsurj u
    rw [hYAcomp, lc_eval, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hcreneg i q hq, smul_zero]
  · -- translation covariance
    intro u
    obtain ⟨c, rfl⟩ := hSsurj u
    rw [hYAcomp]; exact DCovariant_lc fld c hTcov

end VOA.Reconstruction
