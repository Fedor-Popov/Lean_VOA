/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.SuperReconstruction

/-!
# Translation covariance of the super normal-ordered product

`reconstructε` needs every field in the spanning family to be `T`-covariant.  The generators are
handled by hand in each example; the *word* fields are iterated `nprodε`s, so covariance has to
propagate through the product.  This is the super analogue of
`Core.ReconstructionExistence.DCovariant.nprod`.

## The trick that makes this cheap

`normalOrderedε` differs from `normalOrdered` only by a scalar that depends on **`m` alone**:

`normalOrderedε ε a b m n = (if 0 ≤ m then 1 else ε) • normalOrdered a b m n`  (`normalOrderedε_eq`)

Every lemma below fixes `m` (or sums over it with the *same* `m` on both sides), so the scalar
factors straight through and the bosonic proof is reused verbatim.  The one place this fails is
`NO_deriv_left_termε`, which relates index `m-1` to index `m`: those scalars differ exactly at
`m = 0`, and there both sides vanish anyway, so it is a two-line case split rather than a new
argument.
-/

namespace VOA

open Module (End)
open VOA.Reconstruction

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **The super normal ordering is the bosonic one, rescaled by a factor depending only on the
first index.**  This is what lets the whole covariance layer be inherited. -/
theorem normalOrderedε_eq (ε : ℂ) (a b : FormalDist (End ℂ V)) (m n : ℤ) :
    normalOrderedε ε a b m n = (if 0 ≤ m then (1 : ℂ) else ε) • normalOrdered a b m n := by
  rw [normalOrderedε_apply, normalOrdered_apply]
  split_ifs <;> simp

/-! ### `Localε` is preserved by `∂_z`

Needed to build generator fields as derivatives of a basic current, exactly as in the bosonic
examples.  The `ε` is inert: `deriv` only rescales a mode, and a scalar commutes past the
Koszul factor. -/

theorem bracketDistε_deriv_left (ε : ℂ) (a b : FormalDist (End ℂ V)) :
    bracketDistε ε (VOA.deriv a) b = d1 (bracketDistε ε a b) := by
  apply FormalDist₂.ext; intro m n
  change (VOA.deriv a) m * b n - ε • (b n * (VOA.deriv a) m)
      = (m + 1) • bracketDistε ε a b (m + 1) n
  rw [deriv_apply, bracketDistε_apply, smul_sub, smul_mul_assoc, mul_smul_comm, smul_comm ε]

theorem bracketDistε_deriv_right (ε : ℂ) (a b : FormalDist (End ℂ V)) :
    bracketDistε ε a (VOA.deriv b) = d2 (bracketDistε ε a b) := by
  apply FormalDist₂.ext; intro m n
  change a m * (VOA.deriv b) n - ε • ((VOA.deriv b) n * a m)
      = (n + 1) • bracketDistε ε a b m (n + 1)
  rw [deriv_apply, bracketDistε_apply, smul_sub, mul_smul_comm, smul_mul_assoc, smul_comm ε]

theorem Localε.derivL {ε : ℂ} {a b : FormalDist (End ℂ V)} (h : Localε ε a b) :
    Localε ε (VOA.deriv a) b := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N + 1, by rw [bracketDistε_deriv_left]; exact mulBySubPow_succ_d1_of_zero N _ hN⟩

theorem Localε.derivR {ε : ℂ} {a b : FormalDist (End ℂ V)} (h : Localε ε a b) :
    Localε ε a (VOA.deriv b) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N + 1, by rw [bracketDistε_deriv_right]; exact mulBySubPow_succ_d2_of_zero N _ hN⟩

theorem Localε.deriv_iterate_left {ε : ℂ} {a b : FormalDist (End ℂ V)} (h : Localε ε a b)
    (i : ℕ) : Localε ε ((VOA.deriv^[i]) a) b := by
  induction i with
  | zero => simpa using h
  | succ p ih => rw [Function.iterate_succ', Function.comp_apply]; exact ih.derivL

theorem Localε.deriv_iterate_right {ε : ℂ} {a b : FormalDist (End ℂ V)} (h : Localε ε a b)
    (j : ℕ) : Localε ε a ((VOA.deriv^[j]) b) := by
  induction j with
  | zero => simpa using h
  | succ p ih => rw [Function.iterate_succ', Function.comp_apply]; exact ih.derivR

/-- The `b`-derivative diagonal term, super version. -/
theorem NO_deriv_right_termε (ε : ℂ) (a b : FormalDist (End ℂ V)) (m s : ℤ) (x : V) :
    ((s + 1 - m : ℤ) • normalOrderedε ε a b m (s + 1 - m)) x
      = normalOrderedε ε a (VOA.deriv b) m (s - m) x := by
  rw [normalOrderedε_eq, normalOrderedε_eq, LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, smul_comm, ← LinearMap.smul_apply, NO_deriv_right_term]

/-- The `a`-derivative diagonal term, super version.  The scalars at index `m-1` and `m` agree
except at `m = 0`, where both sides vanish. -/
theorem NO_deriv_left_termε (ε : ℂ) (a b : FormalDist (End ℂ V)) (m s : ℤ) (x : V) :
    normalOrderedε ε (VOA.deriv a) b (m - 1) (s - (m - 1)) x
      = (m : ℤ) • normalOrderedε ε a b m (s + 1 - m) x := by
  by_cases hm0 : m = 0
  · subst hm0
    rw [normalOrderedε_eq, normalOrderedε_eq]
    simp only [Int.cast_zero, zero_smul, LinearMap.smul_apply]
    rw [show ((0 : ℤ) - 1) = -1 from by ring]
    rw [if_neg (by norm_num : ¬ (0 : ℤ) ≤ -1)]
    rw [normalOrdered_apply, if_neg (by norm_num : ¬ (0 : ℤ) ≤ -1), deriv_apply]
    simp
  · have hsc : (if (0 : ℤ) ≤ m - 1 then (1 : ℂ) else ε) = (if (0 : ℤ) ≤ m then (1 : ℂ) else ε) := by
      by_cases h : 0 ≤ m
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    rw [normalOrderedε_eq, normalOrderedε_eq, hsc, LinearMap.smul_apply, LinearMap.smul_apply,
      NO_deriv_left_term, smul_comm]

/-- **Field Leibniz rule** for the super normal-ordered product. -/
theorem deriv_nprodε (ε : ℂ) {a b : FormalDist (End ℂ V)} (ha : IsField a) (hb : IsField b) :
    VOA.deriv (nprodε ε ha hb)
      = nprodε ε (ha.deriv) hb + nprodε ε ha (hb.deriv) := by
  funext s
  ext x
  rw [deriv_apply]
  show ((s + 1 : ℤ) • (nprodε ε ha hb (s + 1))) x
      = (nprodε ε (ha.deriv) hb s + nprodε ε ha (hb.deriv) s) x
  rw [LinearMap.smul_apply, nprodε_apply, LinearMap.add_apply, nprodε_apply, nprodε_apply,
    smul_finsum' (s + 1 : ℤ) (normalOrderedε_diag_support_finite ε ha hb (s + 1) x)]
  have hsplit : ∀ m : ℤ, (s + 1 : ℤ) • normalOrderedε ε a b m (s + 1 - m) x
      = normalOrderedε ε (VOA.deriv a) b (m - 1) (s - (m - 1)) x
        + normalOrderedε ε a (VOA.deriv b) m (s - m) x := by
    intro m
    rw [NO_deriv_left_termε, ← NO_deriv_right_termε, LinearMap.smul_apply, ← add_smul]
    congr 1; ring
  rw [finsum_congr hsplit]
  have hfinL : (Function.support
      (fun m : ℤ => normalOrderedε ε (VOA.deriv a) b (m - 1) (s - (m - 1)) x)).Finite := by
    have hbase := normalOrderedε_diag_support_finite ε ha.deriv hb s x
    apply Set.Finite.subset (hbase.image (· + 1))
    intro m hm
    rw [Function.mem_support] at hm
    exact ⟨m - 1, by rw [Function.mem_support]; exact hm, by ring⟩
  rw [finsum_add_distrib hfinL (normalOrderedε_diag_support_finite ε ha hb.deriv s x)]
  congr 1
  rw [← finsum_int_pred_shift
    (fun m : ℤ => normalOrderedε ε (VOA.deriv a) b m (s - m) x)]

namespace DCovariant

/-- Per-term bracket identity, super version: the scalar factors through because the index `p` is
the same on both sides. -/
theorem NO_termε {T : End ℂ V} (ε : ℂ) {a b : FormalDist (End ℂ V)} (ha : DCovariant T a)
    (hb : DCovariant T b) (p s : ℤ) (x : V) :
    T (normalOrderedε ε a b p (s - p) x) - normalOrderedε ε a b p (s - p) (T x)
      = normalOrderedε ε (VOA.deriv a) b p (s - p) x
        + normalOrderedε ε a (VOA.deriv b) p (s - p) x := by
  rw [normalOrderedε_eq, normalOrderedε_eq, normalOrderedε_eq, LinearMap.smul_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, ← smul_sub,
    ← smul_add, Reconstruction.DCovariant.NO_term ha hb p s x]

/-- **`DCovariant` is closed under the super normal-ordered product.** -/
theorem nprodε {T : End ℂ V} (ε : ℂ) {a b : FormalDist (End ℂ V)}
    (haf : IsField a) (hbf : IsField b) (ha : DCovariant T a) (hb : DCovariant T b) :
    DCovariant T (VOA.nprodε ε haf hbf) := by
  intro s
  apply LinearMap.ext
  intro x
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply,
    nprodε_apply, nprodε_apply, map_finsum T (normalOrderedε_diag_support_finite ε haf hbf s x)]
  have hfinDL : (Function.support
      (fun p : ℤ => T (normalOrderedε ε a b p (s - p) x))).Finite := by
    apply Set.Finite.subset (normalOrderedε_diag_support_finite ε haf hbf s x)
    intro p hp
    rw [Function.mem_support] at hp ⊢
    exact fun hz => hp (by rw [hz, map_zero])
  rw [← finsum_sub_distrib hfinDL (normalOrderedε_diag_support_finite ε haf hbf s (T x)),
    finsum_congr (fun p => NO_termε ε ha hb p s x),
    finsum_add_distrib (normalOrderedε_diag_support_finite ε haf.deriv hbf s x)
      (normalOrderedε_diag_support_finite ε haf hbf.deriv s x),
    show (∑ᶠ p : ℤ, normalOrderedε ε (VOA.deriv a) b p (s - p) x)
        = VOA.nprodε ε haf.deriv hbf s x from (nprodε_apply ε haf.deriv hbf s x).symm,
    show (∑ᶠ p : ℤ, normalOrderedε ε a (VOA.deriv b) p (s - p) x)
        = VOA.nprodε ε haf hbf.deriv s x from (nprodε_apply ε haf hbf.deriv s x).symm]
  have hadd : (VOA.nprodε ε haf.deriv hbf s) x
      + (VOA.nprodε ε haf hbf.deriv s) x
      = (VOA.deriv (VOA.nprodε ε haf hbf)) s x := by
    rw [deriv_nprodε]; rfl
  rw [hadd, deriv_apply, LinearMap.smul_apply]

end DCovariant

/-! ## Vacuum behaviour of the super normal product

The `ε` is invisible here: in the `m < 0` branch the value is already zero before the Koszul
factor multiplies it, and the base term sits at `m = 0`, on the unsigned side of the split. -/

/-- `:g(z)h(z):` annihilates the vacuum below degree `0`. -/
theorem nprodε_vacuum_neg_gen (ε : ℂ) {g h : FormalDist (End ℂ V)} (hg : IsField g)
    (hh : IsField h) (vac : V) (hgvac : ∀ q : ℤ, q < 0 → g q vac = 0)
    (hhvac : ∀ q : ℤ, q < 0 → h q vac = 0) {s : ℤ} (hs : s < 0) :
    nprodε ε hg hh s vac = 0 := by
  rw [nprodε_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  rw [normalOrderedε_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, Module.End.mul_apply, hhvac (s - m) (by omega), map_zero]
  · rw [if_neg hm, LinearMap.smul_apply, Module.End.mul_apply, hgvac m (by omega), map_zero,
      smul_zero]

/-- The base vacuum value `:g(z)h(z):₀ vac = g₀ (h₀ vac)`. -/
theorem nprodε_vacuum_base_gen (ε : ℂ) {g h : FormalDist (End ℂ V)} (hg : IsField g)
    (hh : IsField h) (vac : V) (hgvac : ∀ q : ℤ, q < 0 → g q vac = 0)
    (hhvac : ∀ q : ℤ, q < 0 → h q vac = 0) :
    nprodε ε hg hh 0 vac = g 0 (h 0 vac) := by
  rw [nprodε_apply, finsum_eq_single _ 0]
  · rw [normalOrderedε_apply, if_pos le_rfl, Module.End.mul_apply,
      show (0 : ℤ) - 0 = 0 from by ring]
  · intro m hm
    rw [normalOrderedε_apply]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0, Module.End.mul_apply, hhvac (0 - m) (by omega), map_zero]
    · rw [if_neg h0, LinearMap.smul_apply, Module.End.mul_apply, hgvac m (by omega), map_zero,
        smul_zero]

end VOA
