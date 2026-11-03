/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.SCLie
import VOA.AffineGeneral.RootSpaceSimple
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Algebra.Lie.TraceForm

/-!
# Simplicity of a structure-constant Lie algebra from root tables

`isSimple_of_tables` applies the root-space criterion `RootSpace.isSimple_of_roots` to `SCLie.Alg N T hc`.
The root vectors are basis vectors `b_{rootIdx β}`, the coroots are `hb α = ⁅e α, e (neg α)⁆` (in
the concrete tables this is *minus* the standard coroot: `g2_coroot`, `f4_coroot`,
`e6_coroot` give `⁅hb θ, e θ⁆ = -2 e θ`; the sign is irrelevant to the simplicity criterion), and every
hypothesis of the criterion becomes a finite check on sparse lists or integer tables (`RootChecks`), decided
by kernel reduction for a concrete algebra.  The centre condition comes from `center_of_simple`: the coroots
are integral combinations `M` of simple coroots, and the simple pairing matrix has a right inverse `Q`.
-/

namespace VOA.AffineGeneral

namespace RootSpace

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] {R : Type*} [Fintype R]
variable {e hb : R → L} {pair : R → R → ℂ}

/-- **Trivial centralizer from simple coroots.** -/
theorem center_of_simple (hbe : ∀ α β, ⁅hb α, e β⁆ = pair α β • e β) (he0 : ∀ β, e β ≠ 0)
    {r : ℕ} (s : Fin r → R) (M : R → Fin r → ℂ) (hM : ∀ α, hb α = ∑ i, M α i • hb (s i))
    (Q : Fin r → Fin r → ℂ)
    (hQ : ∀ i j, ∑ k, pair (s i) (s k) * Q k j = if i = j then 1 else 0)
    (y : L) (hy : y ∈ Submodule.span ℂ (Set.range hb)) (h : ∀ β, ⁅y, e β⁆ = 0) : y = 0 := by
  have hle : Submodule.span ℂ (Set.range hb) ≤ Submodule.span ℂ (Set.range fun i => hb (s i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    rw [hM α]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hle hy)
  have hk : ∀ k, ∑ i, d i * pair (s i) (s k) = 0 := by
    intro k
    have := h (s k)
    rw [sum_lie] at this
    simp only [smul_lie, hbe, smul_smul] at this
    rw [← Finset.sum_smul] at this
    exact (smul_eq_zero.mp this).resolve_right (he0 _)
  have hd : ∀ j, d j = 0 := by
    intro j
    calc d j = ∑ i, d i * (if i = j then 1 else 0) := by simp
      _ = ∑ i, d i * ∑ k, pair (s i) (s k) * Q k j := by simp only [hQ]
      _ = ∑ k, (∑ i, d i * pair (s i) (s k)) * Q k j := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by simp [hk]
  simp [hd]

/-- Reachability certified by a distance function. -/
theorem reach_of_dist' {n : ℕ} {rel : Fin n → Fin n → Prop} (i0 : Fin n) (d : Fin n → ℕ)
    (hd : ∀ i, i = i0 ∨ ∃ j, d j < d i ∧ rel j i) (i : Fin n) : Relation.ReflTransGen rel i0 i := by
  induction h : d i using Nat.strong_induction_on generalizing i with
  | _ m ih =>
    rcases hd i with rfl | ⟨j, hj, hr⟩
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail (ih (d j) (h ▸ hj) j rfl) hr

end RootSpace

namespace SCLie

variable {N : ℕ} {T : Table}

/-- The root tables of a structure-constant algebra. -/
structure RootData (N : ℕ) where
  nr : ℕ
  rootIdx : Fin nr → Fin N
  neg : Fin nr → Fin nr
  pairT : Fin nr → Fin nr → ℤ
  r : ℕ
  simple : Fin r → Fin nr
  M : Fin nr → Fin r → ℤ
  Q : Fin r → Fin r → ℚ
  base : Fin nr
  dist : Fin nr → ℕ

variable (T) in
/-- Sparse root vector. -/
def eL (D : RootData N) (β : Fin D.nr) : List (ℕ × ℤ) := [((D.rootIdx β : ℕ), 1)]

variable (T) in
/-- Sparse coroot `⁅e α, e (neg α)⁆` (up to sign: minus the standard coroot in the concrete tables).
-/
def hL (D : RootData N) (α : Fin D.nr) : List (ℕ × ℤ) := brL T (eL D α) (eL D (D.neg α))

/-- The finite checks. -/
structure RootChecks (T : Table) (D : RootData N) : Prop where
  inRange_h : ∀ α, inRange N (hL T D α) = true
  hbe : ∀ α β, zeroL (brL T (hL T D α) (eL D β) ++ scale (-(D.pairT α β)) (eL D β)) = true
  hhb : ∀ α β, zeroL (brL T (hL T D α) (hL T D β)) = true
  diag : ∀ α, D.pairT α α ≠ 0
  sep : ∀ α β, α ≠ β → ∃ γ, D.pairT γ α ≠ D.pairT γ β
  symm : ∀ α β, D.pairT α β ≠ 0 → D.pairT β α ≠ 0
  M : ∀ α, zeroL (hL T D α ++ scale (-1)
    ((List.finRange D.r).flatMap fun i => scale (D.M α i) (hL T D (D.simple i)))) = true
  Q : ∀ i j, ∑ k, (D.pairT (D.simple i) (D.simple k) : ℚ) * D.Q k j = if i = j then 1 else 0
  conn : ∀ β, β = D.base ∨ ∃ γ, D.dist γ < D.dist β ∧ D.pairT γ β ≠ 0
  span : ∀ k : Fin N, (∃ β, D.rootIdx β = k) ∨
    ∃ i, zeroL (hL T D (D.simple i) ++ [((k : ℕ), 1)]) = true ∨
      zeroL (hL T D (D.simple i) ++ [((k : ℕ), -1)]) = true

variable (hc : Checks N T) (D : RootData N)

theorem eL_inRange (β : Fin D.nr) : inRange N (eL D β) = true := by
  simp [inRange, eL]

/-- Root vectors. -/
noncomputable def eV (β : Fin D.nr) : Alg N T hc := basis hc (D.rootIdx β)

/-- Coroots `⁅e α, e (neg α)⁆`, up to sign: for the concrete tables `hbV` is minus the standard
coroot (`g2_coroot`, `f4_coroot`, `e6_coroot`: `⁅hbV θ, e θ⁆ = -2 e θ`). -/
noncomputable def hbV (α : Fin D.nr) : Alg N T hc := ⁅eV hc D α, eV hc D (D.neg α)⁆

theorem eV_eq (β : Fin D.nr) : eV hc D β = vec hc (eL D β) := basis_eq_vec hc _

theorem hbV_eq (α : Fin D.nr) : hbV hc D α = vec hc (hL T D α) := by
  rw [hbV, eV_eq, eV_eq, lie_vec hc (eL_inRange D α) (eL_inRange D _)]
  rfl

/-- **A structure-constant algebra with checked root tables is simple.** -/
theorem isSimple_of_tables (hD : RootChecks T D) [Nonempty (Fin D.nr)] :
    LieAlgebra.IsSimple ℂ (Alg N T hc) := by
  classical
  have hbe : ∀ α β, ⁅hbV hc D α, eV hc D β⁆ = ((D.pairT α β : ℤ) : ℂ) • eV hc D β := by
    intro α β
    rw [hbV_eq, eV_eq, lie_vec hc (hD.inRange_h α) (eL_inRange D β)]
    exact vec_eq_of_zeroL hc _ (hD.hbe α β)
  have he0 : ∀ β, eV hc D β ≠ 0 := fun β => (basis hc).ne_zero _
  refine RootSpace.isSimple_of_roots (eV hc D) (hbV hc D) (fun α β => ((D.pairT α β : ℤ) : ℂ))
    ?_ he0 hbe ?_ ?_ ?_ D.neg (fun α => ⟨1, one_ne_zero, (one_smul ℂ _).symm⟩) ?_ ?_
  · -- spanning
    rw [eq_top_iff, ← (basis hc).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rcases hD.span k with ⟨β, hβ⟩ | ⟨i, hi | hi⟩
    · exact Submodule.subset_span (Or.inl ⟨β, by rw [eV, hβ]⟩)
    · have h1 : vec hc (hL T D (D.simple i)) = ((-1 : ℤ) : ℂ) • vec hc [((k : ℕ), 1)] :=
        vec_eq_of_zeroL hc _ (by simpa [scale] using hi)
      rw [← hbV_eq, ← basis_eq_vec] at h1
      have : basis hc k = -hbV hc D (D.simple i) := by rw [h1]; simp
      rw [this]
      exact Submodule.neg_mem _ (Submodule.subset_span (Or.inr ⟨_, rfl⟩))
    · have h1 : vec hc (hL T D (D.simple i)) = ((1 : ℤ) : ℂ) • vec hc [((k : ℕ), 1)] :=
        vec_eq_of_zeroL hc _ (by simpa [scale] using hi)
      rw [← hbV_eq, ← basis_eq_vec] at h1
      have : basis hc k = hbV hc D (D.simple i) := by rw [h1]; simp
      rw [this]
      exact Submodule.subset_span (Or.inr ⟨_, rfl⟩)
  · -- coroots commute
    intro α β
    rw [hbV_eq, hbV_eq, lie_vec hc (hD.inRange_h α) (hD.inRange_h β)]
    exact vec_eq_zero_of_zeroL hc (hD.hhb α β)
  · intro α
    show ((D.pairT α α : ℤ) : ℂ) ≠ 0
    exact_mod_cast hD.diag α
  · intro α β hne
    obtain ⟨γ, hγ⟩ := hD.sep α β hne
    exact ⟨γ, by show ((D.pairT γ α : ℤ) : ℂ) ≠ ((D.pairT γ β : ℤ) : ℂ); exact_mod_cast hγ⟩
  · -- centre
    refine fun y hy hz => RootSpace.center_of_simple hbe he0 D.simple
      (fun α i => ((D.M α i : ℤ) : ℂ)) (fun α => ?_) (fun i j => ((D.Q i j : ℚ) : ℂ)) (fun i j => ?_) y hy hz
    · have h := vec_eq_of_zeroL hc 1 (by simpa using hD.M α)
      rw [← hbV_eq, Int.cast_one, one_smul] at h
      rw [h]
      funext n
      change (coef ((List.finRange D.r).flatMap fun i => scale (D.M α i) (hL T D (D.simple i))) n : ℂ)
        = ((∑ i, ((D.M α i : ℤ) : ℂ) • hbV hc D (D.simple i) : Alg N T hc) : Fin N → ℂ) n
      rw [sum_apply', Fin.sum_univ_def, coef_flatMap, Int.cast_list_sum, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, coef_scale, Int.cast_mul, smul_apply', hbV_eq]
      rfl
    · have h2 := congrArg (fun q : ℚ => (q : ℂ)) (hD.Q i j)
      simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast] at h2
      rw [h2]
      split_ifs <;> simp
  · -- connectivity
    have hsymm : Symmetric fun a b : Fin D.nr => ((D.pairT a b : ℤ) : ℂ) ≠ 0 := by
      intro a b h
      have h' : D.pairT a b ≠ 0 := by exact_mod_cast h
      exact_mod_cast hD.symm a b h'
    have hreach : ∀ β, Relation.ReflTransGen (fun a b : Fin D.nr => ((D.pairT a b : ℤ) : ℂ) ≠ 0)
        D.base β := RootSpace.reach_of_dist' D.base D.dist (fun β => by
          rcases hD.conn β with h | ⟨γ, h1, h2⟩
          · exact Or.inl h
          · exact Or.inr ⟨γ, h1, by exact_mod_cast h2⟩)
    intro α β
    exact (Relation.ReflTransGen.symmetric hsymm (hreach α)).trans (hreach β)

/-- **The Killing form of a sparse vector**, as a finite sum of sparse coefficients. -/
theorem killing_vec (l : List (ℕ × ℤ)) (hl : inRange N l = true)
    (hk : ∀ k : Fin N, inRange N (brL T l [((k : ℕ), 1)]) = true) :
    killingForm ℂ (Alg N T hc) (vec hc l) (vec hc l)
      = ∑ k : Fin N, (coef (brL T l (brL T l [((k : ℕ), 1)])) k : ℂ) := by
  classical
  rw [killingForm_apply_apply, LinearMap.trace_eq_matrix_trace ℂ (basis hc), Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hs : inRange N [((k : ℕ), 1)] = true := by simp [inRange]
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.comp_apply, LieAlgebra.ad_apply,
    LieAlgebra.ad_apply, basis_eq_vec, lie_vec hc hl hs, lie_vec hc hl (hk k)]
  rfl

end SCLie

end VOA.AffineGeneral
