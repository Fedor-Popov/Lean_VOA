/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.GradedUnitarity
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# The prefix no-wall lemma

This file proves, for an arbitrary vertex operator algebra with an invariant bilinear form `B`,
an anti-linear `ρ` and a graded flag `F`, the **prefix no-wall lemma** of the below-critical
ordinary-PBW graded-unitarity argument (the "no wall" lemma of the below-critical prefix).

The current-algebra input is packaged abstractly as a `CurrentSystem`: a finite family of mode
operators `x^i_m` which

* are Hermitian-adjoint to `x^{adj i}_{-m}` for the form `h(a,b) = B(ρa, b)`;
* preserve the flag for `m ≥ 0` and raise its degree by at most one for `m < 0`;
* span every positive weight space by negative modes; and
* satisfy a **Sugawara energy identity**
  `λ_E h(v,v) = Σ_i z_i h(x^i_0 v, x^i_0 v) + Σ_i Σ_{1 ≤ m ≤ E} w_i h(x^i_m v, x^i_m v)`
  with strictly positive real weights `w_i`.

The theorem `layerNondegenerate_of_lower` says: if every lower weight `E - m` (`m ≥ 1`) has the
graded-unitary layer signs, and the full weight-`E` form is nondegenerate, then **every step** of
the flag at weight `E` is nondegenerate.  The proof is the one of the source note: a prefix
radical vector `v` is killed by all positive modes, because each `x^i_m v` lies in a lower layer
of a single sign `(-1)^r` and the Sugawara identity forces the sum of their signed norms to vanish;
then `v` pairs to zero with every negative-mode image, i.e. with the whole weight space.

Nothing here is specific to affine `sl₂` or to the ordinary flag; the same statement applies, for
example, to any flag on a simple quotient whose currents satisfy the listed mode properties.

⚠ This lemma proves **nondegeneracy of prefixes only**.  It says nothing about the signs of the
new layers at weight `E`; those come, in the below-critical argument, from a continuity/anchor
argument in the level, which is not part of this file.
-/

namespace VOA

namespace BelowCriticalNoWall

open VOA.VertexOperatorAlgebra
open LinearMap (BilinForm)

universe u

/-- In finite dimension a bilinear form that separates in its **second** slot is nondegenerate.
(Mathlib's `Nondegenerate` asks for both slots.) -/
theorem nondegenerate_of_separatingRight {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (β : BilinForm ℂ E) (h : ∀ y, (∀ x, β x y = 0) → y = 0) :
    β.Nondegenerate := by
  let b := Module.finBasis ℂ E
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b]
  exact (LinearMap.separatingRight_iff_det_ne_zero b).mp h

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **Abstract current data for the no-wall lemma.**  See the file docstring for the meaning of
each field.  The index type `ι` is finite; `mode i m` is the operator `x^i_m`. -/
structure CurrentSystem (ι : Type*) [Fintype ι] (B : InvariantForm W) (R : RealStructure W)
    (F : GradedFlag W) where
  /-- The mode operators `x^i_m`. -/
  mode : ι → ℤ → Module.End ℂ 𝒱
  /-- The Hermitian-adjoint colour. -/
  adj : ι → ι
  adj_adj : ∀ i, adj (adj i) = i
  /-- `x^i_m` lowers the conformal weight by `m`. -/
  mode_grading : ∀ (i : ι) (m : ℤ) {n : ℤ} {x : 𝒱}, x ∈ W.grading n →
    mode i m x ∈ W.grading (n - m)
  /-- Hermitian adjointness `h(x^i_m a, b) = h(a, x^{adj i}_{-m} b)` for `h(a,b) = B(ρa,b)`. -/
  sesq_adj : ∀ (i : ι) (m : ℤ) (a b : 𝒱),
    sesqForm B R (mode i m a) b = sesqForm B R a (mode (adj i) (-m) b)
  /-- Nonnegative modes preserve the flag degree. -/
  nonneg_mem : ∀ (i : ι) {m : ℤ} {p : ℕ} {n : ℤ} {x : 𝒱}, 0 ≤ m → x ∈ F.piece p n →
    mode i m x ∈ F.piece p (n - m)
  /-- Negative modes raise the flag degree by at most one. -/
  neg_mem : ∀ (i : ι) {m : ℤ} {p : ℕ} {n : ℤ} {x : 𝒱}, 0 < m → x ∈ F.piece p n →
    mode i (-m) x ∈ F.piece (p + 1) (n + m)
  /-- Every positive weight space is spanned by negative-mode images. -/
  creation_span : ∀ {n : ℤ}, 0 < n → W.grading n ≤ Submodule.span ℂ
    {x | ∃ (i : ι) (m : ℕ) (y : 𝒱), 0 < m ∧ y ∈ W.grading (n - m) ∧ x = mode i (-(m : ℤ)) y}
  /-- Positive Sugawara weights. -/
  wt : ι → ℝ
  wt_pos : ∀ i, 0 < wt i
  /-- The coefficient of `h(v,v)` in the energy identity (for affine algebras `2(k+h^∨)E`). -/
  lam : ℤ → ℂ
  /-- The zero-mode coefficients (their sign is irrelevant). -/
  zc : ι → ℂ
  /-- **The Sugawara energy identity.** -/
  sugawara : ∀ {n : ℤ} {v : 𝒱}, v ∈ W.grading n →
    lam n * sesqForm B R v v =
      (∑ i, zc i * sesqForm B R (mode i 0 v) (mode i 0 v)) +
        ∑ i, ∑ m ∈ Finset.Icc 1 n.toNat,
          (wt i : ℂ) * sesqForm B R (mode i (m : ℤ) v) (mode i (m : ℤ) v)
  /-- `ρ` preserves every flag piece. -/
  rho_piece : ∀ {p : ℕ} {n : ℤ} {x : 𝒱}, x ∈ F.piece p n → R.rho x ∈ F.piece p n
  /-- `ρ` preserves every weight space. -/
  rho_grading : ∀ {n : ℤ} {x : 𝒱}, x ∈ W.grading n → R.rho x ∈ W.grading n
  /-- The parity scalar of `ρ² ` is invertible. -/
  parity_ne_zero : ∀ n, R.parity n ≠ 0

variable {B : InvariantForm W} {R : RealStructure W} {F : GradedFlag W}

/-- Sesquilinear orthogonality against a `ρ`-stable set inside one weight space implies bilinear
orthogonality against the same set. -/
theorem form_eq_zero_of_sesq {n : ℤ} {S : Set 𝒱} (hS : ∀ x ∈ S, R.rho x ∈ S)
    (hSn : ∀ x ∈ S, x ∈ W.grading n) (hp : R.parity n ≠ 0) {v : 𝒱}
    (h : ∀ x ∈ S, sesqForm B R x v = 0) : ∀ x ∈ S, B.form x v = 0 := by
  intro x hx
  have h0 := h (R.rho x) (hS x hx)
  rw [sesqForm_apply, R.sq x (hSn x hx), map_smul, LinearMap.smul_apply, smul_eq_mul] at h0
  exact (mul_eq_zero.mp h0).resolve_left hp

theorem sesq_zero_right (a : 𝒱) : sesqForm B R a 0 = 0 := by
  simp [sesqForm]


/-- The sign bookkeeping: a nonzero vector of a layer with the graded-unitary sign has strictly
positive signed norm; zero has zero.  Recorded on real and imaginary parts. -/
theorem signed_norm_props {n : ℤ} {r : ℕ} [FiniteDimensional ℂ (W.grading n)]
    (hpos : LayerPositive F n (LiRadical.gradedForm B n) (gradedSesq B R n))
    (u : W.grading n) (hu : u ∈ F.layer n (LiRadical.gradedForm B n) r) :
    ((-1 : ℂ) ^ r * sesqForm B R u u).im = 0 ∧ 0 ≤ ((-1 : ℂ) ^ r * sesqForm B R u u).re ∧
      (((-1 : ℂ) ^ r * sesqForm B R u u).re = 0 → u = 0) := by
  by_cases hz : u = 0
  · subst hz
    simp [sesqForm]
  · obtain ⟨s, hs, hsu⟩ := hpos r u hu hz
    have hsu' : (-1 : ℂ) ^ r * sesqForm B R u u = (s : ℂ) := hsu
    rw [hsu']
    refine ⟨Complex.ofReal_im s, by simp [hs.le], fun h => ?_⟩
    simp only [Complex.ofReal_re] at h
    exact absurd h hs.ne'

namespace CurrentSystem

variable {ι : Type*} [Fintype ι] (S : CurrentSystem ι B R F)
include S

/-- The adjunction read in the other direction. -/
theorem sesq_adj' (i : ι) (m : ℤ) (a b : 𝒱) :
    sesqForm B R a (S.mode i m b) = sesqForm B R (S.mode (S.adj i) (-m) a) b := by
  rw [S.sesq_adj, neg_neg, S.adj_adj]

/-- A vector sesquilinearly orthogonal (in the second slot) to all negative-mode images is
orthogonal to a whole positive weight space, once all positive modes kill it. -/
theorem sesq_eq_zero_of_pos_kill {n : ℤ} (hn : 0 < n) {v : 𝒱}
    (hkill : ∀ (i : ι) (m : ℕ), 0 < m → S.mode i (m : ℤ) v = 0) :
    ∀ x ∈ W.grading n, sesqForm B R x v = 0 := by
  intro x hx
  have hx' := S.creation_span hn hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i, m, y, hm, -, rfl⟩ := hz
      rw [S.sesq_adj, neg_neg, hkill (S.adj i) m hm, sesq_zero_right]
  | zero => simp [sesqForm]
  | add a b _ _ ha hb => rw [sesqForm_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [sesqForm_smul_left, ha, mul_zero]

/-- **The core of the prefix no-wall lemma.**  A vector of `F_r(E)` that is bilinearly
orthogonal (in the second slot) to all of `F_r(E)` is zero, provided the lower weights carry the
graded-unitary layer signs and the full weight-`E` form separates in its second slot. -/
theorem radical_eq_zero (E : ℤ) (r : ℕ)
    (hfull : ∀ v ∈ W.grading E, (∀ x ∈ W.grading E, B.form x v = 0) → v = 0)
    (hlower : ∀ m : ℕ, 0 < m →
      LayerPositive F (E - m) (LiRadical.gradedForm B (E - m)) (gradedSesq B R (E - m)))
    {v : 𝒱} (hv : v ∈ F.piece r E) (hrad : ∀ w ∈ F.piece r E, B.form w v = 0) : v = 0 := by
  have hvE : v ∈ W.grading E := F.le_grading r E hv
  -- `v` is sesquilinearly orthogonal to `F_r(E)`.
  have hsrad : ∀ w ∈ F.piece r E, sesqForm B R w v = 0 := fun w hw =>
    hrad (R.rho w) (S.rho_piece hw)
  rcases lt_trichotomy E 0 with hneg | hzero | hposE
  · -- negative weight: the space is zero
    have := W.positivity E hneg
    rw [this] at hvE
    exact (Submodule.mem_bot ℂ).mp hvE
  · -- weight zero: `F_r(0)` is the whole weight space
    subst hzero
    apply hfull v hvE
    intro x hx
    have hx' : x ∈ F.piece r 0 := by
      have h0 : F.piece 0 0 ≤ F.piece r 0 := F.mono 0 (Nat.zero_le r)
      rw [F.vacuum_zero, ← W.vacuum_grade] at h0
      exact h0 hx
    exact hrad x hx'
  · -- positive weight
    -- zero modes: their contribution vanishes
    have hzeroMode : ∀ i, sesqForm B R (S.mode i 0 v) (S.mode i 0 v) = 0 := by
      intro i
      rw [S.sesq_adj', neg_zero]
      apply hsrad
      have h1 := S.nonneg_mem i (le_refl 0) hv
      have h2 := S.nonneg_mem (S.adj i) (le_refl 0) h1
      simpa using h2
    have hvv : sesqForm B R v v = 0 := hsrad v hv
    -- positive modes land in a lower layer
    have hlayer : ∀ (i : ι) (m : ℕ), 0 < m →
        ∃ hu : S.mode i (m : ℤ) v ∈ W.grading (E - m),
          (⟨S.mode i (m : ℤ) v, hu⟩ : W.grading (E - m)) ∈
            F.layer (E - m) (LiRadical.gradedForm B (E - m)) r := by
      intro i m hm
      have hpiece : S.mode i (m : ℤ) v ∈ F.piece r (E - m) :=
        S.nonneg_mem i (by positivity) hv
      refine ⟨F.le_grading r _ hpiece, hpiece, ?_⟩
      cases r with
      | zero =>
          intro w hw
          rw [GradedFlag.pieceLT_zero] at hw
          rw [(Submodule.mem_bot ℂ).mp hw]
          exact LinearMap.BilinForm.isOrtho_zero_left _
      | succ q =>
          intro w hw
          rw [GradedFlag.pieceLT_succ, GradedFlag.mem_pieceIn] at hw
          change B.form (w : 𝒱) (S.mode i (m : ℤ) v) = 0
          refine form_eq_zero_of_sesq (S := (F.piece q (E - m) : Set 𝒱))
            (fun x hx => S.rho_piece hx) (fun x hx => F.le_grading q _ hx)
            (S.parity_ne_zero _) ?_ (w : 𝒱) hw
          intro x hx
          rw [S.sesq_adj']
          apply hsrad
          have h := S.neg_mem (S.adj i) (show (0 : ℤ) < m by exact_mod_cast hm) hx
          simpa using h
    -- each signed norm is a nonnegative real, zero only for the zero vector
    have hprops : ∀ (i : ι) (m : ℕ), 0 < m →
        ((-1 : ℂ) ^ r * sesqForm B R (S.mode i (m : ℤ) v) (S.mode i (m : ℤ) v)).im = 0 ∧
        0 ≤ ((-1 : ℂ) ^ r * sesqForm B R (S.mode i (m : ℤ) v) (S.mode i (m : ℤ) v)).re ∧
        (((-1 : ℂ) ^ r * sesqForm B R (S.mode i (m : ℤ) v) (S.mode i (m : ℤ) v)).re = 0 →
          S.mode i (m : ℤ) v = 0) := by
      intro i m hm
      obtain ⟨hu, hmem⟩ := hlayer i m hm
      haveI := W.finrank (E - m)
      obtain ⟨h1, h2, h3⟩ := signed_norm_props (hlower m hm) _ hmem
      exact ⟨h1, h2, fun h => by
        have := h3 h
        exact congrArg Subtype.val this⟩
    -- the Sugawara identity forces every positive-mode signed norm to vanish
    have hsug := S.sugawara hvE
    rw [hvv, mul_zero] at hsug
    simp only [hzeroMode, mul_zero, Finset.sum_const_zero, zero_add] at hsug
    have hsum : (∑ i, ∑ m ∈ Finset.Icc 1 E.toNat, ((S.wt i : ℂ) *
        ((-1 : ℂ) ^ r * sesqForm B R (S.mode i (m : ℤ) v) (S.mode i (m : ℤ) v)))) = 0 := by
      have : (∑ i, ∑ m ∈ Finset.Icc 1 E.toNat, ((S.wt i : ℂ) *
          ((-1 : ℂ) ^ r * sesqForm B R (S.mode i (m : ℤ) v) (S.mode i (m : ℤ) v)))) =
          (-1 : ℂ) ^ r * ∑ i, ∑ m ∈ Finset.Icc 1 E.toNat,
            (S.wt i : ℂ) * sesqForm B R (S.mode i (m : ℤ) v) (S.mode i (m : ℤ) v) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        ring
      rw [this, ← hsug, mul_zero]
    have hre := congrArg Complex.re hsum
    rw [Complex.zero_re, Complex.re_sum] at hre
    simp_rw [Complex.re_sum] at hre
    have hterm_nonneg : ∀ i, ∀ m ∈ Finset.Icc 1 E.toNat, 0 ≤ ((S.wt i : ℂ) *
        ((-1 : ℂ) ^ r * sesqForm B R (S.mode i (m : ℤ) v) (S.mode i (m : ℤ) v))).re := by
      intro i m hm
      have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
      obtain ⟨_, h2, _⟩ := hprops i m hm0
      rw [Complex.re_ofReal_mul]
      exact mul_nonneg (S.wt_pos i).le h2
    have houter := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg (hterm_nonneg i))).mp hre
    have hkillRange : ∀ i, ∀ m ∈ Finset.Icc 1 E.toNat, S.mode i (m : ℤ) v = 0 := by
      intro i m hm
      have hinner := (Finset.sum_eq_zero_iff_of_nonneg (hterm_nonneg i)).mp
        (houter i (Finset.mem_univ i)) m hm
      rw [Complex.re_ofReal_mul] at hinner
      have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
      obtain ⟨_, _, h3⟩ := hprops i m hm0
      exact h3 ((mul_eq_zero.mp hinner).resolve_left (S.wt_pos i).ne')
    have hkill : ∀ (i : ι) (m : ℕ), 0 < m → S.mode i (m : ℤ) v = 0 := by
      intro i m hm
      by_cases hmE : (m : ℤ) ≤ E
      · exact hkillRange i m (Finset.mem_Icc.mpr ⟨hm, by omega⟩)
      · have hg := S.mode_grading i (m : ℤ) hvE
        rw [W.positivity (E - m) (by omega)] at hg
        exact (Submodule.mem_bot ℂ).mp hg
    -- hence `v` is orthogonal to the whole weight space
    apply hfull v hvE
    refine form_eq_zero_of_sesq (S := (W.grading E : Set 𝒱)) (fun x hx => S.rho_grading hx)
      (fun x hx => hx) (S.parity_ne_zero E) ?_
    exact S.sesq_eq_zero_of_pos_kill hposE hkill

/-- **The prefix no-wall lemma.**  If every lower weight `E - m` (`m ≥ 1`) has the
graded-unitary layer signs and the full weight-`E` form separates in its second slot, then the
form is nondegenerate on every step of the flag at weight `E` (ABLR clause (iv) at weight `E`).

⚠ Positivity of the new layers at weight `E` is *not* concluded. -/
theorem layerNondegenerate_of_lower (E : ℤ)
    (hfull : ∀ v ∈ W.grading E, (∀ x ∈ W.grading E, B.form x v = 0) → v = 0)
    (hlower : ∀ m : ℕ, 0 < m →
      LayerPositive F (E - m) (LiRadical.gradedForm B (E - m)) (gradedSesq B R (E - m))) :
    LayerNondegenerate F E (LiRadical.gradedForm B E) := by
  intro r
  haveI := W.finrank E
  apply nondegenerate_of_separatingRight
  intro y hy
  have hy0 : ((y : W.grading E) : 𝒱) = 0 := by
    refine S.radical_eq_zero E r hfull hlower y.2 ?_
    intro w hw
    have := hy ⟨⟨w, F.le_grading r E hw⟩, hw⟩
    simpa using this
  exact Subtype.ext (Subtype.ext hy0)

end CurrentSystem

end BelowCriticalNoWall

end VOA
