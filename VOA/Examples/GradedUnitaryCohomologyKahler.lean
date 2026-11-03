/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.LeeYangCosetTransferHodge
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The Kähler package of a weakly graded-unitary BRST complex, at one conformal weight

This file formalizes, as finite-dimensional linear algebra at one fixed conformal weight, the
positive Hodge theory behind Beem–Garner, *Graded unitarity and relative semi-infinite
cohomology* (arXiv 2509.10364), Lemma 3.16, Proposition 3.24, Theorem 4.1 and Remark 4.4.

## The abstract datum (`KahlerComplex`)

At a fixed conformal weight `h` the relative complex `C(ĝ_{-2h^∨}, g, V_matter)_h` is a
finite-dimensional complex vector space `K`. We record:

* `P` — the *modified* Hermitian form `⟨x|y⟩ = ((σ∘ρ) x, y)` of Beem–Garner Corollary 2.24.
  Weak graded unitarity of the complex (their Theorem 3.20) is the hypothesis `pos`:
  `P` is positive definite on all of `K`. Hermitian symmetry is *not* assumed; it is proved
  from positivity by polarization (`herm`).
* `deg : ℤ × ℤ → Submodule ℂ K` — the bigrading by `(2R, gh)`: twice the `ℜ`-degree (so
  half-integral `R` is allowed) and the ghost number (the `U(1)` weight `Π` of Beem–Garner
  Eq. (3.7), for which `𝐐⁻` has weight `+1` and `𝐐⁺` weight `-1`). The pieces span (`span`)
  and are `P`-orthogonal (`orth`), as in Beem–Garner Remarks 2.30–2.31.
* `Qm, Sm, Qp, Sp` — the four `ℜ`-homogeneous pieces of Lemma 3.16:
  `𝐐⁻ = Q⁻ + S⁻`, `𝐐⁺ = Q⁺ + S⁺`, where `Q^±` raise `R` by `1/2` and `S^±` lower it by `1/2`.
  **This is exactly where goodness of the Hamiltonian action (Definition 3.12) enters:** the
  differentials have *no* `ℜ`-degree-preserving component. Ghost numbers: `Qm, Sm` raise the
  ghost number by one, `Qp, Sp` lower it by one.
* the adjoint relations of Lemma 3.16, `(Q^α)† = ε_{αβ} S^β` and `(S^α)† = -ε_{αβ} Q^β`, in the
  two independent forms `(Q⁻)† = c S⁺` and `(S⁻)† = -c Q⁺` with a sign `c = ε_{-+}`, `c² = 1`.
  The other two (`(Q⁺)† = -c S⁻`, `(S⁺)† = c Q⁻`) are *derived* (`adj_Qp`, `adj_Sp`).
* `sq_zero : (𝐐⁻)² = 0` and `anticomm : 𝐐⁻ 𝐐⁺ + 𝐐⁺ 𝐐⁻ = 0`. (`(𝐐⁺)² = 0` is not needed.)

## Results

* `fine_QmQp`, `fine_SmSp`, `Qm_sq`: the finer relations of Lemma 3.16, *derived* from
  the bold ones by degree splitting.
* `mem_harm_iff` (**Beem–Garner Remark 4.4, in the strong form**): a vector is harmonic for
  `𝐐⁻` iff it is killed by all four pieces `Q⁻, S⁻, Q⁺, S⁺`. The proof is the identity
  `[𝐐⁻, 𝐐̄₋] = [𝐐⁺, 𝐐̄₊]` (Eq. (3.6)), used in the form
  `‖𝐐⁺x‖² + ‖(Q⁻-S⁻)x‖² = c ⟨x | (𝐐̄₋𝐐⁻ + 𝐐⁻𝐐̄₋)-type expression⟩ = 0`.
* `harm_split` (the harmonic space is bigraded): the `deg`-components of a harmonic vector are
  harmonic.
* `harmToLead_injective` (**harmonic vectors inject into the leading cohomology**
  `H(Q⁻)` at the same bidegree; with bidegree `(2R, gh)` this is the shifted grading
  `t = R - gh/2` of the addendum), and `finrank_harm_deg_le_lead`.

Everything is proved outright from the listed hypotheses. Nothing here constructs a BRST
complex, a vertex algebra, or the positive Hodge input for any concrete complex.
-/

namespace VOA.GradedUnitaryCohomology

open VOA.LeeYangCosetTransfer
open Module (finrank)

universe u

/-- Closes bidegree bookkeeping goals such as `a + (1, -1) + (1, 1) = a + (2, 0)`. -/
macro "bideg" : tactic =>
  `(tactic| (ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega))

/-- The bidegree shifts of the four pieces, in the coordinates `(2R, gh)`. -/
abbrev shQm : ℤ × ℤ := (1, 1)
/-- Shift of `S⁻`. -/
abbrev shSm : ℤ × ℤ := (-1, 1)
/-- Shift of `Q⁺`. -/
abbrev shQp : ℤ × ℤ := (1, -1)
/-- Shift of `S⁺`. -/
abbrev shSp : ℤ × ℤ := (-1, -1)

/-- **A weakly graded-unitary BRST complex with a good action, at one conformal weight.**
See the module docstring for the dictionary with Beem–Garner. -/
structure KahlerComplex (K : Type u) [AddCommGroup K] [Module ℂ K] where
  /-- The modified Hermitian form `⟨x|y⟩ = ((σ∘ρ)x, y)` (conjugate-linear in the first slot). -/
  P : SesqForm K
  /-- Weak graded unitarity of the complex: `P` is positive definite. -/
  pos : IsPosOn P ⊤
  /-- The bigrading by `(2R, ghost number)`. -/
  deg : ℤ × ℤ → Submodule ℂ K
  /-- The bigraded pieces span. -/
  span : iSup deg = ⊤
  /-- Distinct bigraded pieces are `P`-orthogonal. -/
  orth : ∀ a b, a ≠ b → ∀ x ∈ deg a, ∀ y ∈ deg b, P x y = 0
  /-- `Q⁻`: raises `2R` by one and the ghost number by one. -/
  Qm : K →ₗ[ℂ] K
  /-- `S⁻`: lowers `2R` by one, raises the ghost number by one. -/
  Sm : K →ₗ[ℂ] K
  /-- `Q⁺`: raises `2R` by one, lowers the ghost number by one. -/
  Qp : K →ₗ[ℂ] K
  /-- `S⁺`: lowers `2R` by one and the ghost number by one. -/
  Sp : K →ₗ[ℂ] K
  Qm_deg : ∀ a, ∀ x ∈ deg a, Qm x ∈ deg (a + shQm)
  Sm_deg : ∀ a, ∀ x ∈ deg a, Sm x ∈ deg (a + shSm)
  Qp_deg : ∀ a, ∀ x ∈ deg a, Qp x ∈ deg (a + shQp)
  Sp_deg : ∀ a, ∀ x ∈ deg a, Sp x ∈ deg (a + shSp)
  /-- The sign `ε_{-+}` of Beem–Garner Lemma 3.16. -/
  c : ℝ
  c_sq : c * c = 1
  /-- `(Q⁻)† = c S⁺`. -/
  adj_Qm : ∀ x y, P (Qm x) y = (c : ℂ) * P x (Sp y)
  /-- `(S⁻)† = -c Q⁺`. -/
  adj_Sm : ∀ x y, P (Sm x) y = -(c : ℂ) * P x (Qp y)
  /-- `(𝐐⁻)² = 0`. -/
  sq_zero : (Qm + Sm).comp (Qm + Sm) = 0
  /-- `𝐐⁻ 𝐐⁺ + 𝐐⁺ 𝐐⁻ = 0`. -/
  anticomm : (Qm + Sm).comp (Qp + Sp) + (Qp + Sp).comp (Qm + Sm) = 0

namespace KahlerComplex

variable {K : Type u} [AddCommGroup K] [Module ℂ K] (C : KahlerComplex K)

/-! ### Positivity and Hermitian symmetry -/

theorem eq_zero_of_self (x : K) (hx : C.P x x = 0) : x = 0 :=
  eq_zero_of_sesq_self_eq_zero C.P C.pos hx

theorem self_re_im (x : K) : 0 ≤ (C.P x x).re ∧ (C.P x x).im = 0 := by
  by_cases hx : x = 0
  · subst hx; simp [C.P.zero_left]
  · obtain ⟨r, hr, hrx⟩ := C.pos x Submodule.mem_top hx
    rw [hrx]; simp [le_of_lt hr]

/-- **Hermitian symmetry from positivity** (polarization): a sesquilinear form with real
diagonal is Hermitian. This is Beem–Garner Corollary 2.24, recovered from positivity alone. -/
theorem herm (x y : K) : (starRingEnd ℂ) (C.P y x) = C.P x y := by
  have h1 := (C.self_re_im (x + y)).2
  have h2 := (C.self_re_im (x + Complex.I • y)).2
  have hx := (C.self_re_im x).2
  have hy := (C.self_re_im y).2
  simp only [C.P.add_left, C.P.add_right, C.P.smul_left, C.P.smul_right, Complex.add_im,
    Complex.mul_im, Complex.conj_I, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.mul_re] at h1 h2
  apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im] <;> nlinarith

theorem eq_zero_of_add_self (x y : K) (h : C.P x x + C.P y y = 0) : x = 0 ∧ y = 0 := by
  have hx := C.self_re_im x
  have hy := C.self_re_im y
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.zero_re] at hre
  have hx0 : C.P x x = 0 := Complex.ext (by simp; linarith) (by simp [hx.2])
  have hy0 : C.P y y = 0 := Complex.ext (by simp; linarith) (by simp [hy.2])
  exact ⟨C.eq_zero_of_self x hx0, C.eq_zero_of_self y hy0⟩

theorem P_neg_right (x y : K) : C.P x (-y) = -C.P x y := by
  rw [← neg_one_smul ℂ y, C.P.smul_right]; ring

theorem P_sub_right (x y z : K) : C.P x (y - z) = C.P x y - C.P x z := by
  rw [sub_eq_add_neg, C.P.add_right, C.P_neg_right]; ring

theorem P_sub_left (x y z : K) : C.P (x - y) z = C.P x z - C.P y z := by
  rw [sub_eq_add_neg, C.P.add_left, ← neg_one_smul ℂ y, C.P.smul_left]; simp; ring

/-! ### Orthogonal splitting along sets of bidegrees -/

/-- The span of the bigraded pieces with bidegree in `A`. -/
def degOn (A : Set (ℤ × ℤ)) : Submodule ℂ K := ⨆ a : A, C.deg (a : ℤ × ℤ)

theorem deg_le_degOn {A : Set (ℤ × ℤ)} {a : ℤ × ℤ} (ha : a ∈ A) : C.deg a ≤ C.degOn A :=
  le_iSup (fun b : A => C.deg (b : ℤ × ℤ)) ⟨a, ha⟩

theorem degOn_mono {A B : Set (ℤ × ℤ)} (h : A ⊆ B) : C.degOn A ≤ C.degOn B :=
  iSup_le fun a => C.deg_le_degOn (h a.2)

/-- Spans of disjoint sets of bidegrees are `P`-orthogonal. -/
theorem orth_degOn {A B : Set (ℤ × ℤ)} (hAB : Disjoint A B) {x y : K}
    (hx : x ∈ C.degOn A) (hy : y ∈ C.degOn B) : C.P x y = 0 := by
  refine Submodule.iSup_induction (fun a : A => C.deg (a : ℤ × ℤ))
    (motive := fun x => C.P x y = 0) hx ?_ (C.P.zero_left y)
    (fun x x' h h' => by beta_reduce at h h' ⊢; rw [C.P.add_left, h, h', add_zero])
  intro a x hx
  refine Submodule.iSup_induction (fun b : B => C.deg (b : ℤ × ℤ))
    (motive := fun y => C.P x y = 0) hy ?_ (C.P.zero_right x)
    (fun y y' h h' => by beta_reduce at h h' ⊢; rw [C.P.add_right, h, h', add_zero])
  intro b y hy
  refine C.orth _ _ ?_ x hx y hy
  intro hab
  exact Set.disjoint_left.mp hAB a.2 (hab ▸ b.2)

/-- Every vector splits along a set of bidegrees and its complement. -/
theorem exists_split (A : Set (ℤ × ℤ)) (x : K) :
    ∃ y ∈ C.degOn A, ∃ z ∈ C.degOn Aᶜ, x = y + z := by
  have hx : x ∈ iSup C.deg := C.span ▸ Submodule.mem_top
  refine Submodule.iSup_induction C.deg
    (motive := fun x => ∃ y ∈ C.degOn A, ∃ z ∈ C.degOn Aᶜ, x = y + z) hx ?_
    ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, (add_zero 0).symm⟩ ?_
  · intro a x hx
    by_cases ha : a ∈ A
    · exact ⟨x, C.deg_le_degOn ha hx, 0, Submodule.zero_mem _, (add_zero x).symm⟩
    · exact ⟨0, Submodule.zero_mem _, x, C.deg_le_degOn (Set.mem_compl ha) hx,
        (zero_add x).symm⟩
  · rintro x x' ⟨y, hy, z, hz, rfl⟩ ⟨y', hy', z', hz', rfl⟩
    exact ⟨y + y', add_mem hy hy', z + z', add_mem hz hz', by abel⟩

/-- A linear map is homogeneous of bidegree `s`. -/
def IsHomog (T : K →ₗ[ℂ] K) (s : ℤ × ℤ) : Prop := ∀ a, ∀ x ∈ C.deg a, T x ∈ C.deg (a + s)

theorem homog_degOn {T : K →ₗ[ℂ] K} {s : ℤ × ℤ} (hT : C.IsHomog T s) (A : Set (ℤ × ℤ))
    {x : K} (hx : x ∈ C.degOn A) : T x ∈ C.degOn {b | b - s ∈ A} := by
  refine Submodule.iSup_induction (fun a : A => C.deg (a : ℤ × ℤ))
    (motive := fun x => T x ∈ C.degOn {b | b - s ∈ A}) hx ?_
    (by beta_reduce; rw [map_zero]; exact Submodule.zero_mem _)
    (fun x x' h h' => by beta_reduce at h h' ⊢; rw [map_add]; exact add_mem h h')
  intro a x hx
  exact C.deg_le_degOn (a := (a : ℤ × ℤ) + s) (by simp [a.2]) (hT a x hx)

/-- **Degree splitting of a kernel.** If a homogeneous map kills `y + z`, with `y` and `z`
supported on complementary sets of bidegrees, it kills `y`. -/
theorem homog_split_ker {T : K →ₗ[ℂ] K} {s : ℤ × ℤ} (hT : C.IsHomog T s) (A : Set (ℤ × ℤ))
    {y z : K} (hy : y ∈ C.degOn A) (hz : z ∈ C.degOn Aᶜ) (h0 : T (y + z) = 0) : T y = 0 := by
  have hTy := C.homog_degOn hT A hy
  have hTz := C.homog_degOn hT Aᶜ hz
  have hdisj : Disjoint {b : ℤ × ℤ | b - s ∈ A} {b | b - s ∈ Aᶜ} :=
    Set.disjoint_left.mpr fun b hb hb' => hb' hb
  have horth := C.orth_degOn hdisj hTy hTz
  have hyz : T y = -T z := eq_neg_of_add_eq_zero_left (by rw [← map_add]; exact h0)
  apply C.eq_zero_of_self
  calc C.P (T y) (T y) = C.P (T y) (-T z) := by rw [← hyz]
    _ = -C.P (T y) (T z) := by
        rw [← neg_one_smul ℂ (T z), C.P.smul_right]; ring
    _ = 0 := by rw [horth, neg_zero]

theorem homog_Qm : C.IsHomog C.Qm shQm := C.Qm_deg
theorem homog_Sm : C.IsHomog C.Sm shSm := C.Sm_deg
theorem homog_Qp : C.IsHomog C.Qp shQp := C.Qp_deg
theorem homog_Sp : C.IsHomog C.Sp shSp := C.Sp_deg

/-! ### Derived adjoint relations -/

theorem c_ne_zero : (C.c : ℂ) ≠ 0 := by
  intro h
  have : C.c = 0 := by exact_mod_cast h
  have := C.c_sq
  simp_all

theorem c_mul_c : (C.c : ℂ) * C.c = 1 := by exact_mod_cast C.c_sq

theorem conj_c : (starRingEnd ℂ) (C.c : ℂ) = C.c := Complex.conj_ofReal _

/-- `(Q⁺)† = -c S⁻`, derived from `(S⁻)† = -c Q⁺`, Hermitian symmetry and `c² = 1`. -/
theorem adj_Qp (x y : K) : C.P (C.Qp x) y = -(C.c : ℂ) * C.P x (C.Sm y) := by
  have h := congrArg (starRingEnd ℂ) (C.adj_Sm y x)
  rw [C.herm, map_mul, map_neg, C.conj_c, C.herm] at h
  rw [h, ← mul_assoc, neg_mul, mul_neg, neg_neg, C.c_mul_c, one_mul]

/-- `(S⁺)† = c Q⁻`. -/
theorem adj_Sp (x y : K) : C.P (C.Sp x) y = (C.c : ℂ) * C.P x (C.Qm y) := by
  have h := congrArg (starRingEnd ℂ) (C.adj_Qm y x)
  rw [C.herm, map_mul, C.conj_c, C.herm] at h
  rw [h, ← mul_assoc, C.c_mul_c, one_mul]

/-! ### The finer relations of Lemma 3.16, by degree splitting -/

theorem mem_deg_of_eq {a b : ℤ × ℤ} (h : a = b) {x : K} (hx : x ∈ C.deg a) : x ∈ C.deg b :=
  h ▸ hx

/-- Three vectors in pairwise distinct bidegrees summing to zero: the first vanishes. -/
theorem eq_zero_of_three {a b d : ℤ × ℤ} (hab : a ≠ b) (had : a ≠ d) {u v w : K}
    (hu : u ∈ C.deg a) (hv : v ∈ C.deg b) (hw : w ∈ C.deg d) (h : u + v + w = 0) : u = 0 := by
  apply C.eq_zero_of_self
  have h' : u = -(v + w) := eq_neg_of_add_eq_zero_left (by rw [← add_assoc]; exact h)
  calc C.P u u = C.P u (-(v + w)) := by rw [← h']
    _ = -(C.P u v + C.P u w) := by
        rw [← neg_one_smul ℂ (v + w), C.P.smul_right, C.P.add_right]; ring
    _ = 0 := by rw [C.orth a b hab u hu v hv, C.orth a d had u hu w hw]; simp

theorem fine_on_deg (a : ℤ × ℤ) (x : K) (hx : x ∈ C.deg a) :
    C.Qm (C.Qp x) + C.Qp (C.Qm x) = 0 ∧ C.Sm (C.Sp x) + C.Sp (C.Sm x) = 0 := by
  have h := LinearMap.congr_fun C.anticomm x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, LinearMap.zero_apply] at h
  set u := C.Qm (C.Qp x) + C.Qp (C.Qm x)
  set v := C.Qm (C.Sp x) + C.Sm (C.Qp x) + C.Qp (C.Sm x) + C.Sp (C.Qm x)
  set w := C.Sm (C.Sp x) + C.Sp (C.Sm x)
  have hsum : u + v + w = 0 := by rw [← h]; simp only [u, v, w]; abel
  have hu : u ∈ C.deg (a + (2, 0)) := by
    refine add_mem (C.mem_deg_of_eq ?_ (C.Qm_deg _ _ (C.Qp_deg a x hx)))
      (C.mem_deg_of_eq ?_ (C.Qp_deg _ _ (C.Qm_deg a x hx))) <;>
      bideg
  have hv : v ∈ C.deg a := by
    refine add_mem (add_mem (add_mem
      (C.mem_deg_of_eq ?_ (C.Qm_deg _ _ (C.Sp_deg a x hx)))
      (C.mem_deg_of_eq ?_ (C.Sm_deg _ _ (C.Qp_deg a x hx))))
      (C.mem_deg_of_eq ?_ (C.Qp_deg _ _ (C.Sm_deg a x hx))))
      (C.mem_deg_of_eq ?_ (C.Sp_deg _ _ (C.Qm_deg a x hx))) <;>
      ext <;> simp
  have hw : w ∈ C.deg (a + (-2, 0)) := by
    refine add_mem (C.mem_deg_of_eq ?_ (C.Sm_deg _ _ (C.Sp_deg a x hx)))
      (C.mem_deg_of_eq ?_ (C.Sp_deg _ _ (C.Sm_deg a x hx))) <;>
      bideg
  have hne1 : a + (2, 0) ≠ a := by intro h; have := congrArg Prod.fst h; simp at this
  have hne2 : a + (2, 0) ≠ a + (-2, 0) := by intro h; have := congrArg Prod.fst h; simp at this
  have hne3 : a + (-2, 0) ≠ a := by intro h; have := congrArg Prod.fst h; simp at this
  have hne4 : a + (-2, 0) ≠ a + (2, 0) := fun h => hne2 h.symm
  refine ⟨C.eq_zero_of_three hne1 hne2 hu hv hw hsum, ?_⟩
  exact C.eq_zero_of_three hne3 hne4 hw hv hu (by rw [← hsum]; abel)

/-- A linear map vanishing on every bigraded piece vanishes. -/
theorem eq_zero_of_deg (T : K →ₗ[ℂ] K) (hT : ∀ a, ∀ x ∈ C.deg a, T x = 0) : T = 0 := by
  have : (⊤ : Submodule ℂ K) ≤ LinearMap.ker T := by
    rw [← C.span]; exact iSup_le fun a x hx => hT a x hx
  ext x; exact this Submodule.mem_top

/-- `[Q⁻, Q⁺] = 0` (Beem–Garner Lemma 3.16), derived from `[𝐐⁻, 𝐐⁺] = 0`. -/
theorem fine_QmQp (x : K) : C.Qm (C.Qp x) + C.Qp (C.Qm x) = 0 := by
  have := C.eq_zero_of_deg (C.Qm.comp C.Qp + C.Qp.comp C.Qm)
    (fun a x hx => (C.fine_on_deg a x hx).1)
  exact LinearMap.congr_fun this x

/-- `[S⁻, S⁺] = 0` (Beem–Garner Lemma 3.16), derived from `[𝐐⁻, 𝐐⁺] = 0`. -/
theorem fine_SmSp (x : K) : C.Sm (C.Sp x) + C.Sp (C.Sm x) = 0 := by
  have := C.eq_zero_of_deg (C.Sm.comp C.Sp + C.Sp.comp C.Sm)
    (fun a x hx => (C.fine_on_deg a x hx).2)
  exact LinearMap.congr_fun this x

/-- `(Q⁻)² = 0`, derived from `(𝐐⁻)² = 0`; so `H(Q⁻)` is an honest cohomology. -/
theorem Qm_sq (x : K) : C.Qm (C.Qm x) = 0 := by
  have := C.eq_zero_of_deg (C.Qm.comp C.Qm) fun a x hx => by
    change C.Qm (C.Qm x) = 0
    have h := LinearMap.congr_fun C.sq_zero x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, LinearMap.zero_apply] at h
    have hu : C.Qm (C.Qm x) ∈ C.deg (a + (2, 2)) :=
      C.mem_deg_of_eq (by bideg) (C.Qm_deg _ _ (C.Qm_deg a x hx))
    have hv : C.Qm (C.Sm x) + C.Sm (C.Qm x) ∈ C.deg (a + (0, 2)) :=
      add_mem (C.mem_deg_of_eq (by bideg) (C.Qm_deg _ _ (C.Sm_deg a x hx)))
        (C.mem_deg_of_eq (by bideg) (C.Sm_deg _ _ (C.Qm_deg a x hx)))
    have hw : C.Sm (C.Sm x) ∈ C.deg (a + (-2, 2)) :=
      C.mem_deg_of_eq (by bideg) (C.Sm_deg _ _ (C.Sm_deg a x hx))
    refine C.eq_zero_of_three ?_ ?_ hu hv hw (by rw [← h]; abel) <;>
      intro h <;> have := congrArg Prod.fst h <;> simp at this
  exact LinearMap.congr_fun this x

/-! ### Harmonic vectors -/

/-- The bold differential `𝐐⁻ = Q⁻ + S⁻`. -/
def D : K →ₗ[ℂ] K := C.Qm + C.Sm

/-- Its adjoint `𝐐̄₋ = c (S⁺ - Q⁺)`. -/
def Dadj : K →ₗ[ℂ] K := (C.c : ℂ) • (C.Sp - C.Qp)

theorem adj_D (x y : K) : C.P (C.D x) y = C.P x (C.Dadj y) := by
  simp only [D, Dadj, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    C.P.add_left, C.adj_Qm, C.adj_Sm, C.P.smul_right]
  rw [sub_eq_add_neg, C.P.add_right, ← neg_one_smul ℂ (C.Qp y), C.P.smul_right]
  ring

theorem D_sq : C.D.comp C.D = 0 := C.sq_zero

/-- The `𝐐⁻`-harmonic space `ker 𝐐⁻ ∩ ker 𝐐̄₋`. -/
def harm : Submodule ℂ K := harmonicSpace C.D C.Dadj

/-- **Beem–Garner Remark 4.4, strong form.** A vector is `𝐐⁻`-harmonic iff it is annihilated
by all four `ℜ`-homogeneous pieces `Q⁻, S⁻, Q⁺, S⁺`. In particular harmonic vectors are also
`𝐐⁺`-harmonic, and are `Q⁻`-closed and `(Q⁻)†`-closed. -/
theorem mem_harm_iff (x : K) :
    x ∈ C.harm ↔ C.Qm x = 0 ∧ C.Sm x = 0 ∧ C.Qp x = 0 ∧ C.Sp x = 0 := by
  constructor
  · rintro ⟨hD, hDa⟩
    have hD : C.Qm x + C.Sm x = 0 := hD
    have hG : C.Sp x - C.Qp x = 0 := by
      have hDa : (C.c : ℂ) • (C.Sp x - C.Qp x) = 0 := hDa
      exact (smul_eq_zero.mp hDa).resolve_left C.c_ne_zero
    have hQm : C.Qm x = -C.Sm x := eq_neg_of_add_eq_zero_left hD
    have hSp : C.Sp x = C.Qp x := sub_eq_zero.mp hG
    -- `E = Q⁺ + S⁺` and `F = Q⁻ - S⁻`.
    obtain ⟨E, hE⟩ : ∃ E, E = C.Qp x + C.Sp x := ⟨_, rfl⟩
    obtain ⟨F, hF⟩ : ∃ F, F = C.Qm x - C.Sm x := ⟨_, rfl⟩
    have hPE : C.P E E = (C.c : ℂ) * C.P x (C.Qm E - C.Sm E) := by
      calc C.P E E = C.P (C.Qp x + C.Sp x) E := by rw [← hE]
        _ = C.P (C.Qp x) E + C.P (C.Sp x) E := C.P.add_left _ _ _
        _ = -(C.c : ℂ) * C.P x (C.Sm E) + (C.c : ℂ) * C.P x (C.Qm E) := by
            rw [C.adj_Qp, C.adj_Sp]
        _ = (C.c : ℂ) * C.P x (C.Qm E - C.Sm E) := by rw [C.P_sub_right]; ring
    have hPF : C.P F F = (C.c : ℂ) * C.P x (C.Qp F + C.Sp F) := by
      calc C.P F F = C.P (C.Qm x - C.Sm x) F := by rw [← hF]
        _ = C.P (C.Qm x) F - C.P (C.Sm x) F := C.P_sub_left _ _ _
        _ = (C.c : ℂ) * C.P x (C.Sp F) - -(C.c : ℂ) * C.P x (C.Qp F) := by
            rw [C.adj_Qm, C.adj_Sm]
        _ = (C.c : ℂ) * C.P x (C.Qp F + C.Sp F) := by rw [C.P.add_right]; ring
    have hfine1 := C.fine_QmQp x
    have hfine2 := C.fine_SmSp x
    have hkey : (C.Qm E - C.Sm E) + (C.Qp F + C.Sp F) = 0 := by
      simp only [hE, hF, map_add, map_sub, hQm, hSp, map_neg] at hfine1 hfine2 ⊢
      linear_combination (norm := module) (2 : ℂ) • hfine1 - (2 : ℂ) • hfine2
    have hsum : C.P E E + C.P F F = 0 := by
      rw [hPE, hPF, ← mul_add, ← C.P.add_right, hkey, C.P.zero_right, mul_zero]
    obtain ⟨hE0, hF0⟩ := C.eq_zero_of_add_self E F hsum
    rw [hE] at hE0
    rw [hF] at hF0
    have h2 : (2 : ℂ) • C.Qm x = 0 := by
      have : (2 : ℂ) • C.Qm x = (C.Qm x + C.Sm x) + (C.Qm x - C.Sm x) := by module
      rw [this, hD, hF0, add_zero]
    have hQm0 : C.Qm x = 0 := (smul_eq_zero.mp h2).resolve_left two_ne_zero
    have hSm0 : C.Sm x = 0 := by rw [hQm0, zero_add] at hD; exact hD
    have h2' : (2 : ℂ) • C.Qp x = 0 := by
      rw [hSp] at hE0; rw [two_smul]; exact hE0
    have hQp0 : C.Qp x = 0 := (smul_eq_zero.mp h2').resolve_left two_ne_zero
    exact ⟨hQm0, hSm0, hQp0, by rw [hSp, hQp0]⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_⟩
    · change C.Qm x + C.Sm x = 0; rw [h1, h2, add_zero]
    · change (C.c : ℂ) • (C.Sp x - C.Qp x) = 0; rw [h3, h4, sub_zero, smul_zero]

/-- **The harmonic space is bigraded.** If a harmonic vector is split along a set of bidegrees
and its complement, both parts are harmonic. -/
theorem harm_split (A : Set (ℤ × ℤ)) {y z : K} (hy : y ∈ C.degOn A) (hz : z ∈ C.degOn Aᶜ)
    (h : y + z ∈ C.harm) : y ∈ C.harm ∧ z ∈ C.harm := by
  obtain ⟨h1, h2, h3, h4⟩ := (C.mem_harm_iff _).mp h
  have hy' : y ∈ C.harm := (C.mem_harm_iff y).mpr
    ⟨C.homog_split_ker C.homog_Qm A hy hz h1, C.homog_split_ker C.homog_Sm A hy hz h2,
      C.homog_split_ker C.homog_Qp A hy hz h3, C.homog_split_ker C.homog_Sp A hy hz h4⟩
  refine ⟨hy', ?_⟩
  have : z = (y + z) - y := by abel
  rw [this]; exact sub_mem h hy'

/-- Harmonic vectors are `P`-orthogonal to `𝐐⁻`-exact vectors. -/
theorem P_harm_D (w v : K) (hw : w ∈ C.harm) : C.P w (C.D v) = 0 := by
  rw [← C.herm, C.adj_D, hw.2, C.P.zero_right, map_zero]

/-! ### Injection of harmonic vectors into the leading cohomology `H(Q⁻)` -/

/-- `Q⁻`-cycles of bidegree `a = (2R, gh)`. -/
def leadCycles (a : ℤ × ℤ) : Submodule ℂ K := LinearMap.ker C.Qm ⊓ C.deg a

/-- `Q⁻`-boundaries of bidegree `a`: images of bidegree `a - (1,1)`, viewed in the cycles. -/
def leadBoundaries (a : ℤ × ℤ) : Submodule ℂ (C.leadCycles a) :=
  (Submodule.map C.Qm (C.deg (a - shQm))).comap (C.leadCycles a).subtype

/-- Every `Q⁻`-boundary of bidegree `a` is a cycle of bidegree `a` (uses `Qm_sq`). -/
theorem map_le_leadCycles (a : ℤ × ℤ) :
    Submodule.map C.Qm (C.deg (a - shQm)) ≤ C.leadCycles a := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨C.Qm_sq y, C.mem_deg_of_eq (by simp) (C.Qm_deg _ y hy)⟩

/-- The leading cohomology `H(Q⁻)` in bidegree `a = (2R, gh)`. In the coordinates of the
addendum, `gh = 0` and `a.1 = 2r` give `H⁰(Q⁻)(r)` at shifted degree `t = R - gh/2 = r`. -/
abbrev leadCohom (a : ℤ × ℤ) := C.leadCycles a ⧸ C.leadBoundaries a

/-- Harmonic vectors of bidegree `a`. -/
def harmDeg (a : ℤ × ℤ) : Submodule ℂ K := C.harm ⊓ C.deg a

theorem harmDeg_le_leadCycles (a : ℤ × ℤ) : C.harmDeg a ≤ C.leadCycles a :=
  fun _ hx => ⟨((C.mem_harm_iff _).mp hx.1).1, hx.2⟩

/-- The map from harmonic vectors of bidegree `a` to their `Q⁻`-classes. -/
def harmToLead (a : ℤ × ℤ) : C.harmDeg a →ₗ[ℂ] C.leadCohom a :=
  (C.leadBoundaries a).mkQ.comp (Submodule.inclusion (C.harmDeg_le_leadCycles a))

/-- **Harmonic vectors inject into the leading cohomology** (the injection used in
§“Good action and harmonic bound” of the coset note): if a harmonic `h = Q⁻ y`, then
`⟨h|h⟩ = ⟨y|(Q⁻)† h⟩ = c ⟨y|S⁺ h⟩ = 0`. -/
theorem harmToLead_injective (a : ℤ × ℤ) : Function.Injective (C.harmToLead a) := by
  apply (LinearMap.ker_eq_bot).mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hmem : ((Submodule.inclusion (C.harmDeg_le_leadCycles a)) x : C.leadCycles a) ∈
      C.leadBoundaries a := (Submodule.Quotient.mk_eq_zero _).mp hx
  obtain ⟨y, -, hy⟩ := hmem
  have hSp : C.Sp (x : K) = 0 := ((C.mem_harm_iff _).mp x.2.1).2.2.2
  apply Subtype.ext
  change (x : K) = 0
  apply eq_zero_of_mem_range_of_adjoint_eq_zero C.P C.pos C.Qm ((C.c : ℂ) • C.Sp)
  · intro u v; rw [C.adj_Qm, LinearMap.smul_apply, C.P.smul_right]
  · exact ⟨y, hy⟩
  · rw [LinearMap.smul_apply, hSp, smul_zero]

/-- Dimension bound: harmonic vectors of bidegree `a` are at most `dim H(Q⁻)_a`. -/
theorem finrank_harmDeg_le_lead [FiniteDimensional ℂ K] (a : ℤ × ℤ) :
    finrank ℂ (C.harmDeg a) ≤ finrank ℂ (C.leadCohom a) :=
  LinearMap.finrank_le_finrank_of_injective (C.harmToLead_injective a)

end KahlerComplex

end VOA.GradedUnitaryCohomology
