/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.SuperNearVOA

/-!
# BRST cohomology of a super vertex algebra

The differential-graded layer that the Drinfeld–Sokolov (quantum Hamiltonian) reduction is
built on: a super vertex algebra `V` equipped with an **odd** operator `Q` of square zero
which is a derivation of *every* product `u₍ₙ₎v`, and the statement that

  `H(V,Q) := ker Q / im Q`

is again a super vertex algebra, with `Y` induced from `V`.

## The Koszul sign in the derivation property

The whole construction turns on the sign in

  `Q(u₍ₙ₎v) = (Qu)₍ₙ₎v + (-1)^{|u|} u₍ₙ₎(Qv)`.

Rather than quantify over parity-homogeneous `u` (which would then have to be undone by a
parity decomposition every single time it is used), the axiom `Q_deriv` is stated with the
sign realized as the honest linear operator `(-1)^F` — `ParityGrading.parityInvol`, here
abbreviated `sgn V`:

  `Q(u₍ₙ₎v) = (Qu)₍ₙ₎v + (sgn V u)₍ₙ₎(Qv)`,   for **all** `u, v`.

This is *equivalent* to the homogeneous statement (`Q_deriv_homog` recovers it), because
both sides are linear in `u` and in `v`, but it is bilinear on the nose, which is what makes
the ideal computations below one-liners.

## What the sign buys

* `ker Q` is closed under all products (`Q_mode_eq_zero`), because `Qu = Qv = 0` kills both
  terms.
* `im Q` absorbs on the **left** against anything (`mode_mem_imQ_left`): `(Qa)₍ₙ₎v =
  Q(a₍ₙ₎v) - (sgn a)₍ₙ₎(Qv) = Q(a₍ₙ₎v)` when `Qv = 0`.
* `im Q` absorbs on the **right** against `Q`-closed states (`mode_mem_imQ_right`): apply
  the derivation property to `sgn V a` instead of `a`, using that `sgn` is an involution
  (`sgn_sgn`) preserving `ker Q` (`Q_sgn`: `Q ∘ (-1)^F = -(-1)^F ∘ Q`).

So `im Q` is a two-sided ideal *inside* `ker Q`, and `H(V,Q)` is a genuine subquotient.

## Main definitions and results

* `BRSTComplex V` — the data: a ghost-number grading, `Q` odd of ghost degree `+1` and
  conformal weight `0`, `Q² = 0`, and the derivation property.
* `BRSTComplex.Coh` — `H(V,Q) = ker Q / im Q`, built directly with
  `Submodule.mkQ` / `Submodule.mapQ` / `Submodule.liftQ` (no dependence on any general
  quotient-VOA construction).
* `BRSTComplex.cohomology : SuperVertexAlgebra C.Coh` — **the main theorem**: all
  fifteen axioms, with `Y` induced from `V`.
* `BRSTComplex.ghostH`, `BRSTComplex.H0` — the ghost-number grading descends, so `Hⁿ(V,Q)`
  and in particular `H⁰` are defined.  Ghost-number *additivity* under products is a
  separate, optional property (`BRSTComplex.GhostAdditive`); when it holds, `H⁰` is closed
  under all products (`BRSTComplex.H0_mode`) — which is where `W^k(𝔤,f)` lives.
* `BRSTComplex.cohEquivOfQZero` — for `Q = 0` the cohomology *is* `V` (a linear equivalence
  intertwining vacuum and all products).
* `BRSTComplex.Q_vacuum`, `BRSTComplex.vacuum_not_mem_imQ` — the vacuum is always `Q`-closed
  (a *theorem*, from `Q_deriv` and VA2/VA3), and it is not exact under the properness
  hypothesis "`𝟙` has ghost number `0` and there are no states of ghost number `-1`".
* `BRSTComplex.cohomologyNearVOA` — the conformal structure descends when `Qω = 0`:
  Virasoro, `L₀`-grading, translation and the central charge all survive.

## Implementation notes

The three gradings (conformal weight `ℂ`, parity `ZMod 2`, ghost number `ℤ`) all descend by
one general lemma, `isInternal_subquotient`: an internal grading of `M` induces an internal
grading of `K ⧸ I` whenever `I ≤ K` are both stable under the homogeneous projections.  That
stability is in turn one general lemma, `homogProj_shift`: an operator that moves the grading
by a *bijection* `e` of the index set commutes with the projections up to `e`, so its kernel
and its range are graded.  The three cases are `e = id` (weight), `e = (· + 1)` on `ZMod 2`
(parity: `Q` is odd) and `e = (· + 1)` on `ℤ` (ghost: `Q` raises ghost number).

The transport of identities from `ker Q` to `H` is organized by the relation
`Compat a A : ∀ x, A [x] = [a x]`, which is functorial for `+ - * •` and Lie brackets and
determines `A` uniquely — so every axiom on `H` is proved by exhibiting the operator on
`ker Q` that induces both sides.

## References
* Feigin–Frenkel, *Quantization of the Drinfeld–Sokolov reduction*, Phys. Lett. B246 (1990);
  Kac–Roan–Wakimoto, Comm. Math. Phys. 241 (2003) (the `W^k(g,f)` definition);
  Frenkel–Ben-Zvi §15 (BRST for vertex algebras); Kac, *VA for Beginners* §4.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u

namespace BRST

/-! ## §0.  Graded subquotients of an internally graded module

Everything in this section is grading-agnostic and vertex-algebra-free.  It is applied three
times below: to the conformal-weight grading, to the parity, and to the ghost number. -/

section GradedSubquotient

variable {ι : Type*} [DecidableEq ι] {M : Type*} [AddCommGroup M] [Module ℂ M]
  (A : ι → Submodule ℂ M) [DirectSum.Decomposition A]

/-- **An operator that shifts the grading by a bijection commutes with the projections.**

If `f (A i) ⊆ A (e i)` for an equivalence `e` of the index set, then
`π_{e i} ∘ f = f ∘ π_i`.  Taking `e = id` recovers `homogProj_comm`; the two cases that
matter here are `e = (· + 1)` on `ZMod 2` (an *odd* operator) and on `ℤ` (an operator of
ghost degree `+1`). -/
theorem homogProj_shift (f : M →ₗ[ℂ] M) (e : ι ≃ ι)
    (hf : ∀ i : ι, ∀ x ∈ A i, f x ∈ A (e i)) (i : ι) (x : M) :
    homogProj A (e i) (f x) = f (homogProj A i x) := by
  obtain ⟨s, hs, hs0⟩ := exists_sum_homogProj A x
  have hsum : f x = ∑ j ∈ s, f (homogProj A j x) := by
    conv_lhs => rw [← hs]
    exact map_sum f _ _
  rw [hsum, map_sum, Finset.sum_eq_single i]
  · rw [homogProj_of_mem A (hf i _ (homogProj_mem A i x))]
  · intro j _ hji
    exact homogProj_of_mem_ne A (fun h => hji (e.injective h)) (hf j _ (homogProj_mem A j x))
  · intro hi
    rw [hs0 i hi, map_zero, map_zero]

/-- **The kernel of a grading-shifting operator is a graded subspace.** -/
theorem homogProj_mem_ker {f : M →ₗ[ℂ] M} {e : ι ≃ ι}
    (hf : ∀ i : ι, ∀ x ∈ A i, f x ∈ A (e i)) (i : ι) {x : M}
    (hx : x ∈ LinearMap.ker f) : homogProj A i x ∈ LinearMap.ker f := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← homogProj_shift A f e hf i x, hx, map_zero]

/-- **The range of a grading-shifting operator is a graded subspace.**  Here the *bijectivity*
of `e` is used: to hit the piece `A j` one projects the source onto `A (e⁻¹ j)`. -/
theorem homogProj_mem_range {f : M →ₗ[ℂ] M} {e : ι ≃ ι}
    (hf : ∀ i : ι, ∀ x ∈ A i, f x ∈ A (e i)) (j : ι) {x : M}
    (hx : x ∈ LinearMap.range f) : homogProj A j x ∈ LinearMap.range f := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨homogProj A (e.symm j) a, ?_⟩
  have h := homogProj_shift A f e hf (e.symm j) a
  rw [e.apply_symm_apply] at h
  exact h.symm

/-- **A graded subquotient is graded.**

If `I` and `K` are both stable under the homogeneous projections of an internal grading `A`
of `M`, then the images of `A i ∩ K` in `K ⧸ I` form an internal grading of `K ⧸ I`.

Independence is the only real content: if `[b] = [c]` with `b` homogeneous of degree `i` and
`c` a sum of degrees `≠ i`, then `b - c ∈ I`, and projecting to degree `i` — which kills `c`
entirely and fixes `b` — puts `b` itself in `I`, i.e. `[b] = 0`. -/
theorem isInternal_subquotient {I K : Submodule ℂ M}
    (hK : ∀ i : ι, ∀ x ∈ K, homogProj A i x ∈ K)
    (hI : ∀ i : ι, ∀ x ∈ I, homogProj A i x ∈ I) :
    DirectSum.IsInternal
      (fun i : ι => Submodule.map (I.comap K.subtype).mkQ ((A i).comap K.subtype)) := by
  have hB : DirectSum.IsInternal (fun i : ι => (A i).comap K.subtype) :=
    isInternal_comap A K hK
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro y hy hy'
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy
    have hmapsup : (⨆ (j) (_ : j ≠ i),
          Submodule.map (I.comap K.subtype).mkQ ((A j).comap K.subtype))
        = Submodule.map (I.comap K.subtype).mkQ
            (⨆ (j) (_ : j ≠ i), (A j).comap K.subtype) := by
      simp only [Submodule.map_iSup]
    rw [hmapsup] at hy'
    obtain ⟨c, hc, hbc⟩ := Submodule.mem_map.mp hy'
    -- the degree-`i` projection annihilates everything of degree `≠ i`
    have hc0 : ∀ z : K, z ∈ (⨆ (j) (_ : j ≠ i), (A j).comap K.subtype) →
        homogProj A i (z : M) = 0 := by
      intro z hz
      refine Submodule.iSup_induction
        (motive := fun w : K => homogProj A i (w : M) = 0)
        (fun j => ⨆ (_ : j ≠ i), (A j).comap K.subtype) hz ?_ ?_ ?_
      · intro j w hw
        have hw2 : w ∈ ⨆ (_ : j ≠ i), (A j).comap K.subtype := hw
        by_cases hji : j = i
        · subst hji
          rw [iSup_neg (by simp)] at hw2
          rw [(Submodule.mem_bot ℂ).mp hw2]
          simp
        · rw [iSup_pos hji] at hw2
          have hw' : (w : M) ∈ A j := hw2
          exact homogProj_of_mem_ne A hji hw'
      · simp
      · intro w v hw hv
        rw [Submodule.coe_add, map_add, hw, hv, add_zero]
    have hcz := hc0 c hc
    have hsub : b - c ∈ I.comap K.subtype := by
      rw [← Submodule.ker_mkQ (I.comap K.subtype), LinearMap.mem_ker, map_sub, hbc, sub_self]
    have h2 : ((b : M) - (c : M)) ∈ I := by
      have h3 := hsub
      rwa [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub] at h3
    have hb' : (b : M) ∈ A i := hb
    have h1 : homogProj A i ((b : M) - (c : M)) = (b : M) := by
      rw [map_sub, hcz, sub_zero, homogProj_of_mem A hb']
    have hbI : (b : M) ∈ I := by
      rw [← h1]
      exact hI i _ h2
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_comap.mpr hbI
  · rw [← Submodule.map_iSup, hB.submodule_iSup_eq_top, Submodule.map_top,
      Submodule.range_mkQ]

end GradedSubquotient

/-! ## §1.  The fermion-number involution `(-1)^F` on a super vertex algebra -/

section Sign

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The parity grading of a super vertex algebra, bundled, so that `(-1)^F` is available. -/
def parGrading (V : SuperVertexAlgebra 𝒱) : ParityGrading 𝒱 :=
  ⟨V.parity, V.parity_isInternal⟩

/-- **`(-1)^F`**: `+1` on the even part, `-1` on the odd part.  This is the linear operator
that carries the Koszul sign of `Q_deriv`. -/
noncomputable def sgn (V : SuperVertexAlgebra 𝒱) : Module.End ℂ 𝒱 := (parGrading V).parityInvol

theorem sgn_even {V : SuperVertexAlgebra 𝒱} {u : 𝒱} (hu : u ∈ V.parity 0) : sgn V u = u :=
  (parGrading V).parityInvol_even hu

theorem sgn_odd {V : SuperVertexAlgebra 𝒱} {u : 𝒱} (hu : u ∈ V.parity 1) : sgn V u = -u :=
  (parGrading V).parityInvol_odd hu

/-- On a parity-homogeneous vector `(-1)^F` is the scalar `(-1)^{|u|}`. -/
theorem sgn_homog {V : SuperVertexAlgebra 𝒱} {p : ZMod 2} {u : 𝒱} (hu : u ∈ V.parity p) :
    sgn V u = parSign p • u :=
  (parGrading V).parityInvol_homog hu

/-- `(-1)^F` is an involution. -/
theorem sgn_sgn (V : SuperVertexAlgebra 𝒱) (u : 𝒱) : sgn V (sgn V u) = u := by
  obtain ⟨u₀, h₀, u₁, h₁, rfl⟩ := (parGrading V).exists_parity_decomp u
  have h : sgn V (u₀ + u₁) = u₀ - u₁ := by
    rw [map_add, sgn_even h₀, sgn_odd h₁]
    abel
  rw [h, map_sub, sgn_even h₀, sgn_odd h₁]
  abel

/-- `i ↦ i + 1`, as an equivalence of an additive group.  Used as the index shift of an odd
operator (`ZMod 2`) and of a ghost-degree-`+1` operator (`ℤ`). -/
def shiftOne (α : Type*) [AddGroup α] [One α] : α ≃ α where
  toFun a := a + 1
  invFun a := a - 1
  left_inv a := by simp
  right_inv a := by simp

@[simp] theorem shiftOne_apply {α : Type*} [AddGroup α] [One α] (a : α) :
    shiftOne α a = a + 1 := rfl

end Sign

/-! ## §2.  The BRST complex -/

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- A **BRST complex** on a super vertex algebra `V`: a ghost-number grading together with an
odd, square-zero differential `Q` of ghost degree `+1` and conformal weight `0` which is a
derivation of every product `u₍ₙ₎v`.

`Q_wt` (weight `0`) is what makes the conformal grading descend to the cohomology; `Q_odd`
and `Q_ghost` make the parity and the ghost number descend.  In the Drinfeld–Sokolov
application `Q = ∮ J_{BRST}(z)dz = (J_{BRST})₍₀₎` with `J_{BRST}` odd of weight `1` and ghost
number `1`, so all three hold.

The sign in `Q_deriv` is carried by the operator `sgn V = (-1)^F`; see the module docstring
and `Q_deriv_homog` for the equivalent homogeneous form. -/
structure BRSTComplex (V : SuperVertexAlgebra 𝒱) where
  /-- The ghost-number grading `𝒱 = ⊕_{g ∈ ℤ} 𝒱^{(g)}`. -/
  ghost : ℤ → Submodule ℂ 𝒱
  /-- The ghost-number grading is a genuine internal direct-sum decomposition. -/
  ghost_isInternal : DirectSum.IsInternal ghost
  /-- The BRST differential. -/
  Q : Module.End ℂ 𝒱
  /-- `Q` has conformal weight `0`. -/
  Q_wt : ∀ h : ℂ, ∀ v ∈ V.grading h, Q v ∈ V.grading h
  /-- `Q` is **odd**: it exchanges the two parity components. -/
  Q_odd : ∀ p : ZMod 2, ∀ v ∈ V.parity p, Q v ∈ V.parity (p + 1)
  /-- `Q` **raises the ghost number by one**. -/
  Q_ghost : ∀ g : ℤ, ∀ v ∈ ghost g, Q v ∈ ghost (g + 1)
  /-- `Q² = 0`. -/
  Q_sq : Q * Q = 0
  /-- **`Q` is a derivation of every product**, with the Koszul sign realized as `(-1)^F`:
  `Q(u₍ₙ₎v) = (Qu)₍ₙ₎v + ((-1)^F u)₍ₙ₎(Qv)`. -/
  Q_deriv : ∀ (u v : 𝒱) (n : ℤ),
    Q (mode (V.Y u) n v) = mode (V.Y (Q u)) n v + mode (V.Y (sgn V u)) n (Q v)

namespace BRSTComplex

variable {V : SuperVertexAlgebra 𝒱} (C : BRSTComplex V)

/-! ### Elementary consequences of the axioms -/

theorem Q_apply_Q (x : 𝒱) : C.Q (C.Q x) = 0 := by
  have h := congrArg (fun T : Module.End ℂ 𝒱 => T x) C.Q_sq
  simpa [Module.End.mul_apply] using h

/-- The homogeneous form of the derivation property:
`Q(u₍ₙ₎v) = (Qu)₍ₙ₎v + (-1)^{|u|} u₍ₙ₎(Qv)`. -/
theorem Q_deriv_homog {p : ZMod 2} {u : 𝒱} (hu : u ∈ V.parity p) (v : 𝒱) (n : ℤ) :
    C.Q (mode (V.Y u) n v)
      = mode (V.Y (C.Q u)) n v + parSign p • mode (V.Y u) n (C.Q v) := by
  rw [C.Q_deriv u v n, sgn_homog hu]
  congr 1
  rw [map_smul]
  rfl

/-- **`Q` anticommutes with `(-1)^F`**, because `Q` is odd.  This is what makes `ker Q`
stable under `(-1)^F`, which is what makes `im Q` absorb on the right. -/
theorem Q_sgn (u : 𝒱) : C.Q (sgn V u) = -sgn V (C.Q u) := by
  obtain ⟨u₀, h₀, u₁, h₁, rfl⟩ := (parGrading V).exists_parity_decomp u
  have hQ₀ : C.Q u₀ ∈ V.parity 1 := by
    have h := C.Q_odd 0 u₀ h₀
    rwa [zero_add] at h
  have hQ₁ : C.Q u₁ ∈ V.parity 0 := by
    have h := C.Q_odd 1 u₁ h₁
    rwa [show (1 : ZMod 2) + 1 = 0 from by decide] at h
  have hs : sgn V (u₀ + u₁) = u₀ - u₁ := by
    rw [map_add, sgn_even h₀, sgn_odd h₁]
    abel
  have ht : sgn V (C.Q u₀ + C.Q u₁) = -C.Q u₀ + C.Q u₁ := by
    rw [map_add, sgn_odd hQ₀, sgn_even hQ₁]
  rw [hs, map_sub, map_add, ht]
  abel

theorem sgn_mem_ker {u : 𝒱} (hu : C.Q u = 0) : C.Q (sgn V u) = 0 := by
  rw [C.Q_sgn u, hu, map_zero, neg_zero]

/-! ### `ker Q` and `im Q` -/

/-- The **`Q`-closed** states. -/
def kerQ : Submodule ℂ 𝒱 := LinearMap.ker C.Q

/-- The **`Q`-exact** states. -/
def imQ : Submodule ℂ 𝒱 := LinearMap.range C.Q

theorem mem_kerQ {x : 𝒱} : x ∈ C.kerQ ↔ C.Q x = 0 := LinearMap.mem_ker

theorem mem_imQ {x : 𝒱} : x ∈ C.imQ ↔ ∃ a : 𝒱, C.Q a = x := LinearMap.mem_range

/-- `Q² = 0` says exactly that every exact state is closed. -/
theorem imQ_le_kerQ : C.imQ ≤ C.kerQ := by
  intro x hx
  rw [C.mem_imQ] at hx
  obtain ⟨a, rfl⟩ := hx
  rw [C.mem_kerQ]
  exact C.Q_apply_Q a

/-- **`ker Q` is closed under all products.**  Both terms of `Q_deriv` vanish. -/
theorem Q_mode_eq_zero {a : 𝒱} (ha : C.Q a = 0) (n : ℤ) {x : 𝒱} (hx : C.Q x = 0) :
    C.Q (mode (V.Y a) n x) = 0 := by
  have h1 : mode (V.Y (C.Q a)) n x = 0 := by
    rw [ha, map_zero]
    rfl
  have h2 : mode (V.Y (sgn V a)) n (C.Q x) = 0 := by
    rw [hx]
    exact map_zero _
  rw [C.Q_deriv a x n, h1, h2, add_zero]

/-- **`im Q` absorbs in the left slot** against `Q`-closed states:
`(Qa)₍ₙ₎v = Q(a₍ₙ₎v)` when `Qv = 0`. -/
theorem mode_mem_imQ_left {a : 𝒱} (ha : a ∈ C.imQ) (n : ℤ) (x : 𝒱) (hx : C.Q x = 0) :
    mode (V.Y a) n x ∈ C.imQ := by
  rw [C.mem_imQ] at ha
  obtain ⟨b, rfl⟩ := ha
  have h := C.Q_deriv b x n
  rw [hx] at h
  have h2 : mode (V.Y (sgn V b)) n (0 : 𝒱) = 0 := map_zero _
  rw [h2, add_zero] at h
  rw [C.mem_imQ]
  exact ⟨mode (V.Y b) n x, h⟩

/-- **`im Q` absorbs in the right slot** against `Q`-closed states:
`a₍ₙ₎(Qb) = Q(((-1)^F a)₍ₙ₎b)` when `Qa = 0`. -/
theorem mode_mem_imQ_right {a : 𝒱} (ha : C.Q a = 0) (n : ℤ) {x : 𝒱} (hx : x ∈ C.imQ) :
    mode (V.Y a) n x ∈ C.imQ := by
  rw [C.mem_imQ] at hx
  obtain ⟨b, rfl⟩ := hx
  have hs : C.Q (sgn V a) = 0 := C.sgn_mem_ker ha
  have h := C.Q_deriv (sgn V a) b n
  rw [hs, map_zero] at h
  have h1 : mode (0 : (Module.End ℂ 𝒱)⟦z^±⟧) n b = 0 := rfl
  rw [h1, zero_add, sgn_sgn] at h
  rw [C.mem_imQ]
  exact ⟨mode (V.Y (sgn V a)) n b, h⟩

/-- **The vacuum is `Q`-closed** — a theorem, not an axiom.  Apply `Q_deriv` to
`u = v = 𝟙`, `n = -1`: creation (VA3) turns the left side into `Q𝟙`, and VA2/VA3 turn the
right side into `Q𝟙 + Q𝟙`. -/
theorem Q_vacuum : C.Q V.vacuum = 0 := by
  have h := C.Q_deriv V.vacuum V.vacuum (-1)
  have e1 : mode (V.Y V.vacuum) (-1) V.vacuum = V.vacuum := V.smul_neg_one_vacuum V.vacuum
  have e2 : mode (V.Y (C.Q V.vacuum)) (-1) V.vacuum = C.Q V.vacuum :=
    V.smul_neg_one_vacuum (C.Q V.vacuum)
  have e3 : sgn V V.vacuum = V.vacuum := sgn_even V.vacuum_parity
  have e4 : mode (V.Y V.vacuum) (-1) (C.Q V.vacuum) = C.Q V.vacuum := by
    rw [V.vacuum_Y, mode_one, if_pos rfl]
    rfl
  rw [e1, e2, e3, e4] at h
  have h4 := congrArg (fun t : 𝒱 => t - C.Q V.vacuum) h
  simp only [sub_self, add_sub_cancel_right] at h4
  exact h4.symm

theorem vacuum_mem_kerQ : V.vacuum ∈ C.kerQ := C.mem_kerQ.mpr C.Q_vacuum

/-- The vacuum, as an element of `ker Q`. -/
def vacK : C.kerQ := ⟨V.vacuum, C.vacuum_mem_kerQ⟩

@[simp] theorem vacK_coe : ((C.vacK : C.kerQ) : 𝒱) = V.vacuum := rfl

/-! ### The cohomology as a module -/

/-- `im Q`, viewed inside `ker Q`. -/
def imQ' : Submodule ℂ C.kerQ := C.imQ.comap C.kerQ.subtype

theorem mem_imQ' {x : C.kerQ} : x ∈ C.imQ' ↔ (x : 𝒱) ∈ C.imQ := Iff.rfl

/-- **BRST cohomology** `H(V,Q) = ker Q / im Q`. -/
abbrev Coh : Type u := C.kerQ ⧸ C.imQ'

/-- The class of a `Q`-closed state in cohomology. -/
def prj : C.kerQ →ₗ[ℂ] C.Coh := C.imQ'.mkQ

theorem prj_surjective : Function.Surjective C.prj := Submodule.mkQ_surjective _

/-- **A class vanishes exactly when the representative is exact.** -/
theorem prj_eq_zero {x : C.kerQ} : C.prj x = 0 ↔ (x : 𝒱) ∈ C.imQ := by
  rw [prj, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

/-! ### The induced state–field correspondence -/

/-- Every coefficient of `Y(a,z)`, for `a` a `Q`-closed state, preserves `ker Q`. -/
theorem coeff_mem_kerQ (a : C.kerQ) (k : ℤ) (x : 𝒱) (hx : x ∈ C.kerQ) :
    V.Y (a : 𝒱) k x ∈ C.kerQ := by
  rw [C.mem_kerQ]
  have h := C.Q_mode_eq_zero (C.mem_kerQ.mp a.2) (-k - 1) (C.mem_kerQ.mp hx)
  rwa [mode_apply, show -(-k - 1) - 1 = k from by ring] at h

/-- `Y(a,z)ₖ` restricted to `ker Q`. -/
noncomputable def Yker (a : C.kerQ) (k : ℤ) : Module.End ℂ C.kerQ :=
  (V.Y (a : 𝒱) k).restrict (C.coeff_mem_kerQ a k)

@[simp] theorem Yker_coe (a : C.kerQ) (k : ℤ) (x : C.kerQ) :
    ((C.Yker a k x : C.kerQ) : 𝒱) = V.Y (a : 𝒱) k (x : 𝒱) := rfl

/-- The `n`-th product on `ker Q`. -/
noncomputable def modeK (a : C.kerQ) (n : ℤ) : Module.End ℂ C.kerQ := C.Yker a (-n - 1)

@[simp] theorem modeK_coe (a : C.kerQ) (n : ℤ) (x : C.kerQ) :
    ((C.modeK a n x : C.kerQ) : 𝒱) = mode (V.Y (a : 𝒱)) n (x : 𝒱) := rfl

/-- `Y(a,z)ₖ` preserves `im Q` inside `ker Q`, by right-slot absorption. -/
theorem Yker_stable (a : C.kerQ) (k : ℤ) : C.imQ' ≤ C.imQ'.comap (C.Yker a k) := by
  intro x hx
  have hx' : (x : 𝒱) ∈ C.imQ := hx
  have h := C.mode_mem_imQ_right (C.mem_kerQ.mp a.2) (-k - 1) hx'
  rw [mode_apply, show -(-k - 1) - 1 = k from by ring] at h
  rw [Submodule.mem_comap, mem_imQ', Yker_coe]
  exact h

/-- `Y(a,z)ₖ` on the cohomology. -/
noncomputable def Ycoh (a : C.kerQ) (k : ℤ) : Module.End ℂ C.Coh :=
  Submodule.mapQ C.imQ' C.imQ' (C.Yker a k) (C.Yker_stable a k)

@[simp] theorem Ycoh_prj (a : C.kerQ) (k : ℤ) (x : C.kerQ) :
    C.Ycoh a k (C.prj x) = C.prj (C.Yker a k x) := rfl

/-! ### `Compat`: transporting operators from `ker Q` to `H` -/

/-- `A : End H` is **induced by** `a : End (ker Q)`. -/
def Compat (a : Module.End ℂ C.kerQ) (A : Module.End ℂ C.Coh) : Prop :=
  ∀ x : C.kerQ, A (C.prj x) = C.prj (a x)

variable {C}

theorem compat_unique {a : Module.End ℂ C.kerQ} {A B : Module.End ℂ C.Coh}
    (hA : C.Compat a A) (hB : C.Compat a B) : A = B := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := C.prj_surjective y
  rw [hA x, hB x]

theorem compat_add {a b : Module.End ℂ C.kerQ} {A B : Module.End ℂ C.Coh}
    (ha : C.Compat a A) (hb : C.Compat b B) : C.Compat (a + b) (A + B) := by
  intro x
  rw [LinearMap.add_apply, ha x, hb x, LinearMap.add_apply, map_add]

theorem compat_sub {a b : Module.End ℂ C.kerQ} {A B : Module.End ℂ C.Coh}
    (ha : C.Compat a A) (hb : C.Compat b B) : C.Compat (a - b) (A - B) := by
  intro x
  rw [LinearMap.sub_apply, ha x, hb x, LinearMap.sub_apply, map_sub]

theorem compat_mul {a b : Module.End ℂ C.kerQ} {A B : Module.End ℂ C.Coh}
    (ha : C.Compat a A) (hb : C.Compat b B) : C.Compat (a * b) (A * B) := by
  intro x
  rw [Module.End.mul_apply, hb x, ha (b x), Module.End.mul_apply]

theorem compat_smul {a : Module.End ℂ C.kerQ} {A : Module.End ℂ C.Coh}
    (ha : C.Compat a A) (c : ℂ) : C.Compat (c • a) (c • A) := by
  intro x
  rw [LinearMap.smul_apply, ha x, LinearMap.smul_apply, map_smul]

theorem compat_zsmul {a : Module.End ℂ C.kerQ} {A : Module.End ℂ C.Coh}
    (ha : C.Compat a A) (k : ℤ) : C.Compat (k • a) (k • A) := by
  have h1 : (k • a) = ((k : ℂ) • a) := (Int.cast_smul_eq_zsmul ℂ k a).symm
  have h2 : (k • A) = ((k : ℂ) • A) := (Int.cast_smul_eq_zsmul ℂ k A).symm
  rw [h1, h2]
  exact compat_smul ha _

theorem compat_one : C.Compat (1 : Module.End ℂ C.kerQ) (1 : Module.End ℂ C.Coh) :=
  fun _ => rfl

theorem compat_zero : C.Compat (0 : Module.End ℂ C.kerQ) (0 : Module.End ℂ C.Coh) := by
  intro x
  rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

theorem compat_lie {a b : Module.End ℂ C.kerQ} {A B : Module.End ℂ C.Coh}
    (ha : C.Compat a A) (hb : C.Compat b B) : C.Compat ⁅a, b⁆ ⁅A, B⁆ := by
  simp only [Ring.lie_def]
  exact compat_sub (compat_mul ha hb) (compat_mul hb ha)

variable (C)

theorem compat_Ycoh (a : C.kerQ) (k : ℤ) : C.Compat (C.Yker a k) (C.Ycoh a k) := fun _ => rfl

/-! ### `Y` descends to the cohomology -/

/-- The state–field correspondence before quotienting the *source*. -/
noncomputable def Ydist (a : C.kerQ) : (Module.End ℂ C.Coh)⟦z^±⟧ := fun k => C.Ycoh a k

theorem Yker_add (a b : C.kerQ) (k : ℤ) :
    C.Yker (a + b) k = C.Yker a k + C.Yker b k := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  have hL : ((C.Yker (a + b) k x : C.kerQ) : 𝒱)
      = V.Y ((a : 𝒱) + (b : 𝒱)) k (x : 𝒱) := by
    rw [Yker_coe, show ((a + b : C.kerQ) : 𝒱) = (a : 𝒱) + (b : 𝒱) from rfl]
  have hR : (((C.Yker a k + C.Yker b k) x : C.kerQ) : 𝒱)
      = V.Y (a : 𝒱) k (x : 𝒱) + V.Y (b : 𝒱) k (x : 𝒱) := rfl
  rw [hL, hR, map_add]
  rfl

theorem Yker_smul (c : ℂ) (a : C.kerQ) (k : ℤ) :
    C.Yker (c • a) k = c • C.Yker a k := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  have hL : ((C.Yker (c • a) k x : C.kerQ) : 𝒱) = V.Y (c • (a : 𝒱)) k (x : 𝒱) := by
    rw [Yker_coe, show ((c • a : C.kerQ) : 𝒱) = c • (a : 𝒱) from rfl]
  have hR : (((c • C.Yker a k) x : C.kerQ) : 𝒱) = c • (V.Y (a : 𝒱) k (x : 𝒱)) := rfl
  rw [hL, hR, map_smul]
  rfl

theorem Ydist_add (a b : C.kerQ) : C.Ydist (a + b) = C.Ydist a + C.Ydist b := by
  refine FormalDist.ext fun k => ?_
  refine compat_unique (a := C.Yker a k + C.Yker b k) ?_ ?_
  · rw [← C.Yker_add a b k]
    exact C.compat_Ycoh (a + b) k
  · exact compat_add (C.compat_Ycoh a k) (C.compat_Ycoh b k)

theorem Ydist_smul (c : ℂ) (a : C.kerQ) : C.Ydist (c • a) = c • C.Ydist a := by
  refine FormalDist.ext fun k => ?_
  refine compat_unique (a := c • C.Yker a k) ?_ ?_
  · rw [← C.Yker_smul c a k]
    exact C.compat_Ycoh (c • a) k
  · exact compat_smul (C.compat_Ycoh a k) c

/-- `a ↦ Y(a,z)` on the cohomology, as a linear map out of `ker Q`. -/
noncomputable def Ylin : C.kerQ →ₗ[ℂ] (Module.End ℂ C.Coh)⟦z^±⟧ where
  toFun := C.Ydist
  map_add' := C.Ydist_add
  map_smul' := C.Ydist_smul

/-- **Exact states act as zero**: left-slot absorption is exactly what makes `Y` descend in
its first argument. -/
theorem Ylin_ker : C.imQ' ≤ LinearMap.ker C.Ylin := by
  intro a ha
  have ha' : (a : 𝒱) ∈ C.imQ := ha
  rw [LinearMap.mem_ker]
  refine FormalDist.ext fun k => ?_
  have hz : (0 : (Module.End ℂ C.Coh)⟦z^±⟧) k = (0 : Module.End ℂ C.Coh) := rfl
  have hl : C.Ylin a k = C.Ycoh a k := rfl
  rw [hl, hz]
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := C.prj_surjective y
  rw [Ycoh_prj, LinearMap.zero_apply, C.prj_eq_zero, Yker_coe]
  have h := C.mode_mem_imQ_left ha' (-k - 1) (x : 𝒱) (C.mem_kerQ.mp x.2)
  rwa [mode_apply, show -(-k - 1) - 1 = k from by ring] at h

/-- **The state–field correspondence of the cohomology.** -/
noncomputable def Ycohom : C.Coh →ₗ[ℂ] (Module.End ℂ C.Coh)⟦z^±⟧ :=
  C.imQ'.liftQ C.Ylin C.Ylin_ker

theorem Ycohom_prj (a : C.kerQ) : C.Ycohom (C.prj a) = C.Ydist a :=
  C.imQ'.liftQ_apply _ a

theorem compat_coeff (a : C.kerQ) (k : ℤ) :
    C.Compat (C.Yker a k) (C.Ycohom (C.prj a) k) := by
  intro x
  rw [Ycohom_prj]
  rfl

/-- **The products descend**: `[a]₍ₙ₎[x] = [a₍ₙ₎x]`. -/
theorem mode_Ycohom (a : C.kerQ) (n : ℤ) (x : C.kerQ) :
    mode (C.Ycohom (C.prj a)) n (C.prj x) = C.prj (C.modeK a n x) := by
  rw [mode_apply, Ycohom_prj]
  rfl

theorem compat_mode (a : C.kerQ) (n : ℤ) :
    C.Compat (C.modeK a n) (mode (C.Ycohom (C.prj a)) n) := fun x => C.mode_Ycohom a n x

/-! ### The three gradings of the cohomology -/

/-- The conformal-weight grading of the cohomology. -/
noncomputable def gradingH (h : ℂ) : Submodule ℂ C.Coh :=
  Submodule.map C.prj ((V.grading h).comap C.kerQ.subtype)

/-- The parity grading of the cohomology. -/
noncomputable def parityH (p : ZMod 2) : Submodule ℂ C.Coh :=
  Submodule.map C.prj ((V.parity p).comap C.kerQ.subtype)

/-- **The ghost-number grading of the cohomology**: `Hⁿ(V,Q)`. -/
noncomputable def ghostH (g : ℤ) : Submodule ℂ C.Coh :=
  Submodule.map C.prj ((C.ghost g).comap C.kerQ.subtype)

/-- `H⁰(V,Q)`, the ghost-number-zero part of the cohomology. -/
noncomputable def H0 : Submodule ℂ C.Coh := C.ghostH 0

theorem mem_gradingH {h : ℂ} {y : C.Coh} :
    y ∈ C.gradingH h ↔ ∃ x : C.kerQ, (x : 𝒱) ∈ V.grading h ∧ C.prj x = y := by
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
    exact ⟨x, hx, hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.mem_map_of_mem hx

theorem mem_parityH {p : ZMod 2} {y : C.Coh} :
    y ∈ C.parityH p ↔ ∃ x : C.kerQ, (x : 𝒱) ∈ V.parity p ∧ C.prj x = y := by
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
    exact ⟨x, hx, hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.mem_map_of_mem hx

theorem mem_ghostH {g : ℤ} {y : C.Coh} :
    y ∈ C.ghostH g ↔ ∃ x : C.kerQ, (x : 𝒱) ∈ C.ghost g ∧ C.prj x = y := by
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
    exact ⟨x, hx, hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.mem_map_of_mem hx

/-! ### Ghost-number additivity (an extra property, not part of the structure) -/

/-- The ghost number is **additive under all products**: `u₍ₙ₎v` has ghost number `|u|+|v|`.

This is deliberately *not* a field of `BRSTComplex`: none of the main theorem needs it, and
a `BRSTComplex` makes perfect sense without it.  It holds in the Drinfeld–Sokolov complex
(where the ghost grading is the `bc`-system charge, hence additive), and it is exactly what
is needed to know that `H⁰(V,Q)` — the degree in which `W^k(𝔤,f)` lives — is closed under
all products. -/
def GhostAdditive : Prop :=
  ∀ (g g' : ℤ), ∀ u ∈ C.ghost g, ∀ v ∈ C.ghost g', ∀ n : ℤ,
    mode (V.Y u) n v ∈ C.ghost (g + g')

/-- Ghost-number additivity descends to the cohomology: `Hᵍ · Hᵍ' ⊆ H^{g+g'}`. -/
theorem ghostH_mode (hadd : C.GhostAdditive) {g g' : ℤ} {ubar vbar : C.Coh}
    (hu : ubar ∈ C.ghostH g) (hv : vbar ∈ C.ghostH g') (n : ℤ) :
    mode (C.Ycohom ubar) n vbar ∈ C.ghostH (g + g') := by
  obtain ⟨a, ha, rfl⟩ := C.mem_ghostH.mp hu
  obtain ⟨b, hb, rfl⟩ := C.mem_ghostH.mp hv
  rw [C.mode_Ycohom]
  refine C.mem_ghostH.mpr ⟨C.modeK a n b, ?_, rfl⟩
  rw [C.modeK_coe]
  exact hadd g g' (a : 𝒱) ha (b : 𝒱) hb n

/-- **`H⁰(V,Q)` is closed under all products** when the ghost number is additive. -/
theorem H0_mode (hadd : C.GhostAdditive) {ubar vbar : C.Coh}
    (hu : ubar ∈ C.H0) (hv : vbar ∈ C.H0) (n : ℤ) :
    mode (C.Ycohom ubar) n vbar ∈ C.H0 := by
  have hu' : ubar ∈ C.ghostH 0 := hu
  have hv' : vbar ∈ C.ghostH 0 := hv
  have h := C.ghostH_mode hadd hu' hv' n
  have h2 : mode (C.Ycohom ubar) n vbar ∈ C.ghostH 0 := by rwa [zero_add] at h
  exact h2

/-- The conformal grading descends: `Q` has weight `0`. -/
theorem gradingH_isInternal : DirectSum.IsInternal C.gradingH := by
  classical
  haveI : DirectSum.Decomposition V.grading := V.isInternal.chooseDecomposition V.grading
  have hf : ∀ h : ℂ, ∀ x ∈ V.grading h, C.Q x ∈ V.grading ((Equiv.refl ℂ) h) :=
    fun h x hx => C.Q_wt h x hx
  exact isInternal_subquotient V.grading
    (fun h x hx => homogProj_mem_ker V.grading hf h hx)
    (fun h x hx => homogProj_mem_range V.grading hf h hx)

/-- The parity descends: `Q` is odd, i.e. it shifts the parity by the bijection `p ↦ p+1`. -/
theorem parityH_isInternal : DirectSum.IsInternal C.parityH := by
  classical
  haveI : DirectSum.Decomposition V.parity := V.parity_isInternal.chooseDecomposition V.parity
  have hf : ∀ p : ZMod 2, ∀ x ∈ V.parity p,
      C.Q x ∈ V.parity ((shiftOne (ZMod 2)) p) := fun p x hx => C.Q_odd p x hx
  exact isInternal_subquotient V.parity
    (fun p x hx => homogProj_mem_ker V.parity hf p hx)
    (fun p x hx => homogProj_mem_range V.parity hf p hx)

/-- **The ghost-number grading descends**, because `Q` raises it by the bijection
`g ↦ g+1`. -/
theorem ghostH_isInternal : DirectSum.IsInternal C.ghostH := by
  classical
  haveI : DirectSum.Decomposition C.ghost := C.ghost_isInternal.chooseDecomposition C.ghost
  have hf : ∀ g : ℤ, ∀ x ∈ C.ghost g, C.Q x ∈ C.ghost ((shiftOne ℤ) g) :=
    fun g x hx => C.Q_ghost g x hx
  exact isInternal_subquotient C.ghost
    (fun g x hx => homogProj_mem_ker C.ghost hf g hx)
    (fun g x hx => homogProj_mem_range C.ghost hf g hx)

/-- The weight spaces of the cohomology are finite-dimensional, being subquotients of the
(finite-dimensional) ambient weight spaces. -/
theorem gradingH_finiteDimensional (h : ℂ) : FiniteDimensional ℂ (C.gradingH h) := by
  haveI := V.finrank h
  haveI : FiniteDimensional ℂ ((V.grading h).comap C.kerQ.subtype) := by
    refine Module.Finite.of_injective (LinearMap.codRestrict (V.grading h)
      (C.kerQ.subtype.comp ((V.grading h).comap C.kerQ.subtype).subtype)
      (fun x => x.2)) ?_
    intro x y hxy
    have hcoe := congrArg Subtype.val hxy
    simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply,
      Submodule.subtype_apply] at hcoe
    exact Subtype.ext (Subtype.ext hcoe)
  have hrange : C.gradingH h
      = LinearMap.range (C.prj ∘ₗ ((V.grading h).comap C.kerQ.subtype).subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  rw [hrange]
  infer_instance

/-! ### Locality survives the subquotient -/

/-- Peeling one factor of `(z₁-z₂)` off `(z₁-z₂)^{N+1}`, in coefficient form. -/
theorem mulBySubPow_succ_coeff {𝒲 : Type*} [AddCommGroup 𝒲] [Module ℂ 𝒲] (k : ℕ)
    (H : FormalDist₂ 𝒲) (m n : ℤ) :
    mulBySubPow (k + 1) H m n = mulBySubPow k H (m - 1) n - mulBySubPow k H m (n - 1) := by
  rw [mulBySubPow_succ, LinearMap.comp_apply, mulBySub_apply]

/-- Transport of `(z₁-z₂)ᴺ` along the projection to cohomology. -/
theorem mulBySubPow_transport (F : FormalDist₂ (Module.End ℂ C.kerQ))
    (G : FormalDist₂ (Module.End ℂ C.Coh))
    (h : ∀ (m n : ℤ) (x : C.kerQ), G m n (C.prj x) = C.prj (F m n x)) (N : ℕ) :
    ∀ (m n : ℤ) (x : C.kerQ),
      mulBySubPow N G m n (C.prj x) = C.prj (mulBySubPow N F m n x) := by
  induction N with
  | zero => intro m n x; exact h m n x
  | succ k ih =>
    intro m n x
    rw [mulBySubPow_succ_coeff, LinearMap.sub_apply, ih (m - 1) n x, ih m (n - 1) x,
      ← map_sub, ← LinearMap.sub_apply, ← mulBySubPow_succ_coeff]

/-- The state–field correspondence on `ker Q`, as a formal distribution. -/
noncomputable def YkerD (a : C.kerQ) : (Module.End ℂ C.kerQ)⟦z^±⟧ := fun k => C.Yker a k

/-- The `ε`-twisted commutator on `ker Q` is the restriction of the ambient one. -/
theorem mulBySubPow_bracketε_coe (ε : ℂ) (a b : C.kerQ) (N : ℕ) (m n : ℤ) (x : C.kerQ) :
    ((mulBySubPow N (bracketDistε ε (C.YkerD a) (C.YkerD b)) m n x : C.kerQ) : 𝒱)
      = mulBySubPow N (bracketDistε ε (V.Y (a : 𝒱)) (V.Y (b : 𝒱))) m n (x : 𝒱) := by
  induction N generalizing m n with
  | zero =>
      simp only [mulBySubPow, LinearMap.id_apply, bracketDistε_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.mul_apply, Submodule.coe_sub, Submodule.coe_smul]
      rfl
  | succ N ih =>
      simp only [mulBySubPow, LinearMap.comp_apply, mulBySub_apply, LinearMap.sub_apply,
        Submodule.coe_sub, ih]

/-! ### The vacuum field -/

theorem Yker_vacuum (k : ℤ) :
    C.Yker C.vacK k = if k = 0 then (1 : Module.End ℂ C.kerQ) else 0 := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  rw [Yker_coe, vacK_coe, V.vacuum_Y, FormalDist.one_apply]
  by_cases hk : k = 0
  · rw [if_pos hk, if_pos hk]
    rfl
  · rw [if_neg hk, if_neg hk]
    rfl

/-! ## §3.  The main theorem: `H(V,Q)` is a super vertex algebra -/

/-- **BRST cohomology is a super vertex algebra.**

`ker Q` is closed under all products (`Q_mode_eq_zero`), `im Q` is a two-sided ideal inside
it (`mode_mem_imQ_left`, `mode_mem_imQ_right`), so `Y` descends; all three gradings descend
because `Q` shifts each of them by a bijection of the index set
(`gradingH_isInternal`, `parityH_isInternal`, `ghostH_isInternal`); and locality descends
because the projection `ker Q → H` intertwines the ambient `ε`-twisted commutator with the
induced one coefficient by coefficient. -/
noncomputable def cohomology : SuperVertexAlgebra C.Coh where
  grading := C.gradingH
  isInternal := C.gradingH_isInternal
  finrank := C.gradingH_finiteDimensional
  parity := C.parityH
  parity_isInternal := C.parityH_isInternal
  Y := C.Ycohom
  vacuum := C.prj C.vacK
  vacuum_mem := Submodule.mem_map_of_mem V.vacuum_mem
  vacuum_parity := Submodule.mem_map_of_mem V.vacuum_parity
  grading_mode := by
    intro h k ubar hu vbar hv n
    obtain ⟨a, ha, rfl⟩ := C.mem_gradingH.mp hu
    obtain ⟨b, hb, rfl⟩ := C.mem_gradingH.mp hv
    rw [C.mode_Ycohom]
    refine C.mem_gradingH.mpr ⟨C.modeK a n b, ?_, rfl⟩
    rw [C.modeK_coe]
    exact V.grading_mode (a : 𝒱) ha (b : 𝒱) hb n
  parity_mode := by
    intro p q ubar hu vbar hv n
    obtain ⟨a, ha, rfl⟩ := C.mem_parityH.mp hu
    obtain ⟨b, hb, rfl⟩ := C.mem_parityH.mp hv
    rw [C.mode_Ycohom]
    refine C.mem_parityH.mpr ⟨C.modeK a n b, ?_, rfl⟩
    rw [C.modeK_coe]
    exact V.parity_mode (a : 𝒱) ha (b : 𝒱) hb n
  vacuum_Y := by
    refine FormalDist.ext fun k => ?_
    have h1 : C.Ycohom (C.prj C.vacK) k = C.Ycoh C.vacK k := by
      rw [Ycohom_prj]
      rfl
    rw [h1, FormalDist.one_apply]
    by_cases hk : k = 0
    · rw [if_pos hk]
      refine compat_unique (a := (1 : Module.End ℂ C.kerQ)) ?_ compat_one
      have h := C.compat_Ycoh C.vacK k
      rwa [C.Yker_vacuum k, if_pos hk] at h
    · rw [if_neg hk]
      refine compat_unique (a := (0 : Module.End ℂ C.kerQ)) ?_ compat_zero
      have h := C.compat_Ycoh C.vacK k
      rwa [C.Yker_vacuum k, if_neg hk] at h
  creation := by
    intro ubar
    obtain ⟨a, rfl⟩ := C.prj_surjective ubar
    refine ⟨?_, ?_⟩
    · rw [C.mode_Ycohom]
      congr 1
      refine Subtype.ext ?_
      rw [C.modeK_coe, vacK_coe]
      exact V.smul_neg_one_vacuum (a : 𝒱)
    · intro n hn
      rw [C.mode_Ycohom]
      have hz : C.modeK a n C.vacK = 0 := by
        refine Subtype.ext ?_
        rw [C.modeK_coe, vacK_coe, Submodule.coe_zero]
        exact V.smul_vacuum_eq_zero (a : 𝒱) hn
      rw [hz, map_zero]
  locality := by
    intro p q ubar hu vbar hv
    obtain ⟨a, ha, rfl⟩ := C.mem_parityH.mp hu
    obtain ⟨b, hb, rfl⟩ := C.mem_parityH.mp hv
    obtain ⟨N, hN⟩ := V.locality (a : 𝒱) ha (b : 𝒱) hb
    refine ⟨N, ?_⟩
    have hbr : ∀ (m n : ℤ) (x : C.kerQ),
        bracketDistε (koszul p q) (C.Ycohom (C.prj a)) (C.Ycohom (C.prj b)) m n (C.prj x)
          = C.prj (bracketDistε (koszul p q) (C.YkerD a) (C.YkerD b) m n x) := by
      intro m n x
      exact (compat_sub (compat_mul (C.compat_coeff a m) (C.compat_coeff b n))
        (compat_smul (compat_mul (C.compat_coeff b n) (C.compat_coeff a m))
          (koszul p q))) x
    refine FormalDist₂.ext fun m n => ?_
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := C.prj_surjective y
    rw [C.mulBySubPow_transport _ _ hbr N m n x]
    have hz : mulBySubPow N (bracketDistε (koszul p q) (C.YkerD a) (C.YkerD b)) m n x = 0 := by
      refine Subtype.ext ?_
      rw [C.mulBySubPow_bracketε_coe _ a b N m n x, hN]
      rfl
    rw [hz, map_zero]
    rfl
  regularity := by
    intro ubar vbar
    obtain ⟨a, rfl⟩ := C.prj_surjective ubar
    obtain ⟨x, rfl⟩ := C.prj_surjective vbar
    obtain ⟨N, hN⟩ := V.regularity (a : 𝒱) (x : 𝒱)
    refine ⟨N, fun n hn => ?_⟩
    rw [C.mode_Ycohom]
    have hz : C.modeK a n x = 0 := by
      refine Subtype.ext ?_
      rw [C.modeK_coe, Submodule.coe_zero]
      exact hN n hn
    rw [hz, map_zero]

@[simp] theorem cohomology_Y : C.cohomology.Y = C.Ycohom := rfl

@[simp] theorem cohomology_vacuum : C.cohomology.vacuum = C.prj C.vacK := rfl

@[simp] theorem cohomology_grading : C.cohomology.grading = C.gradingH := rfl

@[simp] theorem cohomology_parity : C.cohomology.parity = C.parityH := rfl

/-! ## §4.  Sanity checks -/

/-! ### `Q = 0`: the cohomology is `V` itself -/

theorem kerQ_eq_top (hQ : C.Q = 0) : C.kerQ = ⊤ := by
  rw [kerQ, hQ, LinearMap.ker_zero]

theorem imQ_eq_bot (hQ : C.Q = 0) : C.imQ = ⊥ := by
  rw [imQ, hQ, LinearMap.range_zero]

/-- For `Q = 0` every state is closed. -/
noncomputable def ofKer (hQ : C.Q = 0) : 𝒱 →ₗ[ℂ] C.kerQ :=
  LinearMap.codRestrict C.kerQ LinearMap.id (fun x => by rw [C.kerQ_eq_top hQ]; trivial)

@[simp] theorem ofKer_coe (hQ : C.Q = 0) (x : 𝒱) : ((C.ofKer hQ x : C.kerQ) : 𝒱) = x := rfl

/-- The comparison map `V → H(V,0)`. -/
noncomputable def toCoh (hQ : C.Q = 0) : 𝒱 →ₗ[ℂ] C.Coh := C.prj ∘ₗ C.ofKer hQ

theorem toCoh_apply (hQ : C.Q = 0) (x : 𝒱) : C.toCoh hQ x = C.prj (C.ofKer hQ x) := rfl

theorem toCoh_injective (hQ : C.Q = 0) : Function.Injective (C.toCoh hQ) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  rw [toCoh_apply, C.prj_eq_zero, C.ofKer_coe, C.imQ_eq_bot hQ, Submodule.mem_bot] at hx
  exact hx

theorem toCoh_surjective (hQ : C.Q = 0) : Function.Surjective (C.toCoh hQ) := by
  intro y
  obtain ⟨x, rfl⟩ := C.prj_surjective y
  refine ⟨(x : 𝒱), ?_⟩
  rw [toCoh_apply]
  congr 1

/-- **`H(V,0) = V`**: for a vanishing differential the comparison map is a linear
isomorphism. -/
noncomputable def cohEquivOfQZero (hQ : C.Q = 0) : 𝒱 ≃ₗ[ℂ] C.Coh :=
  LinearEquiv.ofBijective (C.toCoh hQ) ⟨C.toCoh_injective hQ, C.toCoh_surjective hQ⟩

/-- …and it intertwines the vacua. -/
theorem toCoh_vacuum (hQ : C.Q = 0) : C.toCoh hQ V.vacuum = C.cohomology.vacuum := by
  rw [toCoh_apply]
  congr 1

/-- …and all the products. -/
theorem toCoh_mode (hQ : C.Q = 0) (a x : 𝒱) (n : ℤ) :
    mode (C.Ycohom (C.toCoh hQ a)) n (C.toCoh hQ x) = C.toCoh hQ (mode (V.Y a) n x) := by
  simp only [toCoh_apply]
  rw [C.mode_Ycohom]
  congr 1

/-! ### The vacuum survives -/

/-- **The vacuum is not exact**, under the properness hypothesis that `𝟙` has ghost number
`0` while there are *no* states of ghost number `-1`.

This is the honest hypothesis: `Q` raises the ghost number, so the ghost-number-`0` part of
`im Q` is `Q(𝒱^{(-1)})`, and if `𝒱^{(-1)} = 0` that part vanishes.  In the Drinfeld–Sokolov
complex the ghost numbers are bounded below by `0` on the relevant (semi-infinite) piece,
which is exactly this hypothesis. -/
theorem vacuum_not_mem_imQ (h0 : V.vacuum ∈ C.ghost 0) (hneg : C.ghost (-1) = ⊥)
    (hne : V.vacuum ≠ 0) : V.vacuum ∉ C.imQ := by
  classical
  haveI : DirectSum.Decomposition C.ghost := C.ghost_isInternal.chooseDecomposition C.ghost
  intro hmem
  rw [C.mem_imQ] at hmem
  obtain ⟨a, ha⟩ := hmem
  have hf : ∀ g : ℤ, ∀ x ∈ C.ghost g, C.Q x ∈ C.ghost ((shiftOne ℤ) g) :=
    fun g x hx => C.Q_ghost g x hx
  have hshift := homogProj_shift C.ghost C.Q (shiftOne ℤ) hf (-1) a
  have he : (shiftOne ℤ) (-1) = 0 := by
    rw [shiftOne_apply]
    norm_num
  rw [he, ha, homogProj_of_mem C.ghost h0] at hshift
  have hzero : homogProj C.ghost (-1) a = 0 := by
    have hm := homogProj_mem C.ghost (-1) a
    rw [hneg] at hm
    exact (Submodule.mem_bot ℂ).mp hm
  rw [hzero, map_zero] at hshift
  exact hne hshift

/-- Consequently the vacuum class of the cohomology is nonzero. -/
theorem cohomology_vacuum_ne_zero (h0 : V.vacuum ∈ C.ghost 0) (hneg : C.ghost (-1) = ⊥)
    (hne : V.vacuum ≠ 0) : C.cohomology.vacuum ≠ 0 := by
  intro hz
  rw [cohomology_vacuum, C.prj_eq_zero, vacK_coe] at hz
  exact C.vacuum_not_mem_imQ h0 hneg hne hz

end BRSTComplex

/-! ## §5.  The conformal structure descends -/

section Conformal

variable {𝒲 : Type u} [AddCommGroup 𝒲] [Module ℂ 𝒲] {W : SuperNearVOA 𝒲}
  (C : BRSTComplex W.toSuperVertexAlgebra) (hω : C.Q W.conformalVector = 0)

namespace BRSTComplex

/-- `ω`, as an element of `ker Q`. -/
def confK : C.kerQ := ⟨W.conformalVector, C.mem_kerQ.mpr hω⟩

@[simp] theorem confK_coe : ((confK C hω : C.kerQ) : 𝒲) = W.conformalVector := rfl

/-- The Virasoro relations on `ker Q`: the ambient ones, restricted. -/
theorem virasoro_ker (m n : ℤ) :
    ⁅C.modeK (confK C hω) (m + 1), C.modeK (confK C hω) (n + 1)⁆
      = ((m : ℂ) - n) • C.modeK (confK C hω) (m + n + 1)
        + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * W.centralCharge) •
            (1 : Module.End ℂ C.kerQ) else 0) := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  have h := congrArg (fun T : Module.End ℂ 𝒲 => T (x : 𝒲)) (W.virasoro m n)
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply] at h ⊢
  simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, modeK_coe, confK_coe]
  rw [h]
  split_ifs <;> simp

/-- The translation identity on `ker Q`: the ambient one, restricted. -/
theorem translation_ker (x : C.kerQ) (k : ℤ) :
    C.Yker (C.modeK (confK C hω) 0 x) k = ((k + 1 : ℤ) : ℂ) • C.Yker x (k + 1) := by
  refine LinearMap.ext fun y => Subtype.ext ?_
  rw [Yker_coe, modeK_coe, confK_coe, LinearMap.smul_apply, Submodule.coe_smul, Yker_coe]
  have h := congrArg (fun F : (Module.End ℂ 𝒲)⟦z^±⟧ => F k) (W.translation (x : 𝒲))
  simp only at h
  rw [h, deriv_apply, ← Int.cast_smul_eq_zsmul ℂ]
  rfl

/-- **The conformal structure descends when `ω` is `Q`-closed.**

The Virasoro relations, the `L₀`-grading and the translation axiom all transport along
`ker Q → H` by `Compat`, and the central charge is unchanged. -/
noncomputable def cohomologyNearVOA : SuperNearVOA C.Coh where
  toSuperVertexAlgebra := C.cohomology
  conformalVector := C.prj (confK C hω)
  conformal_mem := Submodule.mem_map_of_mem W.conformal_mem
  conformal_parity := Submodule.mem_map_of_mem W.conformal_parity
  centralCharge := W.centralCharge
  virasoro := by
    intro m n
    refine compat_unique
      (a := ⁅C.modeK (confK C hω) (m + 1), C.modeK (confK C hω) (n + 1)⁆) ?_ ?_
    · exact compat_lie (C.compat_mode (confK C hω) (m + 1))
        (C.compat_mode (confK C hω) (n + 1))
    · rw [virasoro_ker C hω m n]
      refine compat_add (compat_smul (C.compat_mode (confK C hω) (m + n + 1)) _) ?_
      split_ifs
      · exact compat_smul compat_one _
      · exact compat_zero
  L0_grading := by
    intro h ybar hy
    obtain ⟨x, hx, rfl⟩ := C.mem_gradingH.mp hy
    rw [cohomology_Y, C.mode_Ycohom]
    have hs : C.modeK (confK C hω) 1 x = h • x := by
      refine Subtype.ext ?_
      rw [C.modeK_coe, confK_coe, Submodule.coe_smul]
      exact W.L0_grading (x : 𝒲) hx
    rw [hs, map_smul]
  translation := by
    intro ybar
    obtain ⟨x, rfl⟩ := C.prj_surjective ybar
    rw [cohomology_Y, C.mode_Ycohom]
    refine FormalDist.ext fun k => ?_
    refine compat_unique (a := C.Yker (C.modeK (confK C hω) 0 x) k) ?_ ?_
    · exact C.compat_coeff (C.modeK (confK C hω) 0 x) k
    · rw [translation_ker C hω x k, deriv_apply, ← Int.cast_smul_eq_zsmul ℂ]
      exact compat_smul (C.compat_coeff x (k + 1)) _

@[simp] theorem cohomologyNearVOA_centralCharge :
    (cohomologyNearVOA C hω).centralCharge = W.centralCharge := rfl

@[simp] theorem cohomologyNearVOA_conformalVector :
    (cohomologyNearVOA C hω).conformalVector = C.prj (confK C hω) := rfl

end BRSTComplex

end Conformal

end BRST

end VOA
