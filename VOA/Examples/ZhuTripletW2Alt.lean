/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletW2Log
import VOA.Modules.ZhuVermaAnArchAModScope
import VOA.Modules.ZhuVermaAnArchDLM3Zero

/-!
# `OmegaJordanAt` through a module: a representation-theoretic certificate, and its obstruction

`Examples.TripletW2Log` reduces the existence of a genuinely logarithmic `W(2)`-module to one
Zhu-algebra non-membership,

  `OmegaJordanAt 𝒱 h  :  [ω] − h  ∉  A(𝒱)·([ω] − h)²` ,

and discharges nothing about it.  A non-membership in a left ideal is exactly the kind of statement
that a **representation** certifies: if some `A(𝒱)`-module separates `[ω] − h` from the ideal, the
non-membership is immediate.  This file develops that route in full, and then shows precisely how
far it gets on `W(2)`.

## §1–§2 The certificate (unconditional, and an *equivalence*)

* `AMod_rho_Amul` — a bundled `AMod` is multiplicative on **all** products of `A(𝒱)`, not only on
  representable ones (`mk` is surjective).  This is what makes a module usable against an ideal.
* `IsOmegaJordanVector M h m` — the certificate: `ρ([ω]−h)·(ρ([ω]−h)·m) = 0` and `ρ([ω]−h)·m ≠ 0`,
  i.e. `m` sits in a rank-two Jordan block of the (always central) operator `ρ([ω])` at `h`.
* `omegaJordanAt_of_jordanVector` — **one such vector in one `A(𝒱)`-module proves
  `OmegaJordanAt 𝒱 h`.**  Centrality of `[ω] − h` (`omegaShift_central`) is what makes the *left*
  ideal `A(𝒱)·([ω]−h)²` annihilate `m` as soon as `([ω]−h)²` does.
* `omegaJordanAt_iff_hasOmegaJordanVector` — the converse holds too, with the canonical bottom
  `A(𝒱) ⧸ A(𝒱)([ω]−h)²` of `TripletW2Log` as witness.  So the module route is **not lossy**: it is
  an exact reformulation, and nothing is given up by looking for a module instead of computing the
  algebra.
* `omegaJordanAt_of_nilpotent` — the certificate may be weakened all the way to: *some*
  `A(𝒱)`-module on which `ρ([ω]) − h` is nonzero and nilpotent (any nilpotency order).
* `omegaJordanAt_of_functional` — the dual shape: a linear functional on `A(𝒱)` killing the ideal
  but not `[ω] − h` (a pseudo-trace, in the logarithmic-CFT sense).

## §3 The certificate at the level of `𝒱` itself — no ring theory needed

Taking the regular module (`regularAMod`) and pushing everything back through `mk : 𝒱 ↠ A(𝒱)`:

* `omegaJordanAt_of_zhuMul` — `OmegaJordanAt 𝒱 h` follows from **one state `v ∈ 𝒱`** with

    `(ω − h·𝟙) ∗ v ∉ O(𝒱)`   and   `(ω − h·𝟙) ∗ ((ω − h·𝟙) ∗ v) ∈ O(𝒱)` ,

  where `∗ = zhuMul` and `O(𝒱)` is Zhu's subspace.  No quotient ring, no ideal, no Jordan form:
  two membership questions about `O(𝒱)` alone.  This is the cheapest formulation known to this
  file, and it is the one a future computation of `O(W(2))` should target.

## §4 ⚠ The obstruction — why the *suggested* module route provably cannot work

The natural supply of `A(𝒱)`-modules in this repository is Zhu's forward map `M ↦ M_h`
(`lowestAMod`, `LWModule.toAMod`), applied to the top level of an ordinary lowest-weight module.
**Every module produced that way is useless here, and this is a theorem:**

* `not_isOmegaJordanVector_of_omegaScalar` — if `[ω]` acts on `M` by a single scalar
  (`AMod.OmegaScalar`), then `M` has **no** Jordan vector at any `h` whatsoever.
* `not_isOmegaJordanVector_lowestAMod` / `not_isOmegaJordanVector_toAMod` — and
  `lowestAMod_omegaScalar` says the top level of an ordinary lowest-weight module is *always*
  `OmegaScalar`.  Hence `lowestAMod`/`forwardMap` can never certify `OmegaJordanAt`, for any VOA,
  any module, any weight.

So the plan "take a known `W(2)`-module, push its top level through the Zhu forward map" is not
merely unlucky for the particular module one picks — it is structurally impossible.  What is needed
is an `A(𝒱)`-module that is *not* the top of an ordinary lowest-weight module, and the only
generator of those in the library is `omegaJordanAMod` itself, whose usefulness is exactly
`OmegaJordanAt` (§2, the equivalence).  That circle is the real content of the blocker.

## §5 `W(2)`

`tripletW2Log_L0nil_ne_zero_of_jordanVector` / `_of_zhuMul` re-expose the `W(2)` main theorem of
`Examples.TripletW2Log` with `OmegaJordanAt` replaced by the module- and by the `O(𝒱)`-level
certificate.  They are drop-in alternatives: supply either certificate and the logarithmic module
with `L₀ⁿⁱˡ ≠ 0` follows.

**What is NOT proved here, stated exactly.**  No certificate is produced for `W(2)`.  Concretely:

1. `A(W(2))` is still uncomputed in this repository, so §3's two `O(W(2))`-membership questions
   cannot be answered here.
2. The module suggested as a source — the odd part `evenOdd QSF 1` of the symplectic-fermion Fock
   space, as a module over `tripletW2 = SF^even` — is not available:
   `VOASubalgebra.restrictWeakModule`
   (`Modules.ModuleRestrict`) restricts along a **bosonic** `VOASubalgebra` of a bosonic VOA on the
   *same* carrier, whereas `tripletW2 = sympFermSVOA.evenPartVOA` lives on the submodule
   `evenOdd QSF 0` of a **super** VOA; the repository contains no restriction of a (super) module to
   an even-part VOA, so `evenOdd QSF 1` carries no `tripletW2`-module structure here.
3. Even if it did, §4 forecloses the route: `L₀ = L0SF` is diagonal on the symplectic-fermion word
   basis, so any lowest-weight `W(2)`-module cut out of `FockSF` has `[ω]` acting on its top level
   by a single scalar, and `not_isOmegaJordanVector_of_omegaScalar` applies.

## Status

`sorry`-free; no `admit`, no `native_decide`, no new axiom.  Nothing outside this file is touched,
and every declaration lives in the fresh namespace `VOA.ZhuJordanAlt`.

## References
Zhu, *Modular invariance…*, J. AMS 9 (1996) (the algebra `A(V)`, Lemma 2.1.3 = centrality of `[ω]`);
Dong–Jiang `math/0601626`; Adamović–Milas on `A(W(p))`.  Repo cross-refs:
`Examples.TripletW2Log` (`omegaShift`, `zhuLeftMul`, `OmegaJordanAt`, `omegaJordanAMod`),
`Modules.ZhuBijection` (`AMod`, `lowestAMod`), `Modules.ZhuVermaAnArchAModScope`
(`AMod.OmegaScalar`, `lowestAMod_omegaScalar`), `Modules.ZhuVermaAnArchDLM3Zero` (`regularAMod`).
-/

namespace VOA

open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace ZhuJordanAlt

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## §1 A bundled `A(𝒱)`-module is multiplicative on every product -/

/-- **Full multiplicativity of a bundled `AMod`.**  `AMod.ρ_mul` is stated only on *representable*
Zhu products `[u ∗ v]`; since `mk : 𝒱 → A(𝒱)` is surjective this already gives multiplicativity on
all of `A(𝒱)`.  This is the form needed to make a module see a left ideal. -/
theorem AMod_rho_Amul (M : AMod W) (a b : A W) :
    M.ρ (Amul (zhuRingData_holds W) a b) = M.ρ a * M.ρ b := by
  obtain ⟨u, rfl⟩ := mk_surjective W a
  obtain ⟨v, rfl⟩ := mk_surjective W b
  rw [Amul_mk, M.ρ_mul]

/-- Pointwise form of `AMod_rho_Amul`. -/
theorem AMod_rho_Amul_apply (M : AMod W) (a b : A W) (m : M.carrier) :
    M.ρ (Amul (zhuRingData_holds W) a b) m = M.ρ a (M.ρ b m) := by
  rw [AMod_rho_Amul, Module.End.mul_apply]

/-! ## §2 The Jordan-vector certificate, and the equivalence -/

/-- **A Jordan vector at `h`.**  `m` is killed by `ρ([ω]−h)²` but not by `ρ([ω]−h)`: exactly a
rank-two Jordan block of the central operator `ρ([ω])` at the eigenvalue `h`. -/
def IsOmegaJordanVector (M : AMod W) (h : ℂ) (m : M.carrier) : Prop :=
  M.ρ (omegaShift W h) (M.ρ (omegaShift W h) m) = 0 ∧ M.ρ (omegaShift W h) m ≠ 0

/-- **Some `A(𝒱)`-module has a Jordan vector at `h`.** -/
def HasOmegaJordanVector (W : VertexOperatorAlgebra 𝒱) (h : ℂ) : Prop :=
  ∃ (M : AMod W) (m : M.carrier), IsOmegaJordanVector M h m

/-- **One Jordan vector in one `A(𝒱)`-module proves `OmegaJordanAt 𝒱 h`.**

If `[ω] − h = a·([ω]−h)²` then, acting on `m`, the right-hand side is `ρ(a)·ρ(([ω]−h)²)·m = 0`
while the left-hand side is `ρ([ω]−h)·m ≠ 0`.  Note that only the *square* has to annihilate `m`:
the whole left ideal follows, because `ρ` is multiplicative (`AMod_rho_Amul`). -/
theorem omegaJordanAt_of_jordanVector {M : AMod W} {h : ℂ} {m : M.carrier}
    (hm : IsOmegaJordanVector M h m) : OmegaJordanAt W h := by
  intro hmem
  obtain ⟨a, ha⟩ := (mem_zhuLeftMul W).mp hmem
  refine hm.2 ?_
  rw [← ha, AMod_rho_Amul_apply, AMod_rho_Amul_apply, hm.1, map_zero]

/-- The canonical bottom `A(𝒱) ⧸ A(𝒱)([ω]−h)²` of `Examples.TripletW2Log` carries a Jordan vector
as soon as `OmegaJordanAt 𝒱 h` holds — the class of the unit. -/
theorem hasOmegaJordanVector_of_omegaJordanAt {h : ℂ} (hnd : OmegaJordanAt W h) :
    HasOmegaJordanVector W h := by
  refine ⟨omegaJordanAMod W h, Submodule.Quotient.mk (mk W W.vacuum), ?_, ?_⟩
  · change zhuQuotRho W (Amul (zhuRingData_holds W) (omegaShift W h) (omegaShift W h))
        (omegaShift W h) (zhuQuotRho W
          (Amul (zhuRingData_holds W) (omegaShift W h) (omegaShift W h)) (omegaShift W h)
          (Submodule.Quotient.mk (mk W W.vacuum))) = 0
    have hsq := zhuQuotRho_omegaShift_sq W h
    rw [pow_two] at hsq
    have hap := LinearMap.congr_fun hsq
      (Submodule.Quotient.mk (mk W W.vacuum) : A W ⧸ zhuLeftMul W
        (Amul (zhuRingData_holds W) (omegaShift W h) (omegaShift W h)))
    rwa [Module.End.mul_apply, LinearMap.zero_apply] at hap
  · change zhuQuotRho W (Amul (zhuRingData_holds W) (omegaShift W h) (omegaShift W h))
        (omegaShift W h) (Submodule.Quotient.mk (mk W W.vacuum)) ≠ 0
    rw [zhuQuotRho_apply, Amul_one_right, Ne, Submodule.Quotient.mk_eq_zero]
    exact hnd

/-- **The module route is an exact reformulation, not a weakening.** -/
theorem omegaJordanAt_iff_hasOmegaJordanVector (W : VertexOperatorAlgebra 𝒱) (h : ℂ) :
    OmegaJordanAt W h ↔ HasOmegaJordanVector W h :=
  ⟨hasOmegaJordanVector_of_omegaJordanAt,
    fun ⟨_, _, hm⟩ => omegaJordanAt_of_jordanVector hm⟩

/-- **The certificate only needs nilpotency of some order.**  If `ρ([ω]) − h` is nonzero and
nilpotent on *some* `A(𝒱)`-module, a rank-two Jordan vector can be extracted from the top of the
Jordan filtration, and `OmegaJordanAt 𝒱 h` follows. -/
theorem omegaJordanAt_of_nilpotent (M : AMod W) (h : ℂ) (k : ℕ)
    (hk : M.ρ (omegaShift W h) ^ k = 0) (hne : M.ρ (omegaShift W h) ≠ 0) :
    OmegaJordanAt W h := by
  set f : Module.End ℂ M.carrier := M.ρ (omegaShift W h) with hf
  -- `f ^ (i+1) = 0` for some `i`.
  have hex : ∃ i : ℕ, f ^ (i + 1) = 0 := by
    cases k with
    | zero =>
        exfalso
        have h1 : (1 : Module.End ℂ M.carrier) = 0 := by simpa using hk
        exact hne (by rw [← mul_one f, h1, mul_zero])
    | succ j => exact ⟨j, hk⟩
  classical
  have hfind := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    refine hne ?_
    have := Nat.find_spec hex
    rw [h0, zero_add, pow_one] at this
    exact this
  obtain ⟨j, hj⟩ : ∃ j : ℕ, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hjne : f ^ (j + 1) ≠ 0 := by
    have := Nat.find_min hex (m := j) (by omega)
    exact this
  have hj2 : f ^ (j + 1 + 1) = 0 := by rw [← hj]; exact hfind
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp hjne
  rw [LinearMap.zero_apply] at hw
  refine omegaJordanAt_of_jordanVector (M := M) (h := h) (m := (f ^ j) w) ⟨?_, ?_⟩
  · rw [← hf, ← pow_succ'_apply f j w, ← pow_succ'_apply f (j + 1) w, hj2,
      LinearMap.zero_apply]
  · rw [← hf, ← pow_succ'_apply f j w]
    exact hw

/-- **A pseudo-trace-shaped certificate.**  A `ℂ`-linear functional on `A(𝒱)` that annihilates the
left ideal `A(𝒱)·([ω]−h)²` but not `[ω] − h` certifies `OmegaJordanAt 𝒱 h` outright.  This is the
shape in which logarithmic conformal field theory actually delivers the Jordan block (Miyamoto's
pseudo-trace functions); over a field it is equivalent to the non-membership itself, by extending a
functional off a subspace, and no module has to be built. -/
theorem omegaJordanAt_of_functional {h : ℂ} (f : A W →ₗ[ℂ] ℂ)
    (hf : ∀ a : A W, f (Amul (zhuRingData_holds W) a
      (Amul (zhuRingData_holds W) (omegaShift W h) (omegaShift W h))) = 0)
    (hne : f (omegaShift W h) ≠ 0) : OmegaJordanAt W h := by
  intro hmem
  obtain ⟨a, ha⟩ := (mem_zhuLeftMul W).mp hmem
  exact hne (by rw [← ha]; exact hf a)

/-! ## §3 The certificate at the level of `𝒱`: two `O(𝒱)`-membership questions -/

/-- **`ω − h·𝟙` as a state of `𝒱`** (the representative of `omegaShift W h`). -/
noncomputable def omegaSubV (W : VertexOperatorAlgebra 𝒱) (h : ℂ) : 𝒱 :=
  W.conformalVector - h • W.vacuum

@[simp] theorem mk_omegaSubV (W : VertexOperatorAlgebra 𝒱) (h : ℂ) :
    mk W (omegaSubV W h) = omegaShift W h := by
  rw [omegaSubV, map_sub, map_smul, omegaShift]

/-- The certificate on the **regular** `A(𝒱)`-module: one class `x ∈ A(𝒱)` with `([ω]−h)·x ≠ 0`
and `([ω]−h)²·x = 0`. -/
theorem omegaJordanAt_of_regular {h : ℂ} {x : A W}
    (hsq : Amul (zhuRingData_holds W) (omegaShift W h)
        (Amul (zhuRingData_holds W) (omegaShift W h) x) = 0)
    (hne : Amul (zhuRingData_holds W) (omegaShift W h) x ≠ 0) :
    OmegaJordanAt W h :=
  omegaJordanAt_of_jordanVector (M := regularAMod W) (h := h) (m := x) ⟨hsq, hne⟩

/-- **The cheapest formulation: one state and two `O(𝒱)`-memberships.**

`OmegaJordanAt 𝒱 h` holds as soon as there is a single `v ∈ 𝒱` with

  `(ω − h·𝟙) ∗ v ∉ O(𝒱)`  and  `(ω − h·𝟙) ∗ ((ω − h·𝟙) ∗ v) ∈ O(𝒱)`.

Neither the ring structure of `A(𝒱)` nor any ideal or Jordan form appears: only Zhu's product `∗`
and Zhu's subspace `O(𝒱)`.  For `W(2)` at `h = 0` this asks for a state `v` with `ω ∗ v ∉ O(W(2))`
but `ω ∗ ω ∗ v ∈ O(W(2))`; the repository does not (yet) know `O(W(2))` well enough to exhibit
one. -/
theorem omegaJordanAt_of_zhuMul {h : ℂ} (v : 𝒱)
    (hsq : zhuMul W (omegaSubV W h) (zhuMul W (omegaSubV W h) v) ∈ O W)
    (hne : zhuMul W (omegaSubV W h) v ∉ O W) :
    OmegaJordanAt W h := by
  refine omegaJordanAt_of_regular (W := W) (h := h) (x := mk W v) ?_ ?_
  · rw [← mk_omegaSubV W h, Amul_mk, Amul_mk, mk_eq_zero_iff]
    exact hsq
  · rw [← mk_omegaSubV W h, Amul_mk]
    intro hz
    exact hne ((mk_eq_zero_iff W).mp hz)

/-! ## §4 ⚠ The obstruction: `[ω]`-scalar modules never certify anything -/

/-- **A module on which `[ω]` acts by a scalar has no Jordan vector, at any weight.**

If `ρ([ω]) = h₀`, then `ρ([ω]−h) = (h₀−h)·1`.  For `h = h₀` this is `0`, so no vector survives the
`≠ 0` clause; for `h ≠ h₀` it is invertible, so the `= 0` clause forces `m = 0`, and then the `≠ 0`
clause fails again. -/
theorem not_isOmegaJordanVector_of_omegaScalar {M : AMod W} {h₀ : ℂ} (hM : M.OmegaScalar h₀)
    (h : ℂ) (m : M.carrier) : ¬ IsOmegaJordanVector M h m := by
  have hrho : M.ρ (omegaShift W h) = (h₀ - h) • (1 : Module.End ℂ M.carrier) := by
    rw [omegaShift, map_sub, map_smul, hM, show mk W W.vacuum = one W from rfl, M.ρ_one, sub_smul]
  rintro ⟨hsq, hne⟩
  rw [hrho] at hsq hne
  simp only [LinearMap.smul_apply, Module.End.one_apply, smul_smul] at hsq hne
  have hd : h₀ - h ≠ 0 := by
    intro h0
    exact hne (by rw [h0, zero_smul])
  have hm0 : m = 0 := by
    rcases smul_eq_zero.mp hsq with hc | hm
    · exact absurd hc (mul_ne_zero hd hd)
    · exact hm
  exact hne (by rw [hm0, smul_zero])

variable {Mod : Type u} [AddCommGroup Mod] [Module ℂ Mod]

/-- **Zhu's forward map can never certify `OmegaJordanAt`.**  The top level `M_{h₀}` of an
ordinary lowest-weight module always has `[ω]` acting by the single scalar `h₀`
(`lowestAMod_omegaScalar`), hence carries no Jordan vector at any `h`. -/
theorem not_isOmegaJordanVector_lowestAMod {P : OrdVModule W Mod} {h₀ : ℂ}
    (hcw : IsLowestWeight P h₀) (h : ℂ) (x : (lowestAMod hcw).carrier) :
    ¬ IsOmegaJordanVector (lowestAMod hcw) h x :=
  not_isOmegaJordanVector_of_omegaScalar (lowestAMod_omegaScalar hcw) h x

/-- Same statement for the bundled `LWModule.toAMod`. -/
theorem not_isOmegaJordanVector_toAMod (P : LWModule W) (h : ℂ) (x : P.toAMod.carrier) :
    ¬ IsOmegaJordanVector P.toAMod h x :=
  not_isOmegaJordanVector_of_omegaScalar (LWModule.toAMod_omegaScalar P) h x

/-! ## §5 `W(2)`: the main theorem of `Examples.TripletW2Log` on the new certificates -/

section TripletW2

open CliffordAlgebra SympFerm

/-- `OmegaJordanAt tripletW2 h` from a `W(2)`-Zhu-module Jordan vector. -/
theorem tripletW2_omegaJordanAt_of_jordanVector {h : ℂ} {M : AMod tripletW2}
    {m : M.carrier} (hm : IsOmegaJordanVector M h m) : OmegaJordanAt tripletW2 h :=
  omegaJordanAt_of_jordanVector hm

/-- `OmegaJordanAt tripletW2 h` from a single state of `W(2)` and two `O(W(2))`-memberships. -/
theorem tripletW2_omegaJordanAt_of_zhuMul {h : ℂ} (v : evenOdd QSF 0)
    (hsq : zhuMul tripletW2 (omegaSubV tripletW2 h)
        (zhuMul tripletW2 (omegaSubV tripletW2 h) v) ∈ O tripletW2)
    (hne : zhuMul tripletW2 (omegaSubV tripletW2 h) v ∉ O tripletW2) :
    OmegaJordanAt tripletW2 h :=
  omegaJordanAt_of_zhuMul v hsq hne

/-- **The `W(2)` logarithmic module, with the Zhu-algebra crux replaced by a module
certificate.**  Drop-in alternative to `SympFerm.tripletW2Log_L0nil_ne_zero`. -/
theorem tripletW2Log_L0nil_ne_zero_of_jordanVector (h : ℂ)
    (hAnm : ∀ n : ℕ, FiniteDimensional ℂ (AnmFull tripletW2 n 0))
    (hA : FiniteDimensional ℂ (A tripletW2))
    (hgate : DJAnnEqAn tripletW2 0)
    {M : AMod tripletW2} {m : M.carrier} (hm : IsOmegaJordanVector M h m) :
    (tripletW2Log h hAnm hA).L0nil ≠ 0 :=
  tripletW2Log_L0nil_ne_zero h hAnm hA hgate (omegaJordanAt_of_jordanVector hm)

/-- The same, from the `O(W(2))`-level certificate. -/
theorem tripletW2Log_L0nil_ne_zero_of_zhuMul (h : ℂ)
    (hAnm : ∀ n : ℕ, FiniteDimensional ℂ (AnmFull tripletW2 n 0))
    (hA : FiniteDimensional ℂ (A tripletW2))
    (hgate : DJAnnEqAn tripletW2 0) (v : evenOdd QSF 0)
    (hsq : zhuMul tripletW2 (omegaSubV tripletW2 h)
        (zhuMul tripletW2 (omegaSubV tripletW2 h) v) ∈ O tripletW2)
    (hne : zhuMul tripletW2 (omegaSubV tripletW2 h) v ∉ O tripletW2) :
    (tripletW2Log h hAnm hA).L0nil ≠ 0 :=
  tripletW2Log_L0nil_ne_zero h hAnm hA hgate (omegaJordanAt_of_zhuMul v hsq hne)

end TripletW2

end ZhuJordanAlt

end VOA
