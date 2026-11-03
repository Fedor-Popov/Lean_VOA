/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDLM3Level
import VOA.Modules.ZhuVermaAnArchResSkew
import VOA.Modules.ZhuVermaAnArchBottomDefectClose
import VOA.Modules.ZhuBijection

/-!
# DLM3 Proposition 3.1 at `n = 0`, and the level-0 `ParabolicRep` of an `A(𝒱)`-module

Dong–Li–Mason, *Vertex operator algebras and associative algebras* (arXiv `q-alg/9612010v2`),
Proposition 3.1, reads

> "Regarded `A_n(V)` as a Lie algebra, the map `v(wt v − 1) ↦ v + O_n(V)` is a well-defined onto
> Lie algebra homomorphism from `V̂(0)` to `A_n(V)`."

It is the step "By Proposition 3.1 we can lift `U` to a module for the Lie algebra `V̂(0)`, and then
to one for `P_n` … by letting `V̂(−p)` act trivially" of DLM3 (4.1) — i.e. **exactly** the input
datum `VHat.DLM3.ParabolicRep` of `ZhuVermaAnArchDLM3Induced`, which is otherwise an *assumed* input.

This file builds it at `n = 0`, where `A_0(𝒱) = A(𝒱)` is Zhu's algebra, from an ordinary bundled
`AMod` (`ZhuBijection`).  Nothing here is conditional: the whole chain is proved.

## What is proved

* `zhu_comm_mod_O` — **Zhu's Lemma 2.1.3** (= DLM3 Lemma 2.1(iii) at `n = 0`):
  for homogeneous `u ∈ 𝒱_K`, `v ∈ 𝒱_M`,
  `u * v − v * u − Res_z (1+z)^{K−1} Y(u,z)v ∈ O(𝒱)`.
  Derived from the proved residue skew relation `resHom_skew_mod_Onm` at `(N, m, P) = (0, 0, 1)`
  (whose scalar engine is `cbz_alt_vandermonde`) plus one Pascal step; `Onm_zero_zero_eq_O`
  identifies the Dong–Jiang ideal `O'_{0,0}` with Zhu's `O(𝒱)`.  DLM3's `−z/(1+z)` contour move and
  their Appendix Proposition 5.2 (trivial at `n = 0`) are both absorbed into that proved lemma.

* `VHat.zhuDeg0 : V̂ →ₗ[ℂ] A(𝒱)` — **DLM3 Proposition 3.1 at `n = 0`, as a map on all of `V̂`**:
  `a(m) ↦ [π_{m+1} a]`, where `π_w` is the grade-`w` projection.  It sends a degree-`0` generator
  `a(wt a − 1)` to `[a]` (`zhuDeg0_gen_deg_zero`) and kills every generator of nonzero degree
  (`zhuDeg0_gen_of_ne`), in particular the whole deep part (`zhuDeg0_deepPart`).  Well-definedness
  on the quotient `V̂ = ℂ[t,t⁻¹]⊗𝒱 / D(…)` is precisely the `O(𝒱)`-membership of the Zhu grading
  generator `L₋₁w + L₀w`.

* `VHat.zhuDeg0_bracket_parabolic` — **the Lie-morphism property**, in the form the parabolic
  needs: for `x, y ∈ P₀ = ⨁_{d ≤ 0} V̂(d)` and any `AMod` action `ρ`,
  `ρ (zhuDeg0 ⁅x,y⁆) = ρ(zhuDeg0 x)·ρ(zhuDeg0 y) − ρ(zhuDeg0 y)·ρ(zhuDeg0 x)`.
  Off the diagonal (`deg x + deg y ≠ 0`) both sides vanish for grading reasons
  (`zhuDeg0_bracket_gen_ne`); on the diagonal (`zhuDeg0_bracket_gen_diag`) it *is* `zhu_comm_mod_O`
  combined with the `AMod` multiplicativity `ρ_mul`.  (The bracket is handled through the bilinear
  `VHat.vhb = vhatBracket W (bracketDescends W)`, identified with `⁅·,·⁆` by `vhb_eq_bracket`.)

* `VHat.DLM3.parabolicRepOfAMod U : ParabolicRep W 0 U.carrier` — **the level-0 `ParabolicRep`
  instance**, the deliverable.  Its `deep_zero` is `zhuDeg0_deepPart`; its `vacuum_one` is
  `AMod.ρ_one`.

* `regularAMod W : AMod W` — `A(𝒱)` as a bundled module over itself, with `o(x)·[𝟙] = [x]`
  (`regularAMod_apply_one`).  This is the `U` that step B3 of the `(0,0)` gate feeds into the
  construction; `AMod` carries no finiteness condition, so (unlike `OrdVModule`) it accepts it.

* `VHat.DLM3.indBottom_zhu_equivariant` / `indBarBottom_zhu_equivariant` — the proved bottom map
  `u ↦ [1 ⊗ u]` of `M_0(U)` (and of the defect quotient) is **`A(𝒱)`-equivariant**:
  `o(a)·[1 ⊗ u] = [1 ⊗ [a]·u]` for homogeneous `a`.  This is exactly the upgrade that
  `ZhuVermaAnArchDLM3Level` records as blocked ("DLM3 Proposition 3.1 … is not in the repo, so the
  intertwining cannot yet be upgraded to `A_n(𝒱)`-linearity").

* `VHat.DLM3.indBar_level_zero_AMod` — the main theorem, bundling (1) "the bottom sits in level `0`"
  of the proved `ℤ`-grading `indBarGraded` (`ZhuVermaAnArchDLM3Level`: the levels *span*), (2) the
  `A(𝒱)`-equivariance above, and (3) the exact obstruction `indBarBottom` injective `↔` `U` has a
  separating realization.  Note `indBarWeakModule (parabolicRepOfAMod W U)` is then a genuine weak
  `𝒱`-module attached to *any* `A(𝒱)`-module `U`, unconditionally.

## What is NOT proved (deliberately, and why)

* **No internal direct-sum decomposition of `M_0(U)` is claimed in this file**, and the bottom map
  is *not* claimed injective here.  `ZhuVermaAnArchDLM3Level` records that the levels span
  (`levBar_spanning`); independence of the `levCover` levels of the induced module was later proved
  unconditionally (`levCover_iSupIndep`, `Modules/ZhuVermaAnArchDLM3PBWIndependence.lean`), and
  `indBarBottom_injective_iff` (`ZhuVermaAnArchDLM3Admissible`) shows injectivity of the bottom map
  is *equivalent* to the realization problem, i.e. to DLM3 Theorem 4.1 itself.  Nothing below
  pretends otherwise.
* **`DirectSum.IsInternal` for the level grading of `M_0(U)` is not proved in this file.**
  The grading itself (`VHat.DLM3.levCover`/`levBar`, `ZhuVermaAnArchDLM3Level`) is PBW-free and
  proved, with `levCover_spanning`/`levBar_spanning` and the level shift `actMode_levCover`.
  Independence of the `levCover` levels of the induced module (DLM3's PBW invocation) is the
  unconditional theorem `levCover_iSupIndep`; bottom injectivity follows from the `inducedBottom`
  field of the theorem `VOA.pbw`
  (`voaPBWBottomInjective`).  Nothing in this file depends on either.
* `IndBar` (the repo's defect quotient) is **not** identified with DLM3's `M̄_n(U)`: the repo
  imposes the defect relations for *all* vectors, DLM3 only for `u ∈ U`, so `IndBar` is a priori a
  proper quotient of DLM3's object.

Everything here is `sorry`-free, `pbw`-free and `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`).

## References
DLM3 (`q-alg/9612010v2`) Lemma 2.1(ii)(iii), §3 (3.1)–(3.3), Prop 3.1, §4 (4.1); Zhu, J. Amer.
Math. Soc. **9** (1996) Lemma 2.1.3; Dong–Li–Mason `q-alg/9509005` Lemma 4.2;
`ZhuVermaAnArchResSkew` (`resHom_skew_mod_Onm`, `resFull`), `ZhuVermaAnArchAltVandermonde`
(`cbz_alt_vandermonde`), `ZhuVermaAnArchBottomDefectClose` (`Onm_zero_zero_eq_O`),
`ZhuVermaAnArchDLM3Deg` (`deg`, `parabolic`, `Pn`, `deepPart`), `ZhuVermaAnArchDLM3Induced`
(`ParabolicRep`, `IndMod`, `indRho`, `indBarWeakModule`), `ZhuVermaAnArchDLM3Admissible`
(`indBottom`, `indBarBottom`, `Realization`, `indBarBottom_injective_iff`),
`ZhuVermaAnArchDLM3Level` (`levCover`, `levBar`, `indBarGraded`), `ZhuBijection` (`AMod`),
`ZhuAlgebra` (`zhuMul`, `O`, `A`).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Zhu's Lemma 2.1.3 — the commutator congruence in `A(𝒱)` -/

/-- The Zhu grading generator lies in `O(𝒱)`: `L₋₁w + L₀w = (L₋₁w + L₀w) * 𝟙`. -/
theorem zhuLgen_mem_O (W : VertexOperatorAlgebra 𝒱) (w : 𝒱) :
    W.L (-1) w + W.L 0 w ∈ O W :=
  Submodule.subset_span ⟨w, W.vacuum, (zhuMul_vacuum_right W (W.L (-1) w + W.L 0 w)).symm⟩

/-- **Zhu's Lemma 2.1.3 / DLM3 Lemma 2.1(iii) at `n = 0`.**  For homogeneous `u ∈ 𝒱_K` and
`v ∈ 𝒱_M`,

  `u * v − v * u − Res_z (1+z)^{K−1} Y(u,z)v ∈ O(𝒱)`,

the residue being the honest `ℤ`-indexed `resFull W (K−1) 0 u v = ∑_ℓ C(K−1, ℓ)·u₍ℓ₎v`.

This is the scalar heart of DLM3 Proposition 3.1: it says that `v ↦ [v]` turns the Frenkel–Zhu
bracket `[a(wt a − 1), b(wt b − 1)] = ∑_i C(wt a − 1, i)·(a₍ᵢ₎b)(…)` into the commutator of `A(𝒱)`.

Proof: the proved residue skew relation `resHom_skew_mod_Onm` at `(N, m, P) = (0, 0, 1)` gives
`v * u ≡ Res_z (1+z)^{K−1}/z · Y(u,z)v`, while `u * v = Res_z (1+z)^{K}/z · Y(u,z)v` by definition;
subtracting and applying Pascal `C(K, ℓ+1) − C(K−1, ℓ+1) = C(K−1, ℓ)` leaves exactly the residue. -/
theorem zhu_comm_mod_O (W : VertexOperatorAlgebra 𝒱) {K M : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (hv : v ∈ W.grading (M : ℤ)) :
    zhuMul W u v - zhuMul W v u - resFull W ((K : ℤ) - 1) 0 u v ∈ O W := by
  -- (1) the proved skew relation at `(N, m, P) = (0, 0, 1)`
  have hskew := resHom_skew_mod_Onm W 0 0 hu hv 1
  rw [Onm_zero_zero_eq_O,
    show ((K : ℤ) + 1 - ((0 : ℕ) : ℤ) - 2) = (K : ℤ) - 1 from by push_cast; ring,
    show sgn ((1 : ℤ) + 1) = 1 from by
      rw [sgn, if_pos (by decide : Even ((1 : ℤ) + 1))],
    one_smul, Nat.cast_zero, resHom_zero_one] at hskew
  -- (2) `u * v` is the full residue at exponent `K`
  have huv : zhuMul W u v = resFull W (K : ℤ) 1 u v := by
    have h := resHom_eq_resFull (W := W) (K := K) (s := 0) hu 1 v
    rw [Nat.cast_zero, add_zero, resHom_zero_one] at h
    exact h
  -- (3) Pascal: `resFull K 1 = resFull (K−1) 1 + resFull (K−1) 0`
  have hpas : resFull W (K : ℤ) 1 u v
      = resFull W ((K : ℤ) - 1) 1 u v + resFull W ((K : ℤ) - 1) 0 u v := by
    rw [resFull, resFull, resFull,
      ← finsum_add_distrib (resFull_support_finite W ((K : ℤ) - 1) 1 u v)
        (resFull_support_finite W ((K : ℤ) - 1) 0 u v)]
    refine finsum_congr fun ℓ => ?_
    rw [← add_smul]
    congr 1
    rw [cbz_pascal (K : ℤ) (ℓ + 1), show (ℓ + 1 - 1 : ℤ) = ℓ + 0 from by ring]
  -- (4) assemble
  have hrw : zhuMul W u v - zhuMul W v u - resFull W ((K : ℤ) - 1) 0 u v
      = -(zhuMul W v u - resFull W ((K : ℤ) - 1) 1 u v) := by
    rw [huv, hpas]; abel
  rw [hrw]
  exact Submodule.neg_mem _ hskew

/-! ## The grade projections `π_w : 𝒱 → 𝒱` -/

/-- The grade-`w` component of a vector, as a `ℂ`-linear endomorphism of `𝒱` (chosen through the
internal direct-sum decomposition `W.isInternal`).  Linear companion of `Core.comp`. -/
noncomputable def gradeComp (W : VertexOperatorAlgebra 𝒱) (w : ℤ) : 𝒱 →ₗ[ℂ] 𝒱 :=
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition
  (W.grading w).subtype.comp
    ((DirectSum.component ℂ ℤ (fun i => W.grading i) w).comp
      (DirectSum.decomposeLinearEquiv W.grading).toLinearMap)

theorem gradeComp_coe (W : VertexOperatorAlgebra 𝒱) (w : ℤ) (x : 𝒱) :
    letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition
    gradeComp W w x = ((DirectSum.decompose W.grading x w : W.grading w) : 𝒱) := rfl

/-- The grade-`w` component lands in `𝒱_w`. -/
theorem gradeComp_mem (W : VertexOperatorAlgebra 𝒱) (w : ℤ) (x : 𝒱) :
    gradeComp W w x ∈ W.grading w := by
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition
  exact (DirectSum.decompose W.grading x w).2

/-- On a homogeneous vector of the same grade the projection is the identity. -/
theorem gradeComp_of_mem_same (W : VertexOperatorAlgebra 𝒱) {w : ℤ} {x : 𝒱}
    (hx : x ∈ W.grading w) : gradeComp W w x = x := by
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition
  rw [gradeComp_coe]
  exact DirectSum.decompose_of_mem_same W.grading hx

/-- On a homogeneous vector of a different grade the projection vanishes. -/
theorem gradeComp_of_mem_ne (W : VertexOperatorAlgebra 𝒱) {w w' : ℤ} (h : w ≠ w') {x : 𝒱}
    (hx : x ∈ W.grading w') : gradeComp W w x = 0 := by
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition
  rw [gradeComp_coe]
  exact DirectSum.decompose_of_mem_ne W.grading hx (Ne.symm h)

/-- **`π_{w+1} ∘ L₋₁ = L₋₁ ∘ π_w`** — `L₋₁` raises the grading by one, so it intertwines the
projections.  (Checked on homogeneous vectors and extended by internality of the grading.) -/
theorem gradeComp_Lneg1 (W : VertexOperatorAlgebra 𝒱) (w : ℤ) (x : 𝒱) :
    gradeComp W (w + 1) (W.L (-1) x) = W.L (-1) (gradeComp W w x) := by
  have hx : x ∈ ⨆ k : ℤ, W.grading k := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun x => gradeComp W (w + 1) (W.L (-1) x) = W.L (-1) (gradeComp W w x)) hx
    ?_ ?_ ?_
  · intro k a ha
    by_cases hk : w = k
    · subst hk
      rw [gradeComp_of_mem_same W (L_neg_one_raise W ha), gradeComp_of_mem_same W ha]
    · rw [gradeComp_of_mem_ne W (by omega : w + 1 ≠ k + 1) (L_neg_one_raise W ha),
        gradeComp_of_mem_ne W hk ha, map_zero]
  · simp only [map_zero]
  · intro y z hy hz
    simp only [map_add, hy, hz]

/-! ## The regular `A(𝒱)`-module -/

/-- **`A(𝒱)` as a bundled module over itself** (the *regular* `A(𝒱)`-module).  Its action is the
descended Zhu product `Amul` at the unconditional `zhuRingData_holds`; `ρ_one` is the left unit
`[𝟙]·p = p` and `ρ_mul` is associativity `[u*v]·p = [u]·([v]·p)`.

This is the module the gate's step B3 instantiates: `o(x)·[𝟙] = [x]` (`regularAMod_apply_one`), so
`o(x) = 0` on it forces `[x] = 0`, i.e. `x ∈ O(𝒱)`.  Note `AMod` carries **no** finiteness
condition, so the (infinite-dimensional) regular module is a legitimate object here — unlike
`OrdVModule`, whose `finrank` field blocks this instantiation. -/
noncomputable def regularAMod (W : VertexOperatorAlgebra 𝒱) : AMod W where
  carrier := A W
  ρ := Amul (zhuRingData_holds W)
  ρ_one := by
    refine LinearMap.ext fun p => ?_
    change Amul (zhuRingData_holds W) (mk W W.vacuum) p = p
    rw [Amul_one_left]
  ρ_mul u v := by
    refine LinearMap.ext fun p => ?_
    change Amul (zhuRingData_holds W) (mk W (zhuMul W u v)) p
      = Amul (zhuRingData_holds W) (mk W u) (Amul (zhuRingData_holds W) (mk W v) p)
    rw [← Amul_mk (zhuRingData_holds W) u v, Amul_assoc]

@[simp] theorem regularAMod_carrier (W : VertexOperatorAlgebra 𝒱) :
    (regularAMod W).carrier = A W := rfl

/-- **`o(x)·[𝟙] = [x]` on the regular module** — the reason step B3 of the `(0,0)` gate can read the
class of `x` off its zero mode. -/
theorem regularAMod_apply_one (W : VertexOperatorAlgebra 𝒱) (x : 𝒱) :
    (regularAMod W).ρ (mk W x) (one W) = mk W x := by
  change Amul (zhuRingData_holds W) (mk W x) (mk W W.vacuum) = mk W x
  rw [Amul_one_right]

/-! ## DLM3 Proposition 3.1 at `n = 0`: the map `V̂ → A(𝒱)` -/

namespace VHat

/-- The degree-`0` projection `ℂ[t,t⁻¹] ⊗ 𝒱 → A(𝒱)`, `a(m) ↦ [π_{m+1} a]`, before descending to
`V̂`.  (`π_{m+1} a` is the piece of `a` for which `a(m)` has `V̂`-degree `wt a − m − 1 = 0`.) -/
noncomputable def zhuLoop (W : VertexOperatorAlgebra 𝒱) : VLoop 𝒱 →ₗ[ℂ] A W :=
  Finsupp.lsum ℂ (fun m : ℤ => (_root_.VOA.mk W).comp (gradeComp W (m + 1)))

theorem zhuLoop_single (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (a : 𝒱) :
    zhuLoop W (Finsupp.single m a) = _root_.VOA.mk W (gradeComp W (m + 1) a) := by
  rw [zhuLoop, Finsupp.lsum_single]
  rfl

/-- `zhuLoop` kills the derivative relations `(L₋₁a)(m) + m·a(m−1)`: their image is the Zhu grading
generator `L₋₁b + L₀b` of `O(𝒱)` at `b = π_m a`. -/
theorem zhuLoop_deriv (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (m : ℤ) :
    zhuLoop W (Finsupp.single m (W.L (-1) a) + (m : ℂ) • Finsupp.single (m - 1) a) = 0 := by
  rw [map_add, map_smul, zhuLoop_single, zhuLoop_single,
    show (m - 1 + 1 : ℤ) = m from by ring]
  set b : 𝒱 := gradeComp W m a with hb
  have hbm : b ∈ W.grading m := gradeComp_mem W m a
  have hL : gradeComp W (m + 1) (W.L (-1) a) = W.L (-1) b := gradeComp_Lneg1 W m a
  rw [hL, ← map_smul, ← map_add, ← W.L_zero_grading b hbm]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (zhuLgen_mem_O W b)

/-- **DLM3 Proposition 3.1 at `n = 0`, as a map on all of `V̂`.**  The `ℂ`-linear map
`V̂ →ₗ[ℂ] A(𝒱)` sending the loop generator `a(m)` to `[π_{m+1} a]`.  On the degree-`0` part it is
DLM3's `o(a) = a(wt a − 1) ↦ a + O(𝒱)`; it annihilates every other graded piece. -/
noncomputable def zhuDeg0 (W : VertexOperatorAlgebra 𝒱) : VHatCarrier W →ₗ[ℂ] A W :=
  Submodule.liftQ (loopDerivSubmodule W) (zhuLoop W) (by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨a, m, rfl⟩
    exact zhuLoop_deriv W a m)

theorem zhuDeg0_gen (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (m : ℤ) :
    zhuDeg0 W (gen W a m) = _root_.VOA.mk W (gradeComp W (m + 1) a) := by
  rw [zhuDeg0, gen, mk, show (loopDerivSubmodule W).mkQ (Finsupp.single m a)
      = Submodule.Quotient.mk (Finsupp.single m a) from rfl,
    Submodule.liftQ_apply, zhuLoop_single]

/-- On a degree-`0` generator `a(wt a − 1)` the map is DLM3's `o(a) ↦ [a]`. -/
theorem zhuDeg0_gen_deg_zero (W : VertexOperatorAlgebra 𝒱) {w m : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading w) (hd : w - m - 1 = 0) :
    zhuDeg0 W (gen W a m) = _root_.VOA.mk W a := by
  rw [zhuDeg0_gen, gradeComp_of_mem_same W (by rwa [show (m + 1 : ℤ) = w from by omega])]

/-- On a generator of nonzero `V̂`-degree the map vanishes. -/
theorem zhuDeg0_gen_of_ne (W : VertexOperatorAlgebra 𝒱) {w m : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading w) (hd : w - m - 1 ≠ 0) : zhuDeg0 W (gen W a m) = 0 := by
  rw [zhuDeg0_gen, gradeComp_of_mem_ne W (by omega : m + 1 ≠ w) ha, map_zero]

/-- `zhuDeg0` kills every graded piece of nonzero degree. -/
theorem zhuDeg0_degSpan (W : VertexOperatorAlgebra 𝒱) {S : Set ℤ} (hS : (0 : ℤ) ∉ S)
    {x : VHatCarrier W} (hx : x ∈ degSpan W S) : zhuDeg0 W x = 0 := by
  refine Submodule.span_induction (p := fun x _ => zhuDeg0 W x = 0) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨w, m, a, ha, hmem, rfl⟩
    exact zhuDeg0_gen_of_ne W ha (fun h => hS (h ▸ hmem))
  · exact map_zero _
  · intro x y _ _ hx' hy'; rw [map_add, hx', hy', add_zero]
  · intro c x _ hx'; rw [map_smul, hx', smul_zero]

/-- **`zhuDeg0` annihilates the deep part `⨁_{p>n} V̂(−p)`** — DLM3's "letting `V̂(−p)` act
trivially" (4.1). -/
theorem zhuDeg0_deepPart (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {x : VHatCarrier W}
    (hx : x ∈ deepPart W n) : zhuDeg0 W x = 0 :=
  zhuDeg0_degSpan W (by
    simp only [deepSet, Set.mem_setOf_eq]
    omega) hx

/-! ## The Lie-morphism property of `zhuDeg0` on the parabolic `P₀` -/

/-- The parabolic degree set at `n = 0` is the set of nonpositive degrees. -/
theorem parabolicSet_zero_le {d : ℤ} (h : d ∈ parabolicSet 0) : d ≤ 0 := by
  rcases h with h | h <;> omega

/-- The descended `V̂`-bracket as a genuine `ℂ`-**bilinear map** (`vhatBracket` at the proved
descent obligation).  Working with this rather than with `⁅·,·⁆` keeps bilinearity available as
`map_add`/`map_smul`; `bracket_eq` identifies the two. -/
noncomputable def vhb (W : VertexOperatorAlgebra 𝒱) :
    VHatCarrier W →ₗ[ℂ] VHatCarrier W →ₗ[ℂ] VHatCarrier W :=
  vhatBracket W (bracketDescends W)

theorem vhb_eq_bracket (W : VertexOperatorAlgebra 𝒱) (x y : VHatCarrier W) :
    vhb W x y = ⁅x, y⁆ := (bracket_eq W x y).symm

theorem vhb_gen (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) (m k : ℤ) :
    vhb W (gen W a m) (gen W b k)
      = ∑ᶠ i : ℕ, (gBinom m i) • gen W (W.smul a i b) (m + k - i) :=
  vhatBracket_gen W (bracketDescends W) a b m k

/-- **Off-diagonal vanishing.**  Every OPE term of `⁅a(m), b(k)⁆` is a loop generator of `V̂`-degree
`(wt a − m − 1) + (wt b − k − 1)`, so `zhuDeg0` kills the whole bracket as soon as that sum is
nonzero. -/
theorem zhuDeg0_bracket_gen_ne (W : VertexOperatorAlgebra 𝒱) {wa wb m k : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading wa) (hb : b ∈ W.grading wb)
    (hd : wa - m - 1 + (wb - k - 1) ≠ 0) :
    zhuDeg0 W (vhb W (gen W a m) (gen W b k)) = 0 := by
  rw [vhb_gen, map_finsum (zhuDeg0 W) (genOPE_support_finite W a b m k)]
  have hterm : ∀ i : ℕ,
      zhuDeg0 W ((gBinom m i) • gen W (W.smul a i b) (m + k - i)) = 0 := by
    intro i
    rw [map_smul, zhuDeg0_gen_of_ne W (W.toPreVertexAlgebra.smul_mem_grading ha hb (i : ℤ))
      (by omega), smul_zero]
  rw [finsum_congr hterm, finsum_zero]

/-- **The diagonal case: DLM3 Proposition 3.1's bracket formula.**  On two degree-`0` generators
the Frenkel–Zhu bracket `⁅a(wt a − 1), b(wt b − 1)⁆ = ∑_i C(wt a − 1, i)·(a₍ᵢ₎b)(…)` maps to the
class of the residue `Res_z (1+z)^{wt a − 1} Y(a,z)b` (DLM3 (4.9)/(4.10)). -/
theorem zhuDeg0_bracket_gen_diag (W : VertexOperatorAlgebra 𝒱) {wa wb : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading wa) (hb : b ∈ W.grading wb) :
    zhuDeg0 W (vhb W (gen W a (wa - 1)) (gen W b (wb - 1)))
      = _root_.VOA.mk W (resFull W (wa - 1) 0 a b) := by
  have hfin : (Function.support fun i : ℕ =>
      (gBinom (wa - 1) i) • W.smul a (i : ℤ) b).Finite := by
    obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
    refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.mem_Iio]
    by_contra hcon
    rw [not_lt] at hcon
    exact hi (by
      rw [hNz (i : ℤ) (le_trans (Int.self_le_toNat Nz) (by exact_mod_cast hcon)), smul_zero])
  rw [vhb_gen, map_finsum (zhuDeg0 W) (genOPE_support_finite W a b (wa - 1) (wb - 1))]
  have hterm : ∀ i : ℕ,
      zhuDeg0 W ((gBinom (wa - 1) i) • gen W (W.smul a i b) (wa - 1 + (wb - 1) - i))
        = _root_.VOA.mk W ((gBinom (wa - 1) i) • W.smul a (i : ℤ) b) := by
    intro i
    rw [map_smul, zhuDeg0_gen_deg_zero W (W.toPreVertexAlgebra.smul_mem_grading ha hb (i : ℤ))
      (by ring), map_smul]
  rw [finsum_congr hterm, ← map_finsum (_root_.VOA.mk W) hfin]
  congr 1
  rw [resFull]
  refine finsum_nat_to_int _ _ ?_ ?_
  · intro p hp
    have hc : cbz (wa - 1) (p + 0) = 0 := cbz_apply_neg _ (by omega)
    rw [hc, zero_smul]
  · intro j
    have hc : cbz (wa - 1) ((j : ℤ) + 0) = gBinom (wa - 1) j := by
      rw [show ((j : ℤ) + 0) = (j : ℤ) from by ring, cbz_apply_nonneg _ (by omega)]
      simp
    rw [hc]

/-- **The generator-level Lie morphism property.**  For two parabolic generators (degrees `≤ 0`) the
image of the bracket under `ρ ∘ zhuDeg0` is the commutator of the images.  Off the diagonal both
sides vanish; on the diagonal it is Zhu's Lemma 2.1.3 (`zhu_comm_mod_O`) together with the `AMod`
multiplicativity `ρ_mul`. -/
theorem zhuDeg0_bracket_gen_gen (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {wa wb m k : ℤ}
    {a b : 𝒱} (ha : a ∈ W.grading wa) (hb : b ∈ W.grading wb)
    (hda : wa - m - 1 ≤ 0) (hdb : wb - k - 1 ≤ 0) :
    U.ρ (zhuDeg0 W (vhb W (gen W a m) (gen W b k)))
      = U.ρ (zhuDeg0 W (gen W a m)) * U.ρ (zhuDeg0 W (gen W b k))
        - U.ρ (zhuDeg0 W (gen W b k)) * U.ρ (zhuDeg0 W (gen W a m)) := by
  by_cases hza : wa - m - 1 = 0
  · by_cases hzb : wb - k - 1 = 0
    · have hm : m = wa - 1 := by omega
      have hk : k = wb - 1 := by omega
      subst hm; subst hk
      rcases lt_or_ge wa 0 with hlt | hge
      · rw [W.positivity wa hlt, Submodule.mem_bot] at ha
        subst ha; simp
      rcases lt_or_ge wb 0 with hlt' | hge'
      · rw [W.positivity wb hlt', Submodule.mem_bot] at hb
        subst hb; simp
      obtain ⟨Ka, rfl⟩ : ∃ Ka : ℕ, wa = (Ka : ℤ) := ⟨wa.toNat, by omega⟩
      obtain ⟨Kb, rfl⟩ : ∃ Kb : ℕ, wb = (Kb : ℤ) := ⟨wb.toNat, by omega⟩
      rw [zhuDeg0_bracket_gen_diag W ha hb, zhuDeg0_gen_deg_zero W ha (by ring),
        zhuDeg0_gen_deg_zero W hb (by ring)]
      have h0 : _root_.VOA.mk W
          (zhuMul W a b - zhuMul W b a - resFull W ((Ka : ℤ) - 1) 0 a b) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr (zhu_comm_mod_O W ha hb)
      rw [map_sub, map_sub, sub_eq_zero] at h0
      rw [← h0, map_sub, U.ρ_mul a b, U.ρ_mul b a]
    · rw [zhuDeg0_gen_of_ne W hb hzb, zhuDeg0_bracket_gen_ne W ha hb (by omega)]
      simp
  · rw [zhuDeg0_gen_of_ne W ha hza, zhuDeg0_bracket_gen_ne W ha hb (by omega)]
    simp

/-- **DLM3 Proposition 3.1 at `n = 0`, the Lie-morphism property.**  For `x, y` in the parabolic
`P₀ = ⨁_{d ≤ 0} V̂(d)` and any bundled `A(𝒱)`-module `U`,

  `ρ(zhuDeg0 ⁅x,y⁆) = ρ(zhuDeg0 x)·ρ(zhuDeg0 y) − ρ(zhuDeg0 y)·ρ(zhuDeg0 x)`.

Both sides are `ℂ`-bilinear, so this reduces by a double span induction to
`zhuDeg0_bracket_gen_gen`. -/
theorem zhuDeg0_bracket_parabolic (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    {x y : VHatCarrier W} (hx : x ∈ parabolic W 0) (hy : y ∈ parabolic W 0) :
    U.ρ (zhuDeg0 W (vhb W x y))
      = U.ρ (zhuDeg0 W x) * U.ρ (zhuDeg0 W y) - U.ρ (zhuDeg0 W y) * U.ρ (zhuDeg0 W x) := by
  have hgen : ∀ (wa m : ℤ) (a : 𝒱), a ∈ W.grading wa → wa - m - 1 ≤ 0 →
      ∀ z ∈ parabolic W 0,
        U.ρ (zhuDeg0 W (vhb W (gen W a m) z))
          = U.ρ (zhuDeg0 W (gen W a m)) * U.ρ (zhuDeg0 W z)
            - U.ρ (zhuDeg0 W z) * U.ρ (zhuDeg0 W (gen W a m)) := by
    intro wa m a ha hda z hz
    refine Submodule.span_induction
      (p := fun z _ => U.ρ (zhuDeg0 W (vhb W (gen W a m) z))
        = U.ρ (zhuDeg0 W (gen W a m)) * U.ρ (zhuDeg0 W z)
          - U.ρ (zhuDeg0 W z) * U.ρ (zhuDeg0 W (gen W a m))) ?_ ?_ ?_ ?_ hz
    · rintro z ⟨wb, k, b, hb, hdb, rfl⟩
      exact zhuDeg0_bracket_gen_gen W U ha hb hda (parabolicSet_zero_le hdb)
    · simp
    · intro z₁ z₂ _ _ h₁ h₂
      simp only [map_add, mul_add, add_mul]
      rw [h₁, h₂]
      abel
    · intro c z₁ _ h₁
      simp only [map_smul, smul_mul_assoc, mul_smul_comm]
      rw [h₁, smul_sub]
  refine Submodule.span_induction
    (p := fun x _ => U.ρ (zhuDeg0 W (vhb W x y))
      = U.ρ (zhuDeg0 W x) * U.ρ (zhuDeg0 W y) - U.ρ (zhuDeg0 W y) * U.ρ (zhuDeg0 W x))
    ?_ ?_ ?_ ?_ hx
  · rintro x ⟨wa, m, a, ha, hda, rfl⟩
    exact hgen wa m a ha (parabolicSet_zero_le hda) y hy
  · simp
  · intro x₁ x₂ _ _ h₁ h₂
    simp only [map_add, LinearMap.add_apply, mul_add, add_mul]
    rw [h₁, h₂]
    abel
  · intro c x₁ _ h₁
    simp only [map_smul, LinearMap.smul_apply, smul_mul_assoc, mul_smul_comm]
    rw [h₁, smul_sub]

namespace DLM3

/-- **The level-0 `ParabolicRep` of a bundled `A(𝒱)`-module** — DLM3 (4.1)'s input datum, at last
unconditional at `n = 0`.  The `P₀`-action is `g ↦ ρ(zhuDeg0 g)`; its three obligations are

* the Lie-morphism property — `zhuDeg0_bracket_parabolic` (DLM3 Prop 3.1, resting on Zhu's
  Lemma 2.1.3 `zhu_comm_mod_O`);
* `deep_zero` — `zhuDeg0_deepPart` ("letting `V̂(−p)` act trivially");
* `vacuum_one` — `AMod.ρ_one`, since `𝟙(−1)` has degree `0` and `zhuDeg0 (𝟙(−1)) = [𝟙]`. -/
noncomputable def parabolicRepOfAMod (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    ParabolicRep W 0 U.carrier where
  act :=
    { toFun := fun g => U.ρ (zhuDeg0 W (g : VHatCarrier W))
      map_add' := fun g h => by
        change U.ρ (zhuDeg0 W ((g : VHatCarrier W) + (h : VHatCarrier W))) = _
        rw [map_add, map_add]
      map_smul' := fun c g => by
        change U.ρ (zhuDeg0 W (c • (g : VHatCarrier W))) = _
        rw [map_smul, map_smul]
        rfl
      map_lie' := fun {g h} => by
        change U.ρ (zhuDeg0 W ⁅(g : VHatCarrier W), (h : VHatCarrier W)⁆) = _
        rw [Ring.lie_def, ← vhb_eq_bracket]
        exact zhuDeg0_bracket_parabolic W U ((mem_Pn W 0 _).mp g.2) ((mem_Pn W 0 _).mp h.2) }
  deep_zero := fun g hg => by
    change U.ρ (zhuDeg0 W (g : VHatCarrier W)) = 0
    rw [zhuDeg0_deepPart W 0 hg, map_zero]
  vacuum_one := by
    change U.ρ (zhuDeg0 W (gen W W.vacuum (-1))) = 1
    rw [zhuDeg0_gen_deg_zero W W.vacuum_mem (by ring)]
    exact U.ρ_one

@[simp] theorem parabolicRepOfAMod_act (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (g : Pn W 0) (u : U.carrier) :
    (parabolicRepOfAMod W U).act g u = U.ρ (zhuDeg0 W (g : VHatCarrier W)) u := rfl

/-- **`o(a)` acts on the bottom of `M_0(U)` as `[a] ∈ A(𝒱)` does on `U`.**  This is DLM3's
`o(a)·[1 ⊗ u] = [1 ⊗ a·u]` — the genuine `A(𝒱)`-equivariance of the bottom map at `n = 0`, i.e. the
upgrade that `ZhuVermaAnArchDLM3Level` records as blocked on DLM3 Proposition 3.1. -/
theorem indBottom_zhu_equivariant (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {w : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading w) (u : U.carrier) :
    indBottom (parabolicRepOfAMod W U) (U.ρ (_root_.VOA.mk W a) u)
      = (indRho (parabolicRepOfAMod W U)).actMode a (w - 1)
          (indBottom (parabolicRepOfAMod W U) u) := by
  have hmem : gen W a (w - 1) ∈ parabolic W 0 :=
    gen_mem_parabolic_of_deg_zero W 0 ha (by ring)
  have h := indBottom_equivariant (parabolicRepOfAMod W U) (⟨gen W a (w - 1), hmem⟩ : Pn W 0) u
  rw [parabolicRepOfAMod_act, zhuDeg0_gen_deg_zero W ha (by ring)] at h
  exact h

/-- The same statement on the defect quotient `IndBar` (the repo's `M̄`; **not** identified with
DLM3's `M̄_n(U)`, see the module docstring). -/
theorem indBarBottom_zhu_equivariant (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {w : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading w) (u : U.carrier) :
    indBarBottom (parabolicRepOfAMod W U) (U.ρ (_root_.VOA.mk W a) u)
      = (indBarRho (parabolicRepOfAMod W U)).actMode a (w - 1)
          (indBarBottom (parabolicRepOfAMod W U) u) := by
  have hmem : gen W a (w - 1) ∈ parabolic W 0 :=
    gen_mem_parabolic_of_deg_zero W 0 ha (by ring)
  have h := indBarBottom_equivariant (parabolicRepOfAMod W U) (⟨gen W a (w - 1), hmem⟩ : Pn W 0) u
  rw [parabolicRepOfAMod_act, zhuDeg0_gen_deg_zero W ha (by ring)] at h
  exact h

/-- **The level-0 main theorem.**  For a bundled `A(𝒱)`-module `U`:

1. the bottom map `u ↦ [1 ⊗ u]` of `M̄_0(U)` lands in **level `0`** of the `ℤ`-grading
   (`indBarGraded`, whose levels *span*; directness is not claimed here; for `levCover` it is `levCover_iSupIndep`);
2. it is **`A(𝒱)`-equivariant**: `o(a)·[1 ⊗ u] = [1 ⊗ [a]·u]` for every homogeneous `a` — the new
   content, unlocked by `parabolicRepOfAMod` (DLM3 Prop 3.1 at `n = 0`);
3. its **injectivity is exactly** the existence of a separating realization of `U`
   (`indBarBottom_injective_iff`), i.e. DLM3 Theorem 4.1 at `n = 0`.  It is **not** proved here.

Together with `indBarWeakModule (parabolicRepOfAMod W U)` (a genuine weak `𝒱`-module) this is
everything DLM3 §4 delivers at `n = 0` *before* their `U*`/radical pairing argument. -/
theorem indBar_level_zero_AMod (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    (∀ u : U.carrier, indBarBottom (parabolicRepOfAMod W U) u
        ∈ (indBarGraded (parabolicRepOfAMod W U)).lev ((0 : ℕ) : ℤ)) ∧
      (∀ {w : ℤ} {a : 𝒱}, a ∈ W.grading w → ∀ u : U.carrier,
        indBarBottom (parabolicRepOfAMod W U) (U.ρ (_root_.VOA.mk W a) u)
          = (indBarRho (parabolicRepOfAMod W U)).actMode a (w - 1)
              (indBarBottom (parabolicRepOfAMod W U) u)) ∧
      (Function.Injective (indBarBottom (parabolicRepOfAMod W U))
        ↔ ∃ R : Realization W 0 U.carrier (parabolicRepOfAMod W U), R.Separates) :=
  ⟨indBarBottom_mem_levBar (parabolicRepOfAMod W U),
   fun ha u => indBarBottom_zhu_equivariant W U ha u,
   indBarBottom_injective_iff (parabolicRepOfAMod W U)⟩

end DLM3

end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
