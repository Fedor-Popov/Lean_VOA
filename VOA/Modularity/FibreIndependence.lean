/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.CharIndependenceAMod
import VOA.Modularity.BottomCharacter
import VOA.Modularity.QEvalLinearity
import VOA.Modularity.SqWeightNat
import VOA.Modularity.SubexpClosure
import VOA.Modularity.TEigenInjective

/-!
# `FibreIndependent` — residual (d)

Within one `T`-eigenvalue class the trace functions of pairwise non-isomorphic irreducible modules
are linearly independent.  This is the `A(𝒱)`-character-separation half of Zhu Thm 5.3.3, and by
`traceIndependent_of_fibreIndependent` it is *all* that `TraceIndependent` needs — so it discharges
the `hfib` hypothesis of `Modularity.SqAmbientRank.zhu_modularity_of_slashRepresentable`.

## The argument

Suppose a combination vanishes but some coefficient does not; let `S` be the support.  Inside a
`T`-eigenvalue class the conformal weights differ by **integers** (`tEigen_eq_iff`), so all the
trace functions are `q`-series over one `ℤ`-coset.  Rebase them all about the **minimal** weight
`e₀` in `S` (`qEvalAt_shift`, legitimate because `OnePointSupported` kills the coefficients below
each module's own weight, with `qSummableAt_of_lower` supplying the side condition).  The
combination is then a single `q`-series vanishing on all of `ℍ`, so its **leading** coefficient
vanishes (`leading_coeff_eq_zero_of_qEvalAt_imAxis_eq_zero`).  By `torusOnePoint_at_bottom` that
leading coefficient is a combination of the **bottom characters** of exactly the minimal-weight
members; `sqWeightSpace_nat_spans_top` extends it from homogeneous `v` to all `v`; and
`exists_vector_trace_separating` then forces a minimal-weight coefficient to vanish — contradicting
that it lies in the support.

⚠ **No peeling induction is needed.**  One round already produces a `j₀ ∈ S` with `c j₀ = 0`, which
contradicts `S`'s definition outright; there is no need to drop the minimal stratum and recurse.

⚠ `hsep` is carried explicitly, as it must be: `tEigen`-injectivity is **false in general** (two
non-isomorphic irreducibles may share a conformal weight), which is exactly why `FibreIndependent`
is stated fibrewise.

## Main results

* `bottomChar` — the bottom character as a `ℂ`-linear functional on `𝒱`;
* `fibreIndependent_of_bottomSeparation`;
* `traceIndependent_of_bottomSeparation` — hence `TraceIndependent`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Named hypotheses, all displayed: `hcw`, `hgr`,
`hsimp` (simplicity of the bottoms), `hsep` (pairwise non-isomorphy at equal conformal weight).
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- The **bottom character** of a bundled `A(𝒱)`-module, as a `ℂ`-linear functional on `𝒱`. -/
noncomputable def bottomChar (U : AMod W) : 𝒱 →ₗ[ℂ] ℂ :=
  (LinearMap.trace ℂ U.carrier).comp (U.ρ.comp (mk W))

@[simp] theorem bottomChar_apply (U : AMod W) (v : 𝒱) :
    bottomChar U v = LinearMap.trace ℂ U.carrier (U.ρ (mk W v)) := rfl

/-- The `ℕ`-indexed spanning, in the pointwise form this file needs (the `ℂ`-valued codomain lives
in `Type 0`, so the universe-`u` form of `eq_zero_of_forall_sqWeightSpace_nat` does not apply). -/
theorem eq_zero_of_forall_sqWeightSpace_nat_C (W : VertexOperatorAlgebra 𝒱) (f : 𝒱 →ₗ[ℂ] ℂ)
    (hf : ∀ (m : ℕ), ∀ v ∈ sqWeightSpace W ((m : ℕ) : ℂ), f v = 0) (x : 𝒱) : f x = 0 := by
  have hx : x ∈ (⨆ m : ℕ, sqWeightSpace W ((m : ℕ) : ℂ)) := by
    rw [sqWeightSpace_nat_spans_top]; trivial
  refine Submodule.iSup_induction (fun m : ℕ => sqWeightSpace W ((m : ℕ) : ℂ))
    (motive := fun y => f y = 0) hx ?_ ?_ ?_
  · intro m v hv; exact hf m v hv
  · exact map_zero f
  · intro a b ha hb; rw [map_add, ha, hb, add_zero]

section Fibre

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1600000 in
/-- **Residual (d): `FibreIndependent`.** -/
theorem fibreIndependent_of_bottomSeparation (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hsimp : ∀ j, IsSimpleAMod (lowestAMod (hcw j).2))
    (hsep : ∀ j k : ι, j ≠ k → h j = h k →
      IsEmpty (AModEquiv W (lowestAMod (hcw j).2) (lowestAMod (hcw k).2))) :
    FibreIndependent Mfam h := by
  classical
  intro i c hc
  set F : Finset ι := Finset.univ.filter (fun j => tEigen W h j = tEigen W h i) with hFdef
  by_contra hcon
  push_neg at hcon
  obtain ⟨j₁, hj₁F, hj₁c⟩ := hcon
  set S : Finset ι := F.filter (fun j => c j ≠ 0) with hSdef
  have hj₁S : j₁ ∈ S := Finset.mem_filter.mpr ⟨hj₁F, hj₁c⟩
  have hSne : S.Nonempty := ⟨j₁, hj₁S⟩
  have hSF : S ⊆ F := Finset.filter_subset _ _
  -- integer offsets inside the fibre
  have hoffex : ∀ j ∈ F, ∃ m : ℤ, h j - h i = (m : ℂ) := fun j hj =>
    (tEigen_eq_iff h j i).mp (Finset.mem_filter.mp hj).2
  choose! off hoff using hoffex
  set m₀ : ℤ := S.inf' hSne off with hm₀
  obtain ⟨j₀, hj₀S, hj₀eq⟩ := S.exists_mem_eq_inf' hSne off
  set e₀ : ℂ := (h i - W.centralCharge / 24) + (m₀ : ℂ) with he₀
  -- shifts
  set kk : ι → ℕ := fun j => (off j - m₀).toNat with hkk
  have hoffge : ∀ j ∈ S, m₀ ≤ off j := fun j hj => Finset.inf'_le _ hj
  have hdeq : ∀ j ∈ S, h j - W.centralCharge / 24 = e₀ + ((kk j : ℕ) : ℂ) := by
    intro j hj
    have h1 : h j - h i = ((off j : ℤ) : ℂ) := hoff j (hSF hj)
    have h2 : ((kk j : ℕ) : ℂ) = ((off j - m₀ : ℤ) : ℂ) := by
      rw [hkk]
      have hge := hoffge j hj
      exact_mod_cast congrArg (fun z : ℤ => (z : ℂ))
        (Int.toNat_of_nonneg (by omega : 0 ≤ off j - m₀))
    rw [he₀, h2]
    push_cast
    linear_combination h1
  -- supports and summability
  have hsupp : ∀ j : ι, OnePointSupported (Mfam j).isMod (h j - W.centralCharge / 24) :=
    fun j => onePointSupported_of_hasConformalWeight (Mfam j).isMod (hcw j)
  have hvan : ∀ j ∈ S, ∀ (v : 𝒱) (s : ℕ), s < kk j →
      torusOnePoint (Mfam j).isMod v (e₀ + (s : ℂ)) = 0 := by
    intro j hj v s hs
    have := hsupp j v ((s : ℤ) - (kk j : ℤ)) (by omega)
    rw [hdeq j hj] at this
    have hcast : e₀ + ((kk j : ℕ) : ℂ) + (((s : ℤ) - (kk j : ℤ) : ℤ) : ℂ) = e₀ + (s : ℂ) := by
      push_cast; ring
    rwa [hcast] at this
  have hsumd : ∀ (j : ι) (v : 𝒱) (τ : UpperHalfPlane),
      QSummableAt (torusOnePoint (Mfam j).isMod v) (h j - W.centralCharge / 24) τ :=
    fun j v τ => qSummableAt_of_subexponential _ _ (hgr j v) τ
  have hsum0 : ∀ j ∈ S, ∀ (v : 𝒱) (τ : UpperHalfPlane),
      QSummableAt (torusOnePoint (Mfam j).isMod v) e₀ τ := by
    intro j hj v τ
    refine qSummableAt_of_lower _ e₀ (kk j) τ ?_
    rw [← hdeq j hj]
    exact hsumd j v τ
  -- rebased subexponentiality
  have hsubE : ∀ j ∈ S, ∀ v : 𝒱,
      Subexponential (fun n : ℕ => ‖torusOnePoint (Mfam j).isMod v (e₀ + (n : ℂ))‖) := by
    intro j hj v
    refine Subexponential.of_shift (kk j) ?_
    have hcong : (fun n : ℕ => ‖torusOnePoint (Mfam j).isMod v (e₀ + ((n + kk j : ℕ) : ℂ))‖)
        = fun n : ℕ => ‖torusOnePoint (Mfam j).isMod v
            (h j - W.centralCharge / 24 + (n : ℂ))‖ := by
      funext n
      rw [hdeq j hj]
      congr 2
      push_cast; ring
    rw [hcong]
    exact hgr j v
  -- the rebased trace functions agree with the originals
  have hrebase : ∀ j ∈ S, ∀ (v : 𝒱) (τ : UpperHalfPlane),
      qEvalAt (torusOnePoint (Mfam j).isMod v) e₀ τ = traceFun Mfam h j v τ := by
    intro j hj v τ
    rw [traceFun, hdeq j hj]
    exact qEvalAt_shift _ e₀ (kk j) τ (hsum0 j hj v τ) (fun s hs => hvan j hj v s hs)
  -- Step 2–3: the leading coefficient vanishes
  set S₀ : Finset ι := S.filter (fun j => off j = m₀) with hS₀
  have hj₀S₀ : j₀ ∈ S₀ := Finset.mem_filter.mpr ⟨hj₀S, by rw [hm₀, hj₀eq]⟩
  have hstep : ∀ (n : ℕ) (v : 𝒱), v ∈ sqWeightSpace W ((n : ℕ) : ℂ) →
      ∑ j ∈ S₀, c j * bottomChar (lowestAMod (hcw j).2) v = 0 := by
    intro n v hv
    -- the combined series
    have hzero : ∀ (t : ℝ) (ht : 0 < t),
        qEvalAt (fun e => ∑ j ∈ S, c j * torusOnePoint (Mfam j).isMod v e) e₀ (imAxis t ht) = 0 := by
      intro t ht
      rw [qEvalAt_finsetSum S (fun j => torusOnePoint (Mfam j).isMod v) c e₀ _
        (fun j hj => hsum0 j hj v _)]
      have hcongr : ∀ j ∈ S, c j * qEvalAt (torusOnePoint (Mfam j).isMod v) e₀ (imAxis t ht)
          = c j * traceFun Mfam h j v (imAxis t ht) := by
        intro j hj; rw [hrebase j hj v]
      rw [Finset.sum_congr rfl hcongr]
      have hFS : ∑ j ∈ F, c j * traceFun Mfam h j v (imAxis t ht)
          = ∑ j ∈ S, c j * traceFun Mfam h j v (imAxis t ht) := by
        refine (Finset.sum_subset hSF ?_).symm
        intro j hjF hjS
        have : c j = 0 := by
          by_contra hcj
          exact hjS (Finset.mem_filter.mpr ⟨hjF, hcj⟩)
        rw [this, zero_mul]
      rw [← hFS]
      exact hc n v hv (imAxis t ht)
    have hsubtot : Subexponential
        (fun n : ℕ => ‖(fun e => ∑ j ∈ S, c j * torusOnePoint (Mfam j).isMod v e)
          (e₀ + (n : ℂ))‖) := by
      refine Subexponential.of_le (b := fun n : ℕ => ∑ j ∈ S,
        ‖c j‖ * ‖torusOnePoint (Mfam j).isMod v (e₀ + (n : ℂ))‖) (fun n => ?_) ?_
      · refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
        exact Finset.sum_congr rfl (fun j _ => norm_mul _ _)
      · exact Subexponential.finsetSum S _
          (fun j hj => Subexponential.const_mul (hsubE j hj v) (norm_nonneg _))
    have hlead := leading_coeff_eq_zero_of_qEvalAt_imAxis_eq_zero _ e₀ hsubtot hzero
    -- identify the leading coefficient
    have hS₀S : S₀ ⊆ S := Finset.filter_subset _ _
    have hvanish : ∀ j ∈ S, j ∉ S₀ →
        c j * torusOnePoint (Mfam j).isMod v e₀ = 0 := by
      intro j hjS hjS₀
      have hne : off j ≠ m₀ := by
        by_contra hcj
        exact hjS₀ (Finset.mem_filter.mpr ⟨hjS, hcj⟩)
      have hge := hoffge j hjS
      have hpos : 0 < kk j := by
        have h1 : 0 < off j - m₀ := by omega
        show 0 < (off j - m₀).toNat
        omega
      have hz := hsupp j v (-(kk j : ℤ)) (by omega)
      rw [hdeq j hjS] at hz
      have hcast : e₀ + ((kk j : ℕ) : ℂ) + ((-(kk j : ℤ) : ℤ) : ℂ) = e₀ := by
        push_cast; ring
      rw [hcast] at hz
      rw [hz, mul_zero]
    have hstep1 : ∑ j ∈ S₀, c j * torusOnePoint (Mfam j).isMod v e₀
        = ∑ j ∈ S, c j * torusOnePoint (Mfam j).isMod v e₀ :=
      Finset.sum_subset hS₀S hvanish
    have hstep2 : ∑ j ∈ S₀, c j * torusOnePoint (Mfam j).isMod v e₀
        = ∑ j ∈ S₀, c j * bottomChar (lowestAMod (hcw j).2) v := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjS : j ∈ S := hS₀S hj
      have hoff0 : off j = m₀ := (Finset.mem_filter.mp hj).2
      have hk0 : kk j = 0 := by
        show (off j - m₀).toNat = 0
        omega
      have hde : h j - W.centralCharge / 24 = e₀ := by
        rw [hdeq j hjS, hk0]; simp
      congr 1
      rw [← hde]
      exact torusOnePoint_at_bottom_lowestAMod (Mfam j).isMod (hcw j).2 v
    rw [← hstep2, hstep1]
    exact hlead
  -- Step 4: separate
  have hall : ∀ v : 𝒱, ∑ j ∈ S₀, c j * bottomChar (lowestAMod (hcw j).2) v = 0 := by
    intro v
    have hlin : ∀ w : 𝒱, (∑ j ∈ S₀, c j • bottomChar (lowestAMod (hcw j).2)) w
        = ∑ j ∈ S₀, c j * bottomChar (lowestAMod (hcw j).2) w := by
      intro w
      rw [LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun j _ => rfl
    rw [← hlin v]
    refine eq_zero_of_forall_sqWeightSpace_nat_C W _ (fun m w hw => ?_) v
    rw [hlin w]
    exact hstep m w hw
  -- index `S₀` by `Fin`
  set r : ℕ := S₀.card with hr
  set ee : {x // x ∈ S₀} ≃ Fin r := S₀.equivFin with hee
  set U : Fin r → AMod W := fun k => lowestAMod (hcw ((ee.symm k : {x // x ∈ S₀}) : ι)).2 with hU
  have hfdU : ∀ k, FiniteDimensional ℂ (U k).carrier := fun k =>
    (Mfam ((ee.symm k : {x // x ∈ S₀}) : ι)).isMod.finrank _
  have hsimpU : ∀ k, IsSimpleAMod (U k) := fun k => hsimp _
  have hhq : ∀ j ∈ S₀, h j = h i + (m₀ : ℂ) := by
    intro j hj
    have hjS : j ∈ S := (Finset.filter_subset _ _) hj
    have hoff0 : off j = m₀ := (Finset.mem_filter.mp hj).2
    have := hoff j (hSF hjS)
    rw [hoff0] at this
    linear_combination this
  have hneU : ∀ k l : Fin r, k ≠ l → IsEmpty (AModEquiv W (U k) (U l)) := by
    intro k l hkl
    have hjne : ((ee.symm k : {x // x ∈ S₀}) : ι) ≠ ((ee.symm l : {x // x ∈ S₀}) : ι) := by
      intro hc'
      exact hkl (by
        have : ee.symm k = ee.symm l := Subtype.ext hc'
        simpa using congrArg ee this)
    refine hsep _ _ hjne ?_
    rw [hhq _ (ee.symm k).2, hhq _ (ee.symm l).2]
  set k₀ : Fin r := ee ⟨j₀, hj₀S₀⟩ with hk₀
  obtain ⟨v, hvne, hvzero⟩ := exists_vector_trace_separating U hfdU hsimpU hneU k₀
  -- evaluate the vanishing combination at the separating vector
  have hsumFin : ∑ j ∈ S₀, c j * bottomChar (lowestAMod (hcw j).2) v
      = ∑ k : Fin r, c ((ee.symm k : {x // x ∈ S₀}) : ι) * bottomChar (U k) v := by
    rw [← Finset.sum_coe_sort S₀ (fun j => c j * bottomChar (lowestAMod (hcw j).2) v)]
    exact (Equiv.sum_comp ee.symm
      (fun x : {x // x ∈ S₀} => c (x : ι) * bottomChar (lowestAMod (hcw (x : ι)).2) v)).symm
  have hone : ∑ k : Fin r, c ((ee.symm k : {x // x ∈ S₀}) : ι) * bottomChar (U k) v
      = c ((ee.symm k₀ : {x // x ∈ S₀}) : ι) * bottomChar (U k₀) v := by
    refine Finset.sum_eq_single k₀ (fun k _ hk => ?_) (fun hk => absurd (Finset.mem_univ _) hk)
    rw [bottomChar_apply, hvzero k hk, mul_zero]
  have hzero' : c ((ee.symm k₀ : {x // x ∈ S₀}) : ι) * bottomChar (U k₀) v = 0 := by
    rw [← hone, ← hsumFin]; exact hall v
  have hj₀' : ((ee.symm k₀ : {x // x ∈ S₀}) : ι) = j₀ := by
    rw [hk₀, Equiv.symm_apply_apply]
  rw [hj₀'] at hzero'
  have hc0 : c j₀ = 0 := by
    rcases mul_eq_zero.mp hzero' with hc' | hb
    · exact hc'
    · rw [bottomChar_apply] at hb
      exact absurd hb hvne
  exact (Finset.mem_filter.mp hj₀S).2 hc0

/-- **`TraceIndependent`, from bottom separation.**  Discharges the `hfib` hypothesis of
`Modularity.SqAmbientRank.zhu_modularity_of_slashRepresentable`. -/
theorem traceIndependent_of_bottomSeparation (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hsimp : ∀ j, IsSimpleAMod (lowestAMod (hcw j).2))
    (hsep : ∀ j k : ι, j ≠ k → h j = h k →
      IsEmpty (AModEquiv W (lowestAMod (hcw j).2) (lowestAMod (hcw k).2))) :
    TraceIndependent Mfam h :=
  traceIndependent_of_fibreIndependent Mfam h hcw
    (fibreIndependent_of_bottomSeparation Mfam h hcw hgr hsimp hsep)

end Fibre

end VOA
