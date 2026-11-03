/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.ConversePlus
import VOA.Classification.COne.LatticeC2
import VOA.Moonshine.GenerationFock

/-!
# `C₂(V_{2m}⁺)`: the sector reduction

Write `V = V_{2m}` (lattice `L = ℤα`, `⟨α,α⟩ = 2m`), `θ` its lift of `−1`, `V⁺ = V^θ`,
`P = ½(1 + θ) : V → V⁺` (`PP`) and `x_a = e^a + e^{−a} ∈ V⁺` (`xP`).

## Main results

* `smul_xP_PP` — the **charge-splitting identity** `x_a₍ₙ₎ P(v) = P(e^a₍ₙ₎v + e^{−a}₍ₙ₎v)`, valid
  for every `n` and `v` (no safety condition: the two "θ-partner" terms recombine through
  `θ(u₍ₙ₎v) = (θu)₍ₙ₎(θv)`).
* `sector_reduction` — **Yamskulna, Comm. Algebra 32 (2004), Theorem 4.13** (for every `m ≥ 1`,
  with a new short proof):
  `V⁺ = C₂(V⁺) + P(M(1) ⊗ e⁰) + P(M(1) ⊗ e^α)`.
  Proof: for a charge `g ≥ 2` take `a = α`, `c = (g−1)α` and `n = −d−1−2m(g−1) ≤ −2`.  The
  `e^{−α}` term of `x_α₍ₙ₎P(p ⊗ e^c)` lies in sector `g − 2`, and
  `e^α₍ₙ₎(p ⊗ e^c) = ε·Σ_r S_{d+r}(α)·E⁺(α)_{−r} p ⊗ e^{gα}` is triangular: downward induction on
  `d` (as in `Moonshine/Generation.lean`) reaches `d = 0`, i.e. every `p ⊗ e^{gα}`.  Negative
  charges follow by `P ∘ θ = P`.
* `c2Cofinite_of_sectors` — `C₂`-cofiniteness of `V_{2m}⁺` follows from the finiteness of the
  two low sectors modulo `C₂` (`PlusSectorFinite m hm 0`, `PlusSectorFinite m hm 1`), and
  `sectors_of_c2Cofinite` is the converse, so `c2Cofinite_iff_sectors` is an **equivalence**:
  nothing is lost by the reduction.
* `v2mPlusC2CofiniteFactGe2_of_sectorFact` — the cited fact `V2mPlusC2CofiniteFactGe2` from
  `V2mPlusSectorFactGe2` (and back: `v2mPlusSectorFactGe2_iff`).

## The residual

`V2mPlusSectorFactGe2`: for `m ≥ 2`, the images of `P(M(1) ⊗ e⁰) = M(1)⁺` and of
`P(M(1) ⊗ e^α) = V⁺(1)` in `V⁺/C₂(V⁺)` are finite-dimensional.  This is exactly
Yamskulna's Theorem 5.1(1) (her Cor. 5.19 + Lemma 5.22 for `M(1)⁺`, Thm 5.8 for `V⁺(1)`, `k ≥ 3`;
Lemma 3.8 for `k = 2`); her §4 — which this file replaces — is the part proved here.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN VOA.Moonshine

namespace PlusC2

variable (m : ℕ) (hm : 1 ≤ m)

/-! ## §1  The projection `P = ½(1 + θ)` and the states `x_a` -/

/-- The carrier submodule of `V_{2m}⁺` inside `V_{2m}`. -/
noncomputable abbrev VP : Submodule ℂ (LatModuleGen (latP m)) :=
  (orbifold (Subgroup.zpowers (thetaV2m m hm))).carrier

theorem mem_VP_iff (v : LatModuleGen (latP m)) :
    v ∈ VP m hm ↔ thetaLat (latP m) v = v :=
  mem_orbifold_zpowers_iff (thetaV2m m hm) v

theorem half_add_theta_mem (v : LatModuleGen (latP m)) :
    ((1 / 2 : ℂ) • (v + thetaLat (latP m) v)) ∈ VP m hm := by
  rw [mem_VP_iff, map_smul, map_add, thetaLat_thetaLat, add_comm]

/-- The projection `P = ½(1 + θ) : V_{2m} → V_{2m}⁺`. -/
noncomputable def PP : LatModuleGen (latP m) →ₗ[ℂ] VP m hm :=
  LinearMap.codRestrict _ ((1 / 2 : ℂ) • (LinearMap.id + (thetaLat (latP m)).toLinearMap))
    (fun v => by simpa using half_add_theta_mem m hm v)

theorem PP_coe (v : LatModuleGen (latP m)) :
    ((PP m hm v : VP m hm) : LatModuleGen (latP m)) = (1 / 2 : ℂ) • (v + thetaLat (latP m) v) := by
  simp [PP]

theorem PP_of_mem (v : VP m hm) : PP m hm (v : LatModuleGen (latP m)) = v := by
  apply Subtype.ext
  rw [PP_coe, (mem_VP_iff m hm _).mp v.2, ← two_smul ℂ, smul_smul]
  norm_num

theorem PP_theta (v : LatModuleGen (latP m)) : PP m hm (thetaLat (latP m) v) = PP m hm v := by
  apply Subtype.ext
  rw [PP_coe, PP_coe, thetaLat_thetaLat, add_comm]

/-- `x_a = e^a + e^{−a} ∈ V_{2m}⁺`. -/
noncomputable def xP (a : (latP m).carrier) : VP m hm :=
  ⟨latChargeGen (latP m) a + latChargeGen (latP m) (-a), by
    rw [mem_VP_iff, map_add, thetaLat_latChargeGen, thetaLat_latChargeGen, neg_neg, add_comm]⟩

theorem V2mPlus_smul_coe (u : VP m hm) (n : ℤ) (v : VP m hm) :
    (((V2mPlus m hm).smul u n v : VP m hm) : LatModuleGen (latP m)) =
      (V2m m hm).smul (u : LatModuleGen (latP m)) n v := rfl

theorem theta_smul (u : LatModuleGen (latP m)) (n : ℤ) (v : LatModuleGen (latP m)) :
    thetaLat (latP m) ((V2m m hm).smul u n v) =
      (V2m m hm).smul (thetaLat (latP m) u) n (thetaLat (latP m) v) := by
  have := (thetaV2m m hm).map_smul' u n v
  simpa [thetaV2m] using this

/-- **The charge-splitting identity** `x_a₍ₙ₎ P(v) = P(e^a₍ₙ₎v + e^{−a}₍ₙ₎v)`. -/
theorem smul_xP_PP (a : (latP m).carrier) (n : ℤ) (v : LatModuleGen (latP m)) :
    (V2mPlus m hm).smul (xP m hm a) n (PP m hm v) =
      PP m hm ((V2m m hm).smul (latChargeGen (latP m) a) n v +
        (V2m m hm).smul (latChargeGen (latP m) (-a)) n v) := by
  apply Subtype.ext
  rw [V2mPlus_smul_coe, PP_coe, PP_coe, xP]
  simp only
  rw [map_add, theta_smul, theta_smul, thetaLat_latChargeGen, thetaLat_latChargeGen, neg_neg,
    PreVertexAlgebra.smul_smul_right, PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    PreVertexAlgebra.smul_add_right]
  simp only [smul_add]
  abel

/-! ## §2  The `C₂` pull-back -/

/-- `G = P⁻¹(C₂(V⁺))`. -/
noncomputable def G : Submodule ℂ (LatModuleGen (latP m)) :=
  (O₂ (V2mPlus m hm)).comap (PP m hm)

theorem split_mem_G (a : (latP m).carrier) {n : ℤ} (hn : n ≤ -2) (v : LatModuleGen (latP m)) :
    (V2m m hm).smul (latChargeGen (latP m) a) n v +
      (V2m m hm).smul (latChargeGen (latP m) (-a)) n v ∈ G m hm := by
  rw [G, Submodule.mem_comap, ← smul_xP_PP]
  exact smul_le_neg_two_mem_O₂ _ _ _ hn

/-! ## §3  The sector reduction -/

/-- `P(M(1) ⊗ e^g)`: the image of the charge-`g` sector. -/
noncomputable def sectorP (g : (latP m).carrier) : Submodule ℂ (VP m hm) :=
  Submodule.span ℂ (Set.range fun q : FockN (rank (latP m)) => PP m hm (latStateGen (latP m) q g))

/-- The target: `P⁻¹(C₂(V⁺) + P(sector 0) + P(sector 1))`. -/
noncomputable def H : Submodule ℂ (LatModuleGen (latP m)) :=
  (O₂ (V2mPlus m hm) ⊔ (sectorP m hm 0 ⊔ sectorP m hm (1 : ℤ))).comap (PP m hm)

theorem G_le_H : G m hm ≤ H m hm :=
  Submodule.comap_mono le_sup_left

theorem mem_H_theta_iff (v : LatModuleGen (latP m)) :
    thetaLat (latP m) v ∈ H m hm ↔ v ∈ H m hm := by
  rw [H, Submodule.mem_comap, Submodule.mem_comap, PP_theta]

theorem sector_zero_mem_H (q : FockN (rank (latP m))) : latStateGen (latP m) q 0 ∈ H m hm := by
  rw [H, Submodule.mem_comap]
  exact Submodule.mem_sup_right (Submodule.mem_sup_left (Submodule.subset_span ⟨q, rfl⟩))

theorem sector_one_mem_H (q : FockN (rank (latP m))) :
    latStateGen (latP m) q (1 : ℤ) ∈ H m hm := by
  rw [H, Submodule.mem_comap]
  exact Submodule.mem_sup_right (Submodule.mem_sup_right (Submodule.subset_span ⟨q, rfl⟩))

theorem sector_neg_mem_H_iff (q : FockN (rank (latP m))) (g : (latP m).carrier) :
    latStateGen (latP m) q (-g) ∈ H m hm ↔
      latStateGen (latP m) (sigmaN (rank (latP m)) q) g ∈ H m hm := by
  rw [← mem_H_theta_iff, thetaLat_latStateGen, neg_neg]

/-- The triangular step: in a sector `g ≥ 2` whose sector `g − 2` lies in `H`, every
`S_d(α)·p ⊗ e^{gα}` lies in `H`. -/
theorem vSchur_mul_mem_H (g : ℤ) (hg : 2 ≤ g)
    (IH : ∀ q : FockN (rank (latP m)), latStateGen (latP m) q (g - 2 : ℤ) ∈ H m hm) :
    ∀ k : ℕ, ∀ d : ℕ, ∀ q ∈ gradingWN (rank (latP m)) k,
      latStateGen (latP m) (vSchur (latP m) (1 : ℤ) d * q) (g : ℤ) ∈ H m hm := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro d q hq
  set a : (latP m).carrier := (1 : ℤ) with ha
  set c : (latP m).carrier := (g - 1 : ℤ) with hc
  have hform : (latP m).form a c = 2 * (m : ℤ) * (g - 1) := by
    rw [ha, hc, latP_form]; ring
  set n : ℤ := -(d : ℤ) - 1 - (latP m).form a c with hn
  have hn2 : n ≤ -2 := by
    rw [hn, hform]
    have : (1 : ℤ) ≤ m := by exact_mod_cast hm
    nlinarith
  have h1 := G_le_H m hm (split_mem_G m hm a hn2 (latStateGen (latP m) q c))
  -- the `e^{−α}` term lies in sector `g − 2`
  have h2 : (V2m m hm).smul (latChargeGen (latP m) (-a)) n (latStateGen (latP m) q c) ∈ H m hm := by
    rw [V2m, latVOA_smul_latChargeGen_state]
    refine Submodule.smul_mem _ _ ?_
    have : (-a + c : (latP m).carrier) = (g - 2 : ℤ) := by
      rw [ha, hc]; show (-1 + (g - 1) : ℤ) = g - 2; ring
    rw [this]
    exact IH _
  have h3 := Submodule.sub_mem _ h1 h2
  rw [add_sub_cancel_right, V2m, latVOA_smul_latChargeGen_state,
    show -n - 1 - (latP m).form a c = (d : ℤ) by omega,
    show (a + c : (latP m).carrier) = (g : ℤ) by rw [ha, hc]; show (1 + (g - 1) : ℤ) = g; ring,
    EEVec_expand (latP m) a hq d, latStateGen_finsum, Finset.sum_range_succ', aExpVec_zero,
    LinearMap.id_apply, add_zero, smul_add] at h3
  have hrest : latticeCocycle (latP m) a c • ∑ r ∈ Finset.range k,
      latStateGen (latP m) (vSchur (latP m) a (d + (r + 1)) * aExpVec (latP m) a (r + 1) q)
        (g : ℤ) ∈ H m hm := by
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun r hr => ?_)
    simp only [Finset.mem_range] at hr
    have hq' : aExpVec (latP m) a (r + 1) q ∈ gradingWN (rank (latP m)) (k - (r + 1)) := by
      have := aExpVec_mem_gradingZN (latP m) a (r + 1) hq
      rwa [gradingZN_of_nonneg (by omega), show ((k : ℤ) - ((r + 1 : ℕ) : ℤ)).toNat = k - (r + 1)
        by omega] at this
    exact ihk (k - (r + 1)) (by omega) (d + (r + 1)) _ hq'
  have h4 := Submodule.sub_mem _ h3 hrest
  rw [add_sub_cancel_left] at h4
  have h5 := Submodule.smul_mem _ (latticeCocycle (latP m) a c) h4
  rwa [smul_smul, latticeCocycle_sq, one_smul] at h5

/-- Every homogeneous state of a sector `g ≥ 2` lies in `H`, given sector `g − 2`. -/
theorem sector_mem_H_of (g : ℤ) (hg : 2 ≤ g)
    (IH : ∀ q : FockN (rank (latP m)), latStateGen (latP m) q (g - 2 : ℤ) ∈ H m hm)
    (k : ℕ) (q : FockN (rank (latP m))) (hq : q ∈ gradingWN (rank (latP m)) k) :
    latStateGen (latP m) q (g : ℤ) ∈ H m hm := by
  have := vSchur_mul_mem_H m hm g hg IH k 0 q hq
  rwa [vSchur_zero, one_mul] at this

/-- The sector map `q ↦ q ⊗ e^g` is linear; membership of all homogeneous states gives all. -/
theorem sector_mem_H_of_homog (g : (latP m).carrier)
    (h : ∀ (k : ℕ) (q : FockN (rank (latP m))), q ∈ gradingWN (rank (latP m)) k →
      latStateGen (latP m) q g ∈ H m hm)
    (q : FockN (rank (latP m))) : latStateGen (latP m) q g ∈ H m hm := by
  set φ : FockN (rank (latP m)) →ₗ[ℂ] LatModuleGen (latP m) :=
    (TensorProduct.mk ℂ (FockN (rank (latP m))) ((latP m).carrier →₀ ℂ)).flip (eGen (latP m) g)
    with hφ
  have hφapp : ∀ p, φ p = latStateGen (latP m) p g := fun p => rfl
  suffices hsub : (⊤ : Submodule ℂ (FockN (rank (latP m)))) ≤ (H m hm).comap φ by
    have := hsub (Submodule.mem_top (x := q))
    rwa [Submodule.mem_comap, hφapp] at this
  have hspan : (⊤ : Submodule ℂ (FockN (rank (latP m)))) ≤
      ⨆ k : ℕ, gradingWN (rank (latP m)) k := (gradingWN_iSup_eq_top _).ge
  refine hspan.trans (iSup_le fun k p hp => ?_)
  rw [Submodule.mem_comap, hφapp]
  exact h k p hp

/-- Every charge sector lies in `H`. -/
theorem sector_nat_mem_H : ∀ (g : ℕ) (q : FockN (rank (latP m))),
    latStateGen (latP m) q ((g : ℤ) : (latP m).carrier) ∈ H m hm := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ihg =>
  intro q
  rcases Nat.lt_or_ge g 2 with hg | hg
  · interval_cases g
    · exact sector_zero_mem_H m hm q
    · exact sector_one_mem_H m hm q
  · refine sector_mem_H_of_homog m hm _ (fun k p hp => ?_) q
    refine sector_mem_H_of m hm (g : ℤ) (by exact_mod_cast hg) (fun q' => ?_) k p hp
    have := ihg (g - 2) (by omega) q'
    rwa [show ((g - 2 : ℕ) : ℤ) = (g : ℤ) - 2 by omega] at this

theorem sector_mem_H (c : (latP m).carrier) (q : FockN (rank (latP m))) :
    latStateGen (latP m) q c ∈ H m hm := by
  obtain ⟨g, hg | hg⟩ := Int.eq_nat_or_neg (show ℤ from c)
  · have := sector_nat_mem_H m hm g q
    exact (show c = ((g : ℤ) : (latP m).carrier) from hg) ▸ this
  · have := sector_nat_mem_H m hm g (sigmaN (rank (latP m)) q)
    rw [← sector_neg_mem_H_iff] at this
    exact (show c = (-((g : ℤ) : (latP m).carrier) : (latP m).carrier) from hg) ▸ this

theorem H_eq_top : H m hm = ⊤ := by
  rw [eq_top_iff, ← wordStateLatGen_span (latP m), Submodule.span_le]
  rintro _ ⟨⟨l, α⟩, rfl⟩
  rw [SetLike.mem_coe, Function.uncurry_apply_pair, wordStateLatGen_eq]
  exact sector_mem_H m hm α (wordStateN l)

/-- **The sector reduction** (Yamskulna 2004, Theorem 4.13, every `m ≥ 1`):
`V_{2m}⁺ = C₂(V_{2m}⁺) + P(M(1) ⊗ e⁰) + P(M(1) ⊗ e^α)`. -/
theorem sector_reduction (v : VP m hm) :
    v ∈ O₂ (V2mPlus m hm) ⊔ (sectorP m hm 0 ⊔ sectorP m hm (1 : ℤ)) := by
  have hv : (v : LatModuleGen (latP m)) ∈ H m hm := by rw [H_eq_top]; trivial
  rwa [H, Submodule.mem_comap, PP_of_mem] at hv

theorem sector_reduction_top :
    (⊤ : Submodule ℂ (VP m hm)) = O₂ (V2mPlus m hm) ⊔ (sectorP m hm 0 ⊔ sectorP m hm (1 : ℤ)) :=
  (eq_top_iff.mpr fun v _ => sector_reduction m hm v).symm

/-! ## §4  `C₂`-cofiniteness is equivalent to the finiteness of the two low sectors -/

/-- **Sector `g` is finite modulo `C₂`**: `P(M(1) ⊗ e^g)` lies in `C₂(V⁺)` plus the span of a
finite set. -/
def PlusSectorFinite (g : (latP m).carrier) : Prop :=
  ∃ S : Finset (VP m hm), sectorP m hm g ≤ Submodule.span ℂ (S : Set (VP m hm)) ⊔ O₂ (V2mPlus m hm)

theorem c2Cofinite_of_finite_span_sup' (S : Finset (VP m hm))
    (hS : (⊤ : Submodule ℂ (VP m hm)) = Submodule.span ℂ (S : Set (VP m hm)) ⊔ O₂ (V2mPlus m hm)) :
    C2Cofinite (V2mPlus m hm) := by
  classical
  set W := V2mPlus m hm
  set f : (Submodule.span ℂ (S : Set (VP m hm))) →ₗ[ℂ] A₂ W :=
    (mk₂ W).comp (Submodule.span ℂ (S : Set (VP m hm))).subtype with hf
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (S : Set (VP m hm))) :=
    FiniteDimensional.span_of_finite ℂ S.finite_toSet
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := mk₂_surjective W y
    have hx : x ∈ Submodule.span ℂ (S : Set (VP m hm)) ⊔ O₂ W := by rw [← hS]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨a, ha⟩, ?_⟩
    change mk₂ W a = mk₂ W (a + b)
    rw [mk₂_eq_iff]
    simpa using (O₂ W).neg_mem hb
  exact Module.Finite.of_surjective f hsurj

/-- `C₂`-cofiniteness of `V_{2m}⁺` from the two low sectors. -/
theorem c2Cofinite_of_sectors (h0 : PlusSectorFinite m hm 0) (h1 : PlusSectorFinite m hm (1 : ℤ)) :
    C2Cofinite (V2mPlus m hm) := by
  classical
  obtain ⟨S0, hS0⟩ := h0
  obtain ⟨S1, hS1⟩ := h1
  refine c2Cofinite_of_finite_span_sup' m hm (S0 ∪ S1) (le_antisymm ?_ le_top)
  rw [sector_reduction_top m hm]
  have hspan : Submodule.span ℂ ((S0 : Set (VP m hm))) ⊔ Submodule.span ℂ (S1 : Set (VP m hm)) ≤
      Submodule.span ℂ ((S0 ∪ S1 : Finset (VP m hm)) : Set (VP m hm)) := by
    rw [Finset.coe_union, Submodule.span_union]
  refine sup_le le_sup_right (sup_le (hS0.trans ?_) (hS1.trans ?_))
  · exact sup_le_sup_right ((le_sup_left).trans hspan) _
  · exact sup_le_sup_right ((le_sup_right).trans hspan) _

/-- Conversely, a `C₂`-cofinite `V_{2m}⁺` has every sector finite modulo `C₂`. -/
theorem sectors_of_c2Cofinite (h : C2Cofinite (V2mPlus m hm)) (g : (latP m).carrier) :
    PlusSectorFinite m hm g := by
  classical
  set W := V2mPlus m hm
  haveI : Module.Finite ℂ (A₂ W) := h
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := ℂ) (M := A₂ W)
  choose lift hlift using fun t : A₂ W => mk₂_surjective W t
  refine ⟨T.image lift, fun v _ => ?_⟩
  have hv : mk₂ W v ∈ Submodule.span ℂ (T : Set (A₂ W)) := by rw [hT]; trivial
  have hmap : Submodule.span ℂ (T : Set (A₂ W)) ≤
      (Submodule.span ℂ ((T.image lift : Finset (VP m hm)) : Set (VP m hm))).map (mk₂ W) := by
    rw [Submodule.span_le]
    intro t ht
    refine ⟨lift t, Submodule.subset_span ?_, hlift t⟩
    simp only [Finset.coe_image]
    exact ⟨t, ht, rfl⟩
  obtain ⟨y, hy, hyv⟩ := hmap hv
  have hdiff : v - y ∈ O₂ W := by
    rw [← mk₂_eq_zero_iff, map_sub, hyv, sub_self]
  have : v = y + (v - y) := by abel
  rw [this]
  exact Submodule.add_mem_sup hy hdiff

/-- **`C₂`-cofiniteness of `V_{2m}⁺` is equivalent to the finiteness of sectors 0 and 1.** -/
theorem c2Cofinite_iff_sectors :
    C2Cofinite (V2mPlus m hm) ↔ PlusSectorFinite m hm 0 ∧ PlusSectorFinite m hm (1 : ℤ) :=
  ⟨fun h => ⟨sectors_of_c2Cofinite m hm h 0, sectors_of_c2Cofinite m hm h _⟩,
    fun h => c2Cofinite_of_sectors m hm h.1 h.2⟩

end PlusC2

open PlusC2

/-- **The residual of the `C₂` fact after the sector reduction** (TRUE; Yamskulna 2004,
Theorem 5.1(1) — Cor. 5.19 + Lemma 5.22 for `M(1)⁺`, Thm 5.8 for `V⁺(1)` — for `k = m ≥ 3`, and
Lemma 3.8 (`V_L⁺ ≅ L(½,0) ⊗ L(½,0)`, DGH) for `m = 2`): for `m ≥ 2`, the images of
`M(1)⁺ = P(M(1) ⊗ e⁰)` and `V⁺(1) = P(M(1) ⊗ e^α)` in `V_{2m}⁺ / C₂(V_{2m}⁺)` are
finite-dimensional.  Equivalent to `V2mPlusC2CofiniteFactGe2` (`v2mPlusSectorFactGe2_iff`). -/
def V2mPlusSectorFactGe2 : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → PlusSectorFinite m hm 0 ∧ PlusSectorFinite m hm (1 : ℤ)

/-- The cited `C₂` fact from the two-sector residual. -/
theorem v2mPlusC2CofiniteFactGe2_of_sectorFact (h : V2mPlusSectorFactGe2) :
    V2mPlusC2CofiniteFactGe2 := fun m hm h2 =>
  c2Cofinite_of_sectors m hm (h m hm h2).1 (h m hm h2).2

theorem v2mPlusSectorFactGe2_iff : V2mPlusSectorFactGe2 ↔ V2mPlusC2CofiniteFactGe2 :=
  ⟨v2mPlusC2CofiniteFactGe2_of_sectorFact, fun h m hm h2 => (c2Cofinite_iff_sectors m hm).mp (h m hm h2)⟩

end VOA.Classification.COne

section AxiomAudit
#print axioms VOA.Classification.COne.PlusC2.smul_xP_PP
#print axioms VOA.Classification.COne.PlusC2.sector_reduction
#print axioms VOA.Classification.COne.PlusC2.c2Cofinite_iff_sectors
#print axioms VOA.Classification.COne.v2mPlusC2CofiniteFactGe2_of_sectorFact
#print axioms VOA.Classification.COne.v2mPlusSectorFactGe2_iff
end AxiomAudit
