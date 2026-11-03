/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeChargeMFields

/-!
# Abstract `EE`-reordering / mutual-locality core for the lattice vertex operators

The `LatExp.LatticeFields` file proves the diagonal mutual locality `Local Yeα Yeα` (charge `+1`)
by the chain `Eplus_comp_Eminus` (the `(1-z₂/z₁)²` FLM contraction) ⟹ `eeMaster` (the four-fold
re-summation into the symmetric `Tv`) ⟹ `EE_shift_comm` ⟹ `Yeα_bracket_zero` ⟹ `Local`.

For the lattice VOA instance we also need the **charge `-1`** diagonal `Local (Yemα (-1)) (Yemα
(-1))`.  Its boson factor `EEC (-1)` obeys the *same* `(1-z₂/z₁)^{⟨-α,-α⟩} = (1-z₂/z₁)²` FLM
contraction (the self-pairing `⟨cα,cα⟩ = 2c² = 2` for `c = ±1`), so the entire §10–§11 chain of
`LatticeFields` applies verbatim.  Rather than duplicate it, this file abstracts the chain over a
bundle `EEData` of the half-current data `(Em, Ep, EEop)` satisfying

* `Em` is creation-only (`Em t = 0` for `t < 0`),
* `Ep` is a field (`IsField Ep`),
* the two halves self-commute (`Em_comm`, `Ep_comm`),
* the **3-term FLM contraction** `Ep_a Em_b = Em_b Ep_a − 2 Em_{b-1} Ep_{a+1} + Em_{b-2} Ep_{a+2}`,
* `EEop` is the honest convolution `EEop_s = ∑ᶠ_m Em_m Ep_{s-m}`.

From these it derives `EEData.eeMaster` (the four-fold re-summation) and `EEData.shift_comm`
(`EEop_{a-2} EEop_b = EEop_{b-2} EEop_a`), the algebraic heart of the diagonal locality.  All
`sorry`-free / axiom-clean, `pbw`-free.
-/

namespace VOA
namespace LatExp

open scoped BigOperators
open Module (End)

/-- The half-current reordering data: a creation half `Em`, an annihilation half `Ep` (a field),
their boson dressing `EEop = :Em·Ep:` (honest convolution), with the two self-commutativities and
the 3-term FLM contraction of self-pairing `⟨cα,cα⟩ = 2`.  Abstracts the charge-`±1` boson factor
of the lattice vertex operator. -/
structure EEData where
  /-- The creation half `E⁻`. -/
  Em : ℤ → End ℂ B
  /-- The annihilation half `E⁺`. -/
  Ep : ℤ → End ℂ B
  /-- The boson dressing `EE = E⁻E⁺`. -/
  EEop : ℤ → End ℂ B
  /-- `E⁻` is creation-only (zero on negative `z`-powers). -/
  Em_neg : ∀ t : ℤ, t < 0 → Em t = 0
  /-- `E⁺` is a field (lower-truncated on every vector). -/
  Ep_field : IsField Ep
  /-- `E⁺` is annihilation-only (zero on positive `z`-powers). -/
  Ep_pos : ∀ t : ℤ, 0 < t → Ep t = 0
  /-- The creation halves commute. -/
  Em_comm : ∀ a b : ℤ, (Em a).comp (Em b) = (Em b).comp (Em a)
  /-- The annihilation halves commute. -/
  Ep_comm : ∀ a b : ℤ, (Ep a).comp (Ep b) = (Ep b).comp (Ep a)
  /-- The 3-term FLM contraction `E⁺_a E⁻_b = E⁻_b E⁺_a − 2 E⁻_{b-1} E⁺_{a+1} + E⁻_{b-2} E⁺_{a+2}`. -/
  contr : ∀ a b : ℤ, (Ep a).comp (Em b)
    = (Em b).comp (Ep a) - (2 : ℂ) • (Em (b - 1)).comp (Ep (a + 1)) + (Em (b - 2)).comp (Ep (a + 2))
  /-- `EEop` is the honest convolution `EEop_s x = ∑ᶠ_m E⁻_m E⁺_{s-m} x`. -/
  EE_conv : ∀ (s : ℤ) (x : B), EEop s x = ∑ᶠ m : ℤ, Em m (Ep (s - m) x)

namespace EEData

variable (D : EEData)

/-- The symmetric four-fold operator `T(C,D') = E⁻(z₁)E⁻(z₂)E⁺(z₁)E⁺(z₂)`. -/
noncomputable def Tv (C D' : ℤ) (x : B) : B :=
  ∑ᶠ pq : ℤ × ℤ, D.Em pq.1 (D.Em pq.2 (D.Ep (C - pq.1) (D.Ep (D' - pq.2) x)))

theorem Tv_symm (C D' : ℤ) (x : B) : D.Tv C D' x = D.Tv D' C x := by
  rw [Tv, Tv, ← finsum_comp_equiv (Equiv.prodComm ℤ ℤ)
    (f := fun pq : ℤ × ℤ => D.Em pq.1 (D.Em pq.2 (D.Ep (D' - pq.1) (D.Ep (C - pq.2) x))))]
  refine finsum_congr fun pq => ?_
  obtain ⟨p, q⟩ := pq
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  have hE : ∀ Y, D.Em p (D.Em q Y) = D.Em q (D.Em p Y) := fun Y => by
    have := DFunLike.congr_fun (D.Em_comm p q) Y; simpa [LinearMap.comp_apply] using this
  have hP : ∀ x', D.Ep (C - p) (D.Ep (D' - q) x') = D.Ep (D' - q) (D.Ep (C - p) x') := fun x' => by
    have := DFunLike.congr_fun (D.Ep_comm (C - p) (D' - q)) x'
    simpa [LinearMap.comp_apply] using this
  rw [hE, hP]

theorem Ep_shift_support_finite (b : ℤ) (y : B) :
    (Function.support (fun q : ℤ => D.Ep (b - q) y)).Finite := by
  obtain ⟨B0, hB0⟩ := D.Ep_field y
  apply Set.Finite.subset (Set.finite_Icc b (b - B0))
  intro q hq
  rw [Function.mem_support] at hq
  rw [Set.mem_Icc]
  constructor
  · by_contra h
    exact hq (by rw [D.Ep_pos (b - q) (show (0 : ℤ) < b - q by omega)]; rfl)
  · by_contra h
    exact hq (hB0 (b - q) (by omega))

theorem EpEp_support_finite (a b : ℤ) (x : B) :
    (Function.support
      (fun pq : ℤ × ℤ => D.Ep (a - pq.1) (D.Ep (b - pq.2) x))).Finite := by
  set Sq := Function.support (fun q : ℤ => D.Ep (b - q) x) with hSq
  have hSqfin : Sq.Finite := D.Ep_shift_support_finite b x
  set P := ⋃ q ∈ Sq, Function.support (fun p : ℤ => D.Ep (a - p) (D.Ep (b - q) x)) with hP
  have hPfin : P.Finite := hSqfin.biUnion (fun q _ => D.Ep_shift_support_finite a (D.Ep (b - q) x))
  apply Set.Finite.subset (hPfin.prod hSqfin)
  intro pq hpq
  rw [Function.mem_support] at hpq
  have hq : pq.2 ∈ Sq := by
    rw [hSq, Function.mem_support]; intro h; exact hpq (by rw [h, map_zero])
  refine Set.mem_prod.mpr ⟨?_, hq⟩
  rw [hP]; exact Set.mem_biUnion hq (Function.mem_support.mpr hpq)

theorem fourfold_support_finite (a b : ℤ) (x : B) :
    (Function.support
      (fun pq : ℤ × ℤ => D.Em pq.1 (D.Em pq.2 (D.Ep (a - pq.1) (D.Ep (b - pq.2) x))))).Finite := by
  apply Set.Finite.subset (D.EpEp_support_finite a b x)
  intro pq hpq
  rw [Function.mem_support] at hpq ⊢
  intro h; exact hpq (by rw [h, map_zero, map_zero])

theorem Tv_eq_nestQ (C D' : ℤ) (x : B) :
    D.Tv C D' x = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      D.Em p (D.Em q (D.Ep (C - p) (D.Ep (D' - q) x))) := by
  rw [Tv, ← finsum_comp_equiv (Equiv.prodComm ℤ ℤ)
      (f := fun pq : ℤ × ℤ => D.Em pq.1 (D.Em pq.2 (D.Ep (C - pq.1) (D.Ep (D' - pq.2) x))))]
  rw [finsum_curry _ ((D.fourfold_support_finite C D' x).preimage
      ((Equiv.prodComm ℤ ℤ).injective.injOn))]
  refine finsum_congr fun q => finsum_congr fun p => ?_
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]

theorem EE_marg_support_finite (s : ℤ) (x : B) :
    (Function.support (fun q : ℤ => D.Em q (D.Ep (s - q) x))).Finite := by
  apply Set.Finite.subset (D.Ep_shift_support_finite s x)
  intro q hq
  rw [Function.mem_support] at hq ⊢
  intro h; exact hq (by rw [h, map_zero])

theorem EE_nest (c d : ℤ) (x : B) :
    D.EEop c (D.EEop d x) = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      D.Em p (D.Ep (c - p) (D.Em q (D.Ep (d - q) x))) := by
  rw [D.EE_conv d x, map_finsum (D.EEop c) (D.EE_marg_support_finite d x)]
  refine finsum_congr fun q => ?_
  rw [D.EE_conv c]

theorem inner_reorder (c d p q : ℤ) (x : B) :
    D.Em p (D.Ep (c - p) (D.Em q (D.Ep (d - q) x)))
      = D.Em p (D.Em q (D.Ep (c - p) (D.Ep (d - q) x)))
        - (2 : ℂ) • D.Em p (D.Em (q - 1) (D.Ep (c - p + 1) (D.Ep (d - q) x)))
        + D.Em p (D.Em (q - 2) (D.Ep (c - p + 2) (D.Ep (d - q) x))) := by
  have h := DFunLike.congr_fun (D.contr (c - p) q) (D.Ep (d - q) x)
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.comp_apply] at h
  rw [h, map_add, map_sub, map_smul]

theorem termB (c d : ℤ) (x : B) :
    (∑ᶠ q : ℤ, ∑ᶠ p : ℤ, D.Em p (D.Em (q - 1) (D.Ep (c - p + 1) (D.Ep (d - q) x))))
      = D.Tv (c + 1) (d - 1) x := by
  rw [Tv_eq_nestQ,
    ← finsum_int_succ_shift (fun q : ℤ =>
      ∑ᶠ p : ℤ, D.Em p (D.Em (q - 1) (D.Ep (c - p + 1) (D.Ep (d - q) x))))]
  refine finsum_congr fun q => finsum_congr fun p => ?_
  rw [show q + 1 - 1 = q from by ring, show d - (q + 1) = d - 1 - q from by ring,
    show c - p + 1 = c + 1 - p from by ring]

theorem termC (c d : ℤ) (x : B) :
    (∑ᶠ q : ℤ, ∑ᶠ p : ℤ, D.Em p (D.Em (q - 2) (D.Ep (c - p + 2) (D.Ep (d - q) x))))
      = D.Tv (c + 2) (d - 2) x := by
  rw [Tv_eq_nestQ,
    ← finsum_comp_equiv (Equiv.addRight (2 : ℤ))
      (f := fun q : ℤ =>
        ∑ᶠ p : ℤ, D.Em p (D.Em (q - 2) (D.Ep (c - p + 2) (D.Ep (d - q) x))))]
  refine finsum_congr fun q => finsum_congr fun p => ?_
  simp only [Equiv.coe_addRight]
  rw [show q + 2 - 2 = q from by ring, show d - (q + 2) = d - 2 - q from by ring,
    show c - p + 2 = c + 2 - p from by ring]

theorem finsum_split3 (u v w : ℤ → B)
    (hu : (Function.support u).Finite) (hv : (Function.support v).Finite)
    (hw : (Function.support w).Finite) :
    (∑ᶠ i, (u i - (2 : ℂ) • v i + w i))
      = (∑ᶠ i, u i) - (2 : ℂ) • (∑ᶠ i, v i) + (∑ᶠ i, w i) := by
  have hv2 : (Function.support (fun i => (2 : ℂ) • v i)).Finite :=
    hv.subset (Function.support_smul_subset_right (fun _ => (2 : ℂ)) v)
  have huv : (Function.support (fun i => u i - (2 : ℂ) • v i)).Finite :=
    (hu.union hv2).subset (Function.support_sub u (fun i => (2 : ℂ) • v i))
  rw [finsum_add_distrib huv hw, finsum_sub_distrib hu hv2, ← smul_finsum' (2 : ℂ) hv]

/-- **The four-fold re-summation** `EEop_c EEop_d = T(c,d) − 2 T(c+1,d-1) + T(c+2,d-2)`. -/
theorem eeMaster (c d : ℤ) (x : B) :
    D.EEop c (D.EEop d x) = D.Tv c d x - 2 • D.Tv (c + 1) (d - 1) x + D.Tv (c + 2) (d - 2) x := by
  have pA : ∀ q : ℤ, (Function.support
      (fun p => D.Em p (D.Em q (D.Ep (c - p) (D.Ep (d - q) x))))).Finite := fun q => by
    apply Set.Finite.subset (D.Ep_shift_support_finite c (D.Ep (d - q) x))
    intro p hp; rw [Function.mem_support] at hp ⊢
    intro h; exact hp (by rw [h, map_zero, map_zero])
  have pB : ∀ q : ℤ, (Function.support
      (fun p => D.Em p (D.Em (q - 1) (D.Ep (c - p + 1) (D.Ep (d - q) x))))).Finite := fun q => by
    apply Set.Finite.subset (D.Ep_shift_support_finite (c + 1) (D.Ep (d - q) x))
    intro p hp; rw [Function.mem_support] at hp ⊢
    intro h; exact hp (by rw [show c - p + 1 = c + 1 - p from by ring, h, map_zero, map_zero])
  have pC : ∀ q : ℤ, (Function.support
      (fun p => D.Em p (D.Em (q - 2) (D.Ep (c - p + 2) (D.Ep (d - q) x))))).Finite := fun q => by
    apply Set.Finite.subset (D.Ep_shift_support_finite (c + 2) (D.Ep (d - q) x))
    intro p hp; rw [Function.mem_support] at hp ⊢
    intro h; exact hp (by rw [show c - p + 2 = c + 2 - p from by ring, h, map_zero, map_zero])
  have qSA : (Function.support
      (fun q => ∑ᶠ p, D.Em p (D.Em q (D.Ep (c - p) (D.Ep (d - q) x))))).Finite := by
    apply Set.Finite.subset (D.Ep_shift_support_finite d x)
    intro q hq; rw [Function.mem_support] at hq ⊢
    exact fun h => hq (finsum_eq_zero_of_forall_eq_zero fun p => by
      rw [h, map_zero, map_zero, map_zero])
  have qSB : (Function.support
      (fun q => ∑ᶠ p, D.Em p (D.Em (q - 1) (D.Ep (c - p + 1) (D.Ep (d - q) x))))).Finite := by
    apply Set.Finite.subset (D.Ep_shift_support_finite d x)
    intro q hq; rw [Function.mem_support] at hq ⊢
    exact fun h => hq (finsum_eq_zero_of_forall_eq_zero fun p => by
      rw [h, map_zero, map_zero, map_zero])
  have qSC : (Function.support
      (fun q => ∑ᶠ p, D.Em p (D.Em (q - 2) (D.Ep (c - p + 2) (D.Ep (d - q) x))))).Finite := by
    apply Set.Finite.subset (D.Ep_shift_support_finite d x)
    intro q hq; rw [Function.mem_support] at hq ⊢
    exact fun h => hq (finsum_eq_zero_of_forall_eq_zero fun p => by
      rw [h, map_zero, map_zero, map_zero])
  rw [EE_nest,
    show (∑ᶠ q : ℤ, ∑ᶠ p : ℤ, D.Em p (D.Ep (c - p) (D.Em q (D.Ep (d - q) x))))
        = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
            (D.Em p (D.Em q (D.Ep (c - p) (D.Ep (d - q) x)))
              - (2 : ℂ) • D.Em p (D.Em (q - 1) (D.Ep (c - p + 1) (D.Ep (d - q) x)))
              + D.Em p (D.Em (q - 2) (D.Ep (c - p + 2) (D.Ep (d - q) x))))
      from finsum_congr fun q => finsum_congr fun p => D.inner_reorder c d p q x,
    show (∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
            (D.Em p (D.Em q (D.Ep (c - p) (D.Ep (d - q) x)))
              - (2 : ℂ) • D.Em p (D.Em (q - 1) (D.Ep (c - p + 1) (D.Ep (d - q) x)))
              + D.Em p (D.Em (q - 2) (D.Ep (c - p + 2) (D.Ep (d - q) x)))))
        = ∑ᶠ q : ℤ,
            ((∑ᶠ p, D.Em p (D.Em q (D.Ep (c - p) (D.Ep (d - q) x))))
              - (2 : ℂ) • (∑ᶠ p, D.Em p (D.Em (q - 1) (D.Ep (c - p + 1) (D.Ep (d - q) x))))
              + (∑ᶠ p, D.Em p (D.Em (q - 2) (D.Ep (c - p + 2) (D.Ep (d - q) x)))))
      from finsum_congr fun q => finsum_split3 _ _ _ (pA q) (pB q) (pC q),
    finsum_split3 _ _ _ qSA qSB qSC, ← Tv_eq_nestQ, termB, termC]
  module

/-- **The shifted self-commutativity** `EEop_{a-2} EEop_b = EEop_{b-2} EEop_a`. -/
theorem shift_comm (a b : ℤ) (x : B) :
    D.EEop (a - 2) (D.EEop b x) = D.EEop (b - 2) (D.EEop a x) := by
  rw [D.eeMaster (a - 2) b x, D.eeMaster (b - 2) a x,
    show a - 2 + 1 = a - 1 from by ring, show a - 2 + 2 = a from by ring,
    show b - 2 + 1 = b - 1 from by ring, show b - 2 + 2 = b from by ring,
    D.Tv_symm (a - 2) b x, D.Tv_symm (a - 1) (b - 1) x, D.Tv_symm a (b - 2) x]
  abel

end EEData

end LatExp
end VOA
