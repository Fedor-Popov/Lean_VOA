/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.FrameWeightTwo

/-!
# `98304` minimal vectors outside `Λ₀`, and `dim (V₀⁺)₂ = 49428`, `dim (V₃⁺)₂ = 49152`

The norm-`4` vectors of the Leech lattice outside `Λ₀ = 2A` are the vectors `x ∈ u + 2A ⊆ ℤ²⁴` with
`x·x = 32`.  All coordinates of `x` are odd, so exactly one is `±3` and the others `±1`.  Writing
`x = u + 2a`, the codeword `c = a mod 2 ∈ Golay` fixes every sign: `x_i = 1 - 2c_i` for `i ≠ p`
and `x_p = 6c_p - 3`.  Conversely every `(p, c) ∈ Fin 24 × Golay` gives such an `x`: the parity
condition `4 ∣ ∑ aᵢ` reduces to `4 ∣ wt(c)` (the Golay code is doubly even).  Hence
(`card_normFour_frameChar_one`)

  `#{α ∈ Λ \ Λ₀ | ⟨α,α⟩ = 4} = 24 · 2¹² = 98304`,

and with `FrameWeightTwo.lean`:

* `finrank_V3_grading_two : dim (V₃⁺)₂ = 49152`;
* `finrank_V0_grading_two : dim (V₀⁺)₂ = 49428`.

These agree with the Python count recorded in `FrameSectors.lean` (`98256 + 98304 = 196560`).

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
Unconditional.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.FrameCount

open Leech

/-- `c_i ∈ {0,1}` as an integer. -/
def cvec (c : Fin 24 → ZMod 2) (i : Fin 24) : ℤ := ((c i).val : ℤ)

theorem cvec_cases (c : Fin 24 → ZMod 2) (i : Fin 24) : cvec c i = 0 ∨ cvec c i = 1 := by
  have h := ZMod.val_lt (c i)
  unfold cvec
  omega

theorem cast_cvec (c : Fin 24 → ZMod 2) (i : Fin 24) : ((cvec c i : ℤ) : ZMod 2) = c i := by
  rw [cvec, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- The odd vector attached to a position `p` and a word `c`. -/
def oddVec (p : Fin 24) (c : Fin 24 → ZMod 2) : Fin 24 → ℤ :=
  fun i => if i = p then 6 * cvec c i - 3 else 1 - 2 * cvec c i

/-- `a` with `oddVec p c = u + 2a`. -/
def aVec (p : Fin 24) (c : Fin 24 → ZMod 2) : Fin 24 → ℤ :=
  fun i => -cvec c i + (if i = p then 4 * cvec c i - 2 else 0) + (if i = 0 then -2 else 0)

theorem uVec_apply (i : Fin 24) : uVec i = if i = 0 then 5 else 1 := rfl

theorem oddVec_sub (p : Fin 24) (c : Fin 24 → ZMod 2) :
    oddVec p c - uVec = (2 : ℤ) • aVec p c := by
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, oddVec, aVec, uVec_apply]
  split_ifs <;> ring

theorem reduceMod_aVec (p : Fin 24) (c : Fin 24 → ZMod 2) : reduceMod 2 24 (aVec p c) = c := by
  funext i
  change ((aVec p c i : ℤ) : ZMod 2) = c i
  rw [← cast_cvec c i, ZMod.intCast_eq_intCast_iff_dvd_sub]
  simp only [aVec]
  split_ifs <;> omega

theorem reduceMod_cvec (c : Fin 24 → ZMod 2) : reduceMod 2 24 (cvec c) = c :=
  funext fun i => cast_cvec c i

theorem weight_eq_sum_cvec (c : Fin 24 → ZMod 2) : ((Code.weight c : ℕ) : ℤ) = ∑ i, cvec c i := by
  have h := weight_reduceMod_eq_sum (cvec c)
  rw [reduceMod_cvec] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases cvec_cases c i with h0 | h1
  · rw [h0]; simp
  · rw [h1]; simp

theorem sum_aVec (p : Fin 24) (c : Fin 24 → ZMod 2) :
    ∑ i, aVec p c i = -(∑ i, cvec c i) + (4 * cvec c p - 2) - 2 := by
  simp only [aVec, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

theorem oddVec_mem {p : Fin 24} {c : Fin 24 → ZMod 2} (hc : c ∈ Code.golay) :
    oddVec p c ∈ Leech.carrier := by
  refine Or.inr (mem_subA2.2 ⟨aVec p c, ⟨?_, ?_⟩, (oddVec_sub p c).symm⟩)
  · rw [mem_preG, reduceMod_aVec]; exact hc
  · rw [sum_aVec, ← weight_eq_sum_cvec]
    obtain ⟨k, hk⟩ := Code.golay_isDoublyEven c hc
    have hk' : ((Code.weight c : ℕ) : ℤ) = 4 * k := by exact_mod_cast hk
    rw [hk']
    rcases cvec_cases c p with h | h <;> rw [h] <;> omega

theorem oddVec_sq (p : Fin 24) (c : Fin 24 → ZMod 2) (i : Fin 24) :
    oddVec p c i * oddVec p c i = 1 + (if i = p then 8 else 0) := by
  simp only [oddVec]
  rcases cvec_cases c i with h | h <;> split_ifs <;> rw [h] <;> norm_num

theorem oddVec_dot (p : Fin 24) (c : Fin 24 → ZMod 2) : oddVec p c ⬝ᵥ oddVec p c = 32 := by
  rw [dotProduct]
  simp only [oddVec_sq, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp

theorem oddVec_zero_odd (p : Fin 24) (c : Fin 24 → ZMod 2) : ¬ (2 : ℤ) ∣ oddVec p c 0 := by
  simp only [oddVec]
  split_ifs <;> omega

/-- `x² - 1` is divisible by `8` for odd `x`. -/
theorem eight_dvd_sq_sub_one {x : ℤ} (hx : ¬ (2 : ℤ) ∣ x) : (8 : ℤ) ∣ x * x - 1 := by
  obtain ⟨k, hk⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
  obtain ⟨m, hm⟩ := Int.even_mul_succ_self k
  exact ⟨m, by rw [hk]; linear_combination 4 * hm⟩

/-- An odd vector of norm `32` has exactly one coordinate `±3`, the others `±1`. -/
theorem exists_three {y : Fin 24 → ℤ} (hodd : ∀ i, ¬ (2 : ℤ) ∣ y i) (hy : y ⬝ᵥ y = 32) :
    ∃ p, y p * y p = 9 ∧ ∀ i, i ≠ p → y i * y i = 1 := by
  set d : Fin 24 → ℤ := fun i => y i * y i - 1 with hd
  have hdnn : ∀ i, 0 ≤ d i := fun i => by
    have h := eight_dvd_sq_sub_one (hodd i)
    have : 0 ≤ y i * y i := mul_self_nonneg _
    have hne : y i * y i ≠ 0 := fun h0 => hodd i (by
      rcases mul_self_eq_zero.mp h0 with h1; rw [h1]; exact dvd_zero 2)
    simp only [hd]; omega
  have hsum : ∑ i, d i = 8 := by
    simp only [hd, Finset.sum_sub_distrib]
    rw [← dotProduct, hy]; simp
  obtain ⟨p, hp⟩ : ∃ p, d p ≠ 0 := by
    by_contra h
    push Not at h
    rw [Finset.sum_eq_zero (fun i _ => h i)] at hsum
    norm_num at hsum
  have h8 : ∀ i, (8 : ℤ) ∣ d i := fun i => eight_dvd_sq_sub_one (hodd i)
  have hle : ∀ i j, i ≠ j → d i + d j ≤ 8 := by
    intro i j hij
    rw [← hsum, ← Finset.sum_pair hij]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hdnn k)
  have hp8 : d p = 8 := by
    have h1 := Finset.single_le_sum (fun k _ => hdnn k) (Finset.mem_univ p)
    rw [hsum] at h1
    obtain ⟨m, hm⟩ := h8 p
    have := hdnn p
    rw [hm] at h1 hp this ⊢
    have : m = 1 := by omega
    rw [this]; norm_num
  refine ⟨p, by simp only [hd] at hp8; omega, fun i hi => ?_⟩
  have h1 := hle i p hi
  have h2 := hdnn i
  simp only [hd] at h1 h2 hp8 ⊢
  omega

end VOA.Moonshine.FrameCount

namespace VOA.Moonshine

open LatGen IntegralLattice Module FrameCount Leech

/-- `(p, x) ↦ oddVec p (golayEnc x)` as a Leech vector. -/
noncomputable def oddPt (q : Fin 24 × (Fin 12 → ZMod 2)) : leech.carrier :=
  (⟨oddVec q.1 (Code.golayEnc q.2), oddVec_mem (Code.golayEnc_mem q.2)⟩ : ↥Leech.carrier)

theorem oddPt_val (q : Fin 24 × (Fin 12 → ZMod 2)) :
    Subtype.val (show ↥Leech.carrier from oddPt q) = oddVec q.1 (Code.golayEnc q.2) := rfl

theorem leech_form_eq (α β : leech.carrier) :
    leech.form α β = (Subtype.val (show ↥Leech.carrier from α) ⬝ᵥ Subtype.val (show ↥Leech.carrier from β)) / 8 := rfl

theorem frameChar_eq (α : leech.carrier) :
    frameChar α = ((Subtype.val (show ↥Leech.carrier from α) 0 : ℤ) : ZMod 2) := rfl

theorem oddPt_injective : Function.Injective oddPt := by
  rintro ⟨p, x⟩ ⟨p', x'⟩ h
  have hv : oddVec p (Code.golayEnc x) = oddVec p' (Code.golayEnc x') := by
    have := congrArg (fun z : leech.carrier => Subtype.val (show ↥Leech.carrier from z)) h
    simpa only [oddPt_val] using this
  have hpp : p = p' := by
    by_contra hne
    have h1 := congrFun hv p
    have e1 : oddVec p (Code.golayEnc x) p = 6 * cvec (Code.golayEnc x) p - 3 := by
      simp [oddVec]
    have e2 : oddVec p' (Code.golayEnc x') p = 1 - 2 * cvec (Code.golayEnc x') p := by
      simp [oddVec, hne]
    have a := cvec_cases (Code.golayEnc x) p
    have b := cvec_cases (Code.golayEnc x') p
    omega
  subst hpp
  have hc : Code.golayEnc x = Code.golayEnc x' := by
    funext i
    have h1 := congrFun hv i
    have hcv : cvec (Code.golayEnc x) i = cvec (Code.golayEnc x') i := by
      simp only [oddVec] at h1
      split_ifs at h1 <;> omega
    rw [← cast_cvec (Code.golayEnc x) i, hcv, cast_cvec]
  rw [Code.golayEnc_injective hc]

/-- The norm-`4` vectors outside `Λ₀`. -/
noncomputable def oddFour : Finset leech.carrier :=
  (normFour leech leech_posDef).filter fun α => frameChar α = 1

theorem oddPt_mem (q : Fin 24 × (Fin 12 → ZMod 2)) : oddPt q ∈ oddFour := by
  rw [oddFour, Finset.mem_filter, mem_normFour, leech_form_eq, oddPt_val, oddVec_dot,
    frameChar_eq, oddPt_val]
  refine ⟨by norm_num, ?_⟩
  have h := oddVec_zero_odd q.1 (Code.golayEnc q.2)
  obtain ⟨k, hk⟩ : ∃ k, oddVec q.1 (Code.golayEnc q.2) 0 = 2 * k + 1 :=
    ⟨oddVec q.1 (Code.golayEnc q.2) 0 / 2, by omega⟩
  rw [hk]; push_cast
  rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]

theorem exists_oddPt {α : leech.carrier} (hα : α ∈ oddFour) : ∃ q, oddPt q = α := by
  rw [oddFour, Finset.mem_filter, mem_normFour] at hα
  obtain ⟨hn, hc⟩ := hα
  set y := Subtype.val (show ↥Leech.carrier from α) with hy
  have hmem : y ∈ Leech.carrier := (show ↥Leech.carrier from α).2
  have hy0 : ¬ (2 : ℤ) ∣ y 0 := by
    intro h2
    rw [frameChar_eq, ← hy, (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr h2] at hc
    exact absurd hc (by decide)
  obtain ⟨a, ha, hya⟩ : ∃ a ∈ subA, (2 : ℤ) • a = y - uVec := by
    rcases hmem with h | h
    · exfalso
      obtain ⟨a, _, ha⟩ := mem_subA2.1 h
      exact hy0 ⟨a 0, by rw [← ha]; simp⟩
    · exact mem_subA2.1 h
  have hcoord : ∀ i, y i = uVec i + 2 * a i := fun i => by
    have := congrFun hya i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at this
    omega
  have hodd : ∀ i, ¬ (2 : ℤ) ∣ y i := fun i => by
    rw [hcoord i, uVec_apply]; split_ifs <;> omega
  have hdot : y ⬝ᵥ y = 32 := by
    have h8 := Leech.eight_mul_lattice_bilin (show ↥Leech.carrier from α) (show ↥Leech.carrier from α)
    have : Leech.lattice.bilin (show ↥Leech.carrier from α) (show ↥Leech.carrier from α) = 4 := hn
    rw [this] at h8
    rw [hy]; omega
  obtain ⟨p, hp, hi⟩ := exists_three hodd hdot
  obtain ⟨x, hx⟩ := Code.mem_golay.mp (mem_preG.mp ha.1)
  refine ⟨(p, x), ?_⟩
  have hval : oddVec p (Code.golayEnc x) = y := by
    funext i
    have hcv : cvec (Code.golayEnc x) i = a i % 2 := by
      rw [cvec, hx]
      exact ZMod.val_intCast (a i)
    simp only [oddVec, hcv]
    have hyi := hcoord i
    rw [uVec_apply] at hyi
    split_ifs with h1
    · subst h1
      have : (y i - 3) * (y i + 3) = 0 := by linear_combination hp
      rcases mul_eq_zero.mp this with h | h <;> split_ifs at hyi <;> omega
    · have : (y i - 1) * (y i + 1) = 0 := by linear_combination hi i h1
      rcases mul_eq_zero.mp this with h | h <;> split_ifs at hyi <;> omega
  have : (show ↥Leech.carrier from oddPt (p, x)) = (show ↥Leech.carrier from α) :=
    Subtype.ext (by rw [oddPt_val, hval])
  exact this

/-- **`#{α ∈ Λ \ Λ₀ | ⟨α,α⟩ = 4} = 98304`.** -/
theorem card_normFour_frameChar_one : oddFour.card = 98304 := by
  classical
  have himg : oddFour = Finset.univ.image oddPt := by
    ext α
    rw [Finset.mem_image]
    constructor
    · intro h; obtain ⟨q, hq⟩ := exists_oddPt h; exact ⟨q, Finset.mem_univ _, hq⟩
    · rintro ⟨q, _, rfl⟩; exact oddPt_mem q
  rw [himg, Finset.card_image_of_injective _ oddPt_injective, Finset.card_univ]
  simp [ZMod.card]

/-- **`dim (V₃⁺)₂ = 49152`.** -/
theorem finrank_V3_grading_two :
    finrank ℂ ↥((frameSector 1).comap (leechVOAPlus.grading 2).subtype) = 49152 := by
  have h := two_mul_card_halfFourChi_one
  rw [show ((normFour leech leech_posDef).filter fun α => frameChar α = 1) = oddFour from rfl,
    card_normFour_frameChar_one] at h
  rw [finrank_frameSector_one_grading_two]
  omega

/-- **`dim (V₀⁺)₂ = 49428`.** -/
theorem finrank_V0_grading_two :
    finrank ℂ ↥((frameSector 0).comap (leechVOAPlus.grading 2).subtype) = 49428 := by
  have h := two_mul_card_halfFourChi_one
  rw [show ((normFour leech leech_posDef).filter fun α => frameChar α = 1) = oddFour from rfl,
    card_normFour_frameChar_one] at h
  have h2 := card_halfFourChi_add
  rw [finrank_frameSector_zero_grading_two]
  omega

end VOA.Moonshine
