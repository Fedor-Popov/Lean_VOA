/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkLevelBox

/-!
# Serre–Stark S4-4: the level-box residual follows from Theorem A

Certificate that `SerreStarkLevelBox24` assumes nothing beyond the published theorem:
`levelBox_of_theoremA : SerreStarkTheoremA → SerreStarkLevelBox24`.

Ingredients:
* `primitive_unique`: two primitive Dirichlet characters of conductors dividing `N` that agree
  on `(ℤ/N)ˣ` have the same conductor and are equal (via Mathlib's `factorsThrough_gcd`);
* Dedekind–Artin independence of characters (`linearIndependent_monoidHom`) separates the
  components of `f = Σ cᵢ θ_{ψᵢ,tᵢ}` by their character on `(ℤ/N)ˣ`;
* a minimality argument on the remaining `θ_{ψ,T}`: the least `T` with nonzero total weight has
  `a(T) = 2·(weight) ≠ 0`, so `T ∈ t·□` lies in the box, contradiction.
-/

open Complex
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

open DirichletCharacter

/-- Two primitive characters inducing the same character modulo `N` have the same conductor
and the same values. -/
theorem primitive_unique {N r₁ r₂ : ℕ} [NeZero N] {ψ₁ : DirichletCharacter ℂ r₁}
    {ψ₂ : DirichletCharacter ℂ r₂} (h₁ : ψ₁.IsPrimitive) (h₂ : ψ₂.IsPrimitive) (d₁ : r₁ ∣ N)
    (d₂ : r₂ ∣ N) (heq : changeLevel d₁ ψ₁ = changeLevel d₂ ψ₂) :
    r₁ = r₂ ∧ ∀ x : ℤ, ψ₁ (x : ZMod r₁) = ψ₂ (x : ZMod r₂) := by
  have hr₁ : r₁ ≠ 0 := fun h => by subst h; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd d₁)
  have hr₂ : r₂ ≠ 0 := fun h => by subst h; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd d₂)
  haveI : NeZero r₁ := ⟨hr₁⟩
  haveI : NeZero r₂ := ⟨hr₂⟩
  -- equality at level `r₁ r₂`
  have hlift : ∀ {a b : ℕ} [NeZero a] [NeZero b] {φ₁ : DirichletCharacter ℂ a}
      {φ₂ : DirichletCharacter ℂ b} (da : a ∣ N) (db : b ∣ N),
      changeLevel da φ₁ = changeLevel db φ₂ →
      changeLevel (a.dvd_mul_right b) φ₁ = changeLevel (b.dvd_mul_left a) φ₂ := by
    intro a b _ _ φ₁ φ₂ da db h
    haveI : NeZero (a * b * N) := ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b))
      (NeZero.ne N)⟩
    apply changeLevel_injective (Nat.dvd_mul_right (a * b) N)
    rw [← changeLevel_trans, ← changeLevel_trans,
      changeLevel_trans _ da (N.dvd_mul_left (a * b)), h,
      ← changeLevel_trans]
  have g₁ := factorsThrough_gcd ψ₁ ψ₂ (hlift d₁ d₂ heq)
  have g₂ := factorsThrough_gcd ψ₂ ψ₁ (hlift d₂ d₁ heq.symm)
  have c₁ := conductor_dvd_of_mem_conductorSet ψ₁ g₁
  have c₂ := conductor_dvd_of_mem_conductorSet ψ₂ g₂
  rw [h₁] at c₁
  rw [h₂] at c₂
  have e : r₁ = r₂ := Nat.dvd_antisymm (c₁.trans (Nat.gcd_dvd_right _ _))
    (c₂.trans (Nat.gcd_dvd_right _ _))
  subst e
  have := changeLevel_injective d₁ heq
  subst this
  exact ⟨rfl, fun _ => rfl⟩

/-- The character of `(ℤ/N)ˣ` induced by a Dirichlet character of level dividing `N`. -/
def unitChar {N r : ℕ} (d : r ∣ N) (ψ : DirichletCharacter ℂ r) : (ZMod N)ˣ →* ℂ :=
  ((changeLevel d ψ : DirichletCharacter ℂ N) : ZMod N →* ℂ).comp (Units.coeHom (ZMod N))

theorem unitChar_apply {N r : ℕ} [NeZero N] (d : r ∣ N) (ψ : DirichletCharacter ℂ r) {v : ℕ}
    (hv : v.Coprime N) :
    unitChar d ψ (ZMod.unitOfCoprime v hv) = ψ (v : ZMod r) := by
  have := changeLevel_eq_cast_of_dvd ψ d (ZMod.unitOfCoprime v hv)
  rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast d] at this
  rw [← this]
  rfl

theorem changeLevel_eq_of_unitChar_eq {N r₁ r₂ : ℕ} (d₁ : r₁ ∣ N) (d₂ : r₂ ∣ N)
    {ψ₁ : DirichletCharacter ℂ r₁} {ψ₂ : DirichletCharacter ℂ r₂}
    (h : unitChar d₁ ψ₁ = unitChar d₂ ψ₂) : changeLevel d₁ ψ₁ = changeLevel d₂ ψ₂ := by
  apply MulChar.ext
  intro u
  have := DFunLike.congr_fun h u
  exact this

/-- **Certificate.** Serre–Stark's Theorem A implies the level-box residual. -/
theorem levelBox_of_theoremA (hA : SerreStarkTheoremA) : SerreStarkLevelBox24 := by
  intro N hN h24 r ψ t f hprim hrN ht htN hf hbox
  haveI : NeZero N := ⟨hN.ne'⟩
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  classical
  obtain ⟨m, r', t', ψ', c, hdata, hfe⟩ := hA N f hN h4 hf.1
  have hr'N : ∀ i, r' i ∣ N := fun i =>
    Dvd.dvd.trans (show r' i ∣ 4 * t' i * r' i ^ 2 from ⟨4 * t' i * r' i, by ring⟩)
      (hdata i).2.2.2
  have ht'N : ∀ i, t' i ∣ N := fun i =>
    Dvd.dvd.trans (show t' i ∣ 4 * t' i * r' i ^ 2 from ⟨4 * r' i ^ 2, by ring⟩)
      (hdata i).2.2.2
  -- coefficients of `f`
  set F : Fin m → ℕ → ℂ := fun i k => c i * charThetaCoeff (r' i) (ψ' i) (t' i) k with hF
  have hcoeff : ∀ k, thetaTypeCoeff f k = ∑ i, F i k := by
    intro k
    refine hf.1.coeff_eq_of_hasSum (c := fun n => ∑ i, F i n) (fun τ hτ => ?_) k
    rw [hfe τ hτ]
    have := hasSum_sum (s := Finset.univ) fun i _ =>
      (hasSum_charTheta (ψ' i) (hdata i).2.2.1 hτ).mul_left (c i)
    refine this.congr_fun fun k => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hF]
    ring
  -- the characters on `(ℤ/N)ˣ`
  set hom : Fin m → ((ZMod N)ˣ →* ℂ) := fun i => unitChar (hr'N i) (ψ' i) with hhom
  set ψh := unitChar hrN ψ with hψh
  set grp := Finset.univ.filter fun i => hom i = ψh with hgrp
  -- Step 1: `a(k) = Σ_{i ∈ grp} F i k` for `k > 0`
  have hstep1 : ∀ k, 0 < k → thetaTypeCoeff f k = ∑ i ∈ grp, F i k := by
    intro k hk
    have hid : ∀ u : (ZMod N)ˣ, ∑ i, F i k * hom i u = (∑ i, F i k) * ψh u := by
      intro u
      set v := (u : ZMod N).val
      have hv : v.Coprime N := ZMod.val_coe_unit_coprime u
      have hu : ZMod.unitOfCoprime v hv = u := by
        ext; rw [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]
      have hv0 : 0 < v := by
        rcases Nat.eq_zero_or_pos v with h | h
        · rw [h, Nat.coprime_zero_left] at hv
          subst hv; exact absurd h24 (by norm_num)
        · exact h
      have e := hf.2.2 k v hk hv
      rw [hcoeff, hcoeff] at e
      rw [← hu]
      simp only [hhom, hψh, unitChar_apply _ _ hv]
      rw [mul_comm _ (ψ (v : ZMod r)), ← e]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hF]
      rw [charThetaCoeff_mul_sq (ψ' i) hv0 (Nat.Coprime.coprime_dvd_right (ht'N i) hv)]
      ring
    set H : Finset ((ZMod N)ˣ →* ℂ) := insert ψh (Finset.univ.image hom) with hH
    set g : ((ZMod N)ˣ →* ℂ) → ℂ := fun h =>
      (∑ i ∈ Finset.univ.filter (fun i => hom i = h), F i k) -
        (if h = ψh then ∑ i, F i k else 0) with hg
    have hsum : ∑ h ∈ H, g h • (h : (ZMod N)ˣ → ℂ) = 0 := by
      funext u
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hg, sub_mul,
        Finset.sum_sub_distrib, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq' H ψh, if_pos (Finset.mem_insert_self _ _)]
      have hfib : ∑ h ∈ H, (∑ i ∈ Finset.univ.filter (fun i => hom i = h), F i k) * h u =
          ∑ i, F i k * hom i u := by
        rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := H) (g := hom)
          (fun i _ => Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.1 hi).2]
      rw [hfib, hid u, sub_self]
    have hg0 := (linearIndependent_iff'.1 (linearIndependent_monoidHom (ZMod N)ˣ ℂ)) H g hsum
      ψh (Finset.mem_insert_self _ _)
    simp only [hg, if_true, sub_eq_zero] at hg0
    rw [hcoeff, ← hg0]
  -- Step 2: in the group, `ψ'ᵢ = ψ` and `r'ᵢ = r`
  have hgrpval : ∀ i ∈ grp, r' i = r ∧ ∀ x : ℤ, ψ' i (x : ZMod (r' i)) = ψ (x : ZMod r) := by
    intro i hi
    have hi' : hom i = ψh := (Finset.mem_filter.1 hi).2
    exact primitive_unique (hdata i).1 hprim (hr'N i) hrN
      (changeLevel_eq_of_unitChar_eq _ _ hi')
  have hcθ : ∀ i ∈ grp, ∀ k, charThetaCoeff (r' i) (ψ' i) (t' i) k =
      charThetaCoeff r ψ (t' i) k := by
    intro i hi k
    unfold charThetaCoeff
    exact tsum_congr fun b => (hgrpval i hi).2 b
  -- Step 3: group by `T = t'ᵢ`
  set Ts := grp.image t' with hTs
  set E : ℕ → ℂ := fun T => ∑ i ∈ grp.filter (fun i => t' i = T), c i with hE
  have hstep3 : ∀ k, 0 < k → thetaTypeCoeff f k = ∑ T ∈ Ts, E T * charThetaCoeff r ψ T k := by
    intro k hk
    rw [hstep1 k hk, ← Finset.sum_fiberwise_of_maps_to (s := grp) (t := Ts) (g := t')
      (fun i hi => Finset.mem_image_of_mem _ hi)]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [hE, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨hig, hiT⟩ := Finset.mem_filter.1 hi
    simp only [hF]
    rw [hcθ i hig, hiT]
  -- Step 4: minimality
  by_cases hZ : ∀ T ∈ Ts, E T = 0
  · intro n hn
    rw [hstep3 n hn]
    exact Finset.sum_eq_zero fun T hT => by rw [hZ T hT, zero_mul]
  exfalso
  push Not at hZ
  set Z := Ts.filter fun T => E T ≠ 0 with hZdef
  have hZne : Z.Nonempty := by
    obtain ⟨T, hT, hET⟩ := hZ
    exact ⟨T, Finset.mem_filter.2 ⟨hT, hET⟩⟩
  set T₀ := Z.min' hZne with hT₀
  have hT₀Z : T₀ ∈ Z := Finset.min'_mem Z hZne
  obtain ⟨hT₀Ts, hET₀⟩ := Finset.mem_filter.1 hT₀Z
  obtain ⟨i₀, hi₀, hti₀⟩ := Finset.mem_image.1 hT₀Ts
  have hT₀pos : 1 ≤ T₀ := by rw [← hti₀]; exact (hdata i₀).2.2.1
  -- `ψ` is even
  have hev : ψ ((-1 : ℤ) : ZMod r) = 1 := by
    rw [← (hgrpval i₀ hi₀).2 (-1)]
    have := (hdata i₀).2.1
    rw [DirichletCharacter.Even] at this
    simpa using this
  -- `a(T₀) = 2 E(T₀)`
  have haT₀ : thetaTypeCoeff f T₀ = 2 * E T₀ := by
    rw [hstep3 T₀ (by omega), Finset.sum_eq_single_of_mem T₀ hT₀Ts]
    · rw [charThetaCoeff_self ψ hT₀pos, hev]
      simp; ring
    · intro T hT hne
      by_cases hET : E T = 0
      · rw [hET, zero_mul]
      · have hTZ : T ∈ Z := Finset.mem_filter.2 ⟨hT, hET⟩
        have hle : T₀ ≤ T := Finset.min'_le Z T hTZ
        have hlt : T₀ < T := lt_of_le_of_ne hle (Ne.symm hne)
        rw [charThetaCoeff_eq_zero_of_forall_ne ψ fun b hb => ?_, mul_zero]
        simp only [sqIdx] at hb
        rcases Nat.eq_zero_or_pos b.natAbs with h0 | h0
        · rw [h0] at hb; simp at hb; omega
        · have : T ≤ T * b.natAbs ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
          omega
  have hne : thetaTypeCoeff f T₀ ≠ 0 := by
    rw [haT₀]; exact mul_ne_zero two_ne_zero hET₀
  obtain ⟨x, hx⟩ := hf.2.1 T₀ (by omega) hne
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h] at hx; simp at hx; omega
    · exact h
  apply hne
  rw [hx]
  refine hbox x hx1 ⟨?_, ?_⟩
  · rw [DirichletCharacter.Even]
    simpa using hev
  · have := (hdata i₀).2.2.2
    rw [hti₀, hx, (hgrpval i₀ hi₀).1] at this
    simpa [mul_assoc] using this

end SSHecke

end VOA.Classification.COne
