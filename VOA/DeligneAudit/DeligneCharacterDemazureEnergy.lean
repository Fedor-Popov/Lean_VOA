/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterDemazureCount

/-!
# Energy nonnegativity of `demazureChar` from a convexity invariant

Let `F` be a finite set of linear functionals on root coordinates (in practice the `W`-orbit of the
coroot `θ^∨`, i.e. `φ ↦ ⟨·, β^∨⟩` for long `β`), stable under the reflections of the word and under
`s_θ`, containing `-θ^∨`, with `φ(θ) ≤ 2`.  Then every term `z^μ q^e` of `C_m = demazureChar … m` satisfies

* `φ(μ) ≤ 2m` for all `φ ∈ F` (the weights stay in `conv(W·mθ)`), and
* `e ≥ -m²` (**the energy bound**: after regrading by `m²`, all degrees are `≥ 0`).

Finite operators move weights along `α_i`-strings between `μ` and `s_i μ` (the bound is preserved by
convexity and `F`-stability) and keep `e`.  The affine `D_0` sends `μ ∈ K_{m-1}` to `μ + kθ`,
`0 ≤ k ≤ 1 - ⟨μ, θ^∨⟩ ≤ 2m - 1`, lowering `e` by `k`; so `-(m-1)² - (2m-1) = -m²`.

This proves `D4Wp.energy_holds`-type statements for any type from decidable data checks; for `G₂` it
discharges `G2DemazureEnergy`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.DemCount

open VOA.DeligneAudit.DeligneCharacter Finset

variable {r : ℕ}

/-- A functional (coefficient list) evaluated on root coordinates. -/
def fv (φ : List ℤ) (v : Wt r) : ℤ := ∑ j : Fin r, φ.getD j 0 * v j

theorem fv_add_smul (φ : List ℤ) (v w : Wt r) (c : ℤ) : fv φ (v + c • w) = fv φ v + c * fv φ w := by
  simp only [fv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, sum_add_distrib, mul_sum]
  congr 1; refine sum_congr rfl fun j _ => by ring

theorem fv_zero (φ : List ℤ) : fv φ (0 : Wt r) = 0 := by simp [fv]

theorem fv_eAt (φ : List ℤ) (i : ℕ) (hi : i < r) : fv φ (eAt r i) = φ.getD i 0 := by
  rw [fv, sum_eq_single ⟨i, hi⟩]
  · simp [eAt]
  · intro j _ hj
    have : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
    simp [eAt, this]
  · simp

/-- `φ ∘ s_i` as a coefficient list. -/
def reflFunFin (r : ℕ) (A : List (List ℤ)) (i : ℕ) (φ : List ℤ) : List ℤ :=
  List.ofFn fun j : Fin r => φ.getD j 0 - φ.getD i 0 * (A.getD i []).getD j 0

/-- `φ ∘ s_θ` as a coefficient list. -/
def reflFunTheta (r : ℕ) (A : List (List ℤ)) (θ : List ℤ) (φ : List ℤ) : List ℤ :=
  List.ofFn fun j : Fin r =>
    φ.getD j 0 - (List.zipWith (· * ·) φ θ).sum * (aTheta A θ).getD j 0

/-- `-θ^∨`. -/
def negTheta (r : ℕ) (A : List (List ℤ)) (θ : List ℤ) : List ℤ :=
  List.ofFn fun j : Fin r => -(aTheta A θ).getD j 0

theorem getD_ofFn (g : Fin r → ℤ) (j : Fin r) : (List.ofFn g).getD j 0 = g j := by
  simp [List.getD_eq_getElem?_getD]

/-- `⟨v, θ^∨⟩` in the coordinates of `demazureZeroTerm`. -/
def pTheta (A : List (List ℤ)) (θ : List ℤ) (v : Wt r) : ℤ := ∑ j : Fin r, (aTheta A θ).getD j 0 * v j

theorem fv_reflFunFin (A : List (List ℤ)) (i : ℕ) (φ : List ℤ) (v : Wt r) :
    fv (reflFunFin r A i φ) v = fv φ v - φ.getD i 0 * pFin A i v := by
  simp only [fv, reflFunFin, getD_ofFn, pFin, AddMonoidHom.coe_mk, ZeroHom.coe_mk, mul_sum,
    ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => by ring

theorem fv_theta (φ θ : List ℤ) (hθ : θ.length = r) :
    (List.zipWith (· * ·) φ θ).sum = fv φ (vec r θ) := by
  rw [sum_zipWith_mul, sum_range_eq_fin _ _ hθ]; rfl

theorem fv_reflFunTheta (A : List (List ℤ)) (θ : List ℤ) (hθ : θ.length = r) (φ : List ℤ)
    (v : Wt r) : fv (reflFunTheta r A θ φ) v = fv φ v - fv φ (vec r θ) * pTheta A θ v := by
  simp only [fv, reflFunTheta, getD_ofFn, pTheta, fv_theta φ θ hθ, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => by ring

theorem fv_negTheta (A : List (List ℤ)) (θ : List ℤ) (v : Wt r) :
    fv (negTheta r A θ) v = -pTheta A θ v := by
  simp only [fv, negTheta, getD_ofFn, pTheta, ← sum_neg_distrib]
  refine sum_congr rfl fun j _ => by ring

/-- Linear interpolation along a string. -/
theorem string_le (x y C : ℤ) (n k : ℕ) (hx : x ≤ C) (hy : x - n * y ≤ C) (hk : k ≤ n) :
    x - k * y ≤ C := by
  have hk' : (k : ℤ) ≤ n := by exact_mod_cast hk
  rcases le_total 0 y with h | h
  · nlinarith [Int.natCast_nonneg k]
  · nlinarith

/-- The invariant at level `m` for one term. -/
def PInv (F : List (List ℤ)) (m : ℕ) (t : Term) : Prop :=
  (∀ φ ∈ F, fv φ (vec r t.1.1) ≤ 2 * m) ∧ -((m : ℤ) * m) ≤ t.1.2

/-- The data conditions (all decidable). -/
structure OrbitData (r : ℕ) (A : List (List ℤ)) (θ : List ℤ) (word : List ℕ) (F : List (List ℤ)) :
    Prop where
  hθ : θ.length = r
  hw : ∀ i ∈ word, i < r
  hFin : ∀ i ∈ word, ∀ φ ∈ F, reflFunFin r A i φ ∈ F
  hFθ : ∀ φ ∈ F, reflFunTheta r A θ φ ∈ F
  hneg : negTheta r A θ ∈ F
  hθ2 : ∀ φ ∈ F, (List.zipWith (· * ·) φ θ).sum ≤ 2

/-- `OrbitData` from stability under the simple letters `i < r` only (the word's letters are among them). -/
theorem OrbitData.of_letters {A : List (List ℤ)} {θ : List ℤ} {word : List ℕ} {F : List (List ℤ)}
    (hθ : θ.length = r) (hw : ∀ i ∈ word, i < r)
    (hFin : ∀ i, i < r → ∀ φ ∈ F, reflFunFin r A i φ ∈ F)
    (hFθ : ∀ φ ∈ F, reflFunTheta r A θ φ ∈ F) (hneg : negTheta r A θ ∈ F)
    (hθ2 : ∀ φ ∈ F, (List.zipWith (· * ·) φ θ).sum ≤ 2) : OrbitData r A θ word F :=
  ⟨hθ, hw, fun i hi => hFin i (hw i hi), hFθ, hneg, hθ2⟩

theorem mem_normalize_key (f : LPoly) (x : Term) (hx : x ∈ normalize f) : ∃ s ∈ f, x.1 = s.1 := by
  have key : ∀ f : LPoly, ∀ x ∈ f.foldr addTerm [], ∃ s ∈ f, x.1 = s.1 := by
    intro f
    induction f with
    | nil => intro x hx; simp at hx
    | cons s f ih =>
      intro x hx
      rw [List.foldr_cons] at hx
      rcases mem_addTerm _ _ _ hx with h | h
      · exact ⟨s, List.mem_cons_self, h⟩
      · obtain ⟨u, hu, hxu⟩ := ih x h
        exact ⟨u, List.mem_cons_of_mem _ hu, hxu⟩
  exact key f x (List.mem_filter.mp hx).1

section
variable {A : List (List ℤ)} {θ : List ℤ} {word : List ℕ} {F : List (List ℤ)}

theorem PInv_fin (hD : OrbitData r A θ word F) (i : ℕ) (hi : i ∈ word) (m : ℕ) (t : Term)
    (ht : t.1.1.length = r) (hP : PInv (r := r) F m t) :
    ∀ x ∈ demazureFinTerm A i t, PInv (r := r) F m x := by
  intro x hx
  have hir := hD.hw i hi
  unfold demazureFinTerm at hx
  dsimp only at hx
  have hpair := pairCoroot_eq (r := r) A i t.1.1 ht
  split_ifs at hx with h
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    refine ⟨fun φ hφ => ?_, hP.2⟩
    simp only
    rw [vec_shiftAt _ ht, fv_add_smul, fv_eAt _ _ hir]
    have h1 := hP.1 φ hφ
    have h2 := hP.1 _ (hD.hFin i hi φ hφ)
    rw [fv_reflFunFin, ← hpair] at h2
    have hn : (pairCoroot A i t.1.1) = ((pairCoroot A i t.1.1).toNat : ℤ) :=
      (Int.toNat_of_nonneg h).symm
    have := string_le (fv φ (vec r t.1.1)) (φ.getD i 0) (2 * m) (pairCoroot A i t.1.1).toNat k h1
      (by rw [← hn]; linarith) (by simpa [Nat.lt_succ_iff] using List.mem_range.mp hk)
    push_cast at this ⊢; linarith
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    refine ⟨fun φ hφ => ?_, by simpa using hP.2⟩
    simp only
    rw [vec_shiftAt _ ht, fv_add_smul, fv_eAt _ _ hir]
    have h1 := hP.1 φ hφ
    have h2 := hP.1 _ (hD.hFin i hi φ hφ)
    rw [fv_reflFunFin, ← hpair] at h2
    have hk' := List.mem_range.mp hk
    have hn : -(pairCoroot A i t.1.1) = ((-pairCoroot A i t.1.1).toNat : ℤ) :=
      (Int.toNat_of_nonneg (by omega)).symm
    have := string_le (fv φ (vec r t.1.1)) (-φ.getD i 0) (2 * m) (-pairCoroot A i t.1.1).toNat
      (k + 1) h1 (by rw [← hn]; linarith) (by omega)
    push_cast at this ⊢; linarith

theorem PInv_zero (hD : OrbitData r A θ word F) (m : ℕ) (t : Term)
    (ht : t.1.1.length = r) (hP : PInv (r := r) F m t) :
    ∀ x ∈ demazureZeroTerm A θ t, PInv (r := r) F (m + 1) x := by
  intro x hx
  unfold demazureZeroTerm at hx
  dsimp only at hx
  have hpθ : (List.zipWith (· * ·) ((List.range θ.length).map fun i => pairCoroot A i θ) t.1.1).sum =
      pTheta A θ (vec r t.1.1) := by
    rw [sum_zipWith_mul, sum_range_eq_fin _ _ ht]; rfl
  rw [hpθ] at hx
  have hneg := hP.1 _ hD.hneg
  rw [fv_negTheta] at hneg
  split_ifs at hx with h
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have hk' := List.mem_range.mp hk
    have hn : 1 - pTheta A θ (vec r t.1.1) = ((1 - pTheta A θ (vec r t.1.1)).toNat : ℤ) :=
      (Int.toNat_of_nonneg h).symm
    refine ⟨fun φ hφ => ?_, ?_⟩
    · simp only
      rw [vec_shiftTheta _ _ ht hD.hθ, fv_add_smul]
      have hφθ : fv φ (vec r θ) ≤ 2 := by rw [← fv_theta φ θ hD.hθ]; exact hD.hθ2 φ hφ
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · have := hP.1 φ hφ; push_cast; linarith
      · have h1 := hP.1 φ hφ
        have h2 := hP.1 _ (hD.hFθ φ hφ)
        rw [fv_reflFunTheta _ _ hD.hθ] at h2
        have hn' : -pTheta A θ (vec r t.1.1) = ((-pTheta A θ (vec r t.1.1)).toNat : ℤ) :=
          (Int.toNat_of_nonneg (by omega)).symm
        have := string_le (fv φ (vec r t.1.1)) (-fv φ (vec r θ)) (2 * m)
          (-pTheta A θ (vec r t.1.1)).toNat (k - 1) h1 (by rw [← hn']; linarith) (by omega)
        have hk1 : ((k - 1 : ℕ) : ℤ) = k - 1 := by omega
        rw [hk1] at this
        push_cast at this ⊢
        nlinarith
    · simp only
      push_cast
      have : (k : ℤ) ≤ 1 - pTheta A θ (vec r t.1.1) := by omega
      nlinarith [hP.2]
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have hk' := List.mem_range.mp hk
    refine ⟨fun φ hφ => ?_, ?_⟩
    · simp only
      rw [vec_shiftTheta _ _ ht hD.hθ, fv_add_smul]
      have h1 := hP.1 φ hφ
      have h2 := hP.1 _ (hD.hFθ φ hφ)
      rw [fv_reflFunTheta _ _ hD.hθ] at h2
      have hn' : pTheta A θ (vec r t.1.1) = ((pTheta A θ (vec r t.1.1)).toNat : ℤ) :=
        (Int.toNat_of_nonneg (by omega)).symm
      have := string_le (fv φ (vec r t.1.1)) (fv φ (vec r θ)) (2 * m)
        (pTheta A θ (vec r t.1.1)).toNat (k + 1) h1 (by rw [← hn']; linarith) (by omega)
      push_cast at this ⊢
      nlinarith
    · simp only
      have := hP.2
      push_cast
      nlinarith

theorem PInv_normalize (F : List (List ℤ)) (m : ℕ) (f : LPoly) (hf : ∀ t ∈ f, PInv (r := r) F m t) :
    ∀ t ∈ normalize f, PInv (r := r) F m t := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_normalize_key f x hx
  have := hf s hs
  unfold PInv at this ⊢
  rw [hxs]; exact this

theorem PInv_step (hD : OrbitData r A θ word F) (m : ℕ) (f : LPoly) (hf : Good r f)
    (hP : ∀ t ∈ f, PInv (r := r) F m t) :
    ∀ t ∈ demazureStep A θ word f, PInv (r := r) F (m + 1) t := by
  unfold demazureStep
  have hz : ∀ t ∈ demazureZero A θ f, PInv (r := r) F (m + 1) t := by
    apply PInv_normalize
    intro x hx
    obtain ⟨t, ht, hx⟩ := List.mem_flatMap.mp hx
    exact PInv_zero hD m t (hf t ht) (hP t ht) x hx
  have hgood := (toR1_demazureZero A θ hD.hθ f hf).2
  have key : ∀ w : List ℕ, (∀ i ∈ w, i ∈ word) →
      Good r (w.foldr (fun i g => demazureFin A i g) (demazureZero A θ f)) ∧
      ∀ t ∈ w.foldr (fun i g => demazureFin A i g) (demazureZero A θ f),
        PInv (r := r) F (m + 1) t := by
    intro w
    induction w with
    | nil => intro _; exact ⟨hgood, hz⟩
    | cons i w ih =>
      intro hw
      obtain ⟨g1, g2⟩ := ih (fun j hj => hw j (List.mem_cons_of_mem _ hj))
      simp only [List.foldr_cons]
      refine ⟨(toR1_demazureFin A i _ g1).2, ?_⟩
      apply PInv_normalize
      intro x hx
      obtain ⟨t, ht, hx⟩ := List.mem_flatMap.mp hx
      exact PInv_fin hD i (hw i List.mem_cons_self) (m + 1) t (g1 t ht) (g2 t ht) x hx
  exact (key word fun _ h => h).2

/-- **Energy nonnegativity** of `demazureChar` from the orbit data. -/
theorem energy_of_orbit (hD : OrbitData r A θ word F) (m : ℕ) :
    ∀ t ∈ demazureChar A θ word m, 0 ≤ t.1.2 + (m : ℤ) * m := by
  have key : ∀ m, ∀ t ∈ demazureChar A θ word m, PInv (r := r) F m t := by
    intro m
    induction m with
    | zero =>
      intro t ht
      simp only [demazureChar, Function.iterate_zero, id, List.mem_singleton] at ht
      subst ht
      have : vec r (List.replicate θ.length 0) = 0 := by
        funext j; simp [vec, List.getD_eq_getElem?_getD, List.getElem?_replicate]; split_ifs <;> rfl
      refine ⟨fun φ _ => ?_, by simp⟩
      simp only; rw [this, fv_zero]; simp
    | succ m ih =>
      have e : demazureChar A θ word (m + 1) = demazureStep A θ word (demazureChar A θ word m) := by
        simp only [demazureChar, Function.iterate_succ_apply']
      rw [e]
      exact PInv_step hD m _ (toR1_demazureChar A θ hD.hθ word m).2 ih
  intro t ht
  have := (key m t ht).2
  linarith

end

end VOA.DeligneAudit.DeligneCharacter.DemCount
