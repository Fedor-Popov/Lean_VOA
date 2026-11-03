/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneSectorSparse

/-!
# Lie-theoretic checks from generators

For large types the Jacobi identity and the ad-stability of `I₂` are too expensive to check on every basis
element.  Both reduce to a generating set:

* **Jacobi.**  `ad u` is a derivation of the bracket (`IsDerB`) for `u` in a generating set; derivations are
  closed under brackets when the bracket is antisymmetric (`isDerB_bracket`), and a single-term bracket
  `[x_a, x_b] = k x_c` (`k ≠ 0`) transports the property to `x_c`.  Hence **`jacobiCoord_of_generators`**.
* **Stability.**  The polynomial derivations `D_x` (`X_a ↦ Σ_c f(x,a,c) X_c`) satisfy
  `⁅D_a, D_b⁆ = Σ_e f(a,b,e) D_e` (from Jacobi); a span stable under `D_a`, `D_b` is stable under `D_c` when
  `[x_a, x_b] = k x_c`.  Hence **`relationsStable_of_generators`**.

The generation data is a list of single-term brackets checked against a sparse integer table.
-/

namespace VOA.DeligneAudit.DeligneSector.Generate

open MvPolynomial VOA.DeligneAudit.SectorLoop VOA.QuadraticJetCoefficientPairing
open VOA.DeligneAudit.DeligneSector.Sparse

noncomputable section

variable {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ)

/-! ## The bracket on coordinate vectors -/

/-- The bracket of coordinate vectors. -/
def Bv (u v : Fin n → ℂ) : Fin n → ℂ := fun c => ∑ a, ∑ b, u a * v b * f a b c

theorem Bv_add_left (u u' v : Fin n → ℂ) : Bv f (u + u') v = Bv f u v + Bv f u' v := by
  funext c; simp only [Bv, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem Bv_add_right (u v v' : Fin n → ℂ) : Bv f u (v + v') = Bv f u v + Bv f u v' := by
  funext c; simp only [Bv, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem Bv_smul_left (k : ℂ) (u v : Fin n → ℂ) : Bv f (k • u) v = k • Bv f u v := by
  funext c; simp only [Bv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem Bv_smul_right (k : ℂ) (u v : Fin n → ℂ) : Bv f u (k • v) = k • Bv f u v := by
  funext c; simp only [Bv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem Bv_sub_left (u u' v : Fin n → ℂ) : Bv f (u - u') v = Bv f u v - Bv f u' v := by
  funext c; simp only [Bv, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem Bv_sub_right (u v v' : Fin n → ℂ) : Bv f u (v - v') = Bv f u v - Bv f u v' := by
  funext c; simp only [Bv, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem Bv_single (a b : Fin n) : Bv f (Pi.single a 1) (Pi.single b 1) = fun c => f a b c := by
  funext c
  simp only [Bv]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro b' _ hb; simp [Pi.single_apply, hb]
  · simp
  · intro a' _ ha; simp [Pi.single_apply, ha]
  · simp

theorem Bv_antisymm (hf : ∀ a b c, f a b c = -f b a c) (u v : Fin n → ℂ) :
    Bv f u v = -Bv f v u := by
  funext c
  simp only [Bv, Pi.neg_apply, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hf]; ring

/-- `ad u` is a derivation of the bracket. -/
def IsDerB (u : Fin n → ℂ) : Prop :=
  ∀ y z, Bv f u (Bv f y z) = Bv f (Bv f u y) z + Bv f y (Bv f u z)

variable {f}

theorem isDerB_bracket (hf : ∀ a b c, f a b c = -f b a c) {u u' : Fin n → ℂ} (hu : IsDerB f u)
    (hu' : IsDerB f u') : IsDerB f (Bv f u u') := by
  -- `ad [u,u'] = [ad u, ad u']`
  have hcomm : ∀ z, Bv f (Bv f u u') z = Bv f u (Bv f u' z) - Bv f u' (Bv f u z) := by
    intro z; rw [hu u' z]; abel
  intro y z
  rw [hcomm (Bv f y z), hcomm y, hcomm z, hu' y z, hu y z, Bv_add_right, Bv_add_right,
    hu (Bv f u' y) z, hu y (Bv f u' z), hu' (Bv f u y) z, hu' y (Bv f u z), Bv_sub_left,
    Bv_sub_right]
  abel

theorem isDerB_smul {u : Fin n → ℂ} (k : ℂ) (hk : k ≠ 0) (h : IsDerB f (k • u)) : IsDerB f u := by
  intro y z
  have := h y z
  simp only [Bv_smul_left, Bv_smul_right] at this
  rw [← smul_add] at this
  exact smul_right_injective _ hk this

theorem isDerB_of_basis {u : Fin n → ℂ}
    (h : ∀ b x, Bv f u (Bv f (Pi.single b 1) (Pi.single x 1)) =
      Bv f (Bv f u (Pi.single b 1)) (Pi.single x 1) + Bv f (Pi.single b 1) (Bv f u (Pi.single x 1))) :
    IsDerB f u := by
  intro y z
  have hy : y = ∑ b, y b • Pi.single b (1 : ℂ) := by
    funext c; simp [Finset.sum_apply, Pi.single_apply]
  have hz : z = ∑ x, z x • Pi.single x (1 : ℂ) := by
    funext c; simp [Finset.sum_apply, Pi.single_apply]
  have sumL : ∀ (s : Finset (Fin n)) (g : Fin n → Fin n → ℂ) v, Bv f (∑ i ∈ s, g i) v =
      ∑ i ∈ s, Bv f (g i) v := by
    intro s g v
    classical
    induction s using Finset.induction_on with
    | empty => funext c; simp [Bv]
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Bv_add_left, ih]
  have sumR : ∀ (s : Finset (Fin n)) (g : Fin n → Fin n → ℂ) v, Bv f v (∑ i ∈ s, g i) =
      ∑ i ∈ s, Bv f v (g i) := by
    intro s g v
    classical
    induction s using Finset.induction_on with
    | empty => funext c; simp [Bv]
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Bv_add_right, ih]
  rw [hy, hz]
  simp only [sumL, sumR, Bv_smul_left, Bv_smul_right, h, smul_add, Finset.sum_add_distrib]

theorem jacobiCoord_of_isDerB (h : ∀ a, IsDerB f (Pi.single a 1)) : JacobiCoord f := by
  intro a b x c
  have := congrFun (h a (Pi.single b 1) (Pi.single x 1)) c
  simp only [Bv_single] at this
  simp only [Bv, Pi.add_apply] at this
  have e1 : ∀ (u : Fin n) (g : Fin n → ℂ),
      (∑ a', ∑ b', (Pi.single u (1 : ℂ) : Fin n → ℂ) a' * g b' * f a' b' c) = ∑ d, g d * f u d c := by
    intro u g
    rw [Finset.sum_eq_single u]
    · simp
    · intro a' _ ha; simp [Pi.single_apply, ha]
    · simp
  have e2 : ∀ (u : Fin n) (g : Fin n → ℂ),
      (∑ a', ∑ b', g a' * (Pi.single u (1 : ℂ) : Fin n → ℂ) b' * f a' b' c) = ∑ d, g d * f d u c := by
    intro u g
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finset.sum_eq_single u]
    · simp
    · intro b' _ hb; simp [Pi.single_apply, hb]
    · simp
  rw [e1 a, e2 x, e1 b] at this
  -- `this : Σ_d f b x d f a d c = Σ_e f a b e f e x c + Σ_d f a x d f b d c`
  linear_combination -this

/-! ## Generation by single-term brackets -/

/-- Generation data: every index is a generator or a single-term bracket of earlier ones. -/
theorem induct_generation (P : ℕ → Prop) (G : List ℕ) (gen : List (ℕ × ℕ × ℕ × ℤ))
    (hG : ∀ g ∈ G, P g)
    (hstep : ∀ (pre : List (ℕ × ℕ × ℕ × ℤ)) (t : ℕ × ℕ × ℕ × ℤ), pre ++ [t] <+: gen →
      (∀ c ∈ G ++ pre.map (·.1), P c) → P t.2.1 → P t.2.2.1 → P t.1)
    (hmem : ∀ (pre : List (ℕ × ℕ × ℕ × ℤ)) (t : ℕ × ℕ × ℕ × ℤ), pre ++ [t] <+: gen →
      t.2.1 ∈ G ++ pre.map (·.1) ∧ t.2.2.1 ∈ G ++ pre.map (·.1)) :
    ∀ c ∈ G ++ gen.map (·.1), P c := by
  suffices key : ∀ k, k ≤ gen.length → ∀ c ∈ G ++ (gen.take k).map (·.1), P c by
    have := key gen.length le_rfl
    rwa [List.take_length] at this
  intro k
  induction k with
  | zero => intro _ c hc; simp at hc; exact hG c hc
  | succ k ih =>
    intro hk c hc
    have hk' : k < gen.length := by omega
    have hpre : gen.take k ++ [gen[k]] <+: gen := by
      rw [← List.take_succ_eq_append_getElem hk']; exact List.take_prefix _ _
    rw [List.take_succ_eq_append_getElem hk', List.map_append, ← List.append_assoc,
      List.mem_append] at hc
    rcases hc with hc | hc
    · exact ih (by omega) c hc
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
      subst hc
      have hP := ih (by omega)
      obtain ⟨h1, h2⟩ := hmem _ _ hpre
      exact hstep _ _ hpre hP (hP _ h1) (hP _ h2)

/-! ## Transport along single-term brackets -/

theorem Bv_single_eq (a b c : Fin n) (k : ℂ) (hab : ∀ e, f a b e = if e = c then k else 0) :
    Bv f (Pi.single a 1) (Pi.single b 1) = k • Pi.single c 1 := by
  rw [Bv_single]; funext e; simp [hab, Pi.single_apply]

theorem isDerB_of_bracket (hf : ∀ a b c, f a b c = -f b a c) {a b c : Fin n} {k : ℂ} (hk : k ≠ 0)
    (hab : ∀ e, f a b e = if e = c then k else 0) (ha : IsDerB f (Pi.single a 1))
    (hb : IsDerB f (Pi.single b 1)) : IsDerB f (Pi.single c 1) := by
  have := isDerB_bracket hf ha hb
  rw [Bv_single_eq a b c k hab] at this
  exact isDerB_smul k hk this

theorem isDerB_of_jac (a : Fin n)
    (h : ∀ b x c, (∑ d, f a x d * f b d c) - (∑ d, f b x d * f a d c) = -∑ e, f a b e * f e x c) :
    IsDerB f (Pi.single a 1) := by
  refine isDerB_of_basis fun b x => ?_
  simp only [Bv_single]
  funext c
  have := h b x c
  simp only [Bv, Pi.add_apply]
  have e1 : ∀ (u : Fin n) (g : Fin n → ℂ),
      (∑ a', ∑ b', (Pi.single u (1 : ℂ) : Fin n → ℂ) a' * g b' * f a' b' c) = ∑ d, g d * f u d c := by
    intro u g
    rw [Finset.sum_eq_single u]
    · simp
    · intro a' _ ha; simp [ha]
    · simp
  have e2 : ∀ (u : Fin n) (g : Fin n → ℂ),
      (∑ a', ∑ b', g a' * (Pi.single u (1 : ℂ) : Fin n → ℂ) b' * f a' b' c) = ∑ d, g d * f d u c := by
    intro u g
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finset.sum_eq_single u]
    · simp
    · intro b' _ hb; simp [hb]
    · simp
  rw [e1 a, e2 x, e1 b]
  linear_combination -this

/-! ## Polynomial derivations -/

variable (f) in
/-- The derivation `X_a ↦ Σ_c f(x,a,c) X_c`. -/
def Dx (x : Fin n) : Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ) :=
  MvPolynomial.mkDerivation ℂ (fun a => adX f x a)

theorem Dx_X (x a : Fin n) : Dx f x (X a) = adX f x a := MvPolynomial.mkDerivation_X _ _ _

theorem quadraticRelation_adMatrix_Dx (x : Fin n) (q : Fin n × Fin n → ℂ) :
    quadraticRelation (adMatrix f x q) = Dx f x (quadraticRelation q) := by
  rw [quadraticRelation_adMatrix_eq]
  unfold quadraticRelation
  rw [Fintype.sum_prod_type, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Derivation.map_smul, Derivation.leibniz, Dx_X, Dx_X, smul_eq_mul, smul_eq_mul]
  congr 1; ring

theorem sum_smul_adX (g : Fin n → ℂ) (G : Fin n → Fin n → ℂ) :
    (∑ c', g c' • ∑ c'', G c' c'' • (X c'' : MvPolynomial (Fin n) ℂ)) =
      ∑ c'', (∑ c', g c' * G c' c'') • X c'' := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem Dx_bracket (hJ : JacobiCoord f) (a b c : Fin n) (k : ℂ)
    (hab : ∀ e, f a b e = if e = c then k else 0) : ⁅Dx f a, Dx f b⁆ = k • Dx f c := by
  apply MvPolynomial.derivation_ext
  intro i
  rw [Derivation.commutator_apply, Derivation.smul_apply, Dx_X, Dx_X, Dx_X]
  simp only [adX, map_sum, Derivation.map_smul, Dx_X]
  rw [sum_smul_adX, sum_smul_adX, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c'' _ => ?_
  rw [← sub_smul, smul_smul]
  congr 1
  have hj := hJ a b i c''
  have hs : (∑ e, f a b e * f e i c'') = k * f c i c'' := by
    simp only [hab, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linear_combination -hj + hs

/-! ## Stability of a span -/

section Stable

variable {ρ : Type*} (Q : ρ → Fin n × Fin n → ℂ)

/-- The span of the relations. -/
abbrev Sp : Submodule ℂ (MvPolynomial (Fin n) ℂ) :=
  Submodule.span ℂ (Set.range fun s => quadraticRelation (Q s))

variable (f) in
/-- `D_x` preserves the span. -/
def StableD (x : Fin n) : Prop := ∀ p ∈ Sp Q, Dx f x p ∈ Sp Q

theorem stableD_of_gens {x : Fin n}
    (h : ∀ r, quadraticRelation (adMatrix f x (Q r)) ∈ Sp Q) : StableD f Q x := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨r, rfl⟩ := hw
    rw [← quadraticRelation_adMatrix_Dx]; exact h r
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul k u _ hu => rw [Derivation.map_smul]; exact Submodule.smul_mem _ _ hu

theorem stableD_of_bracket (hJ : JacobiCoord f) {a b c : Fin n} {k : ℂ} (hk : k ≠ 0)
    (hab : ∀ e, f a b e = if e = c then k else 0) (ha : StableD f Q a) (hb : StableD f Q b) :
    StableD f Q c := by
  intro p hp
  have hc := Dx_bracket hJ a b c k hab
  have e : Dx f c p = k⁻¹ • (⁅Dx f a, Dx f b⁆ p) := by
    rw [hc, Derivation.smul_apply, smul_smul, inv_mul_cancel₀ hk, one_smul]
  rw [e, Derivation.commutator_apply]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (ha _ (hb p hp)) (hb _ (ha p hp)))

theorem relationsStable_of_stableD (h : ∀ x, StableD f Q x) : RelationsStable f Q := by
  intro x r
  rw [quadraticRelation_adMatrix_Dx]
  exact h x _ (Submodule.subset_span ⟨r, rfl⟩)

end Stable

end

/-! ## Integer tables -/

section Int

variable {n : ℕ} {br : ℕ → ℕ → SV}

theorem fC_single {a b c : Fin n} {k : ℤ} (h : br a b = [((c : ℕ), k)]) :
    ∀ e, fC n br a b e = if e = c then ((k : ℤ) : ℂ) else 0 := by
  intro e
  simp only [fC, fZ, h, sget_cons, sget_nil, add_zero]
  by_cases he : e = c
  · subst he; simp
  · have : (c : ℕ) ≠ e := fun h' => he (Fin.ext h'.symm)
    simp [this, he]

theorem antisymm_of_check (h : ∀ a < n, ∀ b < n, zeroCheck (br a b ++ br b a) = true) :
    ∀ a b c : Fin n, fC n br a b c = -fC n br b a c := by
  intro a b c
  have := sget_eq_zero_of_check (h a a.2 b b.2) c
  rw [sget_append] at this
  simp only [fC, fZ]
  have : sget (br a b) c = -sget (br b a) c := by linarith
  rw [this]; push_cast; ring

theorem jac_at_of_check (hr : rangeCheck n br = true) (a b x : Fin n)
    (hj : zeroCheck (jacVec br a b x) = true) (c : Fin n) :
    (∑ d, fC n br a x d * fC n br b d c) - (∑ d, fC n br b x d * fC n br a d c) =
      -∑ e, fC n br a b e * fC n br e x c := by
  have h0 := sget_eq_zero_of_check hj (c : ℕ)
  simp only [jacVec, sget_append, sget_flatMap, sget_smulSV] at h0
  have h1 := congrArg (fun z : ℤ => (z : ℂ)) h0
  simp only [Int.cast_add, Int.cast_zero] at h1
  have A1 : ∑ d, fC n br a x d * fC n br b d c =
      ((br a x).map fun p => (p.2 : ℂ) * (fZ br b p.1 c : ℂ)).sum :=
    sum_fC_mul hr a x (fun k => (fZ br b k c : ℂ))
  have A2 : ∑ d, fC n br b x d * fC n br a d c =
      ((br b x).map fun p => (p.2 : ℂ) * (fZ br a p.1 c : ℂ)).sum :=
    sum_fC_mul hr b x (fun k => (fZ br a k c : ℂ))
  have A3 : ∑ e, fC n br a b e * fC n br e x c =
      ((br a b).map fun p => (p.2 : ℂ) * (fZ br p.1 x c : ℂ)).sum :=
    sum_fC_mul hr a b (fun k => (fZ br k x c : ℂ))
  rw [A1, A2, A3]
  simp only [castSum, Int.cast_mul, Int.cast_neg, neg_mul, negSum] at h1
  simp only [fZ]
  linear_combination h1

variable (n br) in
/-- The generation check: each entry `(c, a, b, k)` has `a, b` already seen and `[x_a, x_b] = k x_c`. -/
def genCheck : List (ℕ × ℕ × ℕ × ℤ) → List ℕ → Bool
  | [], _ => true
  | t :: rest, seen =>
    decide (t.2.1 ∈ seen) && decide (t.2.2.1 ∈ seen) && decide (t.1 < n) && decide (t.2.1 < n) &&
      decide (t.2.2.1 < n) && decide (t.2.2.2 ≠ 0) && decide (br t.2.1 t.2.2.1 = [(t.1, t.2.2.2)]) &&
      genCheck rest (t.1 :: seen)

/-- Propagation of a property along a checked generation list. -/
theorem induct_genCheck (P : Fin n → Prop)
    (hstep : ∀ (a b c : Fin n) (k : ℤ), k ≠ 0 → br a b = [((c : ℕ), k)] → P a → P b → P c) :
    ∀ (gen : List (ℕ × ℕ × ℕ × ℤ)) (seen : List ℕ), genCheck n br gen seen = true →
      (∀ c (h : c < n), c ∈ seen → P ⟨c, h⟩) →
      ∀ c (h : c < n), c ∈ seen ++ gen.map (·.1) → P ⟨c, h⟩ := by
  intro gen
  induction gen with
  | nil => intro seen _ hs c h hc; simp only [List.map_nil, List.append_nil] at hc; exact hs c h hc
  | cons t rest ih =>
    intro seen hg hs
    simp only [genCheck, Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, han⟩, hbn⟩, hk⟩, hbr⟩, hrest⟩ := hg
    have hPt : P ⟨t.1, hc⟩ :=
      hstep ⟨t.2.1, han⟩ ⟨t.2.2.1, hbn⟩ ⟨t.1, hc⟩ t.2.2.2 hk hbr (hs _ han ha) (hs _ hbn hb)
    have hs' : ∀ c (h : c < n), c ∈ t.1 :: seen → P ⟨c, h⟩ := by
      intro c h hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hPt
      · exact hs c h hc'
    have := ih (t.1 :: seen) hrest hs'
    intro c h hc'
    apply this c h
    simp only [List.map_cons, List.mem_append, List.mem_cons] at hc' ⊢
    tauto

/-- **Jacobi from generators.** -/
theorem jacobiCoord_of_generators (hr : rangeCheck n br = true)
    (hanti : ∀ a < n, ∀ b < n, zeroCheck (br a b ++ br b a) = true) (G : List ℕ)
    (hrow : ∀ g ∈ G, ∀ (hg : g < n), ∀ b < n, ∀ x < n, zeroCheck (jacVec br g b x) = true)
    (gen : List (ℕ × ℕ × ℕ × ℤ)) (hgen : genCheck n br gen G = true)
    (hcover : ∀ c < n, c ∈ G ++ gen.map (·.1)) : JacobiCoord (fC n br) := by
  have hf := antisymm_of_check hanti
  apply jacobiCoord_of_isDerB
  intro a
  refine induct_genCheck (P := fun a => IsDerB (fC n br) (Pi.single a 1)) ?_ gen G hgen ?_ a a.2
    (hcover a a.2)
  · intro a b c k hk hab ha hb
    exact isDerB_of_bracket hf (by exact_mod_cast hk) (fC_single hab) ha hb
  · intro g hg hgG
    exact isDerB_of_jac _ fun b x c => jac_at_of_check hr ⟨g, hg⟩ b x
      (hrow g hgG hg b b.2 x x.2) c

/-- **Stability from generators.** -/
theorem relationsStable_of_generators {ρ : Type*} (Q : ρ → Fin n × Fin n → ℂ)
    (hJ : JacobiCoord (fC n br)) (G : List ℕ) (gen : List (ℕ × ℕ × ℕ × ℤ))
    (hgen : genCheck n br gen G = true) (hcover : ∀ c < n, c ∈ G ++ gen.map (·.1))
    (hG : ∀ g ∈ G, ∀ (hg : g < n), ∀ r,
      quadraticRelation (adMatrix (fC n br) ⟨g, hg⟩ (Q r)) ∈ Sp Q) :
    RelationsStable (fC n br) Q := by
  apply relationsStable_of_stableD
  intro x
  refine induct_genCheck (P := fun a => StableD (fC n br) Q a) ?_ gen G hgen ?_ x x.2
    (hcover x x.2)
  · intro a b c k hk hab ha hb
    exact stableD_of_bracket Q hJ (by exact_mod_cast hk) (fC_single hab) ha hb
  · intro g hg hgG
    exact stableD_of_gens Q (hG g hgG hg)

end Int

/-! ## Coadjoint cyclicity from a word tree -/

section CycTree

variable {n : ℕ} [NeZero n] (br : ℕ → ℕ → SV) (rows : ℕ → List SV) (vecs : ℕ → SV)
  (cpar : ℕ → ℕ × ℕ × ℕ)

/-- Row-based coadjoint action: `(x·v)(y) = -Σ_{(d,k) ∈ [x,y]} k v_d`, reading the row of `x` once. -/
def slotZr (row : List SV) (v : SV) : SV :=
  row.zipIdx.map fun p => (p.2, -(p.1.map fun q => q.2 * sget v q.1).sum)

theorem sum_sget_swap (A B : SV) :
    (A.map fun p => sget B p.1 * p.2).sum = (B.map fun q => q.2 * sget A q.1).sum := by
  induction A with
  | nil => simp [sget]
  | cons p A ih =>
    simp only [List.map_cons, List.sum_cons, sget_cons, mul_add, List.sum_map_add, ← ih]
    congr 1
    unfold sget
    rw [← List.sum_map_mul_right]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    by_cases h : q.1 = p.1
    · simp [h, mul_comm]
    · simp [h, Ne.symm h]

theorem sget_slotZr (row : List SV) (v : SV) (y : ℕ) (hy : y < row.length) :
    sget (slotZr row v) y = -((row.getD y []).map fun q => q.2 * sget v q.1).sum := by
  unfold slotZr
  have key : ∀ (l : List SV) (k : ℕ), y < k + l.length → k ≤ y →
      sget ((l.zipIdx k).map fun p => (p.2, -(p.1.map fun q => q.2 * sget v q.1).sum)) y =
        -((l.getD (y - k) []).map fun q => q.2 * sget v q.1).sum := by
    intro l
    induction l with
    | nil => intro k h1 h2; simp at h1; omega
    | cons a l ih =>
      intro k h1 h2
      simp only [List.zipIdx_cons, List.map_cons, sget_cons]
      by_cases hk : k = y
      · subst hk
        simp only [if_true, Nat.sub_self, List.getD_cons_zero]
        have : sget ((l.zipIdx (k + 1)).map fun p => (p.2, -(p.1.map fun q => q.2 * sget v q.1).sum)) k
            = 0 := by
          unfold sget
          refine List.sum_eq_zero fun z hz => ?_
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
          have := List.mem_zipIdx hw
          have hne : w.2 ≠ k := by omega
          simp [hne]
        rw [this, add_zero]
      · rw [if_neg hk, zero_add, ih (k + 1) (by simp at h1 ⊢; omega) (by omega)]
        have : y - k = (y - (k + 1)) + 1 := by omega
        rw [this, List.getD_cons_succ]
  have := key row 0 (by omega) (Nat.zero_le _)
  simpa using this

omit [NeZero n] in
theorem vecC_slotZr {x : ℕ} {row : List SV} (hrow : row = (List.range n).map (br x)) (v : SV) :
    vecC n (slotZr row v) = vecC n (slotZ br n x v) := by
  funext y
  simp only [vecC]
  congr 1
  have hy : (y : ℕ) < row.length := by rw [hrow]; simp
  rw [sget_slotZr row v y hy, slotZ, sget_range, if_pos y.2]
  congr 1
  rw [hrow, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  unfold fZ
  rw [sum_sget_swap]

theorem sget_filter_ne (L : SV) (c : ℕ) : sget (L.filter fun p => p.2 != 0) c = sget L c := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [List.filter_cons]
    split_ifs with h
    · rw [sget_cons, sget_cons, ih]
    · simp only [bne_iff_ne, ne_eq, not_not] at h
      rw [sget_cons, ih, h]; simp

/-- Node `i` of a word tree: `vecs i = x · vecs parent`, depth bookkeeping. -/
def cycNodeCheck (n : ℕ) (i : ℕ) : Bool :=
  let p := cpar i
  decide (p.1 < i) && decide (p.2.1 < n) && decide (p.2.2 = (cpar p.1).2.2 + 1) &&
    svRange n (vecs p.1) && svRange n (vecs i) &&
    zeroCheck ((slotZr (rows p.2.1) (vecs p.1)).filter (fun p => p.2 != 0) ++ smulSV (-1) (vecs i))

variable {br rows vecs cpar}

theorem cycTree_word (hrows : ∀ x < n, rows x = (List.range n).map (br x)) (c₀ : Fin n)
    (hroot : vecs 0 = [((c₀ : ℕ), 1)]) (h0 : (cpar 0).2.2 = 0)
    (N : ℕ) (hnode : ∀ i, 0 < i → i < N → cycNodeCheck rows vecs cpar n i = true) :
    ∀ i, i < N → ∃ w : List (Fin n), w.length = (cpar i).2.2 ∧
      vecC n (vecs i) = wordA (fC n br) w (Pi.single c₀ 1) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hiN
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact ⟨[], by simp [h0], by rw [hroot, vecC_single]; rfl⟩
    · have hc := hnode i hi hiN
      simp only [cycNodeCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨hp, hx⟩, hd⟩, hrp⟩, hri⟩, hz⟩ := hc
      obtain ⟨w, hw, hv⟩ := ih (cpar i).1 hp (lt_trans hp hiN)
      refine ⟨⟨(cpar i).2.1, hx⟩ :: w, by simp [hw, hd], ?_⟩
      have heq := vecC_eq_of_check (n := n) hz
      have hfl : vecC n ((slotZr (rows (cpar i).2.1) (vecs (cpar i).1)).filter fun p => p.2 != 0) =
          vecC n (slotZr (rows (cpar i).2.1) (vecs (cpar i).1)) := by
        funext y; simp only [vecC, sget_filter_ne]
      rw [hfl] at heq
      rw [← heq, vecC_slotZr (br := br) (hrows _ hx), ← slotA_vecC ⟨(cpar i).2.1, hx⟩ _ hrp, hv]
      rfl

/-- **Coadjoint cyclicity from a word tree**: `Σ μ_j vecs_j = N e_c` with all depths `≤ L`. -/
theorem single_mem_slotWords_of_tree (hrows : ∀ x < n, rows x = (List.range n).map (br x))
    (c₀ : Fin n) (hroot : vecs 0 = [((c₀ : ℕ), 1)])
    (h0 : (cpar 0).2.2 = 0) (N : ℕ) (hnode : ∀ i, 0 < i → i < N → cycNodeCheck rows vecs cpar n i = true)
    (L : ℕ) (c : Fin n) (K : ℤ) (ws : List (ℕ × ℤ)) (hK : K ≠ 0)
    (hw : ∀ p ∈ ws, p.1 < N ∧ (cpar p.1).2.2 ≤ L)
    (hz : zeroCheck ((ws.flatMap fun p => smulSV p.2 (vecs p.1)) ++
      smulSV (-1) (smulSV K [((c : ℕ), 1)])) = true) :
    (Pi.single c 1 : Fin n → ℂ) ∈ slotWords (fC n br) c₀ L := by
  have hv := vecC_eq_of_check (n := n) hz
  rw [vecC_smul, vecC_single] at hv
  have hmem : vecC n (ws.flatMap fun p => smulSV p.2 (vecs p.1)) ∈ slotWords (fC n br) c₀ L := by
    rw [vecC_flatMap]
    refine list_sum_mem fun z hz' => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz'
    obtain ⟨h1, h2⟩ := hw p hp
    obtain ⟨w, hwl, hwv⟩ := cycTree_word hrows c₀ hroot h0 N hnode p.1 h1
    rw [vecC_smul, hwv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, by omega, rfl⟩)
  have hK' : ((K : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hK
  have : (Pi.single c 1 : Fin n → ℂ) = ((K : ℤ) : ℂ)⁻¹ •
      vecC n (ws.flatMap fun p => smulSV p.2 (vecs p.1)) := by
    rw [hv, smul_smul, inv_mul_cancel₀ hK', one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ hmem

end CycTree

end VOA.DeligneAudit.DeligneSector.Generate

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneSector.Generate.jacobiCoord_of_generators
#print axioms VOA.DeligneAudit.DeligneSector.Generate.relationsStable_of_generators
end AxiomAudit
