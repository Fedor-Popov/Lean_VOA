/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2SectorRep
import VOA.DeligneAudit.A2SectorFiber

/-!
# Homogeneous components on the current carrier

Degree projections commute with every linear map that shifts the polynomial degree uniformly.
Consequently the current carrier is graded (closed under homogeneous components), and the cyclic
loop-span `M_m` is spanned in each degree by the loop words of that degree.
-/

namespace VOA.DeligneAudit.SectorGraded

open MvPolynomial VOA.DeligneAuxiliaryCollision VOA.QuadraticCurrentFunctionalCarrier
open VOA.DeligneAudit.SectorLoop VOA.CollisionCommonFactors

noncomputable section

variable {K : Type*} [Field K]

/-- **Homogeneous components commute with degree-shifting linear maps.** -/
theorem homogeneousComponent_map_shift {A B : Type*}
    (L : MvPolynomial A K →ₗ[K] MvPolynomial B K) (n : ℕ)
    (hL : ∀ c (P : MvPolynomial A K), P.IsHomogeneous c → (L P).IsHomogeneous (c + n))
    (b : ℕ) (P : MvPolynomial A K) :
    homogeneousComponent b (L P) = if n ≤ b then L (homogeneousComponent (b - n) P) else 0 := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent P]
  rw [map_sum, map_sum]
  have hterm : ∀ i, homogeneousComponent b (L (homogeneousComponent i P)) =
      if i + n = b then L (homogeneousComponent i P) else 0 := by
    intro i
    rw [homogeneousComponent_of_mem (by
      rw [mem_homogeneousSubmodule]; exact hL i _ (homogeneousComponent_isHomogeneous i P))]
    by_cases h : i + n = b
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (Ne.symm h), if_neg h]
  simp only [hterm]
  split_ifs with hnb
  · by_cases hmem : b - n ∈ Finset.range (P.totalDegree + 1)
    · rw [Finset.sum_eq_single (b - n)]
      · rw [if_pos (by omega)]
      · intro i _ hi; rw [if_neg (by omega)]
      · intro h; exact absurd hmem h
    · rw [homogeneousComponent_eq_zero _ _ (by simp at hmem; omega), map_zero]
      exact Finset.sum_eq_zero fun i hi => by
        rw [if_neg]; intro h; simp at hi hmem; omega
  · exact Finset.sum_eq_zero fun i _ => by rw [if_neg (by omega)]

/-! ## Tensor polynomials -/

section Tensor

variable {σ ρ : Type*} [Fintype σ] [DecidableEq σ] {m : ℕ}

/-- The degree-`b` projection of a tensor polynomial. -/
def projT (b : ℕ) : TensorPolynomial (K := K) (σ := σ) m 0 →ₗ[K]
    TensorPolynomial (K := K) (σ := σ) m 0 where
  toFun p t := homogeneousComponent b (p t)
  map_add' p q := by funext t; simp
  map_smul' a p := by funext t; simp

/-- A tensor polynomial homogeneous of degree `c` in every component. -/
def IsHomT (c : ℕ) (p : TensorPolynomial (K := K) (σ := σ) m 0) : Prop :=
  ∀ t, (p t).IsHomogeneous c

omit [Fintype σ] [DecidableEq σ] in
theorem projT_of_isHomT {c : ℕ} {p : TensorPolynomial (K := K) (σ := σ) m 0} (hp : IsHomT c p)
    (b : ℕ) : projT b p = if b = c then p else 0 := by
  funext t
  change homogeneousComponent b (p t) = _
  rw [homogeneousComponent_of_mem (by rw [mem_homogeneousSubmodule]; exact hp t)]
  split_ifs <;> rfl

omit [Fintype σ] [DecidableEq σ] in
theorem isHomT_projT (b : ℕ) (p : TensorPolynomial (K := K) (σ := σ) m 0) :
    IsHomT b (projT b p) := fun t => homogeneousComponent_isHomogeneous b (p t)

theorem rename_homogeneousComponent {A B : Type*} (g : A → B) (b : ℕ) (P : MvPolynomial A K) :
    rename g (homogeneousComponent b P) = homogeneousComponent b (rename g P) := by
  have h := homogeneousComponent_map_shift (rename g).toLinearMap 0
    (fun c P hP => by simpa using hP.rename_isHomogeneous) b P
  simp only [AlgHom.toLinearMap_apply, Nat.zero_le, if_true, Nat.sub_zero] at h
  exact h.symm

omit [DecidableEq σ] in
/-- **The current carrier is graded.** -/
theorem projT_mem_carrier {Q : ρ → σ × σ → K} {p : TensorPolynomial (K := K) (σ := σ) m 0}
    (hp : p ∈ currentCarrier Q m 0) (b : ℕ) : projT b p ∈ currentCarrier Q m 0 := by
  refine ⟨fun e g he t => ?_, fun r ij t => ?_⟩
  · change rename e (homogeneousComponent b (p t)) = homogeneousComponent b (p (t ∘ g.symm))
    rw [rename_homogeneousComponent, hp.1 e g he t]
  · have h0 := hp.2 r ij t
    unfold currentReadback projectedDiagonal at h0 ⊢
    change ∑ xy, MvPolynomial.C (Q r xy) * collisionMap _ _ _ (homogeneousComponent b (p (insertPair ij t xy)))
      = 0
    simp only [collisionMap, rename_homogeneousComponent, ← homogeneousComponent_C_mul]
    rw [← map_sum]
    simp only [collisionMap] at h0
    rw [h0, map_zero]

end Tensor

/-! ## Degrees of loop words -/

section Words

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (f : σ → σ → σ → K) {m : ℕ}

/-- The `t`-degree of a loop word. -/
def wordDeg (l : List (σ × ℕ)) : ℕ := (l.map Prod.snd).sum

omit [DecidableEq σ] in
theorem isHomT_loopOp {c : ℕ} {p : TensorPolynomial (K := K) (σ := σ) m 0} (hp : IsHomT c p)
    (x : σ) (r : ℕ) : IsHomT (c + r) (loopOp f m x r p) := by
  intro t
  rw [← mem_homogeneousSubmodule]
  refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => ?_)
  rw [mem_homogeneousSubmodule, add_comm]
  refine ((isHomogeneous_X_pow _ r).mul ?_)
  rw [← mem_homogeneousSubmodule]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [mem_homogeneousSubmodule]
  simpa using (isHomogeneous_C _ _).mul (hp (Function.update t i d))

omit [Fintype σ] in
theorem isHomT_deltaVec (c₀ : σ) : IsHomT 0 (deltaVec (K := K) m c₀) := by
  intro t
  simp only [deltaVec]
  split_ifs
  · exact isHomogeneous_one _ _
  · exact isHomogeneous_zero _ _ _

theorem isHomT_applyWord (c₀ : σ) :
    ∀ l : List (σ × ℕ), IsHomT (wordDeg l) (applyWord f m l (deltaVec (K := K) m c₀))
  | [] => isHomT_deltaVec c₀
  | (xs :: l) => by
      have h := isHomT_loopOp f (isHomT_applyWord c₀ l) xs.1 xs.2
      simpa [wordDeg, applyWord, add_comm] using h

/-- The span of the loop words of `t`-degree `b`. -/
def wordSpan (c₀ : σ) (b : ℕ) : Submodule K (TensorPolynomial (K := K) (σ := σ) m 0) :=
  Submodule.span K {v | ∃ l, wordDeg l = b ∧ v = applyWord f m l (deltaVec m c₀)}

/-- **The degree-`b` part of `M_m` is spanned by the loop words of degree `b`.** -/
theorem projT_mem_wordSpan (c₀ : σ) (b : ℕ) {x : TensorPolynomial (K := K) (σ := σ) m 0}
    (hx : x ∈ Mspace f m c₀) : projT b x ∈ wordSpan f c₀ b := by
  induction hx using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      rw [projT_of_isHomT (isHomT_applyWord f c₀ l)]
      split_ifs with h
      · exact Submodule.subset_span ⟨l, h.symm, rfl⟩
      · exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem wordSpan_le_Mspace (c₀ : σ) (b : ℕ) : wordSpan f c₀ b ≤ Mspace (K := K) f m c₀ := by
  rw [wordSpan, Submodule.span_le]
  rintro _ ⟨l, _, rfl⟩
  exact Submodule.subset_span ⟨l, rfl⟩

theorem wordSpan_isHomT (c₀ : σ) (b : ℕ) {x : TensorPolynomial (K := K) (σ := σ) m 0}
    (hx : x ∈ wordSpan f c₀ b) : IsHomT b x := by
  intro t
  rw [← mem_homogeneousSubmodule]
  induction hx using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      rw [mem_homogeneousSubmodule, ← hl]
      exact isHomT_applyWord f c₀ l t
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

end Words

end

end VOA.DeligneAudit.SectorGraded
