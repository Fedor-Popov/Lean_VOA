/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneSectorData
import VOA.DeligneAudit.A2SectorWeylRel

/-!
# Type-generic local Weyl relations, input U5, and the generator computations

For sector data `S`: the local Weyl and fusion relations of `W_loc(mθ)` (`LocalWeylRelG`), input
U5 in its smallest form with the total-dimension field `≤ (dim g)^m` (`FusionModuleBoundG`), and the
action of the loop operators on the constant vector `δ_{c₀}`: raising operators kill it, Cartan
operators act by `θ(h) p_r(z)`, Vieta gives `f ⊗ t^m δ ∈ B₊·(loop words)`, and the weight data kill
`(f_i ⊗ 1)^{mθ(h_i)+1} δ`.
-/

namespace VOA.DeligneAudit.DeligneSector

open MvPolynomial VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.SectorFiber VOA.DeligneAudit.SectorFiberModule
open VOA.DeligneAudit.A2 (psumS esymmS psumS_mem esymmS_mem vieta_zero)
open VOA.QuadraticCurrentFunctionalCarrier

noncomputable section

variable (S : DeligneSectorData)

/-- Tensor polynomials for the type. -/
abbrev TPs (m : ℕ) := TensorPolynomial (K := ℂ) (σ := Fin S.n) m 0

/-- **The local Weyl and fusion relations of `W_loc(mθ)`** for the type. -/
structure LocalWeylRelG {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule S.f V) (w : V) (m : ℕ) : Prop where
  raising : ∀ e, S.raising e → ∀ r, ρ.op e r w = 0
  cartan_pos : ∀ h, S.cartan h → ∀ r, 1 ≤ r → ρ.op h r w = 0
  cartan_zero : ∀ h, S.cartan h → ρ.op h 0 w = ((m * S.thetaH h : ℕ) : ℂ) • w
  lowering : ∀ i, S.lowering i → (ρ.op i 0)^[m * S.lowExp i + 1] w = 0
  fusion : ∀ x, S.fusion x → ρ.op x m w = 0
  cartanN_pos : ∀ h, S.cartanN h → ∀ r, 1 ≤ r → ρ.op h r w = 0
  cartanN_zero : ∀ h, S.cartanN h → ρ.op h 0 w = -((m * S.thetaN h : ℕ) : ℂ) • w

/-- **Input U5 (smallest form) for the type**: every module satisfying the relations has graded
dimension `≤ [q^b] F_m` and total dimension `≤ (dim g)^m`. -/
structure FusionModuleBoundG (F : ℕ → PowerSeries ℚ) : Prop where
  le : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
    LocalWeylRelG S ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ PowerSeries.coeff b (F m)
  total : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
    LocalWeylRelG S ρ w m → ∀ B : ℕ,
      ∑ b ∈ Finset.range B, Module.finrank ℂ (cycDeg ρ w b) ≤ S.n ^ m

/-! ## The generator -/

theorem deltaVec_update (m : ℕ) (t : Fin m → Fin S.n) (i : Fin m) (c c₀ : Fin S.n) :
    deltaVec (K := ℂ) m c₀ (Function.update t i c) =
      if c = c₀ ∧ ∀ j, j ≠ i → t j = c₀ then 1 else 0 := by
  simp only [deltaVec]
  congr 1
  apply propext
  constructor
  · intro h
    refine ⟨by simpa using congrFun h i, fun j hj => ?_⟩
    have := congrFun h j
    rwa [Function.update_of_ne hj] at this
  · rintro ⟨rfl, h⟩
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj, h j hj]

theorem loopOp_deltaVec_apply (m : ℕ) (x : Fin S.n) (r : ℕ) (t : Fin m → Fin S.n) :
    loopOp S.f m x r (deltaVec m S.c₀) t =
      -∑ i, if ∀ j, j ≠ i → t j = S.c₀ then
        zr i ^ r * MvPolynomial.C (S.f x (t i) S.c₀) else 0 := by
  simp only [loopOp, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [deltaVec_update, mul_ite, mul_one, mul_zero]
  by_cases h : ∀ j, ¬ j = i → t j = S.c₀
  · rw [if_pos h]
    have h' : ∀ j, j ≠ i → t j = S.c₀ := h
    simp only [show (∀ j, j ≠ i → t j = S.c₀) ↔ True from iff_true_intro h', and_true]
    rw [Finset.sum_ite_eq' Finset.univ S.c₀, if_pos (Finset.mem_univ _)]
  · rw [if_neg h]
    simp only [h, and_false, if_false, Finset.sum_const_zero, mul_zero]

theorem loopOp_raising_deltaVec (m : ℕ) (e : Fin S.n) (he : S.raising e) (r : ℕ) :
    loopOp S.f m e r (deltaVec m S.c₀) = 0 := by
  funext t
  rw [loopOp_deltaVec_apply]
  simp [S.raising_table e he]

theorem loopOp_cartan_deltaVec (m : ℕ) (h : Fin S.n) (hh : S.cartan h) (r : ℕ) :
    loopOp S.f m h r (deltaVec m S.c₀) =
      ((S.thetaH h : ℕ) : ℂ) • (psumS m r • deltaVec m S.c₀) := by
  funext t
  rw [loopOp_deltaVec_apply, Pi.smul_apply, SectorFiberModule.smul_apply_sym]
  simp only [S.cartan_table h hh]
  by_cases ht : t = fun _ => S.c₀
  · subst ht
    simp [deltaVec, psumS, psum, zr, Finset.mul_sum, smul_eq_C_mul, mul_comm]
  · have hd : deltaVec (K := ℂ) m S.c₀ t = 0 := by simp [deltaVec, ht]
    rw [hd, mul_zero, smul_zero, neg_eq_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h1 h2
    · exfalso; apply ht; funext j
      by_cases hj : j = i
      · subst hj; exact h2
      · exact h1 j hj
    · simp
    · rfl

theorem loopOp_cartanN_deltaVec (m : ℕ) (h : Fin S.n) (hh : S.cartanN h) (r : ℕ) :
    loopOp S.f m h r (deltaVec m S.c₀) =
      (-((S.thetaN h : ℕ) : ℂ)) • (psumS m r • deltaVec m S.c₀) := by
  funext t
  rw [loopOp_deltaVec_apply, Pi.smul_apply, SectorFiberModule.smul_apply_sym]
  simp only [S.cartanN_table h hh]
  by_cases ht : t = fun _ => S.c₀
  · subst ht
    simp [deltaVec, psumS, psum, zr, Finset.mul_sum, smul_eq_C_mul, mul_comm]
  · have hd : deltaVec (K := ℂ) m S.c₀ t = 0 := by simp [deltaVec, ht]
    rw [hd, mul_zero, smul_zero, neg_eq_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h1 h2
    · exfalso; apply ht; funext j
      by_cases hj : j = i
      · subst hj; exact h2
      · exact h1 j hj
    · simp
    · rfl

/-- **Vieta on the generator.** -/
theorem loopOp_vieta (m : ℕ) (x : Fin S.n) :
    loopOp S.f m x m (deltaVec m S.c₀) =
      -∑ j ∈ Finset.Ico 1 (m + 1), ((-1 : ℂ) ^ j) •
        (esymmS m j • loopOp S.f m x (m - j) (deltaVec m S.c₀)) := by
  funext t
  simp only [Finset.sum_apply, Pi.neg_apply, Pi.smul_apply, SectorFiberModule.smul_apply_sym,
    loopOp_deltaVec_apply]
  simp only [smul_neg, mul_neg, Finset.sum_neg_distrib, neg_neg, Finset.mul_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  rw [neg_eq_iff_eq_neg, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hc
  · have hv := vieta_zero m i
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)] at hv
    simp only [pow_zero, one_mul, Nat.sub_zero, esymm_zero] at hv
    have : zr (K := ℂ) i ^ m = -∑ j ∈ Finset.Ico 1 (m + 1),
        (-1) ^ j * (esymm (Fin (m + 0)) ℂ j * zr i ^ (m - j)) := by
      rw [eq_neg_iff_add_eq_zero]; exact hv
    rw [this, neg_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul, smul_eq_C_mul]
    simp only [esymmS, map_pow, map_neg, map_one]
    ring
  · simp

/-! ## Weights -/

/-- `p` is supported on tensor indices of total weight `μ`. -/
def SuppW {m : ℕ} (μ : Fin S.R → ℤ) (p : TPs S m) : Prop :=
  ∀ t, ∑ i, S.wt (t i) ≠ μ → p t = 0

theorem sum_wt_update {m : ℕ} (t : Fin m → Fin S.n) (i : Fin m) (c : Fin S.n) :
    ∑ j, S.wt (Function.update t i c j) = (∑ j, S.wt (t j)) - S.wt (t i) + S.wt c := by
  have h1 : ∀ g : Fin m → (Fin S.R → ℤ), ∑ j, g j = g i + ∑ j ∈ Finset.univ.erase i, g j :=
    fun g => (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  rw [h1, h1 (fun j => S.wt (t j))]
  simp only [Function.update_self]
  have h2 : ∑ j ∈ Finset.univ.erase i, S.wt (Function.update t i c j) =
      ∑ j ∈ Finset.univ.erase i, S.wt (t j) :=
    Finset.sum_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [h2]
  abel

theorem loopOp_suppW {m : ℕ} {μ : Fin S.R → ℤ} {p : TPs S m}
    (hp : SuppW S μ p) (x : Fin S.n) (r : ℕ) : SuppW S (μ - S.wt x) (loopOp S.f m x r p) := by
  intro t ht
  simp only [loopOp, LinearMap.coe_mk, AddHom.coe_mk, neg_eq_zero]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_eq_zero, mul_zero]
  intro c _
  by_cases hc : S.wt c = S.wt x + S.wt (t i)
  · rw [hp (Function.update t i c) (by
      rw [sum_wt_update, hc]
      intro h; apply ht; rw [← h]; abel), mul_zero]
  · rw [S.table_wt x (t i) c hc, map_zero, zero_mul]

theorem deltaVec_suppW (m : ℕ) : SuppW S (m • S.wt S.c₀) (deltaVec (K := ℂ) m S.c₀) := by
  intro t ht
  simp only [deltaVec]
  rw [if_neg]
  rintro rfl
  apply ht
  simp

theorem applyWord_replicate (m k : ℕ) (x : Fin S.n) :
    applyWord S.f m (List.replicate k (x, 0)) (deltaVec (K := ℂ) m S.c₀) =
      (loopOp S.f m x 0)^[k] (deltaVec m S.c₀) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, Function.iterate_succ_apply', ← ih]
      rfl

theorem iterate_suppW (m k : ℕ) (x : Fin S.n) :
    SuppW S (m • S.wt S.c₀ - k • S.wt x) ((loopOp S.f m x 0)^[k] (deltaVec (K := ℂ) m S.c₀)) := by
  induction k with
  | zero => simpa using deltaVec_suppW S m
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have h := loopOp_suppW S ih x 0
      rwa [show m • S.wt S.c₀ - k • S.wt x - S.wt x = m • S.wt S.c₀ - (k + 1) • S.wt x by
        rw [add_smul, one_smul]; abel] at h

/-- **The integrability relation on the generator.** -/
theorem lowering_deltaVec (m : ℕ) (i : Fin S.n) (hi : S.lowering i) :
    (loopOp S.f m i 0)^[m * S.lowExp i + 1] (deltaVec (K := ℂ) m S.c₀) = 0 :=
  funext fun t => iterate_suppW S m _ i t (S.lowering_noweight i hi m t)

end

end VOA.DeligneAudit.DeligneSector
