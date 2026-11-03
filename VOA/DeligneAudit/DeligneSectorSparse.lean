/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneSectorSparseData
import VOA.DeligneAudit.DeligneSectorData
import VOA.DeligneAudit.A2Carrier

/-!
# Sparse integer certificates for sector data

Kernel-checkable certificates for the Lie-theoretic fields of `DeligneSectorData`, for a type whose
structure constants are integers given by a sparse table `br : ℕ → ℕ → SV` (`SV` = list of
`(index, coefficient)`).

* `jacobiCoord_of_check`: the Jacobi identity from the Boolean check `jacCheck` (evaluated by
  `decide +kernel`);
* `qpoly_eq_zero_of_check`: a sparse quadratic polynomial vanishes if each of its (oriented) monomials
  has total coefficient zero;
* `quadraticRelation_adMatrix_entryMatrix`: the coadjoint derivation of a listed quadratic relation
  is the sparse polynomial `adQ`;
* `slotA_vecC`, `wordA_vecC`: coadjoint words on sparse vectors.

Nothing here is specific to a type.
-/

namespace VOA.DeligneAudit.DeligneSector.Sparse

open MvPolynomial VOA.DeligneAudit.SectorLoop VOA.QuadraticJetCoefficientPairing
open VOA.DeligneAudit.DeligneSector

noncomputable section

/-! ## Sparse vectors -/





@[simp] theorem sget_nil (c : ℕ) : sget [] c = 0 := rfl

@[simp] theorem sget_cons (p : ℕ × ℤ) (L : SV) (c : ℕ) :
    sget (p :: L) c = (if p.1 = c then p.2 else 0) + sget L c := by
  simp [sget]

@[simp] theorem sget_append (L M : SV) (c : ℕ) : sget (L ++ M) c = sget L c + sget M c := by
  simp [sget]



@[simp] theorem sget_smulSV (k : ℤ) (L : SV) (c : ℕ) : sget (smulSV k L) c = k * sget L c := by
  induction L with
  | nil => simp [smulSV]
  | cons p L ih =>
    simp only [smulSV, List.map_cons, sget_cons] at ih ⊢
    rw [ih]; split_ifs <;> ring

theorem sget_flatMap {α : Type*} (L : List α) (F : α → SV) (c : ℕ) :
    sget (L.flatMap F) c = (L.map fun a => sget (F a) c).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

theorem castSum {α : Type*} (L : List α) (g : α → ℤ) :
    (((L.map g).sum : ℤ) : ℂ) = (L.map fun p => ((g p : ℤ) : ℂ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem negSum {α : Type*} (L : List α) (g : α → ℂ) :
    (L.map fun p => -g p).sum = -(L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem sget_range (n : ℕ) (F : ℕ → ℤ) (c : ℕ) :
    sget ((List.range n).map fun y => (y, F y)) c = if c < n then F c else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, sget_append, ih]
    simp only [List.map_cons, List.map_nil, sget_cons, sget_nil, add_zero]
    by_cases h1 : c < n
    · have h2 : n ≠ c := by omega
      simp [h1, h2, show c < n + 1 by omega]
    · by_cases h3 : n = c
      · subst h3; simp
      · simp [h1, h3, show ¬ c < n + 1 by omega]



theorem sget_eq_zero_of_check {L : SV} (h : zeroCheck L = true) (c : ℕ) : sget L c = 0 := by
  by_cases hc : ∃ p ∈ L, p.1 = c
  · obtain ⟨p, hp, rfl⟩ := hc
    simp only [zeroCheck, List.all_eq_true, beq_iff_eq] at h
    exact h p hp
  · push Not at hc
    unfold sget
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    simp [hc p hp]

/-- Sums against a sparse vector. -/
theorem sum_sget_mul {n : ℕ} {R : Type*} [CommRing R] (L : SV) (hL : ∀ p ∈ L, p.1 < n)
    (g : ℕ → R) : ∑ d : Fin n, (sget L d : R) * g d = (L.map fun p => (p.2 : R) * g p.1).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [sget_cons, Int.cast_add, add_mul, Finset.sum_add_distrib, List.map_cons,
      List.sum_cons]
    rw [ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))]
    congr 1
    have hp := hL p List.mem_cons_self
    rw [Finset.sum_eq_single ⟨p.1, hp⟩]
    · simp
    · intro b _ hb
      have : p.1 ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
      simp [this]
    · simp

/-- Sums against a sparse vector, module version. -/
theorem sum_sget_smul {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] (L : SV)
    (hL : ∀ p ∈ L, p.1 < n) (g : ℕ → M) :
    ∑ d : Fin n, ((sget L d : ℤ) : ℂ) • g d = (L.map fun p => ((p.2 : ℤ) : ℂ) • g p.1).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [sget_cons, Int.cast_add, add_smul, Finset.sum_add_distrib, List.map_cons,
      List.sum_cons]
    rw [ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))]
    congr 1
    have hp := hL p List.mem_cons_self
    rw [Finset.sum_eq_single ⟨p.1, hp⟩]
    · simp
    · intro b _ hb
      have : p.1 ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
      simp [this]
    · simp

/-! ## Structure constants from a sparse table -/

section Table

variable (n : ℕ) (br : ℕ → ℕ → SV)



/-- Complex structure constants on `Fin n`. -/
def fC : Fin n → Fin n → Fin n → ℂ := fun a b c => (fZ br a b c : ℂ)



variable {n br}

theorem range_of_check (h : rangeCheck n br = true) {a b : ℕ} (ha : a < n) (hb : b < n) :
    ∀ p ∈ br a b, p.1 < n := by
  simp only [rangeCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h a ha b hb

variable (br)



variable (n)



variable {n br}

theorem sum_fC_mul (hr : rangeCheck n br = true) (a x : Fin n) (g : ℕ → ℂ) :
    ∑ d : Fin n, fC n br a x d * g d = ((br a x).map fun p => (p.2 : ℂ) * g p.1).sum :=
  sum_sget_mul (br a x) (range_of_check hr a.2 x.2) g

theorem jacobiCoord_of_check (hr : rangeCheck n br = true) (hj : jacCheck n br = true) :
    JacobiCoord (fC n br) := by
  intro a b x c
  have h0 := sget_eq_zero_of_check (by
    simp only [jacCheck, List.all_eq_true, List.mem_range] at hj
    exact hj a a.2 b b.2 x x.2) (c : ℕ)
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

end Table

/-! ## Sparse quadratic polynomials -/



/-- The variable `X_a` (zero out of range). -/
def Xn (n : ℕ) (a : ℕ) : MvPolynomial (Fin n) ℂ := if h : a < n then X ⟨a, h⟩ else 0

theorem Xn_fin {n : ℕ} (a : Fin n) : Xn n a = X a := by simp [Xn]

/-- The polynomial of a sparse quadratic form. -/
def qpoly (n : ℕ) (L : QV) : MvPolynomial (Fin n) ℂ :=
  (L.map fun t => ((t.2.2 : ℤ) : ℂ) • (Xn n t.1 * Xn n t.2.1)).sum

@[simp] theorem qpoly_nil (n : ℕ) : qpoly n [] = 0 := rfl

@[simp] theorem qpoly_cons (n : ℕ) (t : ℕ × ℕ × ℤ) (L : QV) :
    qpoly n (t :: L) = ((t.2.2 : ℤ) : ℂ) • (Xn n t.1 * Xn n t.2.1) + qpoly n L := by
  simp [qpoly]

@[simp] theorem qpoly_append (n : ℕ) (L M : QV) : qpoly n (L ++ M) = qpoly n L + qpoly n M := by
  simp [qpoly]



@[simp] theorem qpoly_smulQ (n : ℕ) (k : ℤ) (L : QV) :
    qpoly n (smulQ k L) = ((k : ℤ) : ℂ) • qpoly n L := by
  induction L with
  | nil => simp [smulQ]
  | cons t L ih =>
    simp only [smulQ, List.map_cons, qpoly_cons] at ih ⊢
    rw [ih, smul_add, smul_smul]; push_cast; ring_nf

theorem qpoly_flatMap {α : Type*} (n : ℕ) (L : List α) (F : α → QV) :
    qpoly n (L.flatMap F) = (L.map fun a => qpoly n (F a)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]



theorem qpoly_orient (n : ℕ) (L : QV) : qpoly n (orient L) = qpoly n L := by
  induction L with
  | nil => simp [orient]
  | cons t L ih =>
    simp only [orient, List.map_cons, qpoly_cons] at ih ⊢
    rw [ih]
    split_ifs
    · rfl
    · simp [mul_comm]





theorem qpoly_eq_sum_qget (n : ℕ) (L : QV) :
    qpoly n L = ∑ a : Fin n, ∑ b : Fin n, ((qget L a b : ℤ) : ℂ) • (X a * X b) := by
  induction L with
  | nil => simp [qget]
  | cons t L ih =>
    rw [qpoly_cons, ih]
    have hq : ∀ a b : ℕ, qget (t :: L) a b = (if t.1 = a ∧ t.2.1 = b then t.2.2 else 0) +
        qget L a b := by
      intro a b; simp [qget]
    simp only [hq, Int.cast_add, add_smul, Finset.sum_add_distrib]
    congr 1
    by_cases h1 : t.1 < n
    · by_cases h2 : t.2.1 < n
      · rw [Finset.sum_eq_single ⟨t.1, h1⟩, Finset.sum_eq_single ⟨t.2.1, h2⟩]
        · simp [Xn, h1, h2]
        · intro b _ hb
          have : t.2.1 ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
          simp [this]
        · simp
        · intro a _ ha
          have : t.1 ≠ (a : ℕ) := fun h => ha (Fin.ext h.symm)
          simp [this]
        · simp
      · have : ∀ b : Fin n, t.2.1 ≠ (b : ℕ) := fun b h => h2 (h ▸ b.2)
        simp [Xn, h2, this]
    · have : ∀ a : Fin n, t.1 ≠ (a : ℕ) := fun a h => h1 (h ▸ a.2)
      simp [Xn, h1, this]

theorem qpoly_eq_zero_of_check {n : ℕ} {L : QV} (h : qzeroCheck L = true) : qpoly n L = 0 := by
  rw [← qpoly_orient, qpoly_eq_sum_qget]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  suffices qget (orient L) a b = 0 by simp [this]
  by_cases hc : ∃ t ∈ orient L, t.1 = a ∧ t.2.1 = b
  · obtain ⟨t, ht, h1, h2⟩ := hc
    simp only [qzeroCheck, List.all_eq_true, beq_iff_eq] at h
    rw [← h1, ← h2]
    exact h t ht
  · push Not at hc
    unfold qget
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    by_cases h1 : t.1 = a
    · simp [hc t ht h1]
    · simp [h1]

/-! ## The coadjoint derivation on listed relations -/

section Ad

variable {n : ℕ}

/-- The image of `X_a` under the derivation of `x`: `Σ_c f(x,a,c) X_c`. -/
def adX (f : Fin n → Fin n → Fin n → ℂ) (x a : Fin n) : MvPolynomial (Fin n) ℂ :=
  ∑ c, f x a c • X c

theorem quadraticRelation_adMatrix_eq (f : Fin n → Fin n → Fin n → ℂ) (x : Fin n)
    (q : Fin n × Fin n → ℂ) :
    quadraticRelation (adMatrix f x q) =
      ∑ a, ∑ b, q (a, b) • (adX f x a * X b + X a * adX f x b) := by
  unfold quadraticRelation adMatrix adX
  rw [Fintype.sum_prod_type]
  simp only [add_smul, Finset.sum_add_distrib, Finset.sum_smul, smul_add, Finset.mul_sum,
    Finset.sum_mul, Finset.smul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
  have e1 : ∀ T : Fin n → Fin n → Fin n → MvPolynomial (Fin n) ℂ,
      ∑ c, ∑ d, ∑ a, T a d c = ∑ a, ∑ d, ∑ c, T a d c := by
    intro T
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun d _ => Finset.sum_comm).trans ?_
    exact Finset.sum_comm
  have e2 : ∀ U : Fin n → Fin n → Fin n → MvPolynomial (Fin n) ℂ,
      ∑ c, ∑ d, ∑ b, U c b d = ∑ c, ∑ b, ∑ d, U c b d := fun U =>
    Finset.sum_congr rfl fun c _ => Finset.sum_comm
  exact congrArg₂ (· + ·) (e1 _) (e2 _)

theorem sum_entryMatrix_smul {M : Type*} [AddCommGroup M] [Module ℂ M]
    (L : List (Fin n × Fin n × ℂ)) (G : Fin n → Fin n → M) :
    ∑ a, ∑ b, VOA.DeligneAudit.A2.entryMatrix L (a, b) • G a b = (L.map fun t => t.2.2 • G t.1 t.2.1).sum := by
  induction L with
  | nil => simp [VOA.DeligneAudit.A2.entryMatrix]
  | cons t L ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    simp only [VOA.DeligneAudit.A2.entryMatrix, List.map_cons, List.sum_cons, add_smul, Finset.sum_add_distrib,
      ite_smul, zero_smul, Prod.mk.injEq]
    congr 1
    rw [Finset.sum_eq_single t.1, Finset.sum_eq_single t.2.1]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
    · intro a _ ha; simp [Ne.symm ha]
    · simp

/-- Casting an integer sparse quadratic form to an entry list. -/
def castL (n : ℕ) [NeZero n] (L : QV) : List (Fin n × Fin n × ℂ) :=
  L.map fun t => (Fin.ofNat n t.1, Fin.ofNat n t.2.1, ((t.2.2 : ℤ) : ℂ))



theorem natCast_fin_val [NeZero n] {a : ℕ} (ha : a < n) : ((Fin.ofNat n a : Fin n) : ℕ) = a := by
  simp [Fin.val_ofNat, Nat.mod_eq_of_lt ha]

theorem adX_fC {br : ℕ → ℕ → SV} (hr : rangeCheck n br = true) (x a : Fin n) :
    adX (fC n br) x a = ((br x a).map fun p => ((p.2 : ℤ) : ℂ) • Xn n p.1).sum := by
  unfold adX
  have := sum_sget_smul (n := n) (br x a) (range_of_check hr x.2 a.2) (fun c => Xn n c)
  simp only [Xn_fin] at this
  exact this

theorem qpoly_map_left (L : SV) (b : ℕ) (k : ℤ) :
    qpoly n (L.map fun p => (p.1, b, k * p.2)) =
      ((k : ℤ) : ℂ) • ((L.map fun p => ((p.2 : ℤ) : ℂ) • Xn n p.1).sum * Xn n b) := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, qpoly_cons, List.sum_cons, ih, add_mul, smul_add]
    congr 1
    rw [smul_mul_assoc, smul_smul]; push_cast; ring_nf

theorem qpoly_map_right (L : SV) (a : ℕ) (k : ℤ) :
    qpoly n (L.map fun p => (a, p.1, k * p.2)) =
      ((k : ℤ) : ℂ) • (Xn n a * (L.map fun p => ((p.2 : ℤ) : ℂ) • Xn n p.1).sum) := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, qpoly_cons, List.sum_cons, ih, mul_add, smul_add]
    congr 1
    rw [mul_smul_comm, smul_smul]; push_cast; ring_nf

/-- **The coadjoint derivation of a listed relation is the sparse form `adQ`.** -/
theorem quadraticRelation_adMatrix_castL [NeZero n] {br : ℕ → ℕ → SV}
    (hr : rangeCheck n br = true) (x : Fin n) (L : QV) (hL : ∀ t ∈ L, t.1 < n ∧ t.2.1 < n) :
    quadraticRelation (adMatrix (fC n br) x (VOA.DeligneAudit.A2.entryMatrix (castL n L))) = qpoly n (adQ br x L) := by
  rw [quadraticRelation_adMatrix_eq, sum_entryMatrix_smul, adQ, qpoly_flatMap, castL, List.map_map]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  obtain ⟨h1, h2⟩ := hL t ht
  simp only [Function.comp_apply, qpoly_append, qpoly_map_left, qpoly_map_right]
  have e1 : (Fin.ofNat n t.1 : Fin n) = ⟨t.1, h1⟩ := Fin.ext (natCast_fin_val h1)
  have e2 : (Fin.ofNat n t.2.1 : Fin n) = ⟨t.2.1, h2⟩ := Fin.ext (natCast_fin_val h2)
  rw [e1, e2, adX_fC hr, adX_fC hr]
  simp only [Xn, h1, h2, dif_pos, smul_add]

/-- The quadratic relation of a cast list is its sparse polynomial. -/
theorem quadraticRelation_castL [NeZero n] (L : QV) (hL : ∀ t ∈ L, t.1 < n ∧ t.2.1 < n) :
    quadraticRelation (VOA.DeligneAudit.A2.entryMatrix (castL n L)) = qpoly n L := by
  rw [VOA.DeligneAudit.A2.quadraticRelation_entryMatrix, castL, List.map_map, qpoly]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  obtain ⟨h1, h2⟩ := hL t ht
  have e1 : (Fin.ofNat n t.1 : Fin n) = ⟨t.1, h1⟩ := Fin.ext (natCast_fin_val h1)
  have e2 : (Fin.ofNat n t.2.1 : Fin n) = ⟨t.2.1, h2⟩ := Fin.ext (natCast_fin_val h2)
  simp only [Function.comp_apply, e1, e2, Xn, h1, h2, dif_pos]

/-- Diagonal entries of a cast list. -/
theorem entryMatrix_castL_diag [NeZero n] (L : QV) (hL : ∀ t ∈ L, t.1 < n ∧ t.2.1 < n)
    (c : Fin n) (hc : L.all (fun t => !(t.1 = c ∧ t.2.1 = c)) = true) :
    VOA.DeligneAudit.A2.entryMatrix (castL n L) (c, c) = 0 := by
  unfold VOA.DeligneAudit.A2.entryMatrix castL
  rw [List.map_map]
  refine List.sum_eq_zero fun z hz => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
  obtain ⟨h1, h2⟩ := hL t ht
  simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    not_and] at hc
  have := hc t ht
  simp only [Function.comp_apply, Prod.mk.injEq, ite_eq_right_iff, and_imp]
  intro e1 e2
  exfalso
  refine this ?_ ?_
  · rw [← natCast_fin_val (n := n) h1, e1]
  · rw [← natCast_fin_val (n := n) h2, e2]

end Ad

/-! ## Coadjoint words on sparse vectors -/

section Words

variable {n : ℕ} (br : ℕ → ℕ → SV)





/-- The complex vector of a sparse vector. -/
def vecC (n : ℕ) (v : SV) : Fin n → ℂ := fun y => ((sget v y : ℤ) : ℂ)



theorem svRange_slotZ (x : ℕ) (v : SV) : svRange n (slotZ br n x v) = true := by
  simp [svRange, slotZ]

variable {br}

theorem slotA_vecC (x : Fin n) (v : SV) (hv : svRange n v = true) :
    slotA (fC n br) x (vecC n v) = vecC n (slotZ br n x v) := by
  funext y
  simp only [slotA, vecC]
  have hv' : ∀ p ∈ v, p.1 < n := by
    simpa [svRange] using hv
  have h1 : ∑ d : Fin n, fC n br x y d * ((sget v d : ℤ) : ℂ) =
      ∑ d : Fin n, ((sget v d : ℤ) : ℂ) * (fZ br x y d : ℂ) := by
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [fC, mul_comm]
  rw [h1, sum_sget_mul v hv' (fun d => (fZ br x y d : ℂ)), slotZ, sget_range, if_pos y.2,
    Int.cast_neg, castSum]
  congr 1
  congr 1
  refine List.map_congr_left fun p _ => ?_
  push_cast; ring

theorem svRange_wordZ (l : List ℕ) (v : SV) (hv : svRange n v = true) :
    svRange n (wordZ br n l v) = true := by
  cases l with
  | nil => exact hv
  | cons x l => exact svRange_slotZ br x _

theorem wordA_vecC (l : List (Fin n)) (v : SV) (hv : svRange n v = true) :
    wordA (fC n br) l (vecC n v) = vecC n (wordZ br n (List.map Fin.val l) v) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [wordA]
    rw [ih]
    exact slotA_vecC x _ (svRange_wordZ _ _ hv)

theorem vecC_single (c : Fin n) : vecC n [((c : ℕ), 1)] = Pi.single c 1 := by
  funext y
  simp only [vecC, sget_cons, sget_nil, add_zero, Pi.single_apply]
  by_cases h : y = c
  · subst h; simp
  · have : (c : ℕ) ≠ y := fun e => h (Fin.ext e.symm)
    simp [this, h]

theorem vecC_eq_of_check {v w : SV} (h : zeroCheck (v ++ smulSV (-1) w) = true) :
    vecC n v = vecC n w := by
  funext y
  have := sget_eq_zero_of_check h y
  simp only [sget_append, sget_smulSV] at this
  simp only [vecC]
  congr 1
  linarith

theorem vecC_add (v w : SV) : vecC n (v ++ w) = vecC n v + vecC n w := by
  funext y; simp [vecC]

theorem vecC_smul (k : ℤ) (v : SV) : vecC n (smulSV k v) = ((k : ℤ) : ℂ) • vecC n v := by
  funext y; simp [vecC]

theorem vecC_flatMap {α : Type*} (L : List α) (F : α → SV) :
    vecC n (L.flatMap F) = (L.map fun a => vecC n (F a)).sum := by
  induction L with
  | nil => funext y; simp [vecC]
  | cons a L ih => simp [List.flatMap_cons, vecC_add, ih]

theorem svRange_single {c : ℕ} (hc : c < n) : svRange n [(c, 1)] = true := by
  simp [svRange, hc]

/-- **Coadjoint cyclicity from a sparse certificate**: if `Σ μ_w · w·δ_{c₀} = N e_c` with `N ≠ 0`
and all words of length `≤ L`, then `e_c ∈ slotWords`. -/
theorem single_mem_slotWords_of_check [NeZero n] (c₀ : Fin n) (L : ℕ) (c : Fin n) (N : ℤ)
    (ws : List (List ℕ × ℤ)) (hN : N ≠ 0)
    (hw : ∀ p ∈ ws, p.1.length ≤ L ∧ ∀ x ∈ p.1, x < n)
    (hz : zeroCheck ((ws.flatMap fun p => smulSV p.2 (wordZ br n p.1 [((c₀ : ℕ), 1)])) ++
      smulSV (-1) (smulSV N [((c : ℕ), 1)])) = true) :
    (Pi.single c 1 : Fin n → ℂ) ∈ slotWords (fC n br) c₀ L := by
  have hv := vecC_eq_of_check (n := n) hz
  rw [vecC_smul, vecC_single] at hv
  have hmem : vecC n (ws.flatMap fun p => smulSV p.2 (wordZ br n p.1 [((c₀ : ℕ), 1)])) ∈
      slotWords (fC n br) c₀ L := by
    rw [vecC_flatMap]
    refine list_sum_mem fun z hz' => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz'
    obtain ⟨hl, hx⟩ := hw p hp
    rw [vecC_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨p.1.map (Fin.ofNat n), by simpa using hl, ?_⟩)
    rw [← vecC_single, wordA_vecC _ _ (svRange_single c₀.2), List.map_map]
    congr 2
    conv_lhs => rw [← List.map_id p.1]
    refine List.map_congr_left fun x hx' => ?_
    simp [Fin.val_ofNat, Nat.mod_eq_of_lt (hx x hx')]
  have hN' : ((N : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hN
  have : (Pi.single c 1 : Fin n → ℂ) = ((N : ℤ) : ℂ)⁻¹ •
      vecC n (ws.flatMap fun p => smulSV p.2 (wordZ br n p.1 [((c₀ : ℕ), 1)])) := by
    rw [hv, smul_smul, inv_mul_cancel₀ hN', one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ hmem

end Words

/-! ## Weights -/

theorem exists_of_sget_ne_zero {L : SV} {c : ℕ} (h : sget L c ≠ 0) : ∃ p ∈ L, p.1 = c := by
  by_contra hc
  push Not at hc
  apply h
  unfold sget
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  simp [hc p hp]

/-- **No weight vector**: a linear functional bounded below by `B` on all weights, equal to `B + e`
on `wt c₀` and to `1` on `wt i`, separates `m·wt c₀ - (m e + 1)·wt i` from all sums of `m` weights. -/
theorem noweight_of_functional {n R : ℕ} (wt : Fin n → Fin R → ℤ) (Lf : Fin R → ℤ) (c₀ i : Fin n)
    (e : ℕ) (B : ℤ) (hB : ∀ c, B ≤ ∑ k, Lf k * wt c k) (h0 : ∑ k, Lf k * wt c₀ k = B + e)
    (h1 : ∑ k, Lf k * wt i k = 1) (m : ℕ) (t : Fin m → Fin n) :
    ∑ j, wt (t j) ≠ m • wt c₀ - (m * e + 1) • wt i := by
  intro h
  have hc := congrArg (fun v : Fin R → ℤ => ∑ k, Lf k * v k) h
  simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply] at hc
  simp only [nsmul_eq_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum] at hc
  rw [Finset.sum_comm] at hc
  have hl : ∑ j, ∑ k, Lf k * wt (t j) k ≥ ∑ _j : Fin m, B := Finset.sum_le_sum fun j _ => hB (t j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hl
  have e0 : ∑ k, Lf k * ((m : ℤ) * wt c₀ k) = m * (B + e) := by
    have : ∑ k, Lf k * ((m : ℤ) * wt c₀ k) = (m : ℤ) * ∑ k, Lf k * wt c₀ k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, h0]
  have e1 : ∑ k, Lf k * (((m : ℤ) * e + 1) * wt i k) = (m : ℤ) * e + 1 := by
    have : ∑ k, Lf k * (((m : ℤ) * e + 1) * wt i k) = ((m : ℤ) * e + 1) * ∑ k, Lf k * wt i k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, h1, mul_one]
  push_cast at hc
  rw [e0, e1] at hc
  rw [hc] at hl
  linarith

end

end VOA.DeligneAudit.DeligneSector.Sparse

section AxiomAudit
open VOA.DeligneAudit.DeligneSector.Sparse
#print axioms jacobiCoord_of_check
#print axioms qpoly_eq_zero_of_check
#print axioms quadraticRelation_adMatrix_castL
#print axioms single_mem_slotWords_of_check
#print axioms noweight_of_functional
end AxiomAudit
