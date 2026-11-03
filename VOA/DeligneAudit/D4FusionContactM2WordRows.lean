import VOA.DeligneAudit.D4FusionContactPolynomialEval
import Mathlib.Data.List.Sort

/-! # Exact word rows and sparse cancellation

The closed checker cancels equal canonical words in an association list.
Its soundness is proved for every polynomial variable map; no rank computation
or polynomial equality over the complex numbers is used by the checker.
-/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

abbrev Word := List (Fin 18)
abbrev WordRow := List (Word × ℤ)

def canonical (w : Word) : Word := w.insertionSort (· ≤ ·)

def addTerm (w : Word) (z : ℤ) : WordRow → WordRow
  | [] => if z = 0 then [] else [(w,z)]
  | (v,c)::l => if w = v then
      if z+c = 0 then l else (v,z+c)::l
    else (v,c)::addTerm w z l

def collect : WordRow → WordRow
  | [] => []
  | (w,z)::l => addTerm w z (collect l)

def scaleRow (z : ℤ) (l : WordRow) : WordRow := l.map fun x => (x.1,z*x.2)

def rowEval {ι : Type} (f : Fin 18 → ι) (l : WordRow) : MvPolynomial ι ℂ :=
  (l.map fun x => x.2 • polyWord (x.1.map f)).sum

def multiplyRow (v : Fin 18) (l : WordRow) : WordRow :=
  l.map fun x => (canonical (x.1 ++ [v]),x.2)

variable {ι : Type} (f : Fin 18 → ι)

@[simp] theorem rowEval_nil : rowEval f [] = 0 := rfl

@[simp] theorem rowEval_cons (w : Word) (z : ℤ) (l : WordRow) :
    rowEval f ((w,z)::l) = z • polyWord (w.map f) + rowEval f l := rfl

@[simp] theorem rowEval_append (l k : WordRow) :
    rowEval f (l++k) = rowEval f l + rowEval f k := by simp [rowEval]

theorem rowEval_scale (z : ℤ) (l : WordRow) :
    rowEval f (scaleRow z l) = z • rowEval f l := by
  induction l with
  | nil => simp [scaleRow]
  | cons x l ih =>
      change (z*x.2) • polyWord (x.1.map f) + rowEval f (scaleRow z l) =
        z • (x.2 • polyWord (x.1.map f) + rowEval f l)
      rw [ih, mul_smul]
      exact (smul_add z (x.2 • polyWord (x.1.map f)) (rowEval f l)).symm

theorem polyWord_canonical (w : Word) :
    polyWord ((canonical w).map f) = polyWord (w.map f) :=
  by simpa only [canonical, polyWord, List.map_map, Function.comp_def] using
    ((List.perm_insertionSort (· ≤ ·) w).map (MvPolynomial.X ∘ f)).prod_eq

theorem rowEval_addTerm (w : Word) (z : ℤ) (l : WordRow) :
    rowEval f (addTerm w z l) = z • polyWord (w.map f) + rowEval f l := by
  induction l with
  | nil =>
      by_cases hz : z = 0 <;> simp [addTerm,hz]
  | cons x l ih =>
      obtain ⟨v,c⟩ := x
      by_cases hw : w = v
      · subst w
        by_cases hz : z+c = 0
        · simp only [addTerm, ite_true, if_pos hz, rowEval_cons]
          rw [← add_assoc, ← add_smul, hz, zero_smul, zero_add]
        · simp only [addTerm, ite_true, if_neg hz, rowEval_cons, add_smul]
          abel
      · simp only [addTerm, if_neg hw, rowEval_cons, ih]
        abel

theorem rowEval_collect (l : WordRow) : rowEval f (collect l) = rowEval f l := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [collect, rowEval_addTerm, ih, rowEval_cons]

theorem rowEval_eq_zero_of_collect (l : WordRow) (h : collect l = []) :
    rowEval f l = 0 := by rw [← rowEval_collect, h, rowEval_nil]

theorem rowEval_multiply (v : Fin 18) (l : WordRow) :
    rowEval f (multiplyRow v l) = rowEval f l * MvPolynomial.X (f v) := by
  induction l with
  | nil => simp [multiplyRow]
  | cons x l ih =>
      change x.2 • polyWord ((canonical (x.1 ++ [v])).map f) +
        rowEval f (multiplyRow v l) =
        (x.2 • polyWord (x.1.map f) + rowEval f l) * MvPolynomial.X (f v)
      rw [polyWord_canonical, ih]
      simp only [List.map_append, List.map_cons, List.map_nil, polyWord,
        List.prod_append, List.prod_cons, List.prod_nil, mul_one, add_mul, smul_mul_assoc]

theorem rowEval_scale_mem (I : Ideal (MvPolynomial ι ℂ)) (z : ℤ)
    (l : WordRow) (h : rowEval f l ∈ I) : rowEval f (scaleRow z l) ∈ I := by
  rw [rowEval_scale]
  simpa only [Int.cast_smul_eq_zsmul] using
    (I.restrictScalars ℂ).smul_mem (z:ℂ) h

/-- A finite exact cancellation certificate transfers actual ideal membership. -/
theorem row_mem_of_collect (I : Ideal (MvPolynomial ι ℂ))
    (raw normal earlier : WordRow) (scale factor : ℤ) (hfactor : factor ≠ 0)
    (hcheck : collect (scaleRow scale raw ++ scaleRow (-factor) normal ++ earlier) = [])
    (hraw : rowEval f raw ∈ I) (hearlier : rowEval f earlier ∈ I) :
    rowEval f normal ∈ I := by
  have he := rowEval_eq_zero_of_collect f _ hcheck
  simp only [rowEval_append, rowEval_scale, neg_smul] at he
  have hmem : factor • rowEval f normal ∈ I := by
    have hz : factor • rowEval f normal = scale • rowEval f raw + rowEval f earlier := by
      linear_combination -he
    rw [hz]
    exact I.add_mem
      (by simpa only [Int.cast_smul_eq_zsmul] using
        (I.restrictScalars ℂ).smul_mem (scale:ℂ) hraw) hearlier
  have hc : (factor:ℂ) • rowEval f normal ∈ I := by
    simpa only [Int.cast_smul_eq_zsmul] using hmem
  exact (Submodule.smul_mem_iff _ (by exact_mod_cast hfactor : (factor:ℂ) ≠ 0)).mp hc

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.row_mem_of_collect
