import VOA.DeligneAudit.SL4TDoubledSitePolynomial
import VOA.DeligneAudit.SL4TDoubledSiteVanishing

/-! Boundary products and shortened polynomial relations for the surviving doubled pairs. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R]

/-- The surviving pairs in forward outer order and reversed inner order. -/
def doubledPairIndices (k : Fin 10) : Fin 4 × Fin 4 :=
  ![(0, 0), (1, 1), (1, 0), (2, 2), (2, 1), (2, 0),
    (3, 3), (3, 2), (3, 1), (3, 0)] k

/-- Products of the top classes outside each surviving pair's interval. -/
def doubledPairTop (a : Fin 4 → R) (k : Fin 10) : R :=
  ![a 1 * a 2 * a 3, a 0 * a 2 * a 3, a 2 * a 3,
    a 0 * a 1 * a 3, a 0 * a 3, a 3, a 0 * a 1 * a 2,
    a 0 * a 1, a 0, 1] k

/-- The preceding pair ideal includes the tail ideal from the outset. -/
def doubledPairPrefix (a : Fin 4 → R) (I : Ideal R) (k : ℕ) : Ideal R :=
  I ⊔ principalIdealPrefix (doubledPairTop a) k

/-- The first boundary is the first removed top; the second is its lowered top when repeated. -/
theorem doubledPairTop_boundaries (a b : Fin 4 → R) (I : Ideal R)
    (hz : a 0 * a 1 * a 2 * a 3 = 0)
    (ht : ∀ i, b i * ∏ j ∈ Finset.univ.erase i, a j ∈ I) (k : Fin 10) :
    doubledPairTop a k * a (doubledPairIndices k).1 ∈ doubledPairPrefix a I k.val ∧
      doubledPairTop a k * (if (doubledPairIndices k).2 = (doubledPairIndices k).1 then
        b (doubledPairIndices k).1 else a (doubledPairIndices k).2) ∈
          doubledPairPrefix a I k.val := by
  have hm (n : ℕ) (j : Fin 10) (hj : j.val < n) :
      doubledPairTop a j ∈ doubledPairPrefix a I n :=
    (show principalIdealPrefix (doubledPairTop a) n ≤ _ from le_sup_right)
      (mem_principalIdealPrefix _ n j hj)
  have hh (n : ℕ) (i : Fin 4) :
      b i * ∏ j ∈ Finset.univ.erase i, a j ∈ doubledPairPrefix a I n :=
    (show I ≤ doubledPairPrefix a I n from le_sup_left) (ht i)
  simp only [product_except_eq_ite] at hh
  fin_cases k
  · constructor
    · have he : doubledPairTop a 0 * a (doubledPairIndices 0).1 = 0 := by
        dsimp [doubledPairTop, doubledPairIndices]
        linear_combination hz
      simp [doubledPairTop, doubledPairIndices] at he ⊢
      rw [he]
      exact Ideal.zero_mem _
    · convert hh 0 0 using 1 <;>
        simp [doubledPairTop, doubledPairIndices, Fin.prod_univ_succ] <;> ring
  · constructor
    · have he : doubledPairTop a 1 * a (doubledPairIndices 1).1 = 0 := by
        dsimp [doubledPairTop, doubledPairIndices]
        linear_combination hz
      simp [doubledPairTop, doubledPairIndices] at he ⊢
      rw [he]
      exact Ideal.zero_mem _
    · convert hh 1 1 using 1 <;>
        simp [doubledPairTop, doubledPairIndices, Fin.prod_univ_succ] <;> ring
  · constructor
    · convert hm 2 0 (by decide) using 1 <;>
        simp [doubledPairTop, doubledPairIndices] <;> ring
    · convert hm 2 1 (by decide) using 1 <;>
        simp [doubledPairTop, doubledPairIndices] <;> ring
  · constructor
    · have he : doubledPairTop a 3 * a (doubledPairIndices 3).1 = 0 := by
        dsimp [doubledPairTop, doubledPairIndices]
        linear_combination hz
      simp [doubledPairTop, doubledPairIndices] at he ⊢
      rw [he]
      exact Ideal.zero_mem _
    · convert hh 3 2 using 1 <;>
        simp [doubledPairTop, doubledPairIndices, Fin.prod_univ_succ] <;> ring
  · constructor
    · convert hm 4 1 (by decide) using 1 <;>
        simp [doubledPairTop, doubledPairIndices] <;> ring
    · convert hm 4 3 (by decide) using 1 <;>
        simp [doubledPairTop, doubledPairIndices] <;> ring
  · constructor
    · convert hm 5 2 (by decide) using 1 <;>
        simp [doubledPairTop, doubledPairIndices] <;> ring
    · convert hm 5 4 (by decide) using 1 <;>
        simp [doubledPairTop, doubledPairIndices] <;> ring
  · constructor
    · have he : doubledPairTop a 6 * a (doubledPairIndices 6).1 = 0 := by
        dsimp [doubledPairTop, doubledPairIndices]
        linear_combination hz
      simp [doubledPairTop, doubledPairIndices] at he ⊢
      rw [he]
      exact Ideal.zero_mem _
    · convert hh 6 3 using 1 <;>
        simp [doubledPairTop, doubledPairIndices, Fin.prod_univ_succ] <;> ring
  · constructor
    · convert hm 7 3 (by decide) using 1 <;>
        simp [doubledPairTop, doubledPairIndices] <;> ring
    · convert hm 7 6 (by decide) using 1 <;>
        simp [doubledPairTop, doubledPairIndices] <;> ring
  · constructor
    · convert hm 8 4 (by decide) using 1 <;>
        simp [doubledPairTop, doubledPairIndices] <;> ring
    · convert hm 8 7 (by decide) using 1 <;>
        simp [doubledPairTop, doubledPairIndices] <;> ring
  · constructor
    · convert hm 9 5 (by decide) using 1 <;>
        simp [doubledPairTop, doubledPairIndices] <;> ring
    · convert hm 9 8 (by decide) using 1 <;>
        simp [doubledPairTop, doubledPairIndices] <;> ring

/-- The retained characteristic after both roots have been removed. -/
def doubledPairPolynomial (p : Fin 4 → R[X]) (k : Fin 10) : R[X] :=
  ![p 2 * p 3, p 2 * p 3, p 2 * p 3,
    (p 2).divX.divX * p 3, (p 2).divX * p 3, (p 2).divX * p 3,
    p 2 * (p 3).divX.divX, (p 2).divX * (p 3).divX,
    p 2 * (p 3).divX, p 2 * (p 3).divX] k

/-- A pair raises the inner cutoff once precisely when a retained root occurs. -/
def doubledPairLevelShift (k : Fin 10) : ℕ := if k.val < 3 then 0 else 1

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.doubledPairTop_boundaries
