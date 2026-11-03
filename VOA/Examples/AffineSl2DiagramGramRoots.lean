/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.WakimotoDiagramJoint

/-!
# The opposite family of actual affine highest-word determinant roots

The diagram-transformed screening is tested against the actual positive
word rows. Explicit joint occupation exchange makes the Fock row matrix
square. This gives the other real-root family, including its horizontal
q=0 boundary, without assuming a determinant symmetry or character formula.
-/
namespace VOA.Wak.Charged
open Module (End)
open MvPolynomial Matrix
open AffineVOA.HighestNormalOrdering
open AffineVOA.NormalOrdering (currentWord currentWord_append)
open scoped BigOperators
noncomputable section
local instance (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := jointIndexFintype n c
local instance (n : ℕ) (c : ℤ) : DecidableEq (JointIndex n c) := Classical.decEq _

/-- Reindex the exact actual monomial expansion by the diagram bijection. -/
theorem diagramFock_expansion (n n' : ℕ) (c : ℤ) (hn : (n' : ℤ)=(n : ℤ)-c)
    (P : WakFock) (hP : P∈jointFockSpace n' (-c)) :
    P=∑ d : JointIndex n c,coeff (diagramJointEquiv n n' c hn d).val P •
      monomial (diagramJointEquiv n n' c hn d).val (1 : ℂ) := by
  exact (jointFock_expansion n' (-c) P hP).trans ((Equiv.sum_comp (diagramJointEquiv n n' c hn)
    (fun d : JointIndex n' (-c) => coeff d.val P • monomial d.val (1 : ℂ))).symm)

/-- Actual highest projection after a diagram-transformed word. -/
def diagramRow (k lam : ℂ) (w : List (Fin 3×ℤ)) : WakFock→ₗ[ℂ]ℂ :=
  (lcoeff ℂ 0).comp (currentWord (diagramJ k lam) w)

/-- Square positive-word matrix on the correctly reindexed actual Fock basis. -/
def diagramRowMatrix (k lam : ℂ) (n n' : ℕ) (c : ℤ) (hn : (n' : ℤ)=(n : ℤ)-c) :
    Matrix (JointIndex n c) (JointIndex n c) ℂ := fun i j =>
  diagramRow k lam (adjointWord (occupationWord i.val))
    (monomial (diagramJointEquiv n n' c hn j).val 1)

/-- Actual transformed creation coordinates in that same Fock basis. -/
def diagramCreationMatrix (k lam : ℂ) (n n' : ℕ) (c : ℤ) (hn : (n' : ℤ)=(n : ℤ)-c) :
    Matrix (JointIndex n c) (JointIndex n c) ℂ := fun i j =>
  coeff (diagramJointEquiv n n' c hn i).val
    (currentWord (diagramJ k lam) (occupationWord j.val) (1 : WakFock))

/-- The ordinary highest-word polynomial Gram matrix factors through the
ACTUAL diagram-transformed Fock joint space at weight k-lambda. -/
theorem highestGramPolynomial_diagram_factor (k lam : ℂ) (hk : k+2≠0)
    (n n' : ℕ) (c : ℤ) (hn : (n' : ℤ)=(n : ℤ)-c) :
    (highestGramPolynomial n c).map (MvPolynomial.eval ![k,k-lam])=
      diagramRowMatrix k lam n n' c hn*diagramCreationMatrix k lam n n' c hn := by
  ext i j
  change MvPolynomial.eval ![k,k-lam] (wordPolynomial _)=_
  rw [← wordPolynomial_diagram k lam hk,currentWord_append,Module.End.mul_apply]
  change diagramRow k lam _ (currentWord (diagramJ k lam) _ 1)=_
  rw [diagramFock_expansion n n' c hn _ (diagramOccupationWord_mem_joint k lam n n' c hn j),map_sum]
  simp only [map_smul,smul_eq_mul,Matrix.mul_apply,diagramRowMatrix,diagramCreationMatrix]
  apply Finset.sum_congr rfl
  intro d hd
  exact mul_comm _ _

/-- The actual screening is highest also for the exchanged positive Borel:
positive currents and the transformed E_0 all annihilate it. -/
theorem diagram_screening_positive (r q M : ℕ) (hr : 0<r) (hq : 0<q)
    (k : ℂ) (hMk : (M : ℂ)*(k+2)=1) (a : Fin 3) (n : ℤ)
    (hn : 0<n ∨ (n=0 ∧ a=0)) :
    diagramJ k ((q : ℂ)*(k+2)-(r : ℂ)-1) a n (Screening.state r q M)=0 := by
  rcases fin3_cases a with rfl|rfl|rfl
  · rw [diagramJ_E]
    exact Screening.state_positive_lowering r q M hr hq k hMk (n+1) (by omega)
  · rw [diagramJ_F]
    exact Screening.state_raising r q M (n-1) (by rcases hn with h|h; omega; norm_num [Fin.ext_iff] at h)
  · have hp : 0<n := by rcases hn with h|h; exact h; norm_num [Fin.ext_iff] at h
    have hh := Screening.state_positive_current r q M hr hq k hMk 2 n hp
    rw [J_H] at hh
    rw [diagramJ_H,if_neg (ne_of_gt hp),add_zero,LinearMap.neg_apply,hh,neg_zero]

/-- Every adjoint creation row at opposite screening charge kills the
ACTUAL nonzero state. Nonemptiness follows from charge even at energy zero. -/
theorem diagram_adjoint_kills_screening (r q M : ℕ) (hr : 0<r)
    (k : ℂ) (hMk : (M : ℂ)*(k+2)=1) (d : JointIndex (r*q) (-(r : ℤ))) :
    currentWord (diagramJ k (((q+1 : ℕ) : ℂ)*(k+2)-(r : ℂ)-1))
      (adjointWord (occupationWord d.val)) (Screening.state r (q+1) M)=0 := by
  apply currentWord_kills_of_letters
  · intro he
    have hw : occupationWord d.val=[] := by simpa [adjointWord] using he
    have hd := occupationWord_charge d.val
    rw [hw,wordCharge,List.map_nil,List.sum_nil,d.property.2] at hd
    have hp : (0 : ℤ)<r := by exact_mod_cast hr
    omega
  · intro an han
    obtain ⟨bn,hbn,rfl⟩ := List.mem_map.mp han
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hbn)
    apply diagram_screening_positive r (q+1) M hr (by omega) k hMk
    rcases adjoint_lowerLetter_positive v with h|h
    · exact Or.inl h
    · rw [h]; exact Or.inr ⟨rfl,rfl⟩

/-- The explicit integer equality for the opposite screening joint labels. -/
theorem opposite_screening_labels (r q : ℕ) :
    ((r*(q+1) : ℕ) : ℤ)=((r*q : ℕ) : ℤ)-(-(r : ℤ)) := by push_cast; ring

/-- Actual nonzero screenings force an ordinary determinant root on the
opposite real-root line at every reciprocal-positive-integer parameter. -/
theorem highestDeterminant_opposite_screening_root (r q M : ℕ) (hr : 0<r)
    (k : ℂ) (hMk : (M : ℂ)*(k+2)=1) :
    MvPolynomial.eval ![k,(r : ℂ)-1-(q : ℂ)*(k+2)]
      (highestDeterminant (r*q) (-(r : ℤ)))=0 := by
  let lam : ℂ := ((q+1 : ℕ) : ℂ)*(k+2)-(r : ℂ)-1
  let e := diagramJointEquiv (r*q) (r*(q+1)) (-(r : ℤ)) (opposite_screening_labels r q)
  have hS : Screening.state r (q+1) M∈jointFockSpace (r*(q+1)) (-(-(r : ℤ))) := by
    simpa only [neg_neg] using screening_mem_jointFockSpace r (q+1) M (by omega)
  have hnon : (fun d : JointIndex (r*q) (-(r : ℤ)) =>
      coeff (e d).val (Screening.state r (q+1) M))≠0 := by
    intro hz
    have he := diagramFock_expansion (r*q) (r*(q+1)) (-(r : ℤ))
      (opposite_screening_labels r q) _ hS
    have hc (d : JointIndex (r*q) (-(r : ℤ))) : coeff (e d).val (Screening.state r (q+1) M)=0 := congrFun hz d
    change Screening.state r (q+1) M=∑ d : JointIndex (r*q) (-(r : ℤ)),
      coeff (e d).val (Screening.state r (q+1) M) • monomial (e d).val 1 at he
    simp only [hc,zero_smul,Finset.sum_const_zero] at he
    exact Screening.state_ne_zero r (q+1) M hr (by omega) he
  have hker : diagramRowMatrix k lam (r*q) (r*(q+1)) (-(r : ℤ))
      (opposite_screening_labels r q) *ᵥ
      (fun d : JointIndex (r*q) (-(r : ℤ)) => coeff (e d).val (Screening.state r (q+1) M))=0 := by
    funext i
    have hz := congrArg constantCoeff (diagram_adjoint_kills_screening r q M hr k hMk i)
    change diagramRow k lam _ (Screening.state r (q+1) M)=0 at hz
    rw [diagramFock_expansion (r*q) (r*(q+1)) (-(r : ℤ))
      (opposite_screening_labels r q) _ hS,map_sum] at hz
    simp only [map_smul,smul_eq_mul] at hz
    change (∑ j : JointIndex (r*q) (-(r : ℤ)),_)=0
    convert hz using 1
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  have hdet := Matrix.exists_mulVec_eq_zero_iff.mp ⟨_,hnon,hker⟩
  have hk : k+2≠0 := by intro hz; simp [hz] at hMk
  have hlam : k-lam=(r : ℂ)-1-(q : ℂ)*(k+2) := by dsimp [lam]; push_cast; ring
  rw [← hlam,highestDeterminant,RingHom.map_det]
  change ((highestGramPolynomial (r*q) (-(r : ℤ))).map (MvPolynomial.eval ![k,k-lam])).det=0
  rw [highestGramPolynomial_diagram_factor k lam hk (r*q) (r*(q+1)) (-(r : ℤ))
    (opposite_screening_labels r q),Matrix.det_mul,hdet,zero_mul]


/-- Restriction of the ordinary determinant to the opposite real-root line,
including q=0. It is a polynomial in the shifted level t. -/
def oppositeKacPolynomial (r q : ℕ) : Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![Polynomial.X-Polynomial.C 2,
      Polynomial.C (r : ℂ)-Polynomial.C 1-Polynomial.C (q : ℂ)*Polynomial.X]
    (highestDeterminant (r*q) (-(r : ℤ)))

/-- The finite polynomial restriction has its literal scalar evaluation. -/
theorem oppositeKacPolynomial_eval (r q : ℕ) (t : ℂ) :
    (oppositeKacPolynomial r q).eval t=
      MvPolynomial.eval ![t-2,(r : ℂ)-1-(q : ℂ)*t]
        (highestDeterminant (r*q) (-(r : ℤ))) := by
  change Polynomial.evalRingHom t (oppositeKacPolynomial r q)=_
  rw [oppositeKacPolynomial,MvPolynomial.map_eval₂Hom]
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C=RingHom.id ℂ := by
    ext z; simp
  rw [hc]
  have hv : (fun i : Fin 2 => Polynomial.evalRingHom t
      (![Polynomial.X-Polynomial.C 2,
        Polynomial.C (r : ℂ)-Polynomial.C 1-Polynomial.C (q : ℂ)*Polynomial.X] i))=
      ![t-2,(r : ℂ)-1-(q : ℂ)*t] := by
    funext i
    fin_cases i <;> simp
  rw [hv]
  rfl

/-- Infinitely many ACTUAL diagram-screening roots force the entire opposite
Kac-line restriction to vanish, with no generic singularity premise. -/
theorem oppositeKacPolynomial_eq_zero (r q : ℕ) (hr : 0<r) :
    oppositeKacPolynomial r q=0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective inverse_successor_injective).mono
  intro t ht
  obtain ⟨m,rfl⟩ := ht
  change (oppositeKacPolynomial r q).eval (((m+1 : ℕ) : ℂ)⁻¹)=0
  rw [oppositeKacPolynomial_eval]
  have hm : ((m+1 : ℕ) : ℂ)≠0 := by exact_mod_cast (Nat.succ_ne_zero m)
  have hk : (((m+1 : ℕ) : ℂ))*((((m+1 : ℕ) : ℂ)⁻¹-2)+2)=1 := by
    rw [sub_add_cancel,mul_inv_cancel₀ hm]
  simpa only [sub_add_cancel] using highestDeterminant_opposite_screening_root
    r q (m+1) hr ((((m+1 : ℕ) : ℂ)⁻¹)-2) hk

/-- Ordinary actual highest-word determinant roots on EVERY opposite Kac
line at EVERY complex parameter, including the horizontal q=0 case.
This establishes roots, not their descendant multiplicities. -/
theorem highestDeterminant_opposite_kac_root (r q : ℕ) (hr : 0<r) (t : ℂ) :
    MvPolynomial.eval ![t-2,(r : ℂ)-1-(q : ℂ)*t]
      (highestDeterminant (r*q) (-(r : ℤ)))=0 := by
  rw [← oppositeKacPolynomial_eval,oppositeKacPolynomial_eq_zero r q hr,Polynomial.eval_zero]

end
end VOA.Wak.Charged
