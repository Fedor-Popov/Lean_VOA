import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleNoPositive
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeModes

/-! Every Levi current preserves the pure-A polynomial image, and every
contact current kills it. These facts hold for whole polynomials. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.SectorWeyl
noncomputable section

theorem a_target : ∀ (a : Fin 18) (i : Fin 8), (target a i.castSucc).val < 8 := by
  decide +kernel

theorem contact_a_coeff : ∀ (a : Fin 18) (i : Fin 8),
    category a = 0 → coeff a i.castSucc = 0 := by decide +kernel

variable (K : Type*) [Field K]

def aTarget (a : Fin 18) (i : Fin 8) : Fin 8 := ⟨(target a i.castSucc).val,a_target a i⟩

def aMap (m : ℕ) : Cube.ModePoly K m →ₐ[K] Ring K m :=
  MvPolynomial.rename (fun x => (x.1.castSucc,x.2))

theorem aMap_X (m : ℕ) (x : Fin 8 × Fin m) :
    aMap K m (MvPolynomial.X x) = MvPolynomial.X (x.1.castSucc,x.2) :=
  MvPolynomial.rename_X _ _

theorem aMap_mode (m : ℕ) (i : Fin 8) (r : ℕ) :
    aMap K m (Cube.shiftedX K m i r) = mode K m i.castSucc r := by
  by_cases hr : r < m
  · simp only [Cube.shiftedX,aMap_X,mode,dif_pos hr]
  · simp only [Cube.shiftedX,mode,dif_neg hr,map_zero]

def aDeriv (m : ℕ) (a : Fin 18) (k : ℕ) :
    Derivation K (Cube.ModePoly K m) (Cube.ModePoly K m) :=
  MvPolynomial.mkDerivation K
    (fun x => coeff a x.1.castSucc • Cube.shiftedX K m (aTarget a x.1) (k+x.2.val))

theorem aMap_deriv (m : ℕ) (a : Fin 18) (k : ℕ) (p : Cube.ModePoly K m) :
    aMap K m (aDeriv K m a k p) = deriv K m a k (aMap K m p) := by
  apply Cube.map_derivation
  intro x
  rw [show aDeriv K m a k (MvPolynomial.X x) =
    coeff a x.1.castSucc • Cube.shiftedX K m (aTarget a x.1) (k+x.2.val) from
      MvPolynomial.mkDerivation_X K _ _,map_zsmul,aMap_mode,aMap_X,deriv_X]
  rw [show (aTarget a x.1).castSucc = target a x.1.castSucc from Fin.ext rfl]

theorem aDeriv_contact (m : ℕ) (a : Fin 18) (k : ℕ) (ha : category a = 0) :
    aDeriv K m a k = 0 := by
  apply MvPolynomial.derivation_ext
  intro x
  simp only [aDeriv,MvPolynomial.mkDerivation_X,contact_a_coeff a x.1 ha,
    zero_zsmul,Derivation.zero_apply]

def aWord (m : ℕ) : List (Fin 18 × ℕ) → Cube.ModePoly K m → Cube.ModePoly K m
  | [], p => p
  | x::l, p => aDeriv K m x.1 x.2 (aWord m l p)

theorem word_aMap (m : ℕ) (l : List (Fin 18 × ℕ)) (p : Cube.ModePoly K m) :
    wordOp (representation K m) l (aMap K m p) = aMap K m (aWord K m l p) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      change deriv K m x.1 x.2 (wordOp (representation K m) l (aMap K m p)) = _
      rw [ih,← aMap_deriv]
      rfl

theorem aWord_contact_zero (m : ℕ) (p : Cube.ModePoly K m) :
    ∀ (l : List (Fin 18 × ℕ)), (∃ x ∈ l, category x.1 = 0) → aWord K m l p = 0 := by
  intro l
  induction l with
  | nil => intro h; obtain ⟨x,hx,_⟩ := h; simp at hx
  | cons x l ih =>
      intro hp
      by_cases ht : ∃ y ∈ l, category y.1 = 0
      · change aDeriv K m x.1 x.2 (aWord K m l p) = 0
        rw [ih ht,map_zero]
      · have hx : category x.1 = 0 := by
          obtain ⟨y,hy,hc⟩ := hp
          rcases List.mem_cons.mp hy with hy | hy
          · subst y; exact hc
          · exact (ht ⟨y,hy,hc⟩).elim
        change aDeriv K m x.1 x.2 (aWord K m l p) = 0
        rw [aDeriv_contact K m x.1 x.2 hx]
        rfl

def aTop (m : ℕ) : MonoRing K m →ₐ[K] Cube.ModePoly K m :=
  MvPolynomial.aeval (fun i => Cube.shiftedX K m 0 i.val)

theorem aMap_top (m : ℕ) (p : MonoRing K m) :
    aMap K m (aTop K m p) = monoMap K m 0 p := by
  have he : (aMap K m).comp (aTop K m) = monoMap K m 0 := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply,aTop,MvPolynomial.aeval_X,aMap_mode,monoMap_X]
    rfl
  exact AlgHom.congr_fun he p

end
#print axioms aMap_deriv
#print axioms aWord_contact_zero
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
