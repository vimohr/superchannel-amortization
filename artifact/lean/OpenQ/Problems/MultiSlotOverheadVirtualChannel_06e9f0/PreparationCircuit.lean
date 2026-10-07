import OpenQ.Problems.EqualWeightLowChoiRank_523ed7.ChannelCorrespondence
import Mathlib.Tactic

/-!
Two-slot state-preparation circuits in fixed finite complex bases.
The memories have arbitrary positive finite dimensions. Slot inputs are `Fin 1`;
their factors are restored by `memoryBasis`, rather than omitted from the action.
Physicality of the teeth uses the independent amplification-defined `IsCPTP`.
The generic library predicate below is used only to prove closure properties.
-/

namespace OpenQ.Problems.MultiSlotOverheadVirtualChannel_06e9f0.Preparation

open scoped BigOperators Kronecker ComplexOrder
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7

noncomputable section

set_option maxHeartbeats 800000

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev Map (a b : ℕ) := Mat a →ₗ[ℂ] Mat b
abbrev Processor (b : ℕ) := Map (b * b) b

/-- The Physlib version, for intermediate product-index spaces only. -/
def LibraryCPTP {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (F : MatrixMap I J ℂ) : Prop :=
  F.IsCompletelyPositive ∧ F.IsTracePreserving

theorem libraryCPTP_iff {a b : ℕ} (F : Map a b) :
    LibraryCPTP F ↔ IsCPTP F := by
  exact and_congr (isCompletelyPositive_iff_matrixMap F).symm Iff.rfl

theorem LibraryCPTP.comp {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J]
    {F : MatrixMap I J ℂ} {G : MatrixMap J K ℂ}
    (hF : LibraryCPTP F) (hG : LibraryCPTP G) : LibraryCPTP (G ∘ₗ F) :=
  ⟨hF.1.comp hG.1, hF.2.comp hG.2⟩

theorem LibraryCPTP.id (I : Type*) [Fintype I] [DecidableEq I] :
    LibraryCPTP (LinearMap.id : MatrixMap I I ℂ) :=
  ⟨MatrixMap.IsCompletelyPositive.id, MatrixMap.IsTracePreserving.id⟩

theorem LibraryCPTP.kron {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    [DecidableEq I] [DecidableEq K]
    {F : MatrixMap I J ℂ} {G : MatrixMap K L ℂ}
    (hF : LibraryCPTP F) (hG : LibraryCPTP G) :
    LibraryCPTP (MatrixMap.kron F G) :=
  ⟨hF.1.kron hG.1, hF.2.kron hG.2⟩

/-- A permutation or a change between equivalent finite basis labels. -/
def basisMap {I J : Type*} (σ : J ≃ I) : MatrixMap I J ℂ where
  toFun X := X.submatrix σ σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem basisMap_apply {I J : Type*} (σ : J ≃ I)
    (X : Matrix I I ℂ) (i j : J) : basisMap σ X i j = X (σ i) (σ j) := rfl

theorem basisMap_libraryCPTP {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (σ : J ≃ I) : LibraryCPTP (basisMap σ) := by
  constructor
  · exact MatrixMap.IsCompletelyPositive.submatrix σ
  · intro X
    exact Equiv.sum_comp σ (fun i => X i i)

theorem basisMap_isCPTP {m n : ℕ} (σ : Fin n ≃ Fin m) :
    IsCPTP (basisMap σ) :=
  (libraryCPTP_iff _).1 (basisMap_libraryCPTP σ)

def flatten (x e : ℕ) : MatrixMap (Fin x × Fin e) (Fin (x * e)) ℂ :=
  basisMap finProdFinEquiv.symm

def unflatten (x e : ℕ) : MatrixMap (Fin (x * e)) (Fin x × Fin e) ℂ :=
  basisMap finProdFinEquiv

@[simp] theorem flatten_apply (x e : ℕ)
    (X : Matrix (Fin x × Fin e) (Fin x × Fin e) ℂ) (i j : Fin (x * e)) :
    flatten x e X i j = X (finProdFinEquiv.symm i) (finProdFinEquiv.symm j) := rfl

@[simp] theorem unflatten_apply (x e : ℕ) (X : Mat (x * e)) (p q : Fin x × Fin e) :
    unflatten x e X p q = X (finProdFinEquiv p) (finProdFinEquiv q) := rfl

@[simp] theorem flatten_unflatten (x e : ℕ) (X : Mat (x * e)) :
    flatten x e (unflatten x e X) = X := by
  ext i j
  rw [flatten_apply, unflatten_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

@[simp] theorem unflatten_flatten (x e : ℕ)
    (X : Matrix (Fin x × Fin e) (Fin x × Fin e) ℂ) :
    unflatten x e (flatten x e X) = X := by
  ext i j
  simp

/-- Explicit equivalence restoring the one-dimensional slot-input factor. -/
def memoryBasis (e : ℕ) : Fin 1 × Fin e ≃ Fin e where
  toFun p := p.2
  invFun s := (0, s)
  left_inv p := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  right_inv _ := rfl

def restoreMemory (e : ℕ) : MatrixMap (Fin e) (Fin 1 × Fin e) ℂ :=
  basisMap (memoryBasis e)

@[simp] theorem restoreMemory_apply (e : ℕ) (M : Mat e) (p q : Fin 1 × Fin e) :
    restoreMemory e M p q = M p.2 q.2 := rfl

/-- `N ⊗ id_e`, slot first, on arbitrary complex matrices. -/
def slotExt {a b : ℕ} (e : ℕ) (N : Map a b) :
    MatrixMap (Fin a × Fin e) (Fin b × Fin e) ℂ where
  toFun X p q := N (fun i j => X (i, p.2) (j, q.2)) p.1 q.1
  map_add' X Y := by
    ext ⟨β, s⟩ ⟨γ, t⟩
    exact congrArg (fun M => M β γ) (N.map_add
      (fun i j => X (i, s) (j, t)) (fun i j => Y (i, s) (j, t)))
  map_smul' c X := by
    ext ⟨β, s⟩ ⟨γ, t⟩
    exact congrArg (fun M => M β γ) (N.map_smul c (fun i j => X (i, s) (j, t)))

@[simp] theorem slotExt_apply {a b e : ℕ} (N : Map a b)
    (X : Matrix (Fin a × Fin e) (Fin a × Fin e) ℂ) (p q : Fin b × Fin e) :
    slotExt e N X p q = N (fun i j => X (i, p.2) (j, q.2)) p.1 q.1 := rfl

theorem slotExt_eq_amplification {a b e : ℕ} (N : Map a b)
    (X : Matrix (Fin a × Fin e) (Fin a × Fin e) ℂ) :
    slotExt e N X = tensorSwap (amplification e N (tensorSwap X)) := rfl

theorem slotExt_eq_kron {a b e : ℕ} (N : Map a b) :
    slotExt e N = MatrixMap.kron N (LinearMap.id : Map e e) := by
  ext X ⟨β, s⟩ ⟨γ, t⟩
  have h := amplification_eq_tensorSwap_kron_tensorSwap N (tensorSwap X)
  have hh := congrArg (fun Y => Y (s, β) (t, γ)) h
  exact hh

theorem slotExt_libraryCPTP {a b e : ℕ} (N : Map a b) (hN : IsCPTP N) :
    LibraryCPTP (slotExt e N) := by
  rw [slotExt_eq_kron]
  exact ((libraryCPTP_iff N).2 hN).kron (LibraryCPTP.id (Fin e))

theorem slotExt_kron {a b e : ℕ} (N : Map a b) (Y : Mat a) (Z : Mat e) :
    slotExt e N (Y ⊗ₖ Z) = N Y ⊗ₖ Z := by
  rw [slotExt_eq_kron]
  exact MatrixMap.kron_map_of_kron_state N LinearMap.id Y Z

def scalarInput (z : ℂ) : Mat 1 := z • 1

@[simp] theorem scalarInput_apply (z : ℂ) (i j : Fin 1) :
    scalarInput z i j = z := by
  rw [Subsingleton.elim i j]
  simp [scalarInput]

theorem fin_one_matrix (X : Mat 1) : X = scalarInput (X 0 0) := by
  ext i j
  rw [scalarInput_apply, Subsingleton.elim i 0, Subsingleton.elim j 0]

/-- The arbitrary complex-linear preparation map `N_R([z]) = z R`. -/
def prep {b : ℕ} (R : Mat b) : Map 1 b where
  toFun X := X 0 0 • R
  map_add' _ _ := by simp [add_smul]
  map_smul' _ _ := by simp [mul_smul]

@[simp] theorem prep_one {b : ℕ} (R : Mat b) : prep R 1 = R := by simp [prep]

@[simp] theorem prep_scalar {b : ℕ} (R : Mat b) (z : ℂ) :
    prep R (scalarInput z) = z • R := by simp [prep, scalarInput]

theorem slot_map_eq_prep {b : ℕ} (N : Map 1 b) : N = prep (N 1) := by
  ext X
  conv_lhs => rw [fin_one_matrix X]
  simp [scalarInput, prep]

theorem slotExt_restore {b e : ℕ} (N : Map 1 b) (M : Mat e) :
    slotExt e N (restoreMemory e M) = N 1 ⊗ₖ M := by
  ext ⟨β, s⟩ ⟨γ, t⟩
  rw [slotExt_apply]
  have h : (fun i j : Fin 1 => restoreMemory e M (i, s) (j, t)) =
      M s t • (1 : Mat 1) := by
    funext i j
    rw [Subsingleton.elim i j]
    simp
  rw [h, map_smul]
  simp [Matrix.kroneckerMap_apply, mul_comm]

/-- Arbitrary positive finite memories and fixed CPTP teeth. The implicit
slot-input factors in `T0` and `T1` are restored by `restoreMemory` in `act`. -/
structure Comb (b : ℕ) where
  e1 : ℕ
  e2 : ℕ
  e1_pos : 0 < e1
  e2_pos : 0 < e2
  T0 : Map 1 e1
  T1 : Map (b * e1) e2
  T2 : Map (b * e2) b
  cptp0 : IsCPTP T0
  cptp1 : IsCPTP T1
  cptp2 : IsCPTP T2

/-- Actual tooth composition, defined for every pair of complex-linear slots. -/
def Comb.act {b : ℕ} (C : Comb b) (N1 N2 : Map 1 b) : Map 1 b :=
  C.T2 ∘ₗ flatten b C.e2 ∘ₗ slotExt C.e2 N2 ∘ₗ restoreMemory C.e2 ∘ₗ
    C.T1 ∘ₗ flatten b C.e1 ∘ₗ slotExt C.e1 N1 ∘ₗ restoreMemory C.e1 ∘ₗ C.T0

theorem slotExt_add {a b e : ℕ} (N M : Map a b) :
    slotExt e (N + M) = slotExt e N + slotExt e M := by
  ext X p q
  rfl

theorem slotExt_smul {a b e : ℕ} (z : ℂ) (N : Map a b) :
    slotExt e (z • N) = z • slotExt e N := by
  ext X p q
  rfl

/-- The unrestricted slot action is linear in each slot. -/
theorem Comb.act_add_left {b : ℕ} (C : Comb b) (N M S : Map 1 b) (X : Mat 1) :
    C.act (N + M) S X = C.act N S X + C.act M S X := by
  simp only [Comb.act, LinearMap.comp_apply, slotExt_add, LinearMap.add_apply, map_add]

theorem Comb.act_add_right {b : ℕ} (C : Comb b) (N S T : Map 1 b) (X : Mat 1) :
    C.act N (S + T) X = C.act N S X + C.act N T X := by
  simp only [Comb.act, LinearMap.comp_apply, slotExt_add, LinearMap.add_apply, map_add]

theorem Comb.act_smul_left {b : ℕ} (C : Comb b) (z : ℂ) (N S : Map 1 b) (X : Mat 1) :
    C.act (z • N) S X = z • C.act N S X := by
  simp only [Comb.act, LinearMap.comp_apply, slotExt_smul, LinearMap.smul_apply, map_smul]

theorem Comb.act_smul_right {b : ℕ} (C : Comb b) (z : ℂ) (N S : Map 1 b) (X : Mat 1) :
    C.act N (z • S) X = z • C.act N S X := by
  simp only [Comb.act, LinearMap.comp_apply, slotExt_smul, LinearMap.smul_apply, map_smul]

theorem Comb.act_cptp {b : ℕ} (C : Comb b) (N1 N2 : Map 1 b)
    (h1 : IsCPTP N1) (h2 : IsCPTP N2) : IsCPTP (C.act N1 N2) := by
  apply (libraryCPTP_iff _).1
  have h := ((libraryCPTP_iff _).2 C.cptp0).comp
    ((basisMap_libraryCPTP (memoryBasis C.e1)).comp
    ((slotExt_libraryCPTP N1 h1).comp
    ((basisMap_libraryCPTP finProdFinEquiv.symm).comp
    (((libraryCPTP_iff _).2 C.cptp1).comp
    ((basisMap_libraryCPTP (memoryBasis C.e2)).comp
    ((slotExt_libraryCPTP N2 h2).comp
    ((basisMap_libraryCPTP finProdFinEquiv.symm).comp
      ((libraryCPTP_iff _).2 C.cptp2))))))))
  simpa only [Comb.act, flatten, restoreMemory, LinearMap.comp_assoc] using h

/-- The lexicographic independent input registers for a two-copy processor. -/
def tensorInput {b : ℕ} (R S : Mat b) : Mat (b * b) := flatten b b (R ⊗ₖ S)

theorem Comb.act_prep {b : ℕ} (C : Comb b) (R S : Mat b) (z : ℂ) :
    C.act (prep R) (prep S) (scalarInput z) =
      z • C.T2 (flatten b C.e2
        (S ⊗ₖ C.T1 (flatten b C.e1 (R ⊗ₖ C.T0 1)))) := by
  simp only [Comb.act, LinearMap.comp_apply, slotExt_restore, prep_one]
  simp [scalarInput, Matrix.kronecker_smul]

end
end OpenQ.Problems.MultiSlotOverheadVirtualChannel_06e9f0.Preparation
