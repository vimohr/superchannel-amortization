import OpenQ.Problems.MultiSlotOverheadVirtualChannel_06e9f0.PreparationCircuit
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
Fixed-order complex circuits with an arbitrary positive finite memory at each
slot. `Circuit a b n p` has external input dimension p, n slots a -> b, and
external output dimension b. `Comb n a b` sets p = a. A step contains precisely
one physical tooth p -> a*e followed by an unrestricted slot N tensor id_e.
The tail input is b*e. Its next tooth is therefore b*e -> a*e', or b*e -> b
at the last step. No dimension bound or promise on slot maps is imposed.

The basis and tensor operations are the accepted Preparation operations.
The explicit index convention below is a port of CriticModel.lean (e001-i04),
with its scratch imports removed. The recursive circuit and multilinearity
proofs are new formalization of the working definition, not a new optimum.
-/

namespace OpenQ.Problems.MultiSlotOverheadVirtualChannel_06e9f0.General

open scoped BigOperators ComplexOrder Kronecker
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7 (IsCPTP amplification tensorSwap)
open Preparation (Mat Map flatten unflatten slotExt LibraryCPTP libraryCPTP_iff)

noncomputable section

set_option maxHeartbeats 800000

/-- Lexicographic slot-before-memory basis: (i,s) has index e*i+s. -/
theorem slot_memory_basis (a e : ℕ) (p : Fin a × Fin e) :
    (finProdFinEquiv p : ℕ) = e * p.1 + p.2 := by
  simp [finProdFinEquiv, add_comm]

/-- Slot insertion with explicit conversion to and from the computational basis. -/
def insertSlot {a b : ℕ} (e : ℕ) (N : Map a b) : Map (a * e) (b * e) :=
  flatten b e ∘ₗ slotExt e N ∘ₗ unflatten a e

theorem insertSlot_formula {a b e : ℕ} (N : Map a b) (X : Mat (a * e))
    (p q : Fin b × Fin e) :
    insertSlot e N X (finProdFinEquiv p) (finProdFinEquiv q) =
      N (fun i j => X (finProdFinEquiv (i, p.2))
        (finProdFinEquiv (j, q.2))) p.1 q.1 := by
  simp [insertSlot]

theorem insertSlot_eq_kron {a b e : ℕ} (N : Map a b) :
    insertSlot e N = flatten b e ∘ₗ
      MatrixMap.kron N (LinearMap.id : Map e e) ∘ₗ unflatten a e := by
  rw [insertSlot, Preparation.slotExt_eq_kron]

theorem insertSlot_isCPTP {a b e : ℕ} (N : Map a b) (hN : IsCPTP N) :
    IsCPTP (insertSlot e N) := by
  apply (libraryCPTP_iff _).1
  have hU : LibraryCPTP (unflatten a e) :=
    Preparation.basisMap_libraryCPTP finProdFinEquiv
  have hF : LibraryCPTP (flatten b e) :=
    Preparation.basisMap_libraryCPTP finProdFinEquiv.symm
  have h := hU.comp ((Preparation.slotExt_libraryCPTP N hN).comp hF)
  simpa only [insertSlot, LinearMap.comp_assoc] using h

theorem isCPTP_comp {p q r : ℕ} {F : Map p q} {G : Map q r}
    (hF : IsCPTP F) (hG : IsCPTP G) : IsCPTP (G ∘ₗ F) :=
  (libraryCPTP_iff _).1 (((libraryCPTP_iff _).2 hF).comp
    ((libraryCPTP_iff _).2 hG))

theorem insertSlot_add {a b e : ℕ} (N M : Map a b) :
    insertSlot e (N + M) = insertSlot e N + insertSlot e M := by
  ext X i j
  simp only [insertSlot, LinearMap.comp_apply, Preparation.slotExt_add,
    LinearMap.add_apply, map_add, Matrix.add_apply]

theorem insertSlot_smul {a b e : ℕ} (z : ℂ) (N : Map a b) :
    insertSlot e (z • N) = z • insertSlot e N := by
  ext X i j
  simp only [insertSlot, LinearMap.comp_apply, Preparation.slotExt_smul,
    LinearMap.smul_apply, map_smul]

/-- Each constructor supplies an independent amplification-defined CPTP tooth.
All positive finite memories and all physical teeth are allowed. -/
inductive Circuit (a b : ℕ) : ℕ → ℕ → Type where
  | done {p : ℕ} (T : Map p b) (physical : IsCPTP T) : Circuit a b 0 p
  | step {n p : ℕ} (e : ℕ) (positive : 0 < e)
      (T : Map p (a * e)) (physical : IsCPTP T)
      (tail : Circuit a b n (b * e)) : Circuit a b (n + 1) p

/-- The external input and output are a and b; n is the number of calls. -/
abbrev Comb (n a b : ℕ) := Circuit a b n a

/-- Actual composition for independent arbitrary complex-linear slot maps. -/
def Circuit.act {a b : ℕ} : {n p : ℕ} → Circuit a b n p →
    (Fin n → Map a b) → Map p b
  | _, _, .done T _, _ => T
  | _, _, .step e _ T _ D, N => D.act (Fin.tail N) ∘ₗ insertSlot e (N 0) ∘ₗ T

@[simp] theorem Circuit.act_done {a b p : ℕ} (T : Map p b) (hT : IsCPTP T)
    (N : Fin 0 → Map a b) : (Circuit.done T hT : Circuit a b 0 p).act N = T := rfl

@[simp] theorem Circuit.act_step {a b n p e : ℕ} (he : 0 < e)
    (T : Map p (a * e)) (hT : IsCPTP T) (D : Circuit a b n (b * e))
    (N : Fin (n + 1) → Map a b) (X : Mat p) :
    (Circuit.step e he T hT D).act N X =
      D.act (Fin.tail N) (insertSlot e (N 0) (T X)) := rfl

/-- Independent physical teeth and slots give an independently CPTP output. -/
theorem Circuit.act_isCPTP {a b n p : ℕ} (C : Circuit a b n p)
    (N : Fin n → Map a b) (hN : ∀ i, IsCPTP (N i)) : IsCPTP (C.act N) := by
  induction C with
  | done T hT => exact hT
  | step e he T hT D ih =>
    exact isCPTP_comp (isCPTP_comp hT (insertSlot_isCPTP _ (hN 0)))
      (ih (Fin.tail N) (fun i => hN i.succ))

theorem Circuit.act_update_add {a b n p : ℕ} (C : Circuit a b n p)
    (N : Fin n → Map a b) (i : Fin n) (F G : Map a b) :
    C.act (Function.update N i (F + G)) =
      C.act (Function.update N i F) + C.act (Function.update N i G) := by
  induction C with
  | done T hT => exact Fin.elim0 i
  | step e he T hT D ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · ext X
      simp only [Circuit.act, LinearMap.comp_apply, Function.update_self,
        Fin.tail_update_zero, insertSlot_add, LinearMap.add_apply, map_add]
    · ext X
      simp only [Circuit.act, LinearMap.comp_apply, Fin.tail_update_succ,
        Function.update_of_ne (Fin.succ_ne_zero j).symm, ih,
        LinearMap.add_apply]

theorem Circuit.act_update_smul {a b n p : ℕ} (C : Circuit a b n p)
    (N : Fin n → Map a b) (i : Fin n) (z : ℂ) (F : Map a b) :
    C.act (Function.update N i (z • F)) = z • C.act (Function.update N i F) := by
  induction C with
  | done T hT => exact Fin.elim0 i
  | step e he T hT D ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · ext X
      simp only [Circuit.act, LinearMap.comp_apply, Function.update_self,
        Fin.tail_update_zero, insertSlot_smul, LinearMap.smul_apply, map_smul]
    · ext X
      simp only [Circuit.act, LinearMap.comp_apply, Fin.tail_update_succ,
        Function.update_of_ne (Fin.succ_ne_zero j).symm, ih,
        LinearMap.smul_apply]

/-- The complete action is complex multilinear in every independent slot,
and complex linear on every external input. -/
def Circuit.action {a b n p : ℕ} (C : Circuit a b n p) :
    MultilinearMap ℂ (fun _ : Fin n => Map a b) (Map p b) :=
  MultilinearMap.mk' C.act C.act_update_add C.act_update_smul

@[simp] theorem Circuit.action_apply {a b n p : ℕ} (C : Circuit a b n p)
    (N : Fin n → Map a b) : C.action N = C.act N := rfl

/-- Physical circuits are identified exactly by their full independent action. -/
def SameAction {a b n : ℕ} (C D : Comb n a b) : Prop := C.action = D.action

theorem sameAction_iff {a b n : ℕ} (C D : Comb n a b) :
    SameAction C D ↔ ∀ (N : Fin n → Map a b) (X : Mat a), C.act N X = D.act N X := by
  constructor
  · intro h N X
    exact LinearMap.congr_fun (congrArg (fun A => A N) h) X
  · intro h
    apply MultilinearMap.ext
    intro N
    exact LinearMap.ext (h N)

end
end OpenQ.Problems.MultiSlotOverheadVirtualChannel_06e9f0.General
