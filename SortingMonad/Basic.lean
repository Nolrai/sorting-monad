import Mathlib.Order.Basic
import Mathlib.Data.Vector

def hello := "world"

variable {α β : Type}

section
variable (F : Type -> Type)

class MonadSize (F) extends Monad F where
  size : Nat

class MonadSort (F) extends MonadSize F where
  swap : Fin size -> Fin size -> F Unit
  cmp_at : Fin size -> Fin size -> F Bool
  forAll : F Prop -> Prop
  forAll_pure (x : Prop) : forAll (pure x) = x

infix:50 " <? " => MonadSort.cmp_at

end

section

variable {F : Type -> Type}
open MonadSort

def onAll (r : α → β → Prop) [MonadSort F] (a : F α) (b : F β) : Prop :=
  forAll $ r <$> a <*> b

infix:20 " ≃ " => onAll (· = ·)

def returns [MonadSort F] (a : α) (m : F α) := m ≃ pure a

notation:20 "⟨" m "⟩= " a => returns a m

abbrev Ix {size} := Fin size
end

variable (F : Type -> Type)

class MonadCmpLawful extends MonadSort F where
  cmp_at_refl (mi : F Ix) :
  ⟨(λ i => i <? i) =<< mi⟩= true
  cmp_at_trans (i j k : (Fin size)) :
  ⟨do {
    let ij <- i <? j
    let jk <- j <? k
    let ik <- i <? k
    pure (not ik && ij && jk)
  }⟩= false
  cmp_idem (i j k n : Ix) :
  (do {let _ <- cmp_at i j; cmp_at k n}) ≃ k <? n

def no_change {F} [MonadSort F] (m : F α) :=
  ∀ i j, (do {_ <- m; (i <? j : F Bool)}) ≃ i <? j

class MonadSortLawful extends MonadCmpLawful F where
  swap_rfl (i) : no_change (swap i i)
  swap_symm (i j) : swap i j = swap j i
  swap_idem (i j) : no_change (do {swap i j; swap i j})
  swap_cmp_swap (i j) : (do {swap i j; let b <- (j <? i : F Bool); swap i j; pure b}) ≃ i <? j

instance VectorState.MonadSort [LinearOrder α] [Inhabited α] {n} : MonadSort (StateM (Vector α n)) where
  size := n
  cmp_at := λ i j ↦ do
    let v <- get
    pure (v.get i <= v.get j)
  swap := λ i j ↦ modify (λ (v : Vector α n) ↦
    have ih : i < n := i.2
    have jh : j < n := j.2
    v.swap i j ih jh)
  forAll m := forall s, (m.run s).fst
  forAll_pure p := by simp

open MonadSort

lemma Vector.swap_symm {n} {v : Vector α n} {i j : Fin n} : v.swap i j = v.swap j i := by
  simp_rw [Vector.swap]
  apply Vector.toArray_inj


instance [LinearOrder α] [Inhabited α] {n} : MonadSortLawful (StateM (Vector α n)) where

  cmp_at_refl mi := by
    simp_rw [returns, onAll]
    intros v
    have : ∀ {M} [Monad M] {α β} (x : α → M β) (y : M α), (x =<< y) = (y >>= x) := λ _ _ => rfl
    rw [this, cmp_at]
    simp [VectorState.MonadSort]

  cmp_at_trans i j k := by
    simp [returns, onAll]
    intros s ij jk
    simp at *
    apply lt_of_lt_of_le ij jk

  cmp_idem i j i' j' := by simp [onAll, forAll, cmp_at]

  swap_rfl i := by simp [no_change, onAll, VectorState.MonadSort]
  swap_symm i j := by
    simp [swap]
  swap_idem := _
  swap_cmp_swap := _
