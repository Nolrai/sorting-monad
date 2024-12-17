import Mathlib.Order.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Control.Monad.Writer

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

structure SortingLog (n : ℕ) : Type where
  cmp_at : List (Fin n × Fin n)
  swap : List (Fin n × Fin n)

instance {n} : EmptyCollection (SortingLog n) where
  emptyCollection := {cmp_at := ∅, swap := ∅}

abbrev Perm n := Equiv.Perm (Fin n)

structure SortingMonad (n : ℕ) (α : Type) : Type where
  (run' : ReaderT (Fin n → α) (StateT (Perm (n := n)) (Writer (SortingLog n))) α)

def SortingMonad.run {n} (m : SortingMonad n α) (data : Fin n → α) : α × Perm n × SortingLog n :=
  let ⟨⟨a, result⟩,  log⟩ := (m.run'.run data).run 1
  ⟨a, result,  log⟩
