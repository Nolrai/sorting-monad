import Mathlib.Order.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Control.Monad.Writer

def hello := "world"

variable {α β : Type}

section
variable (F : Type -> Type)

class MonadForAll (F) extends Monad F where
  forAll : F Prop -> Prop
  forAll_pure (x : Prop) : forAll (pure x) = x

class MonadSize (F) extends MonadForAll F where
  size : Nat

class MonadSort (F) extends MonadSize F where
  swap : Fin size -> Fin size -> F Unit
  cmp_at : Fin size -> Fin size -> F Bool

infix:50 " ≤? " => MonadSort.cmp_at

end

section MonadForAll

open MonadForAll

variable (ω σ ε : Type) (m : Type → Type)

instance : MonadForAll Id where
  forAll := id
  forAll_pure (_ : Prop) := rfl

instance [MonadForAll m] [LawfulMonad m] [EmptyCollection ω] [Append ω] : MonadForAll (WriterT ω m) where
  forAll mp := forAll (Prod.fst <$> mp.run)
  forAll_pure p := by
    simp
    simp_rw [WriterT.run, Pure.pure]
    rw [LawfulApplicative.map_pure, forAll_pure]

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
  ⟨(λ i => i ≤? i) =<< mi⟩= true
  cmp_at_trans (i j k : (Fin size)) :
  ⟨do {
    let ij <- i ≤? j
    let jk <- j ≤? k
    let ik <- i ≤? k
    pure (not ik && ij && jk)
  }⟩= false
  cmp_idem (i j k n : Ix) :
  (do {let _ <- cmp_at i j; cmp_at k n}) ≃ k ≤? n

def no_change {F} [MonadSort F] (m : F α) :=
  ∀ i j, (do {_ <- m; (i ≤? j : F Bool)}) ≃ i ≤? j

class MonadSortLawful extends MonadCmpLawful F where
  swap_rfl (i) : no_change (swap i i)
  swap_symm (i j) : swap i j = swap j i
  swap_idem (i j) : no_change (do {swap i j; swap i j})
  swap_cmp_swap (i j) : (do {swap i j; let b <- (j ≤? i : F Bool); swap i j; pure b}) ≃ i ≤? j

structure SortingLog (n : ℕ) : Type where
  cmp_at : List (Fin n × Fin n)
  swap : List (Fin n × Fin n)

instance {n} : EmptyCollection (SortingLog n) where
  emptyCollection := {cmp_at := ∅, swap := ∅}

instance {n} : Append (SortingLog n) where
  append old new := ⟨new.1 ++ old.1, new.2 ++ old.2⟩ -- put the new one on front

def SortingMonad (item : Type) (size : ℕ) (ret : Type) : Type :=
  ReaderT (Fin size → item) (StateT (Fin size ≃ Fin size) (Writer (SortingLog size))) ret

def test {m} [Monad m] (f : α → β → β) : ReaderT α (StateT β m) Unit := do
  let a <- read
  modify (f a)

variable {size : ℕ} {item : Type}

def SortingMonad.run (m : SortingMonad item size α) (data : Fin size → item) : α × (Fin size ≃ Fin size) × SortingLog size :=
  let ⟨⟨a, result⟩,  log⟩ := StateT.run (ReaderT.run m data) 1
  ⟨a, result,  log⟩

def SortingMonad.swap (i j : Fin size) : SortingMonad item size Unit := (modify (trans (Equiv.swap i j)) : ReaderT _ _ _)

instance : Monad (SortingMonad item size) :=
    have inst : Monad (ReaderT (Fin size → item) (StateT (Fin size ≃ Fin size) (Writer (SortingLog size)))) :=
      inferInstance
    inst

instance [Monad (Writer ω)] : LawfulMonad (Writer ω) where
  map_const := funext _
  id_map a :=
    match a with
    | (x, w) => _
  

def SortingMonad.cmp_at [LinearOrder item] (i j : Fin size) : SortingMonad item size Bool :=
  do
    let start <- (read : ReaderT _ _ _)
    let swaps <- (get : ReaderT _ (StateT _ _) _)
    let a := start $ swaps i
    let b := start $ swaps j
    pure (a ≤ b)

instance [Inhabited item] [LinearOrder item] : MonadSort $ SortingMonad item size where
  size := size
  swap := SortingMonad.swap
  cmp_at := SortingMonad.cmp_at
  forAll m := ∀ start, (m.run start).1
  forAll_pure := by
    intros p
    simp
    simp_rw [SortingMonad.run, pure, ReaderT.run, StateT.run, ReaderT.pure, pure, StateT.pure]
    apply Iff.intro _ (by simp)
    intros h
    apply h
    apply default

instance [Inhabited item] [LinearOrder item] : MonadSortLawful $ SortingMonad item size where
  cmp_at_refl := by
    intros mi data
    rw [LawfulApplicative.seq_pure]

  cmp_at_trans := _
  cmp_idem := _
  swap_rfl := _
  swap_symm := _
  swap_idem := _
  swap_cmp_swap := _
