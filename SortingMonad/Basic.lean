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

structure SortingLogItem (n : ℕ) where
  isSwap : Bool
  left : Fin n
  right : Fin n

abbrev SortingLog n := List (SortingLogItem n)

abbrev SortingMonad (item : Type) (size : ℕ) (ret : Type) : Type :=
  ReaderT (Fin size → item) (StateT (Fin size ≃ Fin size) (Writer (SortingLog size))) ret

variable {size : ℕ} {item : Type}

def SortingMonad.run (m : SortingMonad item size α) (data : Fin size → item) : α × (Fin size ≃ Fin size) × SortingLog size :=
  let ⟨⟨a, result⟩,  log⟩ := StateT.run (ReaderT.run m data) 1
  ⟨a, result,  log⟩

def SortingMonad.swap (i j : Fin size) : SortingMonad item size Unit := (modify (trans (Equiv.swap i j)) : ReaderT _ _ _)

instance : Monad (SortingMonad item size) :=
    have inst : Monad (ReaderT (Fin size → item) (StateT (Fin size ≃ Fin size) (Writer (SortingLog size)))) :=
      inferInstance
    inst

instance (ℓ : Type*) : LawfulMonad (Writer (List ℓ)) where
  map_const {α β} := by
    funext a mb
    let (b, w) := mb
    simp [Functor.mapConst, WriterT.mk, Id.instMonad, Functor.map]
  id_map a :=
    match a with
    | (x, w) => by
      simp [Functor.map, WriterT.mk]
  seqLeft_eq := by
    intros α β x y
    let (x₁, x₂) := x
    let (y₁, y₂) := y
    simp [Functor.map, SeqLeft.seqLeft, Id.instMonad, WriterT.mk, Seq.seq]
  seqRight_eq := by
    intros α β x y
    let (x₁, x₂) := x
    let (y₁, y₂) := y
    simp [Functor.map, SeqRight.seqRight, Id.instMonad, WriterT.mk, Seq.seq]
  pure_seq := by
    intros α β f x
    let (x₁, x₂) := x
    simp [Functor.map, Pure.pure, Id.instMonad, WriterT.mk, Seq.seq]
  bind_pure_comp := by
    intros α β f x
    let (x₁, x₂) := x
    simp [bind, pure, Functor.map]
  bind_map := by
    intros α β f x
    let (x₁, x₂) := x
    let (f₁, f₂) := f
    simp [bind, pure, Functor.map, WriterT.mk, Seq.seq, Id.instMonad]
  pure_bind := by
    intros α β x f
    simp [bind, pure, Functor.map, WriterT.mk, Seq.seq, Id.instMonad]
    rfl
  bind_assoc := by
    intros α β γ x f g
    let (x₁, x₂) := x
    simp [bind, WriterT.mk]
    let (fx₁, fx₂) := f x₁
    simp

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

theorem instance_helper {item n} : ((fun _ ↦ True) <$> (get : SortingMonad item n _) = pure True) := by
      simp_rw [Functor.map, get, getThe]
      simp [MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, pure]
      funext env
      simp_rw [ReaderT.pure, pure]
      funext state
      simp [StateT.pure, StateT.map, StateT.get]

theorem instance_helper2 {item n} : ((fun _ ↦ True) <$> (read : SortingMonad item n _) = pure True) := by
      simp_rw [Functor.map, read, readThe]
      simp [MonadReaderOf.read, ReaderT.read]
      funext env state
      have : ∀ {α β s m} [Monad m] (f : α → β) (x : StateT s m α), StateT.map f x = f <$> x := λ a b => by
        simp [Functor.map]
      rw [this, map_pure]
      simp [pure, StateT.pure, ReaderT.pure]

theorem SortingMonad.map_run_result {item n} (f : α → β) (m : SortingMonad item n α) (data) :
  (f <$> m).run data = (f (m.run data).1, (m.run data).2) := by
  simp_rw [SortingMonad.run, ReaderT.run, Functor.map]
  have : ∀ {σ M} [Monad M] (s : StateT σ M α) (f : α → β), StateT.map f s = f <$> s := by
    intros σ M inst s f
    rfl
  rw [this, StateT.run_map]
  rw [StateT.run]
  let ((a, result), log) := (m data 1)
  simp [Functor.map, WriterT.mk]

instance [Inhabited item] [LinearOrder item] : MonadSortLawful $ SortingMonad item size where
  cmp_at_refl := by
    intros mi data
    simp [seq_pure, MonadSort.cmp_at, SortingMonad.cmp_at, Bind.bindLeft, instance_helper]
    simp [instance_helper2]
    simp [SortingMonad.map_run_result]
  cmp_at_trans := by
    intros i j k data
    simp [seq_pure, MonadSort.cmp_at, SortingMonad.cmp_at, Bind.bindLeft, instance_helper]
    simp [read, readThe, MonadReaderOf.read, ReaderT.read]
    simp_rw [get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift]
    

  cmp_idem := _
  swap_rfl := _
  swap_symm := _
  swap_idem := _
  swap_cmp_swap := _
