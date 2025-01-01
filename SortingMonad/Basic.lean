import Mathlib.Order.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Control.Monad.Writer

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

def cmp_log {n} l r := SortingLogItem.mk (n := n) false l r
def swap_log {n} l r := SortingLogItem.mk (n := n) true l r

abbrev SortingLog n := List (SortingLogItem n)

abbrev SortingMonad (item : Type) (size : ℕ) (ret : Type) : Type :=
  ReaderT (Fin size → item) (StateT (Fin size ≃ Fin size) (Writer (SortingLog size))) ret

variable {size : ℕ} {item : Type}

def SortingMonad.run (m : SortingMonad item size α) (data : Fin size → item) : α × (Fin size ≃ Fin size) × SortingLog size :=
  let ⟨⟨a, result⟩,  log⟩ := StateT.run (ReaderT.run m data) 1
  ⟨a, result, log⟩

@[simp]
theorem SortingMonad.run_1 (m : SortingMonad item size α) (data : Fin size → item) :
  (m.run data).1 = (StateT.run (ReaderT.run m data) 1).1.1 := rfl

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
    tell (cmp_log i j)
    pure (a ≤ b)

instance [Inhabited item] [LinearOrder item] : MonadSort (SortingMonad item size) where
  size := size
  swap := SortingMonad.swap
  cmp_at := SortingMonad.cmp_at
  forAll m := ∀ start, (m.run start).1
  forAll_pure := by
    intros p
    simp
    simp_rw [pure]

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

theorem swap_comm_lemma (size : ℕ) (item : Type) [Inhabited item] [LinearOrder item] (i j : Fin size) (data : Fin size → item)
      : decide (data ((Equiv.swap i j) j) ≤ data ((Equiv.swap i j) i)) = decide
          (data ((Equiv.trans (Equiv.swap i j) (Equiv.swap i j)) i) ≤ data ((Equiv.trans (Equiv.swap i j) (Equiv.swap i j)) j)) := by
  simp

def unfold_cmp {item size} [Inhabited item] [LinearOrder item] (i j : Fin size) (r s)
  : (ReaderT.run (MonadSort.swap i j : SortingMonad item size Unit) r).run s = WriterT.mk ()

instance [Inhabited item] [LinearOrder item] : MonadSortLawful $ SortingMonad item size where
  cmp_at_refl := by
    intros mi data
    let (a, w) := mi data 1
    simp [Bind.bindLeft]
    simp only [MonadSort.cmp_at, SortingMonad.cmp_at]
    simp only [le_refl, decide_true]
    simp only [bind_pure_comp, seq_pure, Functor.map_map, SortingMonad.run_1, ReaderT.run_map,
      StateT.run_map]
    simp only [ReaderT.run_bind, ReaderT.run_map, StateT.run_bind, StateT.run_map, map_bind,
      Functor.map_map]
    simp only [get, getThe, MonadStateOf.get, StateT.run]
    simp only [read, readThe, MonadReaderOf.read, ReaderT.read, ReaderT.run]
    let (a, b) := mi data 1
    simp only [liftM, monadLift, MonadLift.monadLift, StateT.get]
    simp only [map_pure, bind_pure_comp]
    simp only [bind, WriterT.mk, Functor.map, pure, StateT.pure]

    -- simp only [bind, WriterT.mk, ReaderT.run, Functor.map, pure, StateT.pure]
    -- simp only [List.empty_eq, List.nil_append, Prod.mk.eta]

  cmp_at_trans := by
    intros i j k data
    simp only [MonadSort.cmp_at, SortingMonad.cmp_at, bind_pure_comp, map_bind, Functor.map_map,
      bind_assoc, bind_map_left, seq_pure, Bool.and_eq_false_imp, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_le, decide_eq_true_eq,
      and_imp]
    simp only [read, readThe, MonadReaderOf.read, ReaderT.read]
    simp only [get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift]
    simp only [SortingMonad.run, StateT.run, ReaderT.run, bind, ReaderT.bind, pure, Functor.map]
    simp only [StateT.bind, StateT.pure, pure, List.empty_eq, StateT.get, StateT.map]
    apply lt_of_lt_of_le

  cmp_idem := by
    intros i j k n start
    simp only [MonadSort.cmp_at, SortingMonad.cmp_at]
    simp only [bind_pure_comp, bind_assoc, bind_map_left, map_bind, Functor.map_map]
    simp only [Seq.seq, Functor.map]
    simp only [read, readThe, MonadReaderOf.read, ReaderT.read]
    simp only [get, getThe, MonadStateOf.get]
    simp only [liftM, monadLift, MonadLift.monadLift]
    simp only [SortingMonad.run, StateT.run, ReaderT.run, bind, ReaderT.bind, pure, Functor.map]
    simp only [StateT.bind, bind_assoc]
    simp only [bind, WriterT.mk, StateT.pure, Functor.map, StateT.get, Prod.mk_one_one,
      Prod.snd_one, StateT.map, Equiv.Perm.coe_one, id_eq, List.empty_eq, List.append_nil,
      StateT.bind]

  swap_rfl := by
    intros i j k data2
    simp only [MonadSort.swap, SortingMonad.swap, SortingMonad.run]
    simp only [MonadSort.cmp_at, SortingMonad.run_1, SortingMonad.cmp_at]
    simp only [Equiv.swap_self, map_bind, ReaderT.run_seq, ReaderT.run_bind, ReaderT.run_map,
      StateT.run_seq, StateT.run_bind, StateT.run_map, bind_assoc, bind_map_left]
    simp only [modify, modifyGet, MonadStateOf.modifyGet]
    simp only [Equiv.instTrans_trans, Equiv.refl_trans, ReaderT.run_monadLift, monadLift_self,
      ReaderT.run_pure, StateT.run_pure, map_pure, bind_pure_comp, pure_bind, decide_eq_decide]
    simp only [read, readThe, MonadReaderOf.read]
    simp only [get, getThe, MonadStateOf.get]
    simp only [liftM, monadLift, MonadLift.monadLift]
    simp only [ReaderT.run, StateT.run, ReaderT.read, StateT.modifyGet, StateT.get]
    simp only [pure, StateT.pure]
    simp only [Functor.map, WriterT.mk, bind]

  swap_symm := by
    intros i j
    simp only [MonadSort.swap, SortingMonad.swap, Trans.trans, Equiv.swap_comm]

  swap_idem := by
    intros i₁ j₁ i₂ j₂ start
    simp only [SortingMonad.run_1, ReaderT.run_seq, ReaderT.run_map, ReaderT.run_pure,
      ReaderT.run_bind, id_eq, ReaderT.run_monadLift, monadLift_self, eq_mpr_eq_cast, cast_eq,
      Prod.mk_one_one, Prod.snd_one, Prod.fst_one, Equiv.Perm.coe_one, List.nil_append, Id.map_eq,
      List.empty_eq, bind_assoc, map_bind, StateT.run_seq, StateT.run_bind, StateT.run_map,
      bind_map_left]
    simp only [MonadSort.swap, SortingMonad.swap]
    simp only [MonadSort.cmp_at, SortingMonad.cmp_at]
    simp only [modify, modifyGet, MonadStateOf.modifyGet]
    simp only [read, readThe, MonadReaderOf.read]
    simp only [get, getThe, MonadStateOf.get]
    simp only [Functor.map, WriterT.mk]
    rw [StateT.run, ReaderT.run_monadLift, monadLift_self, StateT.modifyGet, ]
    simp_rw [ReaderT.read, StateT.run, ReaderT.run]
    simp only [Equiv.instTrans_trans, Equiv.Perm.trans_one]
    simp only [liftM, monadLift, MonadLift.monadLift, bind_pure_comp, pure_bind]
    simp only [bind, WriterT.mk, Functor.map, ReaderT.bind, StateT.bind]
    simp only [StateT.modifyGet, pure, Equiv.swap_swap, List.empty_eq, StateT.pure, StateT.map, StateT.get]
    simp only [bind, WriterT.mk, List.nil_append, Prod.mk.eta, Equiv.refl_apply, Id.map_eq,
      List.append_nil]

  swap_cmp_swap := by
    intros i j data
    simp_rw [SortingMonad.run_1, ReaderT.run_seq, ReaderT.run_map,
      ReaderT.run_bind, StateT.run_seq, StateT.run_map, bind_map_left]
    simp only [ReaderT.run_pure, bind_pure_comp, StateT.run_bind, StateT.run_map, bind_assoc,
      bind_map_left]
    simp_rw [MonadSort.swap, SortingMonad.swap]
    simp_rw [MonadSort.cmp_at, SortingMonad.cmp_at]
    simp_rw [modify, modifyGet, MonadStateOf.modifyGet]
    simp_rw [read, readThe, MonadReaderOf.read]
    simp_rw [get, getThe, MonadStateOf.get]
    simp_rw [monadLift, MonadLift.monadLift]
    simp_rw [ReaderT.run]


    -- simp only [Functor.map, WriterT.mk]
    -- rw [StateT.run, ReaderT.run_monadLift, monadLift_self, StateT.modifyGet, ]
    -- simp_rw [ReaderT.read, StateT.run, ReaderT.run]
    -- simp only [Equiv.instTrans_trans, Equiv.Perm.trans_one]
    --  bind_pure_comp, pure_bind]
    -- simp only [bind, WriterT.mk, Functor.map, ReaderT.bind, StateT.bind]
    -- simp only [StateT.modifyGet, pure, Equiv.swap_swap, List.empty_eq, StateT.pure, StateT.map, StateT.get]
    -- simp only [bind, WriterT.mk, List.nil_append, Prod.mk.eta, Equiv.refl_apply, Id.map_eq,
    --   List.append_nil]
    -- simp [MonadSize.size] at i j
    -- apply swap_comm_lemma
