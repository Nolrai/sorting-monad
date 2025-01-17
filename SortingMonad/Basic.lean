import Mathlib
import SortingMonad.ActionLog

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
  ⟨(λ i => i ≤? i) =<< mi⟩= false
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

structure Swap (n : ℕ) where
  left : Fin n
  right : Fin left

variable {n : ℕ}

@[inline]
instance : ReturnType (Swap n) where
  ret _ := Unit

open ReturnType

def run_swap (a : Swap n) : StateM (Vector α n) (ret a) :=
  modify (λ v => v.swap a.left a.right)

structure Cmp (n : ℕ) where
  left : Fin n
  right : Fin n

@[inline]
instance : ReturnType (Cmp n) where
  ret _ := Bool

def run_cmp (a : Cmp n) [LinearOrder α] : StateM (Vector α n) (ret a) := do
  let (v : Vector α n) <- get
  pure <| decide <| (v.get a.left) < (v.get a.right)

abbrev SortingAction (n) := (Swap n ⊕ Cmp n)

instance [ReturnType α] [ReturnType β] : ReturnType (α ⊕ β) where
  ret a := a.rec ReturnType.ret ReturnType.ret

def SortingAction.run {n} [LinearOrder α] (a : SortingAction n) :
  StateM (Vector α n) (ret a) :=
  match a with
  | Sum.inl swap => run_swap swap
  | Sum.inr cmp => run_cmp cmp

def Swap.castLE {m} (n_le_m : n ≤ m) : Swap n → Swap m
  | Swap.mk l r => Swap.mk (l.castLE n_le_m) <| r.castLE <| by simp only [Fin.coe_castLE, le_refl]

def Cmp.castLE {m} (n_le_m : n ≤ m) : Cmp n → Cmp m
  | {left := left, right := right} => {left := left.castLE n_le_m, right := right.castLE n_le_m}

def SortingAction.castLE {m} (n_le_m : n ≤ m) : SortingAction n → SortingAction m :=
  bimap (Swap.castLE n_le_m) (Cmp.castLE n_le_m)

def SortingMonad n := FreeMonad (SortingAction n)

instance : Monad (SortingMonad n) := (inferInstance : Monad (FreeMonad (SortingAction n)))

instance : LawfulMonad (SortingMonad n) := (inferInstance : LawfulMonad (FreeMonad (SortingAction n)))

def cmp_at (i : Fin n) (j : Fin n) : SortingMonad n Bool :=
  # (Sum.inr (Cmp.mk i j))

def swap_at (i : Fin n) (j : Fin i) : SortingMonad n Unit :=
  # (Sum.inl (Swap.mk i j))

def compare_and_swap (i : Fin n) (j : Fin i) : SortingMonad n Unit := do
  let b <- cmp_at i (j.castLE i.2)
  if b
    then swap_at i j
    else pure ()

def bubbleSort : FreeMonad (SortingAction n) Unit :=
    for i in List.finRange n do
    for j in List.finRange i.1 do
      compare_and_swap i j

def inversions [LinearOrder α] : List α → ℕ
  | [] => 0
  | x :: xs => (xs.filter (not ∘ ↑(x ≤ ·))).length

def SortingMonad.run
  (m : SortingMonad n α)
  [LinearOrder β]
  (v₀ : Vector β n)
  : α × Vector β n
  := flip StateT.run v₀ <| FreeMonad.run m SortingAction.run

def as_modify {α} [LinearOrder α]
  (m : SortingMonad n Unit) (v₀ : Vector α n) : Vector α n :=
    Prod.snd <| m.run v₀

theorem as_modify_swap_at [LinearOrder α] {i j} :
  as_modify (swap_at i j) = (λ v : Vector α n => v.swap i j) := by
  funext v
  simp [swap_at, SortingMonad.run, as_modify]
  simp [FreeMonad.run, flip, StateT.run, mkAction, SortingAction.run, run_swap]
  simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]

theorem as_modify_compare_and_swap [LinearOrder α] {i j} :
  as_modify (compare_and_swap i j) =
    λ v : Vector α n =>
    if v[Fin.castLE i.2 j] < v[i]
    then v.swap i j
    else v := by
  funext v
  simp [compare_and_swap]
  simp [swap_at, cmp_at, SortingMonad.run, as_modify, FreeMonad.run]
  simp [flip, StateT.run, pure, bind, StateT.bind, mkAction, SortingAction.run,
        run_cmp, get, getThe, MonadStateOf.get, Functor.map, StateT.map, StateT.get, pure,
        bind, StateT.bind, StateT.get, pure, StateT.pure]
  split_ifs
  · simp [mkAction, SortingAction.run, run_swap, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
  case neg h₁ h₂ =>
    exfalso
    apply h₂
    apply h₁
  case pos h₁ h₂ =>
    exfalso
    apply h₁
    apply h₂
  · simp [pure, StateT.pure]

theorem as_modify_seq [LinearOrder α]  (f g : SortingMonad n Unit) :
  as_modify (f *> g) = (as_modify g ∘ as_modify f : Vector α n → Vector α n) := by
  funext v
  simp [as_modify, seqRight_eq_bind, SortingMonad.run, FreeMonad.run, flip, StateT.run]
  simp [bind, StateT.bind]
  congr

def sorted_at [LT α] (v : Vector α n) (i j : Fin n) : Prop := v.get i < v.get j ↔ j < i

theorem compare_and_swap.after
  [LinearOrder α]
  (v : Vector α n) (i j) : sorted_at (as_modify (compare_and_swap i j) v) (Fin.castLE i.2 j) i := by
  simp [sorted_at, as_modify_compare_and_swap]
  apply Iff.trans (b := False)
  case h₂ =>
    have ⟨i, i_lt_n⟩ := i
    have ⟨j, j_lt_i⟩ := j
    simp only [Fin.castLE_mk, Fin.mk_lt_mk, false_iff, not_lt, ge_iff_le]
    simp at j_lt_i
    apply le_of_lt j_lt_i
  split_ifs
  case pos vj_lt_vi =>
    simp only [Vector.swap, Vector.get_mk, Fin.getElem_fin, Fin.coe_castLE,
      Array.getElem_swap_right, Vector.getElem_toArray, Array.getElem_swap_left, iff_false, not_lt]
    apply le_of_lt vj_lt_vi
  case neg vj_not_lt_vi =>
    simp at *
    assumption


