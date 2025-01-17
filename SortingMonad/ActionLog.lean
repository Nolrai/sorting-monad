import Mathlib

universe u v

class ReturnType (α : Type) where
  ret : α → Type

open ReturnType

def FreeMonad (Action : Type) [ReturnType Action] (α : Type) :=
  (M : Type → Type) → [Monad M] → [LawfulMonad M] → (∀ a : Action, M (ret a)) → M α

@[inline]
def FreeMonad.run {Action} [ReturnType Action] {α} (m : FreeMonad Action α)
  {M : Type → Type} [inst₀ : Monad M] [inst₀ : LawfulMonad M]
  (interpreter : ∀ a : Action, M (ret a)) : M α := m M interpreter

instance {Action} [ReturnType Action] : Monad (FreeMonad Action) where
  pure a _ _ _ _ := pure a
  bind ma fm M _ _ interpreter := do
    let a <- ma M interpreter
    (fm a) M interpreter

theorem FreeMonad.seqLeft_default {α β Action} [ReturnType Action] (x : FreeMonad Action α) (y : FreeMonad Action β) :
  (x <* y) = do {let a <- x; let _ <- y; pure a}:= by
    funext M monad lawfulMonad run
    congr

theorem FreeMonad.seqRight_default {α β Action} [ReturnType Action] (x : FreeMonad Action α) (y : FreeMonad Action β) :
  (x *> y) = do {let _ <- x; y}:= by
    funext M monad lawfulMonad run
    congr


instance {Action} [ReturnType Action] : LawfulMonad (FreeMonad Action) := by
  apply LawfulMonad.mk'
  case id_map =>
    intros α x
    funext M monad lawfulMonad toM
    simp [Functor.map]
    trans ((x M toM) >>= pure)
    rfl
    rw [bind_pure]
  case pure_bind =>
    intros α β x f
    simp [pure, bind]
  case bind_assoc =>
    intros α β γ x f g
    simp [bind]
  case map_const =>
    intros α β a mb
    simp [Functor.map, Functor.mapConst]
  case seqLeft_eq =>
    intros α β x y
    apply FreeMonad.seqLeft_default
  case seqRight_eq =>
    intros α β x y
    apply FreeMonad.seqRight_default
  case bind_pure_comp := by
    intros α β f x
    congr
  case bind_map := by
    intros α β f x
    congr

section Log
open Batteries

variable {Action ActionRet} {α β γ} {M : Type → Type} {ω}


def Log := Batteries.DList

def Batteries.DList.ext : ∀ (x y : DList α), x.toList = y.toList → x = y
  | ⟨x₁, x₂⟩, ⟨y₁, y₂⟩, h => by
    simp at h
    congr
    funext l
    rw [x₂, y₂, h]

def Batteries.DList.ext_iff (x y : DList α) : x = y ↔ x.toList = y.toList  where
  mp h := by {cases h; simp only [toList]}
  mpr := Batteries.DList.ext x y

instance : Mul (Log α) where
  mul := λ (x y : DList α) => x ++ y

instance : One (Log α) where
  one := (∅ : DList α)

theorem Log.mul_def : (x y : Log α) → x * y = DList.ofList ((x : DList α).toList ++ (y : DList α).toList)
  | ⟨x₁, x₂⟩, ⟨y₁, y₂⟩ => by
    apply DList.ext
    rw [← DList.toList_append]
    simp only [HMul.hMul, Mul.mul]
    rw [DList.toList_ofList]

theorem Log.mul_assoc : (x y z : Log α) → x * y * z = x * (y * z)
  | ⟨x₁, x₂⟩, ⟨y₁, y₂⟩, ⟨z₁, z₂⟩ => by
    simp only [mul_def, DList.toList_ofList]
    rw [List.append_assoc]

theorem Log.one_mul : (x : Log α) → 1 * x = x
  | ⟨x₁, x₂⟩ => by
    apply DList.ext
    simp [mul_def, One.one, DList.empty, DList.append]

theorem Log.mul_one : (x : Log α) → x * 1 = x
  | ⟨x₁, x₂⟩ => by
    apply DList.ext
    simp [mul_def, One.one, DList.empty, DList.append]

instance : Monoid (Log α) where
  one_mul := Log.one_mul
  mul_one := Log.mul_one
  mul_assoc := Log.mul_assoc

instance : Singleton α (Log α) where
  singleton := DList.singleton

def FreeMonad.withLog [Monad M] [LawfulMonad M] [ReturnType Action] (ma : FreeMonad Action α) (interpreter : (a : Action) → M (ret a)) :
  M (α × Log Action) :=
  ma (WriterT _ M) λ action ↦ do
    tell (singleton action)
    interpreter action

def mkAction [ReturnType Action] (a : Action) : FreeMonad Action (ret a) :=
  λ _ _ _ run => run a

prefix:20 "#" => mkAction

end Log
