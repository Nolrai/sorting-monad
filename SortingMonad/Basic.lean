import Mathlib

universe u v

structure Terms (κ : Type u) (π : Type v) [Zero κ] where
  powers : Finset π
  coeffAt : π → κ
  zero_elsewhere : ∀ p, p ∈ coeffAt.support ↔ p ∈ powers

namespace Terms

variable {κ : Type u} {π : Type v} [Zero κ]

instance : GetElem (Terms κ π) π κ (λ _ _ => True) where
  getElem xs p _ := xs.coeffAt p

instance hc {α} [AddCommMagma α] : Std.Commutative (α := α) (· + ·) where
  comm x y := by
    rw [add_comm]

def eval {κ π β} [Zero κ] [AddCommMonoid β] (onTerm : κ → π → β) (expr : Terms κ π) : β := by
  apply expr.powers.fold (· + ·) 0 (λ p => onTerm expr[p] p)

instance : EmptyCollection (Terms κ π) where
  emptyCollection := ⟨∅, λ _ => 0, by simp⟩

instance [DecidableEq π] [DecidableEq κ] : Coe (List (π × κ)) (Terms κ π) where
  coe l :=
    let f p := (l.lookup p).getD 0
    let keys := (l.map Prod.fst).toFinset 

end Terms

def Gold' (κ : Type u) [Zero κ] : ℕ → Type u
  | 0 => PEmpty
  | n+1 => Terms κ (Gold' κ n)

namespace Gold'

variable {κ : Type u} [Zero κ]

@[simp]
theorem zero  : Gold' κ 0 = PEmpty := rfl

@[simp]
theorem succ {n} : Gold' κ (n+1) = Terms κ (Gold' κ n) := rfl

instance {n} : EmptyCollection (Gold' κ (n+1)) where
  emptyCollection := by simp [Gold']; exact ∅

def eval {κ β} [Zero κ] [Ring β] [HomogeneousPow β] (base : β) (toβ : κ → β) : ∀ {n : ℕ}, Gold' κ n → β
  | 0, _ => 0
  | n+1, expr => Terms.eval (π := Gold' κ n) (onTerm := λ k p => toβ k * base ^ (Gold'.eval base toβ p)) expr

end Gold'

def Gold (κ : Type u) [Zero κ] := Σ n, Gold' κ n

namespace Gold

variable {κ : Type u} [Zero κ]

instance : EmptyCollection (Gold κ) where
  emptyCollection := ⟨1, ∅⟩

def eval {κ β} [Zero κ] [Ring β] [HomogeneousPow β] (base : β) (toβ : κ → β) (expr : Gold κ) : β :=
  expr.2.eval base toβ

def toExpr (max : PNat) (n : ℕ) : Sigma (Gold (Fin (max+1))) :=
  if n = 0
  then ∅
  else
    let pn := Nat.log n b
    let place := (max+1) ^ pn
    let c := n / place
    let r := n - c * place
