import Mathlib
import Batteries.Data.RBMap.Basic

open Batteries
open RBNode

universe u v z

namespace Batteries.RBSet

variable {α} (cmp : α → α → Ordering)

abbrev RBS := RBSet _ cmp

variable {cmp}

section

variable (c) {lval : RBNode α} (x) {rval : RBNode α}

section

variable (lr_wf : RBNode.WF cmp lval ∧ RBNode.WF cmp rval)

abbrev destruct_aux : RBS cmp × α × RBS cmp :=
  ⟨⟨lval, lr_wf.1⟩, x, ⟨rval, lr_wf.2⟩⟩

end

variable {c x}
variable (wf : RBNode.WF cmp (.node c lval x rval))

include wf
theorem children_wf : RBNode.WF cmp lval ∧ RBNode.WF cmp rval := by
  simp at *
  have ⟨⟨_, _, l_ord, r_ord⟩, ⟨bal_c, bal_n, bal⟩⟩ := wf
  have ⟨l_bal, r_bal⟩ : (∃ c n, lval.Balanced c n) ∧ (∃ c n, rval.Balanced c n) := by
    cases bal
    case red lbal rbal =>
      split_ands
      · exists .black, bal_n
      · exists .black, bal_n
    case black lc n rc lbal rbal =>
      split_ands
      · exists lc, n
      · exists rc, n
  split_ands
  · exact l_ord
  · exact l_bal
  · exact r_ord
  · exact r_bal

end

def destruct : RBS cmp → Option (RBS cmp × α × RBS cmp)
  | ⟨.nil, _⟩ => .none
  | ⟨.node _ _ x _, wf⟩ => .some <| destruct_aux x <| children_wf wf

def left : RBS cmp → Option (RBS cmp) := λ x => x.destruct.map Prod.fst

def right : RBS cmp → Option (RBS cmp) := λ x => x.destruct.map (Prod.snd ∘ Prod.snd)



end RBSet

namespace RBMap

end RBMap

section Terms

variable (M : Type u) {P : Type v} [AddMonoid M] [Preorder M]

def Pos : Type u := Subtype (0 < · : M → Prop)

-- Formal Polynomials with coefficients in M and Powers in P
def Terms (pcmp : P → P → Ordering) : Type _ := RBMap P (Pos M) (cmp := pcmp)

variable {pcmp : P → P → _} {M}

def Terms.monomial (p : P) (c : Pos (M := M)) : Terms M pcmp := RBMap.empty.insert p c

def Terms.pop (x : Terms M pcmp) : Option ((Pos M × P) × Terms M pcmp) := do
  x.max?.map <| λ (p, c) ↦ ((c, p), x.erase p)

instance : EmptyCollection (Terms M pcmp) := ⟨(∅ : RBMap _ _ _)⟩
instance : Zero (Terms M pcmp) := ⟨∅⟩

theorem Terms.empty_is_nil : (∅ : Terms M pcmp) = ⟨.nil, .mk ⟨⟩ .nil⟩ := rfl
theorem Terms.zero_is_nil : (0 : Terms M pcmp) = ⟨.nil, .mk ⟨⟩ .nil⟩ := rfl

theorem Terms.pop_none_iff {x : Terms M pcmp} : (Terms.pop x).isNone ↔ (x = ∅) := by
  rw [Terms.pop]
  match x with
  | {val := .nil, property := _} =>
    simp [RBMap.max?, RBSet.max?, RBNode.max?]
    rfl
  | {val := .node c l v r, property := wf} =>
    simp [RBMap.max?, RBSet.max?, RBNode.max?, Terms.empty_is_nil]
    apply iff_of_false
    clear * -
    revert c l v
    induction r
    case nil => simp [RBNode.max?]
    case node c l v r l_ih r_ih =>
      intros c₀ l₀ v₀
      simp [RBNode.max?]
      apply r_ih
    intros h
    cases h

theorem Terms.pop_zero_eq_none : (0 : Terms M pcmp).pop = none := rfl

def Terms.pop_size {xc xp xs} {x : Terms M pcmp} : some ((xc, xp), xs) = x.pop → x.size = xs.size + 1 :=
  match x with
  | 0 => by
    intros h
    rw [Terms.pop_zero_eq_none] at h
    cases h
  | ⟨.node c l v r, wf⟩ => by
    simp [pop, RBMap.max?, RBSet.max?, Option.map]
    match h : (RBNode.node c l v r).max? with
    | none => simp
    | some (w₀, _) =>
      simp
      intros h₀ h₁ h₂
      cases h₀
      cases h₁
      cases h₂
      simp_rw [RBMap.size_eq]
      rw []


def Terms.cmp (x y : Terms M pcmp) [DecidableLT M] : Ordering :=
  match x.pop, y.pop with
  | none, none => .eq
  | some _, none => .gt
  | none, some _ => .lt
  | some ((xc, xp), xs), some ((yc, yp), ys) => (pcmp xp yp).then ((_root_.cmp xc.1 yc.1).then (cmp xs ys))
  termination_by x.1.size

end Terms

variable (M : Type u) [AddMonoid M] [Preorder M]

def Gold₀ : ℕ → Type u
