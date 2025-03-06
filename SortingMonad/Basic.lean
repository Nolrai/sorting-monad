import Mathlib
import Batteries.Data.RBMap.Basic

open Batteries

universe u v

instance MapExt (C P : Type) [Zero C] [LinearOrder C] [LinearOrder P] : Setoid (RBMap P ({c : C // 0 < c}) compare) where
  r x y := x.toList = y.toList
  iseqv := {
    refl x := rfl
    symm := by
      intros x y xy
      apply xy.symm
    trans := by
      intros x y z xy yz
      rw [xy, yz]
  }

def Terms (C P : Type) [Zero C] [LinearOrder C] [p_inst : LinearOrder P] :=
  Quotient (MapExt C P)

namespace Terms

variable {C P : Type} [Zero C] [LinearOrder P] [LinearOrder C] (cmp : P → P → Ordering)

def toDecList : Function.Embedding (Terms C P) (List (Lex (P × {c : C // 0 < c}))) where
  toFun := Quotient.lift (λ x : RBMap _ _ _ => x.toList.reverse) <| by
    intros a b a_equiv_b
    simp
    rw [a_equiv_b]
  inj' := by
    intros x y
    induction x using Quotient.ind; case a x =>
    induction y using Quotient.ind; case a y =>
    simp
    intros h
    rw [Quotient.sound h]

instance : LinearOrder (Terms C P) where
  le x y := x.toDecList ≤ y.toDecList
  le_refl := by simp
  le_trans := by
    simp
    intros x y z
    apply le_trans
  le_antisymm := by
    simp;
    intros a b a_le_b b_le_a
    have := le_antisymm a_le_b b_le_a
    apply Function.Embedding.injective toDecList this
  decidableLE := by simp; infer_instance
  le_total x y := by
    simp
    apply le_total

def map {C' P'} [Zero C'] [LinearOrder C'] [LinearOrder P'] (f : P × {c : C // 0 < c} → P' × {c : C' // 0 < c}) : Terms C P → Terms C' P' :=
  Quotient.map (λ x : RBMap _ _ _ => (x.toList.map f).toRBMap compare) <| by
    simp
    intros a b a_equiv_b
    rw [a_equiv_b]

end Terms

inductive Gold where
  | mk :
