import Mathlib
import Mathlib.Data.List.Sort

inductive GExpr (α : Type) where
  | zero : GExpr α
  | term (power : GExpr α) (coeff : α) (remainder : GExpr α)
  deriving Functor, DecidableEq

variable {α β γ : Type} {n : ℕ}

instance : Zero (GExpr α) where
  zero := GExpr.zero

@[simp]
theorem GExpr.zero_def : (GExpr.zero : GExpr α) = 0 := rfl

notation c "×X^(" p ")+ " r => GExpr.term p c r

def GExpr.sizeOf' : GExpr α → ℕ
  | 0 => 0
  | _ ×X^( p )+ r => 1 + p.sizeOf' + r.sizeOf'

instance : SizeOf (GExpr α) where
  sizeOf := GExpr.sizeOf'

@[simp]
theorem GExpr.sizeOf_zero : sizeOf (0 : GExpr α) = 0 := rfl

@[simp]
theorem GExpr.sizeOf_term (c : α) (p r) : sizeOf (c ×X^( p )+ r) = 1 + sizeOf p + sizeOf r := rfl

def GExpr.height {α} : GExpr α → ℕ
  | 0 => 0
  | _ ×X^( p )+ r => max (1 + p.height) r.height

def List.height {α} : List (α × GExpr α) → ℕ
  | [] => 0
  | (_, p) :: r => max (1 + p.height) (r.height)

def GExpr.Terms.toFun_aux : GExpr α → List (α × GExpr α)
  | 0 => []
  | c ×X^( p )+ r => (c, p) :: GExpr.Terms.toFun_aux r

def GExpr.Terms.invFun_aux : List (α × GExpr α) → GExpr α
  | [] => 0
  | (c, p) :: xs => c ×X^( p )+ GExpr.Terms.invFun_aux xs

instance GExpr.terms : GExpr α ≃ List (α × GExpr α) where
  toFun := GExpr.Terms.toFun_aux
  invFun := GExpr.Terms.invFun_aux
  left_inv x := by
    induction x
    case zero => simp [GExpr.Terms.toFun_aux, GExpr.Terms.invFun_aux]
    case term power coeff remainder power_ih remainder_ih =>
      simp [GExpr.Terms.toFun_aux, GExpr.Terms.invFun_aux]
      apply remainder_ih
  right_inv x := by
    induction x
    case nil => simp [GExpr.Terms.toFun_aux, GExpr.Terms.invFun_aux]
    case cons head tail tail_ih =>
      let ⟨c, p⟩ := head
      simp [GExpr.Terms.toFun_aux, GExpr.Terms.invFun_aux]
      apply tail_ih

@[simp]
theorem GExpr.terms_toFun_undef : (GExpr.Terms.toFun_aux : GExpr α → _) = GExpr.terms := rfl

@[simp]
theorem GExpr.terms_invFun_undef : (GExpr.Terms.invFun_aux : _→ GExpr α) = GExpr.terms.symm := rfl

abbrev List.unterms : List (α × GExpr α) ≃ GExpr α := GExpr.terms.symm

@[simp]
theorem GExpr.terms_zero {α} : (0 : GExpr α).terms = [] := rfl

@[simp]
theorem GExpr.terms_cons {α} {c p r} :
  (c ×X^( p )+ r : GExpr α).terms = (c, p) :: r.terms := rfl

@[simp]
theorem List.unterms_nil {α} : ([] : List (α × GExpr α)).unterms = 0  := rfl

@[simp]
theorem List.unterms_cons {α} {c : α} {p xs} :
  ((c, p) :: xs).unterms = c ×X^(p)+ xs.unterms := rfl

section

open GExpr

theorem terms_height (x : GExpr α) : x.terms.height = x.height := by
    induction x
    case zero => simp [List.height, height]
    case term c p r p_ih r_ih =>
      simp [List.height, height]
      rw [r_ih]

theorem mem_lt_list_height {l : List (α × GExpr α)} {x} : x ∈ l → x.2.height < l.height := by
  intros c_p_in_l
  induction c_p_in_l
  case head as =>
    simp [List.height]
  case tail b as a h =>
    simp [List.height]
    right
    exact h

end

mutual

def GExpr.byLevel (f : List (α × β) → β) (x : GExpr α) : β :=
  have := terms_height x
  f (GExpr.byLevel_aux f x.terms)
  termination_by (x.height * 2 + 1)

def GExpr.byLevel_aux (f : List (α × β) → β) (l : List (α × GExpr α)) : List (α × β) :=
  have : ∀ x ∈ l, x.2.height < l.height := by apply mem_lt_list_height
  have l' := l.attachWith (λ (_, p) => p.height < l.height) this
  l'.map (λ ⟨(a, p), p_h⟩ ↦ (a, GExpr.byLevel f p))
  termination_by (l.height * 2)

end

inductive GExpr.lex_lt [PartialOrder α] : GExpr α → GExpr α → Prop where
  | zero_lt_term (c p r) : GExpr.lex_lt 0 (c ×X^(p)+ r )
  | lt_of_power_lt (c₀ c₁ p₀ p₁ r₀ r₁)
    (p_lt : p₀.lex_lt p₁) : (c₀ ×X^(p₀)+ r₀ ).lex_lt (c₁ ×X^(p₁)+ r₁)
  | lt_of_coeff_lt (c₀ c₁ p r₀ r₁)
    (c_lt : c₀ < c₁) : (c₀ ×X^(p)+ r₀ ).lex_lt (c₁ ×X^(p)+ r₁)
  | lt_of_remainder_lt (c p r₀ r₁)
    (r_lt : r₀.lex_lt r₁) : (c ×X^(p)+ r₀ ).lex_lt (c ×X^(p)+ r₁)

open GExpr.lex_lt

theorem leading_powers [PartialOrder α] {c₀ c₁ : α} {p₀ p₁ r₀ r₁} :
  (c₀ ×X^(p₀)+ r₀).lex_lt (c₁ ×X^(p₁)+ r₁) → (p₀.lex_lt p₁ ∨ p₀ = p₁) := by
  intros h
  cases h
  case lt_of_power_lt p_lt =>
    left
    exact p_lt
  case lt_of_coeff_lt =>
    right
    rfl
  case lt_of_remainder_lt =>
    right
    rfl

instance [PartialOrder α] : IsStrictOrder (GExpr α) GExpr.lex_lt where
  irrefl a h := by
    induction a
    case zero => cases h
    case term coeff power remainder power_ih remainder_ih =>
      cases h
      case lt_of_power_lt h => exact power_ih h
      case lt_of_coeff_lt h => exact lt_irrefl _ h
      case lt_of_remainder_lt h => exact remainder_ih h
  trans x y z x_lt_y y_lt_z := by
    revert x
    induction y_lt_z
    case zero_lt_term =>
      intros x x_lt_y
      cases x_lt_y
    case lt_of_power_lt cy cz py pz ry rz py_lt_pz p_ih =>
      intros x x_lt_y
      cases x
      case zero => constructor
      case term cx px rx =>
        cases x_lt_y
        case lt_of_power_lt p_lt =>
          apply GExpr.lex_lt.lt_of_power_lt
          apply p_ih _ p_lt
        case lt_of_coeff_lt c_lt =>
          apply GExpr.lex_lt.lt_of_power_lt
          apply py_lt_pz
        case lt_of_remainder_lt =>
          apply GExpr.lex_lt.lt_of_power_lt
          apply py_lt_pz
    case lt_of_coeff_lt cy cz p ry rz c_lt =>
      intros x x_lt_y
      cases x
      case zero => constructor
      case term cx px rx =>
        cases x_lt_y
        case lt_of_power_lt p_lt =>
          apply GExpr.lex_lt.lt_of_power_lt
          exact p_lt
        case lt_of_coeff_lt c_lt2 =>
          apply GExpr.lex_lt.lt_of_coeff_lt
          apply lt_trans c_lt2 c_lt
        case lt_of_remainder_lt r_lt =>
          apply GExpr.lex_lt.lt_of_coeff_lt
          exact c_lt
    case lt_of_remainder_lt c p rx ry r_lt r_lt_ih =>
      intros x x_lt_y
      cases x
      case zero => constructor
      case term cx px rx =>
        cases x_lt_y
        case lt_of_power_lt p_lt =>
          apply GExpr.lex_lt.lt_of_power_lt
          exact p_lt
        case lt_of_coeff_lt c_lt =>
          apply GExpr.lex_lt.lt_of_coeff_lt
          exact c_lt
        case lt_of_remainder_lt r r_lt2 =>
          apply GExpr.lex_lt.lt_of_remainder_lt
          apply r_lt_ih
          exact r_lt2

instance [PartialOrder α] : PartialOrder (GExpr α) := partialOrderOfSO GExpr.lex_lt

namespace Ordering

end Ordering

section cmp

open Ordering

def GExpr.cmp [LinearOrder α] : (GExpr α) → (GExpr α) → Ordering
  | 0, 0 => eq
  | _ ×X^( _ )+ _, 0 => gt
  | 0, _ ×X^( _ )+ _ => lt
  | c₁ ×X^( p₁ )+ r₁, c₂ ×X^( p₂ )+ r₂ =>
    ((p₁.cmp p₂).then (Ord.compare c₁ c₂)).then (r₁.cmp r₂)

theorem GExpr.cmp_Compares [LinearOrder α] : ∀ (a b : GExpr α), (a.cmp b).Compares a b
  | 0, 0 => rfl
  | _ ×X^( _ )+ _, 0 => by
    simp [cmp]
    constructor
  | 0, _ ×X^( _ )+ _ => by
    simp [cmp]
    constructor
  | c₁ ×X^( p₁ )+ r₁, c₂ ×X^( p₂ )+ r₂ =>
    by
    have p_h := GExpr.cmp_Compares p₁ p₂
    revert p_h
    simp [cmp]
    match p₁.cmp p₂ with
    | lt =>
      rw [Compares]
      intros p_h
      apply lt_of_power_lt
      · apply p_h
    | gt =>
      rw [Compares]
      intros p_h
      apply lt_of_power_lt
      · apply p_h
    | eq =>
      simp
      intros p_h
      cases p_h
      have c_h : (compare c₁ c₂).Compares c₁ c₂ := by
        rw [← compare_iff]
      match h : compare c₁ c₂ with
      | lt =>
        simp [Ordering.then]
        apply lt_of_coeff_lt
        simp [h] at *
        exact c_h
      | gt =>
        simp [Ordering.then]
        apply lt_of_coeff_lt
        simp [h] at *
        exact c_h
      | eq =>
        simp [Ordering.then, h] at *
        cases c_h
        have r_h := GExpr.cmp_Compares r₁ r₂
        revert r_h
        match h : r₁.cmp r₂ with
        | lt =>
          simp
          apply lt_of_remainder_lt
        | gt =>
          simp
          apply lt_of_remainder_lt
        | eq => simp


end cmp

instance [LinearOrder α] : LinearOrder (GExpr α) := linearOrderOfCompares GExpr.cmp GExpr.cmp_Compares


class Zero' (α : Type*) extends AddSemigroup α where
  toZero : α → α
  left_id' (x y : α) : toZero x + y = y
  right_id' (x y : α) : x + toZero y = x

abbrev toZero [Zero' α] : α → α := Zero'.toZero

@[simp]
theorem Zero'.left_id [Zero' α] (x y : α) : toZero x + y = y := Zero'.left_id' x y

@[simp]
theorem Zero'.right_id [Zero' α] (x y : α) : x + toZero y = x := Zero'.right_id' x y

instance [AddMonoid α] : Zero' α where
  toZero _ := 0
  left_id' := by simp
  right_id' := by simp

instance : Zero' (Fin 0) where
  toZero x := x.elim0
  left_id' x := x.elim0
  right_id' x := x.elim0

def ne_zero' [Zero' α] (x : α) : Prop := x ≠ toZero x

theorem toZero_const [Zero' α] : ∀ {x y : α}, toZero x = toZero y := by
  intros x y
  trans toZero x + toZero y
  · rw [Zero'.right_id (toZero x)]
  · rw [Zero'.left_id x]

abbrev gt₂ [PartialOrder β] (x y : α × β) : Prop := y.2 < x.2

def GExpr.power : GExpr α → WithBot (GExpr α)
  | 0 => ⊥
  | _ ×X^(p)+ _ => p

@[simp]
theorem GExpr.power_zero : (0 : GExpr α).power = ⊥ := rfl

@[simp]
theorem GExpr.power_term (c : α) (p r) : (c ×X^(p)+ r).power = ↑p := rfl


def GExpr.remainder : GExpr α → WithBot (GExpr α)
  | 0 => ⊥
  | _ ×X^(_)+ r => r

@[simp]
theorem GExpr.remainder_zero : (0 : GExpr α).remainder = ⊥ := rfl

@[simp]
theorem GExpr.remainder_term (c : α) (p r) : (c ×X^(p)+ r).remainder = ↑r := rfl

def WithBot.allP (P : α → Prop) : WithBot α → Prop := WithBot.recBotCoe True P
def WithBot.existsP (P : α → Prop) : WithBot α → Prop := WithBot.recBotCoe False P

inductive GExpr.Sorted [PartialOrder α] [Zero' α] : GExpr α → Prop where
  | intro {x : GExpr α} (l_sorted : x.terms.Sorted gt₂)
    (all_p_sorted : ∀ c p, (c,p) ∈ x.terms → p.Sorted)
    (all_c_ne_zero : ∀ c p, (c,p) ∈ x.terms → ne_zero' c) :
    x.Sorted


@[simp]
theorem GExpr.sorted_zero [PartialOrder α] [Zero' α] : (0 : GExpr α).Sorted := ⟨by simp, by simp, by simp⟩

@[simp]
theorem GExpr.zero_is : (zero : GExpr α) = 0 := rfl

@[simp]
theorem GExpr.zero_toList : (0 : GExpr α).terms = [] := rfl

@[simp]
theorem GExpr.term_toList {c p r} : (c ×X^(p)+ r : GExpr α).terms = (c, p) :: r.terms := rfl

theorem GExpr.Sorted.l_sorted [PartialOrder α] [Zero' α] {x : GExpr α} : x.Sorted → x.terms.Sorted gt₂
  | intro _ _ _ => by assumption

theorem GExpr.Sorted.all_P_sorted [PartialOrder α] [Zero' α] {x : GExpr α} : x.Sorted → ∀ c p, (c,p) ∈ x.terms → p.Sorted
  | intro _ _ _ => by assumption

theorem GExpr.Sorted.all_c_ne_zero [PartialOrder α] [Zero' α] {x : GExpr α} : x.Sorted → ∀ c p, (c,p) ∈ x.terms → ne_zero' c
  | intro _ _ _ => by assumption

@[simp]
theorem GExpr.zero_sorted [PartialOrder α] [Zero' α] : (0 : GExpr α).Sorted := ⟨by simp, by simp, by simp⟩

@[simp]
theorem GExpr.Sorted.power [PartialOrder α] [Zero' α] (c) (p r : GExpr α) (cpr_h : (c×X^(p)+r).Sorted) : p.Sorted :=
  match cpr_h with
  | ⟨l_sorted, all_p_sorted, all_c_ne_zero⟩ => by
    apply all_p_sorted c
    simp [GExpr.power, WithBot.allP]

@[simp]
theorem GExpr.power_sorted [PartialOrder α] [Zero' α] (x : GExpr α) (x_h : x.Sorted) : x.power.allP GExpr.Sorted :=
  match x, x_h with
  | 0, _ => by
    simp [GExpr.power, WithBot.allP]
  | c ×X^(p)+ _, ⟨l_sorted, all_p_sorted, all_c_ne_zero⟩ => by
    apply all_p_sorted c
    simp [GExpr.power, WithBot.allP]

@[simp]
theorem GExpr.Sorted.remainder [PartialOrder α] [Zero' α] {c} {p r : GExpr α} (cpr_h : (c ×X^(p)+ r).Sorted) : r.Sorted := by
  let ⟨l_sorted, all_p_sorted, all_c_ne_zero⟩ := cpr_h
  constructor
  case l_sorted =>
    simp at l_sorted
    exact l_sorted.2
  case all_p_sorted =>
    intros c p cp_in
    apply all_p_sorted c
    simp
    right
    exact cp_in
  case all_c_ne_zero =>
    intros c p cp_in
    apply all_c_ne_zero _ p
    simp
    right
    exact cp_in

@[simp]
theorem GExpr.remainder_sorted [PartialOrder α] [Zero' α] {x : GExpr α} (x_h : x.Sorted) : x.remainder.allP GExpr.Sorted :=
  match x, x_h with
  | 0, _ => by
    simp [GExpr.remainder, WithBot.allP]
  | c ×X^(p)+ r, h => by
    simp [WithBot.allP, GExpr.remainder]
    apply GExpr.Sorted.remainder h

@[simp]
theorem GExpr.sorted_powers_front [PartialOrder α] [Zero' α] (x : GExpr α) (x_Sorted : x.Sorted) (c p) (cp_in : (c,p) ∈ x.terms) : p ≤ x.power := by
  revert c p
  induction x
  · intros c p cp_in
    simp [] at cp_in
  case term p' c' r' _ r'_ih =>
    intros c p cp_in
    simp at *
    cases cp_in
    case inl h => rw [h.2]
    case inr h =>
      have r'_Sorted : r'.Sorted := GExpr.remainder_sorted x_Sorted
      cases r'
      case zero => cases h
      case term p₂ c₂ r₂ =>
        simp [GExpr.power] at *
        trans p₂
        apply r'_ih r'_Sorted _ (cp_in := h)
        have := x_Sorted.l_sorted
        simp at this
        apply le_of_lt
        apply this.1.1

@[simp]
theorem GExpr.term_sorted [PartialOrder α] [Zero' α] (c : α) (p r : GExpr α)
  (c_ne_zero : ne_zero' c)
  (p_ih : p.Sorted)
  (p_gt : r.power < p)
  (r_ih : r.Sorted) : (c ×X^(p)+ r).Sorted := by
  induction r
  case zero =>
    simp
    constructor
    · simp
    · intros x y h
      simp at h
      cases h.2
      exact p_ih
    · simp
      exact c_ne_zero

  case term p₀ c₀ r₀ _ r₀_ih =>
    simp at p_ih p_gt
    constructor
    simp only [terms_cons, List.sorted_cons, List.mem_cons, gt_iff_lt, forall_eq_or_imp, Prod.forall]
    have := r_ih.l_sorted
    simp only [terms_cons, List.sorted_cons, gt_iff_lt, Prod.forall] at this
    let ⟨sorted_here, sorted_there⟩ := this; clear this
    split_ands
    · exact p_gt
    · intros x y xy_in_r₀
      trans p₀
      · apply sorted_here
        · exact xy_in_r₀
      · exact p_gt
    · apply sorted_here
    · apply sorted_there
    · intros c₁ p₁ c₁p₁_in
      set r := c₀×X^(p₀)+ r₀
      simp at c₁p₁_in
      cases c₁p₁_in
      case inl h =>
        rw [h.1, h.2] at *; clear h c₁ p₁
        exact p_ih
      case inr h =>
        apply GExpr.Sorted.all_P_sorted r_ih _ _ h
    case all_c_ne_zero =>
      intros c₁ p₁ c₁p₁_in
      set r := c₀×X^(p₀)+ r₀
      simp at c₁p₁_in
      cases c₁p₁_in
      case inl h =>
        rw [h.1, h.2] at *; clear h c₁ p₁
        assumption
      case inr h =>
        apply GExpr.Sorted.all_c_ne_zero r_ih _ _ h

instance (a : α) [Zero' α] [LinearOrder α] : Decidable (ne_zero' a) := by
  simp [ne_zero']
  infer_instance

abbrev SGExpr (α) [PartialOrder α] [Zero' α] : Type := {expr : GExpr α // expr.Sorted}

instance [PartialOrder α] [Zero' α] : PartialOrder (SGExpr α) where
  le_antisymm a b := by
    let ⟨a, _⟩ := a
    let ⟨b, _⟩ := b
    simp at *
    apply le_antisymm

instance [LinearOrder α] [Zero' α] : LinearOrder (SGExpr α) where

  le_total a b := by
    let ⟨a, _⟩ := a
    let ⟨b, _⟩ := b
    simp at *
    apply le_total

  decidableLE a b := by
    let ⟨a, _⟩ := a
    let ⟨b, _⟩ := b
    simp at *
    apply LinearOrder.decidableLE

  min_def a b := by
    let ⟨a, _⟩ := a
    let ⟨b, _⟩ := b
    rw [min_def]

  max_def a b := by
    let ⟨a, _⟩ := a
    let ⟨b, _⟩ := b
    rw [max_def]

  compare_eq_compareOfLessAndEq a b := by
    let ⟨a, _⟩ := a
    let ⟨b, _⟩ := b
    rw [LinearOrder.compare_eq_compareOfLessAndEq]
    congr

instance [PartialOrder α] [Zero' α] : Zero (SGExpr α) where
  zero := ⟨0, by simp⟩

theorem SGExpr.zero_def [PartialOrder α] [Zero' α] : (0 : SGExpr α) = ⟨0, by simp⟩ := rfl

@[simp]
theorem SGExpr.zero_val [PartialOrder α] [Zero' α] : (0 : SGExpr α).val = 0 := rfl

def SGExpr.destruct [PartialOrder α] [Zero' α] : SGExpr α → Option (α × SGExpr α × SGExpr α)
  | ⟨0, _⟩ => none
  | ⟨c ×X^(p )+ r, h⟩ =>
    have p' := ⟨p, h.power⟩
    have r' := ⟨r, h.remainder⟩
    some <| (c, p', r')

@[simp]
theorem SGExpr.destruct_term [PartialOrder α] [Zero' α] (c : α) (p r : GExpr α) (h) :
  SGExpr.destruct ⟨c ×X^(p )+ r, h⟩ = some (c, ⟨p, h.power⟩, ⟨r, h.remainder⟩) := rfl

@[simp]
theorem SGExpr.zero [PartialOrder α] [Zero' α] :
  SGExpr.destruct (0 : SGExpr α) = none := rfl

@[simp]
theorem SGExpr.zero' [PartialOrder α] [Zero' α] (h) :
  SGExpr.destruct (⟨0, h⟩ : SGExpr α) = none := rfl

def List.max_power [LinearOrder α] [Zero' α] (l : List (α × SGExpr α)) :=
  (l.map Prod.snd).maximum

theorem List.unterms_Sorted [PartialOrder α] [Zero' α] (l : List (α × GExpr α))
  (l_Sorted : l.Sorted gt₂)
  (all_p_sorted : ∀ c p, (c, p) ∈ l → p.Sorted)
  (all_c_ne_zero : ∀ c p, (c, p) ∈ l → ne_zero' c)
  : l.unterms.Sorted := by
  constructor
  case l_sorted => simp; exact l_Sorted
  case all_p_sorted => simp; exact all_p_sorted
  case all_c_ne_zero => simp; exact all_c_ne_zero

section sort_aux

variable [LinearOrder α] [Zero' α]

def onGExpr (r : GExpr α → GExpr α → β) (x y : α × SGExpr α) : β := r x.2.1 y.2.1

def c_ne_zero (c : α × SGExpr α) : Bool := (ne_zero' c.1)

def pull_out_coeff [LinearOrder α] [Zero' α] : (α × SGExpr α) → Option (α × SGExpr α) → Option (α × SGExpr α)
  | cp, none => cp
  | (c₁, p₁), some (c₀, _) => (c₁ + c₀, p₁)

variable (l : List (α × SGExpr α))

def ge₂ : α × SGExpr α → α × SGExpr α → Bool := onGExpr (· ≥ ·)

def sorted_list := l.mergeSort (le := ge₂)

theorem sorted_list_aux : onGExpr (. ≥ ·) = (λ a b : (α × SGExpr α) => ge₂ a b = true) := by
  funext a b
  simp [onGExpr, ge₂]

theorem sorted_list_sorted : (sorted_list l).Sorted (onGExpr (· ≥ ·)) := by
  rw [sorted_list]
  have := List.sorted_mergeSort (le := ge₂) (l := l)
  rw [sorted_list_aux]
  apply this
  case trans =>
    intros a b c
    simp only [ge₂, onGExpr, ge_iff_le, Subtype.coe_le_coe, decide_eq_true_eq]
    intros ab bc
    apply le_trans bc ab
  case total =>
    intros a b
    simp [ge₂, onGExpr]
    apply le_total

def factor_out_coeff (new : (α × GExpr α)) (sofar : List (α × GExpr α)) : List (α × GExpr α) :=
  match sofar with
  | [] => new :: []
  | old::olds =>
    if new.2 = old.2
    then 

def factored_list := (sorted_list l).foldr factor_out_coeff []

def filtered_list := (factored_list l).filter c_ne_zero

theorem filtered_list_sorted_aux (r : γ → γ → Prop) (f : γ → Bool) (l : List γ) (l_sorted : l.Sorted r) : (l.filter f).Sorted r := by
  induction l
  case nil => simp
  case cons head tail tail_ih =>
    simp at l_sorted
    let ⟨head_ge, tail_sorted⟩ := l_sorted
    have := tail_ih tail_sorted
    simp [List.filter]
    split
    next =>
      simp
      split_ands
      · intros b b_in _
        apply head_ge b b_in
      · exact this
    exact this

theorem filtered_list_c_ne_zero : ∀ pair ∈ filtered_list l, c_ne_zero pair := by
  simp [filtered_list, List.mem_filter]

theorem filtered_list_sorted : (filtered_list l).Sorted (onGExpr (· ≥ ·)) := by
  simp [filtered_list]
  apply filtered_list_sorted_aux
  apply factored_list_sorted

def final_list := (factored_list l).map (λ (c, p) => (c, p.val))

def GExpr.sort_aux : SGExpr α :=  by
  exists (final_list l).unterms
  constructor
  case l_sorted =>

end sort_aux

def GExpr.sort [LinearOrder α] [Zero' α] (x : GExpr α) : SGExpr α := x.byLevel GExpr.sort_aux
