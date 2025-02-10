import Mathlib

inductive GExpr (α : Type) where
  | zero : GExpr α
  | term (power : GExpr α) (coeff : α) (remainder : GExpr α)
  deriving Functor, DecidableEq

variable {α β γ : Type} {n : ℕ}

instance : Zero (GExpr α) where
  zero := GExpr.zero

notation c "×X^(" p ")+ " r => GExpr.term p c r

def GExpr.sizeOf : GExpr α → ℕ
  | 0 => 0
  | _ ×X^( p )+ r => 1 + p.sizeOf + r.sizeOf

instance : SizeOf (GExpr α) where
  sizeOf := GExpr.sizeOf

def GExpr.height {α} : GExpr α → ℕ
  | 0 => 0
  | _ ×X^( p )+ r => max (1 + p.height) r.height

def List.height {α} : List (α × GExpr α) → ℕ
  | [] => 0
  | (_, p) :: r => max (1 + p.height) (r.height)

def GExpr.toList : GExpr α → List (α × GExpr α)
  | 0 => []
  | c ×X^( p )+ r => (c, p) :: r.toList

@[simp]
theorem GExpr.toList_zero {α} : GExpr.toList (0 : GExpr α) = ∅ := rfl

@[simp]
theorem GExpr.toList_cons {α} {c p r} :
  (c ×X^( p )+ r : GExpr α).toList = (c, p) :: r.toList := rfl

def List.toGExpr : List (α × GExpr α) → GExpr α
  | [] => 0
  | (c, p) :: xs => c ×X^( p )+ xs.toGExpr

@[simp]
theorem List.toGExpr_empty {α} : (∅ : List (α × GExpr α)).toGExpr = 0  := rfl

@[simp]
theorem List.toGExpr_cons {α} {c : α} {p xs} :
  ((c, p) :: xs).toGExpr = c ×X^(p)+ xs.toGExpr := rfl

section

open GExpr

theorem toList_height (x : GExpr α) : x.toList.height = x.height := by
    induction x
    case zero => simp [List.height, height]
    case term c p r p_ih r_ih =>
      simp [GExpr.toList, List.height, height]
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
  have := toList_height x
  f (GExpr.byLevel_aux f x.toList)
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

section toSorted

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

namespace ToSorted

def toFinmap [Zero' α] [LinearOrder α] : List (α × GExpr α) → Finmap (λ _ : GExpr α => α)
  | [] => ∅
  | (coeff, power) :: xs =>
    let soFar := toFinmap xs
    if coeff = toZero coeff then soFar
    else
      let newCoeff :=
        match soFar.lookup power with
        | none => coeff
        | some oldCoeff => coeff + oldCoeff
      soFar.insert power newCoeff

@[simp]
theorem empty_entries {S : α → Type} : (∅ : Finmap S).entries = (∅ : Multiset _) := rfl

@[simp]
theorem List.empty_entries : [].toGExpr = (0 : GExpr α) := rfl

@[simp]
theorem toFinmap_empty [Zero' α] [LinearOrder α] : toFinmap ([] : List (α × GExpr α)) = ∅ := rfl

def sort_aux_swap : ((_ : GExpr α) × α) → (α × GExpr α)
  | ⟨a, b⟩ => ⟨b, a⟩

abbrev lt₂ {α} [Zero' α] [LinearOrder α] (_ : GExpr α) (a b : α) := a < b

instance [LinearOrder α] [Zero' α] : IsIrrefl ((_ : GExpr α) × α) (Sigma.Lex (· < ·) lt₂) where
  irrefl
    | ⟨a₁, a₂⟩ => by simp [Sigma.lex_iff]


instance [LinearOrder α] [Zero' α] : IsStrictTotalOrder ((_ : GExpr α) × α) (Sigma.Lex (· < ·) lt₂) where

instance [LinearOrder α] [Zero' α] : LinearOrder ((_ : GExpr α) × α) :=
  linearOrderOfSTO (r := Sigma.Lex (· < ·) lt₂)

def sort_aux [Zero' α] [LinearOrder α] (l : List (α × GExpr α)) : GExpr α :=
  let collated : Multiset ((_ : GExpr α) × α) := (toFinmap l).entries
  have instLO : LinearOrder ((_ : GExpr α) × α) := inferInstance
  have : DecidableRel _ := by apply instLO.decidableLE
  let sorted : List ((_ : GExpr α) × α) := Multiset.sort instLO.le collated
  let swapped : List (α × GExpr α) := sorted.map sort_aux_swap
  List.toGExpr swapped

@[simp]
theorem sort_aux_empty [Zero' α] [LinearOrder α] : sort_aux ([] : List (α × GExpr α)) = 0 := by
  simp [sort_aux]


end ToSorted

def GExpr.sort [Zero' α] [LinearOrder α] : GExpr α → GExpr α :=
  GExpr.byLevel ToSorted.sort_aux

@[simp]
theorem sort_aux_singleton [Zero' α] [LinearOrder α] (c p) (c_ne_zero : c ≠ toZero c) : ToSorted.sort_aux ([(c, GExpr.sort p)]
  : List (α × GExpr α)) = c ×X^( p.sort)+ 0 := by
  simp [ToSorted.sort_aux, ToSorted.toFinmap]
  split_ifs
  case pos h => exfalso; apply c_ne_zero; assumption
  case neg c_ne =>
  simp [← Finmap.empty_toFinmap, ToSorted.sort_aux_swap, List.toGExpr]

@[simp]
theorem sort_aux_c_zero [Zero' α] [LinearOrder α] (c p) : ToSorted.sort_aux ([(toZero c, GExpr.sort p)]
  : List (α × GExpr α)) = 0 := by
  simp [ToSorted.sort_aux, ToSorted.toFinmap]
  rw [if_pos]
  rw [ToSorted.empty_entries, Multiset.empty_eq_zero, Multiset.sort_zero]
  simp
  · apply toZero_const

end toSorted

inductive GExpr.sorted [PartialOrder α] [Zero' α] : GExpr α → Prop where
  | zero : (0 : GExpr α).sorted
  | mononomial {c p} : ne_zero' c → p.sorted → (c ×X^(p)+ 0).sorted
  | polynomial {c₁ p₁ c₀ p₀ r}
    (c₁_ne_zero' : ne_zero' c₁)
    (p₁_sorted : p₁.sorted)
    (p₀_lt_p₁ : p₀ < p₁)
    (remainder_sorted : (c₀ ×X^(p₀)+ r).sorted) :
    (c₁ ×X^(p₁)+ (c₀ ×X^(p₀)+ r)).sorted

@[simp]
theorem GExpr.sorted_zero [PartialOrder α] [Zero' α] : (0 : GExpr α).sorted := GExpr.sorted.zero

@[simp]
theorem GExpr.zero_is : (zero : GExpr α) = 0 := rfl

@[simp]
theorem GExpr.zero_toList : (0 : GExpr α).toList = [] := rfl

@[simp]
theorem GExpr.term_toList {c p r} : (c ×X^(p)+ r : GExpr α).toList = (c, p) :: r.toList := rfl

@[simp]
theorem GExpr.sort_zero [Zero' α] [LinearOrder α] : (0 : GExpr α).sort = 0 := by
  simp [sort, byLevel]
  simp [byLevel_aux] --needs to be seperate so we dont infinately recurse

instance (a : α) [Zero' α] [LinearOrder α] : Decidable (ne_zero' a) := by
  simp [ne_zero']
  infer_instance

@[simp]
theorem GExpr.sort_monomial [Zero' α] [LinearOrder α] {c p} : (c ×X^( p )+ 0 : GExpr α).sort =
  if ne_zero' c
  then (c ×X^( p.sort )+ 0 : GExpr α)
  else 0 := by
  have : byLevel ToSorted.sort_aux p = p.sort := rfl
  split_ifs
  case pos h =>
    simp [GExpr.sort]
    rw [byLevel, byLevel_aux, GExpr.toList, GExpr.toList_zero, List.empty_eq]
    simp
    rw [this, sort_aux_singleton]
    · apply h
  case neg h =>
    simp [GExpr.sort]
    rw [byLevel, byLevel_aux, GExpr.toList, GExpr.toList_zero, List.empty_eq]
    simp [ne_zero'] at h
    rw [h]
    simp
    rw [this, sort_aux_c_zero]

theorem GExpr.sort'_sorted [LinearOrder α] [Zero' α] : (expr : GExpr α) → expr.sort.sorted
  | 0 => by simp
  | c ×X^( p )+ 0 => by
    simp
    split_ifs
    case pos h =>
      apply sorted.mononomial h (GExpr.sort'_sorted p)
  | c₁ ×X^( p₁ )+ c₀ ×X^( p₀ )+ r₀ => by
    

theorem GExpr.power_sorted_of_sorted [PartialOrder α] [Zero' α] {c : α} {p r : GExpr α} :
  (c ×X^(p)+ r).sorted → p.sorted := by
  intro h
  cases h
  case mononomial h _ => exact h
  case polynomial c₀ c_ne_zero p₀ r remainder_sorted p_sorted p₀_lt_p _ => exact p_sorted

theorem GExpr.remainder_sorted_of_sorted [PartialOrder α] [Zero' α] {c : α} {p r : GExpr α} :
  (c ×X^(p)+ r).sorted → r.sorted := by
  intros h
  cases h
  case mononomial _ => exact GExpr.sorted.zero
  case polynomial c₀ p₀ r remainder_sorted c_ne_zero p_sorted p₀_lt_p => exact remainder_sorted

theorem GExpr.ne_zero'_of_sorted [PartialOrder α] [Zero' α] {c : α} {p r} : (c ×X^(p)+ r).sorted -> ne_zero' c := by
  intros h
  cases h
  case mononomial h => exact h
  case polynomial h => exact h

abbrev SGExpr (α) [PartialOrder α] [Zero' α] : Type := {expr : GExpr α // expr.sorted}

def SGExpr.destruct [PartialOrder α] [Zero' α] : SGExpr α → Option (α × SGExpr α × SGExpr α)
  | ⟨0, _⟩ => none
  | ⟨c ×X^(p )+ r, h⟩ =>
    have p' := ⟨p, GExpr.power_sorted_of_sorted h⟩
    have r' := ⟨r, GExpr.remainder_sorted_of_sorted h⟩
    some <| (c, p', r')

open Option
open Ordering

theorem GExpr.cmp_spec [LinearOrder α] : ∀ (a b : GExpr α), (a.cmp b).Compares a b
  | 0, 0 => rfl
  | 0, (_ ×X^(_)+ _) => by
    simp [GExpr.cmp]
    apply zero_lt_term
  | (_ ×X^(_)+ _), 0 => by
    simp [GExpr.cmp]
    apply zero_lt_term
  | (c₀ ×X^(p₀)+ r₀), (c₁ ×X^(p₁)+ r₁) => by
    simp [GExpr.cmp]
    match p₀.cmp p₁, p₀.cmp_spec p₁ with
    | lt, h =>
      simp only [compares_lt, gt_iff_lt]
      apply lt_of_power_lt
      exact h
    | gt, h =>
      simp only [compares_gt, gt_iff_lt]
      apply lt_of_power_lt
      exact h
    | eq, h =>
      simp at *
      cases h
      have spec : (compare c₀ c₁).Compares c₀ c₁ := by
        rw [← compare_iff]
      match compare c₀ c₁, spec with
      | lt, h =>
        simp at *
        apply GExpr.lex_lt.lt_of_coeff_lt
        exact h
      | gt, h =>
        simp at *
        apply GExpr.lex_lt.lt_of_coeff_lt
        exact h
      | eq, h =>
        simp at *
        cases h
        have : (r₀.cmp r₁).Compares r₀ r₁ := GExpr.cmp_spec r₀ r₁
        match r₀.cmp r₁, this with
        | eq, h =>
          simp
          apply h
        | lt, h =>
          simp at *
          apply GExpr.lex_lt.lt_of_remainder_lt
          exact h
        | gt, h =>
          simp at *
          apply GExpr.lex_lt.lt_of_remainder_lt
          exact h

instance [LinearOrder α] : LinearOrder (GExpr α) := by
  apply linearOrderOfCompares GExpr.cmp GExpr.cmp_spec

def GExpr.printWithBase [LinearOrder α] [ToString α] [One α] (base : String) : GExpr α → String
  | 0 => "0"
  | c ×X^(p)+ r =>
    let thisTerm :=
      let c' := if c ≠ 1 then toString c ++ "×" else ""
      match p.printWithBase base with
      | "0" => toString c
      | "1" => c' ++ base
      | s => c' ++ base ++ "^" ++
        if ' ' ∈ s.data ∨ '^' ∈ s.data
        then "(" ++ s ++ ")"
        else s
    let r' := if r = 0 then ""
      else " + " ++ r.printWithBase base
    thisTerm ++ r'

def GExpr.toNat : GExpr (Fin n) → ℕ
  | 0 => 0
  | c ×X^( p)+ r =>
    (c.val * n ^ p.toNat) + r.toNat

namespace GoldstienNumber

variable {base : ℕ}

def digit (n) (h : 2 ≤ base ∧ n ≠ 0) : Fin base :=
  ⟨(n / base ^ Nat.log base n), by
    rw [Nat.div_lt_iff_lt_mul, ← Nat.pow_succ', Nat.lt_pow_iff_log_lt (hy := h.2)]
    apply Nat.lt_succ_self
    linarith
    apply Nat.pow_pos
    apply lt_of_lt_of_le (b := 2) (by simp) h.1
  ⟩

@[simp]
theorem digit_def {n} (h : 2 ≤ base ∧ n ≠ 0) :
  ↑(digit n h) = n / base ^ Nat.log base n := by rfl

theorem digit_ne_zero' {n} (h : 2 ≤ base ∧ n ≠ 0) :
  ne_zero' (digit n h) := by
  cases base
  case zero => cases h.1
  case succ base =>
    exists 0
    simp [Fin.lt_iff_val_lt_val]
    apply Nat.pow_log_le_self _ h.2

theorem power_lt {n} (h₂ : n ≠ 0) : Nat.log base n < n := Nat.log_lt_self _ h₂

theorem remainder_lt (h : 2 ≤ base ∧ n ≠ 0) : n % (base ^ Nat.log base n) < n := by
  apply lt_of_lt_of_le
  · apply Nat.mod_lt
    apply pow_pos
    apply lt_of_lt_of_le zero_lt_two h.1
  · apply Nat.pow_log_le_self _ h.2

variable (base : ℕ)

-- render a number into a hereditary base notation
def inBase (input : ℕ) : GExpr (Fin base) :=
  if h : 2 ≤ base ∧ input ≠ 0 then
      let power := Nat.log base input
      let placeValue := base ^ power
      let remainder := input % placeValue
      have : power < input := by apply power_lt h.2
      have : remainder < input := remainder_lt h
      (digit input h) ×X^(inBase power)+ inBase remainder
  else 0
  termination_by input

def test := (inBase 3 100).printWithBase (toString 3)

#eval test

@[simp]
theorem zero : inBase base 0 = 0 := by
  simp [inBase]

theorem spec (base_non_trivial : 2 ≤ base) (input : ℕ) : (inBase (base := base) input).toNat = input := by
  induction input using Nat.strongRec
  case ind n n_ih =>
  rw [inBase]
  split_ifs
  case neg h =>
    simp at h
    rw [h, GExpr.toNat.eq_def]
    assumption
  case pos non_trivial =>
    have ⟨_, n_ne_zero⟩ := non_trivial
    simp only [GExpr.toNat]
    rw [n_ih _, n_ih _, digit_def]
    · apply Nat.div_add_mod'
    · apply lt_of_lt_of_le
      · apply Nat.mod_lt
        apply pow_pos
        apply lt_of_lt_of_le zero_lt_two base_non_trivial
      · apply Nat.pow_log_le_self _ n_ne_zero
    · exact power_lt n_ne_zero

theorem compares_refl (f : α → α → Ordering) [Preorder α] (spec : ∀ x y, (f x y).Compares x y)
  (x : α) :
  f x x = Ordering.eq := by
  have this : (f x x).Compares x x := spec x x
  rw [Compares.eq_def] at this
  revert this
  cases f x x
  case lt => simp
  case gt => simp
  case eq => simp

theorem cmp_refl [LinearOrder α] (x : GExpr α) : GExpr.cmp x x = eq := by
  rw [compares_refl GExpr.cmp GExpr.cmp_spec]

theorem Fin.compare_val (x y : Fin n) : compare x y = compare x.val y.val := rfl

theorem inBase_mono_aux {base} (base_non_trivial : 2 ≤ base) : ∀ {x y},
   x < y -> (inBase base x).cmp (inBase base y) = lt := by
   intros x y
   revert x
   have base_pos : 0 < base := by
    apply lt_of_lt_of_le zero_lt_two base_non_trivial
   induction y using Nat.strongRec
   case ind y y_ih =>
    intros x x_lt_y
    cases x
    case zero =>
      rw [inBase, inBase]
      have x_h : ¬ (2 ≤ base ∧ 0 ≠ 0) := by simp
      have y_h : 2 ≤ base ∧ y ≠ 0 :=
        And.intro base_non_trivial $ Nat.pos_iff_ne_zero.mp x_lt_y
      simp [dif_neg x_h, dif_pos y_h, GExpr.cmp]
    case succ x =>
      rw [inBase, inBase]
      have x_add_one_ne_zero : x + 1 ≠ 0 := by simp
      have y_ne_zero : y ≠ 0 := by
        rw [← Nat.pos_iff_ne_zero]
        trans x+1
        simp
        exact x_lt_y
      rw [dif_pos ⟨base_non_trivial, x_add_one_ne_zero⟩, dif_pos ⟨base_non_trivial, y_ne_zero⟩]
      simp [GExpr.cmp]
      have ⟨power₀, power₀_def⟩ : {power₀ // power₀ = Nat.log base (x + 1)} := ⟨_, rfl⟩
      have ⟨power₁, power₁_def⟩ : {power₁ // power₁ = Nat.log base y} := ⟨_, rfl⟩
      have : power₀ < power₁ ∨ power₀ = power₁ := by
        rw [← le_iff_lt_or_eq, power₁_def, power₀_def]
        apply Nat.log_mono_right
        apply le_of_lt x_lt_y
      cases this
      case inl this =>
        rw [← power₀_def, ← power₁_def, y_ih]
        · rw [power₁_def]
          apply Nat.log_lt_self
          exact y_ne_zero
        · exact this
      case inr this =>
        rw [← power₀_def, ← power₁_def, this]
        simp [cmp_refl]
        simp [digit, Fin.compare_val]
        have h₀ : 2 ≤ base ∧ x+1≠0 := ⟨base_non_trivial, by simp⟩
        have h₁ : 2 ≤ base ∧ y≠0 := ⟨base_non_trivial, y_ne_zero⟩
        have c₀_le_c₁ : (x+1)/base ^ power₁ ≤ y/base ^ power₁ := Nat.div_le_div_right (le_of_lt x_lt_y)
        rw [← power₀_def, ← power₁_def, this]
        rw [le_iff_eq_or_lt] at c₀_le_c₁
        cases c₀_le_c₁
        case inr c₀_lt_c₁ =>
          rw [compare_lt_iff_lt.mpr c₀_lt_c₁]
        case inl c₀_eq_c₁ =>
          rw [compare_eq_iff_eq.mpr c₀_eq_c₁]
          simp
          apply y_ih
          · rw [lt_iff_le_and_ne]
            apply And.intro (Nat.mod_le _ _)
            simp
            rw [Nat.mod_eq_iff_lt]
            suffices : base ^ power₁ ≤ y
            · rw [not_lt_iff_eq_or_lt]
              rw [power₁_def] at *
              rw [le_iff_eq_or_lt] at this
              cases this
              case a.inl h =>
                left
                rw [h]
              case a.inr h =>
                right
                exact h
            rw [power₁_def] at *
            apply Nat.pow_log_le_self
            apply y_ne_zero
            rw [← Nat.pos_iff_ne_zero]
            apply Nat.pow_pos base_pos
          · clear power₀ power₀_def this
            set w := x+1
            set pv := base ^ power₁
            have : pv * (w / pv) + (w % pv) < pv * (y/pv) + (y % pv) := by
              rw [Nat.div_add_mod, Nat.div_add_mod]
              exact x_lt_y
            simp [c₀_eq_c₁] at this
            exact this

theorem inBase_mono (base) : ∀ x y,
  2 ≤ base → x < y -> (inBase base x) < (inBase base y) := by
  intros x y non_trivial_base x_lt_y
  rw [← compares_lt]
  rw [← inBase_mono_aux non_trivial_base x_lt_y]
  apply GExpr.cmp_spec

theorem inBase_sorted {base input} : (inBase base input).sorted := by
  induction input using Nat.strongRecOn
  case ind n n_ih =>
    rw [inBase]
    simp
    split_ifs
    case neg h => constructor
    case pos h =>
      let ⟨base_non_trivial, n_ne_zero⟩ := h
      have base_pos : 0 < base := by
        apply lt_of_lt_of_le zero_lt_two base_non_trivial
      dsimp only [ne_eq]
      set toGExpr := inBase base
      have p_sorted : (toGExpr (Nat.log base n)).sorted := by
        by_cases n = 0
        case pos n_eq_zero =>
          cases n_eq_zero
          rw [Nat.log_zero_right]
          simp [toGExpr, inBase]
          exact GExpr.sorted.zero
        case neg n_ne_zero =>
          apply n_ih
          apply Nat.log_lt_self
          exact n_ne_zero

      by_cases Nat.log base n = 0
      case pos nat_log_base_n_eq_zero =>
        simp [nat_log_base_n_eq_zero, Nat.mod_one]
        simp [toGExpr]
        apply GExpr.sorted.mononomial
        apply digit_ne_zero'
        apply GExpr.sorted.zero
      case neg nat_log_n_pos =>
        set nat_r := (n % base ^ Nat.log base n)
        have log_r_lt_log_n : Nat.log base nat_r < Nat.log base n := by
          apply lt_of_le_of_ne
          · apply Nat.log_monotone
            apply Nat.mod_le
          · intro log_eq
            rw [Nat.log_eq_iff] at log_eq
            · let ⟨power_lt_nat_r, nat_r_lt_next_power⟩ := log_eq
              clear log_eq
              have : nat_r < base ^ Nat.log base n := by
                apply Nat.mod_lt
                apply Nat.pow_pos
                simp at h
                exact base_pos
              apply lt_irrefl nat_r
              apply lt_of_lt_of_le this
              exact power_lt_nat_r
            · left
              assumption
        by_cases 0 < nat_r
        case neg h =>
          have : nat_r = 0 := by
            revert nat_r
            simp
          simp [this, toGExpr]
          constructor
          apply digit_ne_zero'
          exact p_sorted
        case pos nat_r_pos =>
          let ⟨c₀, p₀, r₀, h⟩ : ∃ c₀ p₀ r₀, toGExpr nat_r = GExpr.term c₀ p₀ r₀ := by
            simp [toGExpr]
            rw [inBase, dif_pos]
            · simp
            simp at *
            apply And.intro h.left
            intros not_zero
            simp [not_zero] at *
          rw [h]
          apply GExpr.sorted.polynomial
          apply digit_ne_zero'
          exact p_sorted
          simp [toGExpr] at h
          rw [inBase, dif_pos] at h
          simp at h
          rw [← h.right.left]
          apply inBase_mono base _ _ base_non_trivial log_r_lt_log_n
          apply And.intro base_non_trivial (Nat.pos_iff_ne_zero.mp nat_r_pos)
          rw [←h]
          · apply n_ih
            apply remainder_lt
            · constructor
              · assumption
              · assumption

end GoldstienNumber

open Ordinal

def GExpr.toOrdinal {n} : GExpr (Fin n) → Ordinal
  | 0 => 0
  | c ×X^( p)+ r =>
    (c * ω ^ p.toOrdinal) + r.toOrdinal







    else r.sort

mutual

def GExpr.goldstein (start : ℕ) (n : ℕ) : GExpr (Fin (n+3)) :=
  (GoldstienNumber.inBase (n+2) (start.goldstein n)).map Fin.castSucc

def Nat.goldstein (start : ℕ) : ℕ → ℕ
  | 0 => start
  | (n+1) =>
    (GExpr.goldstein start n).toNat - 1

def goldstein_list (start : ℕ) (length : ℕ) : List ℕ :=
  (List.range length).map start.goldstein

def on_omega : GExpr (Fin n) → GExpr ℕ := map Fin.val

end

#eval goldstein_list 4 4

theorem goldstein_terminates_aux : ∀ start : ℕ, ∃ n, GExpr.goldstein start n = 0 := by
  intros start

theorem goldstein_terminates : ∀ start : ℕ, ∃ n, start.goldstein (n+1) = 0 := by
  intros start
  simp [Nat.goldstein]
