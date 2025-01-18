import Mathlib

inductive GExpr (α : Type) where
  | zero : GExpr α
  | term (coeff : α) (power : GExpr α) (remainder : GExpr α)

notation c "×X^(" p ")+ " r => GExpr.term c p r

def GExpr.sizeOf {α} : GExpr α → ℕ
  | zero => 0
  | _ ×X^( p )+ r => 1 + p.sizeOf + r.sizeOf

instance {α} : SizeOf (GExpr α) where
  sizeOf := GExpr.sizeOf

variable {α β γ : Type} {n : ℕ}

instance : Zero (GExpr α) where
  zero := GExpr.zero

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

instance [PartialOrder α] : PartialOrder (GExpr α) := partialOrderOfSO (GExpr.lex_lt)

inductive GExpr.sorted [PartialOrder α] : GExpr α → Prop where
  | zero : (0 : GExpr α).sorted
  | mononomial c p : p.sorted → (c ×X^(p)+ 0).sorted
  | polynomial c₁ p₁ c₀ p₀ r :
    p₀.sorted → p₁.sorted → p₀ < p₁
    → (c₀ ×X^(p₁)+ r).sorted
    → (c₁ ×X^(p₁)+ (c₀ ×X^(p₁)+ r)).sorted

theorem GExpr.power_sorted_of_sorted [PartialOrder α] {c : α} {p r : GExpr α} :
  (c ×X^(p)+ r).sorted → p.sorted := by
  intro h
  cases h
  case mononomial h => exact h
  case polynomial h _ _ => exact h

theorem GExpr.remainder_sorted_of_sorted [PartialOrder α] {c : α} {p r : GExpr α} :
  (c ×X^(p)+ r).sorted → r.sorted := by
  intros h
  cases h
  case mononomial _ => constructor
  case polynomial h => exact h

def SGExpr (α) [PartialOrder α] : Type := {expr : GExpr α // expr.sorted}

def SGExpr.destruct [PartialOrder α] : SGExpr α → Option (α × SGExpr α × SGExpr α)
  | ⟨0, _⟩ => none
  | ⟨c ×X^(p )+ r, h⟩ =>
    have p' := ⟨p, GExpr.power_sorted_of_sorted h⟩
    have r' := ⟨r, GExpr.remainder_sorted_of_sorted h⟩
    some <| (c, p', r')

open Option
open Ordering

def GExpr.cmp [LinearOrder α] : ∀ (_ _ : GExpr α), Ordering
  | 0, 0 => eq
  | 0, (_ ×X^(_)+ _) => lt
  | (_ ×X^(_)+ _), 0 => gt
  | (c₀ ×X^(p₀)+ r₀), (c₁ ×X^(p₁)+ r₁) =>
    match p₀.cmp p₁ with
      | lt => lt
      | gt => gt
      | eq =>
        match _root_.cmp c₀ c₁ with
        | lt => lt
        | gt => gt
        | eq => r₀.cmp r₁

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
      have : (_root_.cmp c₀ c₁).Compares c₀ c₁ := cmp_compares _ _
      match _root_.cmp c₀ c₁, this with
      | lt, c_h =>
        simp
        apply lt_of_coeff_lt
        exact c_h
      | gt, c_h =>
        simp
        apply lt_of_coeff_lt
        exact c_h
      | eq, c_h =>
        simp
        cases c_h
        match r₀.cmp r₁, r₀.cmp_spec r₁ with
        | lt, r_h =>
          simp
          apply lt_of_remainder_lt
          exact r_h
        | gt, r_h =>
          simp
          apply lt_of_remainder_lt
          exact r_h
        | eq, r_h =>
          cases r_h
          rfl





instance [LinearOrder α] : LinearOrder (GExpr α) := by
  apply linearOrderOfCompares GExpr.cmp
