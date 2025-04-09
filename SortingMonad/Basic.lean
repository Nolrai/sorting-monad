import Mathlib

open unitInterval

namespace SimpleGraph

variable {P} (g : SimpleGraph P)

def DEdge : Type := {p : P × P // g.Adj (p.fst) (p.snd)}

def DEdge.get (e : g.DEdge) : Fin 2 → P
  | 0 => e.val.fst
  | 1 => e.val.snd

instance : FunLike (DEdge g) (Fin 2) P where
  coe s := s.get
  coe_injective' := by
    intros x y h
    let ⟨(x₀, x₁), x_prop⟩ := x
    let ⟨(y₀, y₁), y_prop⟩ := y
    simp [DEdge] at *
    split_ands
    · have : DEdge.get g ⟨(x₀, x₁), x_prop⟩ 0 = x₀ := by simp [DEdge.get]
      rw [← this, h, DEdge.get]
    · have : DEdge.get g ⟨(x₀, x₁), x_prop⟩ 1 = x₁ := by simp [DEdge.get]
      rw [← this, h, DEdge.get]

theorem DEdge.funLike_eq (d : g.DEdge) (b : Fin 2) : (d b) = DEdge.get g d b := rfl

theorem DEdge.get_0 (d : g.DEdge) : d 0 = d.val.fst := rfl

theorem DEdge.get_1 (d : g.DEdge) : d 1 = d.val.snd := rfl

def DEdge.symm : g.DEdge → g.DEdge
  | ⟨(a, b), h⟩ => ⟨(b, a), h.symm⟩

@[simp]
theorem DEdge.get_symm_0 (d : g.DEdge) :
  (d.symm) 0 = d 1 := by
  let ⟨(i, j), adj⟩ := d
  simp [DEdge.symm, DEdge.get_0, DEdge.get_1]

@[simp]
theorem DEdge.get_symm_1 (d : g.DEdge) :
  (d.symm) 1 = d 0 := by
  let ⟨(i, j), adj⟩ := d
  simp [DEdge.symm, DEdge.get_0, DEdge.get_1]

@[simp]
theorem DEdge.get_symm (d : g.DEdge) (b : Fin 2) :
  (d.symm) b = d (1 - b) := by
  let ⟨(i, j), adj⟩ := d
  match b with
  | 0 =>
    rw [DEdge.get_symm_0]
    simp
  | 1 =>
    rw [DEdge.get_symm_1]
    simp

structure Drawing {P} (g : SimpleGraph P) where
  (draw : g.DEdge → C(I, ℝ × ℝ))
  (symm : ∀ h (t : I), draw h t = draw h.symm (σ t))
  (consecutive : ∀ e₀ e₁ : g.DEdge, e₀ 1 = e₁ 0 → draw e₀ 1 = draw e₁ 0)

variable {g}

def DEdge.symm_r (h₀ h₁ : g.DEdge) : Prop :=
  h₀ = h₁ ∨ h₀.symm = h₁

def DEdge.symm_r_symm {h₀ h₁ : g.DEdge} : h₀.symm_r h₁ → h₁.symm_r h₀
  | Or.inl is_eq => Or.inl is_eq.symm
  | Or.inr is_eq =>
    let ⟨⟨h₀₀, h₀₁⟩, h₀_prop⟩ := h₀
    let ⟨⟨h₁₀, h₁₁⟩, h₁_prop⟩ := h₁
    Or.inr <| by
      rw [Subtype.ext_iff] at *
      simp [symm] at *
      tauto

def DEdge.symm_r_trans {h₀ h₁ h₂ : g.DEdge} : h₀.symm_r h₁ -> h₁.symm_r h₂ -> h₀.symm_r h₂
  | Or.inl is_eq, h => by rw [is_eq]; exact h
  | h, Or.inl is_eq => by rw [← is_eq]; exact h
  | Or.inr p₁, Or.inr p₂ => by
    left
    let ⟨⟨h₀₀, h₀₁⟩, h₀_prop⟩ := h₀
    let ⟨⟨h₁₀, h₁₁⟩, h₁_prop⟩ := h₁
    let ⟨⟨h₂₀, h₂₁⟩, h₂_prop⟩ := h₂
    rw [Subtype.ext_iff] at *
    simp [DEdge.symm] at *
    simp [p₁.1, p₂.2, p₁.2, p₂.1]

def DEdge.irrefl : ∀ d : g.DEdge, ¬ d 0 = d 1
  | ⟨(i, j), h⟩ => by
    intros i_eq_j
    cases i_eq_j
    simp at *

def SEdge : Type := Quotient {
  r (x : g.DEdge) y := x = y ∨ x.symm = y
  iseqv := ⟨by simp, DEdge.symm_r_symm, DEdge.symm_r_trans⟩
}

abbrev SEdge.mk (a b : P) (h : g.Adj a b) : g.SEdge := Quotient.mk _ ⟨⟨a, b⟩, h⟩

def SEdge.ind [LinearOrder P] (motive : SEdge → Prop)
  (H : ∀ (d : g.DEdge), d 0 < d 1 → motive (⟦d⟧) )
  (s) : motive s := by
    induction s using Quotient.inductionOn
    case h d =>
      by_cases lt_hyp : d 0 < d 1
      · apply H d lt_hyp
      · have : (⟦d⟧ : g.SEdge) = ⟦d.symm⟧ := by simp
        rw [this]; clear this
        apply H
        rw [not_lt_iff_eq_or_lt, or_iff_right (DEdge.irrefl _)] at lt_hyp
        let ⟨(i, j), adj⟩ := d; clear d
        revert lt_hyp
        simp

def NonCrossing (d : Drawing g) : Prop :=
  ∀ h₁ h₂ t₁ t₂,
    0 < t₁ → t₁ < 1 → 0 < t₂ → t₂ < 1 →
    h₁ ≠ h₂.symm →
    d.draw h₁ t₁ = d.draw h₂ t₂ →
    h₂ = h₂ ∧ t₁ = t₂

def InjectiveOnPoints (d : Drawing g) : Prop :=
  ∀ h₁ h₂, d.draw h₁ 0 = d.draw h₂ 0 → h₁ 0 = h₂ 0

abbrev Planar (d : Drawing g) := NonCrossing d ∧ InjectiveOnPoints d

abbrev anti_image (d : Drawing g) := {s : ℝ × ℝ // ¬ ∃ h t, d.draw h t = s}

abbrev faces (d : Drawing g) := ConnectedComponents (anti_image d)

def NumVertexes (_ : Drawing g) : Cardinal := Cardinal.mk P
def NumFaces (d : Drawing g) : Cardinal := (Cardinal.mk (faces d))
def NumEdges (_ : Drawing g) : Cardinal := Cardinal.mk g.SEdge

noncomputable
def EularCharacteristic (d : Drawing g) : Option ℤ := do
  match (NumVertexes d).toENat, (NumEdges d).toENat, (NumFaces d).toENat with
  | some V, some E, some F => pure (V - (E : ℤ) + F)
  | _, _, _ => none

instance {n} : OfNat (Option ℤ) n where
  ofNat := some (OfNat.ofNat n)

notation "𝔼" => EularCharacteristic

end SimpleGraph

def ngon : ∀ n, SimpleGraph (Fin n)
  | n+2 => {
    Adj i j := i + 1 = j ∨ j + 1 = i
  }
  | 0 => {
    Adj _ _ := True
    loopless := λ x => x.elim0
    }
  | 1 => {Adj _ _ := False}

open SimpleGraph

namespace ThreeSides

def toFun_aux : (ngon 3).DEdge → Fin 3
  | ⟨⟨0, i⟩, _⟩ => i
  | ⟨⟨i, 0⟩, _⟩ => i
  | _ => 0

def toFun : (ngon 3).SEdge → Fin 3 :=
  Quotient.lift toFun_aux
  <| by
    intros h₀ h₁ hyp
    cases hyp
    case inl hyp => rw [hyp]
    case inr hyp =>
      let ⟨⟨i, j⟩, adj⟩ := h₀
      rw [← hyp]; clear h₁ hyp h₀
      simp [DEdge.symm, toFun_aux]
      match i, j with
      | 0, 0 => rfl
      | 0, 1 => rfl
      | 0, 2 => rfl
      | 1, 0 => rfl
      | 1, 1 => rfl
      | 1, 2 => rfl
      | 2, 0 => rfl
      | 2, 1 => rfl
      | 2, 2 => rfl

def invFun : Fin 3 → (ngon 3).SEdge
  | 0 => by
    apply SEdge.mk 1 2
    simp [ngon]
  | 1 => by
    apply SEdge.mk 0 1
    simp [ngon]
  | 2 => by
    apply SEdge.mk 0 2
    simp [ngon]

def equivalence : (ngon 3).SEdge ≃ Fin 3 where
  toFun := toFun
  invFun := invFun
  left_inv := by
    intros x
    induction x using SEdge.ind
    case H d d_ord
    let ⟨(d₀, d₁), adj⟩ := d
    simp [DEdge.get_0, DEdge.get_1] at d_ord
    match d₁ with
    | 0 => cases d_ord
    | 1 =>
      simp at d_ord; simp [d_ord] at *
      simp [toFun, toFun_aux, invFun, SEdge.mk]
    | 2 =>
      match d₀ with
      | 0 => simp [toFun, toFun_aux, invFun, SEdge.mk]
      | 1 => simp [toFun, toFun_aux, invFun, SEdge.mk]
  right_inv := by
    intros x
    match x with
    | 0 => simp [toFun, invFun, toFun_aux]
    | 1 => simp [toFun, invFun, toFun_aux]
    | 2 => simp [toFun, invFun, toFun_aux]

theorem main (d : Drawing (ngon 3)) : NumEdges d = 3 := by
  simp [NumEdges]
  apply Cardinal.mk_eq_nat_iff.mpr
  exact ⟨equivalence⟩

end ThreeSides

abbrev TriangleHaveThreeSides := ThreeSides.main

open Real

noncomputable
def inflated_ngon_aux₀ (n a b : ℕ): C(I , ℝ) := {
  toFun := λ i => 2 * π / (n - 1) * (a * σ i + b * i)
  continuous_toFun := by continuity
}

noncomputable
def inflated_ngon_aux₁ : C(ℝ , ℝ × ℝ) := {
  toFun := Complex.equivRealProd ∘ Complex.exp ∘ (Complex.I * ·)
  continuous_toFun := by continuity
}

open Complex

infix:50 "⊚" => ContinuousMap.comp

noncomputable
def inflated_ngon_draw' {n} (e : DEdge (ngon n)) :=
  ContinuousMap.comp (β := ℝ) inflated_ngon_aux₁ (inflated_ngon_aux₀ n (e 0) (e 1))

noncomputable
def inflated_ngon (n : ℕ) : Drawing (ngon n) where
  draw := inflated_ngon_draw'
  symm e t := by
    simp [inflated_ngon_draw']
    congr 1
    simp [inflated_ngon_aux₀]
    ring
  consecutive e₀ e₁ end_eq_start := by
    simp [inflated_ngon_draw']
    congr 1
    simp [inflated_ngon_aux₀, end_eq_start]

theorem inflated_ngon.draw_def (n e) :
  (inflated_ngon n).draw e =
    inflated_ngon_aux₁ ∘ (inflated_ngon_aux₀ n (e 0) (e 1)) := by
    simp [inflated_ngon, inflated_ngon_draw']

namespace TwoFaces

theorem inflated_ngon_image {n' : ℕ} (s : ℝ × ℝ) :
  (∃ e i, (inflated_ngon (n := n' + 2)).draw e i = s) ↔ norm (equivRealProd.symm s) = 1 where
  mp h := by
    let n := n' + 2
    let ⟨e, i, h⟩ := h
    rw [← h]
    simp [inflated_ngon.draw_def, inflated_ngon_aux₁, Complex.norm_eq_abs]
    set t : Real := (inflated_ngon_aux₀ n ↑(e 0) ↑(e 1)) i
    rw [Complex.abs_exp]
    simp [Complex.I_mul]
  mpr h := by
    set n := n' + 2
    let angle : Real := arg (equivRealProd.symm s)
    let t : Real := angle * n / (2 * π)
    let e₀ : Fin n := by
      exists (⌊t⌋ + n).natAbs % n
      apply Nat.mod_lt _
      simp [n]
    let i : I := by
      exists t - ⌊t⌋
      simp
      apply le_of_lt
      apply Int.fract_lt_one
    let e : (ngon n).DEdge := by
      exists ⟨e₀, e₀ + 1⟩
      simp [ngon, n]
    exists e
    exists i
    simp [inflated_ngon.draw_def, DEdge.get_0, DEdge.get_1, e]
    simp [inflated_ngon_aux₀, inflated_ngon_aux₁]
    have : ∀ (z : ℂ) (p : ℝ × ℝ), (z.re, z.im) = p ↔ z = equivRealProd.symm p := by
      intros z p
      let ⟨x', y'⟩ := z
      let (x, y) := p
      simp [equivRealProd]
    rw [this]

theorem main (d : Drawing (ngon 3)) : Planar d -> NumFaces d = 2 := by
  simp [NumFaces, faces]
  intros noncrossing inj
  rw [Cardinal.mk_eq_two_iff]
  have x : ConnectedComponents (anti_image d) := by
    rw [ConnectedComponents]
    apply Quotient.mk
    exists (1, 1)


end TwoFaces
