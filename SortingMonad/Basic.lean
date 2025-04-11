import Mathlib

instance : NatPow Type where
  pow α n := Fin n → α

instance {α β} [CoeOut α β] {n} : CoeOut (α ^ n) (β ^ n) where
  coe v := CoeOut.coe ∘ v

section defs
variable {numParticles dim : ℕ}

-- the type of a function that computes one particle's potential energy
def 𝕌Type : Type :=
  (i : Fin numParticles) →
  (v : (ℝ ^ dim) ^ numParticles) →
  (∀ j, v i j = 0) →
  ℝ


def Fin.normSq {n} (p : ℝ ^ n) := ∑ i, p i ^ 2

theorem normSq_def {n : ℕ} (p : ℝ ^ n) : Fin.normSq p = (∑ i, (p i ^ 2)) := rfl

notation "ℝ+" => {x : ℝ // 0 < x}

noncomputable
def 𝕂 (mass : ℝ+ ^ numParticles)
  (q : (ℝ ^ dim) ^ numParticles) :=
  (∑ i, (1/2) * (mass i).val * Fin.normSq (q i))

noncomputable
def 𝕃 (𝕌 : 𝕌Type (dim := dim) (numParticles := numParticles))
  (masses : ℝ+ ^ numParticles) (p q : (ℝ ^ dim) ^ numParticles) :=
  𝕂 masses q - ∑ i, 𝕌 i (λ i' j => p i' j - p i j) (by simp only [sub_self, implies_true])

def SymType :=
  (ℝ ^ dim) ^ numParticles →
  (ℝ ^ dim) ^ numParticles →
  ((ℝ ^ dim) ^ numParticles) × ((ℝ ^ dim) ^ numParticles)

def IsSymOf
  (𝕌 : 𝕌Type (dim := dim) (numParticles := numParticles))
  (σ : SymType (dim := dim) (numParticles := numParticles)) : Type :=
  Σ' (r : Real), ∀ masses p q, 𝕃 𝕌 masses p q + r = 𝕃 𝕌 masses ((σ p q).1) ((σ p q).2)

def translation (a : ℝ ^ dim) : SymType (dim := dim) (numParticles := numParticles) :=
  λ p q => ((λ i j => p i j + a j), q)

def translation_sym (𝕌 : 𝕌Type (dim := dim) (numParticles := numParticles)) (a : ℝ ^ dim) :
  IsSymOf (dim := dim) 𝕌 (translation a) := PSigma.mk 0 <| by
    intros masses p q
    simp [𝕃, 𝕂, translation]
    congr
    funext i
    congr
    funext i' j
    ring

def boost (a : ℝ ^ dim) : SymType (dim := dim) (numParticles := numParticles) :=
  λ p q => (p, (λ i j => q i j + a j))

def boost_sym (𝕌 : 𝕌Type (dim := dim) (numParticles := numParticles)) (a : ℝ ^ dim) :
  IsSymOf (dim := dim) 𝕌 (translation a) := PSigma.mk 0 <| by
    intros masses p q
    simp [𝕃, 𝕂, translation]
    congr
    funext i
    congr
    funext i' j
    ring

noncomputable
def radialForces (f : Fin numParticles → Fin dim → ℝ+ → ℝ) : 𝕌Type (dim := dim) (numParticles := numParticles)
  | i, v, _hyp => ∑ i', if h : 0 < Fin.normSq (v i) then f i i' ⟨Fin.normSq (v i), h⟩ else 0

instance ℝ2Toℂ : ℝ ^ 2 ≃ ℂ where
  toFun (v : ℝ ^ 2) : ℂ := {re := v 0, im := v 1}
  invFun (z : ℂ) i := if i = 0 then z.re else z.im
  left_inv := by
    intros v
    funext ix
    match ix with
    | 0 => simp
    | 1 => simp
  right_inv := by
    intros z
    simp

def amplitwist (z : ℂ) : ℝ ^ 2 → ℝ ^ 2 := ℝ2Toℂ.symm ∘ (z * ·) ∘ ℝ2Toℂ

noncomputable
def rotate (θ : ℝ) : ℝ ^ 2 → ℝ ^ 2 := amplitwist (Complex.exp (θ * Complex.I))

def dilate (τ : ℝ) : ℝ ^ 2 → ℝ ^ 2 := amplitwist τ

theorem norm_ℝ2Toℂ : ∀ p, (ℝ2Toℂ p).normSq = Fin.normSq p := by
  intros p
  simp only [ℝ2Toℂ, Fin.isValue, Equiv.coe_fn_mk, Complex.normSq_mk, normSq_def p, pow_two,
    Fin.sum_univ_two]

theorem norm_amplitwist (z : ℂ) (p : ℝ ^ 2) : Fin.normSq (amplitwist z p) = z.normSq * Fin.normSq p := by
  let ⟨x, y⟩ := z
  simp [amplitwist, ℝ2Toℂ, Complex.abs, normSq_def]
  ring

@[simp]
theorem Complex.normSq_of_exp_of_imaginary (θ : ℝ) : Complex.normSq (Complex.exp (θ * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_abs]
    rw [← one_pow 2]
    congr
    rw [Complex.abs_eq_one_iff]
    exists θ

def simple_sym (σ : ℝ ^ dim → ℝ ^ dim) : SymType (dim := dim) (numParticles := numParticles) :=
  λ p q => (σ ∘ p, σ ∘ q)

def rotate_sym_aux (θ m) (p : (ℝ ^ 2) ^ numParticles) : 𝕂 m (rotate θ ∘ p) = 𝕂 m p := by
  rw [𝕂, 𝕂]
  congr
  funext i
  congr 1
  simp_rw [rotate, Function.comp, norm_amplitwist]
  simp

def rotate_sym (f θ) :
  IsSymOf (radialForces (dim := 2) (numParticles := numParticles) f) (simple_sym (rotate θ)) :=
  PSigma.mk 0 <| by
  intros masses p q
  simp [𝕃, simple_sym, ℝ2Toℂ]
  congr 1
  rw [rotate_sym_aux]
  congr
  funext i
  simp [radialForces]
