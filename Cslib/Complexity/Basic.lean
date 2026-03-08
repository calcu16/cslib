module
/-!
This file defines a Complexity class which matches a lean function with its complexity
for a given computational model.
-/

@[expose] public section

namespace Complexity

/--
A computation model.

Consists of a Program type, a Data type (for input) and Result type (for output),
and an Cost type. The Data and Result types can be different, but it is more
convienent if they are the same.

The Data and Result types are allowed to have a more general notion of equals via Setoids.
For convience the Cost type should be
- CanonicallyOrdered (can't have negative costs)
- Lattice (given two costs we should be able to find a cost ≤ and ≥ both)
- Semiring, we should be able to add and multiple costs together

Given a Program and input Data we should be able to get a Result.
Since not all Programs halt, and given an arbitrary (Program, Data) pair
on a turing complete model its impossible to prove whether it halts this
is provided in Prop form instead instead with a functional requirement on the Prop.

Finally, given a proof that the program halts on data, what was the cost of that computation.

## TODO
Does it make more sense to have Cost be a semiring, or to HMul with ℕ
-/
def CostFunction (α : Type _) ( β: Type _): Type _ := α → β

structure Model where
  Program: Type _
  Data: Type _
  Result: Type _
  Cost: Type _
  [data_equiv : Setoid Data]
  [result_equiv : Setoid Result]
  has_result : Program → Data → Result → Prop
  has_result_isFunc {p : Program} {d₀ d₁ : Data} {r₀ r₁ : Result}:
    d₀ ≈ d₁ → has_result p d₀ r₀ → has_result p d₁ r₁ → r₀ ≈ r₁
  cost': (p : Program) → (d : Data) → (∃ r, has_result p d r) → Cost

instance (m : Model): Setoid m.Data := m.data_equiv
instance (m : Model): Setoid m.Result := m.result_equiv

/--
In order to prove stuff about lean functions, we need to be able
to encode lean types into the data type. The Encoding should be injective relative
to the Model's equivalence relation.

For conviencience we also require a (presumably computable) decode operator
to be able to go the other direction.
-/
class Encoding (α: Type _) (Data: Type _) [Setoid Data] where
  encode: α → Data
  encode_inj a b: encode a ≈ encode b → a = b

theorem Encoding.inj' [s: Setoid Data] [en: Encoding α Data] {a b: α}:
  Quotient.mk s (en.encode a) = Quotient.mk s (en.encode b) → a = b :=
    en.encode_inj _ _ ∘ Quotient.exact

theorem Encoding.inj_iff' [s: Setoid Data] [en: Encoding α Data] {a b: α}:
  Quotient.mk s (en.encode a) = Quotient.mk s (en.encode b) ↔ a = b :=
⟨ Encoding.inj', λ h ↦ h ▸ rfl ⟩

def encode [Setoid Data] [en: Encoding α Data]: α → Data := en.encode

class Coding (α: Type _) (Data: Type _) [Setoid Data] extends Encoding α Data where
  decode (d: Data): Option α
  decode_inv: ∀ (a: α), decode (Complexity.encode a) = some a

def decode (α: Type _) {Data: Type _} [Setoid Data] [en: Coding α Data] (d: Data): Option α := en.decode d

@[simp] theorem decode_inv [Setoid Data] [en: Coding α Data] (a: α):
  decode _ (encode a:Data) = some a := en.decode_inv _

@[simp] theorem decode_comp_encode [Setoid Data] [Coding α Data]:
    Complexity.decode α (Data := Data) ∘ Complexity.encode (α := α) (Data := Data) = some :=
  funext λ _ ↦ decode_inv _

noncomputable instance (α: Type _) (Data: Type _) [Setoid Data] [Encoding α Data]: Coding α Data where
  decode m :=
    open Classical in
    if h:∃ (a: α), encode a = m
    then some (Classical.choose h)
    else none
  decode_inv _ :=
    (dif_pos ⟨_, rfl⟩).trans
    (congrArg some (Encoding.inj'
      (congrArg _ (Classical.choose_spec (⟨_, rfl⟩:∃ _, _ = encode _)))))

instance [Setoid Data] [h: Coding α Data]: Encoding α Data := h.toEncoding

namespace Model
/-- Given a type, this program always halts on all encodings of the type -/
def totalProgram (m: Model) (p: m.Program) (α: Type _) [Encoding α m.Data]: Prop := ∀ (a: α), ∃ r, Model.has_result m p (encode a) r

/-- Given a total program, get the cost in a CostFunction form -/
def cost [Encoding α (Model.Data m)] (h: m.totalProgram p α): α → (Model.Cost m) := λ a ↦ m.cost' _ _ (h a)

end Model

/-- Proof that a lean function can be computed by a model -/
class Computable {α: Type _} {β: Type _} (m: Complexity.Model) [Complexity.Encoding α m.Data] [Complexity.Encoding β m.Result]
    (f: α → β) where
  program: m.Program
  has_result (a: α): m.has_result program (Complexity.encode a) (Complexity.encode (f a))

def Computable.cost
    {m: Complexity.Model} [Complexity.Encoding α m.Data] [Complexity.Encoding β m.Result]
    {f: α → β} [computable: Computable m f]: CostFunction α m.Cost :=
  m.cost λ _ ↦ ⟨_, computable.has_result _⟩

structure ComplexityClass (α : Type _) (β : Type _) [Add β] [LE β] where
  mem : CostFunction α β → Prop
  add_closed : mem f → mem g → mem (λ a ↦ f a + g a)
  le_closed : (∀ {a}, f a ≤ g a) → mem g → mem f

instance[Add β] [LE β] : Membership (CostFunction α β) (ComplexityClass α β) where
  mem := ComplexityClass.mem

end Complexity
