import InterpreterTest.Ast

abbrev ParseInput := List Char

inductive Error : Type where
  | ExpectedMinus : Error
  | ExpectedNat : Error
  deriving Repr, BEq, DecidableEq

/--
An optional value α, with additional errors emitted and where
the rest of the input.
-/
structure ParseResult (α : Type) : Type where
  value : Option α
  rest : ParseInput
  errors : List Error
  errorsNotNil : value = none → errors ≠ []
  deriving Repr, DecidableEq

instance [BEq α] : BEq (ParseResult α) :=
  ⟨fun a b => a.value == b.value && a.rest == b.rest && a.errors == b.errors⟩

@[simp] def Parser ret := ParseInput → ParseResult ret

namespace ParseResult

  -- Simple ways to construct

  def success (value : α) (rest : ParseInput) : ParseResult α :=
    { value := some value
      rest := rest
      errors := []
      errorsNotNil := by simp }

  def fromErrors (errors : List Error) (rest : ParseInput) (h : errors ≠ [])
  : ParseResult α :=
    { value := none
      rest := rest
      errors := errors
      errorsNotNil := fun _ => h }

  abbrev fromError (error : Error) (rest : ParseInput) : ParseResult α :=
    fromErrors [error] rest (by simp)

  -- Properties

  def isSuccess (self : ParseResult α) : Bool := self.value.isSome

  @[simp]
  theorem isSuccess_success {α value rest}
  : isSuccess (@success α value rest) = true := by
    unfold success isSuccess
    cases h : success value rest
    simp_all

  @[simp]
  theorem isSuccess_fromErrors {α errors rest h}
  : isSuccess (@fromErrors α errors rest h) = false := by
    unfold fromErrors isSuccess
    cases h : (fromErrors errors rest h : ParseResult α)
    simp_all

  @[simp]
  theorem isSuccess_isSome {h : isSuccess result}
  : result.value.isSome = true := h

  @[simp]
  theorem not_isSuccess_isSome {h : isSuccess result = false}
  : result.value.isSome = false := h

  @[simp]
  theorem isSome_isNone {a : Option α}
  : a.isSome = true ↔ a.isNone = false := by
    cases a; repeat' simp

  @[simp]
  theorem isSuccess_isNone {h : isSuccess result}
  : result.value.isNone = false := by simp_all [isSuccess]

  @[simp]
  theorem not_isSuccess_isNone {h : isSuccess result = false}
  : result.value.isNone = true := by simp_all [isSuccess]

  @[simp]
  theorem isNone {_ : a.isNone}
  : a = none := by simp_all

  @[simp]
  theorem isSome {_ : a.isSome}
  : ∃ v, a = some v := by cases a; repeat' simp_all

  @[simp]
  theorem isSuccess_value {h : isSuccess result}
  : ∃ v, value result = some v := by simp_all

  @[simp]
  theorem not_isSuccess_value {h : isSuccess result = false}
  : value result = none := by simp_all

  @[simp]
  theorem errors_eq_nil : errors result = [] → result.isSuccess = true := by
    intro h_eq_nil
    false_or_by_contra
    suffices _ : result.errors ≠ [] by contradiction
    apply result.errorsNotNil
    simp_all

  def get (self : ParseResult α) (h : self.isSuccess) :=
    self.value.get (by simp_all)

  def map (self : ParseResult a) (f : a -> b) : ParseResult b :=
    if h : self.isSuccess = true then
      success (f (self.get h)) self.rest
    else
      fromErrors self.errors self.rest (self.errorsNotNil (by simp_all))

  @[simp]
  theorem map_isSuccess {f : α -> β}
  : (map self f).isSuccess = self.isSuccess := by
    cases h : self.isSuccess
    repeat' simp_all [map]

  @[simp]
  theorem isSuccess_map {f : α -> β} {h : isSuccess self}
  : self.map f = success (f (self.get h)) self.rest := by
    simp_all [map]

  @[simp]
  theorem not_isSuccess_map {f : α -> β} {h : isSuccess self = false}
  : self.map f = fromErrors self.errors self.rest (self.errorsNotNil (by simp_all)) := by
    simp_all [map]

  def prependErrors
  (self : ParseResult α)
  (errors : List Error)
  : ParseResult α :=
    { self with
      errors := errors ++ self.errors
      errorsNotNil := by simp_all [self.errorsNotNil] }

  def andThen (self : ParseResult α) (f : (α × ParseInput) → ParseResult β)
  : ParseResult β :=
    if h : self.isSuccess then
      f (self.get h, self.rest)
      |>.prependErrors self.errors
    else 
      have : self.errors ≠ [] := by simp_all [self.errorsNotNil]
      fromErrors self.errors self.rest (h := this)
      
  theorem not_isSuccess_andThen
  (self: ParseResult α)
  (notSuccess : self.isSuccess = false)
  (f : (α × ParseInput) → ParseResult β)
  : ∃ h, self.andThen f = fromErrors self.errors self.rest h := by
    have : self.value = none := by simp_all
    rcases self
    simp at this
    subst this
    simp_all [andThen]
      
  theorem isSuccess_andThen
  (self: ParseResult α)
  (h : self.isSuccess)
  (f : (α × ParseInput) → ParseResult β)
  : (let next := f (self.get h, self.rest)
     self.andThen f = next.prependErrors self.errors) := by simp_all [andThen]

end ParseResult

namespace Parser

  def success (val : α) : Parser α :=
    fun input => ParseResult.success val input

  def fromErrors (errors : List Error) (h : errors ≠ []) : Parser α :=
    fun input => ParseResult.fromErrors errors input h

  abbrev run (parser : Parser α) (input : ParseInput) : ParseResult α :=
    parser input

  def map (self : Parser α) (f : α -> β) : Parser β :=
    fun input => self |>.run input |>.map f

  /-
  @[simp]
  theorem map_isSuccess {f : α -> β} {h : (run self input).isSuccess}
  : (map self f).run input = self.run input |>.map f := by
  -/

  def andThen (first : Parser a) (second : a -> Parser b) : Parser b :=
    fun input =>
      let firstResult := first input
      firstResult.andThen fun (value, rest) => second value rest

  def or (first : Parser α) (second : Parser α) : Parser α := fun input =>
    if (first input).isSuccess then
      first input
    else
      second input
      
end Parser

def char : Parser (Option Char) := fun input =>
  match input with
  | [] => ParseResult.success none []
  | c :: cs => ParseResult.success (some c) cs

@[simp]
theorem char_empty : char [] = .success none [] := rfl

@[simp]
theorem char_cons
: char (h :: t) = .success (some h) t := rfl

@[simp]
theorem char_isSuccess : (char input).isSuccess :=
  by cases input; repeat simp

def sequence (condition : Char → Option α)
: Parser (List α) := inner
where
  inner : ParseInput -> ParseResult (List α)
    | [] => ParseResult.success [] []
    | c :: cs =>
      if let some a := condition c then
        inner cs |>.map (a :: .)
      else
        ParseResult.success [] cs

def nat : Parser Nat :=
  sequence (Option.filter Char.isDigit ∘ some)
  |>.map List.asString
  |>.andThen fun str => match str.toNat? with
    | some n => .success n
    | none => .fromError Error.ExpectedNat

def int : Parser Int :=
  (minus.andThen fun () => nat.map fun n => -(Int.ofNat n))
  |>.or (plus.andThen fun () => nat.map Int.ofNat)
  |>.or (nat.map Int.ofNat)
  where
    minus : Parser Unit := char |>.andThen fun c =>
      if c == '-' then .success () else .fromError Error.ExpectedMinus
    plus : Parser Unit := char |>.andThen fun c =>
      if c == '+' then .success () else .fromError Error.ExpectedMinus

def literal : Parser Ast :=
  int.map Ast.val

#eval literal.run "42".toList
#eval ParseResult.success (Ast.val 42) []
example : literal.run "42".toList == .success (Ast.val 42) [] := by decide

def parse (str : String) : Option Ast := sorry
  
