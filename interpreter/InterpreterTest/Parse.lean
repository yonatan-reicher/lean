import InterpreterTest.Ast

abbrev ParseInput := List Char

inductive Error : Type where
  deriving Repr

/--
An optional value α, with additional errors emitted and where
the rest of the input.
-/
structure ParseResult (α : Type) : Type where
  value : Option α
  rest : ParseInput
  errors : List Error
  errorsNotNil : value = none → errors ≠ []
  deriving Repr

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

  theorem isSuccess_fromErrors {α errors rest h}
  : isSuccess (@fromErrors α errors rest h) = false := by
    unfold fromErrors isSuccess
    cases h : (fromErrors errors rest h : ParseResult α)
    simp_all

  @[simp]
  theorem errors_eq_nil : errors result = [] → result.isSuccess = true := by
    by_contra
    simp

  theorem not_success (h : !isSuccess self) : self.value.isNone :=
    by simp at h; simp_all

  def map : ParseResult a -> (a -> b) -> ParseResult b
    | { value := none, errors := e, rest := r, .. }, _ =>
      fromErrors e r (by simp_all)
    | { value := some value, rest := rest, .. }, f => success (f value) rest

  theorem map_not_isSuccess
  (self : ParseResult a) (f : a -> b) (h : isSuccess self = false)
  : (self.map f).isSuccess = false := by
    rcases self
    simp_all [map]

  theorem map_isSuccess_eq_success
  (self : ParseResult a) (f : a -> b) (h : isSuccess self)
  : self.map f = success (f <| self.value.get (by simp_all)) self.rest := by
    rcases self with ⟨value⟩
    unfold map
    unfold isSuccess at h
    simp at h
    cases value
    . contradiction
    . simp_all

  theorem map_isSuccess
  (self : ParseResult a) (f : a -> b) (h : isSuccess self)
  : (self.map f).isSuccess := by simp_all

  def andThen (self : ParseResult α) (f : (α × ParseInput) → ParseResult β)
  : ParseResult β :=
    match h : self.value with
    | some value =>
      let next := f (value, self.rest)
      let allErrors := self.errors ++ next.errors
      have : next.value.isNone → allErrors ≠ [] := fun _ =>
        have : next.errors ≠ [] := by simp_all
        by simp [this, allErrors]
      { value := next.value
        rest := next.rest
        errors := allErrors
        errorsNotNil := by assumption
      }
    | none =>
      have : self.errors ≠ [] := by simp_all
      fromErrors self.errors self.rest (h := this)
      
  theorem andThen_not_isSuccess
  (self: ParseResult α)
  (notSuccess : self.isSuccess = false)
  (f : (α × ParseInput) → ParseResult β)
  : (self.andThen f).isSuccess = false := by
    rcases self with ⟨value⟩
    have : value = none := by simp_all
    subst this
    unfold andThen
    simp
      
  theorem andThen_isSuccess
  (self: ParseResult α)
  (notSuccess : self.isSuccess)
  (f : (α × ParseInput) → ParseResult β)
  : (self.andThen f).isSuccess = (f (self.value.get (by simp_all), self.rest)).isSuccess := by
    rcases self with ⟨value⟩
    cases value
    . exact Bool.noConfusion notSuccess
    . unfold andThen
      simp_all

end ParseResult

namespace Parser

  def success (val : α) : Parser α :=
    fun input => ParseResult.success val input

  def fromError (error : Error) : Parser α :=
    fun input => ParseResult.fromError error input

  abbrev run (parser : Parser α) (input : ParseInput) : ParseResult α :=
    parser input

  def andThen (first : Parser a) (second : a -> Parser b) : Parser b :=
    fun input =>
      let firstResult := first input
      firstResult.andThen fun (value, rest) => second value rest
      
  theorem andThen_isSuccess
  (first : Parser a) (second : a -> Parser b) (input : ParseInput)
  (h : first.run input |>.isSuccess)
  : ((first.andThen second).run input).isSuccess = (second (first.run input |>.value.get (by simp_all)).value input).isSome := by
    simp_all

end Parser

def parse_sequence (condition : Char → Option α)
: Parser (List α) := fun input =>
  match input with
  | [] => ParseResult.success [] []
  | c :: cs =>
    if let Option.some x := condition c then
      cs |> Parser.run (
        Parser.success x |>.andThen fun x =>
        parse_sequence condition
      )
    else
      ParseResult.failure

def parse_literal (str : String) : ParseResult Ast := by
  sorry

example : parse_literal "42" = some (Ast.val 42) := by
  sorry

def parse (str : String) : Option Ast := sorry
  
