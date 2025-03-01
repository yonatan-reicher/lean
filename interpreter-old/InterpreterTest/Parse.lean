import InterpreterTest.Ast

/--
Input for parsers is just a list of characters.
-/
abbrev ParseInput := List Char

inductive Error : Type where
  | ExpectedMinus : Error
  | ExpectedNat : Error
  deriving Repr, DecidableEq

/--
Either a successful result or a failure.
Both carry the rest of the input that they didn't eat up along with them.
Notice that successful results can still have errors. Motivation: you might be
able to return something just so the rest of the parsing can continue without
completely stopping.
-/
--a sars a
inductive ParseResult (α : Type) : Type where
  | success (value : α) (rest : ParseInput) (errors : List Error) : ParseResult α
  | failure (rest : ParseInput) (errors : List Error) (h : errors ≠ []) : ParseResult α
  deriving Repr, DecidableEq

@[simp] def Parser ret := ParseInput → ParseResult ret

namespace ParseResult

  -- Simple ways to construct

  def success (value : α) (rest : ParseInput) : ParseResult α :=
    { value := some value
      rest := rest
      errors := []
      errorsNotNil := by simp }
  
  /-
  On implementing theorems for properties:
  I like working with @[simp] theorems, it makes life easy. The trick is to
  make sure that you give the right simp theorems. @[simp] theorems should
  partially evaluate an expression, towards some normal form.
  In our case, for ParseResult, the normal form is either success or failure.
  -/

  @[simp]
  theorem success_rest {value: α} {rest}
  : (success value rest).rest = rest := rfl

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

  theorem get_eq_get! {h : isSuccess (self : ParseResult α)} [Inhabited α]
  : self.get h = self.value.get! := by
    unfold get
    rw [Option.get_eq_get!]

  @[simp]
  theorem get_success
  {result: α} {rest} {h}
  : (success result rest).get h = result := rfl

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

  abbrev run (parser : Parser α) (input : ParseInput) : ParseResult α :=
    parser input

  def success (val : α) : Parser α :=
    fun input => ParseResult.success val input

  @[simp]
  theorem run_success
  {val : α} {input}
  : run (success val) input = .success val input := rfl

  def fromErrors (errors : List Error) (h : errors ≠ []) : Parser α :=
    fun input => ParseResult.fromErrors errors input h

  @[simp]
  theorem run_fromErrors
  {α} {errors} {h}
  : run (@fromErrors α errors h) input = .fromErrors errors input h := rfl

  def map (self : Parser α) (f : α -> β) : Parser β :=
    fun input => self |>.run input |>.map f

  @[simp]
  theorem run_map {f : α -> β}
  : run (map self f) input = (run self input).map f := rfl

  def andThen (first : Parser a) (second : a -> Parser b) : Parser b :=
    fun input =>
      let firstResult := first input
      firstResult.andThen fun (value, rest) => second value rest

  @[simp]
  theorem run_andThen
  {f : α -> Parser β}
  : run (self.andThen f) input = (
      let firstResult := run self input
      firstResult.andThen (fun (value, rest) => f value rest)
    ) := rfl

  def or (first : Parser α) (second : Parser α) : Parser α := fun input =>
    if (first input).isSuccess then
      first input
    else
      second input

  @[simp]
  theorem run_or {first : Parser α} {second : Parser α}
  : run (first.or second) input = (
      if (first input).isSuccess then
        first input
      else
        second input
    ) := rfl
      
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
        ParseResult.success [] (c :: cs)

@[simp]
theorem sequence_empty {cond: Char -> Option α}
: sequence cond [] = .success [] [] := rfl

@[simp]
theorem sequence_isSuccess
{cond : Char -> Option α} {input}
: (sequence cond input).isSuccess := by
  -- sequence cond (head :: tail) depends on sequence cond tail so we use 
  -- induction.
  induction input
  case nil => simp
  case cons h t ih =>
    -- split by cases to go into both parts of the if.
    cases h_cond : cond h
    repeat simp_all [sequence, sequence.inner]

@[simp]
theorem sequence_cons_true
{cond: Char -> Option α} {head} {tail}
(cond_head : cond head = some a)
(h : sequence cond tail = .success as rest)
: sequence cond (head :: tail) = .success (a :: as) rest := by
  unfold sequence at *
  simp_all [sequence.inner]

@[simp]
theorem sequence_cons_false
{cond : Char -> Option α} {head} {tail}
(cond_head : cond head = none)
: sequence cond (head :: tail) = .success [] (head :: tail) := by
  unfold sequence at *
  simp_all [sequence.inner]

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
  
