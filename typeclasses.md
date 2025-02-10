# Type-Classes in Lean 4

This document is an introduction to type-classes in Lean 4.

## Type-Classes in General

Type-classes are the functional equivalent of interfaces in object-oriented
programming. Usually, the main difference between interfaces and type-classes
is that interfaces are types while type-classes are *type constraints*.

For example, if in some language we have an interface `Collection` we use it like
this:
```csharp
def dropMaximum (c: Collection) :=
    -- Mutably removes the maximum element from the collection.
    c.dropAt(c.indexOfMaximum())
```
While in Lean 4, this would be more something like:
```lean
def dropMaximum [Collection C] (c: C): C :=
    -- Everything is immutable, can't modify, must return a new one.
    c.withoutElementAt(c.indexOfMaximum)
```
The shows that while interfaces *hide* the structure of the data while
type-classes do not.

## Lean 4 Specifics

In contrast to other languages, Lean 4 type-classes are also types. The
instances of type-classes are regular objects and can be manipulated as such.
Example:
```lean
class Collection (α: Type) where
    empty : α
    insert : α -> Int -> α
    remove : α -> Int -> α

instance intListIsCollection : Collection (List Int) where
    empty := []
    insert l i := l.insert i
    remove l i := l.removeAll [i]

#print intListIsCollection
```

## TODO

What does `deriving` do?
```lean
class Loggable (α: Type) where
    state : Type
    log : state → α → state

instance intIsLoggable : Loggable Int where
    state := List Int
    log l i := i :: l

#print intIsLoggable

def mapLog (l : Loggable β) (f : α → β) : Loggable α :=
  { state := l.state
    log s a := l.log s (f a)
  }

instance natIsLoggable : Loggable Nat := mapLog intIsLoggable (fun x => x.toInt64.toInt)
```
