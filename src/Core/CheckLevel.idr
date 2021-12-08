module Core.CheckLevel

import Data.List
import Data.List1
import Data.Maybe
import Data.Either
import Libraries.Data.Graph
import Libraries.Data.SortedMap
import Libraries.Data.SortedSet

import Core.Name
import Core.Context

joinByFst : Ord k => Ord v => List (k, v) -> SortedMap k (SortedSet v)
joinByFst [] = empty
joinByFst ((k, v) :: xs) =
  let rest = joinByFst xs in
  case lookup k rest of
    Nothing => insert k (singleton v) rest
    Just set => insert k (insert v set) rest

||| Given a partition of a set of elements into equivalence classes
||| and an arbitrary element of the set returns its representative in the class.
||| Assume that if the list doesn't contain a class, the class has exactly one element.
contract : Ord a => List (SortedSet a) -> a -> a
contract contractible x =
  fromMaybe x (findCenterOfContraction contractible x)
  where
   -- Center of contraction is taken arbitrary to be the first element of a set of contractible elements.
   findCenterOfContraction : List (SortedSet a) -> a -> Maybe a
   findCenterOfContraction [] x = Nothing
   findCenterOfContraction (l :: ls) x =
     case contains x l of
       True =>
         case (SortedSet.toList l) of -- This is inefficient, we just want the first element

           [] => Nothing -- impossible
           centerOfContraction :: _ => Just centerOfContraction
       False => findCenterOfContraction ls x

isSingleton : List1 a -> Bool
isSingleton (_ ::: []) = True
isSingleton _ = False

isReflexive : Ord a => (a, a) -> Bool
isReflexive (x, y) = x == y

LTEConstraint : Type
LTEConstraint = (Name, Name)

LTConstraint : Type
LTConstraint = (Name, Name)

toEither : UConstraint -> Either LTEConstraint LTConstraint
toEither (ULE a b) = Left (a, b)
toEither (ULT a b) = Right (a, b)

||| Check if constraints of the form:
||| {x < y, x <= y}, where x, y are elements of a linearly ordered finite set,
||| are satisfiable.
public export
satisfiable : List UConstraint -> Bool
satisfiable u = do
  let (lteInitial, ltInitial) = partitionEithers (map toEither u)
  let lte = joinByFst lteInitial
  let contractible = map (fromList . forget) $ tarjan lte
  let lt0 = filter (not . isReflexive) (map @{Compose} (contract contractible) lteInitial)
  let lt1 = (map @{Compose} (contract contractible) ltInitial)
  case all (not . isReflexive) lt1 of
    False => False
    True => do
      let lt = joinByFst (lt0 ++ lt1)
      all isSingleton (tarjan lt)

export
solveLevelConstraints : {auto c : Ref Ctxt Defs}
                     -> FC
                     -> Core ()
solveLevelConstraints fc = do
  u <- map (uconstraints . gamma) $ get Ctxt
  case satisfiable u of
    True => pure ()
    False => throw (CyclicLevel fc)

