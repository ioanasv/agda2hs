module Haskell.RangedSets.RangedSet where

import Haskell.RangedSets.Boundaries

import Haskell.RangedSets.Ranges

import Data.List

okAdjacent ::
             Ord a => DiscreteOrdered a => Range a -> Range a -> Bool
okAdjacent (Rg lower1 upper1) (Rg lower2 upper2)
  = rangeLower (Rg lower1 upper1) <= rangeUpper (Rg lower1 upper1) &&
      rangeUpper (Rg lower1 upper1) <= rangeLower (Rg lower2 upper2) &&
        rangeLower (Rg lower2 upper2) <= rangeUpper (Rg lower2 upper2)

validRangeList :: Ord a => DiscreteOrdered a => [Range a] -> Bool
validRangeList [] = True
validRangeList [x] = rangeLower x <= rangeUpper x
validRangeList (x : (r1 : rss))
  = okAdjacent x r1 && validRangeList (r1 : rss)

data RSet a = RS [Range a]

rSetRanges :: Ord a => DiscreteOrdered a => RSet a -> [Range a]
rSetRanges (RS ranges) = ranges

overlap1 ::
           Ord a => DiscreteOrdered a => Range a -> Range a -> Bool
overlap1 (Rg _ upper1) (Rg lower2 _) = upper1 >= lower2

normalise :: Ord a => DiscreteOrdered a => [Range a] -> [Range a]
normalise (r1 : (r2 : rs))
  = if overlap1 r1 r2 then
      normalise
        (Rg (rangeLower r1) (max (rangeUpper r1) (rangeUpper r2)) : rs)
      else r1 : normalise (r2 : rs)
normalise rs = rs

unsafeRangedSet ::
                  Ord a => DiscreteOrdered a => [Range a] -> RSet a
unsafeRangedSet rs = RS rs

ranges3 ::
          Ord a =>
            DiscreteOrdered a =>
            Maybe (Boundary a) ->
              (Boundary a -> Boundary a) ->
                (Boundary a -> Maybe (Boundary a)) -> [Range a]
ranges3 (Just b1) upperFunc succFunc
  = if validFunction2 b1 upperFunc && validFunction b1 succFunc then
      ranges2 b1 upperFunc succFunc else []
ranges3 Nothing _ _ = []

ranges2 ::
          Ord a =>
            DiscreteOrdered a =>
            Boundary a ->
              (Boundary a -> Boundary a) ->
                (Boundary a -> Maybe (Boundary a)) -> [Range a]
ranges2 b upperFunc succFunc
  = Rg b (upperFunc b) : ranges3 (succFunc b) upperFunc succFunc

setBounds1 ::
             Ord a => DiscreteOrdered a => [Boundary a] -> [Boundary a]
setBounds1 (BoundaryBelowAll : xs) = xs
setBounds1 xs = BoundaryBelowAll : xs

bounds1 :: Ord a => DiscreteOrdered a => [Range a] -> [Boundary a]
bounds1 (r : rs) = rangeLower r : (rangeUpper r : bounds1 rs)
bounds1 [] = []

ranges1 :: Ord a => DiscreteOrdered a => [Boundary a] -> [Range a]
ranges1 (b1 : (b2 : bs)) = Rg b1 b2 : ranges1 bs
ranges1 [BoundaryAboveAll] = []
ranges1 [b] = [Rg b BoundaryAboveAll]
ranges1 _ = []

merge1 ::
         Ord a => DiscreteOrdered a => [Range a] -> [Range a] -> [Range a]
merge1 [] [] = []
merge1 (h1 : t1) [] = h1 : t1
merge1 [] (h3 : t2) = h3 : t2
merge1 (h1 : t1) (h3 : t2)
  = if h1 < h3 then h1 : merge1 t1 (h3 : t2) else
      h3 : merge1 (h1 : t1) t2

merge2 ::
         Ord a => DiscreteOrdered a => [Range a] -> [Range a] -> [Range a]
merge2 [] [] = []
merge2 (h1 : t1) [] = []
merge2 [] (h3 : t2) = []
merge2 (h1 : t1) (h3 : t2)
  = rangeIntersection h1 h3 :
      if rangeUpper h1 < rangeUpper h3 then merge2 t1 (h3 : t2) else
        merge2 (h1 : t1) t2

rSingleton :: Ord a => DiscreteOrdered a => a -> RSet a
rSingleton a = RS [singletonRange a]

normaliseRangeList ::
                     Ord a => DiscreteOrdered a => [Range a] -> [Range a]
normaliseRangeList [] = []
normaliseRangeList (r1 : rss)
  = normalise
      (sort (filter (\ r -> rangeIsEmpty r == False) (r1 : rss)))

makeRangedSet :: Ord a => DiscreteOrdered a => [Range a] -> RSet a
makeRangedSet [] = RS []
makeRangedSet (r1 : rss) = RS (normaliseRangeList (r1 : rss))

rangesAreEmpty :: Ord a => DiscreteOrdered a => [Range a] -> Bool
rangesAreEmpty [] = True
rangesAreEmpty (r : rs) = rangeIsEmpty r && rangesAreEmpty rs

rSetIsEmpty :: Ord a => DiscreteOrdered a => RSet a -> Bool
rSetIsEmpty (RS ranges) = rangesAreEmpty ranges

rSetNegation :: Ord a => DiscreteOrdered a => RSet a -> RSet a
rSetNegation (RS ranges)
  = RS (ranges1 (setBounds1 (bounds1 ranges)))

rSetIsFull :: Ord a => DiscreteOrdered a => RSet a -> Bool
rSetIsFull set = rSetIsEmpty (rSetNegation set)

rSetEmpty :: Ord a => DiscreteOrdered a => RSet a
rSetEmpty = RS []

rSetFull :: Ord a => DiscreteOrdered a => RSet a
rSetFull = RS [Rg BoundaryBelowAll BoundaryAboveAll]

rSetHas :: Ord a => DiscreteOrdered a => RSet a -> a -> Bool
rSetHas (RS []) _ = False
rSetHas (RS [r]) value = rangeHas r value
rSetHas (RS (r : rs)) value
  = rangeHas r value || rSetHas (RS rs) value

(-?-) :: Ord a => DiscreteOrdered a => RSet a -> a -> Bool
(-?-) rs = rSetHas rs

rSetUnion ::
            Ord a => DiscreteOrdered a => RSet a -> RSet a -> RSet a
rSetUnion (RS ls1) (RS ls2) = RS (normalise (merge1 ls1 ls2))

(-\/-) :: Ord a => DiscreteOrdered a => RSet a -> RSet a -> RSet a
rs1 -\/- rs2 = rSetUnion rs1 rs2

rSetIntersection ::
                   Ord a => DiscreteOrdered a => RSet a -> RSet a -> RSet a
rSetIntersection (RS ls1) (RS ls2)
  = RS (filter (\ x -> rangeIsEmpty x == False) (merge2 ls1 ls2))

(-/\-) :: Ord a => DiscreteOrdered a => RSet a -> RSet a -> RSet a
rs1 -/\- rs2 = rSetIntersection rs1 rs2

rSetDifference ::
                 Ord a => DiscreteOrdered a => RSet a -> RSet a -> RSet a
rSetDifference rs1 rs2 = rSetIntersection rs1 (rSetNegation rs2)

(-!-) :: Ord a => DiscreteOrdered a => RSet a -> RSet a -> RSet a
rs1 -!- rs2 = rSetDifference rs1 rs2

rSetIsSubset ::
               Ord a => DiscreteOrdered a => RSet a -> RSet a -> Bool
rSetIsSubset rs1 rs2 = rSetIsEmpty (rSetDifference rs1 rs2)

(-<=-) :: Ord a => DiscreteOrdered a => RSet a -> RSet a -> Bool
rs1 -<=- rs2 = rSetIsSubset rs1 rs2

rSetIsSubsetStrict ::
                     Ord a => DiscreteOrdered a => RSet a -> RSet a -> Bool
rSetIsSubsetStrict rs1 rs2
  = rSetIsEmpty (rSetDifference rs1 rs2) &&
      not (rSetIsEmpty (rSetDifference rs2 rs1))

(-<-) :: Ord a => DiscreteOrdered a => RSet a -> RSet a -> Bool
rs1 -<- rs2 = rSetIsSubsetStrict rs1 rs2

rSetUnfold ::
             Ord a =>
               DiscreteOrdered a =>
               Boundary a ->
                 (Boundary a -> Boundary a) ->
                   (Boundary a -> Maybe (Boundary a)) -> RSet a
rSetUnfold bound upperFunc succFunc
  = RS (normalise (ranges2 bound upperFunc succFunc))

