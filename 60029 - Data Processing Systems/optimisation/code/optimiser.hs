{-
A toy haskell implementation of relational algebra with query optimisations.
 - Pattern Matching is very useful for optimisations
 - Easy print and display 

 I have not attempted to make data structures representative 
 (e.g here rows are a map)
-}

import Data.Map (Map, fromList)

orElse :: Maybe a -> a -> a
orElse (Just v) _ = v
orElse Nothing  v = v 

-- superset `containsAll` subset
containsAll :: Eq a => [a] -> [a] -> Bool
containsAll _      [] = True
containsAll ys (x:xs) = x `elem` ys && containsAll ys xs

data Value    = INTEGER Int | DOUBLE Double | VARCHAR String
type ColumnID = String
type Row      = [Value]

data Table = Table 
  {
    tableName :: String,
    tableCols :: [ColumnID],
    tableRows :: [Row],
    tableSize :: Int
  }

-- Some predicate types (e.g col1 == "a"), theta is included complex expressions 
data PredFun = EQUAL ColumnID Value | NOTEQUAL ColumnID Value | Theta (Row -> Bool) 

data Predicate = Predicate {
  selectCols :: [ColumnID],
  selectFun  :: PredFun
}

data RowTrans = RowTrans 
  {
    inputCols  :: [ColumnID],
    outputCols :: [ColumnID],
    trans      :: Row -> Row
  }
      
data SortBy = SortBy
  {
    sortCol :: ColumnID,
    sortFun :: [(Int, Value)] -> [(Int, Value)]
  }

data AggFun = AggFun 
  {
    aggCols   :: [ColumnID],
    aggGroups :: Int,
    aggFun    :: Maybe Value -> Row -> Value,
    outCol    :: ColumnID
  }

data Operator = 
    Scan        Table
  | Select      Operator Predicate
  | Project     Operator RowTrans
  | Product     Operator Operator
  | Join        Operator Operator Predicate
  | Difference  Operator Operator
  | Union       Operator Operator
  | Aggregation Operator AggFun
  | TopN        Operator SortBy Int

attributes :: Operator -> [ColumnID]
attributes op = case op of
  Select      op _       -> attributes op
  Project     _  rt      -> outputCols rt
  Product     op op'     -> attributes op ++ attributes op'
  Join        op op' _   -> attributes op ++ attributes op'
  Difference  op _       -> attributes op -- op' op assumed to have same cols
  Union       op _       -> attributes op -- op' op assumed to have same cols
  Aggregation op agf     -> [outCol agf]
  TopN        op _ _     -> attributes op
  Scan        table      -> tableCols table

type Peephole = Operator -> Maybe Operator
type Optimiser = Operator -> Operator

-- Map a function over the operators
apply :: (Operator -> Operator) -> Operator -> Operator
apply m op = case op of  
    Select      op p     -> Select      (m op) p
    Project     op rt    -> Project     (m op) rt
    Product     op op'   -> Product     (m op) (m op')
    Join        op op' p -> Join (m op) (m op') p
    Difference  op op'   -> Difference  (m op) (m op')
    Union       op op'   -> Union       (m op) (m op')
    Aggregation op af    -> Aggregation (m op) af
    TopN        op sb _  -> TopN        (m op) sb
    op -> op

-- Continue traversing until making an optimisation, then return to root.
-- As optimisations on either side of a join, difference, or union are 
-- independent, peep both separately.
root :: Peephole -> Optimiser
root peep orig 
  = case peep orig of
    Just opt -> opt
    Nothing  -> apply (root peep) orig

-- traverse from bottom up - apply rules, then traverse from optimised.  
trav :: Peephole -> Optimiser
trav peep orig = apply (trav peep) (peep orig `orElse` orig)

-- apply opt n levels up the query
-- Pre: n >= 0
travLim :: Peephole -> Int -> Optimiser
travLim peep 0 orig = orig
travLim peep n orig = apply (travLim peep (n - 1)) (peep orig `orElse` orig)

-- 
predicateLess :: Predicate -> Predicate -> Bool
predicateHeuristic 
  Predicate{selectFun=(NOTEQUAL _ _)} 
  Predicate{selectFun=(EQUAL _ _)} 
    = True
predicateHeuristic = False

predicateImplies :: Predicate -> Predicate -> Bool
predicateImplies = undefined

logicalRuleBased :: Peephole
-- Selection Pushdown  
-- Assume join is more expensive than select (essentially always true)
-- Select operates on columns on one side of the join 
logicalRuleBased (Select (Join op op' p1) p2) 
  | attributes op  `containsAll` selectCols p2 = Just (Join (Select op p2) op' p1) 
  | attributes op' `containsAll` selectCols p2 = Just (Join op (Select op' p2) p1)
-- Selection ordering
-- We push down selections that likely have lower selectivity
-- Here we only consider == (EQ) and <> (NEQ) 
logicalRuleBased
  (Select (Select op p1) p2) | p2 `predicateLess` p1
  = Just (Select (Select op p2) p1)
-- Selection Implies
-- Eliminate a redundant selection based on predicates implications 
logicalRuleBased
  (Select (Select op p1) p2) 
  | p1 `predicateImplies` p2 = Just (Select op p1)
  | p2 `predicateImplies` p1 = Just (Select op p2)  

-- default case
logicalRuleBased op = Nothing



-- Types for query optimisation
type Selectivity = Double
type Cost = Double

-- left unimplemented as it requires a great extension to Predicate
selectivity :: Predicate -> Cost
selectivity = undefined

-- Estimating the size of output relations
sizeCost :: Operator -> Cost
sizeCost op = case op of
  Scan        t         -> fromIntegral (tableSize t)
  Select      op   p    -> selectivity p * sizeCost op
  Project     op   _    -> sizeCost op
  Product     opL opR   -> sizeCost opL * sizeCost opR
  Join        opL opR p -> selectivity p * sizeCost opL * sizeCost opR
  Difference  opL opR   -> max (sizeCost opL) (sizeCost opR)
  Union       opL opR   -> sizeCost opL + sizeCost opR
  Aggregation _   af    -> aggGroups af
  TopN        op  _  n  -> min (sizeCost op) n

