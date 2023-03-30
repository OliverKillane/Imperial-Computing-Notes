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
    tableRows :: [Row]
  }

-- Types for query optimisation
type Cost = Int
type Selectivity = Double

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
    aggCols :: [ColumnID],
    aggFun  :: Maybe Value -> Row -> Value,
    outCol  :: ColumnID
  }

data Operator = 
    Scan        Table
  | Select      Operator Predicate Selectivity 
  | Project     Operator RowTrans
  | Product     Operator Operator
  | Join        Operator Operator Predicate Selectivity
  | Difference  Operator Operator
  | Union       Operator Operator
  | Aggregation Operator AggFun Selectivity
  | TopN        Operator SortBy

getOutputs :: Operator-> [ColumnID]
getOutputs op = case op of
  Select      op _   _   -> getOutputs op
  Project     _  rt      -> outputCols rt
  Product     op op'     -> getOutputs op ++ getOutputs op'
  Join        op op' _ _ -> getOutputs op ++ getOutputs op'
  Difference  op _       -> getOutputs op -- op' op assumed to have same cols
  Union       op _       -> getOutputs op -- op' op assumed to have same cols
  Aggregation op agf _   -> [outCol agf]
  TopN        op _       -> getOutputs op
  Scan        table      -> tableCols table

-- Map a function over the operators
apply :: (Operator -> Operator) -> Operator -> Operator
apply m op = case op of  
    Select      op p s     -> Select      (m op) p s
    Project     op rt      -> Project     (m op) rt
    Product     op op'     -> Product     (m op) (m op')
    Join        op op' p s -> Join (m op) (m op') p s
    Difference  op op'     -> Difference  (m op) (m op')
    Union       op op'     -> Union       (m op) (m op')
    Aggregation op cc af   -> Aggregation (m op) cc af
    TopN        op sb      -> TopN        (m op) sb
    op -> op

type Peephole = Operator -> Maybe Operator
type Optimiser = Operator -> Operator

logicalOnly :: Peephole
{- Selection Pushdown  
 - Assume join is more expensive than select (essentially always true)
 - Select operates on columns on one side of the join 

SELECT selectCols
FROM op1 JOIN op2
WHERE selectFun

.. goes to ...

SELECT *
FROM (SELECT selectCols FROM op1 WHERE selectFun) JOIN op2
-}
logicalOnly (Select (Join op op' p1 s1) p2 s2) 
  | getOutputs op `containsAll` selectCols p2
  = Just (Join (Select op p2 s2) op' p1 s1)
logicalOnly (Select (Join op op' p1 s1) p2 s2) 
  | getOutputs op' `containsAll` selectCols p2
  = Just (Join op (Select op' p2 s2) p1 s1)
{- Selection ordering
We push down selections that likely have lower selectivity
- Here we only consider == (EQ) and <> (NEQ)

SELECT ...
FROM (SELECT ... FROM op WHERE ... <> ...)
WHERE ... == ...

... goes to ...

SELECT ...
FROM (SELECT ... FROM op WHERE ... == ...)
WHERE ... <> ...

-}
logicalOnly 
  (Select (Select op p1@Predicate{selectCols=_, selectFun=(NOTEQUAL _ _)} s1) p2@Predicate{selectCols=_, selectFun=(EQUAL _ _)} s2)
  = Just (Select (Select op p2 s2) p1 s1)

-- default case
logicalOnly op = Nothing

-- Rules for optimising a query
naive :: Peephole
{- 
Reorder selectivity [Data Aware]
 - Use the lowest selectivity first
 - Assumes selectivities are independent
-} 
naive (Select (Select op p2 s2) p1 s1) | s2 > s1 
  = Just (Select (Select op p1 s2) p2 s2)

naive op = Nothing

-- Continue traversing until making an optimisation, then return to root.
-- As optimisations on either side of a join, difference, or union are 
-- independent, peep both separately.
root :: Peephole -> Optimiser
root peep orig = case optR of
    Just opt -> opt
    Nothing  -> apply (root peep) orig
  where
    optR = peep orig

-- traverse from bottom up - apply rules, then traverse from optimised.  
trav :: Peephole -> Optimiser
trav peep orig = apply (trav peep) (peep orig `orElse` orig)

-- apply opt n levels up the query
-- Pre: n >= 0
travLim :: Peephole -> Int -> Optimiser
travLim peep 0 orig = orig
travLim peep n orig = apply (travLim peep (n - 1)) (peep orig `orElse` orig)
