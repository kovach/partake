module Episode where

import Prelude

import Control.Monad.State (State, evalState, modify, runState)
import Data.Array as Array
import Data.Foldable (class Foldable, foldl, foldr)
import Data.Generic.Rep (class Generic)
import Data.List (List, concat, (:))
import Data.List (foldl) as List
import Data.Map (Map, update)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (sequence)
import Data.Tuple (Tuple(..))
import Effect.Exception.Unsafe (unsafeThrow)

appends :: forall a f. Monoid a => Foldable f => f a -> a
appends = foldl append mempty

type Var = String
type Name = String
type Time = String -- todo

newtype Binding = Binding (Map Var Value)
type Bindings = Set Binding -- todo: cost of deduplication
data Value
  = ValueInt Int
  | ValueString String
  | ValueBindings Bindings
  | ValueTup Tup

newtype Tup = Tup
  { tag :: Tag
  , id :: Id
  , parent :: Id
  , values :: (Array Value)
  }

type Id = Int
type Tag = String

data Expr = ExprValue Value | ExprVar Var

derive instance eqTup :: Eq Tup
derive instance ordTup :: Ord Tup
derive instance eqVal :: Eq Value
derive instance ordVal :: Ord Value
derive instance eqBind :: Eq Binding
derive instance ordBind :: Ord Binding
derive instance genVal :: Generic Value _
derive instance genTup :: Generic Tup _
derive instance genExpr :: Generic Expr _
derive instance genBind :: Generic Binding _

instance st :: Show Tup where
  show x = genericShow x

instance sb :: Show Binding where
  show x = genericShow x

instance sv :: Show Value where
  show x = genericShow x

instance se :: Show Expr where
  show x = genericShow x

emptyBinding = Binding Map.empty
singleBinding var val = Binding (Map.singleton var val)

instance semiBinding :: Semigroup Binding where
  append (Binding a) (Binding b) = Binding (Map.union a b)

instance monoidBinding :: Monoid Binding where
  mempty = emptyBinding

type Pattern a =
  { tag :: Tag
  , parent :: Var
  , id :: Var
  , terms :: Array a
  }

data QNormal a
  = QNormalQuery (Pattern a)
  | QNormalAssert (Pattern a)
  | QNormalAsk

data QExpr a = QBasic Tag (Array a) (List (QExpr a)) | Assert (QExpr a)

type M a = State Int a

fresh :: M Int
fresh = modify (_ + 1)

freshVar :: M Var
freshVar = show <$> modify (_ + 1)

freshId :: M Id
freshId = fresh

data FlattenMode = FMQuery | FMAssert

fmToCons :: forall a. FlattenMode -> Pattern a -> QNormal a
fmToCons FMQuery = QNormalQuery
fmToCons FMAssert = QNormalAssert

flatten :: forall a. FlattenMode -> Var -> QExpr a -> M (List (QNormal a))
flatten mode parent (QBasic tag terms children) = do
  id <- freshVar
  children' <- concat <$> sequence (map (flatten FMQuery id) children)
  pure $ fmToCons mode { tag, parent, id, terms } : children'
flatten _ parent (Assert q) = flatten FMAssert parent q

rootVar :: Var
rootVar = "__root" -- ??

flattenQuery :: forall a. QExpr a -> List (QNormal a)
flattenQuery q = evalState (flatten FMQuery rootVar q) 0

type DBTuples = Map Tag (Set Tup)
type DB =
  { childParents :: Set (Tuple Id Id)
  , tuples :: DBTuples
  }

dbLookup :: Tag -> DB -> Set Tup
dbLookup tag { tuples } =
  case Map.lookup tag tuples of
    Nothing -> unsafeThrow $ "missing tag: " <> tag
    Just ts -> ts

bindLookup v (Binding b) = Map.lookup v b

evalTerm :: Binding -> Expr -> Expr
evalTerm _ v@(ExprValue _) = v
evalTerm b v@(ExprVar var) = case bindLookup var b of
  Nothing -> v
  Just val -> ExprValue val

evalTerm' :: Binding -> Expr -> Value
evalTerm' _ (ExprValue v) = v
evalTerm' b (ExprVar var) = case bindLookup var b of
  Nothing -> unsafeThrow $ "missing var: " <> var
  Just val -> val

evalParent :: Binding -> Var -> Id
evalParent b var = case evalTerm b (ExprVar var) of
  ExprValue (ValueInt i) -> i
  _ -> unsafeThrow $ "missing parent var: " <> var

unifyOne :: Expr -> Value -> Maybe Binding
unifyOne (ExprValue v) v' = if v == v' then Just emptyBinding else Nothing
unifyOne (ExprVar var) v = Just $ singleBinding var v

unify :: Array Expr -> Array Value -> Maybe Binding
unify e v = appends <$> Array.zipWithA unifyOne e v

-- do: parent check
-- todo: special case root?
ancestorOf :: DB -> Id -> Id -> Boolean
ancestorOf _ x child | x == child = true
ancestorOf { childParents } x child = Tuple child x `Set.member` childParents

doJoin :: DB -> Pattern Expr -> Binding -> Bindings
doJoin db ({ tag, id, parent: queryParent, terms }) b =
  let
    exprs = map (evalTerm b) terms
    qp = evalParent b queryParent
    tuples = dbLookup tag db
  in
    Set.mapMaybe
      ( \(Tup { id: idVal, parent, values }) ->
          if ancestorOf db parent qp then do
            newBindings <- unify exprs values
            pure $ b <> newBindings <> (singleBinding id (ValueInt idVal))
          else Nothing
      )
      tuples

doJoins :: DB -> Pattern Expr -> Bindings -> Bindings
doJoins db q = Set.unions <<< Set.map (doJoin db q)

doAssert_ :: DBTuples -> Pattern Expr -> Binding -> M DBTuples
doAssert_ db { tag, parent, terms } b =
  let
    values = map (evalTerm' b) terms
    parent' = evalParent b parent
  in
    do
      id <- freshId
      let tuple = Tup { tag, id, parent: parent', values }
      pure $ db <> Map.singleton tag (Set.singleton tuple)

-- do: assertions (update childParents)
doAssert :: DB -> Pattern Expr -> Binding -> M DB
doAssert {childParents, tuples} p b =
  {childParents: ?x, tuples: _} <$> doAssert_ tuples p b

unitBindings :: Bindings
unitBindings = Set.singleton (Binding Map.empty)

type Query = List (Pattern Expr)

-- do: join query
evalQuery :: DB -> Query -> Bindings
evalQuery db = List.foldl (flip (doJoins db)) unitBindings

type RuleState = { bindings :: Bindings, todo :: List (QNormal Expr) }
type ProgramState = { db :: DB, stories :: List RuleState }

-- do: agent queries?
-- do: deletion
-- do: start on example
