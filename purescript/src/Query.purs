module Query where

import Prelude

import Binding (Binding(..), Bindings, Expr(..), Id, Tag, Tup(..), Value(..), Var)
import Binding as Binding
import Control.Monad.State (State, evalState, modify)
import Data.Array as Array
import Data.Foldable (class Foldable, foldl)
import Data.Generic.Rep (class Generic)
import Data.List (List(..), concat, (:))
import Data.List (foldl) as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (sequence)
import Data.Tuple (Tuple(..))
import Effect.Exception.Unsafe (unsafeThrow)
import Story (Story, LabeledStory, Stage, Rule, Program)
import Story as Story

appends :: forall a f. Monoid a => Foldable f => f a -> a
appends = foldl append mempty

type Pattern a =
  { tag :: Tag
  , parent :: Var
  , id :: Var
  , terms :: Array a
  }

data QNormal a
  = QNormalQuery (Pattern a)
  | QNormalAssert (Pattern a)
  | QNormalPar (List (QNormal a))
  | QNormalAsk -- todo

data QExpr a
  = QBasic Tag (Array a) (List (QExpr a))
  | Par (List (QExpr a))
  | Assert (QExpr a)

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
  children' <- concat <$> sequence (map (flatten mode id) children)
  pure $ fmToCons mode { tag, parent, id, terms } : children'
flatten mode parent (Par qs) = do
  qs' <- concat <$> sequence (map (flatten mode parent) qs) -- same parent
  pure $ QNormalPar qs' : Nil
flatten _ parent (Assert q) = flatten FMAssert parent q -- same parent

rootVar :: Var
rootVar = "__root" -- ??

flattenQuery :: forall a. QExpr a -> List (QNormal a)
flattenQuery q = evalState (flatten FMQuery rootVar q) 0

type Tuples = Map Tag (Set Tup)
type DB =
  { childParents :: Set (Tuple Id Id)
  , tuples :: Tuples
  }

dbLookup :: Tag -> DB -> Set Tup
dbLookup tag { tuples } =
  case Map.lookup tag tuples of
    Nothing -> unsafeThrow $ "missing tag: " <> tag
    Just ts -> ts

dbInsert :: Tuples -> String -> Tup -> Tuples
dbInsert db tag tuple = db <> Map.singleton tag (Set.singleton tuple)

bindLookup :: String -> Binding -> Maybe Value

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

evalTupleId :: Binding -> Var -> Id
evalTupleId b var = case evalTerm b (ExprVar var) of
  ExprValue (ValueInt i) -> i
  _ -> unsafeThrow $ "missing parent var: " <> var

unifyOne :: Expr -> Value -> Maybe Binding
unifyOne (ExprValue v) v' = if v == v' then Just Binding.empty else Nothing
unifyOne (ExprVar var) v = Just $ Binding.single var v

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
    qp = evalTupleId b queryParent
    tuples = dbLookup tag db
  in
    Set.mapMaybe
      ( \(Tup { id: idVal, parent, values }) ->
          if ancestorOf db parent qp then do
            newBindings <- unify exprs values
            pure $ b <> newBindings <> (Binding.single id (ValueInt idVal))
          else Nothing
      )
      tuples

doJoins :: DB -> Pattern Expr -> Bindings -> Bindings
doJoins db q = Set.unions <<< Set.map (doJoin db q)

doAssert_ :: Tuples -> Pattern Expr -> Binding -> M Tuples
doAssert_ tuples { tag, parent, terms } b =
  let
    values = map (evalTerm' b) terms
    parent' = evalTupleId b parent
  in
    do
      id <- freshId
      let tuple = Tup { tag, id, parent: parent', values }
      pure $ dbInsert tuples tag tuple

-- do: assertions (update childParents)
doAssert :: DB -> Pattern Expr -> Binding -> M DB
doAssert { childParents: c, tuples: t } p b = do
  tuples <- doAssert_ t p b
  childParents <- mempty -- TODO
  pure { childParents, tuples }

unitBindings :: Bindings
unitBindings = Set.singleton (Binding Map.empty)

type Query = List (Pattern Expr)

-- do: join query
evalQuery :: DB -> Query -> Bindings
evalQuery db = List.foldl (flip (doJoins db)) unitBindings

--type RuleState = { bindings :: Bindings, todo :: List (QNormal Expr) }
--type Story = List (QNormal Expr)

type Branch = { binding :: Binding, parent :: Id, todo :: LabeledStory }
type ProgramState = { db :: DB, active :: List Branch, deferred :: Map Id Branch }


{-
class Keyed a key | a -> key where
  key :: a -> key

instance Keyed Rule (Tuple Tag Stage) where
  key (Rule {trigger, stage}) = Tuple trigger stage

toMap :: forall f a k. Functor f => Foldable f => Keyed a k => Ord k => f a -> Map k a
toMap fs = Map.fromFoldable $ map (\x -> Tuple (key x) x) fs

assembleRules :: List Rule -> Program
assembleRules x = toMap x
-}

{-
 rules
 new and old tuples
 create tuple
-}

{-
allBindings :: ProgramState -> Bindings
advance :: Branch -> M Branch

?
  what monad are we using for handling actors (Effect?)

-}

-- do: par (join up after)
-- do: agent queries?
-- do: deletion
-- do: interop
-- do: start on example
-- do: parse
-- todo: split into modules

-- did: dom helloworld
