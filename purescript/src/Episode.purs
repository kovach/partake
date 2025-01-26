module Episode where

import Prelude

import Control.Monad.Identity.Trans (runIdentityT)
import Data.Foldable (fold, foldl, foldr)
import Data.FoldableWithIndex (foldrWithIndex)
import Data.Generic.Rep (class Generic)
import Data.Identity (Identity(..))
import Data.List (List(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Monoid.Additive (Additive(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Effect.Exception.Unsafe (unsafeThrow)

type Var = String
type Name = String

type Binding = Map Var Value
type Bindings = Set Binding
data Value
  = ValueInt Int
  | ValueString String
  | ValueBindings Bindings

derive instance valEq :: Eq Value
derive instance valOrd :: Ord Value

data Story = Done
type Time = String -- todo

data Episode
  = Par Time Episode Episode
  | Seq Episode Episode
  | Bind Var Value Episode
  | Prim Name Episode
  | Mark Episode
  | Tip Story
  | Null

derive instance genVal :: Generic Value _
derive instance genEp :: Generic Episode _
derive instance genSt :: Generic Story _

instance sv :: Show Value where
  show x = genericShow x

instance showSt :: Show Story where
  show = genericShow

instance showEp :: Show Episode where
  show x = genericShow x

ppValue :: Value -> String
ppValue = case _ of
  ValueInt i -> show i
  ValueString s -> s
  ValueBindings c -> ppBindings c

ppBinding :: Binding -> String
ppBinding b = foldrWithIndex
  (\k v s -> wrapP (k <> ":" <> show v) <> s)
  ""
  b

wrapP :: String -> String
wrapP s = "(" <> s <> ")"

wrapC :: String -> String
wrapC s = "{" <> s <> "}"

newline :: String -> String
newline s = s <> "\n"

ppBindings :: Bindings -> String
ppBindings = fold <<< Set.map (newline <<< wrapC <<< ppBinding)

maybeFn :: forall t79. Maybe (t79 -> t79) -> t79 -> t79
maybeFn f x = case f of
  Nothing -> x
  Just f -> f x

episodeMap :: forall f. Monad f => (Episode -> f Episode) -> Episode -> f Episode
episodeMap fn e =
  let
    rec = episodeMap fn
  in
    case e of
      Par t a b -> (Par t <$> (rec a) <*> (rec b)) >>= fn
      Seq a b -> (Seq <$> (rec a) <*> (rec b)) >>= fn
      Bind var val a -> (Bind var val <$> (rec a)) >>= fn
      Prim n a -> (Prim n <$> (rec a)) >>= fn
      Mark a -> (Mark <$> (rec a)) >>= fn
      Tip _ -> fn e
      Null -> fn e

episodeMap' :: (Episode -> Episode) -> Episode -> Episode
episodeMap' fn e = let Identity x = episodeMap (Identity <<< fn) e in x

episodeWalk :: forall a. Monoid a => (Episode -> Maybe (a -> a)) -> a -> Episode -> a
episodeWalk fn zero e =
  let
    rec = episodeWalk fn zero
    f = fn e
  in
    case e of
      Par _ a b -> maybeFn f (rec a <> rec b)
      Seq a b -> maybeFn f (rec a <> rec b)
      Bind _ _ a -> maybeFn f (rec a)
      Prim _ a -> maybeFn f (rec a)
      Mark a -> maybeFn f (rec a)
      Tip _ -> zero
      Null -> zero

todo :: forall a. String -> a
todo = unsafeThrow

sorry :: forall a. Unit -> a
sorry _ = todo "sorry"

countMark :: Episode -> Int
countMark e =
  let
    Additive x = episodeWalk
      ( case _ of
          Mark _ -> Just \x -> x <> (Additive 1)
          _ -> Nothing
      )
      (Additive 0)
      e
  in
    x

contextUnit :: Bindings
contextUnit = Set.singleton Map.empty

toBindings :: Episode -> Bindings
toBindings = episodeWalk
  ( case _ of
      Bind var val _ -> Just $ Set.map (Map.insert var val)
      _ -> Nothing
  )
  contextUnit

-- returns the scope at each Mark
-- not needed?
situationScope :: Episode -> Bindings
situationScope = episodeWalk
  ( case _ of
      Mark _ -> Just (\_ -> contextUnit)
      Bind var val _ -> Just $ Set.map (Map.insert var val)
      _ -> Nothing
  )
  Set.empty

withoutMarks :: Episode -> Episode
withoutMarks = episodeMap'
  ( case _ of
      Mark t -> t
      e -> e
  )

type Id = String
type Tag = Id
data Tuple = Tuple Tag (Array Value)

type ActorFn = Episode -> Tuple -> Binding -> Set Binding
type Actors = Map Time ActorFn

par :: Time -> Episode -> Episode -> Episode
par _ e Null = e
par _ Null e = e
par t a b = Par t a b

episodeOfValues :: Time -> Var -> (Value -> Episode) -> Set Value -> Episode
episodeOfValues t var f = foldr (\val -> par t (Bind var val (f val))) Null

toEpisode :: Time -> Bindings -> Episode -> List Var -> Episode
toEpisode _ _ base Nil = base
toEpisode t c base (Cons var vars) =
  let
    vals = Map.lookup var `Set.mapMaybe` c

    byVal :: Value -> Bindings
    byVal val = Set.filter (\m -> Map.lookup var m == Just val) c
  in
    episodeOfValues t var (\val -> toEpisode t (byVal val) base vars) vals

{-
  p a, choose 1 (q a b, r b c)
  ?rel (p a), (?rel (q a b), ?rel (r b c)), ?get-bindings _here, ?player ((= 1) _here)
-}
