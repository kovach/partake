module Test.Main where

import Prelude

import Data.Array as Array
import Data.List (List(..))
import Data.Map as Map
import Data.Set as Set
import Data.Traversable (sequence_)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Class.Console (log)
import Episode (Episode(..), Story(..), Value(..), countMark, ppBindings, situationScope, toBindings, toEpisode)

e1 :: Episode
e1 = Bind "a" (ValueInt 22)
  ( Par ""
      (Bind "b" (ValueInt 0) Null)
      (Bind "b" (ValueInt 1) Null)
  )

e2 :: Episode
e2 = Seq (Mark (Tip Done)) Null

e3 :: Episode
e3 = Bind "a" (ValueInt 22)
  ( Par ""
      (Bind "b" (ValueInt 0) (Mark Null))
      (Bind "b" (ValueInt 1) Null)
  )

episodes :: Array Episode
episodes = [ e1, e2 ]

bs as vs = Map.fromFoldable (Array.zip as (ValueInt <$> vs))

main :: Effect Unit
main = do
  log "🍝"
  log (show (countMark <$> episodes))
  sequence_ $ map (log <<< ppBindings) (toBindings <$> episodes)
  log (ppBindings (situationScope e3))

  log "toEpisode"
  let vars = [ "a", "b" ]
  let
    c = Set.fromFoldable
      [ bs vars [ 0, 1 ]
      , bs vars [ 0, 2 ]
      , bs vars [ 1, 0 ]
      ]
  let
    ep = toEpisode "t" c
      (Tip Done)
      (Array.toUnfoldable vars)
  log (show ep)
  ep # toBindings # ppBindings # log
  log $ show (c == (ep # toBindings))
