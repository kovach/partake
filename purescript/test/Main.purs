module Test.Main where

import Prelude

import Effect (Effect)
import Effect.Class.Console (log)
import Parser as Parser

main :: Effect Unit
main = do
  log "🍝"
  log  "hi"
  Parser.main
