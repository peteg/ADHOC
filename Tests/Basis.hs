{-# OPTIONS_GHC -XNoImplicitPrelude #-}
module Tests.Basis
    (
      module Tests.Basis
    , module Data.Maybe
    , module Test.QuickCheck
    , module ADHOC
    ) where

-- Hide the Prelude stuff, urk.
import Data.Maybe hiding ( Maybe(..), maybe )

import Test.QuickCheck hiding ( conjoin, disjoin )

import ADHOC hiding ( runNL )
import qualified ADHOC ( runNL )

----------------------------------------

-- We want to DeepSeq runNL. This is cheesy but it works.
runNL c = show nl `seq` nl
  where nl = ADHOC.runNL c
