{-# LANGUAGE TemplateHaskell #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH


import Data.RRB.Vector

--------------------------------------------------------------------------------

main :: IO ()
main = defaultMain allTests
  where allTests = testGroup "All" [ all_tests ]

all_tests :: TestTree
all_tests = $(testGroupGenerator)

--------------------------------------------------------------------------------

case_test1 :: Assertion
case_test1 = assertEqual "for (foo 3)," (1,2) (1,2)
