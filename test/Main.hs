import Control.Monad (when)
import System.Exit (exitFailure)
import System.IO
import Test.HUnit

import Types
import qualified Search

assertProvableWith :: Search.Options -> Formula -> Assertion
assertProvableWith opts phi =
  case Search.searchIter opts (createSignature phi) phi :: [PTerm] of
    [] -> assertBool "failed on provable" False
    p:_ -> assertBool "typecheck failed" (check p phi)

assertProvable :: Formula -> Assertion
assertProvable = assertProvableWith Search.defaultOptions

assertUnprovableWith :: Search.Options -> Formula -> Assertion
assertUnprovableWith opts phi =
  assertBool "success on unprovable"
    (null (Search.searchIter opts (createSignature phi) phi :: [()]))

assertUnprovable :: Formula -> Assertion
assertUnprovable = assertUnprovableWith Search.defaultOptions

testProvableWith :: Search.Options -> String -> Test
testProvableWith opts s = s ~: assertProvableWith opts (read s)

testProvable :: String -> Test
testProvable s = s ~: assertProvable (read s)

testUnprovableWith :: Search.Options -> String -> Test
testUnprovableWith opts s = s ~: assertUnprovableWith opts (read s)

testUnprovable :: String -> Test
testUnprovable s = s ~: assertUnprovable (read s)

tests :: Test
tests = test [
    testProvable "a -> a"
  , testUnprovable "a -> b"
  ]

runTest :: Test -> IO ()
runTest tst = do
  cnts <- runTestTT tst
  when (errors cnts + failures cnts > 0)
    exitFailure

runSimple :: IO ()
runSimple = do
  withFile "tests/simple.in" ReadMode (withFile "tests/simple.out" ReadMode . go)
  where
    go hin hout  = do
      done <- hIsEOF hin
      if done then
        return ()
      else do
        s <- hGetLine hin
        s' <- hGetLine hout
        if s' == "success" then
          runTest $ testProvable s
        else if s' == "failure" then
          runTest $ testUnprovable s
        else
          error "error parsing output file"
        go hin hout

runFile :: Search.Options -> String -> IO ()
runFile opts file = do
  withFile file ReadMode go
  where
    go hin = do
      done <- hIsEOF hin
      if done then
        return ()
      else do
        s <- hGetLine hin
        runTest $ testProvableWith opts s
        go hin

runExponential :: IO ()
runExponential = runFile Search.defaultOptions "tests/exponential.in"

runComplete :: IO ()
runComplete = runFile Search.defaultOptions{Search.optComplete = True} "tests/complete.in"

main :: IO ()
main = do
  runTest tests
  runSimple
  runExponential
  runComplete
