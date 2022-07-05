import Test.HUnit

import Types
import qualified Search

assertProvable :: Formula -> Assertion
assertProvable phi =
  case Search.searchIter Search.defaultOptions (createSignature phi) phi :: [PTerm] of
    [] -> assertBool "failed on provable" False
    p:_ -> assertBool "typecheck failed" (check p phi)

assertUnprovable :: Formula -> Assertion
assertUnprovable phi =
  assertBool "success on unprovable"
    (null (Search.searchIter Search.defaultOptions (createSignature phi) phi :: [()]))

testProvable :: String -> Test
testProvable s = s ~: assertProvable (read s)

testUnprovable :: String -> Test
testUnprovable s = s ~: assertUnprovable (read s)

tests :: Test
tests = test [
    testProvable "a -> a"
  , testUnprovable "a -> b"
  ]

main :: IO ()
main = runTestTTAndExit tests
