import Language.JSON
import Language.JSON.Data

replaceKey : String -> JSON -> List (String, JSON) -> List (String, JSON)
replaceKey k v xs = map tryReplace xs where
  tryReplace (k1, v1) = if k1 == k then (k, v) else (k1, v1)

mergeObjects :  (xs : List (String, JSON)) ->
                (ys : List (String, JSON)) ->
                (merger: JSON -> JSON -> JSON) ->
                List (String, JSON)
mergeObjects xs [] _ = xs
mergeObjects xs (kvp@(k, v) :: ys) merger =
  case find (\(k1, _) => k1 == k) xs of
    Nothing => mergeObjects (xs++[kvp]) ys merger
    (Just (_, v1)) => mergeObjects (replaceKey k (merger v1 v) xs) ys merger

mergeJson : JSON -> JSON -> JSON
mergeJson (JObject xs) (JObject ys) = JObject $ mergeObjects xs ys mergeJson
mergeJson _ json2 = json2

mergeJsonStrs : String -> String -> String
mergeJsonStrs x y = case (parse x, parse y) of
                      (Just a, Just b) => format 4 $ mergeJson a b
                      (_, Just b) => format 4 b
                      _ => ""

merge1 : String
merge1 = mergeJsonStrs """{
  "key1": 11,
  "key2": {
      "key2.1": true,
      "key2.2": {
        "key2.2.1": "bar",
        "key2.2.2": 200
      }
    }
  }"""
  """{
    "key1": 12,
    "key2": {
      "key2.2": {
        "key2.2.1": "quux"
      },
      "key2.3": "foo"
    }
  }"""

main : IO ()
main = do
  putStr merge1
