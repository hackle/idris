import Language.JSON
import Language.JSON.Data

replaceKvp : String -> JSON -> List (String, JSON) -> List (String, JSON)
replaceKvp k v xs = map (\(k1, v1) => if k1 == k then (k, v) else (k1, v1)) xs

mergeKvps : (xs : List (String, JSON)) -> (ys : List (String, JSON)) -> (merger: JSON -> JSON -> JSON) -> List (String, JSON)
mergeKvps xs [] _ = xs
mergeKvps xs (kvp@(k, v) :: ys) merger = case find (\(k1, _) => k1 == k) xs of
  Nothing => mergeKvps (xs++[kvp]) ys merger
  (Just (_, v1)) => mergeKvps (replaceKvp k (merger v1 v) xs) ys merger

mergeJson : JSON -> JSON -> JSON
mergeJson (JObject xs) (JObject ys) = JObject $ mergeKvps xs ys mergeJson
mergeJson _ json2 = json2

mergeJsonStrs : String -> String -> String
mergeJsonStrs x y = case (parse x, parse y) of
                    (Just a, Just b) => format 4 $ mergeJson a b
                    (_, Just b) => format 4 b
                    _ => ""

merge1 : String
merge1 = mergeJsonStrs """{
  "a": 11,
  "b": {
      "c": true,
      "e": {
        "f": "bar",
        "g": 200
      }
    }
  }"""
  """{
    "a": 11,
    "b": {
      "d": "foo",
      "e": {
        "h": "quux"
      }
    }
  }"""

main : IO ()
main = do
  putStr merge1
