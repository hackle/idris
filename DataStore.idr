module Main

import Data.Vect
import Data.String

infixr 5 .+.

data Schema : Type where
  SString : Schema
  SInt : Schema
  (.+.) : Schema -> Schema -> Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
  constructor MkData
  schema: Schema
  size: Nat
  items: Vect size (SchemaType schema)

appendV : a -> (items : Vect size a) -> Vect (S size) a
appendV x [] = [x]
appendV x (y :: xs) = y :: appendV x xs

addToStore : (ds: DataStore) -> SchemaType (schema ds) -> DataStore
addToStore (MkData sch size items) x = MkData _ (S size) (appendV x items)

data Command a = Add a
              | Get Integer
              | Quit

convertTo : (content : String) -> (sch : Schema) -> Maybe (SchemaType sch)
convertTo content SString = Just content
convertTo content SInt = parseInteger content
convertTo content (x .+. y) = case break (== ' ') content of
                                (a, b) => MkPair <$> convertTo a x <*> convertTo (ltrim b) y

parse : (sch: Schema) -> String -> Maybe (Command (SchemaType sch))
parse sch str = case break (== ' ') str of
                 ("add", content) => convertTo (ltrim content) sch >>= (Just . Add)
                 ("get", index) => (case all isDigit (unpack $ ltrim index) of
                                         True => Just (Get (cast index))
                                         False => Nothing)
                 ("quit", _) => Just Quit
                 _ => Nothing

showItem : (item : SchemaType sch) -> String
showItem item {sch = SString} = item
showItem item {sch = SInt} = show item
showItem item {sch = (x .+. y)} = showItem (fst item) ++ "," ++ showItem (snd item)

process_input : (ds: DataStore) -> String -> Maybe (String, DataStore)
process_input ds command = case parse (schema ds) command of
                                Nothing => Just ("try again\n", ds)
                                (Just (Add x)) => Just ("added\n", addToStore ds x)
                                (Just (Get idx)) => (case integerToFin idx (size ds) of
                                                          Nothing => Just ("not found\n", ds)
                                                          (Just findex) => let item = Vect.index findex (items ds)
                                                                                in Just (showItem item ++ "\n", ds))
                                (Just Quit) => Nothing

data VectU : Type -> Type where
  MkVectU : Vect len a -> VectU a

sizeVU : VectU a -> Nat
sizeVU (MkVectU xs) = length xs

addUV : a -> VectU a -> VectU a
addUV x (MkVectU xs) = MkVectU (x::xs)

filterVU : (a -> Bool) -> Vect m a -> VectU a
filterVU f [] = MkVectU []
filterVU f (x :: xs) = let xs1 = filterVU f xs in (case f x of
                                                        False => xs1
                                                        True => addUV x xs1)

filter1 : (a -> Bool) -> Vect m a -> (n**Vect n a)
filter1 f xs = case filterVU f xs of
                    (MkVectU xs) => (_**xs)

charToSchema : List Char -> Maybe Schema
charToSchema ['I'] = Just SInt
charToSchema ['S'] = Just SString
charToSchema [_] = Nothing
charToSchema (x::','::xs) = (.+.) <$> (charToSchema [x]) <*> (charToSchema xs)

getSchema : IO Schema
getSchema = do
  putStrLn "What type? S -> String, I -> Integer or type1,type2,type3... -> Compound?"
  ty <- getLine
  case charToSchema (unpack (toUpper ty)) of
    Nothing => do
                putStrLn "Not valid, try again"
                getSchema
    (Just x) => pure x


main : IO ()
main =
  do
    schema <- getSchema
    replWith (MkData schema _ []) "add x, get i, quit>" process_input
