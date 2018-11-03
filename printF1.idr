data Printable : List Char -> Type where
  PStr : Printable rest -> Printable ('%'::'s'::rest)
  PNum : Printable rest -> Printable ('%'::'i'::rest)
  Lit : Printable rest -> Printable (c::rest)
  None : Printable []

ToPrintable : (xs: List Char) -> Printable xs
ToPrintable [] = None
ToPrintable ('%' :: 's' :: xs) = PStr $ ToPrintable xs
ToPrintable ('%' :: 'i' :: xs) = PNum $ ToPrintable xs
ToPrintable (x::xs) = Lit $ ToPrintable xs

total
toFormat : (cs: List Char) -> Type
toFormat cs with (ToPrintable cs)
  toFormat ('%' :: ('s' :: rest)) | (PStr x) = String -> toFormat rest
  toFormat ('%' :: ('i' :: rest)) | (PNum x) = Int -> toFormat rest
  toFormat (c :: rest) | (Lit x) = toFormat rest
  toFormat [] | None = String

toFunc : (accu: String) -> (cs: List Char) -> (toFormat cs)
toFunc accu cs with (ToPrintable cs)
  toFunc accu ('%' :: ('s' :: rest)) | (PStr x) = \str => toFunc (accu ++ str) rest
  toFunc accu ('%' :: ('i' :: rest)) | (PNum x) = \num => toFunc (accu ++ show num) rest
  toFunc accu (c :: rest) | (Lit x) = toFunc (accu ++ cast c) rest
  toFunc accu [] | None = accu

printf : (str: String) -> toFormat (unpack str)
printf str = toFunc "" (unpack str)
