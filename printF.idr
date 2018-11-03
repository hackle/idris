data Format : Type where
  Lit : Char -> Format -> Format
  IntF : Format -> Format
  StringF : Format -> Format
  End : Format

string2Format : List Char -> Format
string2Format [] = End
string2Format ('%' :: 'i' :: xs) = IntF $ string2Format xs
string2Format ('%' :: 's' :: xs) = StringF $ string2Format xs
string2Format (x::xs) = Lit x $ string2Format xs

Format2Func : Format -> Type
Format2Func (Lit xs x) = Format2Func x
Format2Func (IntF x) = Int -> Format2Func x
Format2Func (StringF x) = String -> Format2Func x
Format2Func End = String

toFunc : (acc: String) -> (fmt: Format) -> Format2Func fmt
toFunc acc (Lit x y) = toFunc (acc++(cast x)) y
toFunc acc (IntF x) = \n => toFunc (acc++(show n)) x
toFunc acc (StringF x) = \str => toFunc (acc++str) x
toFunc acc End = acc

printf : (xs: String) -> Format2Func (string2Format $ unpack xs)
printf xs = let format = string2Format (unpack xs) in toFunc "" format
