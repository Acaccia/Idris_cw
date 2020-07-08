module Sprintf

%access export
%default total

data Format = FInt Format
            | FDouble Format
            | FChar Format
            | Lit String Format
            | End

SprintfType : Format -> Type
SprintfType (FInt fmt) = Int -> SprintfType fmt
SprintfType (FDouble fmt) = Double -> SprintfType fmt
SprintfType (FChar fmt) = Char -> SprintfType fmt
SprintfType (Lit str fmt) = SprintfType fmt
SprintfType End = String

sprintFmt : (fmt : Format) -> (acc : String) -> SprintfType fmt
sprintFmt (FInt fmt) acc = \i => sprintFmt fmt (acc ++ show i)
sprintFmt (FDouble fmt) acc = \d => sprintFmt fmt (acc ++ show d)
sprintFmt (FChar fmt) acc = \c => sprintFmt fmt (acc ++ singleton c)
sprintFmt (Lit str fmt) acc = sprintFmt fmt (acc ++ str)
sprintFmt End acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: xs) = FInt (toFormat xs)
toFormat ('%' :: 'f' :: xs) = FDouble (toFormat xs)
toFormat ('%' :: 'c' :: xs) = FChar (toFormat xs)
toFormat ('%' :: '%' :: xs) = Lit "%" (toFormat xs)
toFormat (x :: xs) = case toFormat xs of
                          Lit str fmt => Lit (strCons x str) fmt
                          fmt => Lit (singleton x) fmt

sprintf : (fmt : String) -> SprintfType (toFormat (unpack fmt))
sprintf fmt = sprintFmt _ ""
