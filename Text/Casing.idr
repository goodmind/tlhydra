module Text.Casing

import List.Split

%access public export

||| An opaque type that represents a parsed identifier.
record Identifier a where
  constructor MkIdentifier
  unIdentifier : List a
-- deriving (Monad, Functor, Applicative, Show, Foldable, Traversable)

Functor Identifier where
  map f (MkIdentifier x) = MkIdentifier (map f x)

implementation Applicative Identifier where
  pure x = MkIdentifier [x]
  (MkIdentifier f) <*> (MkIdentifier fa) = MkIdentifier (f <*> fa)

implementation Monad Identifier where
  -- `x` : List a; `k` : a -> Identifier a (i.e. a -> MkIdentifier (List a))
  (MkIdentifier x) >>= k = MkIdentifier [y | a <- x, let MkIdentifier l = k a, y <- l]

removePunc : String -> String
removePunc = pack . removePunc' . unpack where
  removePunc' : List Char -> List Char
  removePunc' xs = [ x | x <- xs, not (x `elem` unpack ",.?!-:;\"\'") ]

wordCase : String -> String
wordCase s with (strM s)
  wordCase ""             | StrNil = ""
  wordCase (strCons x xs) | (StrCons x xs) = toUpper x `strCons` toLower xs

-- | Convert from "humped" casing (@camelCase@ or @PascalCase@)
fromHumps : String -> Identifier String
fromHumps = MkIdentifier . (map pack) . go . unpack where
  go : List Char -> List (List Char)
  go [] = [[]]
  go [x] = [[x]]
  go (x :: (y :: ys)) =
    let (z :: zs) = go (y :: ys) in
    if not (isUpper x) && isUpper y
    then [x] :: (z :: zs)
    else (x :: z) :: zs

fromWords : String -> Identifier String
fromWords = MkIdentifier . words

-- | Convert from @kebab-cased-identifiers@
fromKebab : String -> Identifier String
fromKebab = MkIdentifier . (map pack) . (wordsBy (== '-')) . unpack

-- | Convert from @snake_cased@ (either flavor)
fromSnake : String -> Identifier String
fromSnake = MkIdentifier . (map pack) . (wordsBy (== '_')) . unpack

-- | Convert from anything, including mixed casing.
fromAny : String -> Identifier String
fromAny str = fromHumps str >>= fromKebab >>= fromSnake >>= fromWords
  
-- | To @PascalCase@
toPascal : Identifier String -> String
toPascal = concat . map wordCase . unIdentifier

-- | To @camelCase@
toCamel : Identifier String -> String
toCamel (MkIdentifier (x :: xs)) = concat $ (toLower x) :: (map wordCase xs)

-- | To @kebab-case@
toKebab : Identifier String -> String
toKebab = concat . intersperse "-" . map toLower . unIdentifier
  
-- | To @snake_Case@
toSnake : Identifier String -> String
toSnake = concat . intersperse "_" . unIdentifier
  
-- | To @quiet_snake_case@
toQuietSnake : Identifier String -> String
toQuietSnake = toLower . toSnake
  
-- | To @SCREAMING_SNAKE_CASE@
toScreamingSnake : Identifier String -> String
toScreamingSnake = toUpper . toSnake
  
-- | To @word Case@
toWords : Identifier String -> String
toWords = unwords . unIdentifier

-- | Directly convert to @PascalCase@ through 'fromAny'
pascal : String -> String
pascal = toPascal . fromAny

-- | Directly convert to @camelCase@ through 'fromAny'
camel : String -> String
camel = toCamel . fromAny

-- | Directly convert to @snake_Case@ through 'fromAny'
snake : String -> String
snake = toSnake . fromAny
  
-- | Directly convert to @quiet_snake_case@ through 'fromAny'
quietSnake : String -> String
quietSnake = toQuietSnake . fromAny
  
-- | Directly convert to @SCREAMING_SNAKE_CASE@ through 'fromAny'
screamingSnake : String -> String
screamingSnake = toScreamingSnake . fromAny
  
-- | Directly convert to @kebab-case@ through 'fromAny'
kebab : String -> String
kebab = toKebab . fromAny
  
-- | Directly convert to @word Case@ through 'fromAny'
wordify : String -> String
wordify = toWords . fromAny
  
-- | Drop the first word from a parsed identifier. Typical usage is between
-- parsing and writing, e.g.: @toKebab . dropPrefix . fromAny $ "strHelloWorld" == "hello-world"@
dropPrefix : Identifier String -> Identifier String
dropPrefix = MkIdentifier . drop 1 . unIdentifier
