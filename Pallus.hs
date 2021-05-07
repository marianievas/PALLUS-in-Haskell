----------------------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------PALLÚS™️-------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------------------------------------------------

{-|
...
          Llenguatges de programació - Pràctica Haskell
            26 Apr 2021
                  Maria Nievas Viñals
...
-}


{-# LANGUAGE RecordWildCards #-}

import Data.Char (isUpper)
import Data.List (nub, isInfixOf)
import Data.List.Split (splitOn)
import Data.String.Utils (strip)
import Data.Maybe (mapMaybe, fromMaybe)

data Regla = Regla { _cap::Atom, _cos::[ Atom ] }
  deriving (Eq, Show)
data Atom = Atom { _nomPredicat::String, _termes::[ Term ] }
  deriving (Eq, Show)
data Term = Var String | Sym String
  deriving (Eq, Show, Read)

type BaseConeixement = [ Atom ]

type Programa = [ Regla ]

type Sustitucio = [ (Term, Term) ]


-------------------------------------------------------------------------------------------------------------------------------------------

{-|
   | The 'sustitucioBuida' returns an empty 'Sustitucio'
-}
sustitucioBuida :: Sustitucio
sustitucioBuida = []

{-|
   | Extracts from a list of Either all the Left elements. All the Left elements are extracted in order.
-}
lefts   :: [Either a b] -> [a]
lefts x = [a | Left a <- x]

{-|
   | Extracts from a list of Either all the Right elements. All the Right elements are extracted in order.
-}
rights   :: [Either a b] -> [b]
rights x = [a | Right a <- x]

{-|
   | The 'isAtomInKb' function checks whether an Atom, which belongs to the consequent of a Regla with an empty field '_cos', exists inside the given Base del Coneixement
   It takes two arguments, the first of type 'Atom' and the second of type "BaseConeixement", and it returns a 'Bool'
-}
isAtomInKb:: Atom -> BaseConeixement -> Bool
isAtomInKb atom kb = atom `elem` kb

{-|
   | The 'resultAnswer' function gives the answer to the query given. The solution can be a boolean or a list of substitutions, depending on the query format.
   If the Regla extracted from the 'String' input has no antecedents, then the resultAnswer will be a boolean of what returns the function 'isAtomInKb'.
   Otherwise, the resultAnswer will be obtained from avaluating the respective query and returning a list of all the possible Substitucions derived form that query
   It takes two arguments, the first of type 'String' and the second of type "BaseConeixement" and it returns an 'Either' type
-}
resultAnswer:: String ->  BaseConeixement -> Either Bool [Sustitucio]
resultAnswer reg kb =
        let atomRes = saveAtom (splitOn " " (last (splitOn " => " reg)))
        in case () of
        _ | (length (splitOn " " (last (splitOn " => " reg))) == 1) -> Left (isAtomInKb (saveAtom (splitOn " " (head (splitOn " => " reg)))) kb)
          | otherwise                                               -> Right (avaluaAtom (consequencia (map saveRegla [reg]) kb) atomRes [])

{-|
   | The 'divideQueries' function handles the concatenation of all the answers of the queries given, with the format of
   a list of an Either type - a 'Bool' or a list of Substitutions, given by the call of the 'resultAnswer' function.
   It takes two arguments, the first of type '[String]' and the second of type "BaseConeixement", and it returns a list of an 'Either' type
-}
divideQueries:: [String] -> BaseConeixement -> [Either Bool [Sustitucio]]
divideQueries [] _ = []
divideQueries (x:xs) kb = [resultAnswer x kb] ++ (divideQueries xs kb)

{-|
   | The 'buildSustitucio' function builds one sustitució within all the list of termes of two Atoms
   It takes two arguments, both of type '[Term]' and it returns a Substitucio
-}
buildSustitucio:: [Term] -> [Term] -> Sustitucio
buildSustitucio t1 t2
            | t1 == []        = []
            | otherwise       = [( (head t1), (head t2) )] ++ ( buildSustitucio (tail t1) (tail t2) )

{-|
   | The 'lookForSameVariables' function checks whether a Substitucio can be built taking into account that two variables cannot be
   referenced to different constants
   It takes two arguments, both of type '[Term]' and it returns a 'Bool'
-}
lookForSameVariables:: [Term] -> [Term] -> Bool
lookForSameVariables [] [] = True
lookForSameVariables t1 t2
                | length(t1) == 1                                                    = True
                | ((head t1) == (head(tail t1))) && ((head t2) /= (head(tail t2)))   = False
                | otherwise                                                          = lookForSameVariables (tail t1) (tail t2)

{-|
   | The 'possibleUnify' function is responsible for the possible Substitucio from two Atoms.
   It takes two arguments, both of type 'Atom'. The first one comes from the antecedent of a Regla,
   and the second one is an Atom Ground taken from the Kb.
   The return value is of type 'Maybe', that returns a Substitucio if the unify process can take place; otherwise it returns 'Nothing'
-}
possibleUnify :: Atom -> Atom -> Maybe Sustitucio
possibleUnify atom1 atom2
            | (_nomPredicat atom1) /= (_nomPredicat atom2)                      = Nothing
            | length(_termes atom1) /= length(_termes atom2)                    = Nothing
            | (_termes atom1) == (_termes atom2)                                = Just []
            | lookForSameVariables (_termes atom1) (_termes atom2) == False     = Nothing
            | otherwise                                                         = Just (buildSustitucio (_termes atom1) (_termes atom2))

{-|
   | The 'listUnify' function is responsible for the union of two lists of Substitucions.
   It takes two arguments, both of type '[[Sustitucio]]' and it returns a '[Sustitucio]'
-}
listUnify :: [[Sustitucio]] -> [[Sustitucio]] -> [Sustitucio]
listUnify s1 s2  = concat( sequence (s1++s2))

{-|
   | The 'avaluaAtom' function evaluates an Atom. If the list of Substitucions is empty, the function builds a list of
   Substitucions within the call to 'possibleUnify' for each Atom of the Kb list. Otherwise, it calls the 'listUnify' to bring together the
   list of Substitucions that had already as a parameter, and the one treated with 'possibleUnify'
   It takes three arguments, of type 'BaseConeixement', 'Atom' and '[Substitucio]' and it returns a '[Substitucio]'
-}
avaluaAtom :: BaseConeixement -> Atom -> [ Sustitucio ] -> [ Sustitucio ]
avaluaAtom kb ant [] = mapMaybe (\x -> possibleUnify ant x) kb
avaluaAtom kb ant sustAnt = nub (listUnify [sustAnt] [(mapMaybe (\x -> possibleUnify ant x) kb)]) --cridar aquí també a validar sustitució per cada sust

{-|
   | The 'avaluaAntecedents' recursive function evaluates each antecedent of a Regla, and fills the list of 'Sustitucio'
   by calling 'avaluaAtom' in each call.
   It takes three arguments, of type 'BaseConeixement', '[Atom]' and '[Substitucio]' and it returns a '[Substitucio]'
-}
avaluaAntecedents:: BaseConeixement -> [Atom] -> [ Sustitucio ] -> [Sustitucio]
avaluaAntecedents _ [] sustAct = sustAct
avaluaAntecedents kb antecedents sustAct
                  = let novaSust = (avaluaAtom kb (head antecedents) sustAct)
                  in case () of
                  _ | novaSust == [] -> avaluaAntecedents kb (tail antecedents) sustAct
                    | otherwise      -> avaluaAntecedents kb (tail antecedents) novaSust

{-|
   | The 'canBeANewAtom' function checks whether a list of Terms (from the consequent of a Regla) can be derived to an Atom Ground
   based on the Substitucio applied.
   It takes two arguments, of type '[Term]' and 'Sustitucio' and it returns a Bool
-}
canBeANewAtom:: [Term] -> Sustitucio -> Bool
canBeANewAtom [] _ = True
canBeANewAtom (x:xs) sust
              | True `elem` (map (\termPar -> (fst(termPar) == x)) sust) = canBeANewAtom xs sust
              | otherwise                                                = False

{-|
   | The 'replaceTerms' function is responsible to replace the Terms from an Atom to convert that atom to ground.
   It takes two arguments, of type 'Sustitucio' and '[Term]' and it returns a '[Term]'
-}
replaceTerms:: Sustitucio -> [Term] -> [Term]
replaceTerms sust [] = []
replaceTerms sust (x:xs) = [snd(i) | i <- sust, fst(i) == x] ++ replaceTerms sust xs

{-|
   | The 'sustitueix' function creates a new Atom, by taking a Substitucio and an Atom and calling 'replaceTerms'
   It takes two arguments, of type 'Atom' and 'Sustitucio' and it returns a 'Atom'
-}
sustitueix :: Atom -> Sustitucio -> Atom
sustitueix at [] = at
sustitueix at sust = Atom (_nomPredicat at) (replaceTerms sust (_termes at))

{-|
   | The 'avaluaRegla' function evaluates a Regla, taking the list of Sustitucions and, if new atoms can be derived,
   the function fills the given Kb with the new incorporations, calling 'sustitueix'.
   It takes two arguments, of type 'BaseConeixement' and 'Regla' and returns a 'BaseConeixement'
-}
avaluaRegla :: BaseConeixement -> Regla -> BaseConeixement
avaluaRegla [] _ = []
avaluaRegla kb reg = map (\x -> sustitueix (_cap reg) x) $ filter ( canBeANewAtom (_termes (_cap reg))) (avaluaAntecedents kb (_cos reg) [sustitucioBuida])

--------------------------------------------------------------------------------------------------------------------------------------------------------------

{-|
   | The 'areAllTermsConstants' function Check whether all terms from an Atom are constants
   It takes one argument, of type '[Term]' and returns a 'Bool'
-}
areAllTermsConstants:: [Term] -> Bool
areAllTermsConstants [] = True
areAllTermsConstants (x:xs)
            | head(show x) == 'V'    = False
            | otherwise              = areAllTermsConstants xs

{-|
   | The 'fillGroundAtoms' function fills the BaseConeixement with the ground Atoms
   It takes one argument, of type '[Atom]' and returns a '[Atom]'
-}
fillGroundAtoms:: [Atom] -> [Atom]
fillGroundAtoms [] = []
fillGroundAtoms (x:xs)
        | areAllTermsConstants (_termes x) == True     = [x] ++ fillGroundAtoms xs
        | otherwise                                    = [] ++ fillGroundAtoms xs

{-|
   | The 'fillWithoutEvaluating' function is responsible to fill the Kb recursively when the program is reading atoms from Regles with no antecedents,
   because they do not need to be evaluated by the function 'avaluaRegla'
   It takes two arguments, of type 'Programa' and 'BaseConeixement' and returns a 'BaseConeixement'
-}
fillWithoutEvaluating:: Programa -> BaseConeixement -> BaseConeixement
fillWithoutEvaluating [] _ = []
fillWithoutEvaluating (x:xs) kbActual --kbActual initially empty
        | [x] == (x:xs) && (_cos x) == []   = kbActual ++ [_cap x]                                                    --the program we've been given has only 1 regla and it has no antecedents
        | [x] == (x:xs) && (_cos x) /= []   = kbActual ++ (fillGroundAtoms (_cos x)) ++ fillGroundAtoms [(_cap x)]    --the program we've been given has only 1 regla, and has consequents as well as antecedents
        | (_cos x) == []                    = fillWithoutEvaluating xs ([_cap x] ++ kbActual)
        | otherwise                         = fillWithoutEvaluating xs (kbActual ++ (fillGroundAtoms (_cos x)) ++ (fillGroundAtoms [(_cap x)]) )


{-|
   | The 'fillWithoutEvaluating' function is responsible to fill the Kb recursively with the Regles from our program.
   It takes two arguments, of type 'Programa' and 'BaseConeixement' and returns a 'BaseConeixement'
-}
fillALL:: Programa -> BaseConeixement -> BaseConeixement
fillALL [] _ = []
fillALL (x:xs) kbActual
        | kbActual == []                    = fillWithoutEvaluating (x:xs) kbActual --first case with kb empty
        | [x] == (x:xs) && (_cos x) == []   = kbActual ++ [_cap x]
        | [x] == (x:xs) && (_cos x) /= []   = kbActual ++ avaluaRegla kbActual x
        | (_cos x) == []                    = fillALL xs (kbActual ++ [_cap x])
        | otherwise                         = fillALL xs (kbActual ++ avaluaRegla kbActual x)

{-|
   |The 'consequencia' function creates the BaseConeixement with multiple calls until the last Kb created
   is the same as the previous one.
   It takes two argument, of type 'Programa' and 'BaseConeixement' and returns a 'BaseConeixement'
-}
consequencia:: Programa -> BaseConeixement -> BaseConeixement
consequencia pr kb
            = let kbNew = nub (fillALL pr kb)
            in case () of
           _ | kb == kbNew  -> kb
             | otherwise    -> consequencia pr kbNew


----------------------------------------------------------------------------------------------------------------------------------------------
----------------------------------------------------PARSING-----------------------------------------------------------------------------------

{-|
   |The 'parseTerm' function parses a string to a Term value, which can be a variable or a constant
   It takes one argument, of type 'String'
-}
parseTerm:: String -> Term
parseTerm s
      | isUpper (head s) == True = Var s
      | otherwise                = Sym s

{-|
   |The 'saveTerms' function parses a string into a term one by one by calling the parseTerm function
   It takes one argument, of type '[String]'
-}
saveTerms:: [String] -> [Term]
saveTerms [] = []
saveTerms (x:xs) = [parseTerm x] ++ saveTerms xs

{-|
   |The 'saveAtom' function declares an atom from a list of terms
   It takes one argument, of type '[String]'
-}
saveAtom:: [String] -> Atom
saveAtom (x:xs) = Atom x (saveTerms xs)

{-|
   |The 'separarAntecedent' function takes an antecedent and splits it into individual atoms.
   It takes one argument, of type '[String]'
-}
separarAntecedent:: [String] -> [Atom]
separarAntecedent [] = []
separarAntecedent (x:xs) = [saveAtom (splitOn " " x)] ++ separarAntecedent xs

{-|
   |The 'treatThirdCase' function creates a regla, defining its conseqüent from the last element of the string and its antecedents by parsing them them from the head of the string
   It takes one argument, of type '[String]'
-}
treatThirdCase:: [String] -> Regla
treatThirdCase resultAnswer = Regla (saveAtom (splitOn " " (last resultAnswer))) (separarAntecedent (splitOn " & " (head resultAnswer)))

{-|
   |The 'treatSecondCase' function creates a regla and defines its conseqüent from the last element of the string and its antecedent from its head
   It takes one argument, of type '[String]'
-}
treatSecondCase:: [String] -> Regla
treatSecondCase reg = Regla (saveAtom (splitOn " " (last reg))) [(saveAtom (splitOn " " (head reg)))]

{-|
   |The 'saveRegla' function creates a regla and defines the conseqüent if it includes no =>. If it includes an & it
   It takes one argument, of type 'String'
-}
saveRegla:: String -> Regla
saveRegla reg
          | (length (splitOn " => " reg) == 1)                        = Regla (saveAtom (splitOn " " reg)) []
          | (length (splitOn "&" (head (splitOn " => " reg))) == 1)   = treatSecondCase (splitOn " => " reg)
          | otherwise                                                 = treatThirdCase (splitOn " => " reg)

-----------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------MAIN------------------------------------------------------------------------------

main :: IO ()
main = do
  inp <- getContents
  if inp/= "end" then do
    let program = map saveRegla (init (splitOn ".\n" (head (splitOn "end" inp))))
    if (program /= []) then do
      let kb0 = []
      let kb = consequencia program kb0
      let resultAnswer = divideQueries (init (tail(splitOn ".\n" ((splitOn "end" inp) !! 1)))) kb
      mapM print (lefts resultAnswer)
      mapM print (rights resultAnswer)
      pure()
    else
      pure()
  else
    pure()
