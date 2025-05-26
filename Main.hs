import Prelude
import Data.Char
import Data.List
import Data.Maybe
import Text.ParserCombinators.Parsec
import Text.Parsec.Char
import Control.Monad
import CoqSolver
import System.Environment
import System.FilePath
import System.IO
import System.Directory
import System.Timeout

dimacsFile = sepEndBy line (endOfLine <?> "wtf")
line = try clauseLine <|> auxLine <?> "wtf"

clauseLine = do
    literals <- manyTill literal (char '0')
    return $ Just literals

auxLine = do
    many (noneOf "\n\r")
    return Nothing

literal = do
    minus <- optionMaybe $ char '-'
    num <- foldl' (\a i -> a * 10 + digitToInt i) 0 <$> many1 digit
    pos <- toBinPos num
    many1 space
    return $ case minus of
                Just _ -> Not pos
                Nothing -> Var pos

toBinPos 1 = return XH
toBinPos x = do
    guard $ x >= 1
    half <- toBinPos $ x `div` 2
    return $ case x `mod` 2 of 
                0 -> XO half 
                _ -> XI half 

fromBinPos :: Positive -> Int
fromBinPos XH = 1
fromBinPos (XI x) = 2 * (fromBinPos x) + 1
fromBinPos (XO x) = 2 * (fromBinPos x)

instance Show Positive where
    show p = show $ fromBinPos p

instance Show Literal where
    show (Var p) = "<Var " ++ show p ++ ">"
    show (Not p) = "<Not " ++ show p ++ ">"

parseDimacs :: String -> Either ParseError [Maybe [Literal]]
parseDimacs input = parse dimacsFile "" input

intoClause :: [Literal] -> Clause
intoClause [] = Bottom
intoClause (l : lits) = Or (intoClause lits) l

intoCnf :: [Maybe [Literal]] -> CNF
intoCnf [] = Top
intoCnf (Nothing : lits) = intoCnf lits
intoCnf (Just c : lits) = And (intoCnf lits) (intoClause c)

solve :: String -> Either ParseError Bool
solve input = isJust <$> solver <$> intoCnf <$> parseDimacs input

solveFile :: FilePath -> IO Bool
solveFile path = do
    contents <- readFile path
    let result = solve contents
    case result of
        Left _ -> fail $ "failed to read file: " ++ path
        Right b -> return b

intoResult :: Bool -> String
intoResult True = "SAT"
intoResult False = "UNSAT"

checkFile :: FilePath -> Bool -> IO (Maybe Bool)
checkFile path expected = do
    solved <- timeout 100 $ solveFile path
    putStr $ case solved of
        Nothing -> path ++ ": timeout\n"
        Just b -> path 
                    ++ ": expected: " 
                    ++ intoResult expected 
                    ++ ", actual: " 
                    ++ intoResult b 
                    ++ "\n"
    return $ ((==) expected) <$> solved 

countOf :: [Maybe Bool] -> Maybe Bool -> String
countOf results res = show (length $ Data.List.filter ((==) res) results)

solveFolder :: FilePath -> Bool -> IO ()
solveFolder path expected = do
    names <- getDirectoryContents path
    let files = Data.List.filter (".cnf" `isSuffixOf`) 
                    $ map (\p -> joinPath [path, p]) names
    results <- mapM (\f -> checkFile f expected) files
    putStr $ "== " ++ path ++ " ==\n"
            ++ "successes: " ++ countOf results (Just True) ++ "\n"
            ++ "failures: " ++ countOf results (Just False) ++ "\n"
            ++ "timeouts: " ++ countOf results Nothing ++ "\n"

runAll :: IO ()
runAll = do
    solveFolder "./tests/sat" True
    solveFolder "./tests/unsat" False

main :: IO ()
main = do
    args <- getArgs
    case args of 
        [] -> runAll
        (cnf : _) -> do
            solved <- solveFile cnf
            putStr $ intoResult solved
    