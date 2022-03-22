{-#
    LANGUAGE
        OverloadedStrings
#-}

module Module where

import Data.Map (Map)
import Data.Map as M
import Control.Monad.State
import Control.Monad.Except
import Data.Text (Text)
import qualified Data.Text as T
import Text.Megaparsec hiding (State)
import System.Directory
import System.IO
import System.IO.Unsafe

import Syntax
import Parsing
import Pretty (runPretty)

data    FEnv 
    =   FEnv
    {

    } deriving (Show, Eq, Ord)

type Finder a = ExceptT Error (StateT FEnv IO) a

packages :: Map Name Name
packages = M.fromList $
    [
        ("base", "E:\\ProgramFiles\\YAL\\packages")
    ]

knownDeps :: Map Name Name
knownDeps = M.fromList $
    [
        ("prelude", "base")
    ]

isThatModule :: Name -> FilePath -> IO Bool
isThatModule modname path = do
    cond <- doesFileExist path
    if cond
        then do
            file <- T.pack <$> readFile path
            return (matchModule modname file)
        else return False

matchModule :: Name -> Text -> Bool
matchModule modname file = case exec pSource file of
    (Left err, _) -> False
    (Right ast, _) -> go ast modname
    where
        go ast@((Module dir):xs) modname = if last dir == modname
            then True
            else go xs modname
        go (_:xs) modname = go xs modname


findModuleInPackage :: Name -> Name -> Finder Name
findModuleInPackage package modname = do
    case M.lookup package packages of
        Nothing -> throwError (NoPackage package)
        Just path -> do
            f <- liftIO $ do
                files <- getDirectoryContents (T.unpack path)
                f' <- findFileWith (isThatModule modname) (fmap (\a -> T.unpack path <> "\\" <> a) files) (T.unpack (modname <> ".yal"))
                return f'
            case f of
                Nothing -> throwError (NoModule modname)
                Just fpath -> T.pack <$> liftIO (do
                    v <- readFile fpath
                    return v)

findModule :: Name -> Finder Name
findModule modname = do
    f <- liftIO $ do
        files <- getDirectoryContents (".")
        f' <- findFileWith (isThatModule modname) (fmap (\a -> ".\\" <> a) files) (T.unpack (modname <> ".yal"))
        return f'
    case f of
        Nothing -> case M.lookup modname knownDeps of
            Nothing -> throwError (NoModule modname)
            Just package -> findModuleInPackage package modname
        Just fp -> T.pack <$> liftIO (readFile fp)

runFinder :: Finder a -> IO (Either Error a, FEnv)
runFinder finder = runStateT (runExceptT finder) FEnv

getImports :: Declaration -> Finder PE
getImports (Import dir _) = case dir of
    x -> do
        f <- liftIO $ do
                p <- runFinder (findModule (last x))
                return (fst p)
        case f of
            Right source -> do
                case exec pSource source of
                    (Right prog, pe) -> do
                        return pe
                -- (Left err, _) -> throwError err -- actually cannot happen (i guess)
            Left err -> throwError err
getImports _ = return initPE

parserStep :: Parser Declaration
parserStep = do
    d <- decl
    case unsafePerformIO (runFinder (getImports d)) of -- EVIL!!!!!!!!!!!
        (Left err, _) -> fail (runPretty err) -- TODO: prettyprinting function for this
        (Right pe, _) -> do
            modify (adjustPE pe)
            return d

pSource :: Parser Program
pSource = spaces *> some (parserStep <* optional (lexeme (symbol ";")))

exec p t = runState (runParserT p "input" t) initPE
execute p t pe = runState (runParserT p "input" t) pe


adjustPE :: PE -> PE -> PE
adjustPE pe1 pe2 = pe2 
    {
        btable = M.unionWith (<>) (btable pe1) (btable pe2)
    ,   utable = M.unionWith (<>) (utable pe1) (utable pe2)
    ,   typetable = M.unionWith (<>) (typetable pe1) (typetable pe2)
    ,   dtypes = (dtypes pe1) <> (dtypes pe2)
    ,   sigs = (sigs pe1) <> (sigs pe2)
    ,   datainfo = (datainfo pe1) <> (datainfo pe2)
    }

instance Semigroup PE where
    (<>) = adjustPE

instance Monoid PE where
    mempty = initPE