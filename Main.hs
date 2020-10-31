{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
module Main where

import Control.Monad
import Control.Monad.Fail (MonadFail)
import Control.Monad.IO.Class
import Data.Function
import Data.List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import System.Console.GetOpt
import System.Environment
import System.FilePath
import System.Directory

import qualified Language.Haskell.Exts.SrcLoc     as Hs
import qualified Language.Haskell.Exts.Syntax     as Hs
import qualified Language.Haskell.Exts.Build      as Hs
import qualified Language.Haskell.Exts.Pretty     as Hs
import qualified Language.Haskell.Exts.Parser     as Hs
import qualified Language.Haskell.Exts.ExactPrint as Hs
import qualified Language.Haskell.Exts.Comments   as Hs

import Agda.Main (runAgda)
import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.BasicOps
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty hiding (pretty)
import Agda.Syntax.Common hiding (Ranged)
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.TheTypeChecker
import Agda.TypeChecking.Rules.Term (isType_)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.Interaction.CommandLine (withCurrentFile)
import Agda.Utils.Lens
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.Pretty as P
import Agda.Utils.FileName
import Agda.Utils.List
import Agda.Utils.Impossible
import Agda.Utils.Maybe.Strict (toLazy, toStrict)

import HsUtils

data Options = Options { outDir :: FilePath }

defaultOptions :: Options
defaultOptions = Options{ outDir = "." }

outdirOpt :: Monad m => FilePath -> Options -> m Options
outdirOpt dir opts = return opts{ outDir = dir }

pragmaName :: String
pragmaName = "AGDA2HS"

type Ranged a    = (Range, a)
type ModuleEnv   = Builtins
type ModuleRes   = ()
type CompiledDef = [Ranged [Hs.Decl ()]]

backend :: Backend' Options Options ModuleEnv ModuleRes CompiledDef
backend = Backend'
  { backendName           = "agda2hs"
  , backendVersion        = Just "0.1"
  , options               = defaultOptions
  , commandLineFlags      = [ Option ['o'] ["out-dir"] (ReqArg outdirOpt "DIR")
                              "Write Haskell code to DIR. Default: ." ]
  , isEnabled             = \ _ -> True
  , preCompile            = return
  , postCompile           = \ _ _ _ -> return ()
  , preModule             = moduleSetup
  , postModule            = writeModule
  , compileDef            = compile
  , scopeCheckingSuffices = False
  , mayEraseType          = \ _ -> return True
  }

-- Helpers ---------------------------------------------------------------

showTCM :: PrettyTCM a => a -> TCM String
showTCM x = show <$> prettyTCM x

hsQName :: Builtins -> QName -> TCM (Hs.QName ())
hsQName builtins f
  | Just p <- Map.lookup f builtins = return $ compilePrim p
  | otherwise = do
    s <- showTCM f
    return $
      case break (== '.') $ reverse s of
        (_, "")        -> Hs.UnQual () (hsName s)
        (fr, _ : mr) -> Hs.Qual () (Hs.ModuleName () $ reverse mr) (hsName $ reverse fr)

freshString :: String -> TCM String
freshString s = freshName_ s >>= showTCM

-- Builtins ---------------------------------------------------------------

data Prim = Unit
          | Nat | Float | Word64
          | Char
          | List | Cons | Nil
          | Bool | True_ | False_
  deriving (Show, Eq)

type Builtins = Map QName Prim

getBuiltins :: TCM Builtins
getBuiltins = Map.fromList . concat <$> mapM getB
  [ builtinUnit |-> Unit
  , builtinNat |-> Nat, builtinFloat |-> Float
  , builtinWord64 |-> Word64
  , builtinBool |-> Bool, builtinTrue |-> True_, builtinFalse |-> False_
  , builtinChar |-> Char
  , builtinList |-> List , builtinCons |-> Cons , builtinNil |-> Nil
  ]
  where
    (|->) = (,)
    getB (b, t) = getBuiltin' b >>= \ case
      Nothing          -> return []
      Just (Def q _)   -> return [(q, t)]
      Just (Con c _ _) -> return [(conName c, t)]
      Just _           -> __IMPOSSIBLE__

compilePrim :: Prim -> Hs.QName ()
compilePrim = \case
  Unit   -> special Hs.UnitCon
  Nat    -> unqual "Integer"
  Float  -> unqual "Double"
  Word64 -> unqual "Word64"
  Bool   -> unqual "Bool"
  True_  -> unqual "True"
  False_ -> unqual "False"
  Char   -> unqual "Char"
  List   -> special Hs.ListCon
  Cons   -> special Hs.Cons
  Nil    -> special Hs.ListCon
  where
    unqual n  = Hs.UnQual () $ hsName n
    special c = Hs.Special () $ c ()

-- Compiling things -------------------------------------------------------

compile :: Options -> Builtins -> IsMain -> Definition -> TCM CompiledDef
compile _ builtins _ def = getUniqueCompilerPragma pragmaName (defName def) >>= \ case
  Just _  -> compile' builtins def
  Nothing -> return []

compile' :: Builtins -> Definition -> TCM CompiledDef
compile' builtins def =
  case theDef def of
    Function{} -> tag <$> compileFun builtins def
    Datatype{} -> tag <$> compileData builtins def
    _          -> return []
  where tag code = [(nameBindingSite $ qnameName $ defName def, code)]

compileData :: Builtins -> Definition -> TCM [Hs.Decl ()]
compileData builtins def = do
  let d = hsName $ prettyShow $ qnameName $ defName def
  case theDef def of
    Datatype{dataPars = n, dataIxs = 0, dataCons = cs} -> do
      TelV tel _ <- telViewUpTo n (defType def)
      addContext tel $ do
        let params = teleArgs tel :: [Arg Term]
        pars <- mapM (showTCM . unArg) $ filter visible params
        cs   <- mapM (compileConstructor builtins params) cs
        let hd   = foldl (\ h p -> Hs.DHApp () h (Hs.UnkindedVar () $ hsName p))
                         (Hs.DHead () d) pars
        return [Hs.DataDecl () (Hs.DataType ()) Nothing hd cs []]
    _ -> __IMPOSSIBLE__

compileConstructor :: Builtins -> [Arg Term] -> QName -> TCM (Hs.QualConDecl ())
compileConstructor builtins params c = do
  ty <- (`piApplyM` params) . defType =<< getConstInfo c
  TelV tel _ <- telView ty
  c <- showTCM c
  args <- compileConstructorArgs builtins tel
  return $ Hs.QualConDecl () Nothing Nothing $ Hs.ConDecl () (hsName c) args

compileConstructorArgs :: Builtins -> Telescope -> TCM [Hs.Type ()]
compileConstructorArgs _ EmptyTel = return []
compileConstructorArgs builtins (ExtendTel a tel)
  | visible a, NoAbs _ tel <- reAbs tel = do
    (:) <$> compileType builtins (unEl $ unDom a) <*> compileConstructorArgs builtins tel
compileConstructorArgs _ tel = genericDocError =<< text "Bad constructor args:" <?> prettyTCM tel

compileFun :: Builtins -> Definition -> TCM [Hs.Decl ()]
compileFun builtins def = do
  let x = hsName $ prettyShow $ qnameName $ defName def
  ty <- compileType builtins (unEl $ defType def)
  cs <- mapM (compileClause x) funClauses
  return [Hs.TypeSig () [x] ty, Hs.FunBind () cs]
  where
    Function{..} = theDef def

compileClause :: Hs.Name () -> Clause -> TCM (Hs.Match ())
compileClause x Clause{clauseTel       = tel,
                       namedClausePats = ps,
                       clauseBody      = body } =
  addContext tel $ do
    builtins <- getBuiltins
    ps   <- compilePats builtins ps
    body <- maybe (return $ Hs.Var () $ Hs.UnQual () (hsName "undefined")) (compileTerm builtins) body
    let rhs = Hs.UnGuardedRhs () body
    case (x, ps) of
      (Hs.Symbol{}, p : q : ps) -> return $ Hs.InfixMatch () p x (q : ps) rhs Nothing
      _                         -> return $ Hs.Match () x ps rhs Nothing

compileType :: Builtins -> Term -> TCM (Hs.Type ())
compileType builtins t = do
  t <- reduce t
  case t of
    Pi a b | hidden a -> underAbstraction a b (compileType builtins . unEl)
             -- Hidden Pi means Haskell forall
    Pi a (NoAbs _ b) | visible a -> do
      hsA <- compileType builtins (unEl $ unDom a)
      hsB <- compileType builtins (unEl b)
      return $ Hs.TyFun () hsA hsB
    Def f es | Just args <- allApplyElims es -> do
      vs <- mapM (compileType builtins . unArg) $ filter visible args
      f <- hsQName builtins f
      return $ tApp (Hs.TyCon () f) vs
    Var x es | Just args <- allApplyElims es -> do
      vs <- mapM (compileType builtins . unArg) $ filter visible args
      x  <- hsName <$> showTCM (Var x [])
      return $ tApp (Hs.TyVar () x) vs
    t -> genericDocError =<< text "Bad Haskell type:" <?> prettyTCM t

compileTerm :: Builtins -> Term -> TCM (Hs.Exp ())
compileTerm builtins v =
  case unSpine v of
    Var x es   -> (`app` es) . Hs.Var () . Hs.UnQual () . hsName =<< showTCM (Var x [])
    Def f es
      | show (qnameName f) == "if_then_else_" -> ite es
      | otherwise -> (`app` es) . Hs.Var () =<< hsQName builtins f
    Con h i es -> (`app` es) . Hs.Con () =<< hsQName builtins (conName h)
    Lit (LitNat _ n) -> return $ Hs.intE n
    Lit (LitFloat _ d) -> return $ Hs.Lit () $ Hs.Frac () (toRational d) (show d)
    Lit (LitWord64 _ w) -> return $ Hs.Lit () $ Hs.PrimWord () (fromIntegral w) (show w)
    Lit (LitChar _ c) -> return $ Hs.charE c
    Lam v b | visible v -> hsLambda (absName b) <$> underAbstraction_ b (compileTerm builtins)
    Lam _ b -> underAbstraction_ b (compileTerm builtins)
    t -> genericDocError =<< text "bad term:" <?> prettyTCM t
  where
    compileArgs :: Elims -> TCM [Hs.Exp ()]
    compileArgs es = do
      let Just args = allApplyElims es
      mapM (compileTerm builtins . unArg) $ filter visible args

    app :: Hs.Exp () -> Elims -> TCM (Hs.Exp ())
    app hd es = eApp <$> pure hd <*> compileArgs es

    ite :: Elims -> TCM (Hs.Exp ())
    ite es = compileArgs es >>= \case
      -- fully applied
      (b : t : f : es') -> return $ Hs.If () b t f `eApp` es'
      -- partially applied -> eta-expand
      es' -> do
        xs <- fmap Hs.name . drop (length es') <$> mapM freshString ["b", "t", "f"]
        let [b, t, f] = es' ++ map Hs.var xs
        return $ Hs.lamE (Hs.pvar <$> xs) $ Hs.If () b t f

compilePats :: Builtins -> NAPs -> TCM [Hs.Pat ()]
compilePats builtins ps = mapM (compilePat builtins . namedArg) $ filter visible ps

compilePat :: Builtins -> DeBruijnPattern -> TCM (Hs.Pat ())
compilePat builtins p@(VarP _ _)  = Hs.PVar () . hsName <$> showTCM p
compilePat builtins (ConP h _ ps) = do
  ps <- compilePats builtins ps
  c <- hsQName builtins (conName h)
  return $ pApp c ps
-- TODO: LitP
compilePat _ p = genericDocError =<< text "bad pattern:" <?> prettyTCM p

-- FOREIGN pragmas --------------------------------------------------------

type Code = (Hs.Module Hs.SrcSpanInfo, [Hs.Comment])

getForeignPragmas :: TCM [Ranged Code]
getForeignPragmas = do
  pragmas <- fromMaybe [] . Map.lookup pragmaName . iForeignCode <$> curIF
  reverse <$> mapM getCode pragmas
  where
    getCode :: ForeignCode -> TCM (Ranged Code)
    getCode (ForeignCode r code) = do
          let Just file = fmap filePath $ toLazy $ rangeFile r
              pmode = Hs.defaultParseMode { Hs.parseFilename     = file,
                                            Hs.ignoreLinePragmas = False }
              line = case posLine <$> rStart r of
                       Just l  -> "{-# LINE " ++ show l ++ show file ++ " #-}\n"
                       Nothing -> ""
          case Hs.parseWithComments pmode (line ++ code) of
            Hs.ParseOk m           -> return (r, m)
            Hs.ParseFailed loc msg -> setCurrentRange (srcLocToRange loc) $ genericError msg

-- Rendering --------------------------------------------------------------

type Block = Ranged [String]

sortRanges :: [Ranged a] -> [a]
sortRanges = map snd . sortBy (compare `on` rLine . fst)

rLine :: Range -> Int
rLine r = fromIntegral $ fromMaybe 0 $ posLine <$> rStart r

renderBlocks :: [Block] -> String
renderBlocks = unlines . map unlines . sortRanges . filter (not . null . snd)

defBlock :: CompiledDef -> [Block]
defBlock def = [ (r, map pp ds) | (r, ds) <- def ]

codePragmas :: [Ranged Code] -> [Block]
codePragmas code = [ (r, map pp ps) | (r, (Hs.Module _ _ ps _ _, _)) <- code ]

codeBlocks :: [Ranged Code] -> [Block]
codeBlocks code = [(r, [uncurry Hs.exactPrint $ moveToTop $ noPragmas mcs]) | (r, mcs) <- code, nonempty mcs]
  where noPragmas (Hs.Module l h _ is ds, cs) = (Hs.Module l h [] is ds, cs)
        noPragmas m                           = m
        nonempty (Hs.Module _ _ _ is ds, cs) = not $ null is && null ds && null cs
        nonempty _                           = True

-- Checking imports -------------------------------------------------------

imports :: [Ranged Code] -> [Hs.ImportDecl Hs.SrcSpanInfo]
imports modules = concat [imps | (_, (Hs.Module _ _ _ imps _, _)) <- modules]

checkImports :: [Hs.ImportDecl Hs.SrcSpanInfo] -> TCM [Hs.ImportDecl ()]
checkImports is = do
  forM_ is $ \i ->
    case checkImport i of
      Just loc -> setCurrentRange loc $
        genericDocError =<< text "Not allowed to import builtin type Word64"
      Nothing  -> return ()
  return [importWord64 | not (any isImportWord64 is)] 
  where
    importWord64 :: Hs.ImportDecl ()
    importWord64 = [importQ|import Data.Word (Word64)|]

    isImportWord64 :: Hs.ImportDecl Hs.SrcSpanInfo -> Bool
    isImportWord64 = \case
      Hs.ImportDecl _ (Hs.ModuleName _ "Data.Word") False _ _ _ _ specs ->
        case specs of 
          Just (Hs.ImportSpecList _ hiding specs) ->
            not hiding && "Word64" `elem` concatMap getExplicitImports specs
          Nothing -> True
      _ -> False

checkImport :: Hs.ImportDecl Hs.SrcSpanInfo -> Maybe Range
checkImport i
  | Just (Hs.ImportSpecList _ False specs) <- Hs.importSpecs i
  , pp (Hs.importModule i) /= "Data.Word"
  = listToMaybe $ mapMaybe checkImportSpec specs
  | otherwise
  = Nothing
  where
    checkImportSpec :: Hs.ImportSpec Hs.SrcSpanInfo -> Maybe Range
    checkImportSpec = \case
      Hs.IVar loc n | check n -> ret loc
      Hs.IAbs loc _ n | check n -> ret loc
      Hs.IThingAll loc n | check n -> ret loc
      Hs.IThingWith loc n ns
        | check n -> ret loc
        | Just loc' <- listToMaybe $ map cloc $ filter (check . cname) ns -> ret loc' 
      _ -> Nothing
      where
        check = (== "Word64") . pp
        ret = Just . srcSpanInfoToRange

-- Generating the files -------------------------------------------------------

moduleFileName :: Options -> ModuleName -> FilePath
moduleFileName opts name =
  outDir opts </> C.moduleNameToFileName (toTopLevelModuleName name) "hs"

moduleSetup :: Options -> IsMain -> ModuleName -> FilePath -> TCM (Recompile ModuleEnv ModuleRes)
moduleSetup _ _ _ _ = do
  setScope . iInsideScope =<< curIF
  Recompile <$> getBuiltins

ensureDirectory :: FilePath -> IO ()
ensureDirectory = createDirectoryIfMissing True . takeDirectory

writeModule :: Options -> ModuleEnv -> IsMain -> ModuleName -> [CompiledDef] -> TCM ModuleRes
writeModule opts _ isMain m defs0 = do
  code <- getForeignPragmas
  let defs = concatMap defBlock defs0 ++ codeBlocks code
  unless (null code && null defs) $ do
    -- Check user-supplied imports and automatically add ones for builtin types
    autoImports <- checkImports (imports code)
    -- The comments makes it hard to generate and pretty print a full module
    let hsFile = moduleFileName opts m
        output = concat
                 [ renderBlocks $ codePragmas code
                 , "module " ++ prettyShow m ++ " where\n\n"
                 , unlines $ map pp autoImports
                 , renderBlocks defs ]
    reportSLn "" 1 $ "Writing " ++ hsFile
    liftIO $ ensureDirectory hsFile
    liftIO $ writeFile hsFile output

main = runAgda [Backend backend]
