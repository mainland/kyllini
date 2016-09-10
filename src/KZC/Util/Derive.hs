{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- |
-- Module      :  KZC.Util.Derive
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module KZC.Util.Derive (
    deriveM,
    deriveInstanceHeader,
    deriveBinary,
    deriveLocated
  ) where

import Data.Generics
import Data.Loc
import Data.Symbol
import Text.PrettyPrint.Mainland as PP

allLetters :: [Doc]
allLetters = [char c | c <- ['a'..'z']]

deriveM :: (a -> Doc) -> a -> IO ()
deriveM derive (_ :: a) = do
    putDoc $ derive (undefined :: a)
    putStrLn ""

deriveInstanceHeader :: forall a . (Typeable a, Data a) => Doc -> a -> (Doc, Doc)
deriveInstanceHeader className _ =
    (ctx, inst)
  where
    typeName :: TyCon
    typeChildren :: [TypeRep]
    (typeName, typeChildren) = splitTyConApp (typeOf (undefined::a))

    nTypeChildren :: Int
    nTypeChildren = length typeChildren

    typeLetters :: [Doc]
    typeLetters = take nTypeChildren allLetters

    ctx :: Doc
    ctx | nTypeChildren > 0 = commasep ([className <+> a | a <- typeLetters]) <+> text "=>" <> space
        | otherwise         = PP.empty

    inst :: Doc
    inst = parensIf (nTypeChildren > 0) $
           sep (text (tyConName typeName) : typeLetters)

deriveBinary :: forall a . (Typeable a, Data a) => a -> Doc
deriveBinary _ =
    nest 2 $
    text "instance" <+> ctx <> text "Binary" <+> inst <+> text "where" </>
    stack (map putDef constrs) </> getDefs
  where
    ctx, inst :: Doc
    (ctx, inst) = deriveInstanceHeader (text "Binary") (undefined :: a)

    typeName :: TyCon
    (typeName, _) = splitTyConApp (typeOf (undefined::a))

    constrs :: [(Int, String, Int)]
    constrs = map gen $ zip [0..] $ dataTypeConstrs (dataTypeOf (undefined::a))
      where
        gen :: (Int, Constr) -> (Int, String, Int)
        gen (i, con) =
            ( i
            , showConstr con
            , gmapQl (+) 0 (const 1) (fromConstrB empty' con :: a)
            )

    putDef :: (Int, String, Int) -> Doc
    putDef (n, name, ps) =
        nest 2 $
        text "put" <+> wrap pattern <+> text "=" <+/>
        sep ([text "putWord8" <+> ppr n | length constrs >  1] ++
             [text ">>"                 | length constrs >  1 && ps >  0] ++
             [text "return ()"          | length constrs == 1 && ps == 0]) <+>
        folddoc ppSeq (map (text "put" <+>) (take ps allLetters))
      where
        wrap | ps /= 0   = parens
             | otherwise = id

        pattern = spread (text name : take ps allLetters)

        ppSeq x y = x <+> text ">>" <+> y

    getDefs :: Doc
    getDefs | length constrs > 1 =
        nest 2 $
        text "get" <+> text "=" <+> text "do" </>
        text "tag_ <- getWord8" </>
        nest 2 (text "case tag_ of" </>
                stack (map getDef constrs) </>
                text "_" <+> text "->" <+> text "fail" <+> text ("\"" ++ tyConName typeName ++ ": no decoding\"")
               )
            | otherwise =
        text "get" <+> text "=" <+> sep (map getDef constrs)

    getDef :: (Int, String, Int) -> Doc
    getDef (n, name, ps) =
        sep $
        [ppr n <+> text "->" | length constrs > 1] ++
        if ps == 0
           then [text "pure" <+> text name]
           else [text name <+> text "<$>" <+> folddoc ppSeq (replicate ps (text "get"))]
      where
        ppSeq x y = x <+> text "<*>" <+> y

deriveLocated :: forall a . (Typeable a, Data a) => a -> Doc
deriveLocated _ =
    nest 2 $
    text "instance" <+> text "Located" <+> inst <+> text "where" </>
    stack (map locDef constrs)
  where
    inst :: Doc
    (_, inst) = deriveInstanceHeader (text "Binary") (undefined :: a)

    constrs :: [(String, [String], Int)]
    constrs = map gen $ dataTypeConstrs (dataTypeOf (undefined::a))
      where
        gen :: Constr -> (String, [String], Int)
        gen con =
            ( showConstr con
            , gmapQ (showConstr . toConstr) (fromConstrB empty' con :: a)
            , gmapQl (+) 0 (const 1) (fromConstrB empty' con :: a)
            )

    locDef :: (String, [String], Int) -> Doc
    locDef (name, ks, ps) =
        nest 2 $
        text "locOf" <+> wrap pattern <+> text "=" <+/> text rhs
      where
        wrap | ps /= 0   = parens
             | otherwise = id

        (pats, rhs) = go ks
          where
            go :: [String] -> ([String], String)
            go [] = ([], "NoLoc")

            go (con : ks') | hasLoc con = ("l" : replicate (length ks') "_", "locOf l")
                           | otherwise  = ("_" : pats, rhs)
              where
                (pats, rhs) = go ks'

            hasLoc :: String -> Bool
            hasLoc "Name"   = True
            hasLoc "SrcLoc" = True
            hasLoc _        = False

        pattern = spread (text name : map text pats)

empty' :: forall a. Data a => a
empty' = Data.Generics.empty
  `extB` pos
  `extB` loc
  `extB` srcloc
  `extB` symbol
  where
    pos :: Pos
    pos = Pos "" 1 1 1

    loc :: Loc
    loc = NoLoc

    srcloc :: SrcLoc
    srcloc = SrcLoc NoLoc

    symbol :: Symbol
    symbol = intern ""
